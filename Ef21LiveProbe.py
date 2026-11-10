#!/usr/bin/env python3
"""Observe bounded Lean import checks without changing the proof or dependencies."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from typing import TextIO

HZ = os.sysconf("SC_CLK_TCK")
PAGE_SIZE = os.sysconf("SC_PAGE_SIZE")


def read_text(path: Path, limit: int = 100_000) -> str:
    try:
        with path.open(errors="replace") as stream:
            return stream.read(limit)
    except OSError as exc:
        return f"[unavailable: {exc.strerror}]"


def proc_stat(pid: int, tid: int | None = None) -> dict | None:
    base = Path(f"/proc/{pid}")
    if tid is not None:
        base = base / "task" / str(tid)
    try:
        text = (base / "stat").read_text()
        end = text.rfind(")")
        fields = text[end + 2 :].split()
        return {
            "pid": pid,
            "tid": tid,
            "name": text[text.find("(") + 1 : end],
            "state": fields[0],
            "ppid": int(fields[1]),
            "session": int(fields[3]),
            "cpu": (int(fields[11]) + int(fields[12])) / HZ,
            "rss_mib": int(fields[21]) * PAGE_SIZE / 1048576,
            "minflt": int(fields[7]),
            "majflt": int(fields[9]),
            "threads": int(fields[17]),
            "wchan": read_text(base / "wchan", 200).strip(),
        }
    except (OSError, ValueError, IndexError):
        return None


def process_table() -> list[dict]:
    rows = []
    for path in Path("/proc").iterdir():
        if path.name.isdecimal():
            row = proc_stat(int(path.name))
            if row is not None:
                rows.append(row)
    return rows


class Report:
    def __init__(self, path: Path):
        self.stream: TextIO = path.open("w", encoding="utf-8", buffering=1)

    def write(self, text: str = "") -> None:
        print(text, flush=True)
        self.stream.write(text + "\n")

    def close(self) -> None:
        self.stream.close()


def memory_snapshot(report: Report) -> None:
    wanted = ("MemTotal:", "MemAvailable:", "SwapTotal:", "SwapFree:")
    for line in read_text(Path("/proc/meminfo")).splitlines():
        if line.startswith(wanted):
            report.write(line)
    for name in ("memory", "io", "cpu"):
        path = Path("/proc/pressure") / name
        if path.exists():
            report.write(f"pressure/{name}: {read_text(path, 1000).strip()}")


def session_snapshot(report: Report, sid: int, elapsed: float) -> None:
    report.write(f"\nSNAPSHOT elapsed={elapsed:.1f}s session={sid}")
    memory_snapshot(report)
    rows = [row for row in process_table() if row["session"] == sid]
    if not rows:
        report.write("No processes from this test remain visible.")
    for row in sorted(rows, key=lambda item: item["pid"]):
        pid = row["pid"]
        command = read_text(Path(f"/proc/{pid}/cmdline"), 1800).replace("\0", " ").strip()
        report.write(
            f"PID={pid} PPID={row['ppid']} state={row['state']} "
            f"cpu_seconds={row['cpu']:.2f} rss_MiB={row['rss_mib']:.1f} "
            f"minor_faults={row['minflt']} major_faults={row['majflt']} "
            f"threads={row['threads']} wchan={row['wchan']}\ncommand={command}"
        )
        io_lines = read_text(Path(f"/proc/{pid}/io"), 2000).splitlines()
        report.write("io: " + "; ".join(io_lines))
        mapped = []
        for line in read_text(Path(f"/proc/{pid}/maps"), 2_000_000).splitlines():
            fields = line.split(maxsplit=5)
            if len(fields) == 6 and any(
                ext in fields[5] for ext in (".olean", ".ilean", ".ir", ".so")
            ):
                if fields[5] not in mapped:
                    mapped.append(fields[5])
        report.write(f"Mapped library/artifact paths (last 8 distinct, not a call stack): {mapped[-8:]}")
        try:
            tasks = [
                proc_stat(pid, int(path.name))
                for path in Path(f"/proc/{pid}/task").iterdir()
                if path.name.isdecimal()
            ]
        except OSError:
            tasks = []
        tasks = sorted(
            (task for task in tasks if task is not None),
            key=lambda task: task["cpu"], reverse=True,
        )
        for task in tasks[:12]:
            report.write(
                f"  TID={task['tid']} state={task['state']} "
                f"cpu_seconds={task['cpu']:.2f} wchan={task['wchan']}"
            )
        if len(tasks) > 12:
            report.write(f"  ({len(tasks) - 12} other threads omitted)")


def stop_group(proc: subprocess.Popen) -> None:
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        pass
    # Also clean up children if their parent exited before they did.
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        pass


def run_probe(
    report: Report, label: str, command: list[str], repo: Path, env: dict[str, str],
    log: Path, seconds: float, trace: Path | None = None,
) -> tuple[int, bool]:
    report.write(f"\n========== {label} ==========\nCommand: {shlex.join(command)}")
    report.write(f"Diagnostic wall-clock cutoff: {seconds:g}s (not a verification-time estimate)")
    started = time.monotonic()
    timed_out = False
    stopped_for_size = False
    with log.open("wb") as output:
        proc = subprocess.Popen(
            command, cwd=repo, env=env, stdout=output, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, start_new_session=True,
        )
        next_snapshot = 1.0
        try:
            while proc.poll() is None:
                elapsed = time.monotonic() - started
                if elapsed >= next_snapshot:
                    session_snapshot(report, proc.pid, elapsed)
                    next_snapshot = elapsed + 5.0
                if trace is not None and trace.exists() and trace.stat().st_size > 8_000_000:
                    stopped_for_size = True
                    report.write("Trace size limit reached; stopping only this test's process group.")
                    stop_group(proc)
                    break
                if elapsed >= seconds:
                    timed_out = True
                    session_snapshot(report, proc.pid, elapsed)
                    report.write("Diagnostic timeout; stopping only this test's process group.")
                    stop_group(proc)
                    break
                time.sleep(0.2)
        finally:
            if proc.poll() is None:
                stop_group(proc)
        status = proc.poll()
    if status is None:
        status = -999
    report.write(
        f"PROCESS_RETURN_CODE={status} TIMED_OUT={timed_out} "
        f"TRACE_LIMIT_REACHED={stopped_for_size} "
        f"WALL_SECONDS={time.monotonic() - started:.2f}"
    )
    report.write("--- Captured command output ---")
    content = read_text(log, 80_000)
    report.write(content if content else "[no output]")
    if trace is not None and trace.exists():
        with trace.open("rb") as stream:
            stream.seek(max(0, trace.stat().st_size - 40_000))
            tail = stream.read().decode(errors="replace").splitlines()[-160:]
        report.write("--- Last 160 syscall-trace lines (diagnostic, not proof output) ---")
        report.write("\n".join(tail))
    return status, timed_out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    args = parser.parse_args()
    repo = args.repository.expanduser().resolve()
    if sys.platform != "linux":
        parser.error("This diagnostic uses Linux /proc and is intended for the Codespace.")
    if not (repo / "lean-toolchain").is_file():
        parser.error(f"No lean-toolchain file in {repo}")
    env = os.environ.copy()
    elan = Path(env.get("ELAN_HOME", str(Path.home() / ".elan"))) / "bin"
    env["PATH"] = f"{elan}{os.pathsep}{env.get('PATH', '')}"
    env.pop("LEAN_NUM_THREADS", None)
    lake = shutil.which("lake", path=env["PATH"])
    if lake is None:
        parser.error("lake was not found, including in the usual Elan directory.")
    work = Path(tempfile.mkdtemp(prefix="Ef21LiveProbe_", dir=repo))
    report_path = work / "Ef21LiveReport.txt"
    report = Report(report_path)
    try:
        report.write("EF21 live import diagnostic; no EF21 lemmas are checked.")
        report.write(f"UTC={datetime.now(timezone.utc).isoformat()}\nRepository={repo}")
        report.write(f"Pinned toolchain: {read_text(repo / 'lean-toolchain').strip()}")
        report.write(f"Lake command: {lake}\nCPU count: {os.cpu_count()}")
        report.write("No proof edits, patch application, cache deletion, or toolchain updates requested.")
        report.write("--- Lean/Lake processes visible BEFORE this test (not stopped by this script) ---")
        for row in process_table():
            if row["name"] in {"lean", "lake", "elan", "leanchecker"}:
                report.write(
                    f"PID={row['pid']} name={row['name']} state={row['state']} "
                    f"cpu_seconds={row['cpu']:.2f} rss_MiB={row['rss_mib']:.1f}"
                )
        memory_snapshot(report)
        pure = work / "CoreOnly.lean"
        small = work / "SmallImport.lean"
        pure.write_text("#check Nat\n", encoding="utf-8")
        small.write_text(
            "import Mathlib.Analysis.InnerProductSpace.Basic\n#check Nat\n", encoding="utf-8"
        )
        shell = (
            'printf "EF21_CHILD_STARTED\\n"; command -v lean; '
            'printf "LEAN_PATH=%s\\n" "$LEAN_PATH"; '
            'printf "LEAN_SYSROOT=%s\\n" "$LEAN_SYSROOT"; '
            'exec lean "$1"'
        )
        def command(file: Path) -> list[str]:
            return [lake, "env", "/bin/sh", "-c", shell, "ef21-probe", str(file)]
        core_result = run_probe(
            report, "Core file: no explicit Mathlib import", command(pure), repo, env,
            work / "core.log", 15,
        )
        failed_file = pure
        if core_result == (0, False):
            result = run_probe(
                report, "Small Mathlib import", command(small), repo, env,
                work / "small.log", 30,
            )
            failed_file = small
        else:
            result = core_result
            report.write("Core-file check failed/timed out; skipping the larger import test.")
        if result != (0, False):
            strace = shutil.which("strace", path=env["PATH"])
            if strace:
                trace = work / "syscalls.log"
                traced = [
                    strace, "-f", "-tt", "-T", "-s", "120", "-e",
                    "trace=%file,%process,futex", "-o", str(trace), *command(failed_file),
                ]
                run_probe(
                    report, "Optional syscall trace of failing test", traced, repo, env,
                    work / "traced.log", 15, trace,
                )
            else:
                report.write("strace is not installed; live /proc snapshots above are still available.")
                report.write("This script does not install software or request administrator access.")
        report.write("\nChecks are complete. Upload this plain-text report, not an archive:")
        report.write(str(report_path))
        return 0
    finally:
        report.close()


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("\nInterrupted. The active test process group has been stopped.", file=sys.stderr)
        raise SystemExit(130)