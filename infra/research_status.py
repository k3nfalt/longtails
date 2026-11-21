"""Show the visible state of remote research tmux panes without attaching."""

import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


def pane_state(screen):
    lines = screen.rstrip().splitlines()
    # An old error can stay in the transcript after the next turn starts.
    prompt = next(
        (
            i
            for i in reversed(range(len(lines)))
            if lines[i].lstrip().startswith(("›", "❯"))
        ),
        len(lines),
    )
    tail = "\n".join(lines[max(0, prompt - 6) :]).lower()
    # Claude can display a menu while a background agent is still working.
    if re.search(
        r"^\s*[✻✶✽✳✢·]\s+Waiting for (?:\d+ |a )?background (?:agents?|tasks?) to finish\b",
        "\n".join(lines[max(0, prompt - 15) : prompt]),
        re.MULTILINE | re.IGNORECASE,
    ):
        return "working (background)"
    if re.search(r"\besc to (?:interrupt|steer)\b", tail):
        return "working"
    if re.search(
        r"press enter to confirm|enter to confirm|would you like to run the following command\?",
        tail,
    ):
        return "waiting for input"
    if prompt < len(lines):
        footer = "\n".join(lines[prompt + 1 :]).lower()
        if "goal achieved" in footer:
            return "goal achieved"
        if "goal paused" in footer:
            return "goal paused"
        if lines[prompt].lstrip().startswith("❯"):
            for line in reversed(lines[max(0, prompt - 12) : prompt]):
                if line.lstrip().startswith("❯"):
                    break
                if re.match(r"^\s*✔\s+Goal achieved\b", line, re.IGNORECASE):
                    return "goal achieved"
        above = "\n".join(lines[:prompt]).rstrip()
        if re.search(
            r"^ *■\s*stream\s+disconnected\s+before\s+completion:[^\n]*(?:\n +[^\n]+)*\Z",
            above,
            re.MULTILINE | re.IGNORECASE,
        ):
            return "disconnected"
    return "unknown"


def inspect_panes():
    if not shutil.which("tmux"):
        print("tmux unavailable")
        return 1
    fmt = "#{session_name}:#{window_index}#{?#{e|>:#{window_panes},1},.#{pane_index},}\t#{pane_id}\t#{window_name}\t#{pane_dead}\t#{pane_tty}\t#{pane_current_command}\t#{pane_start_command}"
    result = subprocess.run(
        ["tmux", "list-panes", "-aF", fmt], capture_output=True, text=True
    )
    if result.returncode:
        if (
            "no server running" in result.stderr
            or "No such file or directory" in result.stderr
        ):
            print("no tmux server")
            return 0
        print("could not list tmux panes")
        return 1
    found = False
    for line in result.stdout.splitlines():
        target, pane, window, dead, tty, foreground, start = line.split("\t", 6)
        if (
            window != "research"
            and "run_research_prompt.py" not in start
            and foreground != "claude"
        ):
            continue
        found = True
        if dead == "1":
            state = "exited"
        else:
            view = subprocess.run(
                ["tmux", "capture-pane", "-pt", pane],
                capture_output=True,
                text=True,
                errors="replace",
            )
            state = pane_state(view.stdout) if view.returncode == 0 else "unknown"
            if foreground in {"sh", "bash", "zsh", "fish", "dash"}:
                ps = subprocess.run(
                    ["ps", "-t", tty, "-o", "comm="], capture_output=True, text=True
                )
                if ps.returncode == 0 and ps.stdout.split() == [foreground]:
                    state = "shell only"
        print(f"{target}  {window}  {state}")
    if not found:
        print("no research panes")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ssh",
        default="ssh",
        metavar="COMMAND",
        help="SSH executable or interactive shell function (default: ssh)",
    )
    parser.add_argument(
        "hosts",
        nargs="*",
        default=["root@37.27.154.109"],
        metavar="HOST",
        help="SSH host or user@host (default: root@37.27.154.109)",
    )
    args = parser.parse_args()
    ssh = [args.ssh]
    if not shutil.which(args.ssh):
        ssh = [
            os.environ.get("SHELL") or "/bin/sh",
            "-ic",
            '"$@"',
            "research-status",
            args.ssh,
        ]
    status = 0
    for host in args.hosts:
        # Accept user@host:/path copied from scp; tmux sessions are per user.
        dest = host.partition(":/")[0]
        if not dest or dest.startswith("-"):
            parser.error(f"invalid SSH destination: {host}")
        print(dest, flush=True)
        try:
            with Path(__file__).open("rb") as script:
                result = subprocess.run(
                    [
                        *ssh,
                        "-o",
                        "BatchMode=yes",
                        "-o",
                        "ConnectTimeout=6",
                        "--",
                        dest,
                        "python3 - --inspect",
                    ],
                    stdin=script,
                    stderr=subprocess.PIPE,
                    timeout=20,
                )
            warning = (
                b"** WARNING: connection is not using a post-quantum key exchange algorithm.\n"
                b'** This session may be vulnerable to "store now, decrypt later" attacks.\n'
                b"** The server may need to be upgraded. See https://openssh.com/pq.html\n"
            )
            sys.stderr.buffer.write(
                result.stderr.replace(b"\r\n", b"\n").replace(warning, b"")
            )
            if result.returncode == 255:
                print("SSH connection failed", flush=True)
            status |= int(result.returncode != 0)
        except subprocess.TimeoutExpired:
            print("SSH probe timed out", flush=True)
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(inspect_panes() if sys.argv[1:] == ["--inspect"] else main())
