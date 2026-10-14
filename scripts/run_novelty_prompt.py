#!/usr/bin/env python3

import argparse
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Review one theorem, or all unreviewed theorems when omitted.",
        epilog="Pass extra agent arguments after --.",
    )
    parser.add_argument(
        "theorem", nargs="?", type=Path, help="Theorem name or .lean path"
    )
    parser.add_argument(
        "--output", type=Path, help="New Markdown path for a single review"
    )
    parser.add_argument(
        "--output-dir", type=Path, help="Review folder (default: scripts/reviews)"
    )
    parser.add_argument(
        "--jobs", type=int, default=1, help="Parallel reviews (default: 1)"
    )
    parser.add_argument("--agent", choices=("codex", "omp", "claude"), default="codex")
    parser.add_argument(
        "--dangerous", action="store_true", help="Enable unrestricted agent execution."
    )
    argv = list(sys.argv[1:] if argv is None else argv)
    split = argv.index("--") if "--" in argv else len(argv)
    args = parser.parse_args(argv[:split])
    agent_args = argv[split + 1 :]
    scripts = Path(__file__).resolve().parent
    theorems = scripts.parent / "LongTails/Theorems"
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    reviews = (
        args.output_dir.expanduser().resolve()
        if args.output_dir
        else scripts / "reviews"
    )
    reviews.mkdir(parents=True, exist_ok=True)
    if args.theorem is not None:
        theorem = args.theorem.expanduser()
        if theorem.parent == Path("."):
            theorem = theorems / theorem
        if not theorem.suffix:
            theorem = theorem.with_suffix(".lean")
        theorem = theorem.resolve()
        if (
            theorem.parent != theorems.resolve()
            or theorem.suffix != ".lean"
            or not theorem.is_file()
        ):
            parser.error("theorem must be an existing .lean file in LongTails/Theorems")
        output = (
            args.output.expanduser().absolute()
            if args.output
            else reviews / f"{theorem.stem}.md"
        )
        if output.suffix.lower() != ".md" or output.exists() or output.is_symlink():
            parser.error(
                "output must be a new .md file; existing reviews are never overwritten"
            )
        pending = [theorem]
    else:
        if args.output is not None:
            parser.error("--output requires a single theorem")
        pending = [
            path
            for path in sorted(theorems.glob("*.lean"))
            if not (reviews / f"{path.stem}.md").exists()
            and not (reviews / f"{path.stem}.md").is_symlink()
        ]
    logs = Path(tempfile.mkdtemp(prefix="auto-math-reviews-"))
    print(f"Logs: {logs}", flush=True)
    prompt = (scripts / "novelty_prompt.md").read_text(encoding="utf-8")
    command = {
        "omp": ["omp"] + (["--yolo"] if args.dangerous else []),
        "claude": ["claude", "--print"]
        + (["--dangerously-skip-permissions"] if args.dangerous else []),
        "codex": [
            "codex",
            "exec",
            "-s",
            "danger-full-access" if args.dangerous else "workspace-write",
        ]
        + (["-c", "features.network_proxy=false"] if args.dangerous else []),
    }[args.agent]

    def review(theorem):
        report = output if args.theorem is not None else reviews / f"{theorem.stem}.md"
        task = prompt + f"\n\nTheorem: {theorem}\nReport destination: {report}\n"
        with (logs / f"{theorem.stem}.log").open("w") as log:
            try:
                result = subprocess.run(
                    [*command, *agent_args, task],
                    cwd=scripts.parent,
                    env={**os.environ, "IS_SANDBOX": "1"}
                    if args.agent == "claude" and args.dangerous
                    else None,
                    stdin=subprocess.DEVNULL,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    check=False,
                )
                success = (
                    result.returncode == 0
                    and report.is_file()
                    and report.stat().st_size > 0
                )
            except OSError as error:
                log.write(str(error))
                success = False
        print(f"{'DONE' if success else 'FAILED'} {theorem.stem}", flush=True)
        return success

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(review, pending))
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
