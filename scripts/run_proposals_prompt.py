#!/usr/bin/env python3

import argparse
import subprocess
import sys
from pathlib import Path


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Run proposals, optionally guided by keywords.",
        epilog="Pass extra agent arguments after --.",
    )
    parser.add_argument("--agent", choices=("codex", "omp", "claude"), default="codex")
    parser.add_argument(
        "--dangerous", action="store_true", help="Enable unrestricted agent execution."
    )
    parser.add_argument(
        "--keywords",
        nargs="+",
        default=[],
        help="Research topics to prioritize; quote multi-word phrases",
    )
    argv = list(sys.argv[1:] if argv is None else argv)
    split = argv.index("--") if "--" in argv else len(argv)
    args = parser.parse_args(argv[:split])
    agent_args = argv[split + 1 :]
    scripts = Path(__file__).resolve().parent
    prompt = (scripts / "proposals_prompt.md").read_text(encoding="utf-8")
    if args.keywords:
        prompt += (
            "\n\nKeyword guidance\n\n"
            "Prioritize research directions related to these keywords or phrases. "
            "All requirements above, including distinctness and independent review, still apply.\n"
            + "\n".join(f"- {keyword}" for keyword in args.keywords)
            + "\n"
        )
    command = {
        "omp": ["omp"] + (["--yolo"] if args.dangerous else []),
        "claude": ["claude"]
        + (["--dangerously-skip-permissions"] if args.dangerous else []),
        "codex": [
            "codex",
            "--enable",
            "goals",
            "-s",
            "danger-full-access" if args.dangerous else "workspace-write",
        ]
        + (["-c", "features.network_proxy=false"] if args.dangerous else []),
    }[args.agent]
    try:
        return subprocess.run(
            [*command, *agent_args, prompt], cwd=scripts.parent, check=False
        ).returncode
    except FileNotFoundError:
        parser.error(f"{args.agent} was not found in PATH")


if __name__ == "__main__":
    sys.exit(main())
