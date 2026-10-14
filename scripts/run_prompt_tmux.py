#!/usr/bin/env python3

import argparse
import os
import shlex
import shutil
import subprocess
import sys
from pathlib import Path


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Run a research or proposals prompt in a new tmux window.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Forwarded runner arguments:
  proposals: --keywords WORD [WORD ...] (quote multi-word phrases)
  research:  [PROPOSAL.md] [--direction {1,2,3,4,5}]
             [--research-direction WORD [WORD ...]] (quote multi-word phrases)
             --direction requires a proposal file.
  Put extra agent arguments after --.

Examples (from the repository root):
  python3 scripts/run_prompt_tmux.py proposals --keywords "nonconvex optimization"
  python3 scripts/run_prompt_tmux.py research --agent omp
  python3 scripts/run_prompt_tmux.py research --research-direction "last-iterate cyclic convergence"
  python3 scripts/run_prompt_tmux.py research scripts/proposals/example.md --direction 2
  python3 scripts/run_prompt_tmux.py proposals --agent omp --model openai/gpt-6-astra
  python3 scripts/run_prompt_tmux.py research --agent omp --openrouter --model openai/gpt-6-astra
  python3 scripts/run_prompt_tmux.py research --agent omp -- --thinking high
  python3 scripts/run_prompt_tmux.py research --agent claude --model opus

Environment:
  Requires a running tmux server and the selected agent on PATH.
  OPENROUTER_API_KEY is required with --openrouter.
  PROXY_URL, when set, is forwarded as HTTP, HTTPS, and WebSocket proxy settings.
  AUTO_MATH_BOT_KEY, when set, is forwarded as an absolute path to the bot key.
  The window starts in the repository root and keeps a shell open on exit
  (zsh if installed, otherwise $SHELL). If the shell dies, the pane stays visible.
""",
    )
    parser.add_argument(
        "--agent",
        choices=("codex", "omp", "claude"),
        default="codex",
        help="Agent to launch (default: codex)",
    )
    parser.add_argument(
        "--dangerous", action="store_true", help="Enable unrestricted agent execution."
    )
    parser.add_argument(
        "--openrouter",
        action="store_true",
        help="Use OpenRouter; requires --model and OPENROUTER_API_KEY",
    )
    parser.add_argument("--model", help="Model identifier; Codex requires --openrouter")
    parser.add_argument(
        "prompt",
        choices=("proposals", "research"),
        help="Generate proposals or investigate a research direction",
    )
    argv = list(sys.argv[1:] if argv is None else argv)
    split = argv.index("--") if "--" in argv else len(argv)
    args, runner_args = parser.parse_known_args(argv[:split])
    runner_args += argv[split:]

    command = [
        sys.executable,
        f"scripts/run_{args.prompt}_prompt.py",
        "--agent",
        args.agent,
        *(["--dangerous"] if args.dangerous else []),
        *runner_args,
    ]
    if args.openrouter:
        if not args.model:
            parser.error("--openrouter requires --model")
        if not os.environ.get("OPENROUTER_API_KEY"):
            parser.error("--openrouter requires OPENROUTER_API_KEY")
        if "--" not in runner_args:
            command.append("--")
        if args.agent == "omp":
            model = (
                args.model
                if args.model.startswith("openrouter/")
                else f"openrouter/{args.model}"
            )
            command.extend(("--model", model, "--thinking", "high"))
        elif args.agent == "claude":
            command.extend(("--model", args.model))
        else:
            command.extend(("-m", args.model))
            for setting in (
                'model_reasoning_effort="high"',
                'model_provider="openrouter"',
                'model_providers.openrouter.name="OpenRouter"',
                'model_providers.openrouter.base_url="https://openrouter.ai/api/v1"',
                'model_providers.openrouter.env_key="OPENROUTER_API_KEY"',
                'model_providers.openrouter.wire_api="responses"',
            ):
                command.extend(("-c", setting))
    elif args.model:
        if args.agent == "codex":
            parser.error("--model requires --openrouter for Codex")
        if "--" not in runner_args:
            command.append("--")
        command.extend(("--model", args.model))

    tmux = [
        "tmux",
        "new-window",
        "-n",
        "research",
        "-c",
        str(Path(__file__).resolve().parent.parent),
    ]
    if args.agent == "claude" and args.dangerous:
        tmux.extend(("-e", "IS_SANDBOX=1"))
    if proxy := os.environ.get("PROXY_URL"):
        for name in (
            "PROXY_URL",
            "HTTP_PROXY",
            "HTTPS_PROXY",
            "WS_PROXY",
            "WSS_PROXY",
            "http_proxy",
            "https_proxy",
        ):
            tmux.extend(("-e", f"{name}={proxy}"))
    if key := os.environ.get("AUTO_MATH_BOT_KEY"):
        key = Path(key).expanduser().resolve()
        if not key.is_file():
            parser.error(f"AUTO_MATH_BOT_KEY is not a file: {key}")
        tmux.extend(("-e", f"AUTO_MATH_BOT_KEY={key}"))
    if installation_id := os.environ.get("AUTO_MATH_BOT_INSTALLATION_ID"):
        tmux.extend(("-e", f"AUTO_MATH_BOT_INSTALLATION_ID={installation_id}"))
    if args.openrouter:
        tmux.extend(("-e", f"OPENROUTER_API_KEY={os.environ['OPENROUTER_API_KEY']}"))
        if args.agent == "claude":
            tmux.extend(
                (
                    "-e",
                    "ANTHROPIC_BASE_URL=https://openrouter.ai/api",
                    "-e",
                    f"ANTHROPIC_AUTH_TOKEN={os.environ['OPENROUTER_API_KEY']}",
                    "-e",
                    "ANTHROPIC_API_KEY=",
                )
            )
    shell = shutil.which("zsh") or os.environ.get("SHELL") or "sh"
    tmux.append(f"{shlex.join(command)}; exec {shlex.quote(shell)}")
    return subprocess.run(
        ["tmux", "source-file", "-"],
        input=shlex.join(tmux[1:]) + "\nset-option -w remain-on-exit on\n",
        text=True,
    ).returncode


if __name__ == "__main__":
    sys.exit(main())
