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
    prompts = [
        i
        for i, line in enumerate(lines)
        if line.lstrip().startswith(("›", "❯"))
        and not line.lstrip().startswith("› Message from @")
    ]
    prompt = prompts[-1] if prompts else len(lines)
    start = prompts[-2] + 1 if len(prompts) >= 2 else 0
    recent = lines[max(start, prompt - 15) : prompt]
    footer = "\n".join(lines[prompt + 1 :]).lower()

    for marker, state in (
        ("goal achieved", "goal achieved"),
        ("goal paused", "goal paused"),
        ("esc to interrupt", "working"),
        ("esc to steer", "working"),
    ):
        if marker in footer:
            return state

    menu = "enter to confirm" in footer
    if prompts and re.search(
        r"^ *■\s*stream\s+disconnected\s+before\s+completion:[^\n]*(?:\n +[^\n]+)*\Z",
        "\n".join(recent).rstrip(),
        re.MULTILINE | re.IGNORECASE,
    ):
        return "waiting for input" if menu else "disconnected"

    # Read newest first. Claude's confirmation menu can coexist with background work.
    for line in reversed(recent):
        line = line.strip().lower()
        if re.match(
            r"[✻✶✽✳✢·]\s+waiting for (?:\d+ |a )?background (?:agents?|tasks?) to finish\b",
            line,
        ):
            return "working (background)"
        if line.startswith("✔ goal achieved"):
            return "waiting for input" if menu else "goal achieved"
        if "esc to interrupt" in line or "esc to steer" in line:
            return "waiting for input" if menu else "working"
        if "would you like to run the following command?" in line:
            return "waiting for input"
        if line.startswith("■"):
            break
    return "waiting for input" if menu else "unknown"


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


def destinations(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--server",
        nargs=2,
        action="append",
        required=True,
        metavar=("SSH_COMMAND", "HOST"),
        help="Check HOST using this SSH executable or shell function; repeat for each server",
    )
    targets = []
    for command, host in parser.parse_args(argv).server:
        # Accept user@host:/path copied from scp; tmux sessions are per user.
        dest = host.partition(":/")[0]
        if not dest or dest.startswith("-"):
            parser.error(f"invalid SSH destination: {host}")
        targets.append((command, dest))
    return targets


def main():
    status = 0
    for command, dest in destinations(sys.argv[1:]):
        ssh = [command]
        if not shutil.which(command):
            ssh = [
                os.environ.get("SHELL") or "/bin/sh",
                "-ic",
                '"$@"',
                "research-status",
                command,
            ]
        print(dest, flush=True)
        try:
            with Path(__file__).open("rb") as script:
                result = subprocess.run(
                    [
                        *ssh,
                        "-o",
                        "BatchMode=yes",
                        "-o",
                        "LogLevel=ERROR",
                        "-o",
                        "ConnectTimeout=6",
                        "--",
                        dest,
                        "python3 - --inspect",
                    ],
                    stdin=script,
                    timeout=20,
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
