"""Review one agent PR in isolation, then push one commit containing its reviews."""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(command, cwd=None, capture=False):
    result = subprocess.run(
        command, cwd=cwd or ROOT, check=True, text=True, capture_output=capture
    )
    return result.stdout.strip() if capture else None


def authenticated(command, cwd=None, capture=False):
    return run(
        [sys.executable, str(ROOT / "scripts/generate_token.py"), *command],
        cwd,
        capture,
    )


def commit_count(root, base):
    return int(run(["git", "rev-list", "--count", f"{base}..HEAD"], root, True))


def task_theorems(root, base):
    changes = run(
        ["git", "diff", "--name-status", "--no-renames", f"{base}...HEAD"], root, True
    )
    names = []
    for line in changes.splitlines():
        status, name = line.split("\t")
        if name == "LongTails/Template.lean" or not (
            name.startswith("LongTails/")
            or name in {"lakefile.toml", "lake-manifest.json"}
        ):
            raise ValueError(f"Research commit changes a forbidden path: {name}")
        path = Path(name)
        if path.parent.as_posix() == "LongTails/Theorems" and path.suffix == ".lean":
            if status != "A":
                raise ValueError(
                    f"Research tasks must add a new theorem, not change {name}"
                )
            names.append(path.stem)
    if not names:
        raise ValueError("No new public theorem found in the research commit")
    return sorted(names)


def generate(root, names, jobs):
    def review(name):
        run(
            [
                sys.executable,
                "scripts/run_novelty_prompt.py",
                name,
                "--dangerous",
                "--agent",
                "claude",
                "--output-dir",
                "scripts/reviews",
            ],
            root,
        )

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(review, names))


def validate_reviews(root, names, changed):
    expected = {f"scripts/reviews/{name}.md" for name in names}
    if set(changed) != expected:
        raise ValueError("Postprocessing must change only the task's review files")
    for name in expected:
        path = root / name
        if path.is_symlink() or not path.is_file() or not path.read_text().strip():
            raise ValueError(f"Missing or empty review: {name}")


def finish_pr(repository, number, names):
    for attempt in range(5):
        pr = json.loads(
            authenticated(
                ["gh", "api", f"repos/{repository}/pulls/{number}"], capture=True
            )
        )
        if pr["commits"] == 2:
            break
        if pr["commits"] != 1 or attempt == 4:
            raise ValueError(
                f"Expected exactly two commits after postprocessing; GitHub reports {pr['commits']}"
            )
        # GitHub can briefly return the pre-push commit count.
        print("Waiting for GitHub to report the reviews commit...", flush=True)
        time.sleep(2)
    links = "\n".join(
        f"- [{name} review](https://github.com/{repository}/blob/{pr['head']['sha']}/scripts/reviews/{name}.md)"
        for name in names
    )
    marker = "<!-- longtails-postprocessing -->"
    body = (pr.get("body") or "").split(marker)[0].rstrip()
    body += f"\n\n{marker}\nTheorem reviews generated successfully.\n\n{links}\n"
    with tempfile.NamedTemporaryFile(mode="w", suffix=".md") as file:
        file.write(body)
        file.flush()
        authenticated(
            [
                "gh",
                "pr",
                "edit",
                str(number),
                "--repo",
                repository,
                "--body-file",
                file.name,
            ]
        )
    if pr["draft"]:
        authenticated(["gh", "pr", "ready", str(number), "--repo", repository])


def postprocess(number, repository, jobs):
    pr = json.loads(
        authenticated(["gh", "api", f"repos/{repository}/pulls/{number}"], capture=True)
    )
    if (
        pr["state"] != "open"
        or pr["head"]["repo"]["full_name"] != repository
        or not pr["head"]["ref"].startswith("agent/")
        or pr["base"]["ref"] != "main"
    ):
        raise ValueError("Expected an open, same-repository agent/* PR targeting main")
    authenticated(["git", "fetch", "origin", pr["base"]["sha"], pr["head"]["sha"]])
    base = pr["base"]["sha"]
    with tempfile.TemporaryDirectory(prefix="postprocess-") as directory:
        worktree = Path(directory) / "task"
        run(["git", "worktree", "add", "--detach", str(worktree), pr["head"]["sha"]])
        try:
            count = commit_count(worktree, base)
            if count == 2:
                changed = run(
                    ["git", "diff", "--name-only", "HEAD^", "HEAD"], worktree, True
                ).splitlines()
                run(["git", "checkout", "--detach", "HEAD^"], worktree)
                names = task_theorems(worktree, base)
                run(["git", "checkout", "--detach", pr["head"]["sha"]], worktree)
                validate_reviews(worktree, names, changed)
                finish_pr(repository, number, names)
                return
            if count != 1:
                raise ValueError(
                    f"Expected exactly one research commit before postprocessing; found {count}"
                )
            names = task_theorems(worktree, base)
            cache = os.environ.get("LONGTAILS_LAKE_CACHE")
            if cache:
                if Path(cache).is_dir():
                    shutil.copytree(cache, worktree / ".lake")
                run(["lake", "exe", "cache", "get"], worktree)
            generate(worktree, names, jobs)
            if cache:
                shutil.copytree(worktree / ".lake", cache, dirs_exist_ok=True)
            changed = run(
                ["git", "diff", "--name-only", "HEAD"], worktree, True
            ).splitlines()
            changed += run(
                ["git", "ls-files", "--others", "--exclude-standard"], worktree, True
            ).splitlines()
            validate_reviews(worktree, names, changed)
            run(["git", "add", "--", *changed], worktree)
            run(
                [
                    "git",
                    "-c",
                    "user.name=LongTails postprocessing",
                    "-c",
                    "user.email=longtails-postprocessing@users.noreply.github.com",
                    "commit",
                    "-m",
                    "Add task novelty reviews",
                ],
                worktree,
            )
            if commit_count(worktree, base) != 2:
                raise ValueError("Expected exactly two commits after postprocessing")
            authenticated(
                ["git", "push", "origin", f"HEAD:refs/heads/{pr['head']['ref']}"],
                worktree,
            )
            finish_pr(repository, number, names)
        finally:
            run(["git", "worktree", "remove", "--force", str(worktree)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pr", type=int, required=True)
    parser.add_argument(
        "--repo", default=os.environ.get("GITHUB_REPOSITORY", "k3nfalt/longtails")
    )
    parser.add_argument("--jobs", type=int, default=10)
    args = parser.parse_args()
    if args.jobs < 1 or args.pr < 1:
        parser.error("PR number and jobs must be positive")
    try:
        postprocess(args.pr, args.repo, args.jobs)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Postprocessing failed: {error}\n")


if __name__ == "__main__":
    main()
