import fcntl
import subprocess
import sys
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    args = sys.argv[1:]
    lock_path = subprocess.check_output(
        ["git", "rev-parse", "--git-path", "longtails-build.lock"],
        cwd=root,
        text=True,
    ).strip()
    with (root / lock_path).open("a") as lock:
        print(f"Waiting for build lock in {root}...", flush=True)
        fcntl.flock(lock, fcntl.LOCK_EX)
        print(f"Building {root}", flush=True)

        def run(command, check=True):
            return subprocess.run(
                command, cwd=root, check=check, pass_fds=(lock.fileno(),)
            )

        run(["lake", "exe", "cache", "get"])
        if run(["lake", "exe", "mk_all", "--lib", "LongTails"], check=False).returncode:
            run(["lake", "exe", "mk_all", "--lib", "LongTails", "--check"])
        run(["lake", "build", *args])


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
