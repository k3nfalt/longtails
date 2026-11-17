import fcntl
import os
import subprocess
import sys


def main():
    command = sys.argv[1:]
    lock_path = os.environ["LONGTAILS_COMPILATION_LOCK"]
    if os.environ.get("LONGTAILS_COMPILATION_LOCK_HELD") == lock_path:
        return subprocess.run(command, check=False).returncode
    with open(lock_path, "a") as lock:
        print(f"Waiting for compilation lock: {lock_path}", file=sys.stderr, flush=True)
        fcntl.flock(lock, fcntl.LOCK_EX)
        environment = os.environ.copy()
        # Nested `lake env lean` calls already run under this lock.
        environment["LONGTAILS_COMPILATION_LOCK_HELD"] = lock_path
        return subprocess.run(
            command,
            env=environment,
            pass_fds=(lock.fileno(),),
            check=False,
        ).returncode


if __name__ == "__main__":
    sys.exit(main())
