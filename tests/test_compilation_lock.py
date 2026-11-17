import fcntl
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import run_research_prompt

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "infra/compilation_lock.py"


class CompilationLockTests(unittest.TestCase):
    def test_waits_for_shared_lock(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "compilation.lock"
            environment = {**os.environ, "LONGTAILS_COMPILATION_LOCK": str(lock_path)}
            environment.pop("LONGTAILS_COMPILATION_LOCK_HELD", None)
            with lock_path.open("a") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                with subprocess.Popen(
                    [
                        sys.executable,
                        str(WRAPPER),
                        sys.executable,
                        "-c",
                        "print('compiled')",
                    ],
                    env=environment,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                ) as process:
                    try:
                        self.assertIn(
                            "Waiting for compilation lock:", process.stderr.readline()
                        )
                        with self.assertRaises(subprocess.TimeoutExpired):
                            process.communicate(timeout=0.2)
                    finally:
                        fcntl.flock(lock, fcntl.LOCK_UN)
                    stdout, stderr = process.communicate(timeout=10)
                    self.assertEqual(process.returncode, 0, stderr)
                    self.assertEqual(stdout, "compiled\n")

    def test_nested_command_and_failure_release(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "compilation.lock"
            environment = {**os.environ, "LONGTAILS_COMPILATION_LOCK": str(lock_path)}
            environment.pop("LONGTAILS_COMPILATION_LOCK_HELD", None)
            prefix = [sys.executable, str(WRAPPER)]
            result = subprocess.run(
                [*prefix, *prefix, sys.executable, "-c", "raise SystemExit(7)"],
                env=environment,
                capture_output=True,
                timeout=10,
            )
            self.assertEqual(result.returncode, 7, result.stderr)
            with lock_path.open("a") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_runner_option(self):
        for enabled in (False, True):
            with (
                self.subTest(enabled=enabled),
                tempfile.TemporaryDirectory() as directory,
            ):
                compiler_bin = None

                def run(command, **kwargs):
                    nonlocal compiler_bin
                    environment = kwargs["env"]
                    self.assertEqual("LONGTAILS_COMPILER_BIN" in environment, enabled)
                    if enabled:
                        compiler_bin = Path(environment["LONGTAILS_COMPILER_BIN"])
                        self.assertEqual(
                            environment["PATH"].split(os.pathsep)[0], str(compiler_bin)
                        )
                        self.assertEqual(
                            environment["LONGTAILS_COMPILATION_LOCK"],
                            str(Path(directory) / "longtails-compilation.lock"),
                        )
                        for tool in ("lake", "lean"):
                            self.assertTrue(os.access(compiler_bin / tool, os.X_OK))
                    return subprocess.CompletedProcess(command, 0)

                with (
                    patch.dict(os.environ, {"PATH": "/usr/bin"}, clear=True),
                    patch.object(
                        run_research_prompt.shutil,
                        "which",
                        return_value="/usr/bin/true",
                    ),
                    patch.object(
                        run_research_prompt.subprocess,
                        "check_output",
                        side_effect=[
                            f"worktree {ROOT}\nHEAD abc\n".encode(),
                            directory,
                        ],
                    ),
                    patch.object(
                        run_research_prompt.subprocess, "run", side_effect=run
                    ) as execute,
                ):
                    result = run_research_prompt.main(
                        ["--serialize-compilation"] if enabled else []
                    )
                    self.assertEqual(result, 0)
                    self.assertEqual(execute.call_count, 2)
                if compiler_bin is not None:
                    self.assertFalse(compiler_bin.exists())


if __name__ == "__main__":
    unittest.main()
