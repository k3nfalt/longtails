"""Strict records, atomic persistence and scoped paths."""

import hashlib
import json
import os
import subprocess
import tempfile
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath


class WorkflowError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise WorkflowError(message)


def canonical(value):
    return json.dumps(
        value,
        sort_keys=True,
        ensure_ascii=False,
        separators=(",", ":"),
        allow_nan=False,
    )


def digest(value):
    raw = value if isinstance(value, bytes) else canonical(value).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def _unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    raw = Path(path).read_bytes()
    require(len(raw) <= 64_000_000, "Record exceeds 64 MB")
    try:
        return json.loads(
            raw,
            object_pairs_hook=_unique,
            parse_constant=lambda x: (_ for _ in ()).throw(
                WorkflowError(f"Nonfinite JSON: {x}")
            ),
        )
    except (ValueError, UnicodeError) as exc:
        raise WorkflowError(f"Invalid JSON in {Path(path).name}: {exc}") from exc


def write_json(path, value, *, compact=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=".write-", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as out:
            out.write(
                (
                    canonical(value)
                    if compact
                    else json.dumps(
                        value, indent=2, ensure_ascii=False, allow_nan=False
                    )
                )
                + "\n"
            )
            out.flush()
            os.fsync(out.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def scoped(root, relative):
    require(isinstance(relative, str) and relative, "Empty relative path")
    rel = PurePosixPath(relative)
    require(
        not rel.is_absolute()
        and ".." not in rel.parts
        and "\\" not in relative
        and ":" not in relative,
        f"Unsafe relative path: {relative}",
    )
    result = (Path(root) / relative).resolve()
    require(
        result.is_relative_to(Path(root).resolve()), f"Path escapes root: {relative}"
    )
    return result


def text(value, label):
    require(
        isinstance(value, str) and bool(value.strip()), f"{label} must be nonempty text"
    )
    return value


def fields(value, required, optional=()):
    require(isinstance(value, dict), "Expected an object")
    require(
        set(required) <= value.keys(),
        f"Missing fields: {sorted(set(required) - value.keys())}",
    )
    require(
        value.keys() <= set(required) | set(optional),
        f"Unknown fields: {sorted(value.keys() - set(required) - set(optional))}",
    )


@contextmanager
def locked(directory):
    path = Path(directory) / ".lock"
    try:
        fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError as exc:
        raise WorkflowError(
            "Run is locked. Verify the owning process has stopped before removing .lock."
        ) from exc
    try:
        with os.fdopen(fd, "w") as out:
            json.dump({"pid": os.getpid(), "created": now()}, out)
        yield
    finally:
        path.unlink(missing_ok=True)


def command(args, cwd, *, timeout=600, input_text=None, env=None):
    try:
        result = subprocess.run(
            args,
            cwd=cwd,
            input=input_text,
            text=True,
            encoding="utf-8",
            errors="replace",
            capture_output=True,
            timeout=timeout,
            env=env,
        )
    except subprocess.TimeoutExpired as exc:

        def decode(value):
            return (
                value.decode("utf-8", errors="replace")
                if isinstance(value, bytes)
                else (value or "")
            )

        return {
            "command": args,
            "exit_code": 124,
            "stdout": decode(exc.stdout),
            "stderr": decode(exc.stderr)
            + f"\nCommand timed out after {timeout} seconds",
        }
    except OSError as exc:
        raise WorkflowError(f"Command did not complete: {args[0]}: {exc}") from exc
    return {
        "command": args,
        "exit_code": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr,
    }


def checked(args, cwd, **kwargs):
    result = command(args, cwd, **kwargs)
    require(result["exit_code"] == 0, result["stdout"] + result["stderr"])
    return result["stdout"].strip()
