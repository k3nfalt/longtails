import http.client
import json
import os
import platform
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request
from pathlib import Path, PurePosixPath
from urllib.parse import quote

REPOSITORY = "k3nfalt/longtails"
CONFIG = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")


def open_url(url):
    request = urllib.request.Request(url, headers={"User-Agent": "longtails-build"})
    return urllib.request.urlopen(request, timeout=60)


def compatible(root, commit):
    if subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ).returncode:
        return False
    return all(
        subprocess.check_output(["git", "show", f"{commit}:{name}"], cwd=root)
        == (root / name).read_bytes()
        for name in CONFIG
    )


def unpack_cache(archive, root, staging):
    build = root / ".lake/build"
    if (
        (root / ".lake").is_symlink()
        or build.is_symlink()
        or any(path.is_symlink() for path in build.rglob("*"))
    ):
        raise ValueError("Build directory contains symlinks")

    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        for member in members:
            path = PurePosixPath(member.name)
            if (
                path.is_absolute()
                or ".." in path.parts
                or not (member.isfile() or member.isdir())
                or not (
                    member.name in CONFIG
                    or path.is_relative_to(PurePosixPath(".lake/build"))
                )
            ):
                raise ValueError(f"Unsafe cache entry: {member.name}")
        for name in CONFIG:
            if not tar.getmember(name).isfile():
                raise ValueError(f"Invalid cache configuration: {name}")
            with tar.extractfile(name) as source:
                if source.read() != (root / name).read_bytes():
                    raise ValueError(f"Cache configuration differs: {name}")
        for member in members:
            if member.name in CONFIG or member.isdir():
                continue
            target = staging / member.name
            target.parent.mkdir(parents=True, exist_ok=True)
            with tar.extractfile(member) as source, target.open("wb") as dest:
                shutil.copyfileobj(source, dest)
            target.chmod(member.mode & 0o777)
            os.utime(target, (member.mtime, member.mtime))

    shutil.copytree(staging / ".lake/build", build, dirs_exist_ok=True)


def find_cache(root):
    page = 1
    while True:
        with open_url(
            f"https://api.github.com/repos/{REPOSITORY}/releases?per_page=100&page={page}"
        ) as response:
            releases = json.load(response)
        if not releases:
            return None
        for release in releases:
            if release["draft"] or not release["tag_name"].startswith("nightly-"):
                continue
            for asset in release["assets"]:
                match = re.fullmatch(
                    r"lean-build-Linux-X64-([0-9a-f]{40})\.tar\.gz", asset["name"]
                )
                if match and compatible(root, match[1]):
                    return release["tag_name"], asset["name"]
        page += 1


def restore_cache(root):
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        print("Nightly cache supports Linux x64 only; building normally.", flush=True)
        return
    try:
        cache = find_cache(root)
        if cache is None:
            print("No compatible nightly cache found; building normally.", flush=True)
            return
        tag, name = cache
        print(f"Restoring nightly cache from {tag}...", flush=True)
        url = (
            f"https://github.com/{REPOSITORY}/releases/download/"
            f"{quote(tag, safe='')}/{name}"
        )
        with tempfile.TemporaryDirectory(prefix="longtails-cache-") as temp:
            staging = Path(temp)
            archive = staging / "build.tar.gz"
            with open_url(url) as response, archive.open("wb") as dest:
                shutil.copyfileobj(response, dest)
            unpack_cache(archive, root, staging)
        print(f"Restored nightly cache from {tag}.", flush=True)
    except (
        OSError,
        EOFError,
        ValueError,
        KeyError,
        http.client.HTTPException,
        tarfile.TarError,
        subprocess.CalledProcessError,
    ) as error:
        print(f"Nightly cache unavailable ({error}); building normally.", flush=True)
