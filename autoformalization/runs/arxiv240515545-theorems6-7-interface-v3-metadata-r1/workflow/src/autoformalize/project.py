"""Small run projects with pinned, demand-copied LongTails dependencies."""

import re
from pathlib import Path

from .common import checked, digest, read_json, require, scoped, write_json
from .layout import CATEGORIES, adapt_comparator, adapt_metadata

MANIFEST = "autoformalization-project.json"
SUPPORT = (
    "AGENTS.md",
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "run_comparator.py",
    "tools/ConvergenceMetadata.lean",
    "tools/RunLinterNoDocString.lean",
    "server/Theorems/BudgetLatex.lean",
    "server/Theorems/create_theorem_description.py",
)


def compact_manifest(project):
    path = Path(project) / MANIFEST
    return read_json(path) if path.is_file() else None


def source_inventory(repository):
    repository = Path(repository)
    names = checked(["git", "ls-files", "-z"], repository).split("\0")
    return {n: digest(scoped(repository, n).read_bytes()) for n in names if n}


def materialize(project, roots):
    project = Path(project)
    metadata = compact_manifest(project)
    require(metadata is not None, "Missing compact project manifest")
    queue, seen, pending = list(roots), set(), {}
    while queue:
        relative = queue.pop()
        if relative in seen or external_module(relative):
            continue
        seen.add(relative)
        require(
            relative not in {"LongTails.lean", "outputs.lean"},
            "Import specific modules, not the whole library",
        )
        path = scoped(project, relative)
        if path.is_file():
            raw = path.read_bytes()
            if relative.startswith("LongTails/"):
                require(
                    digest(raw) == metadata["repository_files"].get(relative),
                    "Copied dependency changed: " + relative,
                )
        else:
            require(
                relative.startswith("LongTails/"),
                "Missing generated dependency: " + relative,
            )
            expected = metadata["repository_files"].get(relative)
            require(expected is not None, "Unknown pinned dependency: " + relative)
            raw = scoped(Path(metadata["repository"]), relative).read_bytes()
            require(digest(raw) == expected, "Pinned dependency changed: " + relative)
            pending[relative] = raw
        for module in imports(raw.decode("utf-8")):
            if module in {"LongTails", "outputs"} or module.startswith(
                ("LongTails.", "outputs.")
            ):
                queue.append(module.replace(".", "/") + ".lean")
    added = {}
    try:
        for relative, raw in pending.items():
            path = scoped(project, relative)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            added[relative] = digest(raw)
    except BaseException:
        for relative in added:
            scoped(project, relative).unlink()
        raise
    return added


def sync_index(project, check=False):
    project = Path(project)
    modules = sorted(
        p.relative_to(project).with_suffix("").as_posix().replace("/", ".")
        for p in (project / "outputs").rglob("*.lean")
    )
    source = "".join("import " + m + "\n" for m in modules)
    path = project / "outputs.lean"
    if check:
        require(
            path.read_text(encoding="utf-8") == source, "Generated output index changed"
        )
    else:
        path.write_text(source, encoding="utf-8", newline="\n")


def initialize_compact(repository, destination, cache=None):
    repository, destination = Path(repository).resolve(), Path(destination)
    inventory = source_inventory(repository)
    for name in (*SUPPORT, "LongTails/Template.lean"):
        require(name in inventory, "Missing pinned repository resource: " + name)
    commit = checked(["git", "rev-parse", "HEAD"], repository)
    destination.mkdir(parents=True)
    for category in CATEGORIES:
        (destination / "outputs" / category).mkdir(parents=True)
    for name in SUPPORT:
        raw = scoped(repository, name).read_bytes()
        require(digest(raw) == inventory[name], "Resource changed during copy: " + name)
        path = scoped(destination, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    config_path = destination / "lakefile.toml"
    config = config_path.read_text(encoding="utf-8")
    for old, new in [
        ('defaultTargets = ["LongTails"]', 'defaultTargets = ["outputs"]'),
        ('needs = ["LongTails"]', 'needs = ["outputs"]'),
        ('roots = ["BudgetLatex", "TestBudgetLatex"]', 'roots = ["BudgetLatex"]'),
    ]:
        require(config.count(old) == 1, "Unsupported pinned Lake configuration: " + old)
        config = config.replace(old, new)
    config += '\n[[lean_lib]]\nname = "outputs"\nglobs = ["outputs.*"]\n'
    config += (
        '\n[[lean_exe]]\nname = "runOutputStyle"\nroot = "RunOutputStyle"\n'
        'srcDir = ".lake/style-check"\nsupportInterpreter = true\nweakLinkArgs = ["-lLake"]\n'
    )
    config_path.write_text(config, encoding="utf-8", newline="\n")
    for relative, adapt in [
        ("run_comparator.py", adapt_comparator),
        ("tools/ConvergenceMetadata.lean", adapt_metadata),
    ]:
        path = destination / relative
        path.write_text(
            adapt(path.read_text(encoding="utf-8")), encoding="utf-8", newline="\n"
        )
    linter = destination / "tools/RunLinterNoDocString.lean"
    linter.write_text(
        linter.read_text(encoding="utf-8")
        .replace("`LongTails", "`outputs")
        .replace("in LongTails", "in outputs"),
        encoding="utf-8",
        newline="\n",
    )
    policy = Path(__file__).resolve().parents[2]
    (destination / "AGENTS.md").write_text(
        "Read "
        + str(policy / "AGENTS.md")
        + " and "
        + str(policy / "WORKFLOW.md")
        + ".\n"
        "Explicit Lean output contract: "
        + str(policy / "OUTPUT_CONTRACT.md")
        + ".\n"
        "All output and style requirements are in the supplied workflow policies.\n"
        "Do not infer additional requirements from repository-root AGENTS.md or examples.\n"
        "Generate only outputs/{Algorithms,Setups,Proofs,Theorems} modules (outputs.*).\n"
        "LongTails/ contains only pinned dependencies; it is read-only. No library alias.\n"
        "Build explicit output modules or outputs, never the whole LongTails library.\n"
        "All restored review, freeze and proof gates remain mandatory.\n",
        encoding="utf-8",
    )
    (destination / "build.sh").write_text(
        '#!/usr/bin/env bash\nset -euo pipefail\ncd "$(dirname "${BASH_SOURCE[0]}")"\nexec lake build "$@"\n',
        encoding="utf-8",
    )
    metadata = {
        "schema": 1,
        "layout": "restored-outputs-v1",
        "repository": str(repository),
        "repository_commit": commit,
        "snapshot": digest(inventory),
        "repository_files": {
            p: h
            for p, h in inventory.items()
            if p.startswith("LongTails/") and p.endswith(".lean")
        },
        "support_sources": {p: inventory[p] for p in SUPPORT},
    }
    write_json(destination / MANIFEST, metadata)
    materialize(
        destination, ["LongTails/Template.lean", "server/Theorems/BudgetLatex.lean"]
    )
    sync_index(destination)
    from .lean import repository_files

    metadata["initial_files"] = {
        p: h for p, h in repository_files(destination).items() if p != MANIFEST
    }
    write_json(destination / MANIFEST, metadata)
    if cache:
        cache = Path(cache).resolve()
        require(cache.is_dir(), "Package cache directory does not exist")
        (destination / ".lake").mkdir(exist_ok=True)
        (destination / ".lake/packages").symlink_to(cache, target_is_directory=True)
    return commit


def external_module(relative):
    """Recognize plan file identities supplied by pinned packages or the toolchain."""
    return (
        re.fullmatch(r"(?:Mathlib|Init|Lean|Std)(?:/[A-Za-z0-9_]+)+\.lean", relative)
        is not None
    )


def header_import_text(source):
    """Erase header comments and stop before ordinary declaration bodies."""
    out = []
    i, depth, string, line_started = 0, 0, False, False
    while i < len(source):
        char = source[i]
        pair = source[i : i + 2]
        if char == "\n":
            line_started = False
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            if char == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 2
            else:
                string = char != '"'
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif char == '"':
            if not line_started:
                return "".join(out)
            string = True
            out.append(" ")
            i += 1
        else:
            if not line_started and not char.isspace() and char != "\ufeff":
                token = re.match(r"[A-Za-z_][A-Za-z0-9_]*", source[i:])
                if not token or token.group() not in {
                    "module",
                    "prelude",
                    "public",
                    "meta",
                    "import",
                }:
                    return "".join(out)
                line_started = True
            out.append(char)
            i += 1
    if depth:
        raise ValueError(
            "Unterminated Lean source comment; cache import graph unavailable"
        )
    return "".join(out)


def imports(source):
    result = []
    for line in header_import_text(source).splitlines():
        if re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\b", line):
            body = re.sub(
                r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?", "", line
            ).strip()
            names = body.split()
            require(
                names
                and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", n) for n in names),
                "Unsupported Lean import header",
            )
            result.extend(names)
    return result
