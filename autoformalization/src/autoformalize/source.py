"""Original-file intake adapted from notebook 01's source-preserving reader."""

import re
from pathlib import Path

from .common import WorkflowError, digest, fields, require, scoped, text


def mask_comments(value):
    chars = list(value)
    for match in re.finditer("%", value):
        start = match.start()
        index = start - 1
        if chars[start] != "%":
            continue
        while index >= 0 and value[index] == "\\":
            index -= 1
        if (start - 1 - index) % 2 == 0:
            end = start
            while end < len(value) and value[end] not in "\r\n":
                end += 1
            chars[start:end] = " " * (end - start)
    return "".join(chars)


def load_package(root, entry, extras=()):
    root = Path(root).resolve()
    require(
        isinstance(extras, (list, tuple)) and all(isinstance(e, str) for e in extras),
        "Extra source files must be a list",
    )
    files, visiting = {}, set()

    def visit(relative):
        path = scoped(root, relative)
        key = path.relative_to(root).as_posix()
        require(key not in visiting, f"Cyclic TeX include: {key}")
        if key in files:
            return
        require(path.is_file(), f"Missing source include: {key}")
        raw = path.read_bytes()
        require(
            len(raw) <= 8_000_000 and len(files) < 256,
            "Source package exceeds intake limits",
        )
        try:
            value = raw.decode("utf-8")
        except UnicodeError as exc:
            raise WorkflowError(f"Source must be UTF-8: {key}") from exc
        visiting.add(key)
        files[key] = {"path": key, "sha256": digest(raw), "text": value}
        active = mask_comments(value)
        references = []
        for match in re.finditer(
            r"\\(?:input|include|subfile)\b\s*(?:\{([^{}\r\n]*)\}|([^\s%{}]+))", active
        ):
            references.append((root, (match.group(1) or match.group(2)).strip()))
        for match in re.finditer(
            r"\\(import|subimport)\s*\{([^{}]*)\}\s*\{([^{}]*)\}", active
        ):
            parent = root if match.group(1) == "import" else path.parent
            references.append((parent / match.group(2), match.group(3).strip()))
        for parent, name in references:
            require(
                name and not any(c in name for c in "\\#$"),
                "Dynamic include requires an explicitly resolved source package: "
                + name,
            )
            candidate = parent / name
            if not candidate.suffix and not candidate.exists():
                candidate = candidate.with_suffix(".tex")
            candidate = candidate.resolve()
            require(
                candidate.is_relative_to(root), "Source include leaves package root"
            )
            visit(candidate.relative_to(root).as_posix())
        for match in re.finditer(
            r"\\(usepackage|RequirePackage|documentclass)\s*(?:\[[^\]]*\])?\s*\{([^{}]+)\}",
            active,
        ):
            suffix = ".cls" if match.group(1) == "documentclass" else ".sty"
            for name in match.group(2).split(","):
                candidate = (root / (name.strip() + suffix)).resolve()
                require(
                    candidate.is_relative_to(root),
                    "Local style path leaves package root",
                )
                if candidate.is_file():
                    visit(candidate.relative_to(root).as_posix())
        visiting.remove(key)

    visit(entry)
    for extra in extras:
        visit(extra)
    result = {"entry": entry, "files": [files[key] for key in sorted(files)]}
    require(
        sum(len(f["text"].encode("utf-8")) for f in result["files"]) <= 32_000_000,
        "Source package exceeds 32 MB",
    )
    result["id"] = digest(result)
    return result


def spans(source):
    """Stable line references; the original complete file remains available."""
    result = {}
    for file in source["files"]:
        offset = 0
        for number, line in enumerate(file["text"].splitlines(keepends=True), 1):
            if line.strip():
                item = {
                    "file": file["path"],
                    "start": offset,
                    "end": offset + len(line),
                    "line": number,
                    "quote": line,
                }
                key = "src_" + digest({"file_hash": file["sha256"], **item})[:24]
                result[key] = item
            offset += len(line)
    return result


def acquisition(record, original_hash):
    fields(
        record,
        [
            "original_pdf_sha256",
            "searches",
            "outcome",
            "version_comparison",
            "user_warning",
            "transcription_pages",
        ],
    )
    require(
        record["original_pdf_sha256"] == original_hash,
        "Search record belongs to another PDF",
    )
    require(
        record["outcome"] in {"author_tex_found", "transcribed"},
        "Search access failure is not TeX unavailability",
    )
    require(
        isinstance(record["searches"], list) and record["searches"],
        "Live search evidence required",
    )
    for search in record["searches"]:
        fields(search, ["query", "timestamp", "tool", "results"])
        for key in ("query", "timestamp", "tool"):
            text(search[key], key)
        require(isinstance(search["results"], list), "Search results must be a list")
        for result in search["results"]:
            fields(result, ["url", "observation"])
            require(
                result["url"].startswith(("https://", "http://")),
                "Search result needs a web URL",
            )
            text(result["observation"], "search observation")
    text(record["version_comparison"], "paper/target version comparison")
    if record["outcome"] == "transcribed":
        text(record["user_warning"], "warning delivered to user")
        require(
            record["transcription_pages"],
            "Transcription needs original PDF page provenance",
        )
    else:
        require(
            any(s["results"] for s in record["searches"]),
            "Author TeX needs located web source",
        )
    return record
