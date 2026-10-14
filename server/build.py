import argparse
import base64
import json
import subprocess
import sys
from datetime import datetime, timezone
from html import escape
from pathlib import Path
from urllib.parse import urlsplit

from server.generation_commits import verified_output

ROOT = Path(__file__).resolve().parent
project_name = "LongTails"


def repository_url():
    origin = subprocess.run(
        ["git", "remote", "get-url", "origin"],
        cwd=ROOT.parent,
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()
    if origin.startswith("git@github.com:"):
        origin = "ssh://git@github.com/" + origin.split(":", 1)[1]
    url = urlsplit(origin)
    path = url.path.rstrip("/").removesuffix(".git").strip("/")
    if url.hostname != "github.com" or len(path.split("/")) != 2:
        raise ValueError("Expected origin to be a GitHub repository URL")
    return "https://github.com/" + path


def font_css():
    faces = []
    for filename, family, weight, style in (
        ("manrope.ttf", "Manrope", 700, "normal"),
        ("texgyretermes-regular.otf", "TeX Gyre Termes", 400, "normal"),
        ("texgyretermes-bold.otf", "TeX Gyre Termes", 700, "normal"),
        ("texgyretermes-italic.otf", "TeX Gyre Termes", 400, "italic"),
        ("texgyretermes-bolditalic.otf", "TeX Gyre Termes", 700, "italic"),
        ("latinmodern-math.otf", "Latin Modern Math", 400, "normal"),
    ):
        encoded = base64.b64encode((ROOT / "fonts" / filename).read_bytes()).decode(
            "ascii"
        )
        extension = Path(filename).suffix[1:]
        format = "truetype" if extension == "ttf" else "opentype"
        faces.append(
            f'@font-face{{font-family:"{family}";font-weight:{weight};'
            f'font-style:{style};src:url(data:font/{extension};base64,{encoded}) format("{format}");}}'
        )
    return "\n".join(faces)


def description_html(text, format, bibliography=None):
    command = ["pandoc", "--from=" + format, "--to=json"]
    if bibliography is not None:
        command += ["--citeproc", "--bibliography=" + str(bibliography)]
    document = json.loads(
        subprocess.run(
            command, input=text, text=True, capture_output=True, check=True
        ).stdout
    )

    def clean(node):
        if isinstance(node, dict):
            if node.get("t") == "RawInline":
                return {"t": "Str", "c": ""}
            if node.get("t") == "RawBlock":
                return {"t": "Plain", "c": []}
            if node.get("t") in ("Link", "Image"):
                target = node["c"][-1][0]
                if not (
                    target.startswith("#")
                    or (
                        urlsplit(target).scheme.lower() in ("http", "https")
                        and urlsplit(target).hostname
                    )
                ):
                    return {"t": "Span", "c": [["", [], []], clean(node["c"][1])]}
            return {key: clean(value) for key, value in node.items()}
        if isinstance(node, list):
            # Pandoc attributes: identifier, classes, arbitrary key/value pairs.
            if (
                len(node) == 3
                and isinstance(node[0], str)
                and isinstance(node[1], list)
                and isinstance(node[2], list)
            ):
                return [node[0], node[1], []]
            return [clean(value) for value in node]
        return node

    return subprocess.run(
        [
            "pandoc",
            "--from=json",
            "--to=html5",
            "--mathml",
            "--shift-heading-level-by=1",
        ],
        input=json.dumps(clean(document)),
        text=True,
        capture_output=True,
        check=True,
    ).stdout


def load_references(catalogs=None):
    references = {}
    for path in sorted((ROOT / "Theorems/References").rglob("*.json")):
        if path.name.endswith((".hashes.json", ".commit.json")) or any(
            part.startswith(".references-") for part in path.parts
        ):
            continue
        report = json.loads(path.read_text(encoding="utf-8"))
        if catalogs is not None and isinstance(report.get("catalog"), dict):
            catalog = dict(report["catalog"])
            legacy = catalog.pop("priority", None)
            if "setup_category" not in catalog and legacy:
                label = {"core": "classical", "active_research": "non_standard"}.get(
                    legacy.get("suggested"), "needs_review"
                )
                catalog["setup_category"] = {
                    "label": label,
                    "reason": "Imported from the previous priority classification; category review pending. "
                    + legacy.get("reason", ""),
                }
            catalogs[report["setup"]] = catalog
        for result in report["results"]:
            text = result["references"].strip()
            html = (
                ""
                if text == "None"
                else description_html(
                    text,
                    "markdown_strict-raw_html+tex_math_dollars+tex_math_single_backslash+autolink_bare_uris",
                )
            )
            status = result.get(
                "match_status", "none" if text == "None" else "unassessed"
            )
            references[(report["setup"], result["module"], result["theorem"])] = (
                html,
                status,
            )
    return references


def setup_modification_dates(files):
    history = subprocess.run(
        [
            "git",
            "log",
            "--format=%ct",
            "--name-only",
            "--no-renames",
            "--",
            "LongTails/Setups",
        ],
        cwd=ROOT.parent,
        text=True,
        capture_output=True,
        check=True,
    ).stdout
    modified = subprocess.run(
        ["git", "diff", "--name-only", "HEAD", "--", "LongTails/Setups"],
        cwd=ROOT.parent,
        text=True,
        capture_output=True,
        check=True,
    ).stdout.splitlines()
    committed = {}
    timestamp = None
    for line in history.splitlines():
        if line.isdigit():
            timestamp = int(line)
        elif line and timestamp is not None:
            committed.setdefault(line, timestamp)
    dates = {}
    for path in files:
        relative = path.relative_to(ROOT.parent).as_posix()
        timestamp = (
            path.stat().st_mtime
            if relative in modified or relative not in committed
            else committed[relative]
        )
        dates[path] = datetime.fromtimestamp(timestamp, timezone.utc).isoformat()
    return dates


def setup_stale(path, rows):
    outputs = [
        ROOT / "Setups/Descriptions" / (path.stem + ".tex"),
        ROOT / "Theorems/References" / (path.stem + ".json"),
    ]
    outputs += [
        ROOT
        / "Theorems/Descriptions"
        / (row["module"].removeprefix("LongTails.Theorems.").replace(".", "/") + ".tex")
        for row in rows
    ]
    return any(not verified_output(output, check_commit=True) for output in outputs)


def review_directory(value):
    path = Path(value).expanduser().resolve()
    if not path.is_dir():
        raise argparse.ArgumentTypeError("Reviews path must be an existing directory")
    if not path.is_relative_to(ROOT.parent):
        raise argparse.ArgumentTypeError(
            "Reviews directory must be inside the repository for published links"
        )
    return path


def load_comparison_tables(directory):
    if directory is None:
        return {}
    directory = Path(directory).expanduser().resolve()
    bibliography = directory / "results_table.bib"
    if not (directory / "tables").is_dir() or not bibliography.is_file():
        raise ValueError("--tables-dir must contain tables/ and results_table.bib")
    return {
        path.stem: description_html(
            path.read_text(encoding="utf-8"), "latex", bibliography
        )
        for path in sorted((directory / "tables").glob("*.tex"))
    }


def render(
    regenerate_all=False,
    jobs=1,
    model=None,
    *,
    generate_descriptions=False,
    reviews_dir=None,
    tables_dir=None,
):
    reviews_dir = review_directory(reviews_dir) if reviews_dir is not None else None
    comparisons = load_comparison_tables(tables_dir)
    if jobs < 1:
        raise ValueError("jobs must be at least 1")
    for module, supports_model in (
        ("server.Setups.create_latex_description", True),
        ("server.Theorems.create_theorem_description", False),
        ("server.Theorems.create_references", True),
    ):
        if supports_model and not (generate_descriptions or regenerate_all):
            continue
        command = [sys.executable, "-m", module]
        if model and supports_model:
            command += ["--model", model]
        if regenerate_all:
            command.append("--regenerate-all")
        if supports_model:
            command += ["--jobs", str(jobs)]
        subprocess.run(command, cwd=ROOT.parent, check=True)
    theorems = json.loads((ROOT / "theorems.json").read_text(encoding="utf-8"))
    catalogs = {}
    references = load_references(catalogs)
    theorems.sort(key=lambda row: (row["module"], row["theorem"]))
    for theorem in theorems:
        theorem["referencesHtml"], theorem["referenceMatch"] = references.get(
            (theorem["setup"], theorem["module"], theorem["theorem"]),
            (None, "unassessed"),
        )
        relative = (
            theorem["module"].removeprefix("LongTails.Theorems.").replace(".", "/")
        )
        review = (
            reviews_dir / (theorem["module"].split(".")[-1] + ".md")
            if reviews_dir
            else None
        )
        theorem["reviewPath"] = (
            review.relative_to(ROOT.parent).as_posix()
            if review is not None and review.is_file()
            else None
        )
        formula = ROOT / "Theorems/Descriptions" / (relative + ".tex")
        theorem["formulaHtml"] = (
            description_html(formula.read_text(encoding="utf-8"), "latex")
            if formula.exists()
            else None
        )
    files = sorted((ROOT.parent / "LongTails/Setups").glob("*.lean"))
    modified_dates = setup_modification_dates(files)
    setups = []
    for path in files:
        description = ROOT / "Setups/Descriptions" / path.stem
        rows = [
            row for row in theorems if row["setup"] == "LongTails.Setups." + path.stem
        ]
        setups.append(
            {
                "id": path.stem,
                "title": path.name,
                "filename": path.name,
                "modifiedAt": modified_dates[path],
                "stale": setup_stale(path, rows),
                "catalog": catalogs.get("LongTails.Setups." + path.stem),
                "descriptionHtml": (
                    description_html(
                        description.with_suffix(".tex").read_text(encoding="utf-8"),
                        "latex",
                    )
                    if description.with_suffix(".tex").exists()
                    else "<p>Description not generated.</p>"
                ),
                "theorems": rows,
                "comparisonHtml": comparisons.get(path.stem),
                "source": path.read_text(encoding="utf-8"),
            }
        )
    data = {
        "project_name": project_name,
        "repository_url": repository_url(),
        "setups": setups,
        "template": (ROOT.parent / "LongTails/Template.lean").read_text(
            encoding="utf-8"
        ),
    }
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c")
    return (
        (ROOT / "template.html")
        .read_text(encoding="utf-8")
        .replace("__PROJECT_NAME__", escape(project_name))
        .replace("__CATALOG_DATA__", payload)
        .replace("__FONT_FACES__", font_css())
        .replace(
            "__LOGO_DATA__",
            base64.b64encode((ROOT / "logo.png").read_bytes()).decode("ascii"),
        )
        .replace(
            "__ICON_DATA__",
            base64.b64encode((ROOT / "mini-logo.png").read_bytes()).decode("ascii"),
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build the website.")
    parser.add_argument(
        "--generate-descriptions",
        action="store_true",
        help="Use Codex to generate missing setup descriptions and reference reports; keep existing files.",
    )
    parser.add_argument(
        "--regenerate-all",
        action="store_true",
        help="Regenerate all descriptions, theorem metadata, and reference reports, including existing files (uses Codex).",
    )

    parser.add_argument("--model", help="Codex model (default: your CLI configuration)")
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Maximum parallel workers per generation stage (default: 1).",
    )
    parser.add_argument(
        "--reviews-dir",
        type=review_directory,
        help="Repository directory of theorem reviews (omit to build without review links).",
    )
    parser.add_argument(
        "--tables-dir",
        type=Path,
        help="Generated table directory containing tables/ and results_table.bib (optional).",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be at least 1")
    page = render(
        args.regenerate_all,
        args.jobs,
        args.model,
        generate_descriptions=args.generate_descriptions,
        reviews_dir=args.reviews_dir,
        tables_dir=args.tables_dir,
    )
    target = ROOT / "index.html"
    target.write_text(page, encoding="utf-8")
    print(f"Built {target}")
