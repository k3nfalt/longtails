#!/usr/bin/env python3

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from threading import Event, Lock
from urllib.parse import urlsplit

HEADER = "\\begingroup\n"
FOOTER = "\\endgroup\n"

COMPILE_DOCUMENT = r"""\documentclass{article}
\usepackage{amsmath,amssymb,array,booktabs,tabularx,threeparttable,textcomp}
\usepackage[numbers]{natbib}
\usepackage{hyperref}
\usepackage{changepage}
\let\originaltable\table
\let\endoriginaltable\endtable
\renewenvironment{table}[1][tbp]
  {\originaltable[#1]\begin{adjustwidth}{-2.5cm}{-2.5cm}}
  {\end{adjustwidth}\endoriginaltable}
\begin{document}
\input{tables.tex}
\clearpage
\bibliographystyle{plain}
\bibliography{results_table}
\end{document}
"""


def check_compilation(table, bibliography, directory):
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "tables.tex").write_text(table, encoding="utf-8")
    (directory / "results_table.bib").write_text(bibliography, encoding="utf-8")
    (directory / "check.tex").write_text(COMPILE_DOCUMENT, encoding="utf-8")
    with (directory / "compile.log").open("w") as log:
        subprocess.run(
            [
                "latexmk",
                "-gg",
                "-pdf",
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-no-shell-escape",
                "check.tex",
            ],
            cwd=directory,
            stdout=log,
            stderr=subprocess.STDOUT,
            check=True,
        )
    log = (directory / "check.log").read_text(encoding="utf-8", errors="replace")
    if "undefined references" in log or "undefined citations" in log:
        raise ValueError(f"Unresolved LaTeX references; see {directory / 'check.log'}")


def added_rows(original, revised):
    # Page breaks after the table are layout separators, not saved table content.
    separators = r"(\\end\{table\})(?:\s*\\(?:clearpage|newpage)\b)*\s*\Z"
    original = re.sub(separators, r"\1", original)
    revised = re.sub(separators, r"\1", revised)
    if original == revised:
        return ""
    if original.count(r"\bottomrule") != 1 or revised.count(r"\bottomrule") != 1:
        raise ValueError("extending a saved table requires exactly one bottomrule")
    prefix, end = original.split(r"\bottomrule")
    suffix = r"\bottomrule" + end
    if not revised.startswith(prefix) or not revised.endswith(suffix):
        raise ValueError("changed previously saved table content")
    return revised[len(prefix) : -len(suffix)]


def normalize_polish(text):
    # The script owns the outer group; agents may copy its closer before new tables.
    parts = re.split(r"(\\begin\{table\}.*?\\end\{table\})", text, flags=re.S)
    if len(parts) == 1:
        raise ValueError("polish produced no complete tables")
    for index in range(0, len(parts), 2):
        if not re.fullmatch(
            r"(?:\s|\\(?:begingroup|endgroup|clearpage|newpage)\b)*", parts[index]
        ):
            raise ValueError("unexpected content outside polished tables")
        parts[index] = re.sub(r"\\(?:begingroup|endgroup)\b", "", parts[index])
    return HEADER + "".join(parts).strip() + "\n" + FOOTER


def validate_polish(original, revised, original_bib, revised_bib, saved=None):
    original_tables = {row[1]: row[2] for row in split_tables(original)}
    revised_tables = {row[1]: row[2] for row in split_tables(revised)}
    for setup, row in (saved or {}).items():
        if setup not in revised_tables:
            raise ValueError(f"polish removed previously saved table: {setup}")
        try:
            added_rows(row[2], revised_tables[setup])
        except ValueError as error:
            raise ValueError(f"{setup}: {error}") from error
    bib_keys = r"@\w+\s*[{(]\s*([^,]+),"
    if sorted(re.findall(bib_keys, revised_bib)) != sorted(
        re.findall(bib_keys, original_bib)
    ):
        raise ValueError("polish changed bibliography keys")
    # Preserve order within each setup; save_tables sorts the setups by contribution.
    identifiers = r"\\label\{[^}]+\}|\\href\{(?![^}]+/LongTails/Setups/)[^}]+\}"
    setup_links = r"\\href\{[^}]+/LongTails/Setups/[^}]+\}"
    citations = r"\\citep(?:\[[^\]]*\]){0,2}\{([^}]+)\}"
    if (
        not revised.startswith(HEADER)
        or not revised.rstrip().endswith(FOOTER.strip())
        or original_tables.keys() != revised_tables.keys()
        or any(
            re.findall(identifiers, table)
            != re.findall(identifiers, revised_tables[setup])
            or list(dict.fromkeys(re.findall(setup_links, table)))
            != list(dict.fromkeys(re.findall(setup_links, revised_tables[setup])))
            or re.findall(citations, table)
            != re.findall(citations, revised_tables[setup])
            for setup, table in original_tables.items()
        )
    ):
        raise ValueError("polish changed table structure, links, citations or labels")


def split_tables(text):
    body = text.removeprefix(HEADER).removesuffix(FOOTER)
    if not body.strip():
        return []
    labels = list(re.finditer(r"\\label\{tab:([A-Za-z0-9_]+)\}", body))
    starts = [body.rfind(r"\begin{table}", 0, label.start()) for label in labels]
    if (
        not labels
        or any(start < 0 for start in starts)
        or len(set(starts)) != len(starts)
    ):
        raise ValueError("Cannot split tables: expected one tab:SETUP label per setup")
    rows = []
    for index, label in enumerate(labels):
        row = body[
            starts[index] : starts[index + 1] if index + 1 < len(starts) else len(body)
        ].strip()
        theorems = {}
        for link in re.finditer(
            r"\\href\{[^}]+/LongTails/Theorems/([A-Za-z0-9_]+)\.lean\}", row
        ):
            cell_end = re.search(r"(?<!\\)&", row[link.end() :])
            if cell_end is None:
                raise ValueError(f"missing result cell boundary for {link[1]}")
            cell = row[link.end() : link.end() + cell_end.start()]
            score = len(re.findall(r"\\star\b", cell))
            if score > 3 or link[1] in theorems or "/LongTails/Theorems/" in cell:
                raise ValueError(f"invalid or duplicate rating for {link[1]}")
            theorems[link[1]] = score
        if not theorems:
            raise ValueError(f"no theorem ratings found for {label[1]}")
        rows.append((max(theorems.values()), label[1], row, theorems))
    if len({name for _, name, _, _ in rows}) != len(rows):
        raise ValueError("Duplicate setup labels")
    return rows


def bibliography_entries(text):
    matches = list(re.finditer(r"(?m)^@\w+\s*[{(]\s*([^,]+),", text))
    return {
        match[1].strip(): text[
            match.start() : matches[i + 1].start()
            if i + 1 < len(matches)
            else len(text)
        ].strip()
        for i, match in enumerate(matches)
    }


def save_tables(directory, rows, entries, saved=None):
    saved = saved or {}
    additions = {
        setup: added_rows(saved[setup][2], row)
        for _, setup, row, _ in rows
        if setup in saved
    }
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "tables").mkdir(exist_ok=True)
    (directory / "metadata").mkdir(exist_ok=True)
    rows.sort(key=lambda item: (-item[0], item[1]))
    for score, setup, row, theorems in rows:
        if setup in saved:
            if not additions[setup]:
                continue
            row = saved[setup][2].replace(
                r"\bottomrule", additions[setup] + r"\bottomrule", 1
            )
        (directory / "metadata" / f"{setup}.json").write_text(
            json.dumps({"contribution": score, "theorems": theorems}, indent=2) + "\n",
            encoding="utf-8",
        )
        (directory / "tables" / f"{setup}.tex").write_text(
            row.rstrip() + "\n", encoding="utf-8"
        )
    (directory / "results_table.bib").write_text(
        "\n\n".join(entries.values()) + "\n", encoding="utf-8"
    )


def main(argv=None):
    scripts = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(
        description="Summarize existing reviews, one fresh agent session per exact setup, then rank tables.",
        epilog="Pass extra agent arguments after --. No additional literature research.",
    )
    parser.add_argument("--agent", choices=("codex", "omp", "claude"), default="codex")
    parser.add_argument(
        "--dangerous", action="store_true", help="Enable unrestricted agent execution."
    )
    parser.add_argument(
        "--polish",
        action="store_true",
        help="Polish new tables and new rows, preserving previously saved content",
    )
    parser.add_argument(
        "--polish-only",
        action="store_true",
        help="Check compilation of existing output files; saved tables remain untouched",
    )
    parser.add_argument(
        "--jobs", type=int, default=6, help="Parallel sessions (default: 6)"
    )
    parser.add_argument(
        "--setups",
        nargs="+",
        help="Setup basenames to extend with missing reviewed results; existing content is preserved",
    )
    parser.add_argument("--reviews-dir", type=Path, default=scripts / "reviews")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=scripts / "tables",
        help="Destination for tables/SETUP.tex, metadata, and results_table.bib (default: scripts/tables)",
    )
    argv = list(sys.argv[1:] if argv is None else argv)
    split = argv.index("--") if "--" in argv else len(argv)
    args = parser.parse_args(argv[:split])
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if not args.polish_only:
        reviews = args.reviews_dir.expanduser().resolve()
        theorems = sorted((scripts.parent / "LongTails/Theorems").glob("*.lean"))
        if not theorems:
            parser.error("no theorems found in LongTails/Theorems")
        missing = [p.stem for p in theorems if not (reviews / f"{p.stem}.md").is_file()]
        if missing:
            print(
                "WARNING: skipping theorems with missing reviews: "
                + ", ".join(missing),
                file=sys.stderr,
                flush=True,
            )
            theorems = [p for p in theorems if p.stem not in missing]
        if not theorems:
            print("No reviewed theorems to process.", flush=True)
            return 0
        sys.path.insert(0, str(scripts.parent))
        from run_comparator import inspect

        try:
            metadata = inspect(theorems, os.environ.copy())
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            parser.error(f"cannot inspect theorem setups: {error}")
        groups = {}
        for theorem in metadata:
            setup = theorem["setup"].removesuffix(".spec").split(".")[-1]
            path = scripts.parent.joinpath(*theorem["module"].split(".")).with_suffix(
                ".lean"
            )
            groups.setdefault(setup, []).append(path)
        if args.setups:
            unknown = set(args.setups) - groups.keys()
            if unknown:
                parser.error(
                    "no reviewed theorems for setups: " + ", ".join(sorted(unknown))
                )
            groups = {
                name: paths for name, paths in groups.items() if name in args.setups
            }
        for name in groups:
            if not (scripts.parent / f"LongTails/Setups/{name}.lean").is_file():
                parser.error(f"missing setup file for {name}")
        try:
            origin = subprocess.run(
                ["git", "remote", "get-url", "origin"],
                cwd=scripts.parent,
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
            repository_url = "https://github.com/" + path + "/blob/main/"
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            parser.error(f"cannot determine repository URL: {error}")
    output = args.output_dir.expanduser().resolve()
    if output.exists() and not output.is_dir():
        parser.error("--output-dir must be a directory")
    bibliography = output / "results_table.bib"
    table_paths = sorted((output / "tables").glob("*.tex"))
    if args.polish_only:
        if not table_paths or not bibliography.is_file():
            parser.error(
                "--polish-only requires existing tables/*.tex and results_table.bib"
            )
        args.polish = True
    if table_paths and not bibliography.is_file():
        parser.error("existing tables require results_table.bib")
    output.mkdir(parents=True, exist_ok=True)
    prompt = (scripts / "prompts" / "results_table_prompt.md").read_text(
        encoding="utf-8"
    )
    command = {
        "omp": ["omp"] + (["--yolo"] if args.dangerous else []),
        "claude": ["claude", "--print"]
        + (["--dangerously-skip-permissions"] if args.dangerous else []),
        "codex": [
            "codex",
            "exec",
            "-s",
            "danger-full-access" if args.dangerous else "workspace-write",
        ]
        + (["-c", "features.network_proxy=false"] if args.dangerous else []),
    }[args.agent]
    temporary = Path(tempfile.mkdtemp(prefix="longtails-table-"))
    print(f"Logs and row data: {temporary}", flush=True)
    try:
        entries = (
            bibliography_entries(bibliography.read_text(encoding="utf-8"))
            if bibliography.exists()
            else {}
        )
        saved = {}
        for path in table_paths:
            parts = split_tables(path.read_text(encoding="utf-8"))
            if len(parts) != 1 or parts[0][1] != path.stem:
                raise ValueError(f"setup filename and label disagree: {path}")
            saved[path.stem] = parts[0]
        rows = list(saved.values())
    except (OSError, ValueError) as error:
        parser.error(f"cannot load saved tables: {error}")
    if not args.polish_only:
        groups = {
            name: [
                p for p in paths if name not in saved or p.stem not in saved[name][3]
            ]
            for name, paths in groups.items()
        }
        groups = {name: paths for name, paths in groups.items() if paths}
    protected = temporary / "previous-tables.tex"
    protected.write_text(
        HEADER + "\n".join(row[2] for row in saved.values()) + "\n" + FOOTER,
        encoding="utf-8",
    )
    lock, stopped = Lock(), Event()
    completed = 0

    def save():
        save_tables(output, rows, entries, saved)

    save()
    started = time.monotonic()

    def run_agent(task, log_path, label):
        session_started = time.monotonic()
        with log_path.open("w") as log:
            process = subprocess.Popen(
                [*command, *argv[split + 1 :], task],
                cwd=scripts.parent,
                env={**os.environ, "IS_SANDBOX": "1"}
                if args.agent == "claude" and args.dangerous
                else None,
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
            )
            try:
                while True:
                    if stopped.is_set():
                        raise KeyboardInterrupt
                    try:
                        returncode = process.wait(timeout=15)
                        break
                    except subprocess.TimeoutExpired:
                        print(
                            f"RUNNING {label} | {time.monotonic() - session_started:.0f}s elapsed",
                            flush=True,
                        )
            except KeyboardInterrupt:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                if not stopped.is_set():
                    raise
                return False
        if returncode:
            raise ValueError(f"agent exited with status {returncode}")
        return True

    def review(index, setup):
        nonlocal completed
        if stopped.is_set():
            return False
        row_path = temporary / f"{setup}.json"
        log_path = temporary / f"{setup}.log"
        # Each session reads an immutable snapshot while other rows finish.
        with lock:
            previous_bib = temporary / f"{setup}-previous.bib"
            previous_bib.write_text(
                bibliography.read_text(encoding="utf-8"), encoding="utf-8"
            )
        inputs = [
            {
                "theorem": str(p),
                "basename": p.stem,
                "review": str(reviews / f"{p.stem}.md"),
                "review_url": (
                    repository_url
                    + (reviews / f"{p.stem}.md").relative_to(scripts.parent).as_posix()
                    if reviews.is_relative_to(scripts.parent)
                    else (reviews / f"{p.stem}.md").as_uri()
                ),
                "url": repository_url + f"LongTails/Theorems/{p.stem}.lean",
            }
            for p in groups[setup]
        ]
        task = (
            prompt
            + "\n\nDo not change previously saved tables, their metadata, or the existing "
            "bibliography. Generate only the supplied setup's table and write only to "
            "the JSON destination below; the runner will merge the result."
            + f"\n\nSetup: {scripts.parent / 'LongTails/Setups' / (setup + '.lean')}"
            f"\nSetup URL: {repository_url}LongTails/Setups/{setup}.lean"
            f"\nTheorems: {json.dumps(inputs)}"
            f"\nExisting bibliography: {previous_bib}"
            f"\nJSON destination: {row_path}\n"
        )
        if setup in saved:
            task += (
                f"\nEXTEND EXISTING TABLE: Read {protected} for this setup's saved table. "
                "The supplied theorems are only the missing results. Return the complete "
                "table and list ALL its theorem basenames in the JSON, with contribution "
                "equal to the maximum of old and new ratings. Insert new rows immediately "
                "before the existing \\bottomrule. Preserve every existing character outside "
                "that insertion, including rows, numbering, caption, assumptions and notes. "
                "Append new result numbers after existing ones; never renumber or reorder old rows. "
                "Include comparisons for the new results in appended prior-work rows, even "
                "if the baseline already appears above. Define any new notation within the "
                "new cells. Start the insertion with \\midrule. These requirements override "
                "the usual sorting and consolidation instructions. Negative novelty reviews "
                "are valid inputs: include their results with the prescribed low rating.\n"
            )
        row_started = time.monotonic()
        print(f"[{index}/{len(groups)}] START {setup} | log: {log_path}", flush=True)
        try:
            if not run_agent(task, log_path, setup):
                return False
            data = json.loads(row_path.read_text(encoding="utf-8"))
            score, row, additions = (
                data["contribution"],
                data["table"],
                data["bibliography"],
            )
            if (
                not args.polish
                and isinstance(row, str)
                and not re.search(r"\\end\{table\}\s*(?:\\clearpage\s*)?$", row)
            ):
                raise ValueError(r"incomplete table: missing final \end{table}")
            if (
                type(score) is not int
                or score not in range(4)
                or not isinstance(row, str)
                or row.count(r"\begin{table}") != 1
                or re.findall(r"\\label\{tab:([A-Za-z0-9_]+)\}", row) != [setup]
                or sorted(data["theorems"])
                != sorted(
                    {p.stem for p in groups[setup]}
                    | (saved[setup][3].keys() if setup in saved else set())
                )
                or any(row.count(item["url"]) != 1 for item in inputs)
                or any(item["review_url"] not in row for item in inputs)
                or not isinstance(additions, dict)
                or not all(
                    isinstance(k, str) and isinstance(v, str) and v.strip()
                    for k, v in additions.items()
                )
            ):
                raise ValueError(
                    "invalid setup JSON: expected contribution 0..3, exact theorem list, complete table, bibliography map"
                )
            parsed = split_tables(row)[0]
            if parsed[0] != score or sorted(parsed[3]) != sorted(data["theorems"]):
                raise ValueError("table ratings disagree with setup JSON")
            if setup in saved:
                row = added_rows(saved[setup][2], row)
            with lock:
                cited = {
                    key.strip()
                    for match in re.findall(
                        r"\\citep(?:\[[^\]]*\]){0,2}\{([^}]+)\}", row
                    )
                    for key in match.split(",")
                }
                if cited - (entries.keys() | additions.keys()):
                    raise ValueError(
                        "unresolved citation keys: "
                        + ", ".join(sorted(cited - (entries.keys() | additions.keys())))
                    )
                # Concurrent sessions may choose the same key for different entries.
                for key, entry in additions.items():
                    if any(
                        existing.lower() == key.lower()
                        and (existing != key or entries[existing] != entry)
                        for existing in entries
                    ):
                        new_key = f"{setup}_{key}"
                        while new_key.lower() in {
                            k.lower() for k in entries.keys() | additions.keys()
                        }:
                            new_key += "_"
                        row = re.sub(
                            r"(\\citep(?:\[[^\]]*\]){0,2}\{)([^}]+)(\})",
                            lambda m, key=key, new_key=new_key: (
                                m[1]
                                + ",".join(
                                    new_key if k.strip() == key else k
                                    for k in m[2].split(",")
                                )
                                + m[3]
                            ),
                            row,
                        )
                        entry = re.sub(
                            r"(@\w+\s*[{(]\s*)" + re.escape(key) + r"(?=\s*,)",
                            lambda m, new_key=new_key: m[1] + new_key,
                            entry,
                            count=1,
                        )
                        key = new_key
                    entries[key] = entry
                if setup in saved:
                    prefix, suffix = saved[setup][2].split(r"\bottomrule")
                    row = prefix + row + r"\bottomrule" + suffix
                rows[:] = [item for item in rows if item[1] != setup]
                rows.append((score, setup, row, parsed[3]))
                save()
                completed += 1
                elapsed = time.monotonic() - started
                remaining = elapsed / completed * (len(groups) - completed)
                print(
                    f"[{completed}/{len(groups)}] DONE {setup} | "
                    f"{time.monotonic() - row_started:.0f}s | contribution {score}/3 | "
                    f"{completed / len(groups):.0%} saved | "
                    f"elapsed {elapsed / 60:.1f}m | ETA ~{remaining / 60:.1f}m",
                    flush=True,
                )
            return True
        except (OSError, ValueError, KeyError, TypeError) as error:
            with log_path.open("a") as log:
                log.write(f"\nRUNNER VALIDATION FAILED: {error}\n")
            print(
                f"FAILED {setup}: {error}; see {log_path}. "
                "Completed rows remain in the output directory.",
                file=sys.stderr,
            )
            return False

    results = []
    if not args.polish_only:
        pool = ThreadPoolExecutor(max_workers=args.jobs)
        try:
            futures = [
                pool.submit(review, i, setup)
                for i, setup in enumerate(sorted(groups), 1)
            ]
            results = [future.result() for future in as_completed(futures)]
        except KeyboardInterrupt:
            stopped.set()
            print(
                "Stopping active sessions; completed rows will be preserved.",
                file=sys.stderr,
            )
            return 130
        finally:
            pool.shutdown(wait=True, cancel_futures=True)
        print("Sorting setup tables by contribution...", flush=True)
        rows.sort(key=lambda item: (-item[0], item[1]))
        save()
        if not all(results):
            print(
                f"Saved {completed}/{len(groups)} requested tables; see logs for failures.",
                file=sys.stderr,
            )
        if not rows:
            return 1
    combined = HEADER + "\n".join(row[2] for row in rows) + "\n" + FOOTER
    if args.polish and any(
        row[1] not in saved or row[2] != saved[row[1]][2] for row in rows
    ):
        polish_input = temporary / "polish-input.tex"
        polish_input.write_text(combined, encoding="utf-8")
        polished = temporary / "polished.tex"
        polished_bib = temporary / "polished.bib"
        compile_dir = temporary / "polish-compile"
        log_path = temporary / "polish.log"
        task = (
            prompt
            + "\n\nFINAL EDITORIAL PASS: The per-setup generation and JSON contract above "
            "do not apply to this pass. Read ONLY the combined LaTeX and bibliography below. "
            "Use the combined LaTeX as the base; preserve its table order. "
            "Use the previous-tables snapshot only to identify protected content. Preserve saved table bodies verbatim, "
            "including text, formulas, formatting, numbering, ratings and citations. "
            "Existing tables may only gain rows immediately before their original bottomrule. "
            "Polish only newly generated tables and the newly inserted rows in existing tables. "
            "Do not reorder existing rows or move new rows outside that insertion. "
            "Keep new notation definitions within new cells; do not edit existing notes. "
            "If a previously saved table prevents compilation, report the problem rather "
            "than modifying it. These preservation requirements override the editing instructions below. "
            "Use one outer \\begingroup before all tables and one \\endgroup after all tables. "
            "Do not copy the snapshot wrapper. Put page breaks only between tables. "
            "Write the complete polished LaTeX to the destination below. Do not do research, "
            "read reviews or proofs. Copy the bibliography to its destination and fix only "
            "LaTeX/BibTeX syntax there, preserving every entry, key and bibliographic fact. Unify typography, "
            "notation for equivalent quantities, output labels, big-O complexity notation, "
            "caption/assumptions/Abbr placement, and concise wording across newly generated tables. "
            "Prefer explicit setup parameters in rates; expand unnecessary A, B, S, T-style "
            "abbreviations. Keep them only when long or repeated expressions would otherwise "
            "be unwieldy, not merely to force a formula onto one line. "
            "Keep formulas on one line whenever they fit their column; remove unnecessary "
            "forced breaks, retaining breaks only to prevent overflow without shrinking the font. "
            "Keep exactly Result, Oracle complexity, Novelty, and Limitations columns; put all differences, including tuning requirements, in the comparison columns; preserve table-local result numbers, leave our comparison cells as dashes, refer to those numbers for our advantages and disadvantages only in prior-work rows, and define notation locally in each table. "
            "Keep comparisons factual; remove review verdicts, opinions and commentary about "
            "the review process, such as 'Review’s composition is not a directly stated theorem'. "
            "Preserve each method's individual star rating in parentheses beside its label; do not replace it with a textual verdict. "
            "Label review links (review) and keep them only beside our methods; prior methods use paper citations only. "
            "Preserve substantive comparison conditions; "
            "do not recast a scope extension as a rate improvement. "
            "Preserve all mathematical guarantees, parameter dependence, validity conditions, "
            "rows, their order, setup boundaries, links, citation keys and labels. "
            "Do not infer new comparisons or resolve mathematical uncertainty by guessing. "
            "After editing, compile and fix LaTeX errors until the candidate works with the "
            "exact wrapper below. Repair minor syntax mistakes, including missing environment "
            "closers and unsafe characters or bare URLs in printed bibliography fields. "
            "Use page breaks between tables if needed to prevent too many unprocessed floats. "
            "Continuation tables are allowed for page fit; preserve setup labels and logical row order. "
            "Use plain BibTeX style and numeric natbib mode, "
            "not author-year mode. Copy the repaired table and bibliography into the compilation "
            "directory as tables.tex and results_table.bib, save the wrapper as check.tex, "
            "and run latexmk -pdf -interaction=nonstopmode -halt-on-error -no-shell-escape check.tex "
            "there. Resolve undefined citations and references as well as compilation errors. "
            "Write all corrections back to the polished destinations. Use no additional agents. "
            "Do not modify the input files.\n"
            f"Previously saved tables: {protected}\n"
            f"Combined LaTeX: {polish_input}\nBibliography: {bibliography}\n"
            f"Compilation directory: {compile_dir}\nWrapper:\n{COMPILE_DOCUMENT}\n"
            f"LaTeX destination: {polished}\nBibliography destination: {polished_bib}\n"
        )
        print(f"START final polish | log: {log_path}", flush=True)
        try:
            run_agent(task, log_path, "final polish")
            original = polish_input.read_text(encoding="utf-8")
            revised = normalize_polish(polished.read_text(encoding="utf-8"))
            revised_bib = polished_bib.read_text(encoding="utf-8")
            validate_polish(
                original,
                revised,
                bibliography.read_text(encoding="utf-8"),
                revised_bib,
                saved,
            )
            rows = split_tables(revised)
            if {row[1]: row[3] for row in rows} != {
                row[1]: row[3] for row in split_tables(original)
            }:
                raise ValueError("polish changed theorem ratings")
            check_compilation(revised, revised_bib, compile_dir)
            entries = bibliography_entries(revised_bib)
            save()
        except KeyboardInterrupt:
            print("Polish interrupted; unpolished tables preserved.", file=sys.stderr)
            return 130
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(
                f"FAILED final polish: {error}; see {log_path} and {compile_dir}. Unpolished tables preserved.",
                file=sys.stderr,
            )
            return 1
        print("DONE final polish", flush=True)
    else:
        try:
            check_compilation(
                combined,
                bibliography.read_text(encoding="utf-8"),
                temporary / "compile",
            )
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(
                f"FAILED compilation: {error}; see {temporary / 'compile'}. Drafts preserved.",
                file=sys.stderr,
            )
            return 1
    print(f"Created tables and metadata in {output}\nBibliography: {bibliography}")
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
