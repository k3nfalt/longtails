"""File protocol for hosted agents; optional command adapters automate the loop."""

import argparse
import json
import sys
from pathlib import Path

from .common import (
    WorkflowError,
    command,
    digest,
    fields,
    locked,
    read_json,
    require,
    write_json,
)
from .engine import Run, workflow_root


def parser():
    p = argparse.ArgumentParser(
        prog="autoformalize",
        description="Source-grounded autoformalization for auto-math",
    )
    sub = p.add_subparsers(dest="command", required=True)
    init = sub.add_parser(
        "init", help="Snapshot TeX and create a compact outputs project"
    )
    init.add_argument(
        "--spec", help="JSON initialization options; explicit flags override the file"
    )
    for name in ("run", "source-root", "entry", "target", "formalizer", "reviewer"):
        init.add_argument("--" + name)
    init.add_argument(
        "--repo",
        help="auto-math checkout; defaults to the repository containing autoformalization/",
    )
    init.add_argument("--lean-bin")
    init.add_argument(
        "--cache",
        help="Optional shared .lake/packages directory; must match the pinned manifest",
    )
    init.add_argument("--extra", action="append", default=[])
    init.add_argument(
        "--pdf",
        help="Original PDF, when TeX was acquired or transcribed from PDF input",
    )
    init.add_argument(
        "--acquisition", help="JSON live-search/version/transcription evidence"
    )
    init.add_argument("--timeout", type=int)
    for name, help_text in [
        ("next", "Get the next agent packet"),
        ("status", "Read current progress"),
        ("compose", "Review all statements together"),
        ("freeze", "Freeze approved statements"),
        ("finish", "Run final build, comparator and axiom audit"),
        ("recover", "Roll back an interrupted controller edit"),
    ]:
        cmd = sub.add_parser(name, help=help_text)
        cmd.add_argument("--run", required=True)
        cmd.add_argument("--out")
    submit = sub.add_parser("submit", help="Submit one agent response")
    submit.add_argument("--run", required=True)
    submit.add_argument(
        "--action",
        required=True,
        choices=["graph", "plan", "statement", "review", "proof", "repair"],
    )
    submit.add_argument("--actor", required=True)
    submit.add_argument("--json", required=True)
    submit.add_argument("--out")
    reopen = sub.add_parser(
        "reopen", help="Reopen a unit's affected dependency closure"
    )
    reopen.add_argument("--run", required=True)
    reopen.add_argument("--unit")
    reopen.add_argument("--reason", required=True)
    export = sub.add_parser(
        "export",
        help="Export proved oracle modules without touching the canonical repository",
    )
    export.add_argument("--run", required=True)
    export.add_argument("--destination", required=True)
    integrate = sub.add_parser(
        "integrate",
        help="Copy proved modules into a repository checkout and run its own lint and Comparator",
    )
    integrate.add_argument("--run", required=True)
    integrate.add_argument("--repository", required=True)
    integrate.add_argument("--timeout", type=int, default=86400)
    integrate.add_argument("--out")
    drive = sub.add_parser(
        "drive", help="Run external Formalizer/Reviewer command adapters"
    )
    drive.add_argument("--run", required=True)
    drive.add_argument(
        "--adapters",
        required=True,
        help="JSON with formalizer and reviewer argv arrays",
    )
    drive.add_argument("--steps", type=int, default=100)
    drive.add_argument("--agent-timeout", type=int, default=1800)
    search = sub.add_parser(
        "search", help="Search local oracle and Mathlib sources; no LLM or network"
    )
    search.add_argument("--run", required=True)
    search.add_argument("--query", required=True)
    return p


def drive(run, adapters, steps, timeout):
    require(
        set(adapters) == {"formalizer", "reviewer"},
        "Adapters need formalizer and reviewer argv arrays",
    )
    for argv in adapters.values():
        require(
            isinstance(argv, list) and argv and all(isinstance(s, str) for s in argv),
            "Adapter must be a nonempty argv array",
        )
    require(steps > 0, "Step budget must be positive")
    previous, repeats, feedback = None, 0, None
    for _ in range(steps):
        run.verify()
        packet = run.next()
        action = packet["action"]
        print("autoformalize: " + action, file=sys.stderr, flush=True)
        if action == "complete":
            return packet
        if action in {"compose", "freeze", "finish"}:
            try:
                with run.transaction():
                    getattr(run, action)()
            except WorkflowError as exc:
                run.state["repair_request"] = {
                    "failed_action": action,
                    "error": str(exc),
                }
                run.save("controller_repair_requested", run.state["repair_request"])
            continue
        if feedback:
            packet["controller_error"] = feedback
        role = "reviewer" if action == "review" else "formalizer"
        result = command(
            adapters[role],
            run.root,
            timeout=timeout,
            input_text=json.dumps(packet, ensure_ascii=False) + "\n",
        )
        run.put(
            {
                "kind": "agent_execution",
                "role": role,
                "packet": digest(packet),
                **result,
            }
        )
        require(
            result["exit_code"] == 0,
            "Agent adapter failed: " + result["stderr"][-4000:],
        )
        try:
            # Use the same strict decoder as submitted files.
            response_path = run.root / "agent-response.json"
            response_path.write_text(result["stdout"], encoding="utf-8")
            payload = read_json(response_path)
            identity = digest({"action": action, "payload": payload})
            repeats = repeats + 1 if identity == previous else 1
            previous = identity
            require(
                repeats < 3,
                "Agent repeated the same response three times; repair or change strategy before resuming",
            )
            with run.transaction():
                run.dispatch(action, payload, packet["actor"])
            feedback = None
        except WorkflowError as exc:
            feedback = str(exc)
            run.put({"kind": "repair_feedback", "action": action, "error": feedback})
            if repeats >= 3:
                raise
    return {
        "status": "step_budget_reached",
        "phase": run.state["phase"],
        "next": run.next(),
    }


def main(argv=None):
    args = parser().parse_args(argv)
    try:
        if args.command == "init":
            if args.spec:
                config = read_json(args.spec)
                required = [
                    "run",
                    "source_root",
                    "entry",
                    "target",
                    "formalizer",
                    "reviewer",
                ]
                fields(
                    config,
                    required,
                    [
                        "repo",
                        "lean_bin",
                        "cache",
                        "extra",
                        "pdf",
                        "acquisition",
                        "timeout",
                    ],
                )
                for key, value in config.items():
                    if not getattr(args, key):
                        if (
                            key
                            in {
                                "run",
                                "repo",
                                "source_root",
                                "lean_bin",
                                "cache",
                                "pdf",
                                "acquisition",
                            }
                            and value
                        ):
                            value = str(
                                (Path(args.spec).resolve().parent / value).resolve()
                            )
                        setattr(args, key, value)
            if not args.repo:
                args.repo = str(workflow_root().parent)
            for key in (
                "run",
                "repo",
                "source_root",
                "entry",
                "target",
                "formalizer",
                "reviewer",
            ):
                require(
                    getattr(args, key),
                    "Initialization requires --" + key.replace("_", "-"),
                )
            run = Run.create(
                args.run,
                args.repo,
                args.source_root,
                args.entry,
                args.target,
                args.formalizer,
                args.reviewer,
                lean_bin=args.lean_bin,
                cache=args.cache,
                extras=args.extra,
                pdf=args.pdf,
                acquisition_record=read_json(args.acquisition)
                if args.acquisition
                else None,
                timeout=args.timeout or 1800,
            )
            result = run.next()
        else:
            run = Run(args.run)
            with locked(run.root):
                if args.command == "recover":
                    run.recover()
                    run.verify()
                    result = {"status": "recovered", "phase": run.state["phase"]}
                else:
                    run.verify(environment=args.command != "status")
                    if args.command == "next":
                        result = run.next()
                    elif args.command == "status":
                        result = {
                            key: run.state[key]
                            for key in (
                                "phase",
                                "target",
                                "repository_commit",
                                "freeze",
                                "final",
                            )
                        }
                        result.update(
                            accepted_units=sorted(run.accepted()),
                            proved_declarations=sorted(run.state["proofs"]),
                        )
                    elif args.command == "drive":
                        result = drive(
                            run,
                            read_json(args.adapters),
                            args.steps,
                            args.agent_timeout,
                        )
                    elif args.command == "search":
                        roots = [
                            run.compiler.project / "outputs",
                            run.compiler.project / "LongTails",
                            Path(run.state["repository"]) / "LongTails",
                            run.compiler.project / ".lake/packages/mathlib/Mathlib",
                        ]
                        roots = list(
                            dict.fromkeys(str(p.resolve()) for p in roots if p.is_dir())
                        )
                        result = command(
                            [
                                "rg",
                                "--line-number",
                                "--glob",
                                "*.lean",
                                "--fixed-strings",
                                "--",
                                args.query,
                                *roots,
                            ],
                            run.compiler.project,
                        )
                        require(result["exit_code"] in {0, 1}, result["stderr"])
                        result["stdout"] = "\n".join(
                            result["stdout"].splitlines()[:200]
                        )
                        result["limit"] = (
                            "First 200 matching lines; use narrower queries if needed"
                        )
                    else:
                        with run.transaction():
                            if args.command == "submit":
                                result = run.dispatch(
                                    args.action, read_json(args.json), args.actor
                                )
                            elif args.command == "reopen":
                                result = (
                                    run.reopen(args.unit, args.reason)
                                    if args.unit
                                    else run.restart_graph(args.reason)
                                )
                            elif args.command == "export":
                                result = run.export(args.destination)
                            elif args.command == "integrate":
                                result = run.integrate(args.repository, args.timeout)
                            else:
                                result = getattr(run, args.command)()
                        if result is None:
                            result = run.next()
        if getattr(args, "out", None):
            write_json(args.out, result)
        else:
            print(json.dumps(result, indent=2, ensure_ascii=False))
        return 0
    except (
        WorkflowError,
        OSError,
        KeyError,
        TypeError,
        ValueError,
        RecursionError,
    ) as exc:
        print(
            json.dumps(
                {"error": str(exc), "status": "not_accepted"}, ensure_ascii=False
            ),
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
