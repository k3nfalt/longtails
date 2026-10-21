"""Resumable, fail-closed orchestration of independent agents and Lean."""

import base64
import copy
import shutil
from contextlib import contextmanager
from pathlib import Path

from . import __version__
from .common import (
    WorkflowError,
    canonical,
    digest,
    fields,
    now,
    read_json,
    require,
    scoped,
    text,
    write_json,
)
from .contracts import (
    identity,
    review_requirements,
    score_review,
    validate_graph,
    validate_plan,
    validate_review,
)
from .layout import in_category
from .lean import (
    Compiler,
    audit,
    check_holes,
    check_proof_signature,
    check_signature,
    frozen_signature,
    initialize_project,
    module_name,
    public_layout,
    render_proofs,
    repository_files,
)
from .output_contract import (
    catalog_contract,
    declaration_contract,
    graph_checks,
    output_checks,
    review_clauses,
)
from .project import MANIFEST, compact_manifest, materialize, sync_index
from .source import acquisition, load_package, spans


def workflow_root():
    return Path(__file__).resolve().parents[2]


def policy_documents():
    """Read the single instruction set beside the workflow launcher."""
    checkout = workflow_root()
    documents = {}
    for name in (
        "AGENTS.md",
        "WORKFLOW.md",
        "PROTOCOL.md",
        "FORMALIZER.md",
        "REVIEWER.md",
    ):
        path = (
            checkout
            / ("prompts" if name in {"FORMALIZER.md", "REVIEWER.md"} else "")
            / name
        )
        require(path.is_file(), "Missing workflow policy: " + name)
        documents[name] = path
    return documents


def controller_version():
    root = Path(__file__).parent
    files = {
        p.name: digest(p.read_bytes())
        for p in root.iterdir()
        if p.suffix in {".py", ".lean"}
    }
    files.update(
        {
            "policy/" + name: digest(path.read_bytes())
            for name, path in policy_documents().items()
        }
    )
    return digest(files)


def evidence_pointers(value):
    pointers = {}

    def walk(item, path="candidate"):
        pointers[path] = path
        if path.rsplit("/", 1)[-1] in {"type_tree", "value_tree"}:
            return
        if isinstance(item, dict):
            for key, child in item.items():
                walk(child, path + "/" + str(key))
        elif isinstance(item, list):
            for index, child in enumerate(item):
                walk(child, path + "/" + str(index))

    walk(value)
    return pointers


class Run:
    def __init__(self, directory):
        self.root = Path(directory).resolve()
        self.state = read_json(self.root / "state.json")
        require(self.state["schema"] == 1, "Unsupported run schema")
        self.compiler = Compiler(
            self.root / "project",
            self.root / "compiler",
            self.state["lean_bin"],
            self.state["timeout"],
        )

    def put(self, value):
        raw = canonical(value).encode("utf-8")
        require(
            len(raw) + 1 <= 64_000_000,
            "Artifact exceeds 64 MB; narrow the unit or provider inventory without omitting required evidence",
        )
        key = digest(raw)
        path = self.root / "objects" / (key + ".json")
        if path.exists():
            require(read_json(path) == value, "Immutable artifact collision")
        else:
            write_json(path, value, compact=True)
        return key

    def get(self, key):
        require(
            isinstance(key, str)
            and len(key) == 64
            and all(c in "0123456789abcdef" for c in key),
            "Invalid artifact identity",
        )
        value = read_json(self.root / "objects" / (key + ".json"))
        require(digest(value) == key, "Artifact was modified: " + key)
        return value

    def save(self, action, details=None):
        self.state["files"] = repository_files(self.compiler.project)
        for path, expected in self.state.get("base_files", {}).items():
            if path == "outputs.lean" and self.state["files"].get(path) != expected:
                sync_index(self.compiler.project, check=True)
                continue
            require(
                self.state["files"].get(path) == expected,
                "Protected repository file changed: " + path,
            )
        if "base_files" in self.state:
            allowed = {u["file"] for u in self.units() if u["mode"] == "new"}
            require(
                self.state["files"].keys() <= self.state["base_files"].keys() | allowed,
                "An unplanned project source file appeared",
            )
        previous = self.state.get("event")
        self.state.pop("event", None)
        event = {
            "action": action,
            "details": details,
            "time": now(),
            "previous": previous,
            "checkpoint": self.put(self.state),
        }
        self.state["event"] = self.put(event)
        write_json(self.root / "state.json", self.state)

    def verify(self, *, environment=True):
        require(
            not (self.root / "transaction.json").exists(),
            "Interrupted edit found; run recover before continuing",
        )
        require(
            self.state["controller"] == controller_version(),
            "Controller changed; start a new run with this version",
        )
        checkpoint = dict(self.state)
        event = checkpoint.pop("event")
        require(
            self.get(self.get(event)["checkpoint"]) == checkpoint,
            "State differs from its recorded checkpoint",
        )
        require(
            repository_files(self.compiler.project) == self.state["files"],
            "Project changed outside the controller; restore the recorded files before continuing",
        )
        self.get(self.state["source"])
        if self.state.get("acquisition"):
            record = self.get(self.state["acquisition"])
            require(
                digest((self.root / "original.pdf").read_bytes())
                == record["original_pdf_sha256"],
                "Original PDF changed",
            )
        if environment:
            require(
                self.compiler.environment() == self.state["environment"],
                "Pinned compiler/dependency environment changed",
            )

    @contextmanager
    def transaction(self):
        """Recover source and checkpoint together after failure or process interruption."""
        before = copy.deepcopy(self.state)
        files = {}
        for u in self.units():
            if u["mode"] == "new":
                path = scoped(self.compiler.project, u["file"])
                files[u["file"]] = (
                    base64.b64encode(path.read_bytes()).decode("ascii")
                    if path.exists()
                    else None
                )
        write_json(self.root / "transaction.json", {"state": before, "files": files})
        try:
            yield
        except BaseException:
            self.recover()
            raise
        else:
            (self.root / "transaction.json").unlink()

    def recover(self):
        path = self.root / "transaction.json"
        require(path.exists(), "No interrupted transaction")
        journal = read_json(path)
        # Journal files must be controller-owned paths in its checkpoint plan.
        state = journal["state"]
        allowed = (
            {u["file"] for u in self.get(state["plan"])["units"] if u["mode"] == "new"}
            if state["plan"]
            else set()
        )
        require(
            journal["files"].keys() <= allowed,
            "Recovery journal contains an unowned path",
        )
        for relative, content in journal["files"].items():
            target = scoped(self.compiler.project, relative)
            if content is None:
                target.unlink(missing_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(base64.b64decode(content, validate=True))
        metadata = compact_manifest(self.compiler.project)
        if metadata:
            for p in (self.compiler.project / "LongTails").rglob("*.lean"):
                relative = p.relative_to(self.compiler.project).as_posix()
                if relative not in state["files"]:
                    require(
                        digest(p.read_bytes())
                        == metadata["repository_files"].get(relative),
                        "Cannot recover a changed dependency",
                    )
                    p.unlink()
        self.compiler.sync_index()
        self.state = state
        write_json(self.root / "state.json", self.state)
        path.unlink()

    @classmethod
    def create(
        cls,
        directory,
        repository,
        source_root,
        entry,
        target,
        formalizer,
        reviewer,
        *,
        lean_bin=None,
        cache=None,
        extras=(),
        pdf=None,
        acquisition_record=None,
        timeout=1800,
    ):
        root = Path(directory).resolve()
        require(
            not (root / "state.json").exists(),
            "Run already initialized; use next/status to resume",
        )
        text(target, "target theorem")
        identity(formalizer)
        identity(reviewer)
        require(
            formalizer != reviewer,
            "Formalizer and Reviewer must be separate identities/contexts",
        )
        source = load_package(source_root, entry, extras)
        if pdf:
            require(
                acquisition_record is not None,
                "PDF input requires live-search acquisition evidence before TeX intake",
            )
            acquisition(acquisition_record, digest(Path(pdf).read_bytes()))
        else:
            require(
                acquisition_record is None,
                "An acquisition record requires the original PDF",
            )
        request = {
            "repository": str(Path(repository).resolve()),
            "source": source["id"],
            "entry": entry,
            "target": target,
            "formalizer": formalizer,
            "reviewer": reviewer,
            "lean_bin": lean_bin,
            "cache": cache,
            "controller": controller_version(),
            "acquisition": acquisition_record,
        }
        marker = root / "initialization.json"
        if root.exists():
            require(
                marker.is_file() and read_json(marker) == request,
                "Existing run has different initialization inputs",
            )
        else:
            root.mkdir(parents=True)
            write_json(marker, request)
        from .common import checked

        if (root / "project").exists():
            metadata = compact_manifest(root / "project")
            require(metadata is not None, "Initialization requires a compact project")
            commit = metadata["repository_commit"]
            require(
                commit == checked(["git", "rev-parse", "HEAD"], repository),
                "Initialization repository changed",
            )
            current = repository_files(root / "project")
            require(
                {p: h for p, h in current.items() if p != MANIFEST}
                == metadata["initial_files"],
                "Initialization project has source changes",
            )
        else:
            commit = initialize_project(repository, root / "project", cache)
        compiler = Compiler(root / "project", root / "compiler", lean_bin, timeout)
        # Restore dependencies through Lake's pinned manifest. This never runs lake update.
        manifest = (root / "project/lake-manifest.json").read_bytes()
        if not cache:
            compiler.run(["lake", "exe", "cache", "get"])
        require(
            (root / "project/lake-manifest.json").read_bytes() == manifest,
            "Dependency restoration changed the manifest",
        )
        environment = compiler.environment()
        compiler.build()
        state = {
            "schema": 1,
            "version": __version__,
            "controller": controller_version(),
            "created": now(),
            "repository_commit": commit,
            "repository": str(Path(repository).resolve()),
            "target": target,
            "formalizer": formalizer,
            "reviewer": reviewer,
            "lean_bin": str(Path(lean_bin).resolve()) if lean_bin else None,
            "timeout": timeout,
            "environment": environment,
            "source": None,
            "evidence": None,
            "acquisition": None,
            "base_files": repository_files(root / "project"),
            "phase": "graph",
            "graph": None,
            "graph_review": None,
            "plan": None,
            "units": {},
            "pending": None,
            "composition": None,
            "freeze": None,
            "proofs": {},
            "final": None,
        }
        write_json(root / "state.json", state)
        run = cls(root)
        run.state["source"] = run.put(source)
        run.state["evidence"] = run.put(spans(source))
        if pdf:
            shutil.copyfile(pdf, root / "original.pdf")
            run.state["acquisition"] = run.put(acquisition_record)
        run.save("created")
        marker.unlink()
        return run

    def units(self):
        return self.get(self.state["plan"])["units"] if self.state["plan"] else []

    def unit(self, uid):
        found = [u for u in self.units() if u["id"] == uid]
        require(len(found) == 1, "Unknown planned unit: " + uid)
        return found[0]

    def accepted(self):
        return {uid for uid, row in self.state["units"].items() if row.get("accepted")}

    def all_holes(self):
        return [
            h
            for row in self.state["units"].values()
            if row.get("candidate")
            for h in self.get(row["candidate"])["holes"]
        ]

    def inventory(self):
        return self.compiler.inspect(self.units(), self.provider_names())

    def provider_names(self):
        return sorted(
            {
                name
                for row in self.state["units"].values()
                if row.get("candidate")
                for name in self.get(row["candidate"])["providers"]
            }
        )

    def packet(self, kind, candidate, clauses, *, extra_checks=()):
        evidence = self.get(self.state["evidence"])
        # Expression trees remain complete evidence, cited at their subtree roots.
        candidate_ids = evidence_pointers(candidate)
        packet = {
            "kind": kind,
            "target": self.state["target"],
            "source": self.get(self.state["source"]),
            "source_ids": evidence,
            "candidate": candidate,
            "candidate_ids": candidate_ids,
            "required_checks": review_requirements(clauses) + list(extra_checks),
            "environment": self.state["environment"],
            "graph": self.state["graph"],
            "plan": self.state["plan"],
            "reviewer": self.state["reviewer"],
            "policy_version": self.state["controller"],
        }
        packet["repository_commit"] = self.state["repository_commit"]
        packet["repository_basis"] = digest(self.state["base_files"])
        packet["basis"] = digest(packet)
        return packet

    def queue(self, packet, owner):
        require(
            packet["basis"] not in self.state.get("rejected_bases", []),
            "This exact candidate was rejected; repair it before requesting review again",
        )
        self.state["pending"] = {"packet": self.put(packet), "owner": owner}

    def submit_graph(self, graph):
        require(
            self.state["phase"] == "graph",
            "Return to graph stage explicitly before revising the graph",
        )
        summary = validate_graph(graph, self.get(self.state["evidence"]))
        self.state["graph"] = self.put(graph)
        self.state["graph_review"] = None
        self.queue(
            self.packet(
                "graph_review",
                {"graph": graph, "layers": summary},
                summary["clauses"],
                extra_checks=graph_checks(graph),
            ),
            "graph",
        )
        self.save("graph_submitted")

    def submit_plan(self, plan):
        require(
            self.state["phase"] == "plan" and self.state["graph_review"],
            "Graph must pass independent review first",
        )
        order = validate_plan(plan, self.get(self.state["graph"]))
        for u in plan["units"]:
            if u["mode"] == "new":
                require(
                    not scoped(self.compiler.project, u["file"]).exists(),
                    "Preserve existing declarations; select a new module or reuse it",
                )
        self.state["plan"] = self.put(plan)
        self.state["units"] = {
            u["id"]: {"accepted": False, "candidate": None, "review": None}
            for u in plan["units"]
        }
        clauses = validate_graph(
            self.get(self.state["graph"]), self.get(self.state["evidence"])
        )["clauses"]
        self.queue(
            self.packet(
                "plan_review",
                {"graph": self.get(self.state["graph"]), "plan": plan, "layers": order},
                clauses,
                extra_checks=output_checks(plan),
            ),
            "plan",
        )
        self.save("plan_submitted", {"layers": order})

    def submit_statement(self, submission):
        fields(submission, ["unit", "code", "holes", "providers"])
        require(self.state["phase"] == "statements", "Not in statement mode")
        uid = submission["unit"]
        unit = self.unit(uid)
        require(
            set(unit["depends_on"]) <= self.accepted(),
            "Formalize and accept prerequisites first",
        )
        require(
            isinstance(submission["providers"], list)
            and all(isinstance(n, str) for n in submission["providers"]),
            "Provider names must be a list",
        )
        require(
            isinstance(submission["code"], str) and "\r" not in submission["code"],
            "Use LF-normalized UTF-8 source",
        )
        require(
            len(submission["code"].encode("utf-8")) <= 2_000_000,
            "Candidate module exceeds 2 MB",
        )
        path = scoped(self.compiler.project, unit["file"])
        affected = self.invalidate(uid)
        self.clear_descendants(uid, affected)
        old = path.read_bytes() if path.exists() else None
        if unit["mode"] == "reuse":
            require(
                submission["code"] == "" and submission["holes"] == [],
                "Reused declarations are read-only",
            )
        else:
            text(submission["code"], "candidate code")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(submission["code"], encoding="utf-8", newline="\n")
        added = {}
        try:
            added = materialize(self.compiler.project, [unit["file"]])
            self.state["base_files"].update(added)
            topology = self.compiler.topology(self.get(self.state["plan"]))
            self.compiler.build(targets=[module_name(unit["file"])])
            observed = self.compiler.inspect([unit], submission["providers"])
            if unit["mode"] == "new":
                owned = [
                    d
                    for d in observed["declarations"]
                    if d["module"] == module_name(unit["file"])
                ]
                check_holes(
                    submission["code"], submission["holes"], owned, unit["declarations"]
                )
                public_layout(unit, submission["code"], observed)
            elif in_category(unit["file"], "Theorems"):
                public_layout(unit, path.read_text(encoding="utf-8"), observed)
            audit(
                observed,
                self.all_holes() + submission["holes"],
                final=unit["mode"] == "reuse",
            )
            declaration_contract([unit], self.get(self.state["graph"]), observed)
            catalog = self.compiler.catalog([unit])
            output = catalog_contract(
                self.get(self.state["plan"]), catalog, observed, [uid]
            )
        except Exception:
            for relative, expected in added.items():
                dependency = scoped(self.compiler.project, relative)
                require(
                    digest(dependency.read_bytes()) == expected,
                    "Copied dependency changed during failed check",
                )
                dependency.unlink()
                self.state["base_files"].pop(relative, None)
            if unit["mode"] == "new":
                if old is None:
                    path.unlink(missing_ok=True)
                else:
                    path.write_bytes(old)
                self.compiler.sync_index()
            raise
        row = self.state["units"][uid]
        row["candidate"] = self.put(submission)
        row["inventory"] = self.put(observed)
        context = {
            "unit": unit,
            "inventory": observed,
            "catalog": catalog,
            "output_contract_check": output,
            "comparator_topology": topology,
            "source_code": submission["code"],
            "graph": self.get(self.state["graph"]),
            "plan": self.get(self.state["plan"]),
            "accepted_prerequisites": {
                dep: self.get(self.state["units"][dep]["inventory"])
                for dep in unit["depends_on"]
            },
        }
        extra = [
            "obligation:" + o["id"]
            for o in self.get(self.state["plan"])["deferred_obligations"]
            if o["owner"] == uid
        ]
        extra += ["declaration:" + d["name"] for d in observed["declarations"]]
        extra += ["node:" + n for n in unit["nodes"]]
        extra += output_checks(context["plan"], uid)
        if in_category(unit["file"], "Theorems"):
            extra.append("catalog:" + uid)
        self.queue(
            self.packet(
                "statement_review",
                context,
                review_clauses(unit, context["plan"], context["graph"]),
                extra_checks=extra,
            ),
            uid,
        )
        self.save("statement_submitted", uid)

    def invalidate(self, uid):
        affected = {uid}
        while True:
            more = {u["id"] for u in self.units() if set(u["depends_on"]) & affected}
            if more <= affected:
                break
            affected |= more
        for key in affected:
            self.state["units"][key]["accepted"] = False
            self.state["units"][key]["review"] = None
        self.state["composition"] = self.state["freeze"] = self.state["final"] = None
        self.state["pending"] = None
        self.state.pop("repair_request", None)
        return sorted(affected)

    def clear_descendants(self, uid, affected):
        for u in self.units():
            if u["id"] in affected:
                for name in u["declarations"]:
                    self.state["proofs"].pop(name, None)
                if u["id"] != uid and u["mode"] == "new":
                    scoped(self.compiler.project, u["file"]).unlink(missing_ok=True)

    def submit_review(self, review, actor):
        require(
            actor == self.state["reviewer"],
            "Only the registered Reviewer submits verdicts",
        )
        pending = self.state["pending"]
        require(pending is not None, "No candidate is waiting for review")
        packet = self.get(pending["packet"])
        accepted = validate_review(review, packet, actor)
        scores = score_review(review, accepted)
        if not accepted:
            self.state.setdefault("rejected_bases", []).append(packet["basis"])
        receipt = self.put(review)
        owner = pending["owner"]
        self.state["pending"] = None
        self.state["last_review"] = {
            "packet": pending["packet"],
            "review": receipt,
            "accepted": accepted,
            "scores": self.put(scores),
        }
        if owner == "graph":
            self.state["graph_review"] = receipt if accepted else None
            self.state["phase"] = "plan" if accepted else "graph"
        elif owner == "plan":
            self.state["plan_review"] = receipt if accepted else None
            self.state["phase"] = "statements" if accepted else "plan"
        elif owner == "composition":
            self.state["composition"] = receipt if accepted else None
            self.state["phase"] = "ready_to_freeze" if accepted else "statements"
        else:
            self.state["units"][owner].update(accepted=accepted, review=receipt)
        self.save(
            "review_accepted" if accepted else "review_rejected",
            {"owner": owner, "receipt": receipt},
        )
        return {"accepted": accepted, "scores": scores, "phase": self.state["phase"]}

    def compose(self):
        require(
            self.state["phase"] == "statements"
            and self.accepted() == {u["id"] for u in self.units()},
            "All required statements must pass before composition",
        )
        self.compiler.build()
        inventory = self.inventory()
        audit(inventory, self.all_holes())
        # A dependency change cannot keep a cached unit acceptance alive.
        current = frozen_signature(inventory)
        for row in self.state["units"].values():
            check_signature(frozen_signature(self.get(row["inventory"])), current)
        clauses = validate_graph(
            self.get(self.state["graph"]), self.get(self.state["evidence"])
        )["clauses"]
        plan = self.get(self.state["plan"])
        graph = self.get(self.state["graph"])
        validate_plan(plan, graph)
        declaration_contract(self.units(), graph, inventory)
        topology = self.compiler.topology(plan)
        catalog = self.compiler.catalog(self.units())
        output = catalog_contract(plan, catalog, inventory)
        packet = self.packet(
            "composition_review",
            {
                "graph": self.get(self.state["graph"]),
                "plan": plan,
                "inventory": inventory,
                "units": self.state["units"],
                "catalog": catalog,
                "output_contract_check": output,
                "comparator_topology": topology,
            },
            clauses,
            extra_checks=["obligation:" + o["id"] for o in plan["deferred_obligations"]]
            + graph_checks(graph)
            + output_checks(plan)
            + ["node:" + n["id"] for n in graph["nodes"]],
        )
        self.state["composed_inventory"] = self.put(inventory)
        self.queue(packet, "composition")
        self.save("composition_submitted")

    def freeze(self):
        require(
            self.state["phase"] == "ready_to_freeze" and self.state["composition"],
            "Composition must pass before freeze",
        )
        inventory = self.inventory()
        require(
            frozen_signature(inventory)
            == frozen_signature(self.get(self.state["composed_inventory"])),
            "Composition basis changed",
        )
        frozen = {
            "signature": frozen_signature(inventory),
            "files": repository_files(self.compiler.project),
            "environment": self.state["environment"],
            "graph": self.state["graph"],
            "plan": self.state["plan"],
            "composition": self.state["composition"],
            "units": self.state["units"],
        }
        self.state["freeze"] = self.put(frozen)
        self.state["phase"] = "proofs"
        self.save("frozen")

    def prove(self, name, proof):
        require(self.state["phase"] == "proofs", "Freeze statements before proving")
        text(proof, "proof body")
        require(
            len(proof.encode("utf-8")) <= 2_000_000 and "\r" not in proof,
            "Use an LF-normalized proof under 2 MB",
        )
        unit = next((u for u in self.units() if name in u["declarations"]), None)
        require(unit is not None, "Unplanned proof declaration")
        candidate = self.get(self.state["units"][unit["id"]]["candidate"])
        require(
            name in {h["declaration"] for h in candidate["holes"]},
            "Not a registered proof slot",
        )
        for dependency in unit["depends_on"]:
            dep = self.get(self.state["units"][dependency]["candidate"])
            require(
                all(h["declaration"] in self.state["proofs"] for h in dep["holes"]),
                "Complete dependency proofs first",
            )
        self.compiler.parse_proof(self.units(), proof)
        proofs = {**self.state["proofs"], name: proof}
        path = scoped(self.compiler.project, unit["file"])
        old = path.read_bytes()
        path.write_text(
            render_proofs(candidate["code"], candidate["holes"], proofs),
            encoding="utf-8",
            newline="\n",
        )
        try:
            self.compiler.build()
            inventory = self.inventory()
            check_proof_signature(
                self.get(self.state["freeze"])["signature"], inventory, self.all_holes()
            )
            audit(inventory, self.all_holes())
            proved = [d for d in inventory["declarations"] if d["name"] in proofs]
            require(
                len(proved) == len(proofs), "Proved declaration missing from inventory"
            )
            audit({"declarations": proved}, final=True)
        except Exception:
            path.write_bytes(old)
            raise
        self.state["proofs"] = proofs
        self.state["proof_inventory"] = self.put(inventory)
        self.save("proof_checked", name)

    def reopen(self, uid, reason):
        text(reason, "reason for reopening statements")
        require(self.state["plan"], "No statement plan to reopen")
        self.unit(uid)
        affected = self.invalidate(uid)
        self.clear_descendants(uid, affected)
        # Unaffected proof terms remain checked and byte-for-byte intact.
        for u in self.units():
            row = self.state["units"][u["id"]]
            if u["id"] == uid and u["mode"] == "new" and row["candidate"]:
                scoped(self.compiler.project, u["file"]).write_text(
                    self.get(row["candidate"])["code"], encoding="utf-8", newline="\n"
                )
        self.state["phase"] = "statements"
        self.save("statements_reopened", {"affected": affected, "reason": reason})

    def restart_graph(self, reason):
        text(reason, "reason for graph revision")
        for u in self.units():
            if u["mode"] == "new" and self.state["units"][u["id"]]["candidate"]:
                scoped(self.compiler.project, u["file"]).unlink(missing_ok=True)
        self.state.update(
            phase="graph",
            graph=None,
            graph_review=None,
            plan=None,
            units={},
            pending=None,
            composition=None,
            freeze=None,
            proofs={},
            final=None,
        )
        self.state.pop("repair_request", None)
        self.save("graph_reopened", reason)

    def finish(self):
        require(
            self.state["phase"] == "proofs" and self.state["freeze"],
            "Not in a frozen proof stage",
        )
        require(
            {h["declaration"] for h in self.all_holes()} == set(self.state["proofs"]),
            "Some registered proofs are incomplete",
        )
        frozen = self.get(self.state["freeze"])
        files = repository_files(self.compiler.project)
        allowed = {u["file"] for u in self.units() if u["mode"] == "new"}
        require(
            files.keys() == frozen["files"].keys(),
            "Project file set changed during proofs",
        )
        for path, original_hash in frozen["files"].items():
            if path not in allowed:
                require(files[path] == original_hash, "Frozen file changed: " + path)
        for u in self.units():
            if u["mode"] == "new":
                c = self.get(self.state["units"][u["id"]]["candidate"])
                expected = render_proofs(c["code"], c["holes"], self.state["proofs"])
                require(
                    scoped(self.compiler.project, u["file"]).read_text(encoding="utf-8")
                    == expected,
                    "Edits occurred outside registered proof bodies",
                )
        public_paths = [
            u["file"] for u in self.units() if in_category(u["file"], "Theorems")
        ]
        self.compiler.build(final=True, public_paths=public_paths)
        inventory = self.inventory()
        check_proof_signature(frozen["signature"], inventory, self.all_holes())
        audit(inventory, final=True)
        catalog = self.compiler.catalog(self.units())
        graph, plan = self.get(self.state["graph"]), self.get(self.state["plan"])
        validate_graph(graph, self.get(self.state["evidence"]))
        validate_plan(plan, graph)
        declaration_contract(self.units(), graph, inventory)
        output = catalog_contract(plan, catalog, inventory)
        topology = self.compiler.topology(plan)
        require(
            self.compiler.environment() == self.state["environment"],
            "Final environment differs from the freeze",
        )
        result = {
            "status": "proved",
            "target": self.state["target"],
            "freeze": self.state["freeze"],
            "inventory": self.put(inventory),
            "catalog": catalog,
            "output_contract_check": output,
            "source_inventory": graph["inventory"],
            "output_contract": plan["output_contract"],
            "comparator_topology": topology,
            "environment": self.state["environment"],
            "files": {p: files[p] for p in sorted(allowed)},
            "repository_commit": self.state["repository_commit"],
        }
        self.state["final"] = self.put(result)
        self.state["phase"] = "complete"
        self.save("completed")
        return result

    def export(self, destination):
        require(
            self.state["phase"] == "complete", "Only a fully proved run can be exported"
        )
        destination = Path(destination).resolve()
        require(not destination.exists(), "Export into a new directory")
        result = self.get(self.state["final"])
        for relative, expected in result["files"].items():
            original = scoped(self.compiler.project, relative)
            require(digest(original.read_bytes()) == expected, "Final source changed")
        destination.mkdir(parents=True)
        for relative in result["files"]:
            target = scoped(destination, relative)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(scoped(self.compiler.project, relative), target)
        write_json(destination / "verification.json", result)
        return result

    def next(self):
        s = self.state
        common = {
            "phase": s["phase"],
            "target": s["target"],
            "run": str(self.root),
            "last_review": s.get("last_review"),
            "instructions": "Read AGENTS.md, WORKFLOW.md and your role prompt. Never invent tool observations.",
        }
        common["project"] = str(self.compiler.project)
        common["paths"] = {
            "workflow": str(workflow_root()),
            "repository": s["repository"],
            "project": str(self.compiler.project),
            **{
                key: str(self.compiler.project / relative)
                for key, relative in {
                    "repository_instructions": "AGENTS.md",
                    "template": "LongTails/Template.lean",
                    "outputs": "outputs",
                    "algorithms": "outputs/Algorithms",
                    "setups": "outputs/Setups",
                    "proofs": "outputs/Proofs",
                    "theorems": "outputs/Theorems",
                    "budget_renderer": "server/Theorems/BudgetLatex.lean",
                    "catalog_extractor": "server/Theorems/create_theorem_description.py",
                    "mathlib": ".lake/packages/mathlib/Mathlib",
                    "toolchain": "lean-toolchain",
                    "manifest": "lake-manifest.json",
                    "verification_script": "build.sh",
                    "comparator": "run_comparator.py",
                    "convergence_metadata": "tools/ConvergenceMetadata.lean",
                }.items()
            },
        }
        common["path_rules"] = (
            "Generated outputs/ and copied LongTails/ dependencies resolve under paths.project. "
            "This is a compact run project. Generate outputs.* modules only; paths.repository supplies read-only library retrieval. "
            "Use paths.workflow for workflow instructions. Submit candidates through the controller; "
            "do not edit either repository directly."
        )
        common["paths"]["library"] = str(Path(s["repository"]) / "LongTails")
        common["repository_interfaces"] = {
            relative: (self.compiler.project / relative).read_text(encoding="utf-8")
            for relative in (
                "LongTails/Template.lean",
                "server/Theorems/BudgetLatex.lean",
            )
        }
        common["repository_commit"] = s["repository_commit"]
        common["repository_instructions"] = (
            self.compiler.project / "AGENTS.md"
        ).read_text(encoding="utf-8")
        role_prompt = "REVIEWER.md" if s["pending"] else "FORMALIZER.md"
        common["policy"] = {
            name: path.read_text(encoding="utf-8")
            for name, path in policy_documents().items()
            if name in {"AGENTS.md", "WORKFLOW.md", "PROTOCOL.md", role_prompt}
        }
        common["source"] = self.get(s["source"])
        common["source_ids"] = self.get(s["evidence"])
        if s.get("last_review"):
            common["feedback"] = self.get(s["last_review"]["review"])
        if s.get("repair_request"):
            return {
                **common,
                "action": "repair",
                "actor": s["formalizer"],
                "controller_error": s["repair_request"],
                "instruction": "Investigate the saved failure; return {unit, reason} to reopen its statement closure, or {reason} to revise the graph.",
            }
        if s["pending"]:
            return {
                **common,
                "action": "review",
                "actor": s["reviewer"],
                "packet": self.get(s["pending"]["packet"]),
            }
        if s["phase"] == "graph":
            return {
                **common,
                "action": "graph",
                "actor": s["formalizer"],
                "source": self.get(s["source"]),
                "source_ids": self.get(s["evidence"]),
                "previous_graph": self.get(s["graph"]) if s["graph"] else None,
            }
        if s["phase"] == "plan":
            return {
                **common,
                "action": "plan",
                "actor": s["formalizer"],
                "graph": self.get(s["graph"]),
                "project": str(self.compiler.project),
            }
        if s["phase"] == "statements":
            ready = [
                u
                for u in self.units()
                if u["id"] not in self.accepted()
                and set(u["depends_on"]) <= self.accepted()
            ]
            if not ready:
                if (
                    s.get("last_review")
                    and not s["last_review"]["accepted"]
                    and self.get(s["last_review"]["packet"])["kind"]
                    == "composition_review"
                ):
                    return {
                        **common,
                        "action": "repair",
                        "actor": s["formalizer"],
                        "instruction": "Return {unit, reason} to reopen a statement unit, or {reason} to rebuild the graph.",
                    }
                return {**common, "action": "compose", "actor": "controller"}
            u = sorted(ready, key=lambda unit: unit["id"])[0]
            return {
                **common,
                "action": "statement",
                "actor": s["formalizer"],
                "unit": u,
                "graph": self.get(s["graph"]),
                "plan": self.get(s["plan"]),
                "project": str(self.compiler.project),
            }
        if s["phase"] == "ready_to_freeze":
            return {**common, "action": "freeze", "actor": "controller"}
        if s["phase"] == "proofs":
            for layer in validate_plan(self.get(s["plan"]), self.get(s["graph"])):
                for uid in layer:
                    c = self.get(s["units"][uid]["candidate"])
                    for h in sorted(c["holes"], key=lambda h: h["start"]):
                        if h["declaration"] not in s["proofs"]:
                            return {
                                **common,
                                "action": "proof",
                                "actor": s["formalizer"],
                                "declaration": h["declaration"],
                                "unit": self.unit(uid),
                                "candidate": c,
                                "project": str(self.compiler.project),
                                "inventory": self.get(s["units"][uid]["inventory"]),
                            }
            return {**common, "action": "finish", "actor": "controller"}
        return {
            **common,
            "action": "complete",
            "actor": "controller",
            "result": self.get(s["final"]),
        }

    def dispatch(self, action, payload, actor):
        if action == "review":
            return self.submit_review(payload, actor)
        require(
            actor == self.state["formalizer"],
            "Only the Formalizer submits mathematical candidates",
        )
        if action == "graph":
            return self.submit_graph(payload)
        if action == "plan":
            return self.submit_plan(payload)
        if action == "statement":
            return self.submit_statement(payload)
        if action == "proof":
            fields(payload, ["declaration", "proof"])
            return self.prove(payload["declaration"], payload["proof"])
        if action == "repair":
            fields(payload, ["reason"], ["unit"])
            if "unit" in payload:
                return self.reopen(payload["unit"], payload["reason"])
            return self.restart_graph(payload["reason"])
        raise WorkflowError("Unknown submission action")
