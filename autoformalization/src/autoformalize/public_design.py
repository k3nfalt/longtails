"""Versioned public-interface designs; semantic truth still needs review/proofs."""

import re

from .common import fields, require, text

ROLES = {"problem_data", "accuracy", "known_input", "analysis_bound", "family_setting"}
MODES = {"expectation", "deterministic", "almost_sure", "high_probability"}


def nonempty_list(value, label):
    require(isinstance(value, list) and value, label + " must be a nonempty list")


def names(value, label):
    require(
        isinstance(value, list)
        and all(isinstance(x, str) and x.strip() for x in value)
        and len(set(value)) == len(value),
        label + " must contain distinct names",
    )


def validate_design(e, units, reachable, graph):
    d = e["design"]
    fields(d, ["params", "parameters", "tuning", "output", "budget", "adaptation"])
    declarations = {n: u["id"] for u in units.values() for n in u["declarations"]}
    available = reachable[e["unit"]] | {e["unit"]}

    def declaration(n, label, category=None):
        require(
            isinstance(n, str) and n in declarations and declarations[n] in available,
            label + " must name a planned prerequisite declaration",
        )
        if category:
            require(
                "/" + category + "/" in units[declarations[n]]["file"],
                label + " has wrong module role",
            )

    def proofs(xs):
        nonempty_list(xs, "Design proof obligations")
        names(xs, "Design proofs")
        for n in xs:
            declaration(n, "Design proof", "Proofs")

    declaration(d["params"], "Params structure", "Setups")
    nonempty_list(d["parameters"], "Parameter ledger")
    roles = {}
    for p in d["parameters"]:
        fields(p, ["field", "role", "public", "justification"])
        require(
            isinstance(p["field"], str)
            and re.fullmatch(r"[^\W\d]\w*", p["field"], re.UNICODE),
            "Invalid parameter field",
        )
        require(
            p["field"] not in roles and p["role"] in ROLES,
            "Duplicate field or forbidden parameter role (derived tuning/counts cannot be Params)",
        )
        require(type(p["public"]) is bool, "Parameter public flag must be Boolean")
        require(
            not (p["role"] == "analysis_bound" and p["public"]),
            "Analysis-only information cannot be public",
        )
        text(p["justification"], "Parameter justification")
        roles[p["field"]] = p["role"]
    require(
        "accuracy" in roles.values(),
        "Public accuracy result needs an accuracy parameter",
    )
    known = {p["field"] for p in d["parameters"] if p["public"]}

    def expression(x, allowed):
        text(x["expression"], "Lean expression")
        names(x["uses"], "Expression parameter dependencies")
        require(set(x["uses"]) <= allowed, "Unknown or unavailable expression input")
        refs = set(re.findall(r"\bp\.([^\W\d]\w*)", x["expression"], re.UNICODE))
        require(
            refs == set(x["uses"]),
            "Expression uses must exactly enumerate p.field references",
        )

    require(
        isinstance(d["tuning"], list),
        "Tuning must be a list (empty only if the method has none)",
    )
    seen = set()
    for t in d["tuning"]:
        fields(t, ["name", "declaration", "expression", "uses", "proofs"])
        text(t["name"], "Tuning name")
        require(t["name"] not in seen, "Duplicate tuning name")
        seen.add(t["name"])
        declaration(t["declaration"], "Tuning definition", "Algorithms")
        expression(t, known)
        proofs(t["proofs"])
    o = d["output"]
    fields(
        o, ["kind", "algorithm", "selector", "criterion", "probability_mode", "proofs"]
    )
    require(
        o["kind"] in {"last", "best", "random", "average", "certificate"},
        "Unknown output selection kind",
    )
    require(o["probability_mode"] in MODES, "Unknown success probability mode")
    for key in ("algorithm", "selector"):
        declaration(o[key], key, "Algorithms")
    text(o["criterion"], "Inline success criterion")
    proofs(o["proofs"])
    criterion_fields = set(
        re.findall(r"\bp\s*\.\s*([^\W\d]\w*)", o["criterion"], re.UNICODE)
    )
    require(
        {n for n, role in roles.items() if role == "accuracy"} <= criterion_fields,
        "Accuracy labels must refer to fields in the actual declared success criterion",
    )
    b = d["budget"]
    fields(b, ["expression", "num_oracles", "components", "boundary_cases"])
    text(b["expression"], "Complete Lean budget lambda")
    require(
        re.match(r"^fun\s+p\s+", b["expression"]),
        "Budget lambda must use Params binder p",
    )
    require(
        type(b["num_oracles"]) is int and b["num_oracles"] > 0,
        "Positive oracle count required",
    )
    nonempty_list(b["components"], "Budget components")
    require(
        [c.get("oracle") for c in b["components"]] == list(range(b["num_oracles"]))
        and all(type(c.get("oracle")) is int for c in b["components"]),
        "Budget components must cover every oracle exactly once in order",
    )
    for c in b["components"]:
        fields(
            c, ["oracle", "expression", "uses", "accuracy_independent_reason", "proofs"]
        )
        expression(c, set(roles))
        proofs(c["proofs"])
        require(
            isinstance(c["accuracy_independent_reason"], str),
            "Accuracy-independent reason must be text",
        )
        if not any(roles[n] == "accuracy" for n in c["uses"]):
            text(
                c["accuracy_independent_reason"],
                "Accuracy-independent component needs an explicit justification",
            )
    nonempty_list(b["boundary_cases"], "Rounding/domain boundary obligations")
    for case in b["boundary_cases"]:
        fields(case, ["case", "reason", "proofs"])
        text(case["case"], "Boundary case")
        text(case["reason"], "Boundary justification")
        proofs(case["proofs"])
    a = d["adaptation"]
    fields(a, ["kind", "source_nodes", "reason", "proofs", "approval"])
    require(
        a["kind"] in {"equivalent", "derived", "approved_departure"},
        "Unknown adaptation kind",
    )
    nonempty_list(a["source_nodes"], "Adaptation source nodes")
    names(a["source_nodes"], "Adaptation source nodes")
    require(
        e["node"] in a["source_nodes"]
        and set(a["source_nodes"]) <= {n["id"] for n in graph["nodes"]},
        "Adaptation must identify its source result and known source nodes",
    )
    text(a["reason"], "Adaptation justification")
    proofs(a["proofs"])
    if a["kind"] == "approved_departure":
        text(a["approval"], "Exact user approval evidence")
    else:
        require(
            a["approval"] is None,
            "Approval must be null for source-preserving adaptation",
        )


def design_declarations(e):
    d = e["design"]
    return {
        d["params"],
        e["spec"],
        e["budget"],
        d["output"]["algorithm"],
        d["output"]["selector"],
    } | {t["declaration"] for t in d["tuning"]}


def design_proofs(e):
    d = e["design"]
    groups = (
        [d["output"], d["adaptation"]]
        + d["tuning"]
        + d["budget"]["components"]
        + d["budget"]["boundary_cases"]
    )
    return {p for g in groups for p in g["proofs"]}


def observed_design(e, inventory):
    records = {
        r["name"]: r for r in inventory["declarations"] + inventory.get("providers", [])
    }
    require(
        design_declarations(e) | design_proofs(e) <= records.keys(),
        "Public design declarations/proofs missing from compiler evidence",
    )
    params = records[e["design"]["params"]]
    require(
        e["design"]["params"] in records[e["spec"]].get("used", []),
        "Design Params structure must be used by the actual spec",
    )
    require(
        "structure_fields" in params, "Params must be an inspected concrete structure"
    )
    require(
        set(params["structure_fields"])
        == {p["field"] for p in e["design"]["parameters"]},
        "Parameter ledger differs from actual Lean structure fields",
    )
    require(
        all(records[n]["kind"] == "theorem" for n in design_proofs(e)),
        "Design proof witnesses must be actual theorem declarations",
    )
    for n in design_declarations(e) - {e["design"]["params"]}:
        require(
            records[n]["kind"] == "definition",
            "Algorithm, selector, tuning, spec and budget must be actual definitions",
        )
