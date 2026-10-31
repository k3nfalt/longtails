"""Deterministic integrity and acceptance checks, not mathematical judgments."""

import re

from .common import fields, require, text
from .output_contract import graph_inventory, validate_output

TOPICS = (
    "domains",
    "binding",
    "logic",
    "assumptions",
    "expressions",
    "algorithm",
    "probability",
    "convergence",
    "representations",
    "providers",
    "composition",
    "boundaries",
)
EDGES = {
    "requires_definition",
    "inherits_setup",
    "uses_result_in_statement",
    "uses_result_in_proof",
    "source_reference",
}
ROLES = {
    "definition",
    "setup",
    "algorithm",
    "assumption",
    "parameter",
    "lemma",
    "theorem",
    "target",
}
DIRECTIONS = ("source_to_candidate", "candidate_to_source")


def identity(value):
    text(value, "identifier")
    require(
        re.fullmatch(r"[A-Za-z][A-Za-z0-9_.-]*", value), f"Invalid identifier: {value}"
    )
    return value


def lean_name(value):
    text(value, "Lean name")
    require(
        re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_'₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'₀-₉]*)*", value
        ),
        "Use an explicit fully qualified Lean declaration name",
    )


def module_path(value):
    require(
        isinstance(value, str)
        and re.fullmatch(
            r"outputs/(Algorithms|Setups|Proofs|Theorems)/[A-Z][A-Za-z0-9]*\.lean",
            value,
        ),
        f"Use an existing oracle category and UpperCamelCase module: {value}",
    )


def unique(values, label):
    require(
        isinstance(values, list)
        and all(isinstance(v, str) for v in values)
        and len(values) == len(set(values)),
        f"Duplicate or malformed {label}",
    )


def layers(nodes, edges, *, include_proofs=True):
    pending = {node: set() for node in nodes}
    for edge in edges:
        if edge["kind"] == "source_reference" or (
            not include_proofs and edge["kind"] == "uses_result_in_proof"
        ):
            continue
        pending[edge["consumer"]].add(edge["provider"])
    result = []
    while pending:
        ready = sorted(key for key, dependencies in pending.items() if not dependencies)
        require(
            ready,
            "Circular mathematical dependencies; distinguish context references from prerequisites",
        )
        result.append(ready)
        for key in ready:
            del pending[key]
        for dependencies in pending.values():
            dependencies.difference_update(ready)
    return result


def validate_graph(graph, evidence, *, partial=False):
    fields(
        graph,
        [
            "nodes",
            "edges",
            "targets",
            "open_issues",
            "closure_explanation",
            "inventory",
        ],
    )
    require(isinstance(graph["nodes"], list) and graph["nodes"], "Graph needs nodes")
    nodes, clauses = {}, set()
    for node in graph["nodes"]:
        fields(
            node,
            [
                "id",
                "role",
                "statement",
                "clauses",
                "objects",
                "interpretations",
                "classification",
            ],
            ["result_context"],
        )
        identity(node["id"])
        require(
            node["id"] not in nodes and node["role"] in ROLES,
            "Duplicate node or unknown role",
        )
        text(node["statement"], "mathematical statement")
        require(isinstance(node["objects"], list), "Objects must be a list")
        object_ids = set()
        for obj in node["objects"]:
            fields(obj, ["id", "type", "scope", "depends_on", "role"], ["parameter"])
            require(
                type(obj.get("parameter", True)) is bool,
                "Object parameter marker must be boolean",
            )
            require(
                obj["role"] in {"parameter", "bound_variable", "defined_quantity"}
                and (obj["role"] == "parameter") == obj.get("parameter", True),
                "Object role must agree with its provider-argument parameter marker",
            )
            identity(obj["id"])
            require(obj["id"] not in object_ids, "Duplicate object identity")
            object_ids.add(obj["id"])
            text(obj["type"], "object mathematical type")
            text(obj["scope"], "object quantifier scope")
            unique(obj["depends_on"], "object dependencies")
        for obj in node["objects"]:
            require(set(obj["depends_on"]) <= object_ids, "Unknown object dependency")
        layers(
            object_ids,
            [
                {"provider": dep, "consumer": obj["id"], "kind": "requires_definition"}
                for obj in node["objects"]
                for dep in obj["depends_on"]
            ],
        )
        require(
            isinstance(node["clauses"], list) and node["clauses"],
            "Node needs mathematical clauses",
        )
        for clause in node["clauses"]:
            fields(clause, ["id", "kind", "text", "evidence", "justification"])
            require(
                clause["kind"]
                in {
                    "proposition",
                    "definition",
                    "assumption",
                    "parameter",
                    "algorithm",
                },
                "Unknown clause kind",
            )
            identity(clause["id"])
            key = node["id"] + "/" + clause["id"]
            require(key not in clauses, "Duplicate clause")
            clauses.add(key)
            text(clause["text"], "clause")
            text(clause["justification"], "clause interpretation/derivation")
            unique(clause["evidence"], "source evidence")
            require(
                clause["evidence"] and set(clause["evidence"]) <= evidence.keys(),
                "Missing or unknown source evidence",
            )
        require(
            isinstance(node["interpretations"], list), "Interpretations must be a list"
        )
        for item in node["interpretations"]:
            fields(item, ["decision", "basis", "effect_on_scope"])
            for key in item:
                text(item[key], key)
        nodes[node["id"]] = node
    unique(graph["targets"], "targets")
    require(
        graph["targets"] and set(graph["targets"]) <= nodes.keys(),
        "Unknown graph target",
    )
    edge_keys = set()
    require(isinstance(graph["edges"], list), "Edges must be a list")
    for edge in graph["edges"]:
        fields(edge, ["provider", "consumer", "kind", "arguments", "justification"])
        require(
            edge["provider"] in nodes and edge["consumer"] in nodes,
            "Unknown dependency node",
        )
        require(edge["kind"] in EDGES, "Unknown dependency type")
        key = (edge["provider"], edge["consumer"], edge["kind"])
        require(key not in edge_keys, "Duplicate dependency")
        edge_keys.add(key)
        require(
            isinstance(edge["arguments"], dict),
            "Dependency arguments need an explicit substitution map",
        )
        if edge["kind"] != "source_reference":
            provider = {
                obj["id"]
                for obj in nodes[edge["provider"]]["objects"]
                if obj.get("parameter", True)
            }
            consumer = {obj["id"] for obj in nodes[edge["consumer"]]["objects"]}
            require(
                set(edge["arguments"]) == provider,
                "Bind every provider object explicitly",
            )
            for binding in edge["arguments"].values():
                fields(binding, ["expression", "uses", "justification"])
                text(binding["expression"], "argument expression")
                text(binding["justification"], "argument scope/type justification")
                unique(binding["uses"], "argument object references")
                require(
                    set(binding["uses"]) <= consumer,
                    "Argument references an unknown consumer object",
                )
        text(edge["justification"], "dependency justification")
    text(graph["closure_explanation"], "recursive statement/proof closure explanation")
    require(isinstance(graph["open_issues"], list), "Open issues must be a list")
    if not partial:
        require(not graph["open_issues"], "Graph has unresolved issues")
    inventory = graph_inventory(graph, evidence)
    return {
        "clauses": sorted(clauses),
        "construction_layers": layers(nodes, graph["edges"]),
        "statement_layers": layers(nodes, graph["edges"], include_proofs=False),
        "inventory": inventory,
    }


def validate_plan(plan, graph):
    fields(plan, ["units", "adaptation", "deferred_obligations", "output_contract"])
    require(isinstance(plan["units"], list) and plan["units"], "Plan needs units")
    nodes = {node["id"]: node for node in graph["nodes"]}
    required = {
        node["id"] + "/" + c["id"] for node in nodes.values() for c in node["clauses"]
    }
    covered, ids, names, owners = set(), set(), set(), {}
    for unit in plan["units"]:
        fields(
            unit,
            [
                "id",
                "nodes",
                "file",
                "declarations",
                "node_declarations",
                "clauses",
                "depends_on",
                "mode",
                "detail",
            ],
        )
        identity(unit["id"])
        unique(unit["nodes"], "unit nodes")
        require(
            unit["id"] not in ids and set(unit["nodes"]) <= nodes.keys(),
            "Duplicate unit or unknown node",
        )
        ids.add(unit["id"])
        for node in unit["nodes"]:
            require(
                node not in owners,
                "Each graph node must belong to exactly one module unit",
            )
            owners[node] = [unit["id"]]
        require(unit["mode"] in {"new", "reuse"}, "Unit mode is new or reuse")
        if unit["mode"] == "new":
            module_path(unit["file"])
        else:
            require(
                isinstance(unit["file"], str)
                and re.fullmatch(
                    r"(?:outputs|LongTails|Mathlib|Init|Lean|Std)/[A-Za-z0-9_/]+\.lean",
                    unit["file"],
                ),
                "Invalid provider module path",
            )
        require(unit["declarations"], "Declare the named exports")
        unique(unit["declarations"], "declarations")
        for name in unit["declarations"]:
            lean_name(name)
            require(name not in names, "Declaration owned by more than one unit")
            names.add(name)
        require(
            isinstance(unit["node_declarations"], dict)
            and set(unit["node_declarations"]) == set(unit["nodes"]),
            "Map every owned node to its actual Lean declarations",
        )
        for mapped in unit["node_declarations"].values():
            unique(mapped, "node declaration mapping")
            require(
                mapped and set(mapped) <= set(unit["declarations"]),
                "Node declaration mapping needs planned exports",
            )
        unique(unit["clauses"], "unit clauses")
        require(
            set(unit["clauses"]) <= required and (unit["clauses"] or not unit["nodes"]),
            "Unknown or missing unit clause",
        )
        require(
            all(c.split("/")[0] in unit["nodes"] for c in unit["clauses"]),
            "Clause belongs to another node",
        )
        category = unit["file"].split("/")[1]
        allowed = {
            "algorithm": {"Algorithms", "Setups"},
            "setup": {"Setups"},
            "target": {"Proofs", "Theorems"},
            "lemma": {"Proofs"},
            "theorem": {"Proofs", "Theorems"},
            "definition": {"Algorithms", "Setups", "Proofs"},
            "assumption": {"Setups", "Proofs"},
            "parameter": {"Algorithms", "Setups", "Proofs"},
        }
        if unit["mode"] == "new":
            require(
                all(category in allowed[nodes[n]["role"]] for n in unit["nodes"]),
                "Plan routes a mathematical role to the wrong oracle directory",
            )
        require(not covered.intersection(unit["clauses"]), "Clause has multiple owners")
        covered.update(unit["clauses"])
        unique(unit["depends_on"], "unit dependencies")
        fields(
            unit["detail"],
            ["construction", "reuse_decisions", "edge_cases", "retrieval"],
        )
        text(unit["detail"]["construction"], "detailed construction plan")
        for key in ("reuse_decisions", "edge_cases", "retrieval"):
            require(isinstance(unit["detail"][key], list), key + " must be a list")
    require(
        covered == required and owners.keys() == nodes.keys(),
        "Plan must own every graph node and clause",
    )
    unique(
        [u["file"] for u in plan["units"] if u["mode"] == "new"],
        "new modules (group related declarations into one unit)",
    )
    unit_edges = []
    by_id = {unit["id"]: unit for unit in plan["units"]}
    for unit in plan["units"]:
        require(set(unit["depends_on"]) <= ids, "Unknown unit dependency")
        unit_edges.extend(
            {"provider": p, "consumer": unit["id"], "kind": "requires_definition"}
            for p in unit["depends_on"]
        )
    order = layers(ids, unit_edges)
    reachable = {}
    for layer in order:
        for uid in layer:
            reachable[uid] = set(by_id[uid]["depends_on"])
            for dep in by_id[uid]["depends_on"]:
                reachable[uid].update(reachable[dep])
    for edge in graph["edges"]:
        if edge["kind"] == "source_reference":
            continue
        for consumer in owners[edge["consumer"]]:
            require(
                set(owners[edge["provider"]]) <= reachable[consumer] | {consumer},
                "Plan dropped a graph prerequisite",
            )
    fields(
        plan["adaptation"],
        [
            "public_information",
            "algorithm_identity",
            "output",
            "cost",
            "probability",
            "source_correspondence",
        ],
    )
    for key in plan["adaptation"]:
        text(plan["adaptation"][key], "adaptation " + key)
    require(
        isinstance(plan["deferred_obligations"], list),
        "Deferred obligations must be a list",
    )
    unique(
        [o.get("id") for o in plan["deferred_obligations"]],
        "deferred obligation identities",
    )
    for obligation in plan["deferred_obligations"]:
        fields(obligation, ["id", "owner", "requirement"])
        require(obligation["owner"] in ids, "Unowned deferred obligation")
        text(obligation["id"], "obligation id")
        text(obligation["requirement"], "obligation requirement")
    validate_output(plan, graph, reachable)
    return order


def review_requirements(clause_ids):
    return [
        f"{direction}:{clause}" for direction in DIRECTIONS for clause in clause_ids
    ] + [f"topic:{topic}" for topic in TOPICS]


def validate_review(review, packet, reviewer):
    fields(review, ["basis", "reviewer", "checks", "blockers", "notes"])
    require(review["basis"] == packet["basis"], "Stale review basis")
    require(
        review["reviewer"] == reviewer,
        "Review must come from the registered independent reviewer",
    )
    require(
        isinstance(review["checks"], list)
        and all(isinstance(c, dict) for c in review["checks"]),
        "Checks must be a list of objects",
    )
    checks = {check.get("id"): check for check in review["checks"]}
    require(
        len(checks) == len(review["checks"])
        and set(checks) == set(packet["required_checks"]),
        "Review must cover every required obligation exactly once",
    )
    accepted = not review["blockers"]
    for key, check in checks.items():
        fields(check, ["id", "verdict", "source", "candidate", "comparison"])
        require(
            check["verdict"] in {"match", "mismatch", "unresolved", "not_applicable"},
            "Unknown review verdict",
        )
        text(check["comparison"], "concrete semantic comparison")
        require(
            isinstance(check["source"], list) and isinstance(check["candidate"], list),
            "Evidence references must be lists",
        )
        require(
            set(check["source"]) <= set(packet["source_ids"]), "Unknown source evidence"
        )
        require(
            set(check["candidate"]) <= set(packet["candidate_ids"]),
            "Unknown candidate evidence",
        )
        if (
            key.startswith(
                DIRECTIONS
                + (
                    "declaration:",
                    "obligation:",
                    "catalog:",
                    "inventory:",
                    "classification:",
                    "output:",
                    "setup:",
                    "cost:",
                    "node:",
                )
            )
            or key == "topic:composition"
        ):
            require(
                check["verdict"] != "not_applicable",
                "Mandatory correspondence/composition cannot be inapplicable",
            )
        if check["verdict"] != "not_applicable":
            require(
                check["source"] and check["candidate"],
                "Semantic comparison needs both evidence directions",
            )
        required_pointer = packet.get("required_candidate_evidence", {}).get(key)
        if required_pointer and check["verdict"] == "match":
            require(
                any(
                    p == required_pointer or p.startswith(required_pointer + "/")
                    for p in check["candidate"]
                ),
                "Public-interface match must cite its result-specific implementation evidence",
            )
        accepted &= check["verdict"] in {"match", "not_applicable"}
    require(
        isinstance(review["blockers"], list) and isinstance(review["notes"], list),
        "Review findings must be lists",
    )
    return accepted


def score_review(review, accepted):
    """Binary conjunction scores derived from a validated independent review.

    A score is protocol acceptance, not a calibrated probability of correctness.
    No arithmetic average can hide one failed or unknown comparison.
    """
    scores = {
        c["id"]: (
            None if c["verdict"] == "not_applicable" else int(c["verdict"] == "match")
        )
        for c in review["checks"]
    }
    return {
        "source_to_candidate": min(
            v for k, v in scores.items() if k.startswith("source_to_candidate:")
        ),
        "candidate_to_source": min(
            v for k, v in scores.items() if k.startswith("candidate_to_source:")
        ),
        "checks": scores,
        "overall": int(accepted),
        "rule": "all_applicable_checks_pass_and_no_blockers",
    }
