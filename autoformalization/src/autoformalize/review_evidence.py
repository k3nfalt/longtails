"""Bounded review packets with immutable, deduplicated compiler/source evidence."""

import json

from .common import canonical, digest, require, scoped
from .public_design import design_declarations, design_proofs, observed_design

MAX_PACKET_BYTES = 64_000_000


def packet_bytes(packet):
    # Includes the CLI's larger pretty-printed representation, UTF-8 and final LF.
    return (
        len(
            json.dumps(packet, indent=2, ensure_ascii=False, allow_nan=False).encode(
                "utf-8"
            )
        )
        + 1
    )


def bounded_packet(packet):
    require(
        packet_bytes(packet) < MAX_PACKET_BYTES,
        "Review/task packet reaches 64 MB; narrow the source/unit or use referenced evidence; no evidence was silently truncated",
    )
    return packet


def closure(plan, ids):
    units = {u["id"]: u for u in plan["units"]}
    result = set(ids)
    while True:
        more = {d for uid in result for d in units[uid]["depends_on"]}
        if more <= result:
            return result
        result |= more


def attach_interface_evidence(run, candidate):
    plan = candidate["plan"]
    exports = [
        e
        for e in plan["output_contract"]["public_results"]
        if "unit" not in candidate or e["unit"] == candidate["unit"]["id"]
    ]
    if not exports:
        return candidate
    selected = closure(plan, [e["unit"] for e in exports])
    units = {u["id"]: u for u in plan["units"]}
    inventories = {}
    sources = {}
    for uid in sorted(selected):
        if "unit" in candidate and uid == candidate["unit"]["id"]:
            inv = candidate["inventory"]
        else:
            key = run.state["units"][uid].get("inventory")
            require(
                key, "Missing accepted compiler evidence for public prerequisite " + uid
            )
            inv = run.get(key)
        inventories[uid] = inv
        path = scoped(run.compiler.project, units[uid]["file"])
        source = path.read_text(encoding="utf-8")
        snapshot = {
            "file": units[uid]["file"],
            "sha256": digest(path.read_bytes()),
            "source": source,
        }
        key = run.put(snapshot)
        sources[uid] = {
            "file": snapshot["file"],
            "sha256": snapshot["sha256"],
            "artifact": key,
            "path": str(run.root / "objects" / (key + ".json")),
        }
        if len(source.encode("utf-8")) <= 64_000:
            sources[uid]["source"] = source
    # Validate each result against just its own closure, not unrelated declarations.
    for e in exports:
        own = closure(plan, [e["unit"]])
        records = {}
        for uid in sorted(own):
            for r in inventories[uid]["providers"] + inventories[uid]["declarations"]:
                previous = records.get(r["name"])
                if previous is None or "type_tree" in r:
                    records[r["name"]] = r
        observed_design(e, {"declarations": list(records.values())})
    return {
        **candidate,
        "interface_evidence": {
            "sources": sources,
            "inventories": inventories,
            "results": {
                e["node"]: {
                    "design": e["design"],
                    "source_units": sorted(closure(plan, [e["unit"]])),
                    "required_declarations": sorted(
                        design_declarations(e) | design_proofs(e)
                    ),
                }
                for e in exports
            },
        },
    }


def compact_candidate(run, candidate):
    """Keep all inventory records addressable, without repeating ASTs in packets."""
    evidence = {}

    def record(r):
        name = r["name"]
        key = run.put(r)
        entry = {
            "artifact": key,
            "path": str(run.root / "objects" / (key + ".json")),
            "sha256": key,
            "module": r["module"],
            "kind": r["kind"],
        }
        for field in ("type_text", "value_repr", "structure_fields"):
            if field in r and len(canonical(r[field]).encode("utf-8")) <= 8_000:
                entry[field] = r[field]
        # Prefer a record with expression trees, but keep every distinct record reference.
        if name not in evidence:
            evidence[name] = {"records": [], "preferred": entry}
        if key not in [x["artifact"] for x in evidence[name]["records"]]:
            evidence[name]["records"].append({"artifact": key, "path": entry["path"]})
        if "type_tree" in r:
            evidence[name]["preferred"] = entry
        return name

    def walk(value):
        if isinstance(value, dict):
            if isinstance(value.get("declarations"), list) and all(
                isinstance(r, dict) and "name" in r for r in value["declarations"]
            ):
                return {
                    "declarations": [record(r) for r in value["declarations"]],
                    "providers": [record(r) for r in value.get("providers", [])],
                    "unexpanded_dependencies": value.get("unexpanded_dependencies", []),
                }
            return {k: walk(v) for k, v in value.items()}
        if isinstance(value, list):
            return [walk(v) for v in value]
        return value

    result = walk(candidate)
    if evidence:
        result["declaration_evidence"] = evidence
    return result


def required_interface_citations(candidate):
    results = candidate.get("interface_evidence", {}).get("results", {})
    return {
        f"output:{check}:{node}": f"candidate/interface_evidence/results/{node}"
        for node in results
        for check in (
            "parameter_roles",
            "accuracy_contract",
            "explicit_budget",
            "source_adaptation",
        )
    }
