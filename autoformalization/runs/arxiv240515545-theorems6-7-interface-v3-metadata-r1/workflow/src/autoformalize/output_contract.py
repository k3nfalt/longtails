"""Source-role inventory and explicit public-result packaging contracts.

These checks establish coverage and ownership, not semantic equivalence. The
independent reviewer must substantiate every classification and correspondence.
"""

import re
from .common import fields, require, text
from .layout import in_category
from .public_design import validate_design


def lean_tokens(code):
    """Erase nested comments/strings before syntax lints; preserve line boundaries."""
    out, i, depth, string = [], 0, 0, False
    while i < len(code):
        pair = code[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if code[i] == '\n' else ' '); i += 1; continue
        if string:
            if code[i] == '\\': out.append('  '); i += 2; continue
            if code[i] == '"': string = False
            out.append('\n' if code[i] == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; out.append(' '); i += 2; continue
        if pair == '--':
            end = code.find('\n', i); i = len(code) if end < 0 else end; continue
        if code[i] == '"': string = True; out.append(' '); i += 1; continue
        out.append(code[i]); i += 1
    require(not depth and not string, 'Unterminated Lean comment/string')
    return ''.join(out)


def budget_lambda(code):
    clean = lean_tokens(code)
    matches = re.findall(r'(?m)^(?:noncomputable\s+)?def budget\s*:[^\n]*?:=\s*(fun\b[^\n]+)$', clean)
    require(len(matches) == 1, 'Budget must be one explicit single-line lambda')
    return matches[0].strip()


def lint_budget_expression(expression, component=None, parameters=None):
    """Reject count-only shapes; names never determine a parameter's meaning.

    This is a narrow structural check, not proof of honest source classification.
    """
    clean = lean_tokens(expression).strip()
    body = clean.split('=>', 1)[-1].strip()
    binder = re.match(r'^fun\s+([^\W\d]\w*)\b', clean, re.UNICODE)
    parameter = binder.group(1) if binder else 'p'
    projection = r'\b' + re.escape(parameter) + r'\s*\.\s*([^\W\d]\w*)'
    # Remove only elementary decorative zero terms. This is deliberately not a
    # symbolic algebra engine; other disguises remain mandatory review failures.
    atom = r'\b' + re.escape(parameter) + r'\s*\.\s*[^\W\d]\w*'
    body = re.sub(r'\b0\s*\*\s*' + atom, '0', body, flags=re.UNICODE)
    body = re.sub(atom + r'\s*\*\s*0\b', '0', body, flags=re.UNICODE)
    refs = set(re.findall(projection, body, re.UNICODE))
    # Remove projections and multiplication/parentheses. This also catches renamed counts.
    rest = re.sub(projection, '', body, flags=re.UNICODE)
    bare = bool(refs) and not re.sub(r'[\s()*↑]', '', rest)
    allowed_exact = component and parameters and component.get('accuracy_independent_reason', '').strip() and all(
        parameters.get(n) == 'problem_data' for n in refs)
    if parameters is not None and refs:
        require(bool(refs & {n for n, role in parameters.items() if role == 'accuracy'}) or allowed_exact,
                'Nonconstant budget needs an effective accuracy dependency or a justified exact problem-size cost')
    require(not bare or allowed_exact, 'Bare parameter projection/product is not a derived complexity budget')
    arithmetic = re.sub(r'\b(?:Nat|Int|Real)\.(?:ceil|floor|cast|ofNat|toNat)\b', '', rest)
    arithmetic = re.sub(r'[\d\s()+*/^.,↑⌈⌉⌊⌋₊−-]', '', arithmetic)
    accurate = parameters is not None and any(parameters.get(n) == 'accuracy' for n in refs)
    require(not (len(refs) == 1 and not arithmetic) or accurate or allowed_exact,
            'Single-field count arithmetic is not a derived accuracy budget; scaling, offsets and rounding do not supply a rate')
    require(not re.fullmatch(r"[\w.']+\s+" + re.escape(parameter), body.strip('() ')),
            'Opaque budget helper: expand the sufficient-count formula')


def lint_public_budget(code, export=None):
    expression = budget_lambda(code)
    if export is None:
        lint_budget_expression(expression)
        return
    d = export['design']; b = d['budget']
    normalize = lambda x: re.sub(r'\s+', '', lean_tokens(x))
    require(normalize(expression) == normalize(b['expression']), 'Actual budget lambda differs from the reviewed design')
    roles = {p['field']: p['role'] for p in d['parameters']}
    if b['num_oracles'] == 1:
        lint_budget_expression(expression, b['components'][0], roles)
    else:
        lint_budget_expression(expression)
    for c in b['components']:
        lint_budget_expression(c['expression'], c, roles)
    return {'status': 'passed', 'expression': expression}

CLASSES = (
    "convergence_result",
    "supporting_proposition",
    "definition",
    "setup",
    "assumption",
    "parameter",
    "algorithm",
)


def distinct(values, label):
    require(
        isinstance(values, list)
        and all(isinstance(x, str) for x in values)
        and len(values) == len(set(values)),
        "Duplicate or malformed " + label,
    )


def exact_counts(actual, expected):
    require(
        isinstance(actual, dict)
        and actual.keys() == expected.keys()
        and all(type(actual[k]) is int and actual[k] == v for k, v in expected.items()),
        "Inventory/output counts do not match their records",
    )


def prerequisites(graph, targets):
    found = set(targets)
    while True:
        more = {
            e["provider"]
            for e in graph["edges"]
            if e["kind"] != "source_reference" and e["consumer"] in found
        }
        if more <= found:
            return found
        found |= more


def graph_inventory(graph, evidence):
    nodes = {n["id"]: n for n in graph["nodes"]}
    parameters = {
        n["id"] + "/" + o["id"]
        for n in nodes.values()
        for o in n["objects"]
        if o.get("parameter", True)
    }
    groups = {kind: [] for kind in CLASSES}
    source_results = []
    assumptions = {
        n["id"] + "/" + c["id"]
        for n in nodes.values()
        for c in n["clauses"]
        if c["kind"] == "assumption"
    }
    for n in nodes.values():
        c = n["classification"]
        fields(c, ["kind", "provenance", "reason", "evidence"])
        require(
            c["kind"] in CLASSES
            and c["provenance"] in {"source", "repository", "derived"},
            "Unknown mathematical classification or provenance",
        )
        compatible_roles = {
            "convergence_result": {"theorem", "lemma", "target"},
            "supporting_proposition": {"theorem", "lemma", "target"},
            "definition": {"definition"},
            "setup": {"setup"},
            "assumption": {"assumption", "setup", "definition"},
            "parameter": {"parameter", "definition"},
            "algorithm": {"algorithm"},
        }
        require(
            n["role"] in compatible_roles[c["kind"]],
            "Dependency role contradicts mathematical classification",
        )
        text(c["reason"], "source-role classification rationale")
        clause_kinds = {clause["kind"] for clause in n["clauses"]}
        if c["kind"] in {"convergence_result", "supporting_proposition"}:
            require(
                "proposition" in clause_kinds, "Result node needs a proposition clause"
            )
        else:
            require(
                "proposition" not in clause_kinds,
                "Definitions/setups/parameters cannot discharge claims; split supporting propositions into their own node",
            )
        distinct(c["evidence"], "classification evidence")
        require(
            c["evidence"] and set(c["evidence"]) <= evidence.keys(),
            "Classification needs source evidence",
        )
        require(
            c["kind"] != "convergence_result" or c["provenance"] != "derived",
            "Derived transport is supporting_proposition; public convergence results need source/repository provenance",
        )
        groups[c["kind"]].append(n["id"])
        if (
            c["kind"] in {"convergence_result", "supporting_proposition"}
            and c["provenance"] == "source"
        ):
            source_results.append(n["id"])
        if c["kind"] == "convergence_result":
            context = n.get("result_context")
            fields(context, ["setups", "hypotheses", "parameters"])
            allowed = prerequisites(graph, [n["id"]])
            for key, universe in (
                (
                    "setups",
                    set(groups["setup"])
                    | {
                        x["id"]
                        for x in nodes.values()
                        if x["classification"].get("kind") == "setup"
                    },
                ),
                ("hypotheses", assumptions),
                ("parameters", parameters),
            ):
                distinct(context[key], "result " + key)
                require(set(context[key]) <= universe, "Unknown result context " + key)
                require(
                    all(x.split("/")[0] in allowed for x in context[key]),
                    "Result context must belong to its statement/proof prerequisite closure",
                )
        else:
            require(
                "result_context" not in n,
                "Only a source convergence result has result_context",
            )
    required = prerequisites(graph, graph["targets"])
    convergence = required & set(groups["convergence_result"])
    inv = graph["inventory"]
    fields(
        inv,
        [
            "by_class",
            "source_results",
            "required_closure",
            "convergence_results",
            "assumptions",
            "parameters",
            "counts",
        ],
    )
    fields(inv["by_class"], CLASSES)
    for kind in CLASSES:
        distinct(inv["by_class"][kind], "classification inventory")
        require(
            set(inv["by_class"][kind]) == set(groups[kind]),
            "Classification inventory is not an exact partition",
        )
    for key, expected in (
        ("source_results", set(source_results)),
        ("required_closure", required),
        ("convergence_results", convergence),
        ("assumptions", assumptions),
        ("parameters", parameters),
    ):
        distinct(inv[key], key)
        require(set(inv[key]) == expected, "Inventory disagrees with computed " + key)
    exact_counts(
        inv["counts"],
        {
            **{k + "_nodes": len(v) for k, v in groups.items()},
            "nodes": len(nodes),
            "source_results": len(source_results),
            "required_closure": len(required),
            "public_results": len(convergence),
            "assumptions": len(assumptions),
            "parameters": len(parameters),
        },
    )
    return inv


def graph_checks(graph):
    return [
        "inventory:classification_partition",
        "inventory:recursive_closure",
        "inventory:source_result_completeness",
        "inventory:assumptions_and_parameters",
    ] + ["classification:" + n["id"] for n in graph["nodes"]]


def output_checks(plan, unit=None):
    contract = plan["output_contract"]
    exports = [
        e for e in contract["public_results"] if unit is None or e["unit"] == unit
    ]
    setups = [
        s
        for s in contract["setups"]
        if unit is None
        or s["unit"] == unit
        or any(e["node"] in s["results"] for e in exports)
    ]
    checks = [] if unit else ["output:result_bijection", "output:catalog_bijection"]
    for e in exports:
        checks.extend(
            prefix + e["node"]
            for prefix in (
                "output:public_result:",
                "output:parameter_roles:",
                "output:accuracy_contract:",
                "output:explicit_budget:",
                "output:source_adaptation:",
                "cost:headline_units:",
                "cost:execution_budget:",
                "cost:correspondence:",
            )
        )
    checks.extend("setup:compatibility:" + s["unit"] for s in setups)
    return checks


def review_clauses(unit, plan, graph):
    """Public wrappers share evidence, never duplicate source-node ownership."""
    nodes = {
        e["node"]
        for e in plan["output_contract"]["public_results"]
        if e["unit"] == unit["id"]
    }
    return sorted(
        set(unit["clauses"])
        | {
            n["id"] + "/" + c["id"]
            for n in graph["nodes"]
            if n["id"] in nodes
            for c in n["clauses"]
        }
    )


def declaration_contract(units, graph, inventory):
    nodes = {n["id"]: n for n in graph["nodes"]}
    observed = {d["name"]: d for d in inventory["declarations"]}
    for u in units:
        module = u["file"][:-5].replace("/", ".")
        for node, names in u["node_declarations"].items():
            require(
                all(n in observed and observed[n]["module"] == module for n in names),
                "Node declaration mapping is not owned by its selected module",
            )
            kinds = {observed[n]["kind"] for n in names}
            if nodes[node]["classification"]["kind"] in {
                "convergence_result",
                "supporting_proposition",
            }:
                require(
                    "theorem" in kinds,
                    "A source proposition must map to an actual theorem, not merely a definition",
                )
            else:
                require(
                    "theorem" not in kinds,
                    "A definition/context node cannot own a proof claim",
                )


def validate_output(plan, graph, reachable):
    contract = plan["output_contract"]
    fields(contract, ["schema_version", "public_results", "setups", "counts"])
    require(type(contract['schema_version']) is int and contract['schema_version'] == 3,
            'Public output contract requires schema_version 3; older runs use their preserved controller')
    require(
        isinstance(contract["public_results"], list)
        and isinstance(contract["setups"], list),
        "Public results and setups must be lists",
    )
    units = {u["id"]: u for u in plan["units"]}
    nodes = {n["id"]: n for n in graph["nodes"]}
    owners = {n: u["id"] for u in units.values() for n in u["nodes"]}
    declarations = {d: u["id"] for u in units.values() for d in u["declarations"]}
    exports, public_units, result_names, concrete_setups = {}, set(), set(), set()

    def proofs(values, consumer):
        distinct(values, "correspondence proof declarations")
        require(
            set(values) <= declarations.keys(),
            "Unknown correspondence proof declaration",
        )
        require(
            all(declarations[p] in reachable[consumer] | {consumer} for p in values),
            "Correspondence proof is not a public-result prerequisite",
        )

    for e in contract["public_results"]:
        fields(e, ["node", "unit", "result", "setup_unit", "spec", "budget", "cost", "design"])
        require(
            e["node"] in graph["inventory"]["convergence_results"]
            and e["node"] not in exports,
            "Each required convergence result needs exactly one public export",
        )
        require(
            e["unit"] in units and e["unit"] not in public_units,
            "Each public result needs its own module unit",
        )
        u = units[e["unit"]]
        require(
            in_category(u["file"], "Theorems")
            and e["result"] in u["declarations"]
            and e["result"].endswith(".result")
            and e["result"] not in result_names,
            "Public export must name its module's unique namespace.result",
        )
        namespace = e["result"].rsplit(".", 1)[0]
        require(
            e["budget"] == namespace + ".budget" and e["budget"] in u["declarations"],
            "Public budget must be a planned export in the result namespace",
        )
        require(
            e["setup_unit"] in units
            and in_category(units[e["setup_unit"]]["file"], "Setups")
            and e["spec"]
            == units[e["setup_unit"]]["file"][:-5].replace("/", ".") + ".spec"
            and e["spec"] in units[e["setup_unit"]]["declarations"],
            "Public spec must be a planned export in the setup module namespace",
        )
        concrete_setups.add(e["setup_unit"])
        require(
            {e["setup_unit"], owners[e["node"]]} <= reachable[e["unit"]] | {e["unit"]},
            "Public wrapper must depend on its source result owner and setup",
        )
        require(
            {owners[n] for n in nodes[e["node"]]["result_context"]["setups"]}
            <= reachable[e["setup_unit"]] | {e["setup_unit"]},
            "Concrete setup must own or depend on every source setup in the result context",
        )
        require(
            not u["nodes"] or u["nodes"] == [e["node"]],
            "Public modules cannot own unrelated source nodes; put support in Proofs/Setups",
        )
        cost = e["cost"]
        fields(cost, ["headline", "execution", "relationship"])
        for key in ("headline", "execution"):
            fields(cost[key], ["expression", "unit", "domain"])
            for name, value in cost[key].items():
                text(value, key + " cost " + name)
        require(
            cost["execution"]["unit"] == "template_oracle_calls"
            and cost["execution"]["domain"] == "Fin spec.numOracles → Nat",
            "Template execution budget counts calls separately for every oracle in Fin spec.numOracles → Nat",
        )
        relation = cost["relationship"]
        fields(relation, ["kind", "explanation", "proofs"])
        require(
            relation["kind"] in {"identity", "conversion"},
            "Unknown cost correspondence",
        )
        text(relation["explanation"], "cost correspondence explanation")
        proofs(relation["proofs"], e["unit"])
        if relation["kind"] == "identity":
            require(
                all(
                    cost["headline"][k] == cost["execution"][k]
                    for k in ("unit", "domain")
                ),
                "Different headline units/domains require an explicit cost conversion",
            )
        else:
            require(
                relation["proofs"],
                "Cost conversion needs a planned correspondence theorem",
            )
        validate_design(e, units, reachable, graph)
        lint_public_budget('noncomputable def budget : Params → Fin 1 → ℕ := ' + e['design']['budget']['expression'], e)
        exports[e["node"]] = e
        public_units.add(e["unit"])
        result_names.add(e["result"])
    require(
        set(exports) == set(graph["inventory"]["convergence_results"]),
        "Plan omitted a required convergence result",
    )
    require(
        public_units
        == {u["id"] for u in units.values() if in_category(u["file"], "Theorems")},
        "Every public module must map to exactly one required convergence result",
    )
    distinct(
        [units[uid]["file"] for uid in public_units],
        "public module paths, including reuse",
    )
    distinct(
        [units[uid]["file"] for uid in concrete_setups],
        "concrete setup module paths, including reuse",
    )
    for u in units.values():
        require(
            u["nodes"] or u["id"] in public_units,
            "Only a mapped public wrapper may have no owned graph nodes",
        )
    setup_units, setup_results = set(), set()
    for s in contract["setups"]:
        fields(
            s,
            [
                "unit",
                "results",
                "shared_hypotheses",
                "shared_parameters",
                "compatibility",
            ],
        )
        require(
            s["unit"] in units and s["unit"] not in setup_units,
            "Duplicate or unknown setup contract",
        )
        setup_units.add(s["unit"])
        distinct(s["results"], "setup consumers")
        require(
            s["results"]
            and set(s["results"]) <= exports.keys()
            and not set(s["results"]) & setup_results,
            "Each public result must occur in exactly one setup contract",
        )
        require(
            all(exports[n]["setup_unit"] == s["unit"] for n in s["results"]),
            "Setup contract disagrees with export mapping",
        )
        setup_results.update(s["results"])
        distinct(s["shared_hypotheses"], "shared hypotheses")
        distinct(s["shared_parameters"], "shared parameters")
        contexts = [nodes[n]["result_context"] for n in s["results"]]
        require(
            set(s["shared_hypotheses"])
            <= {h for c in contexts for h in c["hypotheses"]}
            and set(s["shared_parameters"])
            <= {p for c in contexts for p in c["parameters"]},
            "Shared setup context must name actual source hypotheses and parameters",
        )
        require(
            isinstance(s["compatibility"], list), "Setup compatibility must be a list"
        )
        distinct(
            [c.get("result") for c in s["compatibility"]], "setup compatibility results"
        )
        require(
            {c["result"] for c in s["compatibility"]} == set(s["results"]),
            "Setup compatibility must cover every consumer",
        )
        for c in s["compatibility"]:
            fields(c, ["result", "mode", "justification", "proofs"])
            require(
                c["mode"] in {"identical", "equivalent"},
                "Setup sharing needs identical or proved equivalent hypotheses",
            )
            text(c["justification"], "setup hypothesis/parameter compatibility")
            proofs(c["proofs"], exports[c["result"]]["unit"])
            ctx = nodes[c["result"]]["result_context"]
            if c["mode"] == "identical":
                require(
                    set(ctx["hypotheses"]) == set(s["shared_hypotheses"])
                    and set(ctx["parameters"]) == set(s["shared_parameters"]),
                    "Identical setup cannot silently strengthen/drop hypotheses or parameters",
                )
            else:
                require(
                    c["proofs"],
                    "Equivalent setup sharing needs a planned correspondence theorem",
                )
    require(
        setup_results == set(exports), "Setup contracts must cover all public results"
    )
    exact_counts(
        contract["counts"],
        {
            "convergence_results": len(exports),
            "public_modules": len(public_units),
            "setups": len(setup_units),
        },
    )


def catalog_contract(plan, catalog, inventory, unit_ids=None):
    """Match observed rows and declarations to the reviewed output contract."""
    units = {u["id"]: u for u in plan["units"]}
    selected = set(units) if unit_ids is None else set(unit_ids)
    exports = [
        e for e in plan["output_contract"]["public_results"] if e["unit"] in selected
    ]
    rows = catalog.get("rows")
    require(
        isinstance(rows, list) and len(rows) == len(exports),
        "Catalog/public-result count mismatch",
    )
    require(
        catalog.get("status") == ("passed" if exports else "not_applicable"),
        "Catalog verification did not pass",
    )
    observed = {
        d["name"]: d for d in inventory["declarations"] + inventory.get("providers", [])
    }
    by_name = {r.get("theorem"): r for r in rows}
    require(
        len(by_name) == len(rows) and set(by_name) == {e["result"] for e in exports},
        "Catalog result inventory differs from the plan",
    )
    for e in exports:
        row = by_name[e["result"]]
        module = units[e["unit"]]["file"][:-5].replace("/", ".")
        setup = units[e["setup_unit"]]["file"][:-5].replace("/", ".")
        require(
            row.get("module") == module
            and row.get("setup") == setup
            and row.get("namespace") == setup,
            "Catalog module/setup association differs from the reviewed export",
        )
        for key, expected_module in (
            ("result", module),
            ("budget", module),
            ("spec", setup),
        ):
            require(
                e[key] in observed and observed[e[key]]["module"] == expected_module,
                "Compiler declaration ownership differs from the output contract",
            )
        design = e.get('design')
        if design is not None:
            require(len(row['budgets']) == design['budget']['num_oracles'], 'Compiled oracle count differs from the public design')
            roles = {p['field']: p['role'] for p in design['parameters']}
            for actual, component in zip(row['budgets'], design['budget']['components']):
                lint_budget_expression(actual['value'], component, roles)
        proof_names = list(e["cost"]["relationship"]["proofs"])
        for s in plan["output_contract"]["setups"]:
            for c in s["compatibility"]:
                if c["result"] == e["node"]:
                    proof_names.extend(c["proofs"])
        # A public statement's inventory is intentionally one-hop. Full
        # composition/final inventories must resolve every planned proof witness.
        if unit_ids is None:
            require(
                all(
                    n in observed and observed[n]["kind"] == "theorem"
                    for n in proof_names
                ),
                "Cost/setup correspondence witnesses must be actual theorem declarations",
            )
    return {
        "expected_results": len(exports),
        "catalog_results": len(rows),
        "results": [e["result"] for e in exports],
        "status": "passed",
    }
