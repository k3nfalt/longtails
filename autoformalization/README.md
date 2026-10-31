# Autoformalization

This is a framework for automatic formalization existing mathematical results in
optimization. Receiving a TeX/pdf source package and target theorems, our framework
creates a dependency-complete collection of reviewed statements and checked
proofs using the LongTails interfaces.

The graph inventories all results in the recursive statement and proof closure,
separates convergence results from supporting propositions and definitions, and
counts scoped assumptions and parameters. Every required convergence result gets
one public module through an explicit source-to-export mapping, including results
used only as dependencies. Raw analytic proofs may remain grouped in Proofs.

```text
source + target → dependency graph → graph review → formalization global and local plans
  → statements → text/style + budget lint → elaboration + declaration lint
  → interface + catalog/rendering + topology checks → semantic statement review
  → aggregate statement checks + composition review → verified receipt → freeze
  → proof filling + immediate proof lint → preservation + strict build + proof Comparator
  → axiom audit + verified receipt reuse → export / integrate (repository's own lint + Comparator)
```

The target repository's `LongTails/Template.lean` and `AGENTS.md` are read live from
the run's pinned checkout and supplied to the agents; the workflow keeps no copy of
them, so upstream interface or convention changes apply to the next run without
changing the workflow.

The workflow not only guarantees the semantically faithful versions of the given theorems,
their used optimization algorithms, supporting lemmas, and setups such as assumptions and parameter conditions, but also
benefits from already-formalized results in LongTails lib (our examples in [RingmasterASGD](runs/arxiv250116168-theorem51) and [RennalaSGD](runs/arxiv230512387-theorem75-r6)). 
By running the workflow, you are contributing to create the first optimization-specific Lean library with SOTA algorithms, setups, and convergence theorems.

## Usage

Requires Python 3.11+, Git, Bash and the repository's pinned Lean/Lake environment.
The controller uses Python's standard library. `rg` enables local source search.
It is simple to start the workflow
```
Follow [instructions](AGENTS.md), [procedure](WORKFLOW.md) with the [response shemas](PROTCOL.md).
Formalize theorem <theorem_index_in_pdf-or-TeX_source-file> in <source-file-URL>
```
