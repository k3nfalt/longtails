# Deepdive into LongTails

**LongTails** turns an optimization problem into a precise research task: choose a **Setup**, construct an algorithm, and prove its **Complexity**. Our framework formalizes all these steps.

## Library Structure

| Location | Role |
| --- | --- |
| [Template.lean](Template.lean) | Our main file. Defines the problem interface, oracle execution, and meaning of convergence. |
| [Setups/](Setups/) | States problem assumptions, available information, oracles, and accuracy criteria. |
| [Algorithms/](Algorithms/) | Defines methods as sequences of queries and updates, together with their outputs. |
| [Proofs/](Proofs/) | Derives supporting bounds from the algorithms and setup assumptions. |
| [Theorems/](Theorems/) | Exports explicit budgets and public convergence theorems. |

The generated [LongTails.lean](../LongTails.lean) at the repository root imports the library's Lean modules. The folders Algorithms and Proofs are only for convenience; we could have merged them into one folder.

## Setup

In mathematical optimization, we fix a **Setup,** and want to prove a **Complexity.**

**Setup.** Which functions are allowed? What can the algorithm query? What counts as success?

**Complexity.** How many calls to each oracle are sufficient to guarantee that success?

These questions are formalized in our main file [Template.lean](Template.lean), which defines templates for `Setup` and `Algorithm` in the `OracleTemplate` namespace.

`Setup` has the following complete structure. A concrete problem defines a value of this structure, conventionally named `spec`:

```lean4
structure Setup where
  numOracles : ℕ := 1
  Params : Type uP
  Public : Type uD
  Instance : Public → Type uI
  Query : Public → Type uQ
  Reply : Public → Type uR
  Output : Public → Type uO
  publicInput : Params → Public
  valid : Params → Prop
  admissible : (p : Params) → Instance (publicInput p) →
    Oracle (Query (publicInput p)) (Reply (publicInput p)) numOracles → Prop
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → Instance (publicInput p) →
    (Ω → Output (publicInput p)) → ProbabilityMeasure Ω → Prop
  allowedAlgorithm : (p : Public) → Algorithm (Query p) (Reply p) (Output p) numOracles → Prop :=
    fun _ _ => True
```

The `uP`, `uD`, and other universe names let these types have different universe levels. The fields describe the problem as follows:

| Field | Meaning |
| --- | --- |
| `numOracles` | Number of oracle interfaces, defaulting to one. A query selects an index in `Fin numOracles`, and the complexity budget gives a separate call allowance for each index. |
| `Params` | Type of all parameters used to state assumptions, accuracy, and the budget, including quantities the algorithm may not know. |
| `Public` | Type of information available to the algorithm constructor. |
| `Instance` | Type of the hidden problem for a given public input. It may contain an objective function, several functions, or operators. |
| `Query` | Type of the data sent to an oracle, in addition to its index. |
| `Reply` | Type of the data returned by an oracle. Multiple oracle interfaces share this type and the query type; tagged types can distinguish their payloads. |
| `Output` | Type of the algorithm's answer, such as a point or a pair of points. |
| `publicInput` | Maps full parameters to the public information. It determines which parameters the algorithm constructor can use. |
| `valid` | Predicate on parameters, such as positivity of smoothness constants and the requested accuracy. Convergence is required only for valid parameters. |
| `admissible` | Predicate relating parameters, a hidden instance, and an oracle. It states mathematical assumptions and what the oracle must return, including any sampling or noise assumptions. |
| `successful` | Predicate on parameters, a hidden instance, a random output, and its probability law. It defines the accuracy criterion, which may be deterministic, almost sure, in expectation, or with a specified probability. Measurability and integrability requirements, when needed, are stated by the concrete setup. |
| `allowedAlgorithm` | Optional restriction on the algorithm for a public input, for example requiring a particular update rule. It defaults to `True`, which imposes no family restriction. |

`Instance`, `Query`, `Reply`, and `Output` depend on `Public`: for example, the public input can specify the vector space in which queries and replies live. In `successful`, the implicit type `Ω` and its measurable-space instance describe the execution's randomness; `output : Ω → Output (publicInput p)` is the returned random value, and `P : ProbabilityMeasure Ω` supplies its distribution. The setup does not itself run an algorithm or choose a budget: `Convergence` connects these fields to an actual execution.

For a concrete example, [Setups/SmoothAndConvex.lean](Setups/SmoothAndConvex.lean) defines `spec` with one gradient oracle. Its hidden instance is a function $f : E \to \mathbb R$, and its queries, replies, and outputs are points in a real Hilbert space $E$. Valid parameters satisfy $L>0$, $R\ge0$, and $\varepsilon>0$. Admissibility requires convexity, exact gradient replies at every query, an $L$-Lipschitz gradient, and a minimizer within distance $R$ of $x_0$. Success means that there exists a minimizer $x^\star$ such that $f(\mathrm{output}(\omega))-f(x^\star)\le\varepsilon$ almost surely under the execution's probability law.

**Why distinguish `Params` and `Public`?** In this setup, the algorithm receives $L$ and $x_0$, along with the space in which it operates. The distance bound $R$ and accuracy $\varepsilon$ determine the execution budget, but are not passed to the algorithm constructor. The objective itself is accessed through the oracle.

A setup can also specify `allowedAlgorithm` when the result must concern a particular algorithm family. By default, this condition is `True`.

## Algorithm

An `Algorithm` stores a state and defines how to initialize it, choose a query, update from a reply, and produce an output. Its complete structure in [Template.lean](Template.lean) is:

```lean4
structure Algorithm (Query : Type uQ) (Reply : Type uR) (Output : Type uO) (numOracles : ℕ := 1) where
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  State : Type (max uQ uR uO)
  initial : Seed → State
  query : State → Fin numOracles × Query
  update : State → Reply → State
  output : State → Output
```

`Query`, `Reply`, `Output`, and `numOracles` are parameters of the structure. They specify the oracle interface and answer type supplied by the setup for a particular public input. The algorithm provides the following fields:

| Field | Meaning |
| --- | --- |
| `Seed` | Type of the algorithm's internal random seed. The default `Unit` has one value, `()`, and supports deterministic methods. A randomized method can use a seed containing an entire sequence of random choices. |
| `seedSpace` | Measurable-space structure on `Seed`, used to define its probability law. The square brackets make it a Lean instance. |
| `law` | Probability distribution of the algorithm's seed. The default is the point mass at `()`. A method with a different seed type supplies its own law. |
| `State` | Type of all information retained between calls, such as iterates, counters, momentum, accumulated averages, and unused random choices. Its universe level accommodates the query, reply, and output types. |
| `initial` | Constructs the initial state from the seed. Public parameters, such as a step size or initial point, can be captured when the algorithm is constructed. |
| `query` | Chooses the next oracle index and query payload from the current state. The index belongs to `Fin numOracles`, so it must designate an available oracle. |
| `update` | Takes the current state and one oracle reply and produces the next state. It can use information retained in the state to interpret the reply. |
| `output` | Converts the current state to the returned answer when execution ends. It can return a last iterate, an average, or another selection encoded by the state. |

Once the seed and oracle replies are fixed, these functions determine the execution. The seed is passed directly only to `initial`; later random choices must be retained in the state. The structure itself does not impose measurability on these functions: the convergence proof establishes whatever measurability and integrability the setup's success criterion requires.

In `Convergence`, the algorithm constructor receives only `Public`. The hidden instance and oracle are supplied separately to execution, so the algorithm learns about the instance through replies to its queries. There is no budget or stopping predicate among the algorithm's fields; `execute` controls termination using the external per-oracle budget.

For a concrete example, here is the core of [Algorithms/Gd.lean](Algorithms/Gd.lean):

```lean4
      State := E
      initial _ := x0
      query x := (0, x)
      update x reply := x - (1 / L) • reply
      output x := x
```

The state is the current point. The query `(0, x)` asks oracle number `0` for the gradient at $x$. Once the reply arrives, the algorithm takes a step of size $1/L$. Its output is the current point, so this method returns the **last iterate**.

**Who counts the calls?** `execute` does. A budget assigns a natural-number allowance to each oracle. Before making a query, execution checks the selected oracle's remaining allowance; after receiving a reply, it subtracts one and updates the state. If the next requested oracle has no calls left, execution returns the current output, even if other oracles still have calls available.

Thus, the budget measures **oracle calls**, not arithmetic operations or elapsed time. A method using a batch of gradient samples must represent those samples through the corresponding calls.

Randomized methods use an algorithm seed and its probability law. The oracle has a separate law over its sequence of seeds. `Convergence` evaluates success under the product of these two laws, making the algorithm's randomness independent of the oracle's randomness. Dependencies within the oracle's seed sequence are governed by the setup's assumptions.

## Theorem

`Convergence S budget` is the precise claim that a setup `S` can be solved within the given oracle-call budget. Its definition in [Template.lean](Template.lean) is:

```lean4
def Convergence (S : Setup)
    (budget : S.Params → Fin S.numOracles → ℕ) : Prop :=
  ∃ makeAlgorithm : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
    (∀ p, S.valid p →
      ∀ (I : S.Instance (S.publicInput p))
        (oracle : Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)) S.numOracles),
        S.admissible p I oracle →
          let A := makeAlgorithm (S.publicInput p)
          let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (budget p) seed.1 seed.2
          S.successful p I result
            ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩) ∧
    ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (makeAlgorithm (S.publicInput p))
```

The statement has the following parts:

| Part | Meaning |
| --- | --- |
| `budget` | Assigns a natural-number call allowance to each oracle for each choice of full parameters. It states an upper bound on sufficient oracle calls. |
| `∃ makeAlgorithm` | There must be one algorithm constructor that takes only public inputs. The proof supplies this constructor. |
| `∀ p, S.valid p →` | The guarantee must hold for every parameter choice satisfying the setup's validity conditions. |
| `∀ I oracle, S.admissible p I oracle →` | The same constructor must work for every hidden instance and oracle satisfying the setup's assumptions. |
| `execute oracle A (budget p)` | The accuracy claim concerns the actual output of the defined algorithm executed with the stated allowances. |
| `S.successful p I result ...` | That output must meet the setup's accuracy criterion under the product of the algorithm and oracle probability laws. |
| `S.allowedAlgorithm ...` | The constructed algorithm must satisfy any family restriction imposed by the setup, for every valid parameter choice. |

The order of the quantifiers matters. The algorithm constructor is chosen before the hidden instance and oracle, and receives neither of them as input. It cannot choose a different method by inspecting an unknown objective or its minimizer. Instances with the same public input use the same constructed algorithm, although their execution budgets may differ if their full parameters differ.

The budget is connected to execution, rather than merely attached to a rate formula. `execute` checks the selected oracle's remaining allowance before each call and decrements it after the reply. The proof must show success for the output produced by this execution, including any early termination caused by an exhausted allowance. A convergence theorem therefore proves a sufficient finite budget.

Each file in `Theorems/` must define an explicit `budget` and prove exactly one main theorem named `result`, with the structure `result : Convergence <setup namespace>.spec budget`. The file imports that setup directly; supporting lemmas belong in `Proofs/`.

[Proofs/GdConvex.lean](Proofs/GdConvex.lean) connects execution to gradient-descent iterates and proves the smoothness, convexity, descent, and accuracy lemmas. [Theorems/GdConvex.lean](Theorems/GdConvex.lean) then packages them into the public guarantee:

```lean4
noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈q.L * q.R ^ 2 / (2 * q.ε)⌉₊
```

Its theorem has the statement:

```lean4
Convergence LongTails.Setups.SmoothAndConvex.spec budget
```

This means that there exists an algorithm constructor using only public inputs such that, for **every valid parameter choice and every admissible objective and oracle**, execution within the stated budget satisfies the setup's accuracy criterion. The constructed algorithm must also satisfy `allowedAlgorithm`.

For this theorem, the constructor chooses gradient descent. Other methods can prove different budgets for the same setup: [Theorems/AcceleratedConvex.lean](Theorems/AcceleratedConvex.lean), for example, gives an accelerated guarantee.

## How Do We Check a Result?

Run these commands from the repository root:

```sh
./build.sh LongTails.Theorems.GdConvex
python3 run_comparator.py GdConvex.lean
```

The first command builds the theorem and its dependencies. The second uses [run_comparator.py](../run_comparator.py) to inspect the exported result and independently audit its convergence statement and budget against the named setup. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

**The key point:** a successful audit verifies the upper bound for the formal setup. You still need to check that the setup captures the intended mathematical problem.

To add a result, reuse an existing setup when its assumptions match, define the method in `Algorithms/`, develop its proof in `Proofs/`, and export its budget and `result` in `Theorems/`. Follow [AGENTS.md](../AGENTS.md) for repository conventions and the [main tutorial](../README.md#tutorial) for a complete worked workflow.
