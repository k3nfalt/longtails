# LP-based branch-and-bound for bounded MILP: contribution and scope

This note explains the result formalized in
[LpBranchAndBoundMilp.lean](LpBranchAndBoundMilp.lean), with the
[setup](../Setups/BoundedMixedIntegerLinear.lean), the
[algorithm](../Algorithms/LpBranchAndBound.lean), and the supporting proofs
[LpBranchAndBound.lean](../Proofs/LpBranchAndBound.lean) and
[LpBranchAndBoundOracle.lean](../Proofs/LpBranchAndBoundOracle.lean).

**The theorem is classical.** The user's scope for this task was "a standard
setup for MILP and a proved theorem; the result need not be novel". The
mathematics below is the textbook finite-termination and node-count argument
for LP-based branch-and-bound (Land and Doig 1960; Dakin 1965). The new
contribution is only the faithful, machine-checked formalization in this
repository's oracle framework.

## Problem class

The problem is a mixed-integer linear program in the standard form of
Nemhauser–Wolsey and Conforti–Cornuéjols–Zambelli:

$$
\min_{z\in\mathbb Z^p,\;y\in\mathbb R^q}\; c^\top z + d^\top y
\quad\text{s.t.}\quad Az + Gy \le b,\qquad \ell \le z \le u .
$$

- Data: A ∈ ℝ^{m×p}, G ∈ ℝ^{m×q}, b ∈ ℝ^m, c ∈ ℝ^p and d ∈ ℝ^q are arbitrary
  real data, and ℓ, u ∈ ℤ^p.
- Dimensions: p, q and m are arbitrary.
- Constraints: equalities and sign constraints are expressed as pairs of rows
  of `Az + Gy ≤ b`.
- Continuous variables: y is free apart from the rows.
- All data are public (`Params`), and the instance type is `Unit`.

**Assumptions.**

1. *Finite integer bounds ℓ ≤ z ≤ u.* This is standard and necessary:
   without them, variable branching need not terminate.
2. *`valid`: the LP relaxation over the root box is bounded below.* In
   symbols, ∃ L such that every x satisfying `Az + Gy ≤ b` and `ℓ ≤ z ≤ u`
   (z real) has objective at least L. This is a condition on the public data
   only; it is LP dual feasibility.
   - **What it excludes.** It excludes exactly the instances whose root
     relaxation is feasible but unbounded below. Because z is bounded, every
     recession direction of that polyhedron has zero z-part. So in an
     excluded instance, a ray (0, r) with Gr ≤ 0 and dᵀr < 0 exists, and the
     MILP itself is either infeasible or unbounded below.
   - **Why it is assumed.** Real solvers report such instances as
     "infeasible or unbounded". Certifying which of the two holds would need
     an additional feasibility phase with a different oracle, so those
     instances are left out of scope.

No rationality, vertex, uniqueness, nondegeneracy, total-unimodularity or
binary restriction is imposed.

## Oracle model

The oracle is a *node LP-relaxation oracle*.

- **Query:** a box β = (ℓ′, u′) ∈ ℤ^p × ℤ^p, the branching bounds of a node.
- **Reply:** the oracle solves

  $$
  \min\; c^\top z + d^\top y \quad\text{s.t.}\quad Az+Gy\le b,\;
  \ell\le z\le u,\; \ell'\le z\le u',\; z\in\mathbb R^p .
  $$

  It must answer `none` exactly when this LP is infeasible. Otherwise it
  answers `some x` for some feasible optimal solution x (`IsRelaxationOracle`,
  via `SolvesRelaxation`).
- **No selection rule:** the optimal solution may be chosen adversarially,
  and may depend on the query history and the oracle seeds. Vertex or
  basic solutions are not required.
- **Nonvacuity:** under `valid`, every node LP is feasible-and-bounded or
  infeasible. Its infimum is then attained (Schrijver, *Theory of Linear and
  Integer Programming*, Cor. 7.1g), so a correct oracle exists.
  - The Lean file [LpBranchAndBoundOracle.lean](../Proofs/LpBranchAndBoundOracle.lean)
    proves this existence (`exists_relaxationOracle`) for the common case
    where the root relaxation is a bounded set. The proof uses compactness.
  - The general LP attainment theorem is not formalized.

The cost measure is the number of LP-oracle calls.

## Algorithm and output

[`lpBranchAndBound`](../Algorithms/LpBranchAndBound.lean) is depth-first
LP-based branch-and-bound with Dakin's variable dichotomy.

- **State:** a stack of boxes and an incumbent.
- **Start:** the stack is the root box, or empty if ℓ ≰ u.
- **Each step:** the algorithm pops the top box and queries the oracle on it.
  1. It prunes by infeasibility if the reply is `none`.
  2. It prunes by bound if an incumbent exists whose value is at most the
     node LP value.
  3. If every z-coordinate of the LP solution is integral, the solution
     becomes the new incumbent.
  4. Otherwise it branches on a fractional coordinate j with value v. The
     children are the node box with u′_j := ⌊v⌋ and with ℓ′_j := ⌊v⌋ + 1,
     and both are pushed.
- **Output:** the incumbent, as `Option (ℤ^p × ℝ^q)`.
- **Information used:** only the public data and the oracle replies.

`allowedAlgorithm` is not used: the theorem is an oracle-complexity
statement for the problem class, and the algorithm is constructed in the
proof.

## Guarantee

Let N = ∏_{j}(u_j − ℓ_j + 1)₊ be the number of integer points of the root
box. The public budget is

```
budget P _ = 2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1
```

That is 2N − 1 LP calls, or 2^{p+1} − 1 for binary z. For every valid
instance, every correct oracle and every seed, the output after this budget
satisfies `SolvesMixed`:

- `none` means the MILP has no feasible point;
- `some (z, y)` means (z, y) is MILP-feasible and its objective is at most
  that of every MILP-feasible point.

So the output is an exact global optimum or a certificate of infeasibility.

**Proof mechanism** (`LongTails/Proofs/LpBranchAndBound.lean`).

- **Invariant (`Good`):**
  1. every stack box contains an integer point;
  2. the incumbent is MILP-feasible;
  3. every MILP-feasible point strictly better than the incumbent lies in
     some stack box.
- **Potential:** Φ = Σ_{β ∈ stack} (2·#(β ∩ ℤ^p) − 1). It starts at most at
  2N − 1, and it decreases by at least one per oracle call while the stack is
  nonempty. Branching decreases it by exactly one, because both children are
  nonempty and partition the parent's integer points.
- **Termination:** after 2N − 1 calls the stack is empty. The calls that
  `execute` makes after that are no-ops, and the invariant gives `SolvesMixed`.

## Relation to the literature

- **Land and Doig (1960), Dakin (1965).** LP-based branch-and-bound and the
  dichotomy x_j ≤ ⌊v⌋ / x_j ≥ ⌈v⌉, with finite termination for bounded
  integer variables. Textbook treatments include Wolsey, *Integer
  Programming*, Ch. 7; Nemhauser and Wolsey, *Integer and Combinatorial
  Optimization*, §II.4; and Conforti, Cornuéjols and Zambelli, *Integer
  Programming* (2014), Ch. 9. The leaf-counting bound of 2N − 1 nodes is the
  standard folklore argument.
- **Jeroslow (1974),** "Trivial integer programs unsolvable by
  branch-and-bound", *Math. Programming* 6. There are infeasible binary
  programs on which variable branching needs 2^{⌈n/2⌉} nodes. So the
  exponential budget is essentially unavoidable for this algorithm family;
  it is not merely a limitation of the proof.
- **Dey, Dubey and Molinaro.** Random binary programs are solved by
  branch-and-bound with polynomially many nodes with good probability
  ([arXiv 2007.15192](https://arxiv.org/abs/2007.15192), SODA 2021).
  Exponential lower bounds hold even with general disjunctions
  ([arXiv 2103.09807](https://arxiv.org/abs/2103.09807)). See also Basu,
  Conforti, Di Summa and Jiang
  ([arXiv 2003.05023](https://arxiv.org/abs/2003.05023)) for branch-and-bound
  versus cutting planes, and Balcan et al., "Learning to Branch" (ICML 2018,
  [arXiv 1803.10150](https://arxiv.org/abs/1803.10150)) for data-driven tree
  sizes.
- **Faster algorithms exist.** Lenstra's algorithm and its successors solve
  MILP in polynomial time for fixed p. Plain enumeration with an LP oracle
  over y for each fixed integer z uses N calls instead of 2N − 1. This result
  makes no claim of a better complexity; it formalizes the standard
  relaxation-based algorithm.

## Limitations

- **Worst case:** the budget is exponential in p, and it ignores pruning
  effectiveness and node-selection rules. Best-bound search and strong
  branching are not analyzed.
- **Unbounded relaxations:** instances whose root relaxation is unbounded
  below are excluded by `valid`. See above for exactly what they are.
- **LP-solver cost:** each LP solve counts as one exact oracle call. Numerical
  tolerances and the cost of the LP solves themselves are not modeled.
- **Formalized existence:** the existence of a correct oracle is formalized
  only for a bounded root relaxation; general instances rely on LP theory
  (Cor. 7.1g).
