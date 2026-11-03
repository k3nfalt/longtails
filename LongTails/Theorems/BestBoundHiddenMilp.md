# Best-bound branch-and-bound with a black-box LP solver: gap-dependent information complexity

This note explains the result formalized in
[BestBoundHiddenMilp.lean](BestBoundHiddenMilp.lean). The related files are:
- the [setup](../Setups/HiddenMixedIntegerLinear.lean);
- the [algorithm](../Algorithms/BestBoundBranchAndBound.lean);
- the upper-bound proof, [BestBoundBranchAndBound.lean](../Proofs/BestBoundBranchAndBound.lean);
- the matching lower bound, [HiddenMilpLowerBound.lean](../Proofs/HiddenMilpLowerBound.lean).

It improves the earlier repository result
[LpBranchAndBoundMilp.lean](LpBranchAndBoundMilp.lean): depth-first Dakin branch-and-bound
(B&B), which solves bounded MILPs in 2N − 1 LP calls.

## Summary

- **Upper bound.** Best-bound Dakin B&B solves a bounded mixed-integer linear program
  exactly, or certifies that it is infeasible, using at most

  `min(2N − 1, 1 + 4p·|G_λ|)` calls to an LP-relaxation oracle.

  Here:
  - N is the number of integer points of the variable box.
  - λ is any dual-feasible row multiplier (on instances whose root LP is infeasible no λ is
    needed, and the algorithm stops after at most one call).
  - G_λ is the set of integer points whose Lagrangian value does not exceed the MILP
    optimum.
  - The constraint matrix is hidden from the algorithm and seen only through the oracle.
- **Lower bound.** On a family of binary instances, no algorithm with the same oracle can
  guarantee an optimal output with fewer than C(p,r) − 1 calls. The same family has
  |G_0| ≤ #{S ⊆ [p] : |S| ≤ r}.
- **Consequence.** Over instances with |G| ≤ g, the best-bound bound is minimax-optimal up
  to a factor O(p) when r ≤ p/3.
- **Verification.** The upper bound is the main theorem `result`. The lower bound is the
  supporting lemma `not_convergence_hard`, together with the count `goodPoints_hard_card`.
  Both are machine-checked. The minimax-up-to-O(p) consequence combines them with the
  binomial estimate below, and that arithmetic is done on paper only.

## Why the information model changes (the old budget is vacuous)

In the earlier setup `BoundedMixedIntegerLinear`, all data (A, G, b, c, d, bounds) are
public. In the oracle framework of `LongTails/Template.lean`, the algorithm is built from the
public data, and its internal computation is free and may be noncomputable. An algorithm can
therefore compute an exact answer from the data and output it after **zero** oracle calls.
An exact answer always exists: the integer box is finite, and each fixed-z LP is bounded below
and attains its minimum. Hence every LP-call budget in that setup, including 2N − 1, is
vacuous as an oracle-complexity statement. (A Lean proof of the zero-call claim would need
LP attainment, which the repository formalizes only for bounded relaxations.)

The new setup fixes this by moving the constraint system into the hidden parameters:

- `Public` (what the algorithm sees): the dimensions p and q, the objective (c, d), and the
  integer bounds ℓ ≤ z ≤ u.
- `Params` (also hidden): the number of rows m, the data A, G, b, and an analysis-only
  multiplier λ.

This is the standard abstraction of "branch-and-bound on top of a black-box LP solver". The
algorithm learns the feasible region only through LP answers. The abstraction is in the
spirit of information-complexity models of mixed-integer convex optimization, where the
feasible set is hidden behind separation or first-order oracles. Examples are Basu–Oertel
(SIOPT 2017) and Basu–Jiang–Kerger–Molinaro, *Information complexity of mixed-integer convex
optimization* ([arXiv 2308.11153](https://arxiv.org/abs/2308.11153)). Those works use
separation or first-order oracles; here the oracle is the box-restricted LP relaxation used
by B&B.

The model's weakness is that real solvers do see the constraint data. For example, learned
GNN branching policies read A. Such policies are outside this oracle model.

## Problem class and assumptions

The class is that of the earlier setup:

min cᵀz + dᵀy subject to Az + Gy ≤ b, ℓ ≤ z ≤ u, z ∈ ℤ^p, y ∈ ℝ^q,

with arbitrary real data and arbitrary dimensions.

`valid` requires one of two things:

1. **A dual-feasible multiplier.** λ ≥ 0 and d + Gᵀλ = 0, which is dual feasibility for
   the free continuous block. Or:
2. **An infeasible root relaxation.** The root LP relaxation has no feasible point.

This is not a restriction relative to the earlier theorem. The earlier `valid` asks for a
root relaxation that is bounded below, and it is vacuously true for an infeasible root.

- **Infeasible root.** Condition 2 covers it.
- **Feasible and bounded-below root.** LP duality gives an optimal root dual (λ, μ) that
  satisfies condition 1. This is a pen-and-paper step; the Lean theorem only quantifies
  over instances that come with such a λ.
- **Converse.** Condition 1 itself implies that the root LP is bounded below. Weak duality
  bounds the objective below by L_λ(z), a linear function on the bounded box.

So, as λ ranges over all multipliers, the valid instances are exactly those of the earlier
setup. λ is an analysis parameter that the algorithm never sees, so the theorem holds
simultaneously for every dual-feasible λ, and the best bound is min over λ of |G_λ|. For
pure integer programs (q = 0), λ = 0 is always admissible.

In the infeasible-root case, the first call on the root box returns `none`. The algorithm
never obtains an incumbent and outputs `none`, which is correct
(`bestBound_solves_infeasible`).

No vertex, nondegeneracy, binary, rationality or total-unimodularity assumption is used.

## Oracle model and cost

The oracle model is the one of the earlier setup.

- **Query and reply.** A query is a box β of integer bounds. The reply is `none` exactly
  when the node LP over β (with z relaxed) is infeasible. Otherwise it is *some* optimal
  solution, possibly chosen adversarially and depending on the history.
- **Cost.** The cost is the number of LP calls.
- **No other access.** The algorithm cannot evaluate rows or solve LPs itself, because it
  does not know the rows.

## Algorithm and output

[`bestBoundBranchAndBound`](../Algorithms/BestBoundBranchAndBound.lean) is best-bound Dakin
B&B with lazy keys.

- **Open list.** Entries (box, key) are kept sorted by key. The root key is −∞.
- **Query.** Each step queries the LP of the head box (the minimum key).
- **Infeasible reply.** Discard the box.
- **No improvement.** Discard the box if the LP value does not beat the incumbent.
- **Integral reply.** If the LP solution is integral, it becomes the incumbent. Every open
  entry whose key is ≥ the new incumbent value is then discarded **without an LP call**.
- **Fractional reply.** Otherwise branch on a fractional coordinate j with value v. Insert
  the boxes with u_j := ⌊v⌋ and with ℓ_j := ⌊v⌋ + 1, both keyed by the node's LP value.
- **Output.** The incumbent. It uses only public data and oracle replies.

`allowedAlgorithm` is not used, because the theorem is a statement about the problem class.

## Guarantee

The public budget is

```
budget P _ = min (2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1) (1 + 4 * P.p * (goodPoints P).card)
```

Here `goodPoints P` is

G_λ = { z ∈ ℤ^p ∩ [ℓ,u] : L_λ(z) ≤ cᵀz′ + dᵀy′ for every MILP-feasible (z′,y′) },

where L_λ(z) = (c + Aᵀλ)ᵀz − λᵀb. So G_λ = {L_λ ≤ OPT}, and it is the whole box when the
MILP is infeasible (OPT = +∞).

For every valid instance, every admissible oracle, and every seed, the output after this many
calls satisfies `SolvesMixed`:
- `none` means the MILP is infeasible;
- `some (z, y)` is an exact global optimum.

The algorithm in fact stops by itself, with an empty open list, within that many calls. So
the bound also covers certification of optimality.

When λ is the optimal root dual, L_λ(z) = LP* + Δ_rc(z). For binary z this makes G_λ exactly
the set of "good points" of Dey–Dubey–Molinaro, defined with ≤ IPGap.

### Proof mechanism

The proof is in
[BestBoundBranchAndBound.lean](../Proofs/BestBoundBranchAndBound.lean).

1. **Weak duality** (`lagrangian_le_objective`): L_λ(z) ≤ cᵀz + dᵀy for every row-feasible
   (z, y). Only λ ≥ 0 and d + Gᵀλ = 0 are used, not the LP duality theorem.
2. **Lagrangian rounding** (`roundDown`). Round each coordinate of the node's LP solution
   down when its reduced coefficient (c + Aᵀλ)_k is ≥ 0, and up otherwise. The resulting
   integer point z′ lies in the node box and satisfies L_λ(z′) ≤ L_λ(z^N) ≤ the node value.
   On the branching coordinate, z′_j ∈ {⌊v⌋, ⌊v⌋ + 1}.
3. **Slack counter.** Define slack(z, β) := #{k : ℓ′_k < z_k} + #{k : z_k < u′_k} ≤ 2p.
   Branching never increases any point's slack. It strictly decreases the slack of z′ in the
   child containing it, because the new bound is set exactly at z′_j. This is why the bound
   does not depend on the ranges u − ℓ, even though the tree depth can be Σ(u − ℓ). For
   binary z each coordinate counts once, giving 2p|G| + 1, which is Dey–Dubey–Molinaro's
   Theorem 3.
4. **Best-bound bookkeeping.** While the incumbent is not optimal, the head key is ≤ OPT:
   the open box holding a better feasible point has a valid key ≤ its value, and the
   discarded keys are ≥ the incumbent value. Every LP call therefore processes an entry with
   key ≤ OPT. Two potentials control the count:
   - The *gap potential* Σ_open([key ≤ OPT] + 2·Σ_{z∈G∩box} slack(z, box)) drops by at
     least 1 per call. A good branching (value ≤ OPT) has z′ ∈ G, so it adds two key-≤-OPT
     children but pays them with slack. A bad branching creates children with key > OPT,
     which are not counted.
   - The repository's *box potential* Σ_open(2·#integer points − 1) also drops by at least 1
     per call, whatever the pop order. This gives the 2N − 1 term.

### Matching lower bound (formalized as a supporting lemma)

The lower bound is
[`not_convergence_hard`](../Proofs/HiddenMilpLowerBound.lean): for all p, r and B with
B + 2 ≤ C(p, r), **no algorithm** satisfies `Convergence spec budget` with a budget equal to B
on the family below. This holds even against history-independent oracles.

The family consists of pure binary programs with public c = 𝟙, ℓ = 0, u = 1, and hidden
constraints

P_w = { z ∈ [0,1]^p : ‖z − v‖₁ ≥ 1/2 for every v with |v| ≤ r, v ≠ w },

one instance for each w with |w| = r. Each cut is linear on the cube. Its integer points are
w together with all vertices of weight ≥ r + 1, so w is the unique optimum, with value r.

Every box answers exactly as for the polytope with all cuts unless its fixed-to-one set
equals w. The canonical answer's optimality needs only the single cut at v = 1_{F₁}. So each
call rules out at most one candidate. This adversary argument is formalized:
`hardOracle_admissible`, `hard_lower_bound`.

On the family, λ = 0 is admissible and |G_0| ≤ #{S : |S| ≤ r} = Σ_{k≤r} C(p,k)
(`goodPoints_hard_card`). This sum is ≤ 2·C(p,r) when r ≤ p/3. Hence:
- upper bound: 1 + 4p·|G_0| ≤ 1 + 8p·C(p,r);
- lower bound: no algorithm guarantees correctness below C(p,r) − 1 calls.

The dependence on |G| is therefore optimal up to a factor O(p) among *all* adaptive box-LP
algorithms, not only among B&B trees.

## Relation to the literature

- **Dey, Dubey, Molinaro**, *Branch-and-bound solves random binary IPs in poly(n)-time*
  ([arXiv 2007.15192](https://arxiv.org/abs/2007.15192), v4; SODA 2021; Theorem 3 and
  Lemmas 3–5).
  - **Their result.** Best-bound B&B on a *binary pure* IP, with any variable choice and any
    optimal LP solution, has at most 2n|G| + 1 nodes, where G is defined with the optimal
    root dual.
  - **Our upper bound extends it to:**
    - general integers, with a range-free factor 4p in place of the depth;
    - continuous variables;
    - arbitrary dual-feasible λ;
    - exact LP-call accounting, with lazy keys and discarding without calls.

  The upper bound alone is a short extension of their argument; we do not claim it as the
  main novelty. Their random-instance bounds on |G| (Corollary 3), and those of
  Borst–Dadush–Huiberts–Tiwari ([arXiv 2012.08346](https://arxiv.org/abs/2012.08346)) and
  Borst–Dadush–Mikulincer ([arXiv 2203.11863](https://arxiv.org/abs/2203.11863)), plug
  directly into our budget for binary instances.
- **Lower bounds for B&B trees.**
  - Jeroslow (1974) and Dey–Dubey–Molinaro
    ([arXiv 2103.09807](https://arxiv.org/abs/2103.09807)) give exponential worst-case lower
    bounds on the size of any (general-disjunction) B&B *tree*.
  - Cheng–Basu ([arXiv 2601.23249](https://arxiv.org/abs/2601.23249)) show exponential
    gaps for learned branching rules.
  - Our lower bound differs in two ways: it is parameterized by |G|, and it holds for every
    adaptive algorithm with the box-LP oracle, including algorithms that query singletons or
    arbitrary boxes outside any tree.
- **Black-box tree search.** Karp–Saks–Wigderson (FOCS 1986) and Montanaro
  ([arXiv 1906.10375](https://arxiv.org/abs/1906.10375)) model B&B as search in a *given*
  tree with a branching procedure and a lower-bound procedure. There, best-first is optimal
  among node-selection rules because it expands exactly the critical nodes. In our model the
  tree is not given: the algorithm may query any box, and the LP solution it receives is
  adversarial. Optimality of best-first over critical nodes does not transfer, and our lower
  bound is over all box-query strategies.
- **Information complexity of mixed-integer convex optimization**
  ([arXiv 2308.11153](https://arxiv.org/abs/2308.11153)). There the oracles are separation
  or first-order oracles, and the bounds are worst-case in the dimension and the precision.
  Here the oracle is an exact LP relaxation over boxes, and the bounds are instance-dependent
  through G.

## Improvement over the earlier repository result

- **Meaningful complexity.** The earlier 2N − 1 theorem is vacuous as oracle complexity,
  because zero calls suffice there. In the hidden model, LP calls measure information.
- **Never worse.** Since min(2N − 1, ·) is kept, the new bound is never worse than 2N − 1.
- **Much better on well-behaved instances.** On instances where |G| is small it is
  exponentially smaller, for example random binary packing instances, where
  |G| = n^{O(m)} w.h.p. by Dey–Dubey–Molinaro.
- **Tightness.** Tightness up to O(p) over classes with |G| ≤ g follows from the formalized
  lower-bound lemmas and the binomial estimate Σ_{k≤r} C(p,k) ≤ 2·C(p,r) for r ≤ p/3, which is
  checked on paper.

## Limitations

- **Worst case.** The worst case remains exponential, because |G| can equal N. The lower
  bound is a worst case over instances with |G| ≲ g, not instance optimality. Degenerate
  instances with huge G can finish in one call.
- **The factor p.** The lower bound does not show that the factor p in the upper bound is
  necessary.
- **The hard family.** It is binary with q = 0 and has about p^r hidden rows. Nothing is
  said about lower bounds on infeasible instances.
- **The oracle.** It is exact; LP tolerances and LP-solve costs are not modeled. The
  formalized lower bound is stated for the specific admissible oracle `hardOracle`. It is
  not formalized for oracles restricted to vertex solutions. A pen-and-paper argument
  suggests the same family also defeats any oracle whose answer depends only on the optimal
  face of the queried box: on every box the adversary answers, the two indistinguishable
  instances have the same optimal face. This is not machine-checked.
- **Existence of a correct oracle.** As in the earlier note, this relies on LP attainment.

## Scope requirement

The required direction was "improve the result from `LpBranchAndBoundMilp.lean`; do some
interesting and practical research". The new result keeps that theorem's problem class,
assumptions, oracle and exact-optimality criterion. It changes only what the algorithm may
see, and that change is what makes the LP-call count meaningful. It replaces the
enumeration budget 2N − 1 with a gap-dependent budget that explains when practical best-bound
B&B is fast, and it proves that this dependence cannot be improved beyond a factor O(p). The
earlier theorem and its files are unchanged.
