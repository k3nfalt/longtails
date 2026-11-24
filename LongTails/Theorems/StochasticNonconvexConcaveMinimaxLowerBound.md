# Randomized lower bound for stochastic nonconvex–concave minimax

Lean result: [`StochasticNonconvexConcaveMinimaxLowerBound.result`](StochasticNonconvexConcaveMinimaxLowerBound.lean)
(`NonConvergence spec budget`).
Setup: [`LongTails/Setups/StochasticNonconvexConcaveMinimax.lean`](../Setups/StochasticNonconvexConcaveMinimax.lean).
Hard instance and proof: `LongTails/Proofs/NcConcave*.lean`. The entry points are
[`NcConcaveLower.exists_failure`](../Proofs/NcConcaveLower.lean),
[`NcConcaveAssembly.hard_admissible`](../Proofs/NcConcaveAssembly.lean) and
[`NcConcaveFailure.stationarity_lower`](../Proofs/NcConcaveFailure.lean).

## Setting

We minimize the primal value function Φ(x) = max_{y ∈ Y} f(x, y) over x ∈ X.
- **Sets.** The primal space is ℝ^{2d}, split into two blocks. X is the product of a Euclidean ball of radius
  `radiusU = 2^7 √(Δ/L)` in the first block and a ball of radius `radiusAB = 2^33 ε/L` in the second. The dual set Y is
  the ball of radius D/2 in ℝ^d, so diam Y = D. Both sets are public.
- **Function class.** f is
  - differentiable in each variable;
  - jointly L-smooth on X × Y, in the sense that the partial gradients are jointly L-Lipschitz;
  - concave in y on Y for every x ∈ X;
  - such that the initial primal–dual gap satisfies max_{y∈Y} f(0, y) − inf_{x∈X} f(x, 0) ≤ Δ.
    Because 0 ∈ Y, this also implies Φ(0) − inf_X Φ ≤ Δ.
- **Oracle.** Queries are feasible pairs (x, y) ∈ X × Y. Each query receives one fresh IID sample ξ, with an arbitrary
  sample law, and returns G(x, y, ξ). The reply must be jointly measurable, satisfy E G = (∇ₓf, ∇ᵧf), and have
  E‖G − ∇f‖² ≤ σ². σ = 0 is allowed, which gives the deterministic first-order oracle.
- **Algorithms.** Arbitrary randomized adaptive algorithms (`OracleTemplate.Algorithm`) with any seed law. They may
  return any primal point x̂ ∈ ℝ^{2d}.
- **Accuracy.** The algorithm succeeds if E[2L · dist(x̂, prox(x̂))] ≤ ε. Here prox(x̂) is the set of minimizers over X
  of Φ(z) + L‖z − x̂‖². In the notation of Wu–Gu–Yang, this quantity is ‖∇φ_{1/(2L)}(x̂)‖ for φ = Φ + ι_X, i.e. the
  standard Moreau-envelope (Φ-)stationarity measure of nonconvex–concave optimization. Because the Lean definition uses
  the infimum distance to the set of exact proximal points, the statement makes no uniqueness assumption.
- **Nonempty proximal sets.** For every admissible f the proximal set is nonempty: f is jointly continuous and Y is
  compact, so Φ is continuous on the compact set X. For the hard instance this is proved in Lean inside
  `NcConcaveFailure.stationarity_lower`, using lower semicontinuity of Φ̂ (`value_lsc`). Hence the failure statement
  is never satisfied vacuously through an empty proximal set (where the infimum distance would be 0).

## Result

Assume
- L, Δ, D > 0 and σ ≥ 0;
- 2^67 ε² ≤ LΔ and 2^36 ε ≤ LD (the small-ε regime);
- the dimension satisfies d ≥ 2^180 (LΔ/ε²)^9 (LD/ε)^7 (1 + σ²LD/ε³).

Then for every randomized algorithm and every query budget

  N ≤ ⌊ L²DΔ / (2^100 ε³) + L³D²Δσ² / (2^165 ε⁶) ⌋

there is an admissible instance and oracle on which E[2L·dist(x̂, prox(x̂))] > ε.

In other words, every algorithm, randomized or not, needs Ω(L²DΔε⁻³ + L³D²Δσ²ε⁻⁶) stochastic gradient queries.

## Prior work and what is new

- **Lower bound for zero-respecting methods.** Wu–Gu–Yang, arXiv:2609.14233 (Thm 4.1, Thm 5.5, Cor. 5.6), prove
  exactly these rates, but only for *zero-respecting* methods. Their §6 says: "A natural next step is to determine
  whether the same rates hold for arbitrary, possibly randomized, first-order algorithms … an important open problem."
- **Other recent lower bounds.** The VR lower bound of arXiv:2610.01662 also covers only zero-respecting (randomized)
  methods. So do the NC–SC lower bounds of arXiv:2609.35206 and arXiv:2609.30877.
- **Deterministic algorithms.** The all-algorithm deterministic lower bound of Pan–Zheng–Li, arXiv:2609.14235, covers
  deterministic algorithms only.
- **Upper bounds.**
  - Deterministic: Lin–Jin–Jordan (COLT 2020, Cor. A.8) give Õ(L²DΔε⁻³).
  - Stochastic: SAPD+ (Zhang–Aybat–Gürbüzbalaban, NeurIPS 2022, Thm 5) gives O(L³D²G₀ε⁻⁶) in the primal–dual-gap
    parameterization G₀ = max_y f(x₀, y) − inf_x f(x, y₀) at the initial point (x₀, y₀). Our class fixes the public
    initial point (0, 0), and Δ plays the role of G₀.
  - The upper bounds measure stationarity with the Moreau envelope of Φ at a parameter of order 1/L, possibly with a
    different constant than our 1/(2L). For an L-weakly convex Φ, envelope gradients at two parameters λ, λ' ≤ 1/(2L)
    of the same order differ by at most a constant factor. So the comparison is up to constants, which is all that is
    claimed.
  - Tracked-FOAM (arXiv:2609.14235) removes the logarithm in the deterministic case.

- **Randomized lower bound for the deterministic oracle.**
  - [arXiv:2610.16991](https://arxiv.org/abs/2610.16991) (v2, Oct 2026) treats finite-sum nonconvex–concave
    problems. Its one-component case (Table 1, row n = 1) already gives a lower bound Ω(L²DΔε⁻³) against
    arbitrary randomized algorithms for the *deterministic* first-order oracle. It uses the same Moreau-envelope
    1/(2L) criterion with a bounded dual domain, under a constant-probability (2/3) success criterion.
  - Its hard instances need a dimension that may grow exponentially; §7 and Thm E.1 list polynomial dimension as
    open.
  - Its intermediate finite-sum regime also reaches an ε⁻⁶ rate. That is a different oracle model: the algorithm
    chooses persistent components, and there is no variance parameter. We do not claim that it implies, or fails to
    imply, our stochastic term.
- **Randomized lower bound for nonconvex–strongly-concave.** [arXiv:2610.00229](https://arxiv.org/abs/2610.00229)
  proves lower bounds against arbitrary algorithms with fresh stochastic gradients, but for nonconvex–strongly-concave
  problems: an unbounded dual domain, a ‖∇Φ‖ criterion, and no reduction to a bounded dual radius. Its own text calls
  the bounded-dual setting a different geometry, so it does not give the nonconvex–concave statement.

**New.** The result adds three things.
- **The stochastic term against arbitrary algorithms.** We prove Ω(L³D²Δσ²ε⁻⁶) for stochastic nonconvex–concave
  minimax against arbitrary randomized algorithms, for every σ ≥ 0. This is the question left open by Wu–Gu–Yang §6
  and by arXiv:2610.01662 §6, whose lower bounds are zero-respecting.
- **Polynomial dimension.** The whole bound, including the deterministic term Ω(L²DΔε⁻³), holds in dimension
  polynomial in LΔ/ε², LD/ε and σ²LD/ε³. arXiv:2610.16991 lists this as open for its randomized deterministic-oracle
  bound.
- **Expected-accuracy criterion.** Failure is stated for E[2L·dist(x̂, prox(x̂))] ≤ ε, at every budget up to the stated
  one.

The deterministic-oracle rate itself, against randomized algorithms, is not new: arXiv:2610.16991 already has it, in
exponential dimension.

Together with SAPD+ and Lin–Jin–Jordan, the result shows that SAPD+ is optimal in its dependence on (L, D, G₀, σ, ε)
against all randomized algorithms, and Lin–Jin–Jordan up to its log factor (Tracked-FOAM removes it). This holds for
dimensions polynomial in the problem parameters.

## How the result meets the task requirements

- **Tight pair.** Only the lower bound is formalized here. The matching upper bounds (SAPD+ Thm 5 in the stochastic
  case; Lin–Jin–Jordan and Tracked-FOAM in the deterministic case) are published results on classes that contain our
  class. So the problem is closed up to universal constants, and up to a log factor for Lin–Jin–Jordan:
  Θ(L²DΔε⁻³ + L³D²Δσ²ε⁻⁶).
- **Template.** The upper bounds are not re-formalized. The lower bound uses `TemplateLowerBound`, with failure at
  every budget b ≤ budget p, for every allowed algorithm, with a seed-independent hard instance.
- **Standard setup.** Smooth, stochastic nonconvex–concave minimax with a bounded dual domain, an unbiased
  bounded-variance oracle, and Moreau-envelope stationarity is the standard setting of Lin–Jin–Jordan, SAPD+ and
  Wu–Gu–Yang.
- **No overlap with repository PRs.** The only related PR, #215, gives an NC–SC (generalized-smooth) upper bound, which
  is a different class and a different kind of result. Work on nonconvex–PL minimax concerns a disjoint class.

## Technical mechanism

We keep Wu–Gu–Yang's primal relay and clipped dual blocks as the base instance. Their value identity and their prox
analysis are reused, re-proved in Lean, and extended. The randomized version needs four new ingredients.

1. **Dead-zone robustification.**
   - Every coordinate enters through the C^{1,1} dead zone ζ_θ, which vanishes on [−θ, θ]. The dual couplings use the
     gadget β(s, t) = ζ(s)t + (s − ζ(s))ζ(t). The concavity defect this creates is repaired by the even ramp term
     −2αθ(ω(y₀) + ω(y_m)) (`NcConcaveConcavity.robB_concave`).
   - The robust f̂ is within η of the base instance on X × Y (`robF_close`). It is jointly L-smooth with explicit
     universal constants (`NcConcaveModel.robF_model`, a quadratic two-sided model, which also gives the gradient).
   - It is *functionally local*: f̂ agrees with f̂∘P_{s+1} near any point whose coordinates at positions ≥ s are below
     θ/2 (`NcConcaveLocality.robF_local`). This yields the exact gradient locality ∇f̂ = P_{s+1}∇f̂(P_{s+1}·) via
     uniqueness of Fréchet derivatives (`NcConcaveChainGrad.DFc_local`).
   - This step is what fails for the original instance: there the gradient at a relay depends on tiny coordinates of
     the next position, so a dense randomized query can identify the next coordinate.
2. **Whole-frontier coin masking.**
   - At dual positions the oracle returns the known prefix gradient plus a Bernoulli(p)/p-weighted remainder.
   - It is exactly unbiased, and its variance is (1/p − 1)·(ℓs)²·‖remainder‖², with ‖remainder‖² ≤ 51α².
   - The bound uses the gradient Lipschitz constant and an explicit bound on the dual partial derivative at a zeroed
     coordinate (`NcConcaveSecret.secret_bound`). Choosing p = c₀/(c₀ + σ²) makes the variance exactly ≤ σ².
3. **Simulation and word counting.**
   - A simulated oracle uses only the positions below a coin-driven revealed level. It agrees with the true oracle as
     long as no query has a large coordinate at an unrevealed position (`NcConcaveExecution.coupling`).
   - The bad event is bounded combinatorially over all injective coordinate words
     (`SmoothConvexFiniteHiding.bounded_prefix_bad_count`, reused).
   - Reaching the last relay requires one coin success per dual position (`maskedBelow_le_coin`). Markov's inequality
     then gives the ε⁻⁶ term.
4. **Approximate-prox transfer of the failure certificate.**
   - The base proximal point fails by Wu–Gu–Yang's part 2/3 analysis. Our pooled version (`NcConcavePooled.pooled`,
     `NcConcavePartThree.part_three`) additionally handles
     - off-word mass,
     - both ball multipliers,
     - arbitrary (even infeasible) outputs.
   - The robust proximal objective is (L/8)-strongly convex, from the model bound. Its minimizers are therefore within
     √(8η/L) of the base proximal point (`NcConcaveProx.approx_prox`).
   - Existence of a robust proximal point follows from lower semicontinuity of Φ̂ (`NcConcaveFailure.value_lsc`). The
     resulting bound, E[2L dist] ≥ (49/64)(c_δ/6)ℓs > ε, is proved in `exists_failure`.

## Scope and limitations

- **The domain scales with ε.** As in Wu–Gu–Yang's construction, the hard instances have X with radius ∝ ε/L in one
  block. The class is a subclass of their F_NCC^pd(L, G₀, D_Y), with X public and fixed, so the lower bound applies to
  their full class. It does not show hardness for a fixed, ε-independent X.
- **Constants.** They are far from optimal (2^-100, 2^-165) and the dimension requirement is a large polynomial. Only
  the rates are claimed.
- **Upper bound not formalized.** The matching upper bound (SAPD+, Lin–Jin–Jordan) is a literature result. The
  deterministic upper bound of Lin–Jin–Jordan is stated with the primal value gap; our class is smaller (primal–dual
  gap), so their bound applies.
- **Oracle model.** The stochastic oracle is the standard unbiased bounded-variance joint oracle with one sample per
  query. Mean-square-smooth (VR) oracles are not covered. For those, arXiv:2610.01662 remains zero-respecting only.
- **Compared with Wu–Gu–Yang.** The rate is identical. The contribution is the algorithm class: arbitrary randomized
  algorithms instead of zero-respecting ones, while keeping the primal–dual structure.
- **Compared with arXiv:2610.16991.** At σ = 0 the rate against randomized algorithms is already known in exponential
  dimension. For that term, our contribution is polynomial dimension and the expectation criterion. The stochastic
  σ²-term against arbitrary algorithms is the main new rate.
