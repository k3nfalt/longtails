# Second-order lower bound for Hessian-stable convex minimization: the `(MD)^{2/3}` exponent is optimal for gradient–Hessian oracles

Lean: theorem [`result`](HessianStableNewtonLowerBound.lean) (`NonConvergence LongTails.Setups.HighDimensionalHessianStableSkewMonotone.spec budget`).
- Setup: [`HighDimensionalHessianStableSkewMonotone`](../Setups/HighDimensionalHessianStableSkewMonotone.lean). It reuses the class of [`HessianStableSkewMonotone`](../Setups/HessianStableSkewMonotone.lean) verbatim.
- Matching upper bound: [`HessianStableExpectedNewton`](HessianStableExpectedNewton.lean) (same setup; see its note).
- Hard instance and proofs:
  - [`HsProfile`](../Proofs/HsProfile.lean): the compact bump `(1 − t²)₊^p` and its integrals `g0, g1, g2`; the scaled profile `sp0` and its derivatives; the bump inequalities `|g3| ≤ 4p·g2 + …`, `g2 ≤ 4(p+1)·g1 + …` and `g2 ≤ 4(p+1)(1 − g1) + …`.
  - [`HsChain`](../Proofs/HsChain.lean): the generic chain-plus-override function `fv`, its gradient `Fv` and Hessian `DFv`; derivatives, convexity, existence of a minimizer.
  - [`HsStability`](../Proofs/HsStability.lean): the scalar Grönwall step and the termwise third-derivative bound, giving Hessian stability (`DFv_stable`).
  - [`HsInstance`](../Proofs/HsInstance.lean): the coordinate word `π`, the links `n_j = e_{π(j−1)} − e_{π(j)}`, masking, and the zero-chain identities.
  - [`HsBounds`](../Proofs/HsBounds.lean): the far-field override, the gap and gradient lower bound, the Hessian-norm bound, and the stability constant.
  - [`HsParams`](../Proofs/HsParams.lean): the bump exponent `p = 2(3⌈log₂ K⌉ + 40) + 64` and the budget arithmetic.
  - [`HsExecution`](../Proofs/HsExecution.lean): two-channel execution as an iterate.
  - [`HsLowerBound`](../Proofs/HsLowerBound.lean): scaling, admissibility, and the hiding argument (via [`SharpChainHiding.exists_failure`](../Proofs/SharpChainHiding.lean)).

## Summary

Take convex `f : ℝ^d → ℝ` (the gradient-field case `F = ∇f`, `S = 0`, of the Hessian-stable skew-monotone class) whose Hessian is **Hessian-stable** in the global exponential form

`⟪∇²f(y)v, v⟫ ≤ exp(M‖y − x‖)·⟪∇²f(x)v, v⟫` for all `x, y, v`.

Carmon et al. 2020 (Definition 7) use the local `(r, c)` form. M-quasi-self-concordance (`|D³f(x)[v, v, w]| ≤ M‖w‖·D²f(x)[v, v]`) implies the exponential form, by their Lemma 11; for `C³` functions the two are equivalent.

Assume there is a minimizer `x⋆` with `‖x₀ − x⋆‖ ≤ D`. Let the algorithm query gradients `∇f(x)` (channel 0) and Hessians `∇²f(x)` (channel 1) exactly. We prove that **every randomized algorithm** needs at least

`⌊ (MD / (2^18 · log(2 + MD)))^{2/3} ⌋`

calls on each channel (so at most twice that many calls in total) to output `x̂` with `E‖∇f(x̂)‖ ≤ ε`. More precisely, for every componentwise budget at most this value, some admissible instance makes the expected gradient norm exceed `ε`. This holds whenever

- `MD ≥ 2^60`,
- `ε(MD)² ≤ ΛD` (the Hessian may be as large as the region bound `Λ` allows), and
- `d ≥ 2^21 (MD)^{10/3}`.

The instance and oracle depend on the algorithm and the budget, not on its random seed.

The existing ball-anchored Newton method (repository theorem [`HessianStableSkewNewton`](HessianStableSkewNewton.lean), restated for this setup and criterion in [`HessianStableExpectedNewton`](HessianStableExpectedNewton.lean)) uses `O((1 + (MD)^{2/3})·log³(3 + MD + MΛ(D + 1/M)²/ε))` calls per channel. The pair therefore determines the second-order oracle complexity of Hessian-stable convex minimization in `MD`, up to polylogarithmic factors (see *Tightness*).

## Why this matters, and what was known

- **The class is practical.** Quasi-self-concordance, and hence Hessian stability, holds with explicit `M` for empirical risk minimization:
  - logistic regression and softplus losses `f(x) = (1/n)Σ φ(⟨aᵢ, x⟩) + (μ/2)‖x‖²` with `φ(t) = log(1 + eᵗ)` satisfy `|φ'''| ≤ φ''`, so `M = max‖aᵢ‖` (Bach 2010, "Self-concordant analysis for logistic regression"; Doikov 2023, Example 2.3);
  - soft-max / log-sum-exp objectives `μ log Σ exp((⟨aᵢ, x⟩ − bᵢ)/μ)` are QSC with `M = O(max‖aᵢ‖/μ)` (Doikov 2023, Example 2.2; Carmon et al. 2020, Lemma 14, in `ℓ∞`);
  - matrix scaling/balancing and further examples are in Doikov 2023, §2;
  - smoothed margin objectives for binary classification are QSC, hence Hessian-stable on small balls, and are minimized by ball acceleration (Karmarkar, O'Carroll, Sidford, [Fast, Parallel, Query-Efficient Binary Classification, COLT 2026](https://proceedings.mlr.press/v336/karmarkar26a.html), arXiv:2607.04062; an upper-bound application).


  `MD` is the natural scale-free size of such problems; the rate needs no strong convexity.
- **Upper bounds.**
  - Carmon, Jambulapati, Jiang, Jin, Lee, Sidford, Tian ([Acceleration with a Ball Optimization Oracle, NeurIPS 2020, arXiv:2003.08078](https://arxiv.org/abs/2003.08078)) show that `Õ((MD)^{2/3})` ball-oracle calls suffice. For Hessian-stable functions they implement each call with `Õ(1)` linear-system solves (§3, Theorem 9).
  - Doikov ([Minimizing quasi-self-concordant functions by gradient regularization of Newton method, arXiv:2308.14742](https://arxiv.org/abs/2308.14742); Math. Program. 2025) gives a gradient-regularized Newton method with `Õ(MD)` steps and an accelerated variant with power `2/3`.
  - The repository's ball-anchored Newton gives the bound above for (F, DF) access.
- **Lower bounds.**
  - Carmon et al. 2020, §5, Theorem 24 prove that for convex 1-Lipschitz functions on `B_R(0)`, every `r`-local algorithm (one whose oracle reveals the function on an `r`-ball around each query) needs `Ω((R/r)^{2/3})` queries to reach accuracy `o(R^{2/3}r^{1/3})`. This covers ball-oracle methods.
    - Their hard function is a nonsmooth max of linear pieces, with no Hessian.
    - Its Moreau-smoothed variant is only `C^{1,1}`. Its Hessian is discontinuous and piecewise constant, so it is not Hessian-stable for any finite `M`, and the added ridge does not change this.
    - The theorem therefore says nothing about `(∇f, ∇²f)` oracles on the Hessian-stable class.
  - For Newton-type oracles, the known lower bounds (Arjevani–Shamir–Shiff 2019; Agarwal–Hazan 2018) are for **Lipschitz-Hessian** classes. They are polynomial in `1/ε`, so they do not apply to a class whose upper bound is polylogarithmic in `1/ε`.
  - Adil, Bullins, Jambulapati, Sidford ([arXiv:2410.24158](https://arxiv.org/abs/2410.24158)) prove lower bounds only for zero-respecting `p`-norm proximal and ball-constrained algorithms. Their QSC material is an upper-bound application.
  - Ene, Nguyen, Vladu (NeurIPS 2025, arXiv:2510.22088) use a different access model: rows of the data matrix and linear-system solves, with multiplicative accuracy for structured objectives. Their bounds exploit that structure and do not contradict a lower bound for black-box `(∇f, ∇²f)` access in dimension `d ≳ (MD)^{10/3}`.
  - Doikov 2023 (concluding section) notes that the power `2/3` is known to be optimal only for methods based on the ball-minimization oracle, and that "these optimality results could also hold significant implications for the minimization of Quasi-Self-Concordant functions".
  - **Matrix-vector lower bounds for specific bilinear problems.** Kornowski and Shamir ([The Oracle Complexity of Simplex-based Matrix Games, COLT 2025](https://proceedings.mlr.press/v291/kornowski25a.html), [arXiv:2412.06990 v4](https://arxiv.org/abs/2412.06990v4), Feb 2026) prove that every **deterministic** algorithm using two-sided matrix-vector products with the payoff matrix `A` needs `Ω̃(ε^{-2/3})` queries for `ℓ_p`/simplex matrix games. The same holds for finding a linear separator with margin `γ`, with `Ω̃(γ^{-2/3})` queries. Karmarkar, O'Carroll and Sidford ([Solving Matrix Games with Near-Optimal Matvec Complexity, arXiv:2601.02347](https://arxiv.org/abs/2601.02347)) give matching `Õ(ε^{-2/3})`-matvec algorithms; so does the COLT 2026 classification paper above, for separators. The same `2/3` exponent therefore already appears as an optimal matvec complexity for these bilinear tasks. Neither result implies the other:
    - **Oracle.** A matvec reveals one vector `Aw` or `pᵀA` per query. Our oracle returns the full gradient and the full `d × d` Hessian of a general nonlinear objective at the query point, which is far more information per call. Their lower bound does not bound `(∇f, ∇²f)` queries.
    - **Problem class.** They study one fixed bilinear problem family with bounded payoff entries. We study the general Hessian-stable (and QSC) convex class with scale `MD`. Our hard functions are not matrix games, so our theorem does not imply theirs either.
    - **Algorithms.** Their bound is for deterministic algorithms; their §8 states that extending it to randomized algorithms is open. Ours holds for every randomized algorithm.
  - To our knowledge, there is no lower bound for `(∇f, ∇²f)` access on the Hessian-stable or QSC class.
- **New result (to our knowledge, the first lower bound for `(∇f, ∇²f)` oracles on the Hessian-stable/QSC class, and it holds against randomized algorithms).** The exponent `2/3` cannot be improved by **any** randomized algorithm with exact gradient and Hessian access, even with unlimited computation per step. In particular, no second-order method beats the ball-acceleration rate by more than polylogarithmic factors.

## The hard instance and the mechanism

Work in normalized coordinates `u = (x − x₀)/β`. Let `K = k + 1` be the chain length and `π` an injective word of `K` coordinates. Set:

- **Links.**
  - `ℓ₀(u) = 1 − u_{π(0)}`;
  - `ℓ_j(u) = u_{π(j−1)} − u_{π(j)}`.
- **Chain.** `C(u) = Σ_j ψ(ℓ_j(u))`. The convex profile `ψ` is exactly flat (`ψ ≡ 0`) for `t ≤ 1/(4K)` and has slope `1` for `t ≥ 1/(2K)`. Its second derivative is a compact bump `(1 − s²)₊^p` of width `1/(8K)`.
- **Override.** `R(u) = 2‖u‖² − (2K + 1/8)`, and `ψ₂` is the same kind of profile, centred at `0` with width `1/8`.
- **Function.** `f(u) = (λ/2)‖u‖² + C(u) + ψ₂(R(u) − C(u))`, with `λ = 1/(8K)`.

The construction is a smoothed total-variation chain plus a ridge and a radial override. It is not a logistic regression. It is the analogue, for the Hessian-stable class, of the Nesterov / Carmon et al. chains.

1. **Termwise Hessian stability with only a logarithmic loss.**
   - The bump satisfies `|g₃| ≤ 4p·g₂ + 4p(p+1)2^{−p}`. With `p ≍ log K`, the additive leftover is negligible against the ridge `λ`.
   - Each link therefore satisfies `|ψ'''(ℓ)| ≤ O(pK)·ψ''(ℓ) + tiny`. Summed with the Cauchy–Schwarz bound for the override, this gives `|D³f[v,v,w]| ≤ M̂‖w‖·D²f[v,v]` with `M̂ ≤ 1500(p+1)K`.
   - A scalar Grönwall argument along segments turns this into Hessian stability with constant `M̂` (generic lemma `DFv_stable`, instantiated as `FF_stable`).
   - The bound is **termwise**: it does not depend on the chain depth, unlike iterated smooth-max constructions.
   - The intermediate statement is exactly `M̂`-quasi-self-concordance. The lower bound therefore also holds for the smaller QSC class. Lean records the exp-form statement required by the setup.
2. **Exact zero-chain with flat zones.** `ψ` vanishes identically below `1/(4K)`. Hence, if every undiscovered coordinate `π(j)`, `j ≥ t`, has `|u_{π(j)}| ≤ 1/(16K)`, then `f`, `∇f` and `∇²f` coincide with those of the masked instance that only uses `π(0..t)` (`answers_masked`).
   - For `‖u‖ > 2√(K+1)`, the override saturates and the reply is radial, `(λ + 4)u` (`answers_far`). It reveals nothing.
   - Each query therefore discovers at most one new chain coordinate. Coordinate-word hiding (`SharpChainHiding.exists_failure`, dimension `d ≳ K⁵`) gives the randomized lower bound.
3. **Gap and gradient.** If the last chain coordinate is still undiscovered, `C(u) ≥ 1/2 − u_{π(K−1)}`, by telescoping the slope-one lower bound. The test point `x̄_{π(j)} = 1 − (j + 1)/(4K)` gives `f⋆ ≤ 1/16`, and `‖x⋆‖ ≤ √K`. Together these yield `‖∇f(u)‖ ≥ 1/(8√(K+1))` at every unsuccessful output (`grad_lower`).
4. **Scaling.** `x = x₀ + βu` with `β = D/√K` keeps `‖x₀ − x⋆‖ ≤ D`. The stability constant becomes `M̂/β`, and `M̂√K ≤ MD` when `K ≍ (MD/log MD)^{2/3}`. Multiplying by `α = 16ε√(K+1)` makes bad outputs have `‖∇f‖ ≥ 2ε`. Since at least 3/4 of the hidden words force a bad output, `E‖∇f(x̂)‖ > ε`.
   - The `log` in the budget comes from `p ≍ log K` in the bump exponent.

## Tightness

At budget `B = (MD/log MD)^{2/3}`, the ratio between the upper bound `O((MD)^{2/3}·log³(3 + MD + MΛ(D + 1/M)²/ε))` and the lower bound is

`polylog(MD) · log³(MΛD²/ε)`.

- **Benign curvature.** When `log(MΛD²/ε) = O(log MD)`, for example at the threshold `ΛD/ε ≍ (MD)²`, the ratio is `polylog(MD)`. The pair then determines the complexity up to polylogarithmic factors in `MD`.
- **General case.** The pair is tight up to `polylog(MD)·log³(MΛD²/ε)`.
  - The upper bound carries the extra `log³(MΛD²/ε)`, including `log³(1/ε)`. We do not claim a matching lower bound for this factor.
  - The factor can be large. For exp-type losses the curvature bound can be `Λ = e^{Θ(MD)}`; the `log³` factor alone is then of order `(MD)³`, and the pair is **not** tight there. The upper-bound note of [`HessianStableSkewNewton`](HessianStableSkewNewton.lean) estimates this regime by counting a single logarithm.
  - Whether these logarithmic factors are necessary for second-order methods on this class remains open.
- **Dimension.** The lower bound uses `d ≥ 2^21 (MD)^{10/3}`, as is typical for randomized hiding constructions. The upper bound is dimension-free.

## Assumptions and regime

The class, oracle and accuracy are those of the existing setup [`HessianStableSkewMonotone`](../Setups/HessianStableSkewMonotone.lean):

- `DF = S + H` with `S` skew and `H` symmetric PSD and Hessian-stable;
- a zero `x⋆` with `‖x₀ − x⋆‖ ≤ D`;
- `‖DF‖ ≤ Λ` on `B(x⋆, 3D + 1/(4M))`.

The hard instances are gradient fields (`S = 0`), so the bound holds already for convex minimization.

The new setup changes only four things:

1. `E = ℝ^d` with `d` public.
2. Success is measured in expectation, `E‖F(x̂)‖ ≤ ε` (with integrability), instead of almost surely. This makes the lower bound stronger.
3. `valid` adds only the regime conditions listed above. They hide no instance information.
4. All parameters, including `Λ` and `d`, are public. This only strengthens the lower bound; the upper-bound algorithm ignores `Λ`.

The regime is nonempty: take `M = 2^60`, `D = 1`, `ε = 1`, `Λ = 2^120`, `d = 2^221`.

The matching upper bound holds for every valid parameter of this setup. Its validity conditions are a subset of the new ones, and its deterministic output gives the expectation criterion.

## Scope compliance

- **Almost tight upper and lower bounds.** The upper bound already existed in the repository; it is restated for the same setup and criterion in [`HessianStableExpectedNewton`](HessianStableExpectedNewton.lean). The new lower bound matches it in `MD` up to polylog factors. Both use `OracleTemplate` (`Convergence` / `NonConvergence`).
- **Practical setup.** Hessian-stable or QSC convex minimization with gradient and Hessian access is the standard model for Newton-type methods on logistic, softmax and `ℓ_p` problems.
- **Significant contribution.** To our knowledge, this is the first lower bound for `(∇f, ∇²f)` oracles on this class, and it holds against randomized algorithms. It shows that the `2/3` exponent of ball acceleration is optimal among all randomized second-order methods.
- **No overlap.** We checked open PRs and the current local `main` for overlapping results; none concern this class.

## Literature coverage

The searches covered:
- NeurIPS 2024–2026, ICML 2024–2026 and ICLR 2025–2026;
- COLT 2025–2026, including the matvec lower and upper bounds for matrix games and linear separability (Kornowski–Shamir arXiv:2412.06990 v4; Karmarkar–O'Carroll–Sidford arXiv:2601.02347 and arXiv:2607.04062);
- arXiv 2024–2026, including the Carmon–Jambulapati–Jin–Sidford line (arXiv:2205.15371, 2311.10886) and the papers above. A final re-search on 2026-11-26 found no new lower bound for this class and oracle.

We found no lower bound for this class and oracle. ICLR 2027 submissions on OpenReview were not accessible.

## Limitations

- The lower bound needs `MD ≥ 2^60` and large dimension. The constants are not optimized.
- The `log³(1/ε)` gap discussed above remains open.
- The hard instance is synthetic; logistic-regression instances may be easier.
- The oracle is exact. Noisy or inexact Hessians are not covered.
