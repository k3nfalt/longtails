# A self-contained upper bound on the sublevel α-Polyak–Łojasiewicz class with a bounded-variance gradient oracle

The [Lean theorem](SublevelPLRobustBatchedGd.lean) (`OracleTemplate.SublevelRobustGradient.SublevelPLRobustBatchedGd.result`) proves an expected-accuracy oracle-complexity bound for stochastic first-order minimization of globally smooth functions that satisfy an α-Polyak–Łojasiewicz (α-PŁ) inequality only on the initial sublevel set, with α ∈ [1,2). This is the class on which Masiha, Kiyavash and Thiran ([arXiv:2606.28278v3](https://arxiv.org/abs/2606.28278), Theorem 4.1) proved the lower bound Ω(Lτ^{2/α}ε^{−(2−α)/α} + Lσ²τ^{4/α}ε^{−(4−α)/α}) and listed, as the first of their open questions, a "fully self-contained upper bound" that proves the trajectory containment "directly, without exact function-value queries or a monotone accept/reject safeguard" (their Remark 4.2 and Section 5). The theorem gives such a bound: it matches the lower bound up to a logarithmic factor on the deterministic term, a squared logarithmic factor on the noise term (see the budget below), and α-dependent constants, on the literal class, with a gradient-only method, with no function values, no accept/reject rule, no margin around the sublevel set, and no assumption that the iterates stay anywhere.

## Setup

The [specification](../Setups/SublevelPLBoundedVariance.lean) (`LongTails.Setups.SublevelPLBoundedVariance.spec`) is Masiha–Kiyavash–Thiran's bounded-variance sublevel-α-PŁ model (their Sections 2.2–2.4):

- `E` is a finite-dimensional real inner-product space; `f : E → ℝ` is differentiable with an `L`-Lipschitz gradient on all of `E` and bounded below; `f⋆ := inf f` (the infimum need not be attained, exactly as in the paper, where `f⋆ = inf f`).
- α-PŁ on the initial sublevel set only: for every `x` with `f(x) ≤ f(x₀)`, `f(x) − f⋆ ≤ τ‖∇f(x)‖^α`, with `τ > 0` and `1 ≤ α < 2`. Nothing is assumed outside `{f ≤ f(x₀)}` except global smoothness. (Their Theorem 2.1 shows that a global α-PŁ inequality with global smoothness forces `f` to be constant when α < 2, which is why the class is localized.)
- `f(x₀) − f⋆ ≤ Δ`.
- The oracle returns `g(x, ξ)` for an IID sample `ξ ~ p`, jointly measurable, unbiased (`∫ g(x,ξ) dp = ∇f(x)`) with variance `∫‖g(x,ξ) − ∇f(x)‖² dp ≤ σ²`. There is no function-value oracle. Each sample costs one oracle call.
- Public information: `E, L, τ, α, σ, Δ, ε, x₀` (the lower bound is proved against methods that know the class parameters, their Definition 2.8).
- Accuracy: the output `x̂` must satisfy `E[f(x̂) − f⋆] ≤ ε` (their Definition 2.8 minimax criterion), stated as an integral against the execution law together with integrability.

No `allowedAlgorithm` restriction is imposed. The scalar parameters are only required to satisfy `L, τ, ε > 0`, `σ, Δ ≥ 0`, `1 ≤ α < 2`; in particular the bound holds for every `ε > 0`, while the lower bound is stated for `ε ≲ min{Δ, L^{α/(2−α)}τ^{2/(2−α)}}`.

## Algorithm

The [algorithm](../Algorithms/SublevelRobustGradient.lean) (`OracleTemplate.SublevelRobustGradient.method`) is mini-batch gradient descent with a constant step `1/L`, a constant number of steps `K`, and a robust mean of the mini-batch at every step:

- At the current point `x`, draw `m·b` fresh samples, split them into `m` sub-batches of size `b`, and form the sub-batch means `V₁, …, V_m`.
- Take as gradient estimate `ĝ` the first `V_i` such that more than `m/2` of the `V_l` lie within `B/3` of `V_i` (the repository's `pilotCenter`, the Nemirovski–Yudin / Hsu–Sabato majority-selection aggregate); if no index qualifies, take `V₁`.
- Update `x ← x − ĝ/L`. After `K` steps return the current point.

With `A := 32α/(7(2−α)) · Lτ^{2/α}(ε/4)^{−(2−α)/α}`, the tuning is `K = ⌈A⌉₊ + 1`, `m = 6 + ⌈log₂(32(A+2)Δ/ε)⌉₊`, `b = 1 + ⌈(1152 + 16m)·(19α/(2−α)·τ^{2/α}σ²ε^{−2/α} + 2σ²/(Lε))⌉₊`, and `B = 2√(Lε/(8K))`. The algorithm uses only `L, τ, α, σ, Δ, ε, x₀`: no function values, no restarts, no validation, no clipping.

## Guarantee and oracle cost

`result` proves `E[f(x_K) − f⋆] ≤ ε` after exactly

    budget = K · m · b

oracle calls, with `K, m, b` written out in the Lean budget line (the expression `A` appears once in `K` and once inside each of the two logarithms). Since `m = O(log(KΔ/ε))` and `b = O((1 + m)·((α/(2−α))·τ^{2/α}σ²ε^{−2/α} + σ²/(Lε)))`, the total is

    O( K · log(KΔ/ε) · [ 1 + log(KΔ/ε) · ((α/(2−α)) · σ²τ^{2/α}ε^{−2/α} + σ²/(Lε)) ] ),   K ≤ (32α/(7(2−α))) · Lτ^{2/α}(ε/4)^{−(2−α)/α} + 2,
    = Õ( Lτ^{2/α} ε^{−(2−α)/α} + Lσ²τ^{4/α} ε^{−(4−α)/α} )   whenever Lτ^{2/α}ε^{−(2−α)/α} ≥ 1,

the two terms of the lower bound, up to the factor `log(KΔ/ε)` on the first term and `log²(KΔ/ε)` on the second, and up to constants that depend on α through `α/(2−α)` (the lower bound's constant also depends on α; nothing is claimed uniformly as α → 2). The condition `Lτ^{2/α}ε^{−(2−α)/α} ≥ 1` holds throughout the lower bound's regime `ε ≲ L^{α/(2−α)}τ^{2/(2−α)}`; it is what makes the lower-order terms `log²(KΔ/ε)·(α/(2−α))σ²τ^{2/α}ε^{−2/α}` and `log²(KΔ/ε)·σ²/(Lε)` of the budget no larger than the displayed noise term. For larger ε these two terms are additional. Every sample is counted, including all `m` sub-batches of every step.

## Mechanism

The proof is pathwise on a good event and needs no stopped process, martingale concentration, or containment hypothesis.

1. With step `1/L` the one-step smoothness inequality is exact in the error `e = ĝ − ∇f(x)`: `f(x − ĝ/L) ≤ f(x) − (‖∇f(x)‖² − ‖e‖²)/(2L)` ([`pathwise_descent`](../Proofs/SublevelPLDeterministic.lean)). Only global smoothness is used.
2. Let `ε' = ε/4`, `ν = Lε'/(2K)`, and the good event `G = {‖e_j‖² ≤ ν for all j < K}`. On `G` exactly one of two things happens ([`good_trajectory`](../Proofs/SublevelPLTrajectory.lean)):
   - every gap `f(x_j) − f⋆`, `j ≤ K`, is at least `2ε'`. Then `‖∇f(x_j)‖² ≥ (2ε'/τ)^{2/α} ≥ 8ν ≥ 8‖e_j‖²`, so each step decreases `f` and the iterates stay in the exact initial sublevel set, where α-PŁ applies; the recursion `gap_{j+1} ≤ gap_j − (7/16L)τ^{−2/α} gap_j^{2/α}` and the potential `gap^{1−2/α}` (which grows linearly, `recursion_sum`) force `gap_K < 2ε'` for the chosen `K`, a contradiction;
   - some `j₀ ≤ K` has `gap_{j₀} < 2ε'`. From then on only smoothness is used: `f(x_K) ≤ f(x_{j₀}) + Σ_{j ≥ j₀}‖e_j‖²/(2L) ≤ f⋆ + 2ε' + Kν/(2L) = f⋆ + (9/4)ε'`. The iterates may leave the sublevel set here; it does not matter.
   This two-phase argument is what makes the literal class (initial point on the boundary of the sublevel set, no margin) harmless.
3. Probability of the good event ([`failure_probability_le`](../Proofs/SublevelPLProcess.lean)): conditionally on the past the `m·b` samples of a step are fresh; each sub-batch mean is within `B/6 = √ν/3` of `∇f(x_j)` except with probability `9σ²/(bν) ≤ 1/16` (Chebyshev, any bounded-variance law), and the majority selection fails only if more than half the sub-batches fail, probability at most `2^{−m}` ([`robustCenter_failure_probability`](../Proofs/SublevelPLSampling.lean), via the repository's `majority_failure_probability`). A union bound gives `P(Gᶜ) ≤ K2^{−m}`, and `m` is chosen so that `Δ·K·2^{−m} ≤ ε/32`.
4. Expectation ([`expected_gap`](../Proofs/SublevelPLConvergence.lean)): pathwise, `f(x_K) − f⋆ ≤ Δ + Σ_{j<K}‖e_j‖²/(2L)` for every sample path (smoothness only), and the aggregate is always one of the sub-batch means, so `E‖e_j‖² ≤ mσ²/b` (the crude bound; `b` carries the factor `m` for this reason). Hence `E[f(x_K) − f⋆] ≤ (9/4)ε' + Δ P(Gᶜ) + K·mσ²/(2Lb) ≤ ε`.

Why the robust aggregate is needed: with plain mini-batch means, only Markov's inequality is available under bounded variance, and the expectation criterion forces the failure probability to be of order `ε/Δ`, i.e. a mini-batch inflated by `Δ/ε` (a two-point noise law plus a smooth "trap" basin outside the sublevel set shows this is not an artifact of the analysis for plain means). The majority aggregate turns the per-step failure into `2^{−m}` at the price of one logarithm. The same proof gives, for any `δ ∈ (0,1)`, `f(x_K) − f⋆ ≤ (9/4)ε'` with probability at least `1 − δ` when `m = ⌈log₂(K/δ)⌉` (tunable confidence at a `log(1/δ)` price); only the expectation form is formalized.

## Comparison with prior work

- **Masiha, Kiyavash, Thiran, [arXiv:2606.28278v3](https://arxiv.org/abs/2606.28278) (Aug 2026, preprint).** Theorem 4.1 (lower bound) is matched up to logarithms and α-constants. Their Table 1 lists as the only upper bound on this row "SGD under trajectory containment; Fatkhullin et al. (2022)", and their Remark 4.2 and Section 5 ask for a self-contained bound. This theorem answers that question in the expected-error criterion of their Definition 2.8.
- **Fatkhullin, Etesami, He, Kiyavash, NeurIPS 2022, [arXiv:2210.01748](https://arxiv.org/abs/2210.01748).** SGD under a global KŁ/α-PŁ inequality (their Assumptions 1–3 hold on all of ℝ^d); the rate `O(Lτ^{2/α}ε^{−(2−α)/α} + Lσ²τ^{4/α}ε^{−(4−α)/α})` is the same order. On the globally smooth class with α < 2 the global inequality is vacuous (Masiha et al. Theorem 2.1), and localizing it requires the containment that Masiha et al. flag.
- **Sadiev, Danilova, Gorbunov, Horváth, Gidel, Dvurechensky, Gasnikov, Richtárik, ICML 2023, [arXiv:2302.00999v2](https://arxiv.org/abs/2302.00999), Theorem 3.1 case 2.** Clipped SGD with PŁ (α = 2 only) and smoothness assumed on a margin set `Q ⊇ {f ≤ f⋆ + 2Δ}` enlarged by a ball of radius `√Δ/(20√L)`, under bounded central moments of order in (1,2] (more general tails than bounded variance), with high-probability guarantees. Relative to it, the present theorem (i) covers every α ∈ [1,2), which is the main new content, (ii) uses the exact initial sublevel set with no margin and no neighbourhood, a modest tightening at α = 2, (iii) assumes finite variance, so it does not cover their heavier tails, and (iv) needs no clipping. Expectation versus high probability is not a substantive difference between the two.
- **Scaman, Malherbe, Dos Santos, ICML 2022** ([PMLR 162](https://proceedings.mlr.press/v162/scaman22a.html)): local Łojasiewicz conditions with sub-Gaussian noise and δ-dependent control radii. **Sarkar, Chakrabartty, Aggarwal, [arXiv:2606.26316](https://arxiv.org/abs/2606.26316), Corollary 4**: a sublevel-set localization of PL-SGD (α = 2) under an almost-sure ABC envelope on the stochastic gradients. **Louzi, [arXiv:2412.06070](https://arxiv.org/abs/2412.06070)**; **Dereich–Kassing** and related almost-sure or positive-probability containment results: no complexity matching the lower bound under bounded variance.
- The aggregation device is classical (Nemirovski–Yudin 1983; Hsu–Sabato 2016; Minsker 2015) and is already in this repository (`pilotCenter`); the claim is the resolution of the stated open question through the two-phase pathwise argument, not the aggregate itself.

## Limitations

- The noise term carries `log²(KΔ/ε)` and the deterministic term `log(KΔ/ε)` relative to the lower bound; the second logarithm comes from the crude second-moment bound `E‖ĝ − ∇f‖² ≤ mσ²/b` and could be removed by a finer bound on the aggregate.
- Constants depend on α through `α/(2−α)`; the endpoint α = 2 (classical PŁ, where the lower bound is the separate Theorem 4.3 of Masiha et al.) is not covered by this theorem. The same two-phase argument covers α = 2 with a contraction recursion at the price of a `log(Δ/ε)` factor, but that is not formalized here.
- Even when `σ = 0` the budget keeps the factor `m ≥ 6` and the logarithm, so the deterministic specialization is gradient descent at a logarithmic overhead.
- The method knows `L, τ, α, σ, Δ, ε`; no adaptivity is claimed.
- Global `L`-smoothness is assumed on all of `E` (as in Masiha et al.); Sadiev et al. only need it on their margin set.
