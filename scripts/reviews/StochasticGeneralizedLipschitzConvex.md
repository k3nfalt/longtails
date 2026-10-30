# Novelty assessment: StochasticGeneralizedLipschitzConvex

The [theorem](../../LongTails/Theorems/StochasticGeneralizedLipschitzConvex.lean) proves the following. Take a continuous convex `f` on a separable Hilbert space with a minimizer `x⋆` satisfying `‖x₀−x⋆‖ ≤ R`, and an IID oracle whose mean is a subgradient and which splits as `u+v`, with `E‖u‖² ≤ G₀²` and `‖v‖ ≤ G₁(f(x)−f⋆)` almost surely ([setup](../../LongTails/Setups/StochasticGeneralizedLipschitzConvex.lean)). For this class, the two-phase [`tunedAlgorithm`](../../LongTails/Algorithms/GeneralizedLipschitzConvex.lean) returns a point with `f(x̂)−f⋆ ≤ ε` with probability at least 9/10, after a fixed number of oracle calls.

**Proved complexity.** The tuning needs R, G₀, G₁, and ε. Here R is the initial-distance bound, G₀ the second-moment scale of the bounded part, G₁ the gap-growth coefficient, and ε the target accuracy. Write κ = 1+RG₁ and b = RG₀/ε. The Lean `budget` gives

  N = O( (κ³ + κ²b + b²) · log³(2 + RG₁ + RG₀/ε) ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kovalev, [arXiv:2605.15522v2](https://arxiv.org/abs/2605.15522v2) (v1 15 May, v2 26 May 2026; preprint), Thm 7 / Cor 4: clipped AdamW, Assumption 2 + RG₁ ≥ 1 | Thm 7, eq. (30): `κ³·log(e+FG₁/G₀) + (κ³+κ²b+b²)·log(e+b/κ)`, where F = max over the R-ball of f−f⋆. Eq. (7) only gives log(FG₁/G₀) = O(RG₁), and this is attained by `f(x)=(G₀/G₁)(e^{G₁‖x‖}−1)`. Worst case: `O(κ⁴ + (κ²b+b²)log(e+b/κ))` (Cor 4: Õ(κ⁴+b²)). Markov at ε/10 converts this to 9/10 probability → `O((κ³+κ²b+b²)log³(2+κ+b))` | The worst-case localization cost drops from κ⁴ to κ³·polylog. The bound is better when κ ≫ log³(κ+b) and b ≪ κ²/log³(κ+b). The speedup is about κ/log³ for b ≤ κ and κ²/(b·log³) for κ ≤ b ≤ κ². Example: b = κ gives κ⁴ → κ³log³κ. For b ≳ κ²/log^{1.5} it is worse by about log² | None. The mean need only be a subgradient (same class as Kovalev's nonsmooth setting). The Hilbert-space generality is not the claimed novelty | Output: Kovalev bounds the expected gap of the final AdamW point; this result gives only constant (9/10) probability and no expected-gap bound. Kovalev's bound also depends on the instance through F (or its exponential bound); this one does not | Constant confidence, with no log(1/δ) dependence proved. Three log factors instead of one; constant factor 2⁶⁶. If the initial ball has small F (log(FG₁/G₀) ≲ log³), Kovalev is equal or better |
| Kovalev Thm 3/4 (SGD, AdaGrad-Norm) | `exp(O(RG₁))·b + b²` → N | Exponential → polynomial in RG₁ (Kovalev's Thm 8/9 lower bounds show this is unavoidable for those methods) | None | None | Superseded by Cor 4 already |
| Classical SGD (G₁ = 0, bounded second moment; Nemirovski et al. 2009) | `O(b²)` → `O(b² log³(2+b))` | Worse by log³ | Special case only | None | — |

**Reduction check.** Plugging into Kovalev's tuning cannot remove the κ⁴ term: his first phase costs about κ³ per factor-e decrease of the gap, over log(FG₁/G₀) such factors. I found no reduction (batching, clipping, restarts, or a deterministic normalized method with minibatches) that reaches κ³. As the companion note argues, estimating the gradient to relative accuracy can need about κ² samples per step, which again gives κ⁴. I did not independently verify that argument. The new step is a variance-or-mean scale certificate that localizes to gap O(RG₀) in O(κ³·polylog) calls; I did not check its proof by hand. The tools it uses (median-of-means estimators, robust vector centers, killed-potential concentration) are known proof ancestry. The warm phase follows Kovalev's weighted-averaging scheme with constant weight. Dimension-dependent cutting-plane methods could win in low dimension, but I found no published end-to-end guarantee for them under this noise model, so they are not in the table.

**Search coverage (30 Oct 2026 UTC).** I read the Kovalev v2 PDF (Assumption 2, eqs. (7), (25)–(31), Thms 3–9). I also searched arXiv (including "unbounded gradients" in math.OC, sorted by date) and the web. Checked and found not applicable: Grimmer (2019; second moment linear in the gap), Li–Zhao–Zhu–So [arXiv:2305.14161](https://arxiv.org/abs/2305.14161) (deterministic, growth in the norm of x), Alacaoglu–Malitsky–Wright [arXiv:2504.09951v3](https://arxiv.org/abs/2504.09951) (growth in ‖x‖², a different class), and Dvinskikh et al. [arXiv:2609.06555](https://arxiv.org/abs/2609.06555) (smooth case). The only Semantic Scholar citation of Kovalev is a survey dated one day later, whose content I did not check. The companion note's characterization of Kovalev matches the PDF. Kovalev's paper predates this result (commit 17b4e4f, 30 Oct 2026), and I found no later work covering it. I did not run a build or the audit.

## Conclusion

**Yes: the proved constant-confidence complexity improves polynomially in the gap-growth parameter when it is large.**

The strongest baseline is Kovalev's clipped AdamW (Theorem 7 / Corollary 4) under the identical oracle model. With κ = 1+RG₁ and b = RG₀/ε, the comparison at the 9/10-probability criterion is:

| | worst-case calls |
|---|---|
| Kovalev (via Markov) | κ⁴ + (κ²b + b²)·log |
| This result | (κ³ + κ²b + b²)·log³ |

Kovalev's κ⁴ comes from paying log(initial gap over the R-ball), which can be of order RG₁. The new localization phase removes that dependence. The gain, up to about κ/log³, holds when b ≪ κ²/log³; for b ≳ κ² the new bound is worse by log factors.

The tradeoffs are real. The guarantee holds only with constant probability, while Kovalev bounds the expected gap. It has extra log factors and enormous constants. It loses when the initial ball's gap is already small, and low-dimensional cutting-plane alternatives remain unchecked. The search found no prior or later result matching the κ³ dependence, but the field is five months old and coverage cannot be exhaustive.

The claimable contribution is a first κ³-type constant-confidence oracle complexity for stochastic convex optimization with unbounded, gap-growing subgradients. That is a polynomial gain over the best published bound when b ≪ κ².

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
