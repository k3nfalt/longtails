# Novelty assessment: FiniteLogisticTwoTapGradientDescent

**Guarantee.** Take Tyurin's two-sample, two-tap convolutional logistic problem: the samples are `1_d` (label +1) and `1_d + μe_i` (label −1), with the index `i` hidden. Run full-batch logistic GD with step `η = 2⁻⁴⁰/√d`, starting from a uniformly random direction at radius `r`, and freeze at the first strict separator. With probability ≥ 1−ρ, the returned iterate classifies both samples correctly. Here `d ≥ 3`, `0 < μ ≤ 1/10`, `0 < ρ < 1` and `0 < r ≤ √(μρ)·ρ/(2²⁴d²)`. Links: [theorem](../../LongTails/Theorems/FiniteLogisticTwoTapGradientDescent.lean), [setup](../../LongTails/Setups/FiniteLogisticTwoTap.lean), [algorithm](../../LongTails/Algorithms/FiniteLogisticTwoTap.lean).

**Complexity.** The proved budget is `2⌈2⁵³(√d/μ)·log(1/r)⌉` sample queries. Each query returns one sample's signed score and its gradient, and both queries of every pair are charged. In O-form this is

  N = O( (√d/μ) · log(1/r) ),  valid only for r ≤ μ^{1/2}ρ^{3/2}/(2²⁴d²).

The radius cap forces `log(1/r) ≥ 2 log d + ½ log(1/μ) + (3/2) log(1/ρ) + 24 log 2`. Here `d` is the dimension, `μ` the size of the defect, `ρ` the failure probability, and `r` the initialization radius.

`allowedAlgorithm` is appropriate here because the claim is about GD. It enforces a fixed step `η > 0`, the random-sphere start, the exact averaged logistic-gradient step, freezing at the first separator, and output of the current point. Compliance is proved.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Elementary problem-class baseline (this review; no source). The algorithm knows `d, μ`. One query pair at `(c,v)=((1,0),0)` reveals `1_d` and `−(1_d+μe_i)`, hence `i`. Output `c=(1,0)`, `v=a·1_d−e_i` with `1/d<a<(1+μ)/(d+μ)`. | 2 → O((√d/μ)log(1/r)) | Worse: by a factor of order (√d/μ)log(1/r) | None (same instances) | None: both return a strict separator; the baseline is deterministic | GD is restricted by design; the question is about GD dynamics, not about solving this instance class |
| [Tyurin, ICML 2026 (PMLR 306)](https://proceedings.mlr.press/v306/tyurin26a.html), [arXiv v2, 21 May 2026](https://arxiv.org/abs/2512.11587v2), Thm 5.1: noisy, violation-priority two-sample quadratic perceptron (QPA) | O((√d/μ)·log(√d·A/μ)·A) with A = 2²⁷·(two logarithms in d, μ, ρ and ‖θ₀‖/⟨θ₀,v_{μ,+}⟩), i.e. Õ(√d/μ) with three logs → O((√d/μ)log(1/r)) | Not comparable as an algorithm-to-algorithm gain. The leading √d/μ is the same; the new bound has one logarithm instead of about three, but the algorithms differ | The analysed algorithm changes from noisy perceptron surrogate to actual logistic GD with sigmoid weights | Noise tuned to the initial projection ⟨θ₀,v_{μ,+}⟩ → no noise and no initialization-dependent tuning | Requires a tiny radius, linked to ρ. The universal constant is 2⁵³ |
| Tyurin, Thm 2.1: GD's normalized iterates equal QPA's as ‖w₀‖→∞ | No GD iteration bound (limit statement only; Thm 5.1 is a different, noisy non-batch variant) → O((√d/μ)log(1/r)) | Not comparable: no prior end-to-end GD rate | Large-norm limit → explicit small finite radius. Moderate or unit radius is still not covered | None | Covers the opposite regime (small initialization), not "any finite norm" |
| [Kumar–Haupt, TMLR 2024 (arXiv 2402.09226)](https://arxiv.org/abs/2402.09226); [JMLR 26 (2025)](https://jmlr.org/papers/volume26/25-1089/25-1089.pdf): gradient flow on 2-homogeneous nets at small initialization | Early directional convergence and post-escape tracking; no separation hitting time → explicit bound | Not comparable: no rate for this task | Gradient flow → discrete GD, with an explicit first crossing | None | Covers only this data family, not general homogeneous models |

**Reduction check.** Tyurin's large-norm reduction does not transfer: at small norm the sigmoid weights are ≈ ½ rather than 0/1, so GD is not a perceptron. The small-initialization early-alignment theory (Kumar–Haupt) is proof ancestry. It supplies the picture of linear growth along the top modes near the origin. The new work is the discrete analysis:
- simultaneous Gaussian lower bounds on two initial projections;
- an invariant set for three coupled coordinates;
- a hitting time of O(1/(ημ)) after the warm-up phase;
- an overshoot estimate showing the second score is still positive at the first crossing.

The O(√d/μ) rate is Tyurin's; what is new is that GD itself attains it in this regime. No lower bound for logistic GD, at any radius, is proved here or in Tyurin's paper. The Ω(d/μ) of Tyurin's Thm 5.2 is for the batch perceptron on the linear model, so the "acceleration" is relative to that surrogate only.

**Search coverage (2026-11-25).** I read Tyurin's arXiv v2 HTML, verified the Conclusion text and the Thm 5.1/5.2 statements, and confirmed the PMLR listing. Searches found no later work on small-norm or finite-norm GD for this construction. Tyurin's Conclusion explicitly leaves "the small-norm regime … for future work." I checked the Kumar–Haupt papers only at abstract level; I did not verify their exact theorem numbers.

The result was added in commit f2d9aff8 (2026-11-25). The companion note says the result keeps √d/μ "for inverse-polynomial radii", which matches the formal statement. It also correctly records that fixed unit radius is left open, even though the originating request asked for ‖w₀‖ that "does not go to infinity". I did not run a build or an axiom audit.

## Conclusion

**No optimization advantage: this is a GD-specific analysis that proves, in a regime Tyurin left open, that actual logistic GD reaches his √d/μ rate.**

The strongest relevant baselines differ in kind. Tyurin's Theorem 5.1 bounds a noisy perceptron surrogate, not GD; his Theorem 2.1 links GD to the perceptron only in the infinite-norm limit. Here the actual GD trajectory is bounded at small initialization:

| | Algorithm | Initialization | Queries |
|---|---|---|---|
| Tyurin Thm 5.1 | noisy QPA, noise tuned to θ₀ | fixed, any norm | Õ(√d/μ), about three logs |
| This result | logistic GD | random, r ≤ μ^{1/2}ρ^{3/2}/(2²⁴d²) | O((√d/μ)·log(1/r)) |

No complexity improvement for the problem exists. One gradient query pair reveals the hidden index, so a separator costs 2 queries. Nor is GD shown to need √d/μ, or the linear-model GD to need d/μ; the only lower bound is for the perceptron.

The literature check supports priority for the small-norm GD statement, but it covers one hand-built two-point dataset and excludes moderate radii. What can be claimed is a first rigorous small-initialization, discrete-time proof of Tyurin's implicit-acceleration rate for actual logistic GD on his example. That is a modest, method-specific extension of a known rate.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
