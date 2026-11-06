# Novelty assessment: StochasticConstrainedQuasarHighProbability

**What the theorem proves.** The [theorem](../../LongTails/Theorems/StochasticConstrainedQuasarHighProbability.lean) concerns a finite-dimensional Hilbert space. The objective must be γ-quasar-convex with respect to a constrained minimizer `xstar` of a compact convex set X with diameter at most D, and its gradient must be L-Lipschitz on X. The oracle has two channels: IID unbiased stochastic gradients with variance at most σ², and exact projection onto X. Under these assumptions, the [algorithm](../../LongTails/Algorithms/StochasticQuasarProgram.lean) returns `output ∈ X` with `f(output) − f(xstar) ≤ ε` with probability at least 1−δ. It uses at most B calls on each channel, where B is the budget defined in the theorem file. The [setup](../../LongTails/Setups/StochasticConstrainedQuasar.lean) states the assumptions above. The algorithm uses no function values and does not use `xstar`.

**Complexity.** The parameters are: L is the smoothness constant on X, D is the diameter of X, γ ∈ (0,1] is the quasar parameter, σ² is the variance bound, ε is the target accuracy and δ is the failure probability. The public budget is `B = ⌈2⁹⁶(2+⌈8 log(8/δ)⌉)(1+clog₂⌈2+LD²/(γ²ε)⌉)²(1+√(LD²/ε)/γ+σ²D²/(γ²ε²))⌉`. In O-form, the total number of gradient-plus-projection calls is

  N = O( log(8/δ) · [1 + log(2 + LD²/(γ²ε))]² · [1 + √(LD²/ε)/γ + σ²D²/(γ²ε²)] ).

There is no separate initialization term: the feasible starting point x₀ enters only through D.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Martínez-Rubio, [AISTATS 2026](https://proceedings.mlr.press/v300/martinez-rubio26a.html), [arXiv 2510.01943v3](https://arxiv.org/abs/2510.01943v3) (Jul 14, 2026), Thm 5. Special case: σ=0. | Õ(√(LD²/ε)/γ) value-and-gradient calls, deterministic. The binary search and the PGD proximal solves add log(LD²/ε)-type factors. → N at σ=0: O(log(1/δ) log²(2+LD²/(γ²ε)) (1+√(LD²/ε)/γ)) | None: same order up to logs. This result adds a log(1/δ) factor. | Exact deterministic gradients and values → unbiased finite-variance stochastic gradients | Value oracle → gradients plus projections only | The guarantee is now randomized, holding with probability 1−δ instead of deterministically, and it pays an extra log(1/δ). |
| Fu–Xu–Wilson, [ICML 2023](https://proceedings.mlr.press/v202/fu23e.html), [2305.04736v2](https://arxiv.org/abs/2305.04736v2), Cor. 3.3 (QASGD). Special case: unconstrained. | Expected gap: O((R√(L/ε) + σ²R²/(γ²ε²)) log⁺(LR²/(γε))). For confidence δ, Markov's inequality requires accuracy εδ, giving O((δ^{-1/2}R√(L/ε) + δ^{-2}σ²R²/(γ²ε²))·log) → N with R ≤ D | Confidence dependence improves from δ^{-2} to log(1/δ) on the noise term when δ < 1/polylog. The two bounds have the same powers of ε and σ. | Unconstrained ℝᵈ with global minimizer and bounded second moment E‖∇fᵢ‖² ≤ σ² → constrained X, boundary minimizers allowed, bounded variance only | Expected gap → probability bound. Component function values (Bisearch) → gradients only | Requires compact X with known D. FXW's R ≤ D, so this result can lose when R ≪ D. |
| Convex overlap (γ=1). Reduction: regularize f by (ε/2D²)‖x−x₀‖², then apply proxBoost (Davis–Drusvyatskiy–Xiao–Zhang, [JMLR 22(49) 2021](https://www.jmlr.org/papers/v22/20-821.html), Cor. 5.3 and §6 composite extension) | Õ(log(1/δ)(√(LD²/ε) + σ²D²/ε²)) with polylog(LD²/ε) factors. I read the composite accelerated statement only in summary. → N at γ=1 | None: same order up to logs. | γ=1 (convex) → γ<1 (nonconvex quasar). Regularization destroys quasar convexity (Martínez-Rubio §4, Example 1). | None | On the γ=1 overlap there is no gain, and this result may carry more logarithmic factors. Nguyen–Ene–Nguyen ([2304.01119v2](https://arxiv.org/abs/2304.01119), Thm 4.1) give O(log(1/δ)(R√(L/ε)+R²σ²/ε²)) but require ∇f(x*)=0, so boundary minimizers are excluded. |

**Reduction check.** Markov conversion of expected results loses polynomial factors in 1/δ. Boosting by selecting among repeated runs needs objective comparisons. Without function values, those comparisons could be rebuilt by integrating stochastic gradients along segments. That costs about O(LD²/ε + σ²D²/ε²) calls per comparison, so it adds a non-accelerated LD²/ε term. It also needs an expected-accuracy constrained gradient-only quasar method, and I did not find one already proved. Regularization-based proxBoost fails for γ<1. So the result is not a routine corollary. The proof does draw on known pieces, which I treat as proof ancestry. They supply the envelope M(c)=min_X{f+L‖·−c‖²}, which preserves quasar convexity (Martínez-Rubio, Prop. 2), multilevel debiasing ([Asi et al., 2106.09481](https://arxiv.org/abs/2106.09481)), and continuized acceleration (Wang–Wibisono, ICLR 2023). The new step is controlling biased, clipped, noisy acceleration with high probability through the power-barrier argument. For context on optimality, [Saad–Lee–Orabona, COLT 2025](https://proceedings.mlr.press/v291/saad25a.html), Thm 3.4 gives a lower bound of Ω(σ²D²/(γ²ε² log(2/γ))) stochastic-gradient calls for expected accuracy on balls, when d ≥ log_{16/15}(4/γ²). Hinder–Sidford–Sohoni (COLT 2020) give Ω(√(LD²/ε)/γ) in the deterministic case. Both terms of N therefore match known lower bounds up to polylogarithmic factors. The lower bounds have their own dimension restrictions, and I did not check them on this exact constrained class.

**Search coverage.** I searched on 2026-11-06 across arXiv, PMLR, OpenReview and JMLR. I read the key statements of Martínez-Rubio, Saad–Lee–Orabona, Nguyen–Ene–Nguyen and Fu–Xu–Wilson; some extractions were partial, and Fu–Xu–Wilson's γ-dependence in the accelerated term is not verified. I read DDXZ §6, Gbaguidi–Hermant [2607.19965](https://arxiv.org/abs/2607.19965) and Kuruzov et al. [2611.04597](https://arxiv.org/abs/2611.04597) only in summary. Gbaguidi–Hermant is unconstrained, uses paired zeroth-order samples and strong growth, and its confidence dependence is polynomial. Kuruzov et al. (Nov 3, 2026, about concurrent) give expected-accuracy bounds only. I could not access the Valdivia Viscarra–Stonyakin OPTIMA 2025 chapter. The theorem entered the repository on 2026-11-06 (commit b7e87e14). Its companion note's citations agree with what I verified. One thing the note leaves out is the Saad–Lee–Orabona near-matching lower bound.

**Conclusion**

**Yes: this covers a meaningful new setting at near-optimal cost, without improving the rate on any previously solved special case.** The setting is constrained, nonconvex quasar-convex optimization with only noisy gradients, and the guarantee holds with high confidence. Every baseline I verified lacks at least one of these features:

| Baseline | What it lacks |
|---|---|
| Martínez-Rubio (2026) | Deterministic only, and needs function values |
| Fu–Xu–Wilson (2023) | Unconstrained, needs component values, and gives only an expected gap |
| Convex high-confidence methods | Need γ=1, and some also need ∇f(x*)=0 |

The proved cost is

  log(1/δ) · polylog · (√(LD²/ε)/γ + σ²D²/(γ²ε²)).

On the overlap with each baseline, it matches the baseline up to logarithms, so there is no complexity gain. The only quantitative gain is against Markov conversion of Fu–Xu–Wilson's expected bound. That conversion costs roughly δ^{-2}σ²R²/(γ²ε²), and the gain matters when δ is small. Both terms of the cost match known lower bounds up to logarithms.

I could not rule out a simpler path. Routine reductions either pay polynomially in 1/δ or add an unaccelerated LD²/ε term, and they need an expected-accuracy constrained method that does not appear to exist. Priority is not fully established: one book chapter was inaccessible, and two recent preprints were read only in summary.

What can be claimed is the first high-confidence, gradient-and-projection-only accelerated guarantee I found for constrained quasar-convex optimization under finite variance. Its cost is near-optimal, but it is no faster than the existing deterministic or convex special cases.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
