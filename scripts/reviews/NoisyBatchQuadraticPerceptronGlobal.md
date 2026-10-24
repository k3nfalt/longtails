# Novelty assessment: NoisyBatchQuadraticPerceptronGlobal

[`result`](../../LongTails/Theorems/NoisyBatchQuadraticPerceptronGlobal.lean) proves the following for every finite dataset that is linearly separable with margin δ: the noisy, averaged-batch quadratic perceptron on the width-one model `v⟨a,c⟩` ([algorithm](../../LongTails/Algorithms/NoisyBatchQuadraticPerceptron.lean)) outputs a strict separator with probability at least `1−ρ`. Here `η = δ/(8(n+1)R²)`, the noise scale `σ > 0` is fixed, the initialization `w₀` is arbitrary, and the setup is [`NoisyBatchQuadraticPerceptron`](../../LongTails/Setups/NoisyBatchQuadraticPerceptron.lean).

**Parameters.** `n` is the number of examples, `d` the dimension, `‖a_i‖ ≤ R` bounds the signed examples, `δ` is the margin, `w₀` is the initial weight, `σ` the noise scale, and `ρ` the failure probability. A cost unit is one per-example oracle call, which returns the margin `v⟨a_i,c⟩` and the gradient `(v a_i, ⟨a_i,c⟩)`. The proved budget, with the outer constant suppressed but the constants in the exponent kept, is

`O( (n/ρ)·(n²R²/δ² + ‖w₀‖²/(dσ²)) · (2/ρ)^{5·exp(25000 (d+1)² (n+1)⁴ R⁴/δ⁴)} ).`

This is valid for `0 < δ ≤ R`, `σ > 0` and `0 < ρ < 1`. Even at `n = d = 1` and `R = δ`, the exponent of `2/ρ` is `5e^{1.6·10⁶}`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Direct competitor, same oracle: query every example once at `(c,v) = (0,1)`. Each reply's direction equals `(a_i, 0)`, so the whole dataset is recovered; then solve the linear feasibility problem offline and output `(c,1)`. | `n`, deterministic → the budget above | Worse: by a factor of at least `(2/ρ)^{5e^{25000(d+1)²(n+1)⁴R⁴/δ⁴}}·(n²R²/δ²)/ρ` in every regime | None: the same data class | None: both certify a separating output; the baseline is deterministic | Offline computation is unrestricted. The selected result instead requires the prescribed noisy QPA family, enforced through `allowedAlgorithm`. |
| Direct competitor, same oracle and an iterative method: cyclic classical perceptron (Novikoff 1962, the mistake bound `(R/δ)²`). Query `(x,1)`, whose reply is `⟨a_i,x⟩` together with `a_i`. | `n((R/δ)² + 1)`, deterministic, from `x₀ = 0` → the budget above | Worse: doubly exponential in `d`, `n` and `R/δ`, and polynomial in `1/ρ` instead of independent of it | None | Arbitrary `w₀` is covered, but the perceptron also converges from any `x₀`, with an added `‖x₀‖`-dependent term | The baseline uses a linear model rather than the factorized model. |
| Prior work: Tyurin, [arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587) (21 May 2026, ICML 2026), Thm 5.1. Restriction: `n = 2`, dataset (5), convolutional `k = 2` model, non-batch noisy QPA. | `Õ(√d/µ)` steps with probability `1−ρ` → not comparable | Not comparable: the models differ, there is no common instance, and the acceleration is not retained | Two-sample, convolutional, specially tuned σ → any `n`, any separable data, width-one two-layer model, any fixed σ > 0 | Probability `1−ρ` → also almost-sure eventual constancy of the frozen output | Batch updates instead of non-batch; the rate is lost. |
| Repository: [`TwoSampleQuadraticPerceptronAcceleration`](../../LongTails/Theorems/TwoSampleQuadraticPerceptronAcceleration.lean). Restriction: `n = 2`, noiseless non-batch QPA, initialization in a data-dependent cone. | `O((R/gain)² log(·))` → the budget above, specialized to `n = 2` | Worse wherever both apply, but the update rules differ | Cone initialization (about a quarter of Gaussian starts) → every `w₀`; `n = 2` → any `n` | Deterministic → probabilistic or almost-sure | Requires injected noise; the update is batch rather than non-batch. |

**Reduction check and proof ancestry.** No standard reduction gives the dynamics theorem: clipping, fixing `v` or restarting would change the method. However, the reductions in rows 1–2 settle the problem-class question. The new mechanism is the nonsmooth potential `V` with uniform Gaussian-escape trials and a regeneration argument (`NoisyBatchQuadraticPerceptron{Drift,Escape,Regeneration}`). Tyurin's Thm 2.1 supplies the QPA-as-GD-limit motivation, stated for the convolutional model, and §4 defines noisy QPA with no convergence theorem. Ji–Telgarsky ([ICLR 2019, Thm 2.2](https://arxiv.org/abs/1810.02032)) prove risk → 0 for gradient flow on deep linear networks, but only under `R(W(0)) ≤ ℓ(0)`. They study logistic gradient flow rather than QPA and give no rate.

**Search coverage.** On 24 Oct 2026 UTC I read the Tyurin v2 HTML theorem list and checked the assumptions of Ji–Telgarsky Thm 2.2 in the PDF. I also searched arXiv and the web for follow-ups on QPA and on noisy perceptron or two-layer separable dynamics, and found none proving this statement. I did not independently verify the companion note's other citations (Yu et al. 2014; Wang et al. 2023; Wang–Giannakis–Chen 2019; Bianchi et al.). The companion note's characterization agrees with the Lean statement: an arbitrary-`n`, arbitrary-start guarantee with no complexity claim. The result entered the repository in commit `f1bb72d` on 24 Oct 2026.

**Conclusion**

**No: this is another analysis of one prescribed method, with a complexity astronomically worse than trivial baselines.** The strongest baseline uses the same per-example oracle. One query per example at `(0,1)` reveals every `a_i`, which leaves an offline linear-feasibility problem. The classical perceptron, run through this oracle, also certifies a separator deterministically:

| Method | Oracle calls |
|---|---|
| Data recovery + LP | `n` |
| Cyclic perceptron | `n((R/δ)² + 1)` |
| This result | `(n/ρ)(n²R²/δ² + ‖w₀‖²/(dσ²))·(2/ρ)^{5e^{25000(d+1)²(n+1)⁴R⁴/δ⁴}}` |

The selected bound loses in every parameter regime. It gains nothing in scope or output either, because both baselines already handle every bounded separable dataset. What is new is method-specific: almost-sure global convergence of the noisy batch QPA for the width-one two-layer model, from every initialization and for arbitrary `n`. Tyurin defines noisy QPA but proves a result only for a two-sample convolutional instance. The Thm 5.1 acceleration, the main motivation for studying QPA, is not retained.

The comparison establishes that there is no complexity, scope or output improvement. The literature search found no prior proof of this dynamics statement, but that is weak evidence of priority, and the significance of the statement alone is limited. The claimable contribution is a first global convergence proof for this particular noisy factorized perceptron, not a better guarantee for linear classification.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
