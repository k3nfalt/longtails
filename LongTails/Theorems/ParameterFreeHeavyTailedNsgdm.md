# Parameter-free optimal nonconvex optimization under heavy-tailed noise

[The Lean theorem](ParameterFreeHeavyTailedNsgdm.lean) (`LongTails.Theorems.ParameterFreeHeavyTailedNsgdm.result`) proves an expected-gradient-norm guarantee for smooth nonconvex stochastic optimization when the stochastic gradients only have a bounded central `p`-th moment, `1 < p ≤ 2`. The algorithm receives nothing but the starting point: it does not know the tail index `p`, the noise scale `σ`, the smoothness constant `L`, the initial gap `Δ`, the accuracy `ε`, or the number of oracle calls it will be allowed. For every admissible instance the budget

\[
N \;=\; \Big\lceil 80\,\big(2+\log_2(S+V)\big)^2\,(S+V)\Big\rceil,\qquad
S \;=\; \frac{8000\,L\Delta}{\varepsilon^2} \;+\; L\Delta\,\sigma^{\frac{p}{p-1}}\Big(\frac{80}{\varepsilon}\Big)^{\frac{3p-2}{p-1}} \;+\; \sigma^{\frac{5p-2}{2p-2}}(L\Delta)^{-\frac{p}{2p-2}}\Big(\frac{60}{\varepsilon}\Big)^{\frac{3p-2}{2p-2}} \;+\; \Big(\frac{\sigma^2}{L\Delta}\Big)^{\frac{p}{2p-2}} \;+\; \sqrt{\tfrac{3L}{\Delta}} \;+\; \Big(\tfrac{\Delta}{3L}\Big)^{1/3} \;+\; 6^{\frac{1}{p-1}}\Big(\frac{5\sigma}{\varepsilon}\Big)^{\frac{p}{p-1}} \;+\; 1,
\]

with `V = (64(1+5σ/ε)^p((22+2p\log_2(1+5σ/ε))/(p−1))⁴)^{1/(p−1)}`, guarantees `E‖∇f(x_out)‖ ≤ ε`. The first two terms of `S` are the known-tail-index optimal complexity `Θ(LΔ/ε² + LΔσ^{p/(p−1)}ε^{-(3p−2)/(p−1)})` (Zhang et al. 2020; Liu–Zhou 2025, Theorems 3.2 and 3.3). Every published result that does not know `p` has the worse accuracy exponent `2p/(p−1)` (Liu–Zhou Theorem 3.6; Hübler–Fatkhullin–He 2025, eq. (4); Fradin et al. 2025, Theorem 4.3; Yu–Jakovetic–Kar, ICLR 2026, Theorem 2; Liu 2026, Theorem 4.2). The gain is a factor `ε^{-(2−p)/(p−1)}` (`ε^{-1}` at `p = 3/2`, `ε^{-2}` at `p = 4/3`), at the price of the polylogarithmic factor `(2+\log_2(S+V))^2` and of lower-order terms discussed below.

The contribution is a price-of-adaptivity statement, not a new analysis technique: it answers the open question of Liu and Zhou (ICLR 2025, Conclusion, item 1: "is it possible to find an algorithm that can improve our `O(T^{(1−p)/(2p)})` upper bound to the best-known `O(T^{(1−p)/(3p−2)})` rate" without any prior information on `p`) affirmatively, up to logarithmic factors, and simultaneously the question of Hübler, Fatkhullin and He (AISTATS 2025, Section 5: "it remains open whether the sample complexity that is optimal for parameter-dependent algorithms can be achieved by any algorithm without knowledge of problem parameters"). The mechanism is model selection: run plain normalized SGD with momentum on a geometric grid of momentum and step-size parameters, validate every candidate with a fresh sample mean of stochastic gradients, and double the horizon. The same idea is used by Lawrence, Kalinsky, Bradfield, Carmon and Hinder (JMLR 2026) for convex Lipschitz problems with holdout validation on function values. The novelty here is the resulting guarantee in the nonconvex heavy-tailed setting, the fact that validation on gradient norms can be analysed in expectation with nothing but the `p`-th moment bound and no concentration inequality, and the anytime form.

## Problem, oracle and information

The [setup](../Setups/ParameterFreeHeavyTailedSmooth.lean) (`LongTails.Setups.ParameterFreeHeavyTailedSmooth.spec`) is the standard class of Liu–Zhou (Assumptions 2.1–2.4 with `L₁ = σ₁ = 0`) and Hübler et al. (Assumptions 1–3):

- `f : E → ℝ` on a complete real inner-product space (any finite dimension), differentiable with `L`-Lipschitz gradient;
- `f` is bounded below by some `lower` with `f(x0) − lower ≤ Δ`;
- the oracle returns `g(x, ξ)` for IID samples `ξ ~ ν` (the repository's `IID` structure; the product form is derived internally), jointly measurable, unbiased `∫ g(x,ξ) dν = ∇f(x)`, with `∫ ‖g(x,ξ) − ∇f(x)‖^p dν ≤ σ^p` for some `p ∈ (1, 2]`. The variance may be infinite. No sample-wise smoothness, symmetry, or bounded-gradient assumption is made.

Parameters: `L > 0`, `Δ > 0`, `σ ≥ 0`, `1 < p ≤ 2`, `ε > 0`. Requiring `Δ > 0` loses nothing because `Δ` is only an upper bound on the gap.

**Information.** `Public = (E, x0)`. The algorithm is built from the space and the starting point alone; `L, Δ, σ, p, ε` and the oracle budget live only in `Params`. The Lean statement enforces this by typing: the algorithm must produce a good point whenever it is stopped after at least `N` calls, so it is anytime.

**Accuracy criterion.** `E‖∇f(X)‖ ≤ ε`, with the expectation over the samples and the algorithm's own randomness (the product of the algorithm's seed law and the oracle law), stated as an integral.

## Algorithm

The [algorithm](../Algorithms/ParameterFreeNsgdm.lean) (`LongTails.Algorithms.ParameterFreeNsgdm.algorithm`) runs phases `k = 0, 1, 2, …`. Phase `k` has horizon `T_k = 2^k` and a grid of `C_k = (2k+1)(5k+1)` candidates indexed by `(i, j)` with `0 ≤ i ≤ 2k`, `0 ≤ j ≤ 5k`:

- momentum parameter `α = e^{-i/2}` (covering `[1/T_k, 1]` with ratio `e^{1/2}`), step size `η = e^{k − j/2}` (covering `[T_k^{-2}, T_k]`);
- each candidate is one run of normalized SGD with momentum restarted from `x0` (every run in every phase starts at `x0`; nothing is warm-started): `m_1 = g(x_1, ξ_1)`, `x_{t+1} = x_t − η m_t/‖m_t‖`, `m_{t+1} = (1−α) m_t + α g(x_{t+1}, ξ_{t+1})` for `T_k` steps (Cutkosky–Mehta 2020; Liu–Zhou 2025, Algorithm 1 with `B = 1`), returning `x_τ` with `τ` uniform on `{1, …, T_k}` from the algorithm's seed;
- validation: for every candidate `y_c`, the mean of `T_k` fresh stochastic gradients at `y_c` is formed, and the candidate with the smallest sample-mean norm is selected (ties broken by the smaller index);
- the point returned at any truncation is the selected point of the last completed phase (`x0` before phase 0 completes).

Phase `k` costs `2 C_k T_k` oracle calls; all runs, all validation batches, and the partial phase at truncation are counted. The seed is a sequence of uniform indices, one per candidate per phase, with law `Measure.infinitePi` of finite uniform product measures.

## Guarantee and proof

The proof modules are [Run](../Proofs/ParameterFreeNsgdmRun.lean) (descent step `f(x_{t+1}) ≤ f(x_t) − η‖∇f(x_t)‖ + 2η‖m_t − ∇f(x_t)‖ + Lη²/2`, which also holds when `m_t = 0`; exact EMA decomposition `m_{t+1} − ∇f(x_t) = N_t + B_t` with `‖B_t‖ ≤ Lη(1−α)/α`), [Moments](../Proofs/ParameterFreeNsgdmMoments.lean) and [RunMoments](../Proofs/ParameterFreeNsgdmRunMoments.lean) (`E‖N_t‖^p ≤ 6σ^p((1−α)^{pt} + α^{p−1})` by a time-indexed version of the repository's Hilbert-space Bahr–Esseen bound under the product measure), [RunBound](../Proofs/ParameterFreeNsgdmRunBound.lean) (Lemma A: `(1/T)Σ_t E‖∇f(x_t)‖ ≤ Δ/(ηT) + 3Lη/α + 12σ/(αT) + 12σα^{(p−1)/p}` for every `α ∈ (0,1]`, `η > 0`), [Grid](../Proofs/ParameterFreeNsgdmGrid.lean) (Lemma B: a grid point within a factor `e^{1/2}` of the optimal `(α⋆, η⋆)`, `α⋆ = min{1, max{1/T, (LΔ/(σ²T))^{p/(3p−2)}}}`, `η⋆ = √(Δα⋆/(3LT))`, loses only constant factors), [Selection](../Proofs/ParameterFreeNsgdmSelection.lean) and [Phase](../Proofs/ParameterFreeNsgdmPhase.lean) (Lemma C: pathwise `‖∇f(y_ĉ)‖ ≤ ‖∇f(y_c)‖ + e_c + (Σ_{c'} e_{c'}^p)^{1/p}` with `e_c` the validation errors, then `E e_c ≤ (6σ^p/T^{p−1})^{1/p}` and `E (Σ e_{c'}^p)^{1/p} ≤ (6 C_k σ^p/T^{p−1})^{1/p}` using only the `p`-th moment of fresh batch means; the uniform index turns the time average of Lemma A into the expectation at the returned iterate), [Execution](../Proofs/ParameterFreeNsgdmExecution.lean) (the state machine equals the phase recursion; the output is stable within a phase), [Budget](../Proofs/ParameterFreeNsgdmBudget.lean) (inversion of the per-phase bound; the validation term is non-monotone in `k` for small `k` when `p` is near 1, so the phase threshold is an explicit `K̄` after which it is below `ε/5` for all later phases) and [Main](../Proofs/ParameterFreeNsgdmMain.lean).

Per-phase bound: for every phase `k` with `2^k ≥ S` and `k ≥ K̄` (both implied by `k ≥ K⋆ := ⌈max(\log_2 S, K̄)⌉`),

\[
E\|\nabla f(x_{\text{out},k})\| \le 2\sqrt3 e^{1/2}\sqrt{\tfrac{L\Delta}{\alpha_\star T_k}} + 12 e^{1/4}\sigma\alpha_\star^{(p-1)/p} + \tfrac{12\sigma}{\alpha_\star T_k} + \Big(\tfrac{6\sigma^p}{T_k^{p-1}}\Big)^{1/p} + \Big(\tfrac{6 C_k\sigma^p}{T_k^{p-1}}\Big)^{1/p} \le \varepsilon .
\]

In the heavy-tail regime (`LΔ < σ²T_k`) the first two terms equal constant multiples of `M = (LΔ/T_k)^{(p−1)/(3p−2)}σ^{p/(3p−2)}`, the known-`p` optimal rate, and the third equals `12 M²σ/(LΔ)` (the initial-sample term). The budget is `phaseStart(K⋆+1) ≤ 4 C_{K⋆} 2^{K⋆} ≤ N`, and since the guarantee holds for every later phase, it holds for whatever phase is the last completed one at `N` calls.

## Comparison with the closest results

| result | known to the algorithm | heavy-tail accuracy exponent (calls) | guarantee |
|---|---|---|---|
| Liu–Zhou, ICLR 2025, Thm 3.2 ([arXiv 2412.19529](https://arxiv.org/abs/2412.19529)) | `p, σ, L, Δ, T` | `(3p−2)/(p−1)` (optimal, Thm 3.3) | expectation |
| Liu–Zhou Thm 3.6 / Thm D.2 | `T` (and `L₁` if `L₁ > 0`) | `2p/(p−1)` | expectation |
| Hübler–Fatkhullin–He, AISTATS 2025, eq. (4) ([arXiv 2410.13849](https://arxiv.org/abs/2410.13849)) | `T` | `2p/(p−1)` plus `ε^{-4}(Δ⁴+L⁴)`; Thm 2 shows this is tight for minibatch NSGD with polynomial schedules | expectation |
| Fradin et al. 2025, Thm 4.3 ([arXiv 2512.18713](https://arxiv.org/abs/2512.18713)) | `T, L̄, Δ` | `2p/(p−1)` | expectation |
| Yu–Jakovetic–Kar, ICLR 2026 (GT-NSGDm), Thm 2 ([arXiv 2505.03736](https://arxiv.org/abs/2505.03736)) | `T, L` (decentralized) | `2p/(p−1)` | expectation |
| Liu, ICML 2026, AdaGrad-Norm Thm 4.2 ([arXiv 2605.18694](https://arxiv.org/abs/2605.18694)) | nothing | `2p/(p−1)`; an algorithm-dependent lower bound shows AdaGrad cannot reach the minimax rate | expectation |
| He–Lu–Sun–Deng 2025, Thms 2/4/6 ([arXiv 2506.11214](https://arxiv.org/abs/2506.11214)) | tail index unknown, `L, σ`-agnostic | worse than `(3p−2)/(p−1)` | expectation |
| this work | nothing (anytime) | `(3p−2)/(p−1)` up to `(2+\log_2(S+V))^2` | expectation |

Reading the table: the two algorithm-specific lower bounds (Hübler et al. Theorem 2 for NSGD; Liu 2026 for AdaGrad) are not barriers for general algorithms. The known-`p` baselines use strictly more information than this method and reach the same exponent without the logarithmic factor; the unknown-`p` baselines use the same or less information (`T`) and lose a polynomial factor. Liu–Zhou's question 2 (a lower bound for unknown `p`) is therefore moot beyond logarithmic factors.

## Limitations

- **Logarithmic and constant factors.** The grid has `(2k+1)(5k+1)` candidates and the validation cost doubles the phase cost, giving the `(2+\log_2(S+V))^2` factor. The term `V = 64^{1/(p−1)}(1+5σ/ε)^{p/(p−1)}((22+2p\log_2(1+5σ/ε))/(p−1))^{4/(p−1)}` is the phase index after which the `C_k^{1/p}` validation loss is below `ε/5` for *every* later phase (the validation term is not monotone in `k` for small `k` when `p` is near 1); it has the accuracy exponent `p/(p−1) < (3p−2)/(p−1)` and a `\log^{4/(p−1)}(1+σ/ε)` factor. Altogether the budget is the known-`p` optimal complexity times `O((\log(S+V))^2)`, plus lower-order terms carrying `\log^{4/(p−1)}` factors. Constants such as `8000`, `80^{(3p−2)/(p−1)}` and the `1/(p−1)` exponents are not optimized and blow up as `p → 1`, as in all known heavy-tailed analyses.
- **Lower-order terms.** `S` contains the initial-sample term `σ^{(5p−2)/(2p−2)}(LΔ)^{-p/(2p−2)}(60/ε)^{(3p−2)/(2p−2)}` (dominated by the main term whenever `σε ≤ 80·LΔ`-type conditions hold), the momentum-range term `(σ²/(LΔ))^{p/(2p−2)}` and the validation terms `6^{1/(p−1)}(5σ/ε)^{p/(p−1)}` and `V` (all dominated by the main term when `ε² ≤ LΔ`, up to the logarithmic factor in `V`), and the step-size-range terms `√(3L/Δ) + (Δ/(3L))^{1/3}` (the price of not knowing the scale `Δ/L`). None of them changes the accuracy exponent.
- **Noiseless case.** With `σ = 0` the budget reduces to `O((LΔ/ε² + √(L/Δ) + (Δ/L)^{1/3} + c_p)·\log^2(·))` with `c_p = (64(22/(p−1))^4)^{1/(p−1)}` a constant depending only on `p`: the deterministic `LΔ/ε²` rate up to the grid-search logarithm, again without knowing `L` or `Δ`.
- **Expectation only.** The guarantee is in expectation; a high-probability version with logarithmic confidence dependence is not claimed.
- **Mechanism.** The method is a grid search with validation; it is not a single-run adaptive scheme, and no new analysis technique is claimed. Whether a single-run method (one trajectory, no validation) can be tail-index-oblivious and optimal remains open.
- **Literature.** The assessment covers ICLR/ICML/NeurIPS 2024–2026 and arXiv through November 2026 as recorded in the review; a published construction achieving the optimal exponent without `p` was not found.
