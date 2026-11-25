# Novelty assessment: TwoTapLogisticSeparation

[`result`](../../LongTails/Theorems/TwoTapLogisticSeparation.lean) proves the following. Take constant-step full-batch GD on the mean logistic loss of the bilinear two-tap model `mᵢ = ⟨a xᵢ + b S xᵢ, v⟩`, started at the given `(a₀,b₀,v₀)`, and return the last iterate. After the stated number of exact negative-gradient calls, every training margin is strictly positive. The update and output rule are enforced by `allowedAlgorithm` ([setup](../../LongTails/Setups/TwoTapLogisticSeparation.lean), [algorithm](../../LongTails/Algorithms/TwoTapLogisticGd.lean)).

**Hypotheses.**
- The rows satisfy `‖xᵢ‖ ≤ R`.
- Both views `(I+S)xᵢ` and `(I−S)xᵢ` have unit-ball separators with margin `γ`.
- The initialization satisfies either `F₀ ≤ log 2 − δ`, or `F₀ ≤ 1` together with `U − V ≥ δ`.
- Here `U = a₀² + b₀²` and `V = ‖v₀‖²`, and `γ, δ, R > 0`.
- The class is empty when `d = 1`, because then `S = I`.

**Simplified budget.** Let `W = 2 + |U − V|`. Let `K ≍ W/δ` when `δ ≤ U − V`, and `K ≍ W + R²W²/δ²` otherwise. Then

`T = O( n(1+R)·K·[1 + R + R²(1+U+V) + R²√K/γ + 𝟙{δ≤U−V}/δ] / γ² · log(2 + R + U + V + √K·log^{3/2}(8n)/γ) )`.

With the initialization fixed and `R ≥ 1`, the leading term is about `nR³K^{3/2}/γ³`. In the deficit case this becomes `nR⁶W³/(γδ)³`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fixed-filter logistic GD. Query the same oracle at `((1,0),w)`, start from `w₀ = 0`, use constant step `1/R²`. Risk bound: [Ji–Telgarsky, arXiv 1803.07300 Thm 3.1](https://arxiv.org/abs/1803.07300) (COLT 2019). Separation then follows from `F < log2/n`. | `O((nR²/γ²)·log²(2+nR/γ))` → `T` above. Uses raw margin `≥ γ/2`, since `‖(I+Sᵀ)u‖ ≤ 2`. | Worse by a factor of at least `(1+R)K^{3/2}/(γ·log²(2+nR/γ))`. This holds because `T ≳ (nR²/γ²)(1+R)K^{3/2}/γ` and `γ ≤ 2R`. The selected bound is better only by a polylog factor (`log²n` vs `log log n`), and only when `R/γ, U, V, 1/δ = O(1)` and `n → ∞`. | None. The baseline needs only raw separability, which is implied by the sum-view assumption. | None. Both give a deterministic final-iterate separator. | The baseline leaves the given initialization and the two-tap GD family. It is excluded by `allowedAlgorithm` but uses the same oracle. The selected result additionally needs difference-view separability and the `δ` initialization condition. |
| Normalized LR+GD: [Tyurin, AAAI 2025, arXiv 2412.08424 Thm 6.1](https://arxiv.org/abs/2412.08424) (statement read via a fetched summary). | `R²/μ² + 2log(2n−1)/(η̄μ²)` steps, with `μ ≥ γ/2`, so `O(R²/γ²)` for a large step → `T`. | Worse: linear versus logarithmic dependence on `n`, plus a worse dependence on `R/γ`. | None | None | Stronger oracle: the step needs the mean sigmoid `Q`, which a gradient-only reply does not reveal. |
| Risk-adaptive GD: [Zhang–Wu–Lin–Bartlett, arXiv 2504.04105 Thm 2.1, Fact 1](https://arxiv.org/abs/2504.04105) (JMLR 2026). Their Thm 3.2 lower bound is `min{ln n/(8 ln2), 1/(30γ²)}` for batch first-order methods. | `O(R²/γ²)` averaged iterates, `n`-free → `T`. | Worse in both `n` and `R/γ`. | None | Averaged iterate → last iterate; this is minor, because the baseline output is still a separator. | Stronger oracle: needs loss values. |

**Reduction check.** The fixed-filter reduction above already solves the problem class with fewer calls under weaker data assumptions. The selected result is therefore not a problem-class improvement. The new technical content is specific to the method:
- two moving layers are controlled at one fixed step from non-separating initializations;
- the imbalance drift is paid for by loss descent;
- a bound on the squared augmented energy is obtained from `log³(2/F)`.

Proof ancestry is the standard logistic descent argument and the conservation law for the `‖v‖² − a² − b²` imbalance known from linear-network gradient flow. Full-matrix deep-linear analyses do not cover the circulant two-tap restriction. [Ji–Telgarsky 1810.02032](https://arxiv.org/abs/1810.02032) gives only asymptotic GD results with adaptive steps. [Lyu–Li](https://arxiv.org/abs/1906.05890) starts from separated initializations. I found no prior finite-time constant-step bound for this bilinear model.

**Search coverage (2026-11-25).** I searched arXiv, COLT, AAAI, JMLR and ICLR sources on logistic GD separation, large and normalized steps, and linear and convolutional networks. Some theorem statements were read only through fetched summaries: Tyurin Thm 6.1, Zhang et al. Thm 3.2, and the Ji–Telgarsky 1810.02032 GD theorems. The `log²` substitution into Ji–Telgarsky Thm 3.1 is mine. [Tyurin 2512.11587](https://arxiv.org/abs/2512.11587) poses the empirical two-tap question, but its only two-tap bound is for a two-sample noisy quadratic perceptron (Thm 5.1). The companion note is consistent with the Lean statement. It already concedes the unrestricted `O(n(R/m)³)` alternative (an unverified sketch), and it concedes that the worst-case budget (`~10³⁸`) does not explain the Figure 1 speedup. The result was introduced in commit `6ff98d9d` (2026-11-26), and all cited baselines predate it.

**Conclusion**

**No optimization advantage is established; the novelty is a finite-time analysis of constant-step GD on one particular bilinear two-tap model.** The strongest relevant baseline uses the same gradient oracle. It freezes the filter at `(1,0)` and runs ordinary logistic-regression GD (Ji–Telgarsky), which needs only raw separability.

| Guarantee | Full-gradient calls to strict separation |
|---|---|
| fixed-filter GD (Ji–Telgarsky) | `O((nR²/γ²) log²(2+nR/γ))` |
| this result | `≳ (nR²/γ²)·(1+R)K^{3/2}/γ`, where `K ≥ W/δ` grows with the initial imbalance and `1/δ` |

The selected bound wins only a polylogarithmic factor in `n`, and only when `R/γ`, the initial energies and `1/δ` are all bounded. It is polynomially worse as soon as any of these grows. It also requires an extra difference-view margin and an initialization condition. Methods with loss-value access, or access to the mean sigmoid, reach `O(R²/γ²)` independent of `n`.

The comparison above shows that no complexity gain exists, independent of any priority question. Separately, my search found no earlier finite-time constant-step separation bound for two-tap GD from non-separating initializations, so that method-specific analysis may well be new. However, the bound is too loose to explain the observed speedup of the learned filter. What can be claimed is a first explicit finite-time separation guarantee for this fixed method, not a better guarantee for the problem.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
