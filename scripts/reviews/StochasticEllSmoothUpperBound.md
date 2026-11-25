# StochasticEllSmoothUpperBound: novelty assessment

[`result`](../../LongTails/Theorems/StochasticEllSmoothUpperBound.lean) proves the following. Take any `f` on a complete real Hilbert space with `‖∇²f(x)‖ ≤ ℓ(‖∇f(x)‖)`, where `ℓ` is nondecreasing and regular of order `ρ ∈ [0,2)` (`ℓ(v)u^ρ ≤ ℓ(u)v^ρ` for `u ≤ v`), and `f(x₀) − inf f ≤ Δ`. Take IID unbiased stochastic gradients whose central `p`-th moment is at most `σ^p`, for `p ∈ (1,2]` ([setup](../../LongTails/Setups/StochasticEllSmoothNonconvex.lean)). Then the medoid-of-block-means method with freezing and an `x₀` fallback ([algorithm](../../LongTails/Algorithms/StochasticEllSmoothMedoid.lean)) returns a single output with `E‖∇f(x̂)‖ ≤ ε`.

**Proved budget.** The budget is a deterministic count of stochastic-gradient calls:

`O( (1 + Δℓ(ε)/ε²) · (1 + (Cσ/ε)^{p/(p−1)}) · log(2 + Δℓ(ε)/ε²) / (2−ρ) )`, with `C = 2¹⁶`.

- The constant `2^{16p/(p−1)}` blows up as `p → 1`.
- For `ℓ(u) = L₀ + L_ρu^ρ` we have `Δℓ(ε)/ε² = L₀Δ/ε² + L_ρΔ/ε^{2−ρ}`.
- The updates need `ℓ, ρ, p, σ, Δ, ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2412.11773](https://arxiv.org/abs/2412.11773) v2 (27 Jun 2025, ICML 2025), Thm 9.2, Alg. 2 | `O((1+σ²/ε²)(1+Δℓ(ε)/ε²)·log(Δℓ(ε)/(ε²δ)))` (his `ε` is our `ε²`) → the bound above at `p=2` | None: same order up to the log, which differs in form (his `log(T/δ)`, ours `log(2+T̄)/(2−ρ)`) | Sub-Gaussian noise (Assump. 9.1) → finite variance, or a finite `p`-th moment with `p<2` | High-probability min-iterate `min_k‖∇f(x_k)‖ ≤ ε` (iterate not identified) → expectation for one identified output; neither converts to the other directly | Ours gives no `1−δ` statement; both need `ℓ, σ` |
| Li et al., [arXiv:2306.01264](https://arxiv.org/abs/2306.01264) v2 (NeurIPS 2023), Thm 5.3 | `O(ℓ(2G)F/ε² + G²F²/ε⁴)` with `F ≍ (Δ+σ)/δ` and `G² = 2ℓ(2G)F`; for the polynomial `ℓ`, `G ≳ (L_ρF)^{1/(2−ρ)}` → ours `≍ Δℓ(ε)σ²/ε⁴` | Not comparable: different criteria. The leading `ε⁻⁴` coefficient is `ℓ(2G)F³` with `δ⁻³` (theirs) versus `ℓ(ε)Δσ²` (ours), which is much smaller when `L_ρ>0` and `ε` is small | Variance `σ²` → `p`-th moment | Average of `‖∇f‖²` with probability `1−δ` → expectation for one output | Li uses plain constant-step SGD, with no batching or robust estimator |
| Liang–Luo, [arXiv:2610.21692](https://arxiv.org/abs/2610.21692) v2 (15 Nov 2026), Thm 5.1 (MB-NSGD); covers only `ρ = 1` | `O((1+(σ/ε)^{p/(p−1)})(L₀Δ/ε² + L₁Δ/ε))` → ours at `ρ=1` | Worse by `log(2 + L₀Δ/ε² + L₁Δ/ε)` and constants | `ρ = 1` → every `ρ ∈ [0,2)`; for `ρ ∈ (1,2)` the classes are strictly larger | None: the accuracy criterion is the same (Liang–Luo use a uniformly random iterate) | Extra log; the `1/(2−ρ)` factor; larger `p`-dependent constants |
| Ghadimi–Lan SGD and Liang–Luo at `L₁=0` (`ρ=0`, `L`-smooth) | `O((1+(σ/ε)^{p/(p−1)})LΔ/ε²)` → ours | Worse by `log(2+LΔ/ε²)` | None | None | Same as the row above |

**Reduction check.** The proof plausibly reduces to known pieces in a high-probability form, though we have not checked this:

- Tyurin's per-step analysis, which uses sub-Gaussianity only through batch-mean concentration;
- a geometric-median or medoid-of-means estimator, which gives the same concentration under `p`-th moments (Minsker 2015; Puchkin et al. [arXiv:2311.04161](https://arxiv.org/abs/2311.04161));
- a union bound over the rounds.

The obstacle we did not find addressed elsewhere is the in-expectation guarantee for a single output when `ρ>1`. On the failure event, the gradient at a mis-stepped point is unbounded in this class. The proof handles this with freezing and an `x₀` fallback, whose gradient is bounded by `G₀ = ε(1+(16T̄)^{1/(2−ρ)})` because `ρ<2`. It also uses a medoid tail bound that controls the excess error when the run freezes on a wrong estimate. This mechanism is modest but not a mere substitution. The step rule `x − v/(2ℓ(3‖v‖))` and the safe-step lemma are inherited from Tyurin and repository PR #244.

**Search coverage.** Searched on 2026-11-25:

- arXiv and proceedings for stochastic and heavy-tailed results under ℓ-, `(ρ,L₀,L_ρ)`- and `(L₀,L₁)`-smoothness;
- clipping, normalization, sign, and median-of-means methods;
- Tyurin Thm 9.2 and Liang–Luo Thm 5.1, read in full text;
- Li et al. Thm 5.3, read only through a summary of the HTML.

The 2026 papers we found ([2609.06555](https://arxiv.org/abs/2609.06555) is convex and sub-Gaussian; [2505.20817](https://arxiv.org/abs/2505.20817) and [2502.07923](https://arxiv.org/abs/2502.07923) assume `ρ ≤ 1`) do not cover `ρ ∈ (1,2)` under heavy tails. We did not inspect the appendices of Liang–Luo or the medoid-SGD paper [2605.07634](https://arxiv.org/abs/2605.07634). The companion note's citations match what we checked. The result was introduced in commit `f5b3e4a4` on 2026-11-24, after every source cited above.

**Conclusion**

**Yes, for `ρ ∈ (1,2)` this appears to be the first `ℓ(ε)`-rate guarantee beyond light-tailed noise. For `ρ ≤ 1` there is no improvement.** The closest baseline is Tyurin's Theorem 9.2. Under sub-Gaussian noise, it gives the same order with high probability, for an iterate that is not identified:

| | noise | guarantee | calls |
|---|---|---|---|
| Tyurin | sub-Gaussian | `min_k‖∇f(x_k)‖ ≤ ε` w.p. `1−δ` | `(1+σ²/ε²)(1+Δℓ(ε)/ε²)·log(T/δ)` |
| This result | `p`-th moment, `p∈(1,2]` | `E‖∇f(x̂)‖ ≤ ε`, one output | `(1+(σ/ε)^{p/(p−1)})(1+Δℓ(ε)/ε²)·log(2+Δℓ(ε)/ε²)/(2−ρ)` |

So the rate is unchanged. What is new is removing the light-tail assumption, and with it covering heavy-tailed noise for superlinear `ℓ` such as `L₀ + L_ρu^ρ`. The only earlier heavy-tailed-compatible guarantee for this class is Li et al.'s, which depends on a sublevel gradient bound and on `δ⁻³`. At `ρ = 1`, Liang–Luo's log-free optimal bound is strictly better; at `ρ = 0`, classical SGD is.

Some steps are routine: robust gradient estimation, and the high-probability version, which plausibly follows from Tyurin's analysis plus median-of-means. The substantive step is the expectation-for-one-output argument, which bounds the damage of a failure when `ρ>1`. Our search did not find prior coverage, but that does not prove priority.

What can be claimed is a near-optimal heavy-tailed stochastic guarantee for generalized smoothness with `ρ ∈ (1,2)`, up to a logarithmic factor and `p`-dependent constants.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
