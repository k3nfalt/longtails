# Novelty assessment: MinibatchSignSgdUpperBound

[`result`](../../LongTails/Theorems/MinibatchSignSgdUpperBound.lean) proves that minibatch SignSGD ([algorithm](../../LongTails/Algorithms/MinibatchSignSgd.lean)) with step `η = ε/(2L)`, `T = ⌈8LΔ/ε²⌉+1` steps and batch `B = ⌈16S²/ε²⌉+1`, returning a uniformly random iterate, satisfies `E‖∇f(x_τ)‖₁ ≤ ε`. This holds for every differentiable `f` on `ℝ^d` with `Σ_i|∂_if(x)−∂_if(y)| ≤ L‖x−y‖∞` and `f(x0) − inf f ≤ Δ`, accessed through an unbiased IID oracle with `Σ_i (E(g_i(x)−∂_if(x))²)^{1/2} ≤ S` at every `x` ([setup](../../LongTails/Setups/SeparableNoiseLinfSmooth.lean)).

**Complexity.** Here `L` is the ℓ∞→ℓ1 gradient-Lipschitz constant, `Δ` the initial gap, `S` the pointwise ℓ1 sum of coordinate noise standard deviations, and `ε` the expected ℓ1-stationarity target. The bound holds for all `d`, `L>0`, `S,Δ≥0`, `ε>0`:

  `N = O((1 + LΔ/ε²)(1 + S²/ε²)) = O(1 + LΔ/ε² + S²/ε² + LΔS²/ε⁴)` stochastic gradient calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tao–Yu–Zhang, [arXiv:2605.06615 v1](https://arxiv.org/abs/2605.06615) (7 May 2026; NeurIPS 2026 poster), Thm. 1 and eq. (9): minibatch SignSGD with `B = max{1, ‖σ⃗‖₁²T/(LΔ)}` | `O(1 + LΔ/ε² + ‖σ⃗‖₁²LΔ/ε⁴)` with `‖σ⃗‖₁ ≤ S` → `O((1+LΔ/ε²)(1+S²/ε²))` | None: same order. The extra `S²/ε²` term only matters when `LΔ < ε²`. | Fixed per-coordinate noise vector `σ⃗` → point-dependent profile `Σ_iσ_i(x) ≤ S`. Their two-sided quadratic smoothness (Asm. 3a) → ℓ∞→ℓ1 Lipschitz gradient, a narrower condition. So the two classes are incomparable. | Averaged `E[(1/T)Σ‖∇f(x_t)‖₁]` → random iterate. These are the same expectation, so neither is stronger. | Fresh IID samples per call, versus their conditionally unbiased, martingale-adapted samples. Stronger smoothness form. |
| Bernstein et al., [ICML 2018, arXiv:1802.04434](https://arxiv.org/abs/1802.04434), Thm. 1 (SignSGD, batch `= K`, step `1/√(‖L⃗‖₁K)`) | As stated: `O((‖L⃗‖₁(Δ+1) + ‖σ⃗‖₁²)²/ε⁴)`. Retuning their proof to `η ≍ ε/L` and `B ≍ ‖σ⃗‖₁²/ε²` gives the bound above. | Only against their untuned schedule. With the proof retuned: none, same order. | The same fixed-`σ⃗` → pointwise generalization. Their smoothness is separable with vector `L⃗`, which gives this class's `L ≤ (Σ√L_i)²`. | None | IID samples and an ℓ∞-type smoothness constant |

**Standard-reduction check.** The proof (ℓ∞ descent lemma, the bound `a·sign(m) ≥ |a| − 2|m−a|`, a coordinatewise minibatch variance bound, telescoping) is exactly the Bernstein / Tao–Yu–Zhang argument. Because each step is analyzed conditionally on `x_t`, replacing the constant `σ_i` by `σ_i(x_t)` with `Σ_iσ_i(x_t) ≤ S` needs no new idea. The only proof ancestry is this one-step SignSGD analysis. I found no new mechanism. The companion all-algorithm lower bound uses a separate construction and is not assessed here.

**Scope example.** The pointwise class is strictly larger than the fixed-vector class. Take noise of size `S` placed on a coordinate `i(x)` that varies with `x`. A fixed vector covering it needs `σ_i = S` for every `i`, so `‖σ⃗‖₁ = dS`, and the prior noise term grows by a factor `d²`. No application of this moving-sparse-noise model is given or checked here.

**Search coverage (2026-11-19).** I searched arXiv and NeurIPS/ICML sources for SignSGD under ℓ∞/ℓ1 geometry, separable noise and heavy tails, including Kornilov et al. [arXiv:2502.07923](https://arxiv.org/abs/2502.07923) and Yu et al. [arXiv:2602.07425](https://arxiv.org/abs/2602.07425). For Tao–Yu–Zhang I read v1 through the arXiv HTML; the later parts of the appendix were not read verbatim. For Bernstein et al. Thm. 1 I relied on my knowledge of the paper and did not re-read it. Both papers predate this result, which was introduced in commit `04a401ca` (2026-11-19). The companion note says itself that the rate is known, which agrees with these findings. Its claim that the class is broader is correct but minor.

## Conclusion

**No: this upper bound gives a known rate, and the proof is the standard one.** The strongest baseline is Tao–Yu–Zhang (May 2026), Theorem 1. Under fixed coordinatewise noise `σ⃗` it proves the same complexity for the same algorithm, the same ℓ1-stationarity criterion and the same expectation. Bernstein et al. (2018) contains the argument with an untuned schedule.

| | ℓ1-stationarity calls |
|---|---|
| Tao–Yu–Zhang Thm. 1 | `O(1 + LΔ/ε² + ‖σ⃗‖₁²LΔ/ε⁴)` |
| This theorem | `O((1 + LΔ/ε²)(1 + S²/ε²))` |

The only difference in scope is that the per-coordinate noise level may vary with the query point, as long as its ℓ1 sum stays below `S`. This strictly enlarges the noise class: it covers sparse noise whose support moves with `x`, where a fixed noise vector could lose a factor `d²`. However, the conditional one-step proof handles it unchanged. In return, the smoothness condition is a stronger gradient-Lipschitz form and samples must be IID.

This theorem has no present-day complexity advantage in any regime. Its value lies in the repository: it supplies the upper half of the companion lower bound's Θ-characterization. What can be claimed is a formal verification of the known minibatch-SignSGD rate under a mildly generalized, pointwise noise condition.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
