# Novelty assessment: SublevelPLWeightedGradient

[`result`](../../LongTails/Theorems/SublevelPLWeightedGradient.lean) proves the following on the [sublevel α-PŁ bounded-variance class](../../LongTails/Setups/SublevelPLBoundedVariance.lean). For every finite dimension, every L-smooth, bounded-below f with f − inf f ≤ τ‖∇f‖^α on {f ≤ f(x₀)} (1 ≤ α < 2), and every IID, jointly measurable, unbiased gradient oracle with variance ≤ σ², the [gradient-only batched method](../../LongTails/Algorithms/SublevelWeightedGradient.lean) returns its last iterate with E[f(x_K) − inf f] ≤ ε. The method uses K = 1+⌈16T/(2−α)⌉ steps of length 1/L and batch sizes that decrease as √(K/j).

**Complexity** (L: smoothness; τ, α: PŁ constant and exponent; σ²: variance; ε: accuracy; valid for every ε > 0; Δ is not used):

$$N=O\!\left(1+\frac{L\tau^{2/\alpha}\varepsilon^{-(2-\alpha)/\alpha}}{2-\alpha}+\frac{L\sigma^2\tau^{4/\alpha}\varepsilon^{-(4-\alpha)/\alpha}}{(2-\alpha)^2}\right).$$

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fatkhullin–Etesami–He–Kiyavash, [NeurIPS 2022, arXiv:2210.01748](https://arxiv.org/abs/2210.01748), Cor. 1 (SGD). *Applies only to global α-PŁ or to trajectories assumed to stay in the PŁ region.* | O_α(Lτ^{2/α}ε^{−(2−α)/α} + Lσ²τ^{4/α}ε^{−(4−α)/α}) → N above | None: same order on the overlap. The constants are hidden on both sides. | Global α-PŁ, or assumed containment → α-PŁ only on {f ≤ f(x₀)}, with containment proved instead of assumed. Global PŁ plus global smoothness forces f to be constant for α < 2 ([2606.28278 Thm 2.1](https://arxiv.org/html/2606.28278v3)), so the prior theorem says nothing about nonconstant members of this class without the containment hypothesis. | Same: expected last iterate. | Uses batches, step 1/L, and known L, τ, α, σ, ε. Explicit factors (2−α)^{−1} and (2−α)^{−2}; large constant (110000). |
| Masiha–Kiyavash–Thiran, [arXiv:2606.28278 v3](https://arxiv.org/abs/2606.28278) (Aug 2026), Prop. 3.2 (GD). *Exact gradients only (σ = 0).* | O_α(Lτ^{2/α}ε^{−(2−α)/α}) → same at σ = 0 | None at σ = 0. | Deterministic gradients → bounded-variance stochastic gradients. | None. | None on the overlap. |
| Masiha et al., [AISTATS 2026, arXiv:2408.01839v2](https://arxiv.org/abs/2408.01839), Thm 3.2 (local SARAH) | O(ε^{−2/α}), with constants unstated and conditioned on staying in a neighborhood → N above | Not comparable: stronger oracle and a conditional criterion | Incomparable classes: PŁ on neighborhoods of minimizer components plus a batch-smooth oracle (shared noise across points) vs. the initial sublevel set with a plain variance oracle. | Conditional E[·∣stay] holding with prob. ≥ 1−δ → unconditional expectation | The prior rate is better in ε but requires mean-square-smooth, shared-sample oracle access. |
| Repository: [SublevelPLRobustBatchedGd](../../LongTails/Theorems/SublevelPLRobustBatchedGd.lean) (2026-11-13, unpublished) | O((1+K₀)ℓ[1+ℓ(σ²τ^{2/α}ε^{−2/α}/(2−α) + σ²/(Lε))]), where K₀ = Lτ^{2/α}ε^{−(2−α)/α}/(2−α) and ℓ = log(2+(1+K₀)Δ/ε) → N above | Removes the factor ℓ from the deterministic term and ℓ² from the noise term. The gain is a factor ≍ log(K₀Δ/ε) whenever Δ ≫ ε/K₀. | None (same spec). | Budget and tuning no longer depend on Δ. | The earlier proof's concentration argument may give a confidence statement. Its Lean theorem states only expectation, like this one. |

**Lower bound and reduction check.** [2606.28278 Thm 4.1](https://arxiv.org/html/2606.28278v3) gives Ω(Lτ^{2/α}ε^{−(2−α)/α} + Lσ²τ^{4/α}ε^{−(4−α)/α}) for ε ≤ c_α·min{Δ, L^{α/(2−α)}τ^{2/(2−α)}}, with dimension allowed to grow. In that range, N matches it up to factors depending only on α (c_α is unspecified, and the upper bound grows like (2−α)^{−2}). No standard reduction gives N. Plain SGD analyses assume containment. A union bound with Chebyshev or robust means needs P(escape) ≲ ε/Δ, which costs at least a factor log(Δ/ε). Uniform batches combined with the pathwise bound leave a harmonic log K. The new mechanism is the pathwise inequality "final gap ≤ deterministic target + O(Σe_j/j + Σe_j/L)", which charges an early exit to the 1/j-weighted error sum, together with √(K/j) batches that make both sums cost O(1/v) without increasing the total budget. Proof ancestry: the power-descent recursion of GD and of Fatkhullin et al. supplies the in-region analysis only.

**Search coverage.** On 2026-11-18 I searched arXiv, PMLR/AISTATS and NeurIPS for stochastic upper bounds on local or sublevel α-PŁ / KŁ classes. I read 2606.28278 v3 (Defs. 2.3, 2.7–2.8; Thms 2.1, 3.1, 4.1; Prop. 3.2; Rem. 4.2; §5) and 2408.01839 v2 (Thms 3.1–3.2). For Fatkhullin et al., I verified only the abstract rate and Assumption 3; Corollary 1 is known only from a summary, and I did not read 2606's Appendix D, so I could not confirm the IID fit claimed by the note. I found no later work. The companion note's citations and claims agree with what I read; its comparison with the repository result is accurate.

**Conclusion**

**Yes—this settles, up to α-dependent constants, a problem the strongest prior source explicitly left open.** Masiha–Kiyavash–Thiran (arXiv:2606.28278, Remark 4.2 and §5) prove the lower bound below for gradient-only methods on this exact class. They state that no self-contained upper bound was known: the matching SGD rate required assuming that the iterates stay in the sublevel set.

$$\Theta_\alpha\!\left(L\tau^{2/\alpha}\varepsilon^{-(2-\alpha)/\alpha}+L\sigma^2\tau^{4/\alpha}\varepsilon^{-(4-\alpha)/\alpha}\right)$$

This theorem attains the upper bound unconditionally, for the expected last iterate, without function values or a dependence on Δ. Relative to the only earlier unconditional bound (this repository's robust version from five days earlier), it removes log(K₀Δ/ε) and log²(K₀Δ/ε) factors.

The comparison establishes optimality for each fixed α < 2 and small ε. It does not establish uniformity as α → 2, where the upper bound grows like (2−α)^{−2} and c_α is unknown. At σ = 0 it only matches GD. Priority rests on a search that found no competing post-June-2026 result; this is not proof that none exists.

What can be claimed: the first literature-level, gradient-only, rate-optimal (for fixed α) expected-accuracy upper bound on the sublevel α-PŁ bounded-variance class, via a new error-weighted escape argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
