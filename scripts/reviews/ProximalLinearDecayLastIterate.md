# Proximal SGD with linear decay under variance at a minimizer: novelty assessment

The [theorem](../../LongTails/Theorems/ProximalLinearDecayLastIterate.lean) proves a last-iterate guarantee for proximal SGD x_{k+1} = prox_{η_k ψ, Q}(x_k − η_k∇F_{ξ_k}(x_k)) with η_k = η(T−k)/T and η = R/(8LR + σ√T) ([algorithm](../../LongTails/Algorithms/ProximalLinearDecaySgd.lean)): **E Φ(x_T) − Φ(x\*) ≤ ε**. The [setup](../../LongTails/Setups/SampledCompositeSmoothConvex.lean) is Φ = E F_ξ + ψ on a closed convex set Q in a Hilbert space. Every F_ξ is convex with an L-Lipschitz gradient on all of E, and ψ is real-valued, lsc, and convex on Q. The prox is exact, and only the variance at one minimizer x\* is bounded.

**Proved complexity.** Here L is the per-sample smoothness constant, R ≥ ‖x₀ − x\*‖ (R > 0), Δ ≥ Φ(x₀) − Φ(x\*), σ² ≥ E‖∇F_ξ(x\*) − ∇f(x\*)‖², and ε is the expected gap. One gradient call plus one prox call per iteration gives

  2⌈72LR²/ε + 900σ²R²/ε² + 6Δ/ε⌉ = O(1 + LR²/ε + σ²R²/ε² + Δ/ε) calls, with no logarithm.

The steps need L, R, σ and T. `allowedAlgorithm` pins this exact method and its last-iterate output, and the convergence proof constructs it.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vaidyan–Friedlander–Alacaoglu, [arXiv:2602.05489](https://arxiv.org/abs/2602.05489) v1 (Feb 2026; ICML 2026), Thm 3.1. Same method family, τ = 1/(3L√T), last iterate. σ_\*² = E‖∇F_ξ(x\*)‖² = σ² + ‖∇f(x\*)‖² | O(1 + (LR²/ε)² + Δ/ε + (σ_\*²/(Lε))²log²(2+σ_\*²/(Lε))) → O(1 + LR²/ε + σ²R²/ε² + Δ/ε) | Never worse, up to constants: σ²R²/ε² ≤ ½[(LR²/ε)² + (σ²/(Lε))²]. Polynomially better when LR²/ε ≫ 1, e.g. σ = 0 gives (LR²/ε)² → LR²/ε. A retuned constant step in their Lemma 3.3 would plausibly leave only a log gap, but that bound is not stated in the paper | Second moment at x\* → variance at x\*. Example: deterministic ℓ₁-regularized f with ∇f(x\*) ≠ 0 has σ = 0 but σ_\* > 0 | None: both are last iterates with known L and T | ψ must be finite on a closed Q (excludes, e.g., −log barriers). Linear decay needs R and σ. No RIPM (incremental prox) analogue |
| Garrigos–Gower handbook, [arXiv:2301.11235](https://arxiv.org/abs/2301.11235), Thm 12.5. Prox SGD with averaged output, finite sum, σ = variance at x\* (Def. 8.22) | With an optimally tuned constant γ ≤ 1/(8L): O(1 + LR²/ε + Δ/ε + σ²R²/ε² + σ²Δ/(Lε²)) → O(1 + LR²/ε + σ²R²/ε² + Δ/ε) | Removes σ²Δ/(Lε²), which dominates when Δ ≫ LR² and σ² ≫ Lε. That term is probably an artifact of bounding the variance by the Φ-gap rather than D_f(x₀,x\*) ≤ LR²/2, but I did not check a source for this | Finite sum → general sample law (minor) | Weighted average → last iterate, at the same order | None beyond the first row |
| Liu–Zhou, [arXiv:2312.08531](https://arxiv.org/abs/2312.08531) v4 (ICLR 2024), Thm 3.4/C.3. The same linear-decay prox SGD, composite F = f + h, last iterate | O(1 + LR²/ε + σ_u²R²/ε²), with σ_u² a uniform variance bound → this result | None at equal noise. The Δ/ε term is extra here | Uniform variance → variance only at x\*. This covers, e.g., ℓ₁-regularized random-design least squares (σ_u = ∞). The classes are incomparable | None | Needs per-sample convexity and smoothness. Pays Δ/ε. No Bregman geometry or high-probability bound |
| Ilandarideva–Juditsky–Lan–Li, [arXiv:2307.01497](https://arxiv.org/abs/2307.01497) v3 (Math. Program. 2025), Cor. 1/(3.6), SAGD. **Restricted to ψ ≡ 0 on Q**. (SN) holds with constant 4L and noise term 2σ² by co-coercivity | O(1 + LR²/ε + σ²R²/ε²) → O(1 + LR²/ε + σ²R²/ε² + Δ/ε) | Worse on this overlap when Δ ≫ LR² + σ²R²/ε. Here Δ can be as large as ‖∇f(x\*)‖R + LR²/2 | Covers nonzero ψ; the prior result has none | None: SAGD's output x_k is also an iterate of the method | Plain prox SGD instead of an accelerated three-sequence method |

**Reduction check.** The proof combines a prox one-step inequality (essentially Vaidyan et al.'s Lemma 3.2, with variance replacing the second moment via the gap-transfer bound D_f ≤ Φ − Φ\*) with Zamani–Glineur reference points. The weight algebra is imported from the repository's [LinearDecaySgdLastIterate](../../LongTails/Theorems/LinearDecaySgdLastIterate.lean) (`ProximalLinearDecayWeights` imports `LinearDecaySgdWeights`). Its one genuinely new observation, that under linear decay ∏(1 + c_s/S_s) stays bounded by a constant, is unpublished. I did not verify any published composite version of a log-free σ\*-only method, such as heavy ball with iterate averaging (Sebbouh–Gower–Defazio, [arXiv:2006.07867](https://arxiv.org/abs/2006.07867), Thm G.1, which is unconstrained) or a composite AC-SA under (SN). Such a method would remove the remaining advantage.

**Search coverage.** I searched on 2026-10-16 UTC: arXiv, ICML/ICLR pages, forward citations of Vaidyan et al., Garrigos et al. and Attia et al., and the accelerated state-dependent-noise literature. I read the theorem statements for all table rows. Git introduces the result on 2026-10-16 (`490df2a`), so every row predates it and no subsequent work was found. The companion note cites its sources accurately. However, it omits Ilandarideva et al. and Sebbouh et al., which already beat or match this bound on the ψ ≡ 0 overlaps. It also understates that Vaidyan et al.'s published step leaves a polynomial gap, not just ln T.

## Conclusion

**The problem-class complexity does not improve; the gain is a log-free last-iterate bound for proximal SGD itself.**

The direct predecessor is Vaidyan–Friedlander–Alacaoglu (ICML 2026, Thm 3.1), the only checked last-iterate proximal SGD result under noise bounded at the minimizer:

| | calls |
|---|---|
| Vaidyan et al., as stated | O(1 + (LR²/ε)² + Δ/ε + (σ_\*²/(Lε))² log²) |
| this theorem | O(1 + LR²/ε + σ²R²/ε² + Δ/ε) |

The new bound is never worse. It is polynomially better as stated, and it replaces the second moment σ_\*² by the variance σ². Against a natural, unproved retuning of their step, the gain would shrink to a logarithm plus the σ_\* → σ refinement.

This is modest for two reasons. Averaged proximal SGD already attains this order. On the constraint-only overlap, Lan-type accelerated SA (Ilandarideva et al.) matches it without the Δ/ε term. The mechanism is a known prox one-step inequality plus the repository's linear-decay weight bound.

Whether a published composite heavy-ball or AC-SA analysis already gives a log-free last iterate under σ\* remains unchecked. If one exists, the verdict becomes NO IMPROVEMENT.

What can be claimed is a log-free last-iterate rate for proximal SGD under variance only at a minimizer. It closes the logarithmic gap that Vaidyan et al. leave open; I found no earlier such bound, but that does not establish priority. It is not a faster method for the problem class.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
