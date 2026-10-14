# Novelty assessment: KatyushaCompositeStronglyConvex

The [theorem](../../LongTails/Theorems/KatyushaCompositeStronglyConvex.lean) proves that, for F = (1/n)Σᵢ fᵢ + ψ on a real Hilbert space with convex differentiable L-smooth fᵢ, a real-valued μ-strongly convex ψ with an exact prox oracle, an existing minimizer x\*, and F(x₀)−F(x\*) ≤ Δ, the final weighted epoch snapshot of [Katyusha](../../LongTails/Algorithms/Katyusha.lean) satisfies E[F(x̃_S)] − F(x\*) ≤ ε ([setup](../../LongTails/Setups/CompositeFiniteSumStronglyConvex.lean)).

**Complexity** (component-gradient plus prox calls, deterministic for every seed). The budget is 108(n+⌈√(nL/μ)⌉)·⌈log₂⌈14Δ/ε⌉⌉₊, i.e.

  **O( (n + √(nL/μ)) · log(1 + Δ/ε) )**,

where n is the number of components, L the component smoothness, μ the strong-convexity modulus of ψ, Δ the initial gap, and ε the target expected gap. If 14Δ ≤ ε the budget is 0 and x₀ is returned. The algorithm is Allen-Zhu's Option I with m = 2n, τ₂ = ½, τ₁ = 1/(2r), r = max(1,⌈√(L/(2nμ))⌉), α = 1/(24nrμ) (smaller than Allen-Zhu's 1/(3τ₁L) by a constant factor), and 12r⌈log₂⌈14Δ/ε⌉⌉ epochs of 9n calls each. Updates and budget need n, L, μ, Δ and ε. No μ ≤ L restriction is imposed.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Allen-Zhu, Katyusha, [arXiv:1603.05953 v6 (2018-09-24; v1 2016-03-18)](https://arxiv.org/abs/1603.05953), STOC 2017 / [JMLR 18(221), 2018](https://jmlr.org/papers/v18/16-410.html); Algorithm 1, Thm 2.1 with σ = μ, m = 2n | Thm 2.1 gives E F(x̃_S)−F\* ≤ O((1+√(μ/(3Lm)))^{−Sm} or 1.5^{−S})·Δ, so O((n+√(nL/μ))·log(1+Δ/ε)) gradient+prox calls (9n per epoch) → O((n+√(nL/μ))·log(1+Δ/ε)) | None: same order in every regime | None on ℝᵈ (finite convex ψ is continuous, so it lies inside Allen-Zhu's lsc class). Hilbert space instead of ℝᵈ is a routine extension of dimension-free inequalities. | None: same weighted epoch snapshot, same known L, μ; no restarts in either | Narrower: ψ must be finite everywhere, so indicator constraints are excluded; worse constants (α, rounding, factor 108) |
| Lan–Li–Zhou, Varag, [NeurIPS 2019](https://proceedings.neurips.cc/paper/2019/hash/add5aebfcb33a2206b6497d53bc4f309-Abstract.html), [arXiv:1905.12412 v3](https://arxiv.org/abs/1905.12412), Thm 2; applicable via the reduction fᵢ+μ‖·‖²/2, ψ−μ‖·‖²/2 (L → L+μ, prox of ψ−μ‖·‖²/2 with step a < 1/μ is a rescaled prox of ψ; admissibility of Varag's prox steps not checked) | O(n log(D₀/ε)) if n ≥ 3(L+μ)/(4μ), else O(n log n + √(nL/μ) log(D₀/ε)), with D₀ = 2Δ + 3(L+μ)‖x₀−x\*‖²/2 ≤ (2+3(L+μ)/μ)Δ → O((n+√(nL/μ))·log(1+Δ/ε)) | Same order up to logs; the selected bound avoids Varag's log(L/μ) inside D₀ and n log n, but Katyusha already did | None | None: Varag also adapts to μ = 0, which this theorem does not cover | Selected result loses Varag's unified μ ≥ 0 coverage |

**Reduction check / proof ancestry.** The result is a direct specialization of Allen-Zhu's Theorem 2.1 (identical coupling x = τ₁z + ½x̃ + (½−τ₁)y, SVRG estimator, two prox steps, (1+αμ)ʲ-weighted snapshot, and potential telescoping of §2.1–2.2), and his initial potential is already expressed through F(x₀)−F(x\*). No new mechanism appears; Prox-SVRG (Xiao–Zhang 2014) and Nesterov's coupling are ancestry only. The repository's [SVRG](../../LongTails/Theorems/SvrgConvex.lean) and [accelerated finite-sum](../../LongTails/Theorems/AcceleratedFiniteSumConvex.lean) theorems treat smooth non-composite objectives and do not overlap.

**Search coverage** (2026-10-07 UTC). I read Katyusha v6's problem (1.1), Algorithm 1, Theorem 2.1 and footnote 9, and Varag's Theorem 2 via ar5iv (its rate table was partly garbled; regimes cross-checked against the abstract). I did not re-read L-Katyusha (Qian–Qu–Richtárik, JMLR 2021) or Lan–Zhou's RPDG; the older repository review lists the former at the same order. Hannah et al. (NeurIPS 2018) indicate the n·log(1/ε) term is improvable when κ = O(n) by non-span methods, so I make no optimality claim. The theorem entered the repository on 2026-09-23 (`b3d990f`), about ten years after Katyusha. No companion note exists.

## Conclusion

**No: this is a Lean re-proof of Katyusha's original strongly convex guarantee, with the same algorithm, rate, and output.**

The decisive baseline is Allen-Zhu's Katyusha (Theorem 2.1, STOC 2017/JMLR 2018). It assumes convex L-smooth components and a μ-strongly convex proximal term, returns the same weighted epoch snapshot, and bounds the expected gap by a multiple of F(x₀)−F(x\*).

| | gradient + prox calls for E F(x̃)−F\* ≤ ε |
|---|---|
| Katyusha (2016–2018) | O((n+√(nL/μ))·log(1+Δ/ε)) |
| This theorem | O((n+√(nL/μ))·log(1+Δ/ε)) |

The orders agree in every regime, including μ > L. On ℝᵈ the selected class is a subclass of Katyusha's, because ψ must be finite everywhere; the Hilbert-space setting is a routine extension, not a meaningful new problem class. The modified step α changes only constants.

What can be claimed is a machine-checked formalization of a known result, with an explicit deterministic call budget. It is not a new mathematical result.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
