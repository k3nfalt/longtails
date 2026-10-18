# Novelty review: CompositeLazyCubicAcceleration

[`result`](../../LongTails/Theorems/CompositeLazyCubicAcceleration.lean) constructs [`CompositeLazyCubic.algorithm`](../../LongTails/Algorithms/CompositeLazyCubic.lean) for [`CompositeLipschitzHessian.spec`](../../LongTails/Setups/CompositeLipschitzHessian.lean). It proves that, for every admissible instance and every oracle seed, the last damped outer point is feasible and satisfies `F(x) − F(x⋆) ≤ ε`, where `F = f + ψ`. Here `f` is convex, C² and H-Hessian-Lipschitz on the whole space; `ψ` is convex on a set `C` and has a closed epigraph; the space is finite-dimensional and of arbitrary dimension. The available oracles are exact gradients (ch. 0), exact Hessians (ch. 1), and an exact composite cubic/metric-prox model solve (ch. 2).

**Complexity.** Write T = HR³/ε, where R ≥ ‖x₀−x⋆‖, and let m ≥ 1 be the Hessian-cost weight, which the algorithm is told. Expanding `budget` gives
- gradients and model solves: O(log⁴(2+m) · log(2+T/m³) · (m + m^{1/7}T^{2/7})) each;
- Hessians: O(log(2+m) · log(2+T/m³) · (1 + T^{2/7}/m^{6/7})).

The weighted cost G + M + m·𝓗 is therefore **O(log⁴(2+m) · log(2+HR³/(m³ε)) · (m + m^{1/7}(HR³/ε)²ᐟ⁷))**. The bound needs neither an initial gap nor a level-set or subgradient bound.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Monteiro–Svaiter A-NPE, [SIOPT 2013 (preprint rev. 2012)](https://optimization-online.org/wp-content/uploads/2011/05/3030.pdf), Thm 6.4 + Thm 7.15 (composite g+h, C.1–C.3). Direct competitor; prior. | O((HR³/ε)^{2/7}·ℓ) Newton black-box calls, where ℓ = 1+\|log ε\|+\|log H\|+\|log R\|. Each call costs one Hessian, one gradient and one metric-prox solve, so the weighted cost is O(m(HR³/ε)^{2/7}ℓ) → O(log⁴(2+m)log(2+T/m³)(m + m^{1/7}T^{2/7})). | Polynomial cost ratio ≈ T^{-2/7} + m^{-6/7}, up to logs. Example: with m = T^{1/3} the cost falls from T^{13/21} to T^{1/3}. A gain requires m^{6/7} and T^{2/7} both ≫ log⁴(2+m)log(2+T)/ℓ. None at m = 1. | None: MS already covers proper closed convex h with no bounded-subgradient condition, and needs smoothness only on a set containing dom ∂h. | None: both have last-iterate-type gap outputs and need H, R, ε. | Global ambient Hessian-Lipschitz `f` (stronger than MS). Up to ≈ m^{1/7} + m/T^{2/7} times more model solves. Also needs cubic (σ>0) composite solves. Gains only if a gradient or model solve is ≈ 1/m the cost of a Hessian. |
| Zhang–Chen–Liu–Zhang, [arXiv:2610.03222v1](https://arxiv.org/abs/2610.03222) (2 Oct 2026; unreviewed), Thm 4.1. **Special case ψ = 0, C = ℝᵈ only**; prior by 16 days. | O((m + m^{1/7}T^{2/7})·log^{11/3}m) → O(log⁴(2+m)log(2+T/m³)(m + m^{1/7}T^{2/7})). On the overlap, model replies depend only on the query, so they are internal computation. | Worse by a factor of log^{1/3}(2+m)·log(2+T/m³). | Smooth unconstrained objective → `f + ψ` with closed convex `ψ` (constraints, ℓ₁/TV terms, boundary optima). The classes are nested. | None. | Needs the exact composite model oracle. Has larger logs and huge explicit constants. |
| Chen–Liu–Luo–Zhang, [COLT 2026 / arXiv:2501.17488v3](https://arxiv.org/html/2501.17488v3), Thm 5.1. **Smooth unconstrained only.** | O((m + m^{13/21}T^{2/7})ln m) → as above. | On the overlap: m^{13/21} → m^{1/7}, but this is dominated by the row above. | Same extension as the row above. | None. | Same as the row above. |

**Reduction check and proof ancestry.** The smooth results do not cover ψ ≠ 0, and the composite non-accelerated lazy tools do not give the rate:
- [Doikov–Chayti–Jaggi, ICML 2023](https://arxiv.org/abs/2212.00781), App. F gives composite lazy cubic steps, but only subgradient-norm lemmas and no functional-gap rate.
- [Chayti et al., TMLR 2024](https://arxiv.org/abs/2302.11962) give a lazy convex rate with exponent ε^{-1/2} and a level-set diameter.
- [Alphonse et al., arXiv:2602.08069](https://arxiv.org/abs/2602.08069) prove a composite semismooth 1/k rate for an incomparable class.

Applying MS line-search acceleration with a lazy inner solver is the evident route, so the mechanism is not conceptually new. The composite obstacles named in the note are plausible: extrapolating ψ outside its domain, and keeping a reused Hessian valid along the search. I checked that they are not resolved in the cited smooth papers. I did not verify the proofs in `CompositeLazyCubicConvergence` line by line, and I ran no build or axiom audit. Transferring ZCLZ's lower bound (Thm 3.1, deterministic, high-dimensional) to this oracle model is only an inference.

**Search coverage.** Searched on 18 Oct 2026 (UTC): arXiv and the proceedings of ICML 2023, COLT 2026 and TMLR 2024 for lazy-Hessian, composite cubic-Newton and Monteiro–Svaiter work. I read the theorem statements of MS 2013, ZCLZ, CLLZ and DCJ App. F. Alphonse et al. and LEN (ICLR 2025, a minimax ε^{-2/3} rate) were checked only at abstract level. The companion note's citations and claims match the Lean statement. The note itself says the improvement is relative to MS and that it loses logs relative to ZCLZ; I found no discrepancy. The result was introduced in commit 261ff09 (18 Oct 2026), after ZCLZ.

## Conclusion

**Yes: for composite objectives, it lowers the proved cost of Hessian-weighted second-order acceleration, though only by porting a two-week-old smooth result.**

Classical composite acceleration (Monteiro–Svaiter 2013) needs a fresh Hessian at each step. The new theorem reuses Hessians and reaches the near-optimal lazy rate that Zhang–Chen–Liu–Zhang proved only for smooth unconstrained problems:

| | weighted cost (Hessian = m gradients) |
|---|---|
| Monteiro–Svaiter, composite | m·(HR³/ε)^{2/7} · log |
| this result, composite | (m + m^{1/7}(HR³/ε)^{2/7}) · log⁴(2+m)·log(2+HR³/(m³ε)) |

The gain is polynomial when both m and HR³/ε are large; for example, m = (HR³/ε)^{1/3} saves a factor of (HR³/ε)^{2/7}. At m = 1 there is no gain. The result also uses more exact composite model solves than Monteiro–Svaiter. On the smooth special case it is logarithmically slower than ZCLZ, and it assumes global Hessian-Lipschitz smoothness.

The comparison establishes the gain over the composite baseline I checked. I found no earlier composite lazy-accelerated bound, but this extension of the October preprint is a natural one, and I have not checked its proof in detail. What can be claimed is the first proved (m + m^{1/7}ε^{-2/7}) lazy-Hessian guarantee for general closed convex composite problems, up to logarithms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
