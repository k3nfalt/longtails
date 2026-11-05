# Novelty assessment: StochasticCompositeGeneralizedAccelerated

The [theorem](../../LongTails/Theorems/StochasticCompositeGeneralizedAccelerated.lean) proves a high-probability bound for minimizing `F = f + ψ` over a convex set `Q`. Here `f` is convex and globally symmetric `(L₀,L₁)`-smooth, `ψ` and `Q` are accessed through an exact prox oracle, and the stochastic gradients are IID, unbiased, and have a finite central `α`-moment, `1<α≤2` ([setup](../../LongTails/Setups/StochasticCompositeGeneralizedSmooth.lean)). Under these assumptions the accelerated clipped method ([algorithm](../../LongTails/Algorithms/StochasticCompositeGeneralizedAccelerated.lean)) returns its last point `x_out`, and `P{x_out ∉ Q or F(x_out) − F* > ε} ≤ δ`.

**Complexity.** The bound counts gradient samples and prox calls together. Here `R ≥ ‖x₀−x⋆‖`, `Δ ≥ F(x₀)−F*`, `G ≥ ‖∇f(x⋆)‖` (where `G` is used only in the analysis), and `σ` is the moment scale. The public budget simplifies, with no change in order, to

`O( 2^{128α/(α−1)} [1 + √((L₀+L₁G)R²/ε) + (1+L₁R)·log(2+(1+L₁R)√(Δ/(L₀R²))) + (σR/ε)^{α/(α−1)}] · log^{(2α−1)/(α−1)}((8+L₁R+(L₀+L₁G+L₁σ)R²/ε+Δ/(L₀R²)+σR/ε)/δ) )`.

The simplification works because the budget's `192L₁σ` term inside the square root is absorbed: `√(192·L₁R·σR/ε) ≤ 7(L₁R+σR/ε)`. The constant and the logarithm's exponent blow up as `α↓1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gorbunov et al., [ICML 2024, arXiv:2310.01860v2](https://arxiv.org/pdf/2310.01860v2), Thm 2.7 (n=1). This is the direct composite competitor: it assumes `L`-smoothness on the ball `B(x⋆,5√2R)`. | The ball's gradients can be as large as `(G+L₀/L₁)e^{L₁r}`, so the ball constant is `L ≤ (L₀+L₁G)e^{5√2L₁R}`. Previous: `Õ(e^{3.6L₁R}√((L₀+L₁G)R²/ε) + √(RG/ε) + (σR/ε)^{α/(α−1)})` → this result: the displayed bound. | Exponential → polynomial dependence on `L₁R`. The gain holds when `e^{3.6L₁R}√((L₀+L₁G)R²/ε)` exceeds `(1+L₁R)log(·) + (σR/ε)^{α/(α−1)}` by more than the extra polylog. Example: `σ=0` and `L₁R = log(LR²/ε)` gives a polynomial bound here versus a super-polynomial one there. At `L₁=0` the standalone `√(RG/ε)` term is dropped. | The ball-local fixed-`L` composite class → globally `(L₀,L₁)`-smooth composite instances such as exponential risks plus `ℓ₁`/trust-region terms, with no exponential cost. | None. Both methods know the parameters, and both bounds are for a single output point. | Smoothness and the moment bound must hold on all of `E`, not just on a ball. The logarithm power is higher and the constants depend on `α`. The prior bound is an upper bound, not a lower bound on that method. |
| El Bakkali El Kadi–Gorbunov, [arXiv:2610.23301v2](https://arxiv.org/html/2610.23301v2) (preprint, v1 16 Oct 2026, so prior), Thm 2 (one-phase Clip-SSTM). **Applies only when unconstrained:** `ψ=0`, `Q=ℝᵈ`, `G=0`. | Previous: `O(ℓ[√(L₀R²/ε) + (σR/ε)^{α/(α−1)} + (1+L₁R)log(ℓ(1+L₁R)√(Δ/(L₀R²)))])` with `ℓ = log(K/δ)`. Their proof bound is `ℓ²L₀R²/K² + σRℓ^{(α−1)/α}/K^{(α−1)/α}`, which I inverted by hand. → this result: the same terms times `log^{(2α−1)/(α−1)}`. | **Worse** on the overlap, by a factor of about `log^{α/(α−1)}(·/δ)` and an `α`-dependent constant. | Unconstrained → composite/constrained with `∇f(x⋆)≠0`. The two classes are nested. | None. | No gain on the shared smooth unconstrained class. |
| Repository: [FiniteVarianceGeneralizedAcceleratedConvex](../../LongTails/Theorems/FiniteVarianceGeneralizedAcceleratedConvex.lean). **Applies only when unconstrained and `α=2`.** | Previous: `O([1+√(L₀R²/ε)+log(Δ/ε)+(L₁R·log(Δ/ε))^{2/3}+σ²R²log(1/δ)/ε²]·log(·/δ))` → this result: a `(1+L₁R)log(·)` transient times `log³`. | **Worse** when `L₁R ≫ 1`: the transient is `(L₁R)^{1}` instead of `(L₁R)^{2/3}`, and the logarithm power is larger. | Same scope extension as the row above. | None. | None beyond those columns. |

**Reduction check.** Tilting by `∇f(x⋆)` cancels inside the prox. But no checked reduction maps this composite problem onto the unconstrained theorem of arXiv:2610.23301, and the only checked composite route, Theorem 2.7, goes through a ball constant that is exponential in `L₁R`. The specific new step is closing the induction on local curvature and energy along a noisy *proximal* trajectory while the statistical cost stays additive. I did not check whether this is routine. **Proof ancestry:** clipped-SSTM ([Gorbunov et al., NeurIPS 2020](https://proceedings.nips.cc/paper_files/paper/2020/file/abd1c782880cc59759f4112fda0b8f98-Paper.pdf)), shifts and composite clipping (arXiv:2310.01860), and the weight schedule with an `(L₀,L₁)` transient (arXiv:2610.23301). [Nguyen–Ene–Nguyen, arXiv:2304.01119](https://arxiv.org/abs/2304.01119), Thm 4.1, accelerates constrained mirror descent only under `∇f(x⋆)=0` with `L`-smoothness. [Chezhegov et al., arXiv:2505.20817v3](https://arxiv.org/html/2505.20817v3), Thms 1–2, cover unconstrained, non-accelerated Clip-SGD; their conclusion lists accelerated methods as future work.

**Search coverage.** I searched on 3 Nov 2026 (UTC): arXiv, ICML/NeurIPS proceedings, and forward searches combining "composite/proximal", "(L₀,L₁)" and "heavy-tailed", plus the repository. I found no composite or constrained heavy-tailed `(L₀,L₁)` acceleration result. I read [He–Li–Lu, arXiv:2510.11676](https://arxiv.org/abs/2510.11676) (hybrid Hölder smoothness, no `L₁`) and [Ji–Lan, arXiv:2604.06525](https://arxiv.org/abs/2604.06525) (bounded variance) only as abstracts. I read the appendix of arXiv:2610.23301 only partially. The companion note's citations agree with what I checked. It does not mention that the result is worse than arXiv:2610.23301 in logarithmic factors on the unconstrained overlap. The theorem was added in commit `e6b6aa83` on 3 Nov 2026.

## Conclusion

**Yes, but as a scope extension: the result brings polynomial `L₁R` dependence to composite and constrained problems, not a faster rate.**

The strongest composite baseline is Gorbunov et al., ICML 2024, Theorem 2.7. Applied to this class, it needs a smoothness constant on a ball, and that constant grows like `e^{O(L₁R)}`:

| | Leading optimization cost |
|---|---|
| ICML 2024 via ball reduction | `e^{3.6L₁R}·√((L₀+L₁G)R²/ε)` |
| This result | `√((L₀+L₁G)R²/ε) + (1+L₁R)·log(·)` |

Both bounds share the additive statistical term `(σR/ε)^{α/(α−1)}`. So the gain survives whenever the exponential curvature cost dominates that term and the polylog factors, for example with small noise and `L₁R` above about `log(R²L₀/ε)`.

On smooth unconstrained problems the result gains nothing. It matches El Bakkali El Kadi–Gorbunov (October 2026) only up to an extra factor of roughly `log^{α/(α−1)}(1/δ)`, and it has a worse `L₁R` transient than the repository's `α=2` result. My search found no earlier composite heavy-tailed `(L₀,L₁)`-smooth acceleration. However, the field is moving week by week, and I did not check whether the extension is routine.

The contribution that can be claimed is extending heavy-tailed generalized-smooth acceleration to exact-prox composite and constrained problems, removing the exponential `L₁R` cost of the known composite theorem, without improving any rate on the unconstrained overlap.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
