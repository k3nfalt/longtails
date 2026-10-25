# Guarded Hessian transport under (L₀,L₁)-curvature and affine mixed-tail noise

The [theorem](../../LongTails/Theorems/GuardedAffineHessianTransport.lean) builds an [algorithm](../../LongTails/Algorithms/ValidatedHessianTransport.lean) and proves `E‖∇f(X)‖ ≤ ε` for the returned point X. The [setup](../../LongTails/Setups/GeneralizedAffineHessianVector.lean) is: any finite dimension, f bounded below with `f(x₀)−inf f ≤ Δ`, `‖∇²f(x)‖ ≤ L₀+L₁‖∇f(x)‖`, and IID unbiased oracles for gradients and Hessian-vector products (HVPs). The gradient noise has central p-moment `≤ σg^p+αg^p‖∇f‖^p`, and the HVP noise has central q-moment `≤ (σh^q+αh^q‖∇f‖^q)‖v‖^q`, with `1<p,q≤2`.

**Complexity.** Each oracle reply counts as one call. Write `b = p/(p−1)` and `R = √(L₀Δ)+L₁Δ+ε`; R bounds the gradient norm on the initial sublevel set, up to ε. The proved budget, with constants depending on p, is

N = O_p( ℓ^{b+1} [ (1+(σg+αgR)/ε)^b + (Δ(L₀+σh+(L₁+αh)R)/ε² + Δ/(εR)) · (1+(σg+αgR)/ε)^{b/q} · (1+αg+σg/R)^b ] ),

where `ℓ = 1+log(2+R/ε+Δ(L₀+σh+(L₁+αh)R)/ε²+(σg+αgR)/ε)`. The exact Lean constant is `2^{100b+100}(1+b)`. For fixed positive parameters the ε-exponent is `max{b, 2+b/q}`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| RanSOM-E, Chayti–Fakhouri, [arXiv:2602.06824v3](https://arxiv.org/html/2602.06824v3) (v1 Feb 6, v3 Oct 9, 2026; preprint). Theorem B.24 and Remark B.26. Same oracle model (Assumption B.4); case L₁+αh>0. | For q>p, inverting Remark B.26's `T^{−(p−1)/(2p−1)}` gives a leading term of about `Δ(L₁+αh)σg^b/ε^{b+1}`; this is my derivation, and the lower-order terms are not expanded. This result: N above, of order `ε^{−max{b,2+b/q}}` | For q>p, σg>0 and ε→0 with the other parameters fixed, the exponent drops from b+1 to max{b, 2+b/q}. Example: p=3/2, q=2 gives ε⁻⁴ → ε^{−7/2}·ℓ⁴. For q≤p: none, same exponent. | None: same instance class (RanSOM also allows general norms) | None. RanSOM outputs a uniformly sampled iterate; both bound E‖∇f(output)‖ | If σg=0 and αg>0, RanSOM's degenerate case (β=½, batch B ≥ (64αg)^b) costs about `(1+αg)^b[Δ(L₀+σh)/ε²+Δ(L₁+αh)/ε]`. Ours keeps `(αgR/ε)^{b/q}`, so it is worse. Ours also adds the factors ℓ^{b+1}, (1+σg/R)^b and 2^{100b} |
| RanSOM, Corollary 4.8 / B.27 (L₁=αg=αh=0). This is a special-case baseline. | `(σg/ε)^b + Δ(L₀+σh)/ε²·[1+(σg/ε)^{b/q}]` → our N with L₁=α=0 | Worse by a factor `ℓ^{b+1}(1+σg/(√(L₀Δ)+ε))^b` | Global-smooth, uniform noise → (L₀,L₁), affine noise | None | None beyond the extra factors |
| Fradin et al., [AISTATS 2026](https://proceedings.mlr.press/v300/fradin26a.html), [arXiv:2512.18713v2](https://arxiv.org/html/2512.18713v2), Theorem 5.1 (NSGD-Hess). Requires an L-smooth objective, an L₂-Lipschitz Hessian and operator-norm Hessian moments. | `σhΔ/ε²(σg/ε)^{b/q}+(σg/ε)^b+√L₂·Δ·σg^{1/4}ε^{−7/4}(…)` | Not comparable outside the overlap. On the overlap it matches the leading terms, with extra logs | Drops the Lipschitz-Hessian requirement and allows L₁ and affine noise | None | Same as row 2 |

**Reduction check.** On the sublevel set `{f ≤ f(x₀)}`, (L₀,L₁)-curvature gives `‖∇f‖ ≲ R`. The affine noise then becomes uniform, `σg+αgR` and `σh+αhR`, and the local smoothness constant is `L₀+L₁R`. Substituting these into RanSOM's Corollary 4.8 reproduces exactly the structure of N. The new step is making this localization rigorous in expectation under heavy-tailed noise. Stochastic iterates can leave the set, and the gradient can grow exponentially in the horizon. The proof uses a fresh robust norm guard at every step, which keeps the second moment uniformly below `O(R²)`, together with restart/validation selection. The guard and moment bound are checked here only as they are described in the companion note; the proof was not re-derived. Proof ancestry: uniform-segment HVP transport (Fradin et al., Appendix E), restart/validation conversion (Chezhegov et al., ICLR 2026, §4.2), and the localization idea. None of these gives the bound directly.

**Search coverage.** The search was run on 2026-10-25. It covered arXiv (RanSOM v1–v3; Fradin v2; Sadiev et al. 2510.10690, which needs p=q and global smoothness; 2610.21692, which is first-order only; 2502.07923, sign methods with first-order (L₀,L₁)) and AISTATS/ICLR proceedings. No paper found gives mixed-tail exponents under (L₀,L₁) with HVPs. RanSOM v1/v2 were not read; only v3 was. No build or axiom audit was run. The companion note's claims agree with the Lean statement and the RanSOM text, but it omits the σg=0, αg>0 regime where this result loses.

**Conclusion**

**Yes: for q>p, the proved complexity has a better ε-exponent than the closest prior analysis on the same problem class.** The baseline is RanSOM-E (arXiv:2602.06824v3, Remark B.26). For (L₀,L₁)-curvature with L₁+αh>0 and q>p, its proof gives only exponent b+1, because of a step/momentum coupling.

| Regime (fixed parameters, σg>0, ε→0) | RanSOM | This result |
|---|---|---|
| q>p | ε^{−(b+1)} | ε^{−max{b,2+b/q}}·log^{b+1} |
| q≤p, or L₁=α=0 | ε^{−(2+b/q)} | same exponent, more logs and σg/R factors |

The gain is polynomial, for example ε⁻⁴ → ε^{−3.5} at p=3/2, q=2, so it survives the logarithms for small ε. The result is worse when σg=0 and αg>0, and it is worse by logarithmic and polynomial σg factors in the global-smooth case, where RanSOM's Corollary 4.8 already reaches the same exponent. The rate itself equals the global-smooth rate after substituting sublevel-set constants. The actual content is proving that this localization survives heavy-tailed noise in expectation.

The comparison shows a gain over RanSOM's *proved* bound, which RanSOM itself describes as a limitation of its proof, not a lower bound. Priority depends on a search that found no competitor, which does not prove none exists. The contribution that can be claimed is the first verified mixed-tail exponent `max{b,2+b/q}` for HVP methods under (L₀,L₁)-curvature with affine noise when q>p, obtained by a guarded-localization argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
