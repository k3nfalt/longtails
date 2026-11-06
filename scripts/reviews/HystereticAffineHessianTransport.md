# Hysteretic Hessian transport under (L₀,L₁)-curvature and affine mixed-tail noise

The [theorem](../../LongTails/Theorems/HystereticAffineHessianTransport.lean) runs the [algorithm](../../LongTails/Algorithms/HystereticHessianTransport.lean) through `execute` and proves `∫‖∇f(X)‖ dP ≤ ε` for the returned point X. X is the point where an estimator-based pilot test stops the run; if the run aborts or exhausts its allocation, X falls back to x₀. The [setup](../../LongTails/Setups/GeneralizedAffineHessianVector.lean) is as follows. The dimension is any finite d. The objective f is C² and bounded below, with gap `f(x₀)−inf f ≤ Δ`. Its Hessian satisfies `‖∇²f‖ ≤ L₀+L₁‖∇f‖`. The gradient oracle is IID and unbiased, with central p-moment at most `σg^p+αg^p‖∇f‖^p`. The Hessian-vector-product (HVP) oracle is also IID and unbiased, with central q-moment at most `(σh^q+αh^q‖∇f‖^q)‖v‖^q`. Here `1<p,q≤2`, and all parameters are known to the algorithm.

**Complexity (from the Lean budget).** Let β = p/(p−1). Each oracle reply counts as one call. The total is

N = O( 2^{32β+16q/(q−1)} β · log(2+αg+σg/ε+(√(L₀Δ)+L₁Δ)/ε+ΔH/ε²) · [ (1+αg+σg/ε)^β + (ΔH/ε²)·( (1+αg+σg/ε)^{β/q} + (1+αg)²(1+αg+σg/ε)^{β−2} ) ] ),

where H = L₀+σh+(L₁+αh)(ε+σg/(1+αg)). Note that β−2 = (2−p)/(p−1). For fixed positive parameters, the ε-exponent is max{β, 2+β/q}, and the dependence on Δ is linear up to the logarithm.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| RanSOM-E, Chayti–Fakhouri, [arXiv:2602.06824v3](https://arxiv.org/abs/2602.06824v3) (v1 Feb 6, v3 Oct 9, 2026; preprint). Thm B.24, eqs. (52), (56), Remark B.26, branch q>p, Λh>0. Same oracle model. | My derivation from Remark B.26, using B^A ≳ αg and ᾱ_path ∝ L₁: leading term ≈ `ΔL₁σg^β/ε^{β+1} + (1+αg)^β[1+ΔL₁/ε+Δ(L₀+σh)/ε²]`. The transient terms were not expanded. → N above | For q>p, L₁>0, σg>0, and ε→0 with the other parameters fixed: ε^{−(β+1)} → ε^{−max{β,2+β/q}}·log(1/ε). Example: p=3/2, q=2 gives ε⁻⁴ → ε^{−3.5} log. For q≤p: none, the exponent is the same (RanSOM's interior branch). | None: same class. RanSOM additionally allows general norms and constraints. | Output changes from a uniformly sampled iterate to an estimator-stopped iterate, under the same E‖∇f‖ criterion. Both methods need the same known parameters. | Constant 2^{32β+16q/(q−1)}, which blows up as p→1 or q→1. One extra log. Extra term `Δ(L₀+σh)(1+αg)²S^{β−2}/ε²` (row 2). |
| RanSOM Cor. 4.8/B.27. Special-case baseline: L₁=αg=αh=0. | `(σg/ε)^β + Δ(L₀+σh)/ε²·[1+(σg/ε)^{β/q}]` → `log·[(1+σg/ε)^β + Δ(L₀+σh)/ε²((1+σg/ε)^{β/q}+(1+σg/ε)^{β−2})]` | Worse by the log factor. When β(1−1/q)>2 (for example p<4/3 with q=2), ΔL₀≥σg² and σg≥ε, it is polynomially worse by about min{ΔL₀/σg², (σg/ε)^{β−2−β/q}}. | Global smoothness with uniform noise → (L₀,L₁)-curvature with affine noise. | None | Same as row 1 |
| Repository [GuardedAffineHessianTransport](../../LongTails/Theorems/GuardedAffineHessianTransport.lean) (committed Oct 25, 2026; unpublished; [review](GuardedAffineHessianTransport.md)) | `ℓ^{β+1}[S_R^β + ΔH_R ε⁻² S_R^{β/q} G_R^β]`, where R₀=√(L₀Δ)+L₁Δ+ε, S_R=1+(σg+αgR₀)/ε, H_R=L₀+σh+(L₁+αh)R₀+ε/R₀, G_R=1+σg/R₀+αg → N | Sublevel scale R₀ → gradient scale ε+σg/(1+αg), and log^{β+1} → log. For Δ=ε^{−d} with L₁>0: exponent (1+d)·max{β,2+β/q} → d+max{β,2+β/q}. For σg=0, αg>0: now O((1+αg)^β[1+Δ(L₀+σh)/ε²+Δ(L₁+αh)/ε]), which matches RanSOM's degenerate case. At fixed Δ the ε-exponent is unchanged. | None | None | When L₁=α=0, neither bound dominates: Guarded has the factor G_R^β, the new bound has the S^{β−2} term. |

**Reduction check.** Two shortcuts do not reproduce N. Gradient minibatching in RanSOM cancels in total calls, because Aβ=1, but the path residual ᾱ_path ∝ L₁ is unbatched ((52) and the text after it). So the β+1 exponent persists. Sublevel localization, the Guarded approach, inflates the constants to R₀ and gives superlinear Δ. The mechanism that is actually new, as I read it from the code and the note, is the hysteretic fine/coarse switch: enter fine mode at pilot norm ≤U/4, exit at ≥3U. It is paired with a potential that charges every mode re-entry to objective decrease, which lets the batches be tuned at the gradient scale U. The algorithm code contains these thresholds; I did not re-derive the proof. Proof ancestry: uniform-segment HVP transport and clipping ([Fradin et al., AISTATS 2026](https://proceedings.mlr.press/v300/fradin26a.html); their theorem needs a Lipschitz Hessian and L-smoothness, so it is not a baseline here), medoid-of-means estimation, normalized generalized-smooth steps ([Reisizadeh et al.](https://arxiv.org/abs/2303.00883)), and the guarded high-probability-to-expectation conversion from the Guarded theorem.

**Search coverage (2026-11-04).** I read RanSOM v3 from the PDF (Thm B.24 through Cor B.27); v1 and v2 were not read. I also searched arXiv and the web for later work combining HVPs with generalized smoothness and heavy tails. [Liang–Luo, arXiv:2610.21692](https://arxiv.org/abs/2610.21692) (Oct 15, 2026) uses a first-order oracle with uniform noise. Its lower bound `Ω((1+(σ/ε)^β)(L₀Δ/ε²+L₁Δ/ε))` does not apply to HVP access. [Sadiev et al., 2510.10690](https://arxiv.org/abs/2510.10690) needs p=q and global smoothness. I found no HVP result under (L₀,L₁) with linear Δ and the mixed-tail exponent. The companion note's claims agree with the Lean budget and RanSOM's text. However, it does not mention the row-2 S^{β−2} loss. No build or axiom audit was run.

**Conclusion**

**Yes: when q>p and L₁>0, the proved complexity beats the closest published analysis, and it improves the Δ-dependence of the repository's earlier mixed-tail bound.** The strongest published baseline is RanSOM-E (Remark B.26). On this exact class, its proof gives exponent β+1 when q>p, because of an unbatched path term.

| Regime | RanSOM | Guarded (repo) | This result |
|---|---|---|---|
| fixed Δ, ε→0, q>p | ε^{−(β+1)} | ε^{−m}·log^{β+1} | ε^{−m}·log |
| Δ=ε^{−d}, L₁>0 | ε^{−(d+β+1)} | ε^{−(1+d)m} | ε^{−(d+m)}·log |

Here m = max{β, 2+β/q} < β+1 when q>p. For example, p=3/2, q=7/4, d=1 gives exponents 5, 52/7 and 33/7.

The result loses in some regimes. When q≤p it gives no exponent gain. In the global-smooth special case it carries an extra (σg/ε)^{β−2} term, which makes it polynomially worse than RanSOM's Corollary 4.8 when p<4/3, q=2 and ΔL₀≫σg². It also carries the constant 2^{32β+16q/(q−1)}.

That is what the comparison establishes. Priority rests on a search that found no competitor, which does not prove none exists, and the RanSOM gap is a limitation of RanSOM's proof, not a lower bound.

What can be claimed: the first bound I found that combines the mixed-tail exponent max{β,2+β/q} with linear Δ-dependence for HVP methods under (L₀,L₁)-curvature and affine heavy-tailed noise, obtained through a hysteretic re-entry charge.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
