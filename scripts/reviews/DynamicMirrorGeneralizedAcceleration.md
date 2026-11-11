# DynamicMirrorGeneralizedAcceleration: novelty assessment

The [theorem](../../LongTails/Theorems/DynamicMirrorGeneralizedAcceleration.lean) covers convex, differentiable `f` on a finite-dimensional normed space with **any** norm, where the gradient satisfies `‖g(x)−g(y)‖_* ≤ (L₀+L₁M)‖x−y‖` whenever `‖g‖_* ≤ M` on the segment `[x,y]`. The ([setup](../../LongTails/Setups/MirrorGeneralizedSmooth.lean)) supplies a mirror `ψ` with `B_ψ(u,z) ≥ ½‖u−z‖²` and an exact oracle for `argmin_u ⟨v,u⟩ + B_ψ(u,z)`. Under these assumptions, a deterministic accelerated mirror method ([algorithm](../../LongTails/Algorithms/MirrorGeneralizedAcceleration.lean)) returns a last iterate with `f(x_K) − f* ≤ ε`. Each iteration uses 2 gradient calls and 1 prox call, and the method chooses its step from the current `‖g(x)‖_*`.

**Proved complexity.** Here `D ≥ B_ψ(x*,x₀)` bounds the Bregman distance to the minimizer and `Δ ≥ f(x₀)−f*` bounds the initial gap. The method knows `L₀, L₁, D, Δ`. The budget is `3⌈24576(1+√(2L₀D/ε)+(1+2L₁√D)log(2+2Δ/ε))⌉`, which gives

  `O( 1 + √(L₀D/ε) + (1+L₁√D)·log(2+Δ/ε) )` oracle calls (gradient + prox).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Yu–Jiang–Tao–Wan–Zhang, accelerated mirror descent ([arXiv:2502.00753v4](https://arxiv.org/abs/2502.00753), 30 May 2026; ICML 2026), Thm 3.7 with eq. (7); **prior, direct competitor** | Affine link, `B = D`, gap `Δ`: `G ≍ L₁Δ+√(L₀Δ)`, `L = ℓ(4G) ≍ L₀+L₁²Δ`, `τ ≍ √D·L/G`, `η ≍ min{1,1/τ}`, so `1+√((L₀+L₁²Δ)D/ε · max{1, √D(L₀+L₁²Δ)/(L₁Δ+√(L₀Δ))})` → `1+√(L₀D/ε)+(1+L₁√D)log(2+Δ/ε)` | If `L₁√D ≥ 1` and `L₁²Δ ≥ L₀`: `(L₁√D)^{3/2}√(Δ/ε)` → at most `L₁√D(√(Δ/ε)+log(2+Δ/ε))`. That is a gain of at least `≈√(L₁√D)` when `Δ ≥ ε`. Example: `L₀=D=Δ=1`, `L₁=q`, `ε→0` gives `q^{3/2}ε^{-1/2}` → `ε^{-1/2}+q log(1/ε)`. At `L₁=0`, Yu's certificate loses a factor `(L₀D/Δ)^{1/4}` that this bound removes. For `Δ ≥ ε`, this bound is never worse than Yu's up to constants, except for the additive `log(2+Δ/ε)` | None. Yu covers a broader class: any sub-quadratic link `ℓ` and an open domain `X ⊆ E`, whereas this result is affine-link and unconstrained. This setup allows any `x₀`, but on `X = E` Bregman recentering makes Yu's `x₀ = argmin ψ` without loss of generality | None: both need the smoothness constants, `D`, and the gap; both give a last-iterate gap | 3 calls per iteration instead of 2. Global unconstrained domain only. Yu's bound is a sufficient certificate, not a lower bound on the method |
| Tyurin, AGD ([arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884), 21 May 2026; ICML 2026), Thm 4.3; **prior, Euclidean special case only** (`‖·‖₂`, `ψ=½‖·‖²`, `R²=2D`) | `√(L₀R²/ε)+L₁R·log⁺min{L₁²Δ/L₀, Δ/ε}+log⁺(Δ/(L₀R²))` → `√(L₀R²/ε)+(1+L₁R)log(2+Δ/ε)` | None: same order. Tyurin's logarithm saturates at `log(L₁²Δ/L₀)`, so Tyurin is slightly better when `ε < L₀/L₁²` | Euclidean `‖·‖₂` → any norm with a strongly convex mirror | None | Needs a prox oracle. Tyurin also covers a general link `ℓ` |
| Rudomanov–Fomin–Gasnikov–Stonyakin, "Descending Everest" ([arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461), 5 Nov 2026, preprint), Thm 3.7; **prior, Euclidean special case only** | `√(L₀R²/ε)+(1+L₁R)log(2+L₁R)` → `√(L₀R²/ε)+(1+L₁R)log(2+Δ/ε)` | **Worse** on the Euclidean overlap whenever `log(Δ/ε) ≫ log(2+L₁R)`. The repository's [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean) has an `(L₁R)^{2/3}log(Δ/ε)` transient, which is also better | Euclidean → any norm | Everest needs no gap bound `Δ`; this result does | Euclidean only. Its Thm 4.10 lower bound shows that the `L₁R` transient is near-optimal there |

**Reductions and proof ancestry.** Two standard reductions do not give this bound. Converting a non-Euclidean instance to `‖·‖₂` and applying Tyurin or Everest multiplies the constants by dimension factors; this geometric loss is classical, and I did not verify the companion note's Hadamard example. Freezing the curvature on a gradient-bounded region is Yu's analysis itself, and it is what produces the `q^{3/2}` factor. The mechanism has two familiar ingredients. The first is the self-bounding inequality `‖g‖_*² ≲ (L₀+L₁‖g‖_*)(f−f*)`, an analogue of Yu's Lemma 3.4. The second is a similar-triangles/Bregman energy step, in which mixing weights are chosen from the current gradient and strong convexity of `ψ` keeps the query points inside the local smoothness ball. The result has the same shape as Tyurin's Euclidean bound. I could not demonstrate a routine transfer, because Tyurin's proof is written in `ℝᵈ` with the Euclidean inner product.

**Search coverage (2026-11-11 UTC).** I searched arXiv and the web for non-Euclidean, mirror, and Bregman acceleration under (L₀,L₁)/ℓ-smoothness, and read the following theorem statements: Yu (Thm 3.5/3.7, Def 2.1, Lemma 3.4), Tyurin (Thm 4.3), and Everest (Thm 3.7). I checked the following but found no comparable end-to-end bound:
- Xu–Chen [2606.02787](https://arxiv.org/abs/2606.02787) Thm 4.4: dual relative smoothness, a boundedness assumption, and an unspecified constant `C`.
- Yamashita et al. [2609.34773](https://arxiv.org/abs/2609.34773): relative smoothness.
- Chen et al. [2601.19038](https://arxiv.org/abs/2601.19038): a GCS-condition analysis that cites Yu as the generalized-smooth result.
- Pethick et al. [2506.01913](https://arxiv.org/abs/2506.01913): non-Euclidean (L₀,L₁), but nonconvex and not accelerated.

Git dates the theorem to commit `93edfb9` (2026-11-11), after all of these papers. The companion note's citations exist and agree with what I read. I did not check its claimed factor-4 slip in Yu's eq. (97) or its fixed-metric separation example.

## Conclusion

**Yes: for non-Euclidean geometry, the proved complexity is polynomially better than the only published accelerated mirror guarantee under (L₀,L₁)-smoothness.**

That guarantee is Yu et al.'s Theorem 3.7 (ICML 2026). It freezes curvature at the worst gradient level, and in the high-curvature regime `L₁√D ≥ 1`, `L₁²Δ ≥ L₀` the two bounds compare as

| | calls |
|---|---|
| Yu et al., Thm 3.7 | `(L₁√D)^{3/2}·√(Δ/ε)` |
| this result | `√(L₀D/ε) + (1+L₁√D)·log(2+Δ/ε)` |

For `Δ ≥ ε` this is at least a `√(L₁√D)` speedup, and it reaches `(L₁√D)^{3/2}` when `Δ = L₀D` and `ε` is small enough that `√(L₀D/ε)` dominates. On the common affine-link, unconstrained class the result is never worse than Yu's bound up to constants and an additive logarithm. Yu, however, covers general links and open domains.

The gain does not extend to the Euclidean special case. There the bound only matches Tyurin's and is worse than Everest's gap-free `(1+L₁R)log(2+L₁R)` transient. In effect, the result brings the Euclidean dynamic-curvature rate shape to arbitrary norms. These are comparisons of proved upper bounds, and priority rests on a targeted search of a fast-moving 2025–26 literature.

What can be claimed is an explicit accelerated bound (the first one my search found) with additive `L₁√D·log` dependence for (L₀,L₁)-smooth convex problems in arbitrary norm/mirror geometry, under exact gradient and prox oracles.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
