# Novelty assessment: GeneralizedAcceleratedConvex

The [theorem](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean) ([setup](../../LongTails/Setups/GeneralizedSmoothAndConvex.lean), [algorithm](../../LongTails/Algorithms/DampedGeneralizedAccelerated.lean)) applies to convex `f` on a real Hilbert space with differentiable gradient, `‖∇²f(x)‖ ≤ L₀ + L₁‖∇f(x)‖` everywhere, and a minimizer `x*` with `‖x₀−x*‖ ≤ R` and `f(x₀)−f* ≤ Δ`. For such `f`, a damped Monteiro–Svaiter/similar-triangles method that knows `L₀, L₁, R, Δ` uses two exact gradients per iteration, with no function values and no line search. Its deterministic last iterate satisfies `f(x_K) − f* ≤ ε`.

**Proved complexity.** Here `L₀ > 0, L₁ ≥ 0` are the smoothness constants, `R` is the initial distance, and `Δ` is the initial gap. The budget `2⌈4096(1 + √(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉·log(4+4Δ/ε))⌉` (zero calls if `Δ ≤ ε`) gives

  `O( 1 + √(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉·log(4 + 4Δ/ε) )` gradient calls.

The ceiling is 0 when `L₁ = 0` (plain smooth acceleration) and at least 1 for any `L₁ > 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vankov et al., AGMsDR ([arXiv:2410.10800](https://arxiv.org/abs/2410.10800) v3, 2025-03-07; ICLR 2025, venue not rechecked), Thm 6.2, Alg. 1, App. E.2; **prior** | `(ν+1)·[√(48L₀R²/ε) + ⌈3(2L₁R)^{2/3}⌉⌈log₂(2Δ/ε)⌉]`. Here `ν` is the oracle cost of an exact segment minimization and is left unbounded → `√(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉log(4+4Δ/ε)` | Not comparable as a call count, because `ν` has no bound in `L₀, L₁, R, Δ, ε`. The iteration counts are the same order | None (same Hessian-form class; Hilbert space vs ℝᵈ) | None: both give a last-iterate gap with known `L₀, L₁` | **Oracle gain:** gradient + function values + exact 1-D search → two gradients per iteration. Loss: this method needs `R` and `Δ` for initialization (`A₀ = R²/(2Δ)`) |
| Tyurin, AGD ([arXiv:2508.06884](https://arxiv.org/abs/2508.06884) v1 2025-08-09, v2 2026-05-21), Thm 4.3; **prior** | With `R̄ = R`, `Γ₀ = 2Δ/R²`: `√(L₀R²/ε) + L₁R·log⁺min{2L₁²Δ/L₀, 2Δ/ε} + log⁺(2Δ/(L₀R²))` → `√(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉log(4+4Δ/ε)` | If `ε ≥ L₀/L₁²` (so the minimum is `2Δ/ε`) and `Δ ≥ 2ε`, the gain factor is about `min{(L₁R)^{1/3}, L₁R·log(Δ/ε)/√(L₀R²/ε)}`. Example: `Δ = L₀R²`, `ε = L₀R²/(L₁R)^{4/3}` gives `(L₁R)·log(L₁R) → (L₁R)^{2/3}·log(L₁R)` | None | None: both need `L₀, L₁, R, Δ` and both give a last-iterate gap | **Worse** when `ε < L₀/L₁²`: Tyurin's logarithm saturates at `log(L₁²Δ/L₀)`, but this one keeps growing like `log(Δ/ε)`. The loss shows only if `(L₁R)^{2/3}log(Δ/ε) > √(L₀R²/ε)`, which requires `log(Δ/ε) > (L₁R)^{1/3}`. Tyurin also covers general ℓ and open domains |
| Borodich–Kovalev, Accelerated GRAAL ([arXiv:2507.09823](https://arxiv.org/abs/2507.09823) v2, 2025-08-29), Cor. 3; **prior** | With `η₀ = e^{−L₁R}/L₀`: `1 + √(L₀R²/ε) + (L₁R)³ + (1+L₁²R²)L₁R` → `√(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉log(4+4Δ/ε)` | Start-up `(L₁R)³ → (L₁R)^{2/3}log(4+4Δ/ε)`. This matters when `ε ≫ L₀R²/(L₁R)⁶`. Example: `Δ = L₀R²`, `ε = L₀R²/(L₁R)⁴` gives `(L₁R)³ → (L₁R)²` | None | **Worse:** GRAAL needs only `η₀ ≤ e^{−L₁R}/L₀` (any small value works), while this method needs `L₀, L₁, R, Δ`. Both give a last-iterate gap | GRAAL's curvature estimate `Λ` uses Bregman divergences, so it needs function values; this method needs gradients only. This method's start-up depends on `ε` |

For Tyurin, `Γ₀` must bound `2(f(x₀)−f*)/‖x₀−x*‖²`. Adding a flat dummy coordinate puts a minimizer at distance exactly `R` without changing the iterates, so `Γ₀ = 2Δ/R²` is admissible. According to the comparison tables in Tyurin and GRAAL, Gorbunov et al. ([2409.14989](https://arxiv.org/abs/2409.14989)) and Li et al. (NeurIPS 2023) have factors exponential or multiplicative in `L₁R`, so they are dominated. I did not re-derive those bounds.

**Reduction check and ancestry.** Freezing the curvature on a ball around `x*` gives an `e^{Θ(L₁R)}` factor in the leading term. Running AGMsDR with a bisection would add a per-iteration search cost that has no checked bound. So I found no routine reduction to this bound. The algorithm descends from the damped MS scheme of Carmon et al. (NeurIPS 2022). The new step, which I checked in [`GeneralizedMixedRate.lean`](../../LongTails/Proofs/GeneralizedMixedRate.lean) and [`GeneralizedConvergence.lean`](../../LongTails/Proofs/GeneralizedConvergence.lean), is a charging argument. It splits the rejected-guess steps into low-curvature steps, which cost `√(L₀A)`, and high-curvature steps, which cost `(L₁R)^{2/3}·log`. This is what recovers Vankov's rate without the segment search.

**Search coverage (2026-10-07 UTC).** I searched arXiv and the web for accelerated (L₀,L₁)/ℓ-smooth methods and read the theorem statements of Vankov (Thm 6.2, App. E.2), Tyurin (Thm 4.3 and its discussion of Vankov) and GRAAL (Cor. 3, Alg. 1). Git dates the theorem to `9600c80` (2026-09-25), after all three papers. Lobanov ([2608.04884](https://arxiv.org/abs/2608.04884)) uses a different `(H₀,H₁)` class, a level-set radius, restarts and a 1-D relaxation, so it is not a baseline. I found no later paper that supersedes the bound. I did not verify the ICLR/ICML venue claims. No companion note exists. An older local review (`scripts/reviews/`) agrees with these findings but served only as a lead. In the repository, the later [GeneralizedSelfNormalizedConvex](../../LongTails/Theorems/GeneralizedSelfNormalizedConvex.lean) (2026-09-28) refines the logarithm for the same algorithm.

## Conclusion

**Yes: it gets Vankov et al.'s accelerated (L₀,L₁) rate with a bounded number of gradient calls, and in a moderate-accuracy regime that beats the best line-search-free bounds.**

| method | oracle per iteration | total calls |
|---|---|---|
| Vankov (Thm 6.2) | values + gradient + exact 1-D search | `ν·[√(L₀R²/ε) + (L₁R)^{2/3}log(Δ/ε)]`, with `ν` unbounded |
| Tyurin (Thm 4.3) | gradients | `√(L₀R²/ε) + L₁R·log min{L₁²Δ/L₀, Δ/ε}` |
| this result | 2 gradients | `√(L₀R²/ε) + ⌈(L₁R)^{2/3}⌉log(Δ/ε)` |

Against Tyurin, the strongest gradient-only baseline with known parameters, the gain is up to `(L₁R)^{1/3}` when `ε ≥ L₀/L₁²` and `√(L₀R²/ε) ≲ (L₁R)^{2/3}log(Δ/ε)`. For very small `ε`, Tyurin's saturating logarithm can be better. Against GRAAL, the start-up drops from `(L₁R)³` to `(L₁R)^{2/3}log`, but GRAAL is nearly parameter-free.

These are comparisons of upper bounds; no lower bound shows that the baselines are slower. Priority rests on a limited search that found no earlier bounded-cost implementation of Vankov's rate.

What can be claimed is a gradient-only accelerated method with known parameters for convex (L₀,L₁)-smooth problems. It matches AGMsDR's rate without AGMsDR's exact line search, which makes the bound polynomially better than Tyurin's in the stated moderate-accuracy regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
