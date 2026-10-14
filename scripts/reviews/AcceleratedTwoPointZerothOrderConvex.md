# Accelerated two-point zeroth-order method for smooth convex functions with independent value noise

[`result`](../../LongTails/Theorems/AcceleratedTwoPointZerothOrderConvex.lean) gives a guarantee for a constant-step accelerated method that queries noisy function values. Its [setup](../../LongTails/Setups/ZerothOrderSmoothAndConvex.lean) is a convex, `L`-smooth `f` on a `d`-dimensional Euclidean space with a minimizer `x⋆` satisfying `‖x₀−x⋆‖≤R`. Each oracle call returns `f(x)+noise`, where each call uses a fresh i.i.d. seed, the noise has mean zero and variance at most `σ²`, and no further tail condition is imposed. The [algorithm](../../LongTails/Algorithms/AcceleratedTwoPointZerothOrderConvex.lean) forms a random-sphere central-difference estimate from two independent noisy values per iteration. Its last iterate `x_K` satisfies `E f(x_K) − f⋆ ≤ ε`. The tuning uses known `d, L, R, σ, ε`.

**Proved budget** (total value calls; `d≥1`, `L,ε>0`, `R,σ≥0`):

  N = 2·max{1, ⌈64 d√(LR²/ε) + 512 d²LR²σ/ε² + 256 d²LR²σ²/ε³ + 1⌉} = O(1 + d√(LR²/ε) + d²LR²σ/ε² + d²LR²σ²/ε³).

Within the repository, the coordinate-grid sibling [`AcceleratedZerothOrderConvex`](../../LongTails/Theorems/AcceleratedZerothOrderConvex.lean) has the same setup and a `d³LR²σ²/ε³` noise term. The two-point version saves a factor of `d` on that term. This comparison concerns novelty within the repository, not novelty in the literature.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Bach–Perchet, COLT 2016](https://arxiv.org/abs/1605.08165), Prop. 7 (unconstrained convex, `β=2`). It uses the same two-point scheme with independent noises, Eq. (5), and SGD. | As stated, the bound is untuned: `2(d²/N)^{1/3}(96L²R²+σ²/10+18)+2d²/N`. Retuning their SGD argument (my derivation) gives `O(dLR²/ε + d²LR²σ²/ε³ + d²LR²·min{σ/ε², dσ²/ε³})` → `O(d√(LR²/ε)+d²LR²σ/ε²+d²LR²σ²/ε³)` | If `σ≥ε/d` (and `LR²≥ε`): none, same order. If `σ<ε/d`: `dLR²/ε` → `d√(LR²/ε)+d²LR²σ/ε²`, a speedup of `min{√(LR²/ε), ε/(dσ)}`. | None (same class and oracle) | Output changes from the averaged iterate to the accelerated last iterate. This is immaterial for the expected-gap criterion. | None |
| [Nesterov–Spokoiny, FoCM 2017](https://doi.org/10.1007/s10208-015-9296-2), Thm 9, §6 (accelerated random search). Applies only when `σ=0`. | `O(d√(LR²/ε))` → same when `σ=0` | None: same order | Exact values → values with finite-variance noise | None | None on the overlap |
| [Lattimore–György, COLT 2023](https://arxiv.org/abs/2302.05371), Thm 1. Overlap only: `f` must also be globally `G`-Lipschitz, and the noise must be sub-Gaussian with ψ₂-norm `σ`. | Online-to-batch on the averaged played point gives `Õ(d³(σ+GR/d)²/ε² + d³(σ+GR/d)/ε)` → ours | Worse: for `σ≥GR/d`, theirs is smaller when `ε ≲ LR²/(d·polylog)`. Ours is smaller when `ε ≳ LR²/d`. | Globally Lipschitz `f` and sub-Gaussian noise → L-smooth `f` (quadratics allowed) and finite variance only. These classes are incomparable. | Their result is a high-probability regret bound, while ours bounds the expected gap. The conversion to expectation was not checked. | Their method has a worse `d`-exponent but a better `ε`-exponent. |
| *Subsequent:* [Loginov et al., arXiv:2610.05517v1](https://arxiv.org/abs/2610.05517) (4 Oct 2026), Thm 4(b) with `V=L`. Applies only to the subclass with an additional Hölder `β>2` condition. Uses projection onto the known ball, and allows broader systematic and adversarial noise. | `O(d²LR²σ²/ε³ + d(1+LR²/ε))` → ours | If `σ<ε/d`: the low-noise term improves from `dLR²/ε` to `d√(LR²/ε)+d²LR²σ/ε²`. Otherwise the order is the same. | Ours drops `β>2`. Theirs admits non-random error components. | None | None |

**Reduction check and proof ancestry.** The result combines Nesterov–Spokoiny accelerated random search with the classical smoothing bias–variance bound. The smoothing bound gives `E‖ĝ‖² ≲ d‖∇f‖² + d²(L²h² + σ²/h²)`, as in Bach–Perchet, Flaxman et al., and Saha–Tewari. The proof absorbs the noise variance through a variance-scaled constant step, using `M = 128Ld² + 8K·v/ε` [(`ZerothOrderConvergence`)](../../LongTails/Proofs/ZerothOrderConvergence.lean). I found no published theorem that states exactly this accelerated, unbatched bound for independent finite-variance noise. However, the mechanism is the standard one. [Gasnikov et al. 2024a](https://arxiv.org/abs/2211.13566), §4.4, sketches the analogous batched-accelerated one-point bound `T≃d²G²LR²/ε³` with `G² ≥ E|f(x,ξ)|²`. That sketch is not a theorem and is not directly comparable.

**Search coverage.** I searched on 2026-10-07 (UTC). I read the cited theorem statements directly from arXiv PDFs. I did not open the Fokkema et al. (2024) bandit bounds, Gasnikov et al. (2017, Automation & Remote Control), or [Lobanov–Gasnikov](https://arxiv.org/abs/2307.12725), which uses same-seed noise. Loginov et al. postdate the result's introduction (commit `b1c09a0`, 2026-09-22). Their Thm 5(a) is a Gaussian-noise lower bound for `d≥256`, and I did not check its proof. Letting the Hölder constant grow, it gives `Ω(σ²/ε²·min{d^{5/2}, d²LR²/ε})` for this class. So the `σ²/ε³` term is order-optimal when `LR²/ε ≤ √d`. No companion note exists.

## Conclusion

**The complexity improves only in a low-noise regime, and that gain is modest.** The strongest full-setup baseline is classical two-point smoothing with SGD (Bach–Perchet 2016, retuned):

| regime | baseline | this result |
|---|---|---|
| `σ ≥ ε/d` | `d²LR²(σ/ε² + σ²/ε³)` | same order |
| `σ < ε/d` | `dLR²/ε` | `d√(LR²/ε) + d²LR²σ/ε²` |

The leading noise term `d²LR²σ²/ε³` is unchanged. Acceleration helps only when the noise is so small that the problem is nearly noiseless. In that regime the result essentially recovers Nesterov–Spokoiny's `d√(LR²/ε)` and pays an extra `d²LR²σ/ε²` for the noise.

At high accuracy, the ε-exponent is not competitive on a large overlapping class. For globally Lipschitz `f` with sub-Gaussian noise, Lattimore–György's method needs `Õ(d³σ²/ε²)` calls, which beats this bound once `ε ≲ LR²/d`. Their method cannot handle quadratics or noise with only finite variance, while this result does.

The proof uses a known mechanism: accelerated random search with a variance-scaled step. I found no earlier paper that states this exact bound, so priority is plausible but not established. What can be claimed is a correct accelerated two-point analysis under finite-variance independent noise. It improves the low-noise term from `dLR²/ε` to `d√(LR²/ε)` when `σ < ε/d`, and it saves a factor of `d` over the repository's coordinate-grid version.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
