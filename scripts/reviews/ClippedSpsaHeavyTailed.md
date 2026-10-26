# Novelty assessment: clipped SPSA under heavy-tailed noise

[`ClippedSpsaHeavyTailed.result`](../../LongTails/Theorems/ClippedSpsaHeavyTailed.lean) proves the following. Take any `f` on `ℝ^d` that is bounded below with `f(x0) − inf f ≤ Δ`. Its sample functions `F(·;ξ)` must be uniformly `L`-smooth, the sample gradients unbiased, and the central `p`-th moment bounded, `E‖G(x,ξ)−∇f(x)‖^p ≤ σ^p` with `1<p≤2`. The oracle returns two-point values with a shared IID sample ([setup](../../LongTails/Setups/HeavyTailedTwoPointZerothOrder.lean)). Under these conditions, scalar-clipped SPSA with Rademacher directions and a uniformly random stopping index ([algorithm](../../LongTails/Algorithms/ClippedSpsa.lean)) outputs `x_τ` with `E‖∇f(x_τ)‖ ≤ ε`.

**Complexity.** Let `q = p/(p−1)`. The method uses `⌈2²⁰·132^q·dLΔ/ε²·(1+(σ/ε)^q)⌉+1` two-point calls, that is,

  N = O(1 + 132^{p/(p−1)} · dLΔ/ε² · (1 + (σ/ε)^{p/(p−1)})).

Here `d` is the dimension, `L` the sample smoothness, `Δ` the initial gap, `σ` the `p`-th-moment noise scale and `ε` the accuracy. No logarithms appear, and the updates require `L, σ, p, ε, d` (and `Δ` for the horizon).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Omiya–Poirion–Takeda, RS-NSGD, [arXiv 2601.20399](https://arxiv.org/abs/2601.20399) (v1 28 Jan 2026, preprint), Thm 5.4 / C.3 with `r=1`, `𝕃=LI`. Prior. It is stated for directional-derivative calls; the two-point emulation below is my reduction. | `O(dLΔ/ε²·(1+(σ/ε)^q))` → `O(132^q·dLΔ/ε²·(1+(σ/ε)^q))` | None: same order (both carry `p`-dependent constants; ours is `132^q`, theirs is not made explicit) | None: the same unbiased, full-norm `p`-BCM noise. The emulation uses sample smoothness, which this setup also assumes | None: both need `L,Δ,σ,p,ε` and give `(1/T)ΣE‖∇f(x_k)‖ ≤ ε`, which equals the random-iterate criterion | RS-NSGD uses minibatches of about `(σ/ε)^q` calls along one shared Haar direction, then normalization. Ours is batch-free, uses single-sample scalar clipping, and has a worse explicit constant |
| El Bakkali et al., RSC-ZO, [arXiv 2605.17394v1](https://arxiv.org/abs/2605.17394) (17 May 2026), Thm 2.3, Remark 2.4. Prior | `Õ(LΔ(√(LΔ)+σ)^q d^{q/2} ε^{−(3p−2)/(p−1)})`, with high probability → `O(132^q·dLΔ/ε²·(1+(σ/ε)^q))` | Not comparable as stated. After converting theirs to expectation (≈`log(1/δ)` overhead): fixed `p<2` gains `d^{(2−p)/(2(p−1))}`; also drops `√(LΔ)` and logs (they require `ε² ≤ 32LΔ`) | Worse: their weak-`L_p` tail class contains our `p`-moment class | Worse: theirs bounds the trajectory average of `‖∇f‖²` with probability `1−δ`; ours is in expectation only | Their constants as `p↓1` are unchecked, so the gain is shown only for fixed `p` |

**Standard-reduction check.** RS-NSGD with `r=1` updates `x − η̄·P·sign(s)`, where `s` is a batch average of directional derivatives along one Haar direction `P` (`‖P‖=√d`). Each such derivative can be replaced by `(F(x+μP;ξ)−F(x−μP;ξ))/(2μ)`, which costs one two-point call and has error at most `Lμd/2`. A sign flip can only happen when `|P^T g| ≤ Lμd/2`. In that case the descent loss is at most `2(Lμd/2 + |P^T(g−∇f)|)`, and `E_P|P^T v| ≤ ‖v‖`. So the bias adds only `O(Lμd)` plus a noise term of the order the paper already has. Choosing `μ ≍ ε/(Ld)` keeps the order. The proof of Thm C.3 averages over `P` conditionally on the full minibatch gradient (`E[PPᵀg/‖Pᵀg‖] = τg/‖g‖`). That step is what makes the noise term dimension-free, and it is the same mechanism as this proof's "free directional moment". Proof ancestry: the selected proof's directional clipping-bias bound (`tail_cross_le`) and Rademacher fourth-moment bound are a different, batch-free route, but they produce no new rate. I sketched the reduction myself and did not formalize it. The `2σ/B̄^{(p−1)/p}` moment step is delegated to Hübler et al. and I did not re-read it.

**Search coverage.** I searched on 2026-10-26 (arXiv/HTML full texts). Sources covered: El Bakkali et al.; Liu–Luo [2605.24513](https://arxiv.org/abs/2605.24513) (nonsmooth Goldstein, not comparable); Liu [2512.23178](https://arxiv.org/abs/2512.23178) (first-order, convex); Omiya et al.; the Kornilov et al. convex works (cited in the companion note). I did not verify NeurIPS 2026 proceedings, the OMS Kornilov paper, or Ghadimi–Lan's exact corollary (I did not re-read the `p=2` special case). The [companion note](../../LongTails/Theorems/ClippedSpsaHeavyTailed.md) says that "all published heavy-tailed two-point analyses" carry `d^{q/2}`. It omits Omiya et al., whose in-expectation bound is already linear in `d`. The note's Lean description matches the formal statement.

**Conclusion**

**No, the complexity does not improve on the class: the bound is the same order as an earlier, easily adapted method.** The strongest baseline is RS-NSGD of Omiya–Poirion–Takeda (Jan 2026) with one random direction. It sees the same function-value information once its directional derivatives are replaced by two-point differences.

| | Two-point calls for `E‖∇f(output)‖ ≤ ε` |
|---|---|
| RS-NSGD (`r=1`) + finite differences | `O(dLΔ/ε²·(1+(σ/ε)^{p/(p−1)}))` |
| This result (clipped SPSA) | `O(132^{p/(p−1)}·dLΔ/ε²·(1+(σ/ε)^{p/(p−1)}))` |

Both use the same unbiased `p`-th-moment noise model, need the same parameters, and bound the same averaged / random-iterate criterion. The real gain of `d^{(2−p)/(2(p−1))}` holds only against El Bakkali et al.'s clipping analysis. That analysis gives a stronger output (high probability) under a broader tail assumption, so it is not a like-for-like competitor in expectation.

The remaining differences are that the method is batch-free and uses scalar clipping with Rademacher directions, and that its constant is worse. My reduction from Omiya et al. is a short, unformalized bias argument. If it failed, the assessment could move toward a method-specific novelty, but I see no obstacle. What can actually be claimed is a new batch-free clipped-SPSA analysis that matches an already available dimension-linear complexity.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
