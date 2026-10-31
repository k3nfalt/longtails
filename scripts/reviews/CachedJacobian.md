# Novelty assessment: CachedJacobian

For a monotone operator `F` with an `L`-Lipschitz Jacobian on a compact convex set `X` of diameter at most `D`, the [theorem](../../LongTails/Theorems/CachedJacobian.lean) proves the following. The deterministic [cached-Jacobian anchored chord method](../../LongTails/Algorithms/CachedJacobian.lean) returns `u ∈ X` with `∃ n ∈ N_X(u), ‖F(u)+n‖ ≤ ε`, which is the tangent residual of the last inner iterate. This uses separately counted exact value calls `F(x)` and Jacobian calls `J(x)` ([setup](../../LongTails/Setups/LipschitzJacobianMonotone.lean)). Here `m ≥ 1` is the supplied price of one Jacobian call in units of value calls. The method needs `L, D, ε, m`; solving known affine VIs is free.

**Complexity.** Write `Q = LD²/ε`. The proved budget gives

- `G = O((1+√(mQ))·log(2+mQ))` value calls;
- `H = O((1+√(Q/m))·log(2+mQ))` Jacobian calls;
- weighted cost `W = G + mH = O((m + √(mQ))·log(2+mQ))`.

No dimension enters, and the bound does not depend on the size of `F` or `J`. Below, "weighted" charges an exact full-jet call (`F` and `J`) at `m+1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| H. Zhang et al., [arXiv:2609.13462v2](https://arxiv.org/abs/2609.13462) (v2 Oct 19 2026, preprint), Thm 3.3; also X. Zhang et al., [arXiv:2609.23557v1](https://arxiv.org/abs/2609.23557) (Sep 20 2026), Thm 3.1. Prior. | `O(Q^{2/5})` jet calls, up to `log^6` in 2609.13462 → weighted `(m+1)Q^{2/5}` → `(m+√(mQ))log(2+mQ)` | Gain when `m ≫ Q^{1/5}log²(mQ)`; the factor is ≈ `√m/(Q^{1/10}log)` for `m ≤ Q`. Example: `m=√Q` gives `Q^{0.9}` → `Q^{0.75}log Q`. **Worse** when `m ≲ Q^{1/5}`; at `m=1` it is `Q^{1/2}log` vs `Q^{2/5}`. | None (same class and criterion) | None (the same tangent residual; known `L,D`) | The fresh-jet method is optimal for jet calls (Ω(Q^{2/5}) lower bound in 2609.13462). This result loses `Q^{1/10}` when Jacobians are cheap. |
| L. Chen et al., Halpern-NPE, [arXiv:2608.08463v1](https://arxiv.org/abs/2608.08463) (Aug 9 2026), Thm 4.1 (p=2). Prior. | `Õ(√Q)` jet calls → weighted `Õ(m√Q)` → `(m+√(mQ))log` | ≈`√m` speedup up to logs when `m ≤ Q`; same order at `m=1` | None | That paper guarantees the normalized proximal residual `‖x−P_η x‖/η`; this result guarantees the tangent residual at the output. | Its output criterion differs, and I did not check the conversion cost. |
| Agafonov et al., VIJI, [NeurIPS 2024](https://proceedings.neurips.cc/paper_files/paper/2024/hash/d1ca7877cdaf3201ecfa95b1240f7942-Abstract.html), Thm 3.2, with `J(x₀)` reused (`δ=LD`). Prior; the reduction is mine. | gap `≤ εD` after `O(Q^{2/3}+Q)` value calls + 1 Jacobian → weighted `m+Q` → `(m+√(mQ))log` | ≈`√(Q/m)/log` when `m ≪ Q`; same order when `m ≳ Q` | None | Averaged gap → last-iterate tangent residual, which implies gap `≤ εD` | None beyond the logarithm |
| Chen–Liu–Zhang, LEN, [ICLR 2025](https://arxiv.org/abs/2410.09568) (arXiv v2), Thm 4.1. Prior; **convex–concave, unconstrained only**. | With lazy period `m` and `R≈D`: weighted `O(m+(mQ)^{2/3})` for restricted gap `εD` → `(m+√(mQ))log` | `(mQ)^{1/6}/log` on any heuristic overlap. The setups are not strictly nested, since LEN needs no compact `X` and this result needs no saddle structure. | Convex–concave saddle → general monotone VI on compact `X` | Ergodic restricted gap → tangent residual | LEN does not need compact `X` |

**Reductions and proof ancestry.** The two endpoints are easy to reconstruct:

- With one Jacobian (`m ≳ Q`), inexact-Jacobian or chord-prox schemes give `Õ(m+Q)`.
- At `m=1`, Halpern-NPE gives `Õ(√Q)`.

I found no substitution that yields the interpolation `m+√(mQ)`. Halpern anchoring ([Diakonikolas, COLT 2020](https://proceedings.mlr.press/v125/diakonikolas20a.html)), large-step inexact Halpern (2608.08463), and lazy derivative reuse (LEN; Doikov–Chayti–Jaggi, ICML 2023) are proof ancestry. The new step is the warm-start distance control across growing prox steps, together with the refresh-count ledger along the computed path.

The companion note proposes a stronger, unpublished baseline: compose the Q^{2/5} framework with LEN-restart inner solves, which it puts at `Õ(m + m^{4/5}Q^{2/5})`. I did **not** verify this. 2609.23557 mentions lazy Hessians only as future work in Sec. 6. If that composition holds, the gain regime shrinks to `m ≫ Q^{1/3}`, with `m ≪ Q` for the gain to be polynomial. Cutting-plane methods give dimension-dependent bounds and are not tabulated.

**Search coverage.** I searched on 2026-10-25 UTC: arXiv 2024–Oct 2026 (Halpern/high-order VI, lazy Hessians, inexact and quasi-Newton Jacobians, including [arXiv:2609.22481](https://arxiv.org/abs/2609.22481)), plus the ICLR/NeurIPS proceedings above. I found no mixed value/Jacobian residual bound. The result was introduced in commit `ba6da18` (2026-10-25 21:44 UTC), so every cited work predates it. The note's citations matched the sources I checked. Its proposed lazy-composition baseline is not stated in 2609.23557.

**Conclusion**

**Yes: when Jacobians are expensive enough relative to value calls, the proved total weighted cost beats every published guarantee I checked.**

The strongest prior method is the optimal fresh-jet method of H. Zhang et al. and X. Zhang et al. (2026), which uses `Q^{2/5}` full-jet calls. Charging `m+1` per jet call:

| | weighted cost |
|---|---|
| optimal fresh jets | `m·Q^{2/5}` |
| one reused Jacobian (Agafonov et al.) | `m + Q` |
| this result | `(m + √(mQ))·log(2+mQ)` |

The gain is polynomial for `Q^{1/5}polylog ≪ m ≪ Q`; for example, `m=√Q` gives `Q^{0.75}` instead of `Q^{0.9}`. The result is worse than the fresh-jet method when `m ≲ Q^{1/5}`, including the ordinary second-order case `m=1`. No matching lower bound for the weighted cost is known.

The main uncertainty is an unpublished baseline: lazy strongly monotone solvers composed with the optimal outer framework, which the note estimates at `m + m^{4/5}Q^{2/5}`. If that estimate is right, the advantage survives only for `m ≫ Q^{1/3}`. Priority also rests on searches in a field that is moving fast.

The contribution that can be claimed is a new dimension-free tradeoff between value and Jacobian calls for monotone-VI tangent residuals. In a regime where Jacobians are expensive, it beats the published fresh-jet and single-Jacobian guarantees.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
