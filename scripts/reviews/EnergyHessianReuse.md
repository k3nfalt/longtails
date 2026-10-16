# Novelty review: EnergyHessianReuse

[`result`](../../LongTails/Theorems/EnergyHessianReuse.lean) shows the following. Let `f` be C³ on a finite-dimensional space with `‖D³f(x)‖ ≤ L₀ + L₁‖∇f(x)‖` ([setup](../../LongTails/Setups/GradientDependentHessian.lean)), with exact gradient and Hessian oracles. Then a capped cubic-Newton method that reuses each Hessian for `m` steps ([algorithm](../../LongTails/Algorithms/EnergyHessianReuse.lean)) deterministically returns its best observed iterate with `‖∇f(x_out)‖ ≤ ε`. The method knows `L₀, L₁, Δ, G₀, ε, m`, uses no function values, and its guarantee is first-order stationarity only.

**Complexity.** Here `Δ ≥ f(x₀) − inf f`, `G₀ ≥ ‖∇f(x₀)‖`, `m ≥ 1` is the reuse period, `L₀ > 0`, and `L₁ ≥ 0`. The proved budget gives

```
N_grad = O( m + log(1 + L₁G₀/(mL₀)) + √m·Δ(√L₀ ε^{-3/2} + √L₁ ε^{-1}) )
N_hess = O( 1 + log(1 + L₁G₀/(mL₀)) + m^{-1/2}·Δ(√L₀ ε^{-3/2} + √L₁ ε^{-1}) )
```

The bounds below use the lazy-Hessian cost model in which one Hessian costs `m` gradients, for example `m = d`. In that model,

`W = N_grad + m·N_hess = O( m·[1 + log(1 + L₁G₀/(mL₀))] + √m·Δ(√L₀ ε^{-3/2} + √L₁ ε^{-1}) ).`

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fang–Marumo–Takeda, [arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741) (12 Jul 2026, preprint), Assumption 1, Thm 2, Cor 1. Fresh Hessian every iteration. **Direct competitor on the identical class.** | Weighted: `O(m·[1 + Δ(√L₀ε^{-3/2} + √L₁ε^{-1}) + log₊(L₁G₀/(L₀+L₁^{3/2}Δ)) + log₊((L₀+L₁^{3/2}Δ)/σ_init)])` → `W` | Factor `Θ(min{√m, Δ(√L₀ε^{-3/2}+√L₁ε^{-1})/(1+log(1+L₁G₀/(mL₀)))})`. That is `√m` when `Δ(√L₀ε^{-3/2}+√L₁ε^{-1}) ≥ √m(1+log(1+L₁G₀/(mL₀)))`. Otherwise it is the same order, up to the differing log initialization terms. | None (same class) | **Worse**: their updates are parameter-free, and they also give `(ε,δ)`-second-order stationarity. | Needs known `L₀, L₁, Δ, G₀`. Gradient calls are `√m` *larger* than FMT's iteration count, so this is a gain only when Hessians cost about `m` gradients. Constants are large (27000). FMT also counts function values in backtracking; this method uses none. |
| Doikov–Chayti–Jaggi, LazyCRN, [ICML 2023](https://proceedings.mlr.press/v202/doikov23a.html), Thm 3.1, Cor 3.6. **Only when `L₁ = 0`** (global Hessian Lipschitz constant `L₀`). | `O(m + √m·Δ√L₀ ε^{-3/2})` → same, because the log term vanishes at `L₁ = 0` | None: same order | Uniform Lipschitz Hessian → `‖D³f‖ ≤ L₀ + L₁‖∇f‖`. This adds, e.g., `cosh x + A cos x` (A>1): nonconvex, with unbounded third derivative. | None | LazyCRN also bounds the minimum Hessian eigenvalue along the iterates (Thm 3.1, eq. (15)). |
| Chen–Liu–Luo–Zhang, NALEN, [arXiv:2501.17488v3](https://arxiv.org/abs/2501.17488) / [COLT 2026](https://proceedings.mlr.press/v336/chen26a.html), Thm 4.1. **Only when `L₁ = 0`.** | `O(m + m^{1/3}Δ√L₀ ε^{-3/2})` → `O(m + m^{1/2}Δ√L₀ ε^{-3/2})` | **Worse** by `m^{1/6}` on the overlap | Same scope extension as in the previous row | None | NALEN's output is an averaged epoch point; on the overlap it is strictly stronger. |

**Example check.** For `f(x) = cosh x + A cos x` with `A > 1`, `|f'''| = |sinh x + A sin x| ≤ |f'| + 2A`, so the condition holds with `(L₀, L₁) = (2A, 1)`. `f''(0) = 1 − A < 0`, and `f ≥ 1 − A`. This example also violates the two-point condition `‖∇²f(y) − ∇²f(x)‖ ≤ (M₀ + M₁‖∇f(x)‖)‖y − x‖` used by Xie et al. (AAAI 2024) and by Semenov–Jaggi–Doikov ([ICLR 2026](https://mlanthology.org/iclr/2026/semenov2026iclr-gradientnormalized/), Example 5). Take `x = 0`: the left side grows like `e^{|y|}`. Semenov et al. handle inexact Hessians only when the error is a polynomial in `‖∇f‖` (their condition (12)). Stale-Hessian error grows with path length, so their Corollary 3 does not cover lazy reuse.

**Reduction check and proof ancestry.** I found no standard reduction. Running LazyCRN with a uniform constant fails because members of this class can lack any finite global or sublevel-set Hessian Lipschitz constant (FMT's scalar example `√(1+x²) − x cos x`). Using an epoch-maximum gradient leaves an unbounded quantity. The new mechanism is an energy-based damping term. It charges the transport error of the stale Hessian to the descent energy of each step, and fresh "preparatory" Hessian resets keep the bookkeeping valid. LazyCRN supplies the block structure and the `√m` accounting. FMT supplies the class and the Taylor-type local bounds. I did not verify the Lean proof beyond reading the statement and its dependencies, and I did not run a build.

**Search coverage.** The search ran on 2026-10-16 UTC and covered arXiv, ICML 2023, ICLR 2026, COLT 2026, and searches for lazy, stale or reused Hessians under generalized or relaxed smoothness. I found no lazy-Hessian guarantee beyond uniform Lipschitz-type assumptions. Other lazy-Hessian work, such as Alphonse–Dvurechensky–Sirotenko [arXiv:2602.08069](https://arxiv.org/abs/2602.08069), assumes Lipschitz gradients. I did not check the Filho–Gonçalves papers cited in the companion note. The companion note's claims (FMT rates, `√m` versus NALEN's `m^{1/3}`, the `m^{1/6}` loss) agree with the sources I checked. FMT predates the result by about three months; the result was committed on 2026-10-16 23:38 UTC (commit `d7c42d3`).

## Conclusion

**Yes: on the full gradient-dependent third-derivative class, the weighted gradient-plus-Hessian cost improves by a factor of up to `√m`.** The strongest baseline on this class is the fresh-Hessian cubic Newton analysis of Fang–Marumo–Takeda (2026). With Hessian cost `m` and `T = Δ(√L₀ε^{-3/2} + √L₁ε^{-1})`:

| | weighted cost |
|---|---|
| FMT | `O(m·T + m·log terms)` |
| this result | `O(√m·T + m·[1 + log(1 + L₁G₀/(mL₀))])` |

The gain is `√m` whenever `T ≥ √m(1 + log(1 + L₁G₀/(mL₀)))`. For example, with `m = 10⁴` and `L₀ = L₁ = Δ = 1`, `ε = 10⁻⁴`, the cost falls from about 10¹⁰ to 10⁸.

The price is real. The method needs `L₀, L₁, Δ, G₀`, while FMT's updates are parameter-free, and it proves only first-order stationarity, while FMT also gives second-order stationarity. It uses `√m` more gradient calls, so it gains nothing when Hessians are cheap. When `L₁ = 0` it only matches LazyCRN and is `m^{1/6}` worse than NALEN.

The comparison does prove the gain. Priority is less certain: the search found no earlier lazy-Hessian result for this class, but FMT is recent and concurrent work cannot be excluded. The contribution that can be claimed is an apparently new extension of Hessian reuse, with its `√m` weighted saving, to objectives whose curvature varies with the gradient norm. It uses a new energy-damping argument rather than a substitution into known theorems.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
