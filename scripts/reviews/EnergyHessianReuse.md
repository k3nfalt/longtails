# Novelty review: Hessian reuse with energy control under gradient-dependent third derivatives

[`result`](../../LongTails/Theorems/EnergyHessianReuse.lean) proves the following. Take a C³ nonconvex `f` on any finite-dimensional Euclidean space with `‖D³f(x)‖ ≤ L₀ + L₁‖∇f(x)‖`, `f(x₀) − inf f ≤ Δ` and `‖∇f(x₀)‖ ≤ G₀`. With exact gradient and Hessian oracles, the [algorithm](../../LongTails/Algorithms/EnergyHessianReuse.lean) returns the queried point with the smallest observed gradient, and this point satisfies `‖∇f(x_out)‖ ≤ ε` deterministically ([setup](../../LongTails/Setups/GradientDependentHessian.lean)). The algorithm is a capped cubic-Newton method that reuses each Hessian for `m` steps. It needs to know `L₀, L₁, Δ, G₀, ε, m`.

**Complexity.** Charge one unit per gradient and `m` units per Hessian. The proved budgets `N_g + m·N_H` then give

`O( Δ√m (√L₀ ε^{-3/2} + √L₁ ε^{-1}) + m·(1 + log(1 + L₁G₀/(mL₀))) )`, valid for `L₀, Δ, ε > 0`, `L₁, G₀ ≥ 0`, `m ≥ 1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fang–Marumo–Takeda, [arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741) (12 Jul 2026, preprint), Thm. 2 / Cor. 1. Same class: parameter-free CRN with a fresh Hessian at every iteration. | `m·O(Δ(√L₀ε^{-3/2} + √L₁ε^{-1}) + log(L₁G₀/(L₀+L₁^{3/2}Δ)) + 1)` (setting δ = ∞; backtracking trials add more calls) → `O(Δ√m(√L₀ε^{-3/2} + √L₁ε^{-1}) + m(1 + log(1 + L₁G₀/(mL₀))))` | Factor √m when `Δ(√L₀ε^{-3/2} + √L₁ε^{-1}) ≥ √m·(1 + log(1 + L₁G₀/(mL₀)))`. Same order when `m = O(1)`. | None: identical class | None | Loses parameter-freeness: Fang needs no `L₀, L₁, Δ`, while this result needs `L₀, L₁, Δ, G₀, ε`. Loses Fang's (ε,δ)-second-order stationarity; this is first-order only. |
| Doikov–Chayti–Jaggi, [ICML 2023](https://proceedings.mlr.press/v202/doikov23a.html), Thm. 3.1 / Cor. 3.6 (LazyCRN). **Special case only**: uniform Hessian-Lipschitz `L`. | On the overlap `L₁ = 0`, `L = L₀`: `O(√m L₀^{1/2}Δε^{-3/2} + m)` → same (the burn-in vanishes) | None: same order | Uniform Lipschitz Hessian → pointwise `L₀ + L₁‖∇f‖` third-derivative bound. This covers objectives with unbounded curvature growth, such as `√(1+x²) − x cos x`. | None. Both use the best gradient among the iterates. | Needs the known parameters listed above. Doikov's result also gives second-order information (Eq. 19). |
| Chen–Liu–Luo–Zhang, NALEN, [arXiv:2501.17488v3](https://arxiv.org/abs/2501.17488), [COLT 2026](https://proceedings.mlr.press/v336/chen26a.html), Thm. 4.1. **Special case only**: uniform `H`. | `L₁ = 0`: `O(m + m^{1/3}√L₀Δε^{-3/2})` → `O(m + m^{1/2}√L₀Δε^{-3/2})`. If `H` also holds with `L₁ > 0`: `O(m + m^{1/3}√HΔε^{-3/2})` → this bound | Worse by `m^{1/6}` at `L₁ = 0`. Better on the intersection only when `H ≳ m^{1/3}(L₀ + L₁ε)`. | Same as the row above | None | NALEN's online-to-nonconvex analysis needs a global `H`, and none exists in this class. |

**Reduction check.** Reducing to LazyCRN or NALEN through a Hessian-Lipschitz constant on the sublevel set fails. In Fang's scalar example `f = √(1+x²) − x cos x`, `f' ≈ x sin x` and `f''' ≈ x sin x` track each other, but near `x = 2πk` the sublevel set has width about `√(c/x)`, where `|f'''| ≈ √(cx)` is unbounded. Two other routes only lose: running Fang's method with fresh Hessians costs a factor `m`, and plugging an epoch-maximum gradient into Doikov's coefficient `M ∝ mL` leaves an unknown quantity. The mechanism I could not find in prior work is the energy-dependent damping `δ = 4L₀P + 100L₁E_history`, which charges gradient×step-length products in the stale-Hessian error to descent energy, together with a fresh preparatory step at each reset. Proof ancestry: Doikov et al. supply the lazy cubic step, and Fang et al. supply the class and its local Taylor control. I did not rule out that a careful direct combination of the two is routine.

**Search coverage.** On 2026-10-17 UTC I searched arXiv, PMLR/ICML/COLT, ICLR 2026 and Optimization Online for lazy or reused Hessians under generalized or relaxed Hessian smoothness. I found none that covers this class. Checked non-competitors: Semenov–Jaggi–Doikov, [ICLR 2026](https://arxiv.org/abs/2506.13710), which treats approximate Hessians, not lazy reuse, and gives no explicit nonconvex (M₀,M₁) rate; Gratton–Jerad–Toint, which uses fresh Hessians and assumes weak convexity; and Filho–Gonçalves (Optimization Online, May 2026), which reuses Hessians under uniform Lipschitzness. I did not verify the assumptions of arXiv:2608.22129 from its abstract. The result entered the repository on 2026-10-17 (commit 46b2790), after Fang et al. The companion note's comparisons agree with what I checked.

**Conclusion**

**Yes: for this curvature class, Hessian reuse provably cuts the weighted oracle cost by about √m compared with the only existing guarantee.** The strongest baseline for the full class is Fang–Marumo–Takeda's cubic Newton, which needs a fresh Hessian at every step:

| | weighted cost (Hessian = m gradients) |
|---|---|
| Fang et al. | `m·Δ(√L₀ε^{-3/2} + √L₁ε^{-1})` + logs |
| This result | `√m·Δ(√L₀ε^{-3/2} + √L₁ε^{-1}) + m(1 + log(1 + L₁G₀/(mL₀)))` |

The gain holds once the accuracy term exceeds `√m` times the additive term. For example, with `m = d = 10⁴`, `L₀ = Δ = 1`, `L₁G₀ ≤ 1` and `ε ≤ 10⁻²`, the bound is about 90× smaller (ratio ≈ 1.1·10⁷ / 1.2·10⁵).

The gain has costs. The algorithm needs `L₀, L₁, Δ, G₀, ε`, which Fang's method does not, and it certifies only first-order stationarity, not Fang's second-order guarantee. At `L₁ = 0` it only matches LazyCRN and is `m^{1/6}` worse than NALEN, so it gives no gain under a uniform Lipschitz Hessian.

The comparison proves the gain over the checked baselines. Priority rests on a search that found no lazy-Hessian analysis for this class, but that search cannot exclude that a direct combination of the Doikov and Fang analyses is routine. The claimable contribution is the first Hessian-reuse guarantee, with a √m weighted saving, under gradient-dependent third-derivative bounds.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
