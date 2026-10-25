# Gradient-only ε^{-5/3} stationarity under Lipschitz third derivatives

[`result`](../../LongTails/Theorems/GradientOnlyThirdOrderAcceleration.lean) shows the following. Let `f` be a `C³` function on any finite-dimensional Euclidean space, with an `L₁`-Lipschitz gradient, an `L₃`-Lipschitz third derivative and `f(x₀) − inf f ≤ Δ` ([setup](../../LongTails/Setups/GradientOnlyThirdOrderNonconvex.lean)). Then a deterministic method that queries **only exact gradients** ([algorithm](../../LongTails/Algorithms/GradientOnlyGuarded.lean)) returns `x̂` with `‖∇f(x̂)‖ ≤ ε` for every run. It uses at most the stated budget of gradient calls, and its tuning requires `L₁, L₃, Δ, ε`.

**Complexity.** This bound comes from the Lean budget (epochs × calls per epoch), with universal constants dropped. It holds for all positive `L₁, L₃, Δ, ε`:

```
O( (1 + Δ L₃^{1/3} ε^{-4/3}) · (1 + √(1 + L₁/(L₃^{1/3} ε^{2/3})) · log(1 + (L₁ + L₃^{1/3} ε^{2/3}) Δ / ε²)) )
```

When `ε^{2/3} ≤ min(Δ L₃^{1/3}, L₁/L₃^{1/3})` it reduces to `O(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} log(1 + L₁Δ/ε²))`. The constants are large: about `2·10⁵` versus 20 in CDHS17.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon–Duchi–Hinder–Sidford, ["Convex until proven guilty"](https://arxiv.org/abs/1705.02766), ICML 2017, Thm 2. Uses **value + gradient** oracle. | `20 Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} log(500 L₁Δ/ε²)` gradient calls plus the same order of value calls (their Remark 2). Valid for `ε^{2/3} ≤ min(ΔL₃^{1/3}, L₁/(8L₃^{1/3}))`. → `O(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} log(1+L₁Δ/ε²))` gradient calls | None: same order, with constants about `10⁴` times larger. Outside CDHS's ε-range, gradient descent already gives `O(L₁Δ/ε²)`, so removing that range restriction gains nothing. | None: same function class | None: both are deterministic, both need `L₁, L₃, ε`, and both certify a stopped point | **Advantage: value + gradient → gradient only.** No function values are used anywhere. |
| Li–Lin, [Restarted nonconvex AGD](https://arxiv.org/abs/2201.11411), JMLR 24 (2023), Thm 1. Gradient-only, needs Lipschitz Hessian `ρ`. On this class, `ρ ≤ √(2L₁L₃)` by the Landau–Kolmogorov inequality applied to `t ↦ ∇²f(x+tu)[u,u]`. | `O(Δ L₁^{5/8} L₃^{1/8} ε^{-7/4})` → `O(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} log(1+L₁Δ/ε²))` | The ε exponent improves from 7/4 to 5/3. The speedup factor is `(L₁/(L₃^{1/3}ε^{2/3}))^{1/8} / log(1+L₁Δ/ε²)`, a real gain only when `L₁/(L₃^{1/3}ε^{2/3}) ≫ log⁸(1+L₁Δ/ε²)`. With `L₁=L₃=Δ=1` the gain is `ε^{-1/12}/log(1/ε)`. | None on the overlap. Li–Lin's class (Lipschitz Hessian only) is broader. | Li–Lin certify `‖∇f‖ ≤ 82ε` at an averaged point; this is equivalent after rescaling ε | Requires a Lipschitz third derivative and knowledge of `L₃`. Worse by a log factor when `L₁ ≲ L₃^{1/3}ε^{2/3} log⁸(...)`. |
| Zhou–Sugiyama–Suzuki, [arXiv:2610.02791v1](https://arxiv.org/abs/2610.02791) (2 Oct 2026, prior preprint), Thm 1.3. Gradient-only, `p=3`, dimension-dependent. | `O(d² + d^{4/3} ε^{-4/3})`; dependence on `L₃, Δ` not checked → dimension-free bound above | Better when `d ≳ ε^{-1/4}` (up to logs and constants). Worse in low dimension. | None | None | Their bound is better for small `d` |

**Reduction check.** A naive reduction fails. One could replace CDHS's value comparisons by gradient line integrals, but their AGD pairs can be about `√(Δ/(L₃^{1/3}ε^{2/3}))` apart. Keeping the quadrature error below the certificate margin then needs about `(ΔL₃^{1/3})^{1/3}ε^{-4/9}` nodes per comparison, which destroys the rate. Restart tests such as `f(y_t) > f(y₀)` and best-iterate selection have no margin at all. The selected proof gets around this as follows:
- Every tested pair is kept inside a ball of radius `√(α/L₃)/21`, and exiting that ball itself certifies progress.
- Pairs are tested with a 2-point composite Gauss–Legendre surrogate whose error is a fixed fraction of the `α‖u−v‖²` margin.
- Negative curvature is exploited by taking the surrogate argmin over six candidates.

The proof's ancestry is CDHS17 (guarded AGD, convexity certificates, third-order exploitation lemmas), a ball-exit restart in the spirit of Li–Lin, and textbook quadrature. Each piece is standard; the combination is not a demonstrated routine corollary.

**Search coverage.** Searched on 2026-10-25: arXiv and proceedings for gradient-only and third-order nonconvex acceleration, following citations both backward and forward. Sources read:
- CDHS17 Thm 2 and Remark 2, from the PDF.
- Li–Lin Thm 1.
- Zhou–Sugiyama–Suzuki Thms 1.2–1.4. Their discussion after Thm 1.4 states that "the strict gradient-only complexity therefore remains open between the exponents 5/3 and 7/4".
- Xiong–Jerad–Cartis, [arXiv:2605.02127](https://arxiv.org/abs/2605.02127): parameter-free, but uses function values for backtracking and restarts.
- Zhou, [arXiv:2606.05438v2](https://arxiv.org/abs/2606.05438), Thm 5.2: deterministic value + gradient lower bound `Ω(ΔL₁^{1/2}L₃^{1/6}ε^{-5/3})`.
- Zhang et al., [arXiv:2610.17074v2](https://arxiv.org/abs/2610.17074) (12/19 Oct 2026): randomized lower bound only; it cites CDHS for the upper bound.
- Yu–Xu–Gu, [arXiv:1712.06585](https://arxiv.org/abs/1712.06585): its finite-sum rate is `ε^{-2}` at `n=1`.

The Jiang–Mokhtari–Patitucci `d^{1/4}ε^{-13/8}` bound was not read directly. The companion note's citations check out, with one exception: the note's attribution of a **value-and-gradient** randomized lower bound to ZSS Cor. 6.3 was not verified (their Thm 1.4 is stated for gradient-only oracles). The result entered this repository on 2026-10-25 (`a94803e`), and no repository theorem covers this class. I did not run the build or axiom audit.

**Conclusion**

**Yes: it is the first dimension-free, gradient-only method I found that reaches the ε^{-5/3} rate under Lipschitz third derivatives.** CDHS17 already achieves this rate, but it needs function values. The best previous dimension-free gradient-only guarantee (Li–Lin, which needs only a Lipschitz Hessian) is ε^{-7/4}:

| | oracle | gradient calls, `ε^{2/3} ≤ min(ΔL₃^{1/3}, L₁/L₃^{1/3})` |
|---|---|---|
| CDHS17 | value + gradient | `Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} log(L₁Δ/ε²)` |
| Li–Lin | gradient | `Δ L₁^{5/8} L₃^{1/8} ε^{-7/4}` |
| this result | gradient | `Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} log(1+L₁Δ/ε²)` |

Against CDHS17 the rate is unchanged and the constants are worse; the gain is that function values are no longer needed. Against Li–Lin, the extra third-order assumption buys a factor of `(L₁/(L₃^{1/3}ε^{2/3}))^{1/8}`, which survives the log only when `L₁/(L₃^{1/3}ε^{2/3}) ≫ log⁸(L₁Δ/ε²)`. That gain is asymptotically real but numerically small. Combined with Zhou's deterministic lower bound, the gradient-only deterministic complexity is now tight up to a log factor.

The comparison proves the oracle relaxation at an unchanged rate. As for priority, a paper from 2 Oct 2026 explicitly called this gap open, and I found no later closure. The search window is short, though, and the localization-plus-quadrature idea could be folklore. The contribution that can be claimed is closing the gradient-only 5/3-versus-7/4 gap with a matching-order upper bound, not a faster method than CDHS17.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
