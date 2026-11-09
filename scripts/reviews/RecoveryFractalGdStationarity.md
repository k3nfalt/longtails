# Novelty assessment: RecoveryFractalGdStationarity

[`result`](../../LongTails/Theorems/RecoveryFractalGdStationarity.lean) proves the following. Take any finite-dimensional `C²` function `f` with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian and `f(x₀) − f(x) ≤ Δ` for all `x` ([setup](../../LongTails/Setups/SmoothHessianLipschitzGd.lean)). The method is [recovery-gated fractal Chebyshev GD](../../LongTails/Algorithms/RecoveryFractalGd.lean): every update is `x − η∇f(x)` with `η > 0`, and `η` is chosen from the history using `L, ρ, Δ, ε`. Using exact gradients only, it deterministically outputs the best queried point, which satisfies `‖∇f(x̂)‖ ≤ ε`. Compliance with `adaptiveGdFamily` is proved (`RecoveryFractalExecution.allowed`).

**Complexity.** `L` is the gradient-Lipschitz constant, `ρ` the Hessian-Lipschitz constant, `Δ` the initial gap and `ε` the gradient-norm target. For `L, ε > 0` and `ρ, Δ ≥ 0`, the exact Lean budget gives

```
N = O( log(2 + LΔ/ε²)^{4/3} · [ ΔL^{2/3}ρ^{1/6}ε^{-11/6} + √(LΔ)/ε + L^{11/17}Δ^{15/17}ρ^{2/17}ε^{-28/17} + 1 ] )
```

The leading constant is `2¹⁸`. There is no `min` with plain GD, so the bound exceeds GD's order when `ρε > L²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Li–Lin restarted AGD, [arXiv:2201.11411v4](https://arxiv.org/abs/2201.11411) (ICML 2022; JMLR 2023), Thm 1. This is a direct competitor: same class, gradients only. Its guarantee is `82ε`, and it needs `θ = 4(ερ/(16L²))^{1/4} ≤ 1`. Rescale to `ε/82`, run it with `ρ' = max(ρ, ε³/Δ²)`, and use GD when `θ > 1`. | `O(1 + min{LΔ/ε², ΔL^{1/2}ρ^{1/4}ε^{-7/4} + √(LΔ)/ε})`, including the final epoch `(L²/(ρ'ε))^{1/4} ≤ √(LΔ)/ε` → bound above | **Worse** in every regime. When `ρε ≤ L²`, the leading-term ratio is `(L²/(ρε))^{1/12}` times logs. The `√(LΔ)/ε` term is shared, and the mixed term adds cost. When `ρε > L²`, the result is worse than GD. | None: same class. | None. Both need `L, ρ, ε` (and `Δ` for this retuning). Li–Lin output a last-epoch average; this result outputs a queried point. Both certify the same `‖∇f‖ ≤ ε`. | The only distinction is that the selected method uses no momentum. That restricts the method, not the problem class. |
| Repository [`FractalChebyshevGdStationarity`](../../LongTails/Theorems/FractalChebyshevGdStationarity.lean) (commit `4a914a3`, 2026-10-30). It is momentum-free GD on the same objective class; its setup encodes a different restart family. | `O(ΔL^{7/9}ρ^{1/9}ε^{-17/9}log(2+L²/(ρε)) + (L²/(ρε))^{1/9} + 1)` → bound above | Exponent `17/9 → 11/6`. The leading ratio is `(ρε/L²)^{1/18}` times `log^{4/3}(LΔ/ε²)/log(L²/(ρε))`. This needs `ρε ≪ L²` and `LΔ/ε² ≥ (L²/(ρε))^{5/12}`. For fixed `L, ρ, Δ` as `ε → 0`, the bound improves from `ε^{-17/9}` to `ε^{-11/6}`. With the stated constants, a gain appears only for `L²/(ρε)` above roughly `2^{220}`. | None. | Worse: `Δ` becomes required in the updates. | The extra `√(LΔ)/ε` and mixed terms are added. The constant is larger. |
| GD with step `1/L` (Nesterov, *Lectures on Convex Optimization*, 2018, §1.2.3) | `O(1 + LΔ/ε²)` → bound above | Factor `(L²/(ρε))^{1/6}` up to logs when `ρε ≪ L²` and `LΔ ≫ ε²`. With the stated constants, the gain needs about `L²/(ρε) ≳ 2^{170}`. | None. GD needs only `L`-smoothness. | None: both can return the best queried point. | Needs a Lipschitz Hessian and knowledge of `ρ, Δ`. |

**Reduction check and ancestry.** No composition of known theorems gives a sub-`ε^{-2}` bound for positive-step GD.
- Convex long-step and silver analyses (Grimmer, [arXiv:2307.06324](https://arxiv.org/abs/2307.06324); Altschuler–Parrilo) do not transfer to nonconvex stationarity.
- The fractal schedule and its window bounds come from Agarwal–Goel–Zhang ([ICML 2021](https://proceedings.mlr.press/v139/agarwal21a.html)), but for quadratics only.
- What is new is the step-weighted impulse estimate, the low/high/negative energy split and the paid recovery after aborted trials. I did not audit these proofs, and I ran no build or axiom check.
- The deterministic lower bound is `Ω(ε^{-12/7})` (Carmon–Duchi–Hinder–Sidford, [arXiv:1711.00841](https://arxiv.org/abs/1711.00841)). An unreviewed preprint claims `Ω(ε^{-7/4})` (Zhou, [arXiv:2606.05438v2](https://arxiv.org/abs/2606.05438)). So `11/6` is not shown to be optimal for this method family.

**Search coverage.** I searched on 2026-11-06 across arXiv, PMLR and the web for long, silver, fractal and Chebyshev stepsizes and for momentum-free GD on Hessian-Lipschitz nonconvex problems. I read Li–Lin Thm 1 via arXiv HTML v4. Carmon et al., Zhou, and the recent convex stepsize lower bounds ([arXiv:2608.10418](https://arxiv.org/abs/2608.10418), [arXiv:2609.02855](https://arxiv.org/abs/2609.02855)) were checked at abstract level only. The companion note's Flatland and First-ish citations were not verified independently. Outside this repository, I found no sub-`ε^{-2}` guarantee for momentum-free GD on this class. The companion note's claims agree with the Lean statement, including its admission that `Δ` is needed.

## Conclusion

**No improvement for the problem class: the result sharpens the repository's own momentum-free GD exponent, but restarted AGD is faster everywhere.**

The strongest baseline is Li–Lin's restarted AGD. It has the same objective class, the same gradient-only oracle and the same deterministic `‖∇f‖ ≤ ε` target:

| Method | Gradient calls (up to logs) |
|---|---|
| restarted AGD | `ΔL^{1/2}ρ^{1/4}ε^{-7/4} + √(LΔ)/ε` |
| this result | `ΔL^{2/3}ρ^{1/6}ε^{-11/6} + √(LΔ)/ε + L^{11/17}Δ^{15/17}ρ^{2/17}ε^{-28/17}` |
| previous fractal GD (repository) | `ΔL^{7/9}ρ^{1/9}ε^{-17/9} + (L²/(ρε))^{1/9}` |

AGD's leading term is smaller by `(L²/(ρε))^{1/12}`, and no term of the selected bound is better.

Within positive-step GD, the exponent gap to `7/4` shrinks from `5/36` to `1/12`. That gain is over a repository theorem added one week earlier, not over published work. It also costs `Δ` in the updates, and with the stated constants it only shows up at astronomically small `ρε/L²`. That is not "GD almost as fast as AGD." My search found no external momentum-free result of this kind, but that does not establish priority.

What can be claimed is a new, formally proved `ε^{-11/6}` stationarity bound for adaptive momentum-free GD, with no advantage over existing methods for the problem.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
