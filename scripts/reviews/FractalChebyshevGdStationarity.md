# Novelty assessment: FractalChebyshevGdStationarity

[`result`](../../LongTails/Theorems/FractalChebyshevGdStationarity.lean) proves the following. Take any C² function `f` on a finite-dimensional space with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian and `f(x₀) − inf f ≤ Δ`. Run restarted gradient descent ([algorithm](../../LongTails/Algorithms/RestartedChebyshevGd.lean)): its steps are fractal-ordered Chebyshev stepsizes, plus `1/L` steps when the gradient is large, with a distance restart and stopping at `‖∇f‖ ≤ ε`. This method deterministically returns a point with `‖∇f(x̂)‖ ≤ ε` using exact gradient queries only ([setup](../../LongTails/Setups/HessianLipschitzGradientStationarity.lean)). `allowedAlgorithm` enforces memoryless updates `x ← x − h∇f(x)`, positive menu steps, this restart/threshold rule and the stopped-iterate output, and the theorem proves compliance.

**Proved budget.** Here `L` is the gradient-Lipschitz constant, `ρ` the Hessian-Lipschitz constant, `Δ` the initial gap and `ε` the gradient-norm target. All `L, ρ, ε > 0`, `Δ ≥ 0`, and the bound holds for every `ε`:

```
N = O( L^{7/9} ρ^{1/9} Δ ε^{-17/9} · log(2 + L²/(ρε)) + (L²/(ρε))^{1/9} + 1 )
```

The constant is 1000 in the leading term. The method needs `L, ρ, ε` but not `Δ`.

Below, write `κ = L²/(ρε)` and `T = LΔ/ε²`; these are used only to state regimes.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| GD with step `1/L` (folklore descent-lemma bound, e.g. Nesterov, *Lectures on Convex Optimization*, §1.2.3); applies to the full target class | `O(1 + LΔ/ε²)` → `O(L^{7/9}ρ^{1/9}Δε^{-17/9}log(2+L²/(ρε)) + (L²/(ρε))^{1/9} + 1)` | Factor `(L²/(ρε))^{1/9}/log(L²/(ρε))` on the leading term. With the proved constants this needs `L²/(ρε) ≳ 2^{145}` and `LΔ/ε² ≳ (L²/(ρε))^{1/9}`. **Worse** for `2^{40} ≤ L²/(ρε) < 2^{145}`. | None. GD needs only an L-smooth function. | None. Both use the same gradient-only oracle and return a stopped iterate. | Needs a ρ-Lipschitz Hessian, C² regularity and knowledge of `ρ`. Adds a restart rule and long steps. |
| Li–Lin, restarted AGD, [arXiv 2201.11411](https://arxiv.org/abs/2201.11411), JMLR 24 (2023), Thm 1; direct competitor, same class and gradient-only oracle | Thm 1 targets `82ε`; rescale to `ε`. Applies when `ε ≲ L²/ρ`, and GD covers larger `ε`. Including the final uncertified-length epoch of `K ≈ (L²/(ρε))^{1/4}` steps (proof of Thm 1, §4.1): `O(ΔL^{1/2}ρ^{1/4}ε^{-7/4} + (L²/(ρε))^{1/4})` → this result | **Worse** by a factor `(L²/(ρε))^{5/36}·log(L²/(ρε))` whenever the leading terms dominate. Smaller only in the narrow window `κ^{1/9} ≲ T ≲ κ^{13/36}/log κ` with `κ ≳ 2^{145}`, where the bound is driven by additive certification terms (see body). | None. | None. Both need `L, ρ, ε`. Li–Lin output an average from the last epoch and the result returns the stopped iterate; both give deterministic gradient-norm certificates. | The result's only distinction is that the method uses no momentum. That restricts the method; it does not widen the problem class. |

**Regime check.** The leading-term ratio of the result to Li–Lin is `L^{5/18}ρ^{-5/36}ε^{-5/36} = κ^{5/36}`, times a log factor. The only regime where the result's proved bound is smaller than both baselines comes from additive terms. For example, at `T = κ^{1/4}`, i.e. `Δ = ε^{7/4}L^{-1/2}ρ^{-1/4}`, Li–Lin's bound is dominated by its final epoch, `≈ κ^{1/4}`, and GD needs `≈ κ^{1/4}` steps. The result needs `≈ κ^{5/36}log κ + κ^{1/9}`. This compares upper bounds only, at κ beyond 10⁴³. Whether Li–Lin's last epoch can be shortened was not checked, so I give this window little weight.

**Reduction check and proof ancestry.** I found no standard reduction that yields a sub-`ε^{-2}` bound for momentum-free GD. The convex long-step results do not transfer to nonconvex stationarity:
- Altschuler–Parrilo silver stepsizes ([2309.16530](https://arxiv.org/abs/2309.16530));
- Grimmer, long steps ([SIOPT, 10.1137/23M1588408](https://doi.org/10.1137/23M1588408));
- Grimmer–Shu–Wang ([2410.16249](https://arxiv.org/abs/2410.16249));
- Rotaru–Glineur–Patrinos ([2406.17506](https://arxiv.org/abs/2406.17506)). They treat L-smooth nonconvex functions without a Hessian assumption, where `Ω(ε^{-2})` holds for all first-order methods, so they can only improve constants.

Proof ancestry:
- Agarwal–Goel–Zhang ([ICML 2021](http://proceedings.mlr.press/v139/agarwal21a/agarwal21a.pdf)) and Lebedev–Finogenov supply the fractal schedule and its window/prefix bounds, but only for convex quadratics.
- Li–Lin supply the distance-restart template.

The new step is controlling Hessian drift of order `ρR`, comparable to the smallest Chebyshev root, together with `L/μ` window amplification, negative-curvature directions, and inter-block "debts". This combination gives the `κ^{-1/9}` gain. The lower bound is `Ω(ε^{-12/7})` (Carmon et al., [1711.00841](https://arxiv.org/abs/1711.00841)), so `17/9` is not shown to be optimal for stepsize-only methods.

**Search coverage.** I searched on 2026-10-30 across arXiv and ICML/JMLR/SIOPT sources for long-step, silver, Chebyshev and fractal stepsizes and for momentum-free acceleration in nonconvex Hessian-Lipschitz settings. I read Li–Lin Thm 1 and its proof; the other sources were checked at abstract or snippet level. I found no earlier sub-`ε^{-2}` guarantee for momentum-free GD on this class. Very recent preprints may have been missed. The result entered the repository today (commit `4a914a3`). The companion note's citations match what I found. Its claim "GD and nothing else" should be qualified: the method uses oracle-dependent restarts and threshold switches.

## Conclusion

**No problem-class improvement: this is a new analysis of momentum-free GD that beats GD's own `ε^{-2}` bound only at astronomically small `ε`.**

The strongest applicable baseline is Li–Lin's restarted AGD. It uses the same class, the same exact-gradient oracle and the same deterministic `‖∇f‖ ≤ ε` certificate:

| | gradient queries |
|---|---|
| GD (`1/L`) | `LΔ/ε²` |
| this result | `L^{7/9}ρ^{1/9}Δε^{-17/9}·log(L²/(ρε)) + (L²/(ρε))^{1/9}` |
| restarted AGD | `L^{1/2}ρ^{1/4}Δε^{-7/4} + (L²/(ρε))^{1/4}` |

AGD's leading term is smaller by a factor `(L²/(ρε))^{5/36}` and a log. The result beats GD's proved bound only once `L²/(ρε) ≳ 2^{145}`, and it is worse than GD for `2^{40} ≤ L²/(ρε) < 2^{145}`.

What the comparison does establish is a method-specific exponent: gradient descent without momentum (distance restarts, a fixed stepsize menu) goes below `ε^{-2}` on general Hessian-Lipschitz nonconvex functions. That is a nonconvex counterpart to the convex long-step results. Priority for this claim is not contradicted by my search, but very recent work may have been missed. The gap to `7/4` remains, and the result is not "almost AGD".

The contribution that can be claimed is the first, to my knowledge, sub-`ε^{-2}` stationarity guarantee for momentum-free GD on this class, with no advantage over existing methods for the problem.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
