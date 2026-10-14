# Novelty assessment: BacktrackingGeneralizedAccelerated

The [theorem](../../LongTails/Theorems/BacktrackingGeneralizedAccelerated.lean) ([setup](../../LongTails/Setups/GeneralizedSmoothParameterFree.lean), [algorithm](../../LongTails/Algorithms/BacktrackingAccelerated.lean)) proves the following for every convex `f` on a real Hilbert space that satisfies `‖∇²f(x)‖ ≤ L₀ + L₁‖∇f(x)‖` and has a minimizer `x*` with `‖x₀−x*‖ ≤ R` and `f(x₀)−f* ≤ Δ`. A similar-triangles Nesterov method with step doubling and halving uses only gradients. Its public input is `(x₀, h₀)` for an arbitrary `h₀ > 0`; it does not receive `L₀, L₁, R, Δ, ε`. Its deterministic last iterate satisfies `f(x̂) − f* ≤ ε` after the stated number of gradient calls, which includes the calls made by rejected trials.

**Complexity of the selected result.** Here `L₀, L₁` are the (L₀,L₁) constants, `R` is the initial distance, `Δ` is the initial gap, and `h₀` is the initial trial step. The bound comes directly from `budget = 2⌈5 + 4√(32L₀R²/ε) + 26(1+L₁R)·log(1 + (2+13L₁R)²(2 + 1/(64L₀h₀) + 16L₀h₀ + 5L₁²Δ/(4L₀) + 80L₁²Δh₀))⌉`:

  `O( √(L₀R²/ε) + (1+L₁R)·log(2 + L₁R + 1/(L₀h₀) + L₀h₀ + L₁²Δ/L₀ + L₁²Δh₀) )` gradient calls.

Because `∇f(x*) = 0`, the standard (L₀,L₁) integration bound gives `L₁²Δ/L₀ ≤ e^{L₁R}`. Therefore the second term is always `O((1+L₁R)(1 + L₁R + log(2 + 1/(L₀h₀) + L₀h₀)))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Borodich–Kovalev, Accelerated GRAAL ([arXiv:2507.09823v2](https://arxiv.org/abs/2507.09823), 29 Aug 2025, Cor. 3); **prior** direct adaptive competitor | `1 + √(L₀R²/ε) + (L₁R)³ + (1+L₁²R²)·log(1/(η₀L₀))`, valid only if `η₀L₀e^{L₁R} ≤ 1`, which forces `log(1/(η₀L₀)) ≥ L₁R` → with `h₀ = η₀`: `√(L₀R²/ε) + (1+L₁R)(1+L₁R+log(1/(L₀h₀)))` | Start-up `(L₁R)³ + (L₁R)²log(1/(L₀η₀))` → `(1+L₁R)(L₁R + log(1/(L₀h₀)))`: an `≈L₁R` factor when `L₁R ≥ 1`. The total gains when `ε ≳ L₀R²/(L₁R)⁶`; same order when `L₁R ≲ 1` or for smaller `ε` | None (same class) | Initial step must satisfy `η₀ ≤ e^{−L₁R}/L₀` (unknown) → any `h₀ > 0`; gradient + function-value oracle → gradients only. Both give last-iterate guarantees | Backtracking: 2 gradient calls per trial, and rejected trials are counted (constant factor). These are proved upper bounds, not lower bounds on GRAAL |
| Tyurin, AGD ([arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884), ICML 2026, PMLR 306, Thm 4.3); **prior**, known parameters | With `Γ₀ = 2Δ/R²`, `R̄ = R`: `√(L₀R²/ε) + L₁R·log(2 + min{L₁²Δ/L₀, Δ/ε}) + log(2 + Δ/(L₀R²))` → selected bound | None: same order when `h₀ ≈ 1/L₀`. Worse by an additive `(1+L₁R)log(L₀h₀ + 1/(L₀h₀))` for a poor `h₀`, by an extra `log(2+L₁R)`, and when `Δ/ε < L₁²Δ/L₀` | None | Needs `L₀, L₁, R̄ ≥ R, Γ₀ ≥ 2Δ/R²` → needs nothing (the overestimate `R̄` enters through `L₁R̄`); same last-iterate output | Backtracking constant factor; no `ε`-dependent shortcut in the logarithm |
| Vankov et al., AGMsDR ([arXiv:2410.10800v3](https://arxiv.org/abs/2410.10800), Thm 6.2); **prior** | `(ν+1)[√(L₀R²/ε) + (L₁R)^{2/3}log(Δ/ε)]`, where `ν` is the unbounded cost of an exact 1-D search → selected bound | Not comparable: the cost `ν` is not bounded in the original parameters. Ignoring `ν`, its start-up has a better power of `L₁R`, but an `ε`-dependent logarithm | None | Needs `L₀, L₁` in the step and an exact line search → no parameters and no search | Loses the `(L₁R)^{2/3}` start-up power |
| Repository `GeneralizedAcceleratedConvex` (2026-09-25) | `√(L₀R²/ε) + (L₁R)^{2/3}log(Δ/ε)`, with `L₀, L₁, R, Δ` known → selected bound | Mixed: worse start-up power and better (`ε`-free) logarithm | None | Known parameters → none | Repository overlap only; not literature evidence |

**Reduction check and proof ancestry.** Standard reductions do not give this bound. If `f` is treated as smooth on `B(x*, 3R)`, Nesterov's backtracking FGM (Math. Program. 2013, Sec. 4) pays `L₀e^{cL₁R}` in the leading term. Running GRAAL with a tiny `η₀` gives the cubic start-up. Guessing and doubling `L₀, L₁, R, Δ` for Tyurin's method requires restarts and adds `ε`-dependent logarithms. Nesterov's backtracking FGM and Tyurin's potential-tied step cap `a/A ≲ 1/(L₁R)` supply the scheme and the key estimate. The new step is the proof (`small_step_accept`, `progress_step`) that a gradient-only test accepts every step of size up to `min(1/(64L₀), A/σ²)` with `σ = 2+13L₁R`. As a result, backtracking finds the state-dependent cap without being given `L₁` or `R`.

**Search coverage (2026-10-07).** I searched arXiv and the ICML/ICLR proceedings for adaptive, parameter-free, and backtracking accelerated methods under (L₀,L₁) and ℓ-smoothness. I found nothing before the result's introduction (commit `22949a3`, 2026-10-03) that is parameter-free with a linear-in-`L₁R` start-up. Lobanov ([2608.04884](https://arxiv.org/abs/2608.04884)) needs the parameters and uses restarts. Dvinskikh et al. ([2609.06555](https://arxiv.org/abs/2609.06555)) is stochastic. Xu–Chen (2601.19013) and Wang–Peypouquet (2512.20478) assume globally smooth objectives. I did not verify that GRAAL appeared at ICLR 2026, as the companion note claims; the note's other claims match the checked statements. Not finding a paper does not prove priority.

**Conclusion**

**Yes: it is the first checked method that needs no parameters and matches the best known-parameter bound up to logarithms.** It also improves the start-up cost of the strongest prior adaptive method, Accelerated GRAAL.

| | supplied | gradient calls |
|---|---|---|
| GRAAL (Cor. 3) | `η₀ ≤ e^{−L₁R}/L₀` | `√(L₀R²/ε) + (L₁R)³ + (1+L₁R)²log(1/(L₀η₀))` |
| Tyurin (Thm 4.3) | `L₀, L₁, R, Δ` | `√(L₀R²/ε) + L₁R·log(2+L₁²Δ/L₀) + log(2+Δ/(L₀R²))` |
| this result | any `h₀ > 0` | `√(L₀R²/ε) + (1+L₁R)·log(2+L₁R+1/(L₀h₀)+L₀h₀+L₁²Δ/L₀+L₁²Δh₀)` |

The gain over GRAAL affects only the `ε`-free start-up term, which shrinks by a factor of about `L₁R`. It matters when `L₁R ≫ 1` and `ε ≳ L₀R²/(L₁R)⁶`. For the 1-D instance `f(x) = eˣ − x` (`L₀ = L₁ = 1`, `x₀ = R`), the proved start-up is `O(R² + R·log(1/h₀ + h₀))` instead of `Ω(R³)` in GRAAL's bound. The method also removes GRAAL's requirement of an exponentially small initial step and its use of function values. Against Tyurin's known-parameter method, nothing is faster: the bound is the same order, plus an `h₀`-mismatch logarithm. Vankov et al.'s line-search method is not comparable on cost.

These are comparisons of upper bounds. Nothing here shows that GRAAL actually needs `(L₁R)³` calls or that `L₁R·log` is optimal. Priority is supported only by a limited search of arXiv and recent proceedings.

What can be claimed is a parameter-free, gradient-only accelerated method for convex (L₀,L₁)-smooth problems whose last-iterate complexity matches Tyurin's known-parameter bound and has a proved start-up roughly `L₁R` times smaller than that of GRAAL.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
