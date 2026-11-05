# RadiusFreeGeneralizedAccelerated: novelty assessment

[`result`](../../LongTails/Theorems/RadiusFreeGeneralizedAccelerated.lean) shows that, for every convex, differentiable `f` on a Hilbert space with `‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖` and a minimizer within distance `R` of `x₀`, the [setup](../../LongTails/Setups/RadiusOnlyGeneralizedSmoothConvex.lean)'s gradient-only [RadiusFreeSherpa](../../LongTails/Algorithms/RadiusFreeSherpa.lean) method returns a point with `f(x̂) − f* ≤ ε` after the stated number of calls. The method receives only `x₀, L₀, L₁`. It does not use `R` or `ε` and needs no bound on the initial gap.

**Complexity** (`L₀, L₁ > 0` smoothness constants, `R` the distance bound, `ε` the target accuracy; every probe and every Phase-2 trial counted; `R, ε > 0`):

  `O( √(L₀R²/ε) + (1 + L₁R)·log(2 + L₁R) )`.

The proved budget is `⌈64√(L₀R²/ε) + 32768(1+L₁R)log(2+L₁R)⌉`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, SHERPA+CRUISE, [arXiv:2610.21461v1](https://arxiv.org/abs/2610.21461) (15 Oct 2026, preprint), Thm 3.7; lower bound Thm 4.10 | `5√(L₀R²/ε) + 240(1+L₁R)log₂(64(1+L₁R)) + 2` → `O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R))` | None: same order. Both match the Thm 4.10 lower bound `Ω(1 + √(L₀R²/ε) + L₁R/√log(2+L₁R))` (for `L₀R² ≥ ε`) up to a `log^{3/2}(2+L₁R)` factor on the `L₁R` term | None: same class `P_R` | Inputs `L₀, L₁, R, ε` → `L₀, L₁` only. The guarantee holds at every `N ≥ budget` (anytime). Both use the final point as output | Constants are worse (64 vs 5; 32768 vs 240·log₂). Both are deterministic, gradient-only methods with an exact oracle |
| Tyurin, [arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884) (May 2026), Thm 4.3 | `√(L₀R²/ε) + L₁R̄·log(min{L₁²R̄²Γ₀/L₀, Γ₀R²/ε}) + log⁺(Γ₀/L₀)` with `R̄ ≥ R` and `Γ₀ ≥ 2Δ/R²`. In `P_R`, `Δ` can reach `(L₀/L₁²)e^{L₁R}`, which gives `Θ((L₁R)²)` | `(L₁R)² → (L₁R)log(2+L₁R)` whenever `(L₁R)² ≳ √(L₀R²/ε)` | None | Needs `R̄, Γ₀`, i.e. `R` and a gap bound → needs neither | None |
| Repository [`BacktrackingGeneralizedAccelerated`](../../LongTails/Theorems/BacktrackingGeneralizedAccelerated.lean) (parameter-free, in the repository since 2026-10-14) | `√(L₀R²/ε) + (1+L₁R)log(…+L₁²Δ/L₀+…)`, which is `Θ((L₁R)²)` in `P_R` → this result | `(L₁R)² → (L₁R)log(2+L₁R)` in the same regime | None | Knows nothing, not even `L₀, L₁` → needs `L₀, L₁` | Supplying `L₀, L₁` is a loss of adaptivity |

Methods that pay at least `(L₁R)²` without acceleration, such as Gorbunov et al. [2409.14989](https://arxiv.org/abs/2409.14989) and Okazaki et al. [2610.27681](https://arxiv.org/abs/2610.27681), are dominated and omitted from the table. Some methods need stronger oracles and are not comparable: Vankov et al. AGMsDR [2410.10800](https://arxiv.org/abs/2410.10800) uses exact segment minimization, and Lobanov [2608.04884](https://arxiv.org/abs/2608.04884), Thm 5 and §7, needs `f*`, function values and segment minimization.

**Standard-reduction check.** Everest's guarantees hold for any input `R̄ ≥ R` (Lemmas 3.4–3.5; SHERPA's call count is fixed by `R̄`).
- *Known `ε`.* Run Thm 3.7 with guesses `R̄ = 2ʲ√(ε/L₀)` and output the last completed run. Each later run also succeeds, and the geometric sum gives `O(1 + √(L₀R²/ε) + (1+L₁R)log(2+L₁R))`. This makes the method `R`-oblivious at the same order.
- *Unknown `ε` as well.* At stage `s`, run SHERPA with `R̄_s = 2ˢ/(sL₁)` (about `2ˢ` calls), then run the repository's anytime parameter-free method for `2ˢ` calls, and output the last completed stage. This appears to give the same order. The repository's method was already used by this proof.

I sketched this reduction but did not formalize it. If it holds, the adaptivity follows from Thm 3.7 by guess-and-doubling, up to constants. The new mechanism is a single run with no restarts. It uses an observable bisection acceptance test (`φ(t) ≥ 0` gives `f(z(t)) ≤ f(x)` by convexity) and stops at a gradient-norm threshold `‖∇f‖ ≤ L₀/(4L₁)` that needs no certificate. It also has a new incremental-potential count. *Proof ancestry:* the Everest potential and the Φ-inequality (Lemma 3.4), and the repository's backtracking accelerated method as Phase 2.

**Search coverage** (2026-11-01): arXiv and web searches on accelerated, parameter-free and radius-free methods for convex `(L₀,L₁)` optimization, plus the full Everest HTML (Thms 3.7 and 4.10, Prop. 3.6, §5) and Tyurin's Thm 4.3. Everest has only v1, and I found no later work citing it. The result was committed on 2026-11-01. The companion note's claim that every `R`-oblivious gradient method pays `q²` is accurate for the explicit published methods, but it ignores the doubling reduction above. Its other citations agree with the sources I checked.

## Conclusion

**The rate is unchanged; what is new is that `R` and `ε` are no longer inputs, but a standard doubling argument appears to recover that too.**

The strongest baseline is Everest's Theorem 3.7, which gets the same `O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R))` on the same class. That bound is already near-optimal up to logarithms. Everest's method needs `R` and `ε`; this one needs only `L₀, L₁`.

| | inputs | calls |
|---|---|---|
| Everest Thm 3.7 | `L₀, L₁, R, ε` | `O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R))` |
| this result | `L₀, L₁` | same order, larger constants |

Against the published methods that do not use `R` (Tyurin with a trivial `R̄`, and the repository's parameter-free method), the transient term improves from `(L₁R)²` to `L₁R·log(2+L₁R)`. That gain matters when `(L₁R)² ≳ √(L₀R²/ε)`. However, running Everest's own method with doubled guesses of `R`, and outputting the last completed run, appears to give the same order. A second staged schedule that reuses the repository's anytime method appears to remove `ε` as well. I sketched this reduction but did not formalize it.

What can be claimed is a cleaner single-run method, free of `R` and `ε`, with a formal proof that matches Everest's rate. If my reduction sketch is wrong, the adaptivity gain would be more substantial. The literature search found no prior method stated this way, but priority rests on a two-week-old preprint.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
