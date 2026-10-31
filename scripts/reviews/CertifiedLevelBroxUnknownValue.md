# CertifiedLevelBroxUnknownValue: what is actually new?

The [theorem](../../LongTails/Theorems/CertifiedLevelBroxUnknownValue.lean) ([setup](../../LongTails/Setups/UnknownValueSmoothConvexLocalLinear.lean), [algorithm](../../LongTails/Algorithms/CertifiedLevelBrox.lean)) covers a closed convex `C` in a real Hilbert space and an objective `f` that is convex and `L`-upper-quadratic on `C`. It uses exact value-gradient queries and an exact point-only local LMO `argmin{⟨g,v⟩ : v ∈ C, ‖v−x‖ ≤ r}`, whose ties may be broken adversarially. The algorithm receives only `x₀`, `R` and `ε`. Within the stated budget, the returned best-observed point is feasible and satisfies `f(y) − f⋆ ≤ ε` for every seed.

**Complexity (all value-gradient and local-LMO calls):**
`N = ⌈400√(LR²/ε) + 40 log₂(2 + (Δ+LR²)/ε)⌉ + 300 = O(1 + √(LR²/ε) + log(2 + Δ/ε + LR²/ε))`.
Here `L` is the smoothness constant on `C`, `R ≥ ‖x₀ − x⋆‖`, `Δ ≥ f(x₀) − f⋆`, and `ε > 0` is the objective accuracy. `L` and `Δ` enter only the budget. The bound holds for `L = 0` and `R = 0`. Because of the normal gradient at a constrained `x⋆`, `Δ` is not bounded by `LR²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Frank–Wolfe with step `2/(k+2)` on `D = C ∩ B(x₀,R)` (Jaggi, [ICML 2013](https://proceedings.mlr.press/v28/jaggi13.html), Thm 1, with `diam D ≤ 2R` and `C_f ≤ L·diam²`). One local-LMO call at radius `R` plays the role of the LMO over `D`; `x⋆ ∈ D` | `O(1 + LR²/ε)` → `O(1 + √(LR²/ε) + log(2 + Δ/ε + LR²/ε))` | Factor `√(LR²/ε)` when `LR²/ε ≥ log²(2 + Δ/ε)`, for example `Δ ≤ poly(LR²/ε)` and `LR²/ε → ∞` | None (the same class; FW needs smoothness only on `D`) | None in required information: both need only `R`, and FW is anytime and needs no `ε`. Output: FW gives the last iterate; this result gives the best observed point | **Worse** when `LR²/ε ≲ log(Δ/ε)`. For example, at `L = 0` FW is exact after one iteration, while this method pays `Θ(log(Δ/ε))` calls |
| Richtárik–Gruntkowska–Li, [BroxGD](https://arxiv.org/abs/2605.08850) (v2, 28 Sep 2026, preprint), Thm 3.2(ii): radius `R/√K`, best iterate, `LR²/(2K)` | `2K` calls with `K ≥ LR²/(2ε)`, i.e. `O(1 + LR²/ε)` → same as above | Same regime as the FW row | `X ⊆ ℝᵈ` with `∇f` Lipschitz on an open neighbourhood → Hilbert space with an upper model on `C` only (minor) | Removes the need to know `L`: choosing a horizon `K` that certifies `ε` requires `L`, and this result does not | Same `log(Δ/ε)` loss when `LR²/ε` is small |
| Same paper, Thm 3.5, and Richtárik–Mahran, [arXiv:2609.33383](https://arxiv.org/abs/2609.33383) (v1, 27 Sep 2026), Thms 3–4: Polyak radius | Non-accelerated `O(1/K)`, needs `f⋆` → as above | `ε⁻¹` → `ε⁻¹ᐟ²` leading dependence | None | Exact `f⋆` → not needed; still needs `R` | Needs `R`; the Polyak-radius methods do not |
| Repository [SplitBroxKnownValue](SplitBroxKnownValue.md) (2026-10-11, unpublished) | `3(⌈√(10LR²/ε)⌉+1)` with `f⋆, L, R` known → as above | Worse by an additive `O(log(2 + Δ/ε + LR²/ε))` | None | Known `f⋆` and `L` → unknown; last iterate → best observed point | Larger constants |

**Reduction check and proof ancestry.** Given the repository's split-reply analysis, the new step is largely a standard composition. With `ℓ ≥ f⋆`, the cut inequality with anchor `x⋆` lets SplitBrox's invariants hold with `ℓ` in place of `f⋆`. A capped run that misses `ℓ + gap/4` then certifies `ℓ < f⋆`. This is Lan's bundle-level gap reduction ([Math. Program. 2015](https://doi.org/10.1007/s10107-013-0737-x)) combined with checked backtracking on `L̂`, and the potential count makes both overheads additive rather than multiplicative, as in Hazan–Kakade ([arXiv:1905.00313](https://arxiv.org/abs/1905.00313)). No published theorem yields `√(LR²/ε)` local-LMO calls. Projection-based accelerated methods (APMM, Lan's APL) need exact projections onto `C ∩ halfspace`, and emulating one with a local LMO needs a radius search with an unknown step length. That obstruction is resolved by SplitBrox, not by this theorem.

**Search coverage (2026-10-21).** I searched arXiv and the web for accelerated local-LMO, broximal, ball-oracle and unknown-`f⋆` level methods. I read BroxGD v2 Thm 3.2 and the Richtárik–Mahran theorem summaries, and the latter claims no acceleration. I found no accelerated local-LMO method. Carmon et al.'s [ball optimization oracle](https://arxiv.org/abs/2003.08078) minimizes `f` itself over a ball, a stronger oracle that is not comparable. The theorem was introduced in commit `0df2c3c` (2026-10-21), after all cited works. The companion note omits the Frank–Wolfe baseline on `C ∩ B(x₀,R)`, which uses the same information and is the fair comparison. It also describes BroxGD as not needing `L`, but a certified horizon does need it.

## Conclusion

**Yes, against published local-LMO methods it improves the proved complexity from `LR²/ε` to accelerated, using the same information (`R` only).**

The strongest same-information baseline is Frank–Wolfe on `C ∩ B(x₀,R)`, which costs one local-LMO call per iteration. BroxGD Thm 3.2(ii) has the same order but needs `L` to pick its horizon.

| | calls | needs |
|---|---|---|
| FW / BroxGD | `O(1 + LR²/ε)` | `R` (BroxGD also needs `L` for `K`) |
| this result | `O(1 + √(LR²/ε) + log(2 + Δ/ε + LR²/ε))` | `R`, `ε` |

The gain is a factor of about `√(LR²/ε)` once `LR²/ε ≳ log²(2 + Δ/ε)`. The result loses when `LR²/ε` is small but `Δ/ε` is huge, for example on nearly linear objectives, where FW needs `O(1)` calls.

The comparison establishes this gain. The literature search found no prior accelerated local-LMO bound, but these preprints are recent and fast-moving, so priority is not certain. The acceleration mechanism belongs to the repository's unpublished SplitBrox. What this theorem adds is a fairly standard, though carefully certified, removal of `f⋆` and `L` at additive logarithmic cost. The claim that can be made is the first accelerated oracle complexity found for exact local linear minimization that needs neither `f⋆` nor `L`.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
