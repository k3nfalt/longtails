# Novelty review: recursive momentum under affine variance and mean-squared smoothness

[`result`](../../LongTails/Theorems/RecursiveMomentumAffineVariance.lean) proves this guarantee for unnormalized STORM ([algorithm](../../LongTails/Algorithms/RecursiveMomentum.lean)) with constant parameters, one initial minibatch at `x₀`, and an output iterate chosen uniformly at random. The problem class is any `L`-smooth `f` on a separable Hilbert space with `f(x₀) − inf f ≤ Δ`. The oracle returns unbiased same-sample pairs `(g(x,ξ), g(y,ξ))` from IID samples, satisfying affine variance `E‖g(x)−∇f(x)‖² ≤ Γ²‖∇f(x)‖² + Λ²` and mean-squared smoothness (MSS) `E‖g(x)−g(y)‖² ≤ L̄²‖x−y‖²` ([setup](../../LongTails/Setups/AffineVarianceMeanSquaredSmooth.lean)). Under these assumptions it guarantees `E‖∇f(x_out)‖ ≤ ε`.

**Proved budget**, in pair calls; the ceiling formula bounds every call, `B + T`:

  `O(1 + Γ⁴ + Λ²/ε² + (L+L̄)(1+Γ)Δ/ε² + (L+L̄)ΛΔ/ε³)`

- **Parameters.** `L` is the smoothness of `f`, `L̄` the MSS constant, `Γ` the relative noise, `Λ` the additive noise, and `ε` the target expected gradient norm. Validity requires `L, ε > 0`; the others are `≥ 0`.
- **Simplification.** The `131Γ²` term is absorbed by `1 + Γ⁴`.
- **Relation between constants.** Jensen gives true smoothness `≤ L̄`, so `L + L̄ ≍ L̄` when `L` is chosen minimally.
- **Degenerate case.** At `Γ = 0` the class becomes bounded variance plus MSS. The bound is then the standard `O(1 + Λ²/ε² + L̄Δ/ε² + L̄ΛΔ/ε³)` of STORM/SPIDER, which is optimal by [Arjevani et al.](https://arxiv.org/abs/1912.02365) Thm 3. Any novelty therefore concerns `Γ > 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SGD under ABC/expected smoothness, [Khaled–Richtárik](https://arxiv.org/abs/2002.03329) (v3; TMLR 2023), Cor. 1, with `B = 1+Γ²`, `C = Λ²`, `A = 0`. *Covers the full setup with a weaker oracle.* | `O((1+Γ²)LΔ/ε² + LΛ²Δ/ε⁴)` → ours | At `Λ = 0`, by a factor `≍ ΓL/L̄` when `ΓL ≫ L̄` and `Γ³ε² ≲ L̄Δ`. For `Λ > 0`, `ε⁻⁴ → ε⁻³` when `ε ≲ LΛ/L̄`. **Worse** by a factor `≍ (1+Γ)L̄/((1+Γ²)L)` when `L̄ ≳ ΓL` | None | None (random-iterate expected norm in both) | Needs MSS and the pair oracle (2 gradients per call); adds a `Γ⁴` term; SGD uses only `L` |
| SPIDER under affine variance, [Chen–Zhou–Liang–Lu](https://arxiv.org/abs/2303.02854) (v2 Jun 2023; ICML 2023), Thm 4, `L₁ → 0`, step `≍ ε/L̄`. Also with minibatches of `b = Γ²` pairs (`Γ_b ≤ 1`, `Λ_b = Λ/Γ`, `L̄_b ≤ L + L̄/Γ`). *Same class.* | Plain: `O(Λ²/ε² + (1+Γ²)L̄Δ/ε² + (1+Γ)L̄ΛΔ/ε³)`. Minibatched: `O(Λ²/ε² + (Γ²L + ΓL̄)Δ/ε² + (ΓL+L̄)ΛΔ/ε³)` → ours | The `ε⁻³` coefficient falls by `(ΓL+L̄)/L̄`. The `ε⁻²` term falls by `≍ ΓL/L̄` when `ΓL ≫ L̄`, with no change for `ΓL ≲ L̄` | None (same class) | None | Adds `Γ⁴` (inessential once `Γ³ε² ≲ L̄Δ`); hidden `Ω(·)` constants of Thm 4 unchecked |
| Repository [`NormalizedStormExpectedSmoothness`](../../LongTails/Theorems/NormalizedStormExpectedSmoothness.lean) (ABC + MSS). *Overlap: `A = LΓ²`, `C = Λ²`.* | `O(1+Γ² + (L̄Δ+LΓ²Δ+Λ²)/ε² + L̄Δ(Λ+Γ√(LΔ))/ε³)` → ours | At `Λ = 0`, `ε⁻³ → ε⁻²`. For `Λ > 0`, the term `ΓL̄Δ√(LΔ)/ε³` is removed | Narrower: ABC → affine variance | None | `Γ²` initial term becomes `Γ⁴` |

**Reductions.**
- **Bounded-variance STORM/SPIDER** (Cutkosky–Orabona; [Jiang et al. 2610.01599](https://arxiv.org/abs/2610.01599), Thm 1) needs `sup‖∇f‖`, which is not available.
- **Minibatching Chen et al.** gives the `Γ²L` term in row 2.
- **SpiderBoost with relative-error refreshes** (my sketch, not a proof of impossibility). It needs `γLq ≲ 1` to transfer refresh-point gradients across an epoch, which leaves `≳ Γ²LΔ/ε²`.
- **New mechanism.** The step not covered by these reductions is a Lyapunov term `−2aγΓ²E‖∇f(x_t)‖²`. It charges the fresh relative noise to the next step's descent, so the momentum `a ≍ min(Γ⁻², ε²/Λ²)` averages only `Γ²` samples.
- **Proof ancestry.** STORM ([Cutkosky–Orabona 2019](https://arxiv.org/abs/1905.10018)) supplies the estimator and the standard error recursion.

**Search coverage (2026-10-18).**
- **Sources checked.** arXiv (API and web), NeurIPS/ICML/TMLR sources, Chen et al. Thm 4 and Khaled–Richtárik Cor. 1 (full text), META-STORM (bounded variance only), Upadhyay et al. [2605.15314](https://arxiv.org/abs/2605.15314) (normalized, distance-growth noise), and the trust-region SGC paper [2604.14017](https://arxiv.org/abs/2604.14017). The trust-region paper has no MSS, and its `ρ`-dependence was unchecked.
- **Not checked.** DASHA/MARINA frameworks in full.
- **Result.** No prior nonconvex guarantee linear in `Γ` was found.
- **Companion note.** Its baseline formulas agree with my reading. Its zero-respecting lower bounds `Θ(min{(1+Γ²)L, (1+Γ)L̄}Δ/ε²)` are unformalized sketches that I did not verify.
- **Chronology.** The result was introduced in commit `585d718` (2026-10-18).

**Conclusion**

**Yes: on Chen et al.'s affine-variance + MSS class, the proved complexity is better in a meaningful regime.** The strongest baselines are SGD (Khaled–Richtárik) and SPIDER under affine variance (Chen et al., ICML 2023, also minibatched). Under strong growth (`Λ = 0`):

| | Pair/gradient calls |
|---|---|
| SGD / minibatched SPIDER | `(1+Γ²)LΔ/ε²` / `(Γ²L+ΓL̄)Δ/ε²` |
| This result | `(1+Γ)L̄Δ/ε² + Γ⁴` |

This is a speedup `≍ ΓL/L̄` when `ΓL ≫ L̄` and `Γ³ε² ≲ L̄Δ`. For `Λ > 0`, the `ε⁻³` coefficient drops from `(ΓL+L̄)Λ` to `L̄Λ`. The result loses to SGD when `L̄ ≳ ΓL`, needs the pair oracle and MSS, and pays an extra `Γ⁴`.

The comparison proves these gains against the checked bounds. The search found no earlier guarantee linear in `Γ`, but that does not prove priority. The only evidence that `L̄ ≪ ΓL` actually occurs comes from convex least-squares instances, where other methods are faster anyway. The note's matching lower bound is unverified.

The claimable contribution is an improved upper bound on the oracle complexity of a published problem class, obtained with a simple Lyapunov modification of STORM that none of the checked standard reductions reproduces.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
