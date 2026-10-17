# Novelty review: normalized STORM under expected-smoothness (ABC) noise

[`result`](../../LongTails/Theorems/NormalizedStormExpectedSmoothness.lean) proves the following. Take an unbiased, jointly measurable, same-sample pair oracle with IID samples, mean-squared smoothness (MSS) constant `L`, and ABC variance `E‖g(x)−∇f(x)‖² ≤ 2A(f(x)−lower)+C` ([setup](../../LongTails/Setups/ExpectedSmoothnessNonconvex.lean)). Then normalized STORM with an initial minibatch ([algorithm](../../LongTails/Algorithms/NormalizedStorm.lean)), outputting a uniformly random iterate, achieves `E‖∇f(x_out)‖ ≤ ε`.

**Proved budget**, in pair calls (each call is one sample and two gradients):

  `O(1 + A/L + (LΔ + AΔ + C)/ε² + LΔ√(AΔ + C)/ε³)`

- **Parameters.** `L` is the MSS constant, which also bounds the smoothness of `f`. `Δ ≥ f(x₀) − lower`. `A, C ≥ 0` are the ABC constants. `ε` is the target `E‖∇f‖`.
- **Simplification.** This uses `√(4AΔ + 2Aε²/L + C) ≤ 2√(AΔ+C) + ε√(2A/L)` and `Δ√(AL)/ε² ≤ (A+L)Δ/ε²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SPIDER/STORM, bounded variance σ² ([Fang et al. 2018](https://arxiv.org/abs/1807.01695); [Cutkosky–Orabona 2019](https://arxiv.org/abs/1905.10018)); lower bound [Arjevani et al., Thm 3](https://arxiv.org/abs/1912.02365). *Applies only when `A = 0`.* | `O(1 + (LΔ+σ²)/ε² + LΔσ/ε³)` → the same with `C = σ²`, `A = 0` | None: same order, which is optimal | bounded variance → ABC: variance may grow with `f − lower` | None | None on the overlap |
| [Chen–Zhou–Liang–Lu, ICML 2023](https://arxiv.org/abs/2303.02854), Thm 4: SPIDER under affine variance `Γ²‖∇f‖²+Λ²`. MSS lies in their `𝔼ℒ*_sym` class as `L₁↓0`. *Overlap: `A = LΓ²`, `C = Λ²`.* | Our retuning of their conditions: `O((LΔ(1+Γ²)+Λ²)/ε² + LΔ(1+Γ)Λ/ε³)` → `O(1+Γ²+(LΔ(1+Γ²)+Λ²)/ε² + LΔ(Λ+Γ√(LΔ))/ε³)` | Mixed. If `Γ ≥ 1` and `Λ ≥ √(LΔ)`, the `ε⁻³` term falls by a factor `≍ min(Γ, Λ/√(LΔ))`. **Worse** when `Λ ≪ Γ√(LΔ)/(1+Γ)`: at `Λ → 0`, theirs is `ε⁻²`, ours `ε⁻³` | affine variance → ABC, a strictly larger class (example below) | None | Uses the pair oracle (they use minibatches); loses `ε⁻¹` near strong growth |
| [Upadhyay–Fazla–Hashemi, arXiv 2605.15314](https://arxiv.org/abs/2605.15314) (May 2026), Thm 2(i): NSTORM under Blum–Gladyshev (BG‑0) noise and MSS. *Covers the full setup*, since MSS + ABC give `var(x) ≤ 2L²‖x−x₀‖² + 2(2AΔ+C)`. | With `γ₀=√(Δ/L)` and `LΔ ≥ 1` (their bound is not scale-invariant): `O((LΔ)²/ε⁴ + (AΔ+C)LΔ/ε²)` → ours | `ε⁻⁴ → ε⁻³`. By AM–GM ours is never worse when `1 ≤ LΔ` and `ε² ≤ LΔ`; at fixed parameters the gain grows like `ε⁻¹` | BG noise class → ABC. The classes are incomparable in general; on this overlap ABC is the extra structure exploited | None (both use a random iterate) | Requires ABC; BG also covers distance-driven noise, where `Θ(ε⁻⁴)` is tight ([Fazla et al. 2604.16620](https://arxiv.org/abs/2604.16620)) |
| [Khaled–Richtárik, TMLR 2023](https://arxiv.org/abs/2002.03329), Cor. 1: SGD under ES/ABC. *Covers the full setup with a weaker oracle.* | `O(LΔ/ε² + LΔ(AΔ+C)/ε⁴)` → ours | Leading term falls by a factor `≍ √(AΔ+C)/ε` when `ε ≤ min(√(AΔ+C), √(LΔ))` | None: SGD needs neither MSS nor pair queries | None (min/random-iterate criterion in both) | Needs MSS and the same-sample pair oracle; costs 2 gradients per call; SGD uses `L_F ≤ L` |

**Chen et al. comparison.** Their Theorem 4 requires `B ≳ max(Λ²/ε², Γ²q²)`, `B′ ≳ q` and `γ = ε/(8L)` as `L₁ → 0`. We chose `q = max(1, Λ/(max(1,Γ)ε))`. The absolute constants hidden in their `Ω(·)` were not checked in their appendix.

**Strict-scope example.** Let `f(x,ξ) = √(1+x²) + cos x + ξΦ(x)`, with Rademacher `ξ` and `Φ′(x) = (1+x²)^{1/4}`.
- MSS holds with `L ≈ 2.03`, because `|F″| ≤ 2` and `|Φ″| ≤ 0.31`.
- ABC holds with `A = ½`, `C = 0`, `lower = −1`.
- The variance `√(1+x²)` is unbounded while `|∇F| ≤ 2`, so no affine bound holds.

Conversely, the note's least-squares-plus-bounded-penalty example and its PSD-quadratic example already satisfy affine variance. In both, the variance depends only on the range-of-`H` component, which `‖∇F‖` controls. The quadratic example has `Λ = 0`, so Chen et al. give `ε⁻²` there, though with `Γ ~ L/λ⁺`. We did not check whether the softplus example lies outside the affine class.

**Mechanism and proof ancestry.** No standard reduction gives the result:
- ABC does not imply affine variance.
- The sublevel-set and ball reductions give only `ε⁻⁴`.

The new step is short. The STORM error recursion uses the variance only in total expectation, which is affine in `E f(x_{t+1})`. An induction keeps `E f(x_t) − lower ≤ 2Δ + ε²/L`. The standard normalized-STORM tuning then applies with `σ² ← 2A(2Δ+ε²/L)+C`. The proof ancestry is the bounded-variance normalized-STORM analysis ([Cutkosky–Mehta 2020](https://arxiv.org/abs/2002.03305)).

**Search coverage.** On 2026-10-17 we searched arXiv, the proceedings and Google-indexed sources for STORM, SPIDER, PAGE and MARINA, and for momentum-VR under ABC/ES, affine, relaxed and BG noise. We read Chen et al. Thm 4, Khaled–Richtárik Cor. 1, Upadhyay et al. Thm 2, Reisizadeh et al. 2023 (bounded variance) and PStorm (bounded variance).
- **Introduction date.** The result was added on 2026-10-16 (commit `a1cfca4`). Every comparator above predates it.
- **Not read.** The full text of Fazla et al. and of arXiv 2610.01599/2610.13799, which appear to assume bounded variance.
- **Discrepancy with the note.** The companion note claims only SGD-type `ε⁻⁴` guarantees were known for its motivating instances. It omits Chen et al., who already give `ε⁻³` VR under affine variance, which covers those checked instances.

**Conclusion**

**Partly. ε⁻³ is new for the full ABC class, but on the instances the note uses as motivation an ε⁻³ method was already known.**

Against the methods that apply to the whole ABC + MSS class, the gain is real:

| Method | Budget (ABC + MSS) |
|---|---|
| SGD (Khaled–Richtárik) | `LΔ(AΔ+C)/ε⁴` |
| BG-noise NSTORM (Upadhyay et al.) | `(LΔ)²/ε⁴` |
| **This result** | `LΔ√(AΔ+C)/ε³` |

The overlap with SPIDER under affine variance `Γ²‖∇f‖²+Λ²` (Chen et al., ICML 2023) is the decisive comparison. That class contains the note's least-squares and quadratic examples. There, this result wins only when `Γ ≥ 1` and `Λ ≥ √(LΔ)`, and it loses a factor `1/ε` near `Λ = 0`. The instances where only this result applies, ABC without affine variance, are verified here only through an artificial one-dimensional example.

The proof adds one short induction on `E f(x_t)` to the standard normalized-STORM analysis. The literature search did not find a prior `ε⁻³` theorem under ABC, but finding none does not prove priority. What can be claimed is a modest scope extension: the `ε⁻³` STORM rate holds under function-value-dependent variance, while its natural instances mostly already had `ε⁻³` guarantees.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
