# Novelty review: recursive momentum with a gap-dependent initial batch

[`result`](../../LongTails/Theorems/RecursiveMomentumGapBatch.lean) proves a guarantee for unnormalized constant-parameter STORM ([algorithm](../../LongTails/Algorithms/RecursiveMomentumGapBatch.lean)) on a separable Hilbert space ([setup](../../LongTails/Setups/AffineVarianceMeanSquaredSmooth.lean)). The algorithm uses `b₀` diagonal calls at `x₀` and outputs an iterate chosen uniformly at random. The objective `f` is `L`-smooth with `f(x₀) − inf f ≤ Δ`. The oracle returns IID same-sample unbiased pairs satisfying affine variance `E‖g(x)−∇f(x)‖² ≤ Γ²‖∇f(x)‖² + Λ²` and mean-squared smoothness (MSS) `E‖g(x)−g(y)‖² ≤ L̄²‖x−y‖²`. Under these assumptions the output satisfies `E‖∇f(x_out)‖ ≤ ε`.

**Proved budget.** The cost is counted in pair calls. The exact budget is `⌈8Λ²/ε² + 64Γ(L+L̄)Δ/ε²⌉ + 1 + ⌈20(1+3Γ+6Λ/ε)(L+L̄)Δ/ε²⌉`, which simplifies to

  `N = O(1 + Λ²/ε² + (1+Γ)(L+L̄)Δ/ε² + (L+L̄)ΛΔ/ε³)`.

All parameters are public. The validity conditions are `L, ε > 0` and `L̄, Γ, Λ, Δ ≥ 0`.

**Key change.** This result differs from the repository's [`RecursiveMomentumAffineVariance`](../../LongTails/Theorems/RecursiveMomentumAffineVariance.lean) (commit `585d718`, 2026-10-18) only in how the start-up is handled. That theorem's exported budget contains an ε-independent `5Γ⁴ + 131Γ²`. Here, a new lemma ([variance proof](../../LongTails/Proofs/RecursiveMomentumGapBatchVariance.lean)) uses MSS together with a nearby low-gradient point to bound the initial variance by `2Λ² + 12Γ(L+L̄)Δ`. The naive bound `2LΓ²Δ + Λ²` would instead add a `Γ²LΔ/ε²` term.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SGD, [Khaled–Richtárik](https://arxiv.org/abs/2002.03329), Cor. 1. ABC with `A=0`, `B=1+Γ²`, `C=Λ²`. *Covers the full setup with a weaker oracle* | `O(1+(1+Γ²)LΔ/ε² + LΛ²Δ/ε⁴)` → `O(1+Λ²/ε²+(1+Γ)(L+L̄)Δ/ε²+(L+L̄)ΛΔ/ε³)` | At `Λ=0`, gain ≍ `ΓL/(L+L̄)` when `Γ ≫ 1` and `L̄ ≪ ΓL`, at every ε. For `Λ>0`, `ε⁻⁴ → ε⁻³` when `ε ≲ LΛ/(L+L̄)`. **Worse** when `L̄ ≳ ΓL` | None | None: both bound the expected norm at a random iterate | Needs MSS and same-sample pairs (2 gradients per call); SGD needs neither `L̄` nor pairs |
| SPIDER under affine variance, [Chen–Zhou–Liang–Lu](https://arxiv.org/abs/2303.02854) (ICML 2023), Thm 4, with `L₁=0`. Minibatched form from the [earlier review](RecursiveMomentumAffineVariance.md). *Same class* | `O(Λ²/ε² + (Γ²L+ΓL̄)Δ/ε² + (ΓL+L̄)ΛΔ/ε³)` → same new bound | `Γ²L → (1+Γ)(L+L̄)` in the `ε⁻²` term. `(ΓL+L̄)Λ → (L+L̄)Λ` in the `ε⁻³` term | None | None | Hidden `Ω(·)` constants in Thm 4 not rechecked by me |
| Repository `RecursiveMomentumAffineVariance` (2026-10-18). *Identical setup* | `O(1+Γ⁴+Λ²/ε²+(1+Γ)(L+L̄)Δ/ε²+(L+L̄)ΛΔ/ε³)` → same without `Γ⁴` | Removes the additive `Γ⁴`. This is an order gain only when `Γ⁴ ≫ Λ²/ε² + (1+Γ)(L+L̄)Δ/ε² + (L+L̄)ΛΔ/ε³`. The Lean lemma `budget_lt_existing` states strict inequality everywhere | None | None | None: same algorithm family, oracle and output |

**Reductions and proof ancestry.** I found no standard reduction that reproduces this bound:

- Bounded-variance STORM or SPIDER needs `sup‖∇f‖`.
- Minibatching Chen et al. leaves a `Γ²L` term.
- The naive gap bound leaves a `Γ²D` batch.

The ancestry is as follows:

- [Cutkosky–Orabona](https://arxiv.org/abs/1905.10018) supplies the estimator.
- The predecessor's Lyapunov recursion supplies the `(1+Γ)` dependence.
- The new pieces are the MSS gap-transfer lemma and a finite-horizon error sum, which drops the predecessor's requirement `T ≥ 16/a`.

**Search coverage (2026-11-26).** I searched arXiv and the web for STORM, SPIDER, SARAH and recursive momentum under affine variance, strong growth or relative noise, and for lower bounds under relative noise. The papers checked were:

- [Jiang et al. 2610.13799](https://arxiv.org/abs/2610.13799): bounded variance only, no `Γ`.
- [Upadhyay et al. 2605.15314](https://arxiv.org/abs/2605.15314) and [Fazla et al. 2604.16620](https://arxiv.org/abs/2604.16620): distance-growth noise, an incomparable class. For 2604.16620 I read only the abstract.

I took Chen et al.'s Γ-dependence from the earlier review's full-text reading. I did not re-derive it from their appendix. I found no published nonconvex guarantee that is linear in `Γ`. The companion note's citations and formulas agree with what I checked. Its zero-respecting lower-bound sketch is unformalized and I did not verify it. I did not run a build or the axiom audit.

**Conclusion**

**The rate is unchanged from the repository's previous theorem; what is new is removing its ε-independent `Γ⁴` start-up term.** The strongest published baselines are SGD under ABC noise and SPIDER under affine variance (Chen et al.). At `Λ = 0`:

| | Calls at `Λ=0` |
|---|---|
| SGD | `(1+Γ²)LΔ/ε²` |
| Previous repository theorem | `Γ⁴ + (1+Γ)(L+L̄)Δ/ε²` |
| This result | `1 + (1+Γ)(L+L̄)Δ/ε²` |

The advantage over SGD requires `L̄ ≪ ΓL`, and this result now delivers it at every accuracy. For example, at `L=L̄=1` and `Δ/ε²=Γ`, the counts are `Γ³` for SGD, `Γ⁴` for the previous theorem and `Γ²` for this one. When `L̄ ≳ ΓL` it is no better than SGD, and it always needs MSS and same-sample pairs.

The comparison establishes these gains against the checked bounds. Priority in the literature is plausible, since I found no published guarantee linear in `Γ`, but this is not proved. The improvement in `Γ`-dependence over published work was already delivered by the predecessor. The only new gain is an additive term that matters when `Γ⁴` exceeds the accuracy-dependent cost, roughly `ε² ≳ (L+L̄)Δ/Γ³`. Natural instances with `L̄ ≪ ΓL` remain undocumented, because multiplicative noise gives `L̄ ≈ √(1+Γ²)L`.

What can be claimed is a cleaner affine-variance STORM bound: the predecessor's linear-in-`Γ` rate without any accuracy-independent `Γ⁴` start-up, obtained through a short MSS-based initial-variance lemma.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
