# MedianFirstMomentNonconvex: novelty assessment

[`result`](../../LongTails/Theorems/MedianFirstMomentNonconvex.lean) proves the following. Let `f : ℝᵈ → ℝ` be `L`-smooth with `f(x₀) − inf f ≤ Δ`. Its unbiased, jointly measurable paired oracle `(g(x,ξ), g(y,ξ))` is IID, with centered noise `ζ = g − ∇f` satisfying three conditions: `E‖ζ(x)‖ ≤ σ`; `E‖ζ(x) − ζ(y)‖ ≤ Λ‖x−y‖`; and coordinatewise marginal symmetry at each fixed `x` ([setup](../../LongTails/Setups/SymmetricFirstMomentNonconvex.lean)). Under these conditions, coordinatewise median-of-three estimators fed into the normalized dyadic variance-reduction method return a uniformly random iterate with `E‖∇f(x_out)‖ ≤ ε` ([algorithm](../../LongTails/Algorithms/MedianGradient.lean)).

**Complexity** (paired queries; each query costs two gradient evaluations). Here `L` is smoothness, `Δ` the initial gap, `σ` the first-moment noise bound, `Λ` the first-moment centered coupling constant, and `ε` the target accuracy, with `L, ε > 0` and `Λ, σ, Δ ≥ 0`:

  N = O( log²(2 + LΔ/ε²) · (1 + (LΔ + σ²)/ε² + ΛσΔ/ε³) ).

This is derived from the proved budget `3⌈14400(1+log₂(2+16LΔ/ε²))²(1 + (LΔ+σ²)/ε² + ΛσΔ/ε³)⌉`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Median-of-3 + SGD: [Ghadimi–Lan 2013](https://arxiv.org/abs/1309.5549), Cor. 2.2, with the elementary median bound `E‖med − ∇f‖² ≤ 3σ²` (cf. [Puchkin et al., AISTATS 2024](https://proceedings.mlr.press/v238/puchkin24a.html), Prop. 4.1) | `O(1 + LΔ/ε² + LΔσ²/ε⁴)` → `N` | Stochastic term `LΔσ²/ε⁴ → ΛσΔ/ε³·log²(2+LΔ/ε²)`. The gain survives when `ε·log²(2+LΔ/ε²) ≪ Lσ/Λ` and `σ² ≳ ε²` | None (same class) | None (random iterate in both) | Adds a log² factor; worse when `Λ ≫ Lσ/ε`. |
| [Fradin–Sadiev–Condat–Richtárik, arXiv:2512.18713v2](https://arxiv.org/abs/2512.18713) (Mar. 2026), Thm. 4.2 with `q = 1`. **Special case:** requires a central moment `σ_p` with `p ∈ (1,2]` | `O((σ_p/ε)^{p/(p−1)} + (L+Λ)Δ/ε² + ΛΔσ_p^{p/(p−1)}/ε^{2+p/(p−1)})` → `N` with `σ ≤ σ_p` | Accuracy exponent `2 + p/(p−1) ≥ 4 → 3` (up to log²) | First moment only, `p = 1` (no `p > 1` moment) | None | Requires coordinatewise symmetry, which Fradin et al. do not. Their Thm. 3.2 lower bound shows that without symmetry the ε⁻⁴-type exponent is unavoidable. |
| Standard reduction: median-of-3 + [SPIDER (Fang et al., NeurIPS 2018)](https://arxiv.org/abs/1807.01695), Thm. 1. **Special case:** raw mean-squared smoothness `E‖g(x)−g(y)‖² ≤ L̄²‖x−y‖²` | `O(L̄σΔ/ε³ + σ²/ε² + σ/ε)` → `N` (on overlap `Λ ≤ 2L̄`, `L ≤ L̄`) | None: same order. Loses log² unless `Λ·log²(2+LΔ/ε²) ≪ L̄` | Covers instances with infinite second-moment increments | None | None beyond the log² factor. The median is 1-Lipschitz in ℓ∞ per coordinate, so the median oracle is `√3L̄`-mean-squared smooth with variance `≤ 3σ²`. |
| Standard reduction: median of three paired *differences* plus median anchors, SPIDER-type estimator. **Special case:** each pair difference `ζ_j(x)−ζ_j(y)` is symmetric (e.g. jointly sign-symmetric noise fields); sketch, constants unchecked | `O((L+Λ)σΔ/ε³ + σ²/ε² + σ/ε)` via SPIDER Thm. 1 with averaged constant `O(L+Λ)` → `N` | Factor up to `L/Λ` when `Λ·log² ≪ L`. A centered VR analysis would likely remove this; not checked | Pointwise symmetry instead of pairwise symmetry | None | Same oracle; this reduction avoids the log² factor. |

**Reduction check and mechanism.** The ε⁻³ rate follows routinely whenever the noise has L² mean-squared smoothness (row 3) or pairwise-symmetric differences (row 4). Liu–Zhang–Zhou ([COLT 2023](https://proceedings.mlr.press/v195/liu23c.html), Thm. 4) need almost-sure samplewise Lipschitz gradients and `p > 1`, so they fall under row 3. The genuinely new step is the median replacement inequality `‖m(a,b,c) − m(a′,b,c)‖² ≤ ‖a−a′‖‖b−c‖` (with `E‖m‖² ≤ 3σ²`). It turns L¹ coupling into the half-Hölder L² bound `E‖Δ‖² ≤ 18Λσ‖x−y‖`. A SPIDER-type method under that Hölder bound only reaches about ε^{−3.5}. ε⁻³ needs the repository's own dyadic Hölder method ([DyadicVarianceReductionHolder](../../LongTails/Theorems/DyadicVarianceReductionHolder.lean)), rerun in centered form because the raw-Hölder theorem would pick up an `L²‖x−y‖²` term. That dyadic result is proof ancestry, not published literature.

**Search coverage.** As of 2026-10-18 UTC, I searched arXiv and PMLR/NeurIPS sources on heavy-tailed variance reduction, symmetric-noise median/sign methods and similarity-based normalized SGD with momentum variance reduction (NSGD-MVR). I read the theorem texts of Liu–Zhang–Zhou, Puchkin et al., SPIDER, and the Fradin et al. abstract and §4. I did not check whether Fradin et al.'s lower-bound construction is symmetric, the companion note's quantization example, or the Armacki and Vukovic–Jakovetic citations.

Two discrepancies with the companion note. First, Puchkin et al.'s Corollary 5.3 is a quasi-convex clipped-SGD result, so the nonconvex ε⁻⁴ baseline requires composing it with Ghadimi–Lan. Second, the note does not mention row 3's reduction. The result was introduced in commit `c25d577` (2026-10-18), so all cited works predate it.

## Conclusion

**The rate improves only on a narrow slice of the stated class; on the natural instances, standard reductions already give ε⁻³.**

Against the strongest checked end-to-end literature bound on the full class (median-of-three SGD), the improvement is real:

  `LΔσ²/ε⁴  →  log²(2+LΔ/ε²)·ΛσΔ/ε³`.

Fradin et al. cannot reach first moments at all. Their lower bound shows the symmetry assumption is what makes ε⁻³ possible.

However, median-of-three is unbiased and 1-Lipschitz per coordinate under the same symmetry. So median-of-three plus SPIDER already gives `O(L̄σΔ/ε³ + σ²/ε²)` whenever the raw increments are mean-squared smooth. Taking medians of paired differences does the same when noise differences are symmetric, which covers additive or multiplicative symmetric heavy-tailed noise. On those overlaps this theorem only matches them, with an extra log² factor.

What is established is a new mechanism: the median replacement inequality combined with a centered dyadic Hölder analysis. Its rate advantage is confined to oracles with infinite second-moment increments and pointwise-but-not-pairwise symmetry. The only evidence those occur is the note's constructed dithered-quantization example, which I did not verify. The defensible claim is an ε⁻³·log² guarantee for that niche class, without a verified lower bound.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
