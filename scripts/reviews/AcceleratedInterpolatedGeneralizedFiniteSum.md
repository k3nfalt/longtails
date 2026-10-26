# Novelty assessment: AcceleratedInterpolatedGeneralizedFiniteSum

The [theorem](../../LongTails/Theorems/AcceleratedInterpolatedGeneralizedFiniteSum.lean) concerns `F = n⁻¹ Σᵢ fᵢ` on a finite-dimensional Hilbert space. Each `fᵢ` is convex and differentiable with a continuous, symmetrically `(L₀,L₁)`-smooth gradient, the components share a minimizer `x⋆`, and `‖x₀ − x⋆‖ ≤ R` ([setup](../../LongTails/Setups/InterpolatedGeneralizedFiniteSum.lean)). Using only exact component-gradient queries, the randomized [ComponentEnvelope algorithm](../../LongTails/Algorithms/ComponentEnvelope.lean) returns its final snapshot `x̂`, and the theorem proves `P{F(x̂) − F(x⋆) ≤ ε} ≥ 2/3`.

**Complexity.** Here `n` is the number of components, `L₀ > 0` and `L₁ ≥ 0` are the smoothness constants, `R > 0` bounds the initial distance, and `ε > 0` is the accuracy. The proved budget is exactly `⌈2³⁰[…]·log(…)⌉`. Writing `κ = L₀R²/ε` only to abbreviate the display, it is

  **O( [ n(1 + L₁²R²) + √(n L₀R²/ε) ] · log(2 + n + L₀R²/ε + L₁²R²) )** component-gradient calls.

The updates need `n, L₀, L₁, R, ε`. Below, `ℓ = log(2 + n + κ + L₁²R²)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gorbunov et al., [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/f21a5fedfbcb55406ddaf51cf90d494a-Abstract-Conference.html), [arXiv v2](https://arxiv.org/html/2409.14989v2), Thm 7.2 / App. H.1, `(L₀,L₁)`-SGD. Assumption 7.1 is the **same class**. | Telescoping (H.1) bounds `Σₖ E min{νη/(8nL₁²), η(F(xᵏ)−F⋆)/(2L₀)} ≤ R²`. With a uniformly random index and Markov's inequality, this gives `O(L₀R²/ε + nL₁²R²)` at probability 2/3; I derived this conversion myself. → `O([n(1+L₁²R²) + √(nL₀R²/ε)]ℓ)` | `κ → √(nκ)·ℓ`. The new bound is smaller when `L₀R²/ε ≥ C·n·ℓ²` and `L₀R²/ε ≥ C·nL₁²R²·ℓ`, with a speedup of order `√(L₀R²/(nε))/ℓ`. **Worse** when `L₀R²/ε ≲ n` (an unavoidable `n` term appears) or when `nL₁²R²` dominates (an extra factor `ℓ`). | None: same class. | Output changes from a uniformly random SGD iterate to the final snapshot. Both are probability-2/3 guarantees, and both need `L₀,L₁` in the updates. | The new updates also need `R` (projection onto `B̄(x₀,R)`) and `ε` (through the smoothing `μ = L₀ + 8nL₁²ε`). In SGD, `R` and `ε` enter only through the iteration count. |
| Tyurin, [arXiv 2508.06884v2](https://arxiv.org/abs/2508.06884) (v2, 21 May 2026), eq. (8). Applied to `F` with full gradients at `n` calls each. **Applies only when `F` is `(L₀,L₁)`-smooth**, which I verified for `d = 1` (common minimizer ⇒ all `fᵢ′` share a sign ⇒ `|F′| = mean|fᵢ′|`). | `n·O(√(L₀R²/ε) + L₁²R²)` → `O([n(1+L₁²R²) + √(nL₀R²/ε)]ℓ)` | On the `d = 1` overlap: smaller when `n ≥ Cℓ²` and `√(L₀R²/ε) ≥ C·L₁²R²·ℓ`, with a speedup of up to `√n/ℓ`. For general `d`, the mean need not inherit component `(L₀,L₁)`-smoothness; I verified no reduction, so the bounds are **not comparable** there. | Covers `d > 1` (mean smoothness not required). | Deterministic last iterate → probability-2/3 final snapshot (a loss). | Extra log factor on the shared `nL₁²R²` term. Tyurin's Thm 4.3 sharpens the `L₁` term further, using an initial-gap bound. |
| Lan–Li–Zhou, VARAG, [NeurIPS 2019](https://arxiv.org/abs/1905.12412), Thm 1. **Special case `L₁ = 0` only.** | With `D₀ = O(L₀R²)` (interpolation), the bound is `O(n log n + √(nL₀R²/ε))` for `κ > n` and `O(n log κ)` otherwise, for the expected gap. → `O((n + √(nκ))ℓ)` | **Worse** by a factor `ℓ` on `√(nκ)`. | — | Expected gap → probability 2/3 (an equivalent conversion via Markov). | The selected result exists to handle `L₁ > 0`. |

**Reduction check.** Running Katyusha/VARAG on the component Moreau envelopes requires an exact prox oracle, which is stronger than the gradient oracle here. Charging each gradient-based inner solve its worst-case cost multiplies the whole outer complexity by `(1 + L₁²R²)`. The genuinely new step is the amortized charge `qᵢ(c)² ≤ (2L₁²/μ)[hᵢ(c) − hᵢ(x⋆)]`, which is summed against the accelerated potential. That makes the curvature cost additive. One alternative reduction remains unchecked: SGD warm-up into the region `F − F⋆ ≲ L₀/(nL₁²)`, followed by accelerated variance reduction there. It would need pathwise localization of non-monotone iterates. The proof ancestry is the Moreau-envelope/Catalyst smoothing, the Katyusha/VARAG coupling, and Gorbunov et al.'s generalized-smooth descent inequalities. None of them gives this end-to-end bound.

**Search coverage.** I searched on 2026-10-26 (UTC) across arXiv and the ICLR/ICML/NeurIPS proceedings. Queries covered finite sums, variance reduction, acceleration, interpolation, and `(L₀,L₁)`/generalized smoothness. I found no prior bound that combines finite-sum acceleration with component `(L₀,L₁)`-smoothness. Lobanov [2608.04884](https://arxiv.org/abs/2608.04884) is deterministic or coordinate-based, judged from its abstract only. ARC-SG [2609.06555](https://arxiv.org/abs/2609.06555) assumes sub-Gaussian noise and objective smoothness; I did not read its theorems. Tyurin's ICML 2026 status and the OpenReview pages were not verified. The result was introduced in commit `8e7be95` (2026-10-26), so every cited work predates it. The companion note's claims and its Gorbunov-derived baseline agree with the Lean statement, and I found no mismatch.

**Conclusion**

**Yes: for high accuracy, the proved complexity beats the only end-to-end baseline I found for this exact class.** That baseline is `(L₀,L₁)`-SGD (Gorbunov et al., ICLR 2025), converted to a probability-2/3 guarantee:

| | component-gradient calls |
|---|---|
| clipped SGD (same class) | `L₀R²/ε + nL₁²R²` |
| this result | `[n(1+L₁²R²) + √(nL₀R²/ε)] · log(2+n+L₀R²/ε+L₁²R²)` |

The new bound wins once `L₀R²/ε` exceeds both `n·log²` and `nL₁²R²·log`. For example, with `n` and `L₁R` fixed and `ε → 0`, the cost drops from order `1/ε` to `√(n/ε)·log(1/ε)`. It loses at low accuracy (`L₀R²/ε ≲ n`) and pays an extra logarithm when the curvature term `nL₁²R²` dominates. In one dimension, where full-gradient generalized-smooth acceleration applies to the mean, it also saves up to a factor `√n/log`.

The naive reductions do not reach this bound: smoothing with inner gradient solves gives a multiplicative `(1 + L₁²R²)` factor. The summed-gap accounting is what makes that factor additive. The search found no competitor, but that does not prove priority, and one localization-based alternative remains unchecked.

What can be claimed is the first accelerated (`√(nκ)`-type) gradient-only bound I could find for interpolated convex finite sums with component `(L₀,L₁)`-smoothness. It requires known parameters, gives a fixed-confidence guarantee, and has no optimality claim.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
