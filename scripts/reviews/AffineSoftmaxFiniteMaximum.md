# AffineSoftmaxFiniteMaximum: novelty assessment

The [theorem](../../LongTails/Theorems/AffineSoftmaxFiniteMaximum.lean) proves the following. Let `max_{i≤m} f_i` be minimized over the ball `B(x₀,R)`, where each component is convex, has gradients bounded by `G` and `L`-Lipschitz on the ball, and a constrained minimizer `x⋆` exists. The randomized [algorithm](../../LongTails/Algorithms/AffineSoftmaxFiniteMaximum.lean) returns a feasible point with `Pr{f_max(out) − f_max(x⋆) ≤ ε} ≥ 1−δ`. Its deterministic hard cap on calls to the exact single-component value/gradient oracle of the [setup](../../LongTails/Setups/SmoothFiniteMaximum.lean) is given below.

**Proved budget.** The parameters are: `m` components, gradient bound `G`, smoothness `L ≥ 0`, radius `R`, accuracy `ε`, and failure probability `δ`. Up to universal constants, the bound is

`O( log(2/δ) · log⁷(2+m+GR/ε+LR²/ε) · [ m + m(LR²/ε)^{1/3} + m^{3/4}(LR²/ε)^{1/2} + m^{6/7}(GLR³/ε²)^{2/7} + GR/ε ] )`.

This follows directly from `budget` (constant `2·10²¹`, `Nat.clog` powers). When `ε ≥ 2GR`, the algorithm returns `x₀`.

The rows below are compared in the normalized scaling `G=L=R=1`, `m=ε^{-α}`, ignoring polylogarithmic factors. In that scaling the new bound has order `ε^{-max{1, α+1/3, (6α+4)/7}}`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Accelerated linearization: Nesterov (2018) §2.3.1, as analyzed in [Carmon et al. COLT 2021](https://arxiv.org/abs/2105.01778) §1.1 and App. A.3 (arXiv v1, 4 May 2021) | `m(1+√(LR²/ε))` → the bound above | `mε^{-1/2}` → `mε^{-1/3}+m^{6/7}ε^{-4/7}`. Polynomially better iff `m ≫ ε^{-1/2}`. | None (constrained convex smooth components) | None. Converting a deterministic guarantee to `1−δ` is free. | Worse for `m ≪ ε^{-1/2}`: the new bound has an `ε^{-1}` term (`GR/ε`). It is also randomized, with `log⁷` and `log(1/δ)` factors. |
| [Carmon–Jambulapati–Jin–Sidford, SODA 2024](https://arxiv.org/abs/2311.10886), Thm 8.1 (arXiv v1, 17 Nov 2023) | `m(LR²/ε)^{1/3} + (GR/ε)²` → the bound above | `ε^{-2}` → `ε^{-(6α+4)/7}` for `m ≪ ε^{-5/3}`. Same order for `m ≳ ε^{-5/3}`. | Their condition `ε ≤ min{LR², G²/L}` is dropped. Small `L` was already covered by row 1, so this is not a substantive gain. | Expected error → probability `1−δ`. The SODA bound converts via Markov plus `O(log 1/δ)` repetitions and `O(m log 1/δ)` scoring, so this is no real gain. | SODA also handles the simplex setup and gives runtime bounds. The new result controls only queries and has larger polylogs. |
| Carmon et al. COLT 2021, arXiv Thm 2 (smooth case; the note calls it Thm 6, which is the proceedings numbering, unverified) | `m(GR/ε)^{2/3} + √m(GR/ε + √(LR²/ε))` → the bound above | Better for every `α>0` in this scaling. In general, better only if `L ≲ G²/ε`. | COLT assumes global assumptions, an unconstrained problem, and `‖x₀−x⋆‖≤R`. The new setup needs assumptions only on the ball. These classes are overlapping, not nested. | None. COLT has constant probability 99/100 and is amplifiable at the same cost. | Worse when `L ≫ G²/ε`. Example: `G=R=1, L=ε^{-2}` gives `≥ mε^{-1}` for the new bound against `mε^{-2/3}+√m ε^{-3/2}` for COLT. |

Taking the minimum over the three rows, the strict polynomial gain region is `ε^{-1/2} ≪ m ≪ ε^{-5/3}`, with gain exponent `min{(α−½)/7, (10−6α)/7}`. The gain is largest at `m = ε^{-3/2}`: `ε^{-2} → ε^{-13/7}`. The lower bound of COLT arXiv Thm 3, `Ω(m min{(GR/ε)^{2/3},(LR²/ε)^{1/3}} + min{(GR/ε)², √(mLR²/ε)})`, gives `ε^{-11/6}` at that point, so the upper–lower gap there shrinks from `1/6` to `1/42`.

**Reduction check and proof ancestry.** Substituting the SODA moving-Gibbs estimator into the known local-to-global proximal/multilevel framework does not give this rate. Batching does not either, since variance and cost scale together. The missing ingredient is the new centered numerator estimator combined with an unbiased geometric-product reciprocal, which achieves variance `O(L²r² + G²L²r⁴ log²m/ε²)` on SODA-size balls `r ≤ √(ε/(2L log m))`, which are larger than COLT's `ε/G`-scale balls. SODA §1.1 explicitly left variance reduction on such larger balls as future work. Proof ancestry, which is not counted as baselines:
- ball acceleration ([Carmon et al. 2020](https://arxiv.org/abs/2003.08078));
- [Carmon–Hausler NeurIPS 2022](https://arxiv.org/abs/2203.13225) for the proximal-gradient/MLMC outer loop;
- [Asi et al. 2021](https://arxiv.org/abs/2106.09481) for bias reduction;
- Moka–Kroese–Juneja (WSC 2019) for the reciprocal estimator.

These supply the outer loop. The variance bound and the radius balancing are the new parts. I spot-checked the Lean budget chain (`PublicBudget`, `successful_execution`, no `sorry`); I did not run the build or the comparator.

**Search coverage (6 Nov 2026).** I read the full COLT and SODA arXiv texts. I checked the Semantic Scholar citation lists of both papers through Nov 2026. I read the main theorems of the following and found no competitor:
- Gladin et al. arXiv 2509.24894v4: SGD on a LogSumExp surrogate, about `ε^{-4}`;
- Gladin–Popova–Babinskii arXiv 2609.32872v1: needs a near-active condition and is `ε^{-2}`;
- Yu et al. 2403.03562: `ε^{-1}`;
- Lin–Zhang 2601.14680: full-batch, or quadratic growth.

Variance-reduced primal–dual methods were excluded because of COLT's noted `Ω(m)` complexity–variance product for `∇_p`. Venue status of the 2026 preprints, and OpenReview items, remain unverified. The companion note's numerical claims match the Lean statement and the sources. Only its theorem numbering differs, because it uses the proceedings numbering.

## Conclusion

**Yes. For intermediate numbers of components, the proved query complexity is polynomially better than every applicable bound I could find.** The strongest baselines are AGD on the linearization and the SODA 2024 ball method of Carmon et al. With `G=L=R=1`, `m=ε^{-α}`, and polylogarithms ignored:

| | `m ≪ ε^{-1/2}` | `ε^{-1/2} ≪ m ≪ ε^{-5/3}` | `m ≳ ε^{-5/3}` |
|---|---|---|---|
| best prior | `mε^{-1/2}` (better) | `min{mε^{-1/2}, ε^{-2}}` | `mε^{-1/3}` |
| this result | `ε^{-1}` | `m^{6/7}ε^{-4/7}` | `mε^{-1/3}` (same) |

The gain is at most a factor of `ε^{-1/7}`, at `m=ε^{-3/2}`, and it sits against a `log⁷` overhead and a `2·10²¹` constant. It is therefore asymptotic, not practical. The result also loses to the COLT 2021 bound when `L ≫ G²/ε`, and loses to AGD for small `m`.

The comparison does establish the gain. Priority is supported by citation tracing that found no later or concurrent improvement, but that search cannot rule out unindexed work. The mechanism behind the gain is a genuinely new low-variance gradient estimator for larger balls, which the SODA authors had left open; the gain does not come from tuning.

The contribution that can be claimed is a new upper bound for smooth finite maxima that narrows the gap to the known lower bound in the regime `ε^{-1/2} ≪ m ≪ ε^{-5/3}`. It comes with no optimality and no practical speedup.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
