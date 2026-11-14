# Randomized lower bound for convex (L₀,L₁)-smooth minimization

[`result`](../../LongTails/Theorems/FullGeneralizedSmoothConvexLowerBound.lean) proves that, in the setup [GeneralizedSmoothConvexFull](../../LongTails/Setups/GeneralizedSmoothConvexFull.lean), every adaptive randomized algorithm with exact gradient-only access fails to reach `E[f(x̂) − f(x⋆)] ≤ ε` (with integrability required) at every fixed budget `b ≤ ⌊(√(L₀R²/ε) + L₁R/log(2+L₁R))/2²³⌋`. The setup imposes no algorithm restriction, and all parameters are public. The hard instance depends on the algorithm and on `b`, but not on the realized seed.

Here f is convex with a differentiable gradient satisfying `‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖`, and `‖x⁰ − x⋆‖ ≤ R` for some minimizer x⋆. The result is valid for `L₀,R,ε > 0`, `L₁ ≥ 0`, `ε ≤ L₀R²/16` and `d ≥ ⌈2⁴⁴(1+L₁R+√(L₀R²/ε))⁵⌉`. The necessary number of gradient calls is

  **N = Ω(1 + √(L₀R²/ε) + L₁R / log(2+L₁R)).**

The best upper bound is O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R)), from Everest I, Thm 3.7. The repository transfers it in [FullGeneralizedSmoothUpper](../../LongTails/Proofs/FullGeneralizedSmoothUpper.lean) via [RadiusFreeSherpa](../../LongTails/Algorithms/RadiusFreeSherpa.lean). The remaining gap is a factor log²(2+L₁R) on the L₁R term. In a lower bound, a larger necessary budget is stronger.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, [Descending Everest I](https://arxiv.org/abs/2610.21461), Thm 4.10 (arXiv v1 15 Oct 2026, v2 5 Nov; preprint, prior) | Ω(1+√(L₀R²/ε)+L₁R/√log(2+L₁R)) → Ω(1+√(L₀R²/ε)+L₁R/log(2+L₁R)) | Worse: smaller by a factor √log(2+L₁R) when L₁R dominates. Same order when √(L₀R²/ε) ≥ L₁R/log(2+L₁R) | Deterministic methods → randomized methods with an expected-accuracy criterion | None. Both bounds allow arbitrary queries and outputs, and both make the parameters known | Gradient-only oracle (Everest I also allows function values). Dimension is polynomial, ≥2⁴⁴(·)⁵, versus 2n. Constants are 2⁻²³. Restricted to ε ≤ L₀R²/16 |
| Same authors, [Descending Everest II](https://arxiv.org/abs/2611.04171), Thm 7.1 (v1 3 Nov 2026; preprint, prior to this commit) | Ω(T₀/log²N₀) component calls with T₀ ∋ √(n(L₁R)²) → bound above | Not comparable: no verified reduction to n = 1 | Not comparable: finite sums with n ≥ 2, heterogeneity δ > 0 and L₁²R²δ/ε ≥ 3 → a single function | Expected stopping time → fixed budget | Identical components give δ = 0, which is excluded. No check that the average of the components satisfies (L₀,L₁) with the same constants. log²N₀ contains log(L₀R²/ε) |
| Woodworth–Srebro, [arXiv 1605.08003](https://arxiv.org/abs/1605.08003) Thm 7, and the classical first-order bound credited in [Garg et al., NeurIPS 2021](https://proceedings.neurips.cc/paper_files/paper/2021/file/fa6c94460e902005a0b660266190c8ba-Paper.pdf). Special case L₁ = 0 | Ω(√(L₀R²/ε)) (randomized; Woodworth–Srebro state m ≥ 2 and a ball domain) → same plus L₁R/log(2+L₁R) | Adds the L₁R/log(2+L₁R) term for L₁ > 0. At L₁ = 0 the order is the same | L₀-smooth → (L₀,L₁)-smooth single objective | None | None beyond the constants and dimension listed above |

**Standard-reduction check.** The theorem is a case split over three hard families:
- a zero-query quadratic pair;
- the classical smoothed chain, mollified to obtain a differentiable gradient;
- the inherited initialization family, at accuracy max{ε, L₀/L₁²} when L₁R ≥ 2²⁰.

The √ term and the union of rates are standard, and the companion note says so. The non-routine ingredient is the randomized initialization family, which this commit adds to `main`: a polynomial-dimension localization plus seed-independent averaging over hidden coordinates. The mechanism comes from the Yao-type and hidden-coordinate lemmas (Woodworth–Srebro; Everest II, Lemmas D.1–D.4). This result still had to make it work with a single-function gradient oracle, which costs an extra √log. The companion credits that ingredient to PRs #166/#168. They are not in local history, so I could not verify their content or dates.

**Search coverage.** On 14 Nov 2026 I searched arXiv and NeurIPS/ICML/ICLR sources for randomized (L₀,L₁)-smooth convex lower bounds and found none for the single-function class. Everest I proves deterministic bounds only, and its summarized Section 5 calls the randomized case open; I did not read that section verbatim. Everest II's Section 2 and Appendix B were only partly read. The companion's citations and its comparison with Everest I/II match what I checked.

**Conclusion**

**Partly: it extends the known deterministic lower bound to randomized algorithms, but with a weaker initialization term.** The strongest baseline is the Everest I deterministic bound:

| | Algorithms | Oracle | L₁R term |
|---|---|---|---|
| Everest I, Thm 4.10 | deterministic | value + gradient | L₁R/√log(2+L₁R) |
| This result | randomized | gradient only | L₁R/log(2+L₁R) |

Both include √(L₀R²/ε). The best upper bound has (1+L₁R)log(2+L₁R).

The gain is in scope: hardness now holds against randomized algorithms, and no published single-function result I found covers them. The price is an extra √log(2+L₁R), gradient-only access, polynomial dimension and huge constants. The deterministic theorem stays stronger on its own class. The accuracy term and the case combination are classical, and the randomization mechanism already exists in Everest II for finite sums. The non-classical hard family is credited to earlier, unverified repository PRs.

What can be claimed is a randomized, gradient-only lower bound Ω(√(L₀R²/ε) + L₁R/log(2+L₁R)) for convex (L₀,L₁)-smooth minimization over the full accuracy range. It sits within log²(2+L₁R) of the upper bound. It is a modest extension of known deterministic hardness using known randomization tools.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
