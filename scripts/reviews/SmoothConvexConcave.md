# SmoothConvexConcave: novelty assessment

**Guarantee.** For a function φ on X × Y whose gradient field is deterministic and Lipschitz, and which is convex–concave on compact convex sets, the theorem says the following. Projected extragradient started at a point of X × Y, using step `1/(2L)` and run for `N = max(1, ⌈2LD²/ε⌉)` iterations, returns the uniform average of the N extrapolated points, and that average has saddle gap `sup_Y φ(x̄,·) − inf_X φ(·,ȳ) ≤ ε`. See the [theorem](../../LongTails/Theorems/SmoothConvexConcave.lean), [setup](../../LongTails/Setups/SmoothConvexConcave.lean) and [algorithm](../../LongTails/Algorithms/Extragradient.lean).

**Complexity.** The proved cost is `2·max(1, ⌈2LD²/ε⌉) = O(1 + LD²/ε)` gradient-oracle calls, plus one projection per call.
- L is the Lipschitz constant of `(∇ₓφ, −∇ᵧφ)` on all of E × F, measured in Lean's max product norm `‖(x,y)‖ = max(‖x‖,‖y‖)`.
- D is the diameter of X × Y in that same norm.
- ε is the target gap.

The oracle is deterministic: the setup forces every answer to equal the exact gradient. E and F may be any real Hilbert spaces. The degenerate case D = 0 costs 2 calls. There is no companion Markdown note. The file first appears on 2026-09-21 in commit `ea894ff`.

**Reduction check.** Convert to the Euclidean product norm: the Lipschitz constant becomes `L₂ ≤ √2·L` and the Euclidean diameter satisfies `D₂² ≤ 2D²`. Now apply Nemirovski's Theorem 3.2 with `ω = ½‖·‖²` and `α = 1`:
- Θ(z₀) ≤ D².
- His step `γ = α/(√2 L₂)` becomes exactly `1/(2L)`.
- Bound (3.10) gives `ε_f(z^N) ≤ √2·Θ·L₂/N ≤ 2LD²/N`, at a cost of 2N operator calls.

On compact convex sets, Sion's theorem makes his ε_f equal to the Lean gap. So the selected step, the averaged output, `N = ⌈2LD²/ε⌉` and the `2N` call count are all Nemirovski's Basic Implementation, with no further work needed.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nemirovski, *Prox-method with rate of convergence O(1/t)…*, SIAM J. Optim. 15(1):229–251, 2004 ([pdf](https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf)), Prop. 2.2 (2.14) + Thm 3.2 (3.10), Euclidean prox-function. This is prior work and a direct competitor. | `2⌈2LD²/ε⌉` → `2·max(1,⌈2LD²/ε⌉)` | None: the formula is identical | Finite-dimensional Euclidean spaces → real Hilbert spaces with compact X, Y. The proof carries over word for word, so this is not a meaningful new class. | None. Both use the same averaged extrapolated point, the same deterministic oracle, and need L and D to set the step and budget. | Stronger assumption here: φ must be differentiable, and its gradient Lipschitz, on all of E × F, whereas Nemirovski needs this only on X × Y. Nemirovski also covers general Bregman setups, which can be dimension-friendlier (e.g. simplices). |
| Ouyang–Xu, Math. Program. 2021 ([arXiv:1808.02901](https://arxiv.org/abs/1808.02901), v1 2018), Thms 2 and 9. These are lower bounds, not an algorithm. | Lower bound `Ω(‖A‖R_X R_Y/ε)` on bilinear instances over balls, for dimension larger than about 4× the iteration count → `O(LD²/ε)` | None. With L ≍ ‖A‖ and D ≍ R_X ≍ R_Y, the selected bound is order-optimal and cannot be beaten in that large-dimension regime. | None | None | Not applicable |

**Proof ancestry and repository overlap.** The mechanism is a prox-inequality sum that telescopes, as in Korpelevich's extragradient (1976) and Nemirovski's Lemma 3.1 / (2.16). I found no new technical step. The repository result [AlexGdaConvexConcave](../../LongTails/Theorems/AlexGdaConvexConcave.lean) has the weaker cost `O(1 + L²R²/ε²)` for a different method. So inside this repository the selected theorem is the strongest smooth convex–concave gap bound, but that does not make it novel in the literature.

**Search coverage (2026-10-07).** I read the Nemirovski 2004 theorem text (Sec. 2.3, Sec. 3) and the Ouyang–Xu theorem statements directly. Korpelevich (1976) and Nesterov's dual extrapolation (Math. Program. 109, 2007) are well-known, but I did not re-read them, because they are not needed for the verdict. I did not run any Lean build.

## Conclusion

**No: this is Nemirovski's 2004 extragradient/Mirror-Prox guarantee, restated and formally verified.**

The strongest baseline is Nemirovski (2004), Theorem 3.2. With a Euclidean prox-function and the max-norm constants used in Lean, it gives exactly the same step, the same averaged output and the same budget:

| | Calls for averaged saddle gap ≤ ε |
|---|---|
| Nemirovski 2004 | `2⌈2LD²/ε⌉` |
| This theorem | `2·max(1, ⌈2LD²/ε⌉)` |

There is no regime where the selected result does better. Its only formal broadening, from Euclidean to Hilbert spaces, follows from the same proof. It is also slightly narrower than Nemirovski, because it requires differentiability and Lipschitz gradients on the whole ambient space. Ouyang–Xu's bilinear lower bound shows that the `LD²/ε` order cannot be improved in high dimension, so no later method beats it in order either.

The contribution that can be claimed is a faithful Lean formalization of a classical, optimal-order result. It is not new mathematics.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
