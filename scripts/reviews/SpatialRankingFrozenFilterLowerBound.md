# SpatialRankingFrozenFilterLowerBound: novelty assessment

The [theorem](../../LongTails/Theorems/SpatialRankingFrozenFilterLowerBound.lean) concerns one explicit dataset ([frozen setup](../../LongTails/Setups/SpatialRankingFrozenFilter.lean), [shared geometry and GD scan](../../LongTails/Setups/SpatialRankingLogistic.lean)). The dataset has `2n` adjacent-comparison rows on two orthonormal item paths in `ℝ^d`. Fix any two-tap filter `aI + bS`; `(a,b)` may depend on the seed. Start the readout at `0` and run full-batch logistic GD on the readout only, with any positive state- and reply-dependent step at each pass and the current iterate as output. On this dataset, every such procedure fails to strictly separate all rows within `K ≤ n(n−3)` single-row gradient calls.

**Proved necessary budget.** The parameters are `n ≥ 8` (path length) and `d ≥ 32(n+1)` (pixel dimension). There is no accuracy parameter, because success means exact separation. Every frozen-filter GD run needs

`K > n(n−3) = Ω(n²)` row-gradient calls, i.e. more than `⌊(n−3)/2⌋` full passes of `2n` calls each.

The hard dataset depends only on `n` and `d`, not on the algorithm or its seed. The proof (`execution_fails`) also holds for every seed and for partial passes.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Unrestricted reconstruct-and-solve on the same class (repo, [companion note](../../LongTails/Theorems/SpatialRankingFrozenFilterLowerBound.md); [review](SpatialRankingLogisticAcceleration.md)) | `2n` calls suffice for any algorithm → `Ω(n²)` only for frozen GD | Not comparable: a problem-class upper bound of `2n` means the `Ω(n²)` bound cannot hold for the problem class | None | None | The lower bound holds only for the restricted frozen-GD family; the problem class itself is easy |
| Joint two-tap GD on the same dataset (repo, [SpatialRankingLogisticAcceleration](../../LongTails/Theorems/SpatialRankingLogisticAcceleration.lean), same-day companion) | `6n` calls (joint, taps start at `(1,0)`) vs `> n(n−3)` calls for every frozen filter | Separation factor of at least `(n−3)/6`, which exceeds 1 for `n > 9` | Same instance class; the frozen setup adds `d ≥ 32(n+1)` | Frozen family: arbitrary positive adaptive rates and arbitrary taps | Method-family separation, not an optimization advantage |
| Zhang–Wu–Lin–Bartlett, [arXiv:2504.04105](https://arxiv.org/abs/2504.04105) v2 (Apr 2025, preprint), Thm 3.2 and App. C.1; statements only partly verified | Span first-order batch methods on worst-case separable datasets with `N` rows: `Ω(min{log N, γ⁻²})` steps (Thm 3.2) and `Ω(min{N/4, γ^{-2/3}/8})` steps (C.1) → `> (n−3)/2` passes with `N = 2n` | If C.1 holds as summarized: none in order for a fixed feature map, since both give `Θ(N)` passes, i.e. `Θ(N²)` row calls | Incomparable classes: worst case over datasets for one fixed map → one dataset that defeats every two-tap map simultaneously | None | Their hard data are general and adapted to `γ`; here the data are a hand-built Gram family |

**Reduction check and mechanism.** No direct substitution gives the result, because frozen GD with taps `(a,b)` is ordinary logistic GD on the features `(aI+bS)x_i`. The `Ω(diameter)` delay is the familiar finite-propagation phenomenon behind Nesterov's chain lower bound for span methods (*Introductory Lectures*, 2004, Thm 2.1.7). It is also behind graph-diameter bounds for decentralized optimization. The new technical step replaces zero-chain sparsity with an affine-score invariant: logistic weights are nonzero on every row, so the Nesterov argument does not apply verbatim. On top of that invariant, opposite contact slopes on the two paths make one interior margin nonpositive for every sign of `ab`. Tyurin ([ICML 2026, PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html); arXiv v2 dated 21 May 2026) supplies the motivation only. That paper compares a quadratic perceptron with the raw perceptron on a two-sample dataset (`Θ̃(√d/μ)` vs `Ω(d/μ)`). I found no lower bound there for logistic GD with a fixed linear feature map over all stepsizes.

**Search coverage (25 Nov 2026).** I ran web searches on Tyurin's paper, minimax and lower bounds for logistic GD on separable data, and diameter and chain lower bounds in ranking and decentralized optimization. Zhang et al.'s Theorem 3.2 and Appendix C.1 statements were read only through a summary, not verbatim, and Tyurin's Appendix E was not read. The result was added to the repository today (commit `fbffc28d`), so all cited work predates it. The companion note correctly states that unrestricted methods need only `2n` calls. It does not compare against prior span-method lower bounds for logistic regression.

## Conclusion

**No new problem-class lower bound: the result shows that one restricted GD family is slow on one constructed dataset.**

The instance class is easy for unrestricted methods and for joint GD:

| Procedure on this dataset | Calls to separate all rows |
|---|---|
| Reconstruct rows, then solve a linear system | `2n` |
| Joint two-tap logistic GD (repository) | `6n` |
| Any frozen two-tap filter with adaptive positive readout steps (this result) | `> n(n−3)` |

What is established is a learned-versus-frozen separation of at least `(n−3)/6` on one explicit dataset. It holds uniformly over all filters, seeds, and positive step schedules, with the current iterate as output. That uniformity over filters, with all rows carrying nonzero logistic weight, appears new relative to the sources checked. The search does not establish priority, though.

The gain is modest for two concrete reasons. The `Θ(n)`-pass delay is the standard diameter phenomenon for gradient methods on path-structured data. Prior span-method lower bounds for logistic regression (Zhang et al., if their linear-in-`N` appendix bound is as summarized) already give the same `Θ(N)` order for a fixed feature map. Upper bounds for frozen GD on this dataset are not established, so the tightness of `n(n−3)` within the frozen family is open.

The contribution that can be claimed is an explicit, uniform-over-filters finite-step lower bound for frozen-filter logistic GD on a constructed ranking instance, complementing the repository's `6n` joint-GD bound.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
