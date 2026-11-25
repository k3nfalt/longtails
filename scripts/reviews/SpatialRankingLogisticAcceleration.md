# Novelty assessment: SpatialRankingLogisticAcceleration

[`result`](../../LongTails/Theorems/SpatialRankingLogisticAcceleration.lean) shows the following for every instance of the constructed two-path ranking family in the [setup](../../LongTails/Setups/SpatialRankingLogistic.lean) with `n ≥ 8`. Full-batch logistic GD on the cyclic two-tap model `a⟨x,v⟩+b⟨Sx,v⟩`, with taps `(1,0)`, readout `0` and constant mean-loss step `4n` ([algorithm](../../LongTails/Algorithms/SpatialRankingLogistic.lean)), returns its third iterate. That iterate strictly separates all `2n` signed comparisons, deterministically.

**Proved complexity.** The budget is exactly `6n` component-gradient calls, i.e. three passes over `2n` examples. Here `n` is the number of adjacent comparisons per path, and the dimension `d` does not appear. The instance class is fixed: the items are orthonormal, the shifted Gram entries are prescribed by `lagEntry`, and the six population constants are hard-coded. A realization exists for `d ≥ 32(n+1)`. For smaller `d` there may be no admissible instance. `allowedAlgorithm` enforces the claimed update family: joint simultaneous full-batch GD, any constant positive step, taps `(1,0)`, readout `0`, and output equal to the current iterate. The theorem then proves its algorithm is in this family.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Reconstruct-then-solve (checked here; the companion note also states it). At `θ=((1,0),0)` the reply to query `(g,i)` is `((0,0), x_{gi}/2)`. Solve `⟨x_{gi},w⟩=1` offline and output `((1,0),w)`. | `2n` → `6n` | **Worse by the constant 3, same order `Θ(n)`** | None | None. Both are deterministic, need only `n`, and certify strict separation. | The baseline stores `O(nd)` data and is not GD. The setup has no memory constraint. |
| Tyurin, ICML 2026 ([PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html); [arXiv:2512.11587](https://arxiv.org/abs/2512.11587), v1 12 Dec 2025), Thms 5.1–5.2. **Special case and different method:** two samples, quadratic-perceptron limit of GD. | Not comparable: `Θ̃(√d/μ)` vs `Ω(d)` iterations on dataset (5) → `6n` on the ranking family | Not comparable. No common setup. | Two-sample dataset → `2n` examples on a hand-built path family. The classes are incomparable. | Large-step perceptron limit → actual finite-step logistic GD | Exact Gram identities and fixed population constants |
| Repository companion [lower bound](../../LongTails/Theorems/SpatialRankingFrozenFilterLowerBound.lean) (same commit; frozen filter only) | Frozen-filter GD needs `> n(n−3)` calls → joint GD needs `6n` | Method-level `Θ(n)` separation between learned-filter and frozen-filter GD. This is not a problem-class gain. | None | None | The lower bound covers one frozen filter with adaptive positive scalar readout steps. It does not cover ensembles or other optimizers. |

**Baseline admissibility.** Within each path the rows `f_g(u_j−u_{j+1})` are linearly independent, and the two groups are orthogonal. So `w = Xᵀ(XXᵀ)⁻¹𝟏` exists, and it is computed from the `2n` replies. With taps `(1,0)` the margin is `⟨x,w⟩ = 1 > 0`. No lower bound for arbitrary algorithms was checked, so `Θ(n)` optimality for the problem class is plausible but unproved.

**Reduction check and mechanism.** The problem-class guarantee follows from data reconstruction plus linear algebra. The new content is the finite three-step analysis of joint logistic GD: endpoint-only first updates, a third-step summation by parts, and the sign-opposite coefficient `C_g`. Tyurin supplies the motivating phenomenon (Figure 1) and the GD-as-perceptron perspective. Gunasekar et al. ([NeurIPS 2018](https://arxiv.org/abs/1806.00468)) and Arora–Cohen–Hazan ([ICML 2018](https://proceedings.mlr.press/v80/arora18a.html)) are context on implicit bias and implicit acceleration through overparameterization. None of them gives a hitting-time bound for this update.

**Search coverage (25 Nov 2026).** I ran web searches on Tyurin's paper, large-step logistic GD on separable data (Wu et al. [arXiv:2402.15926](https://arxiv.org/abs/2402.15926), [arXiv:2602.12471](https://arxiv.org/abs/2602.12471)), Nacson et al. [arXiv:1803.01905](https://arxiv.org/abs/1803.01905), and hitting times for linear convolutional networks. I found no prior learned-versus-frozen filter hitting-time separation for finite-step logistic GD. That absence does not prove priority. I did not open full texts in this session. Tyurin's theorem content is taken from search excerpts and the repository's earlier review of v2. I could not verify the note's citation of Musat–Boumal (arXiv:2610.26748), and I did not check Zhang–Wu–Bartlett. The note's "acceleration" refers to joint-vs-frozen GD, not to problem-class complexity. On that point the note is candid, since it states the `2n` baseline.

## Conclusion

**No problem-class improvement: a trivial method already solves this family in fewer calls; what is new is a statement about GD itself.** The strongest baseline reads every comparison once at the initial point, where the oracle returns the row itself, then solves a linear system offline:

| Method | Calls to strictly separate all `2n` comparisons |
|---|---|
| Reconstruct + linear solve | `2n` |
| Joint two-tap GD (this result) | `6n` |
| Any single frozen filter, adaptive readout steps (companion) | `> n(n−3)` |

Both upper bounds are `Θ(n)`, and the selected bound is three times larger. Its scope is also not broader: the instance class is a hand-designed family with exact Gram identities and fixed constants, chosen so that every frozen filter fails.

The established content is method-level. Actual finite-step logistic GD with a learned two-tap filter needs a constant number of passes, while every frozen filter needs `Θ(n)` passes on the same data. That separation appears new relative to Tyurin's two-sample perceptron-limit theorems, but this search does not establish priority. It also gives no advantage over other applicable methods and explains the CIFAR experiment only by analogy.

The claim that can be made is a new finite-step learned-versus-frozen GD separation on a constructed instance family. It is not a better optimization guarantee.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
