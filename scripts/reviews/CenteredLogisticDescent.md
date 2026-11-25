# Novelty assessment: CenteredLogisticDescent

The [theorem](../../LongTails/Theorems/CenteredLogisticDescent.lean) proves the following. Take the [setup](../../LongTails/Setups/CenteredLogisticClassification.lean)'s data class (signed rows `Dᵢ = yᵢR(ℓe + hᵢ)` with `‖hᵢ‖ ≤ ε ≤ 1/32`, centered `hᵢ`, signed mean `≤ ε`, and projected-centroid gap `yᵢ⟨hᵢ,T⟩ > (9+17‖Pe−e‖)ε³`). The [algorithm](../../LongTails/Algorithms/CenteredLogisticDescent.lean) is two full-batch logistic GD steps on the two-tap cyclic-filter model, started at `((R^{-1/2},0),0)` with step `8/R`. After it, every training score is strictly positive, deterministically.

**Complexity.** The budget is exactly `2n` indexed score/gradient queries. Here `n ≥ 2` is the number of samples, `d ≥ 2` the dimension, `R` the RMS row norm, and `ε` the normalized scatter. The count does not depend on `d`, `R`, `ε` or the gap. `allowedAlgorithm` restricts algorithms to batched GD with one positive rescaling and step, which may be any function of the first batch. The proof shows the algorithm is in this family.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Standard reduction: one scan at `((1,0),0)` returns `direction = ((0,0),Dᵢ)`, so all rows are revealed; then solve the separating LP locally (feasible, since `v=T` separates) | `n` → `2n` | Worse: factor 2, same order | None | None (both deterministic; both strictly separate the training set) | GD family only; this result needs two passes |
| Zhang–Wu–Lin–Bartlett, adaptive large-step GD, [Thm 2.1](https://arxiv.org/abs/2504.04105v2) (JMLR 27, 2026). Applies to linear GD on any data with margin `γ`; here `γ ≥ 9ε²` | Risk `≤ exp(−γ²η/4)` on the averaged iterate after `t ≥ 1/γ²` steps. Strict separation needs risk below `log 2/n`, so `O(n/ε⁴)` calls in the worst case of the class → `2n` | Better within GD on this subclass: by a factor of order `ε⁻⁴` when the margin is near `ε²` | Not a scope gain: the class here is a narrow subclass of margin-`γ` data | Averaged-iterate risk → last iterate, zero training error (for this subclass only) | The cubic gap, low-rank background and small scatter are strong. The Ω(1/γ²) lower bound (Thm 3.2) is worst-case, not on this class |
| Tyurin, batch perceptron delay, [Thm 5.2](https://arxiv.org/html/2512.11587v2) (ICML 2026). Repository comparison lemma (not a public theorem): more than `⌊1/μ⌋` passes on the pair family | `n(⌊1/μ⌋+1)` → `2n` | Better against the perceptron alone, when `μ ≤ 1/4096` | None | None | The perceptron is a weak baseline. The note says linear logistic GD at step `8/R²` already matches the first two readouts |
| Muşat–Boumal, [arXiv 2610.26748](https://arxiv.org/abs/2610.26748) (v1, 19 Oct 2026, prior). GD reaches ε-optimality in a data-dependent fixed number of large steps | Not comparable: only the abstract was checked, and the step count depends on `n` and the margin | Unresolved | — | — | — |

**Reduction check.** The problem-class complexity follows from the reduction above. The oracle reveals each row in one query, so any strictly feasible LP gives `n` calls, and the GD result cannot improve that. The calculation that is new to the method is the second-order sigmoid expansion. It gives `W = 8(m − Cm) + O(ε³)`, and the background cancels because `C ≈ ℓ²eeᵀ`. That is the classical two-step polynomial `2η − η²λ` from least squares (proof ancestry), plus control of the filter taps. The note itself states that the filter contributes nothing to these two steps: raw linear GD gives the same readouts.

**Search coverage.** Searched on 2026-11-25: Tyurin (arXiv 2512.11587 v2; AAAI 2412.08424), Zhang et al. (2504.04105 v2), Wu et al. large-stepsize logistic GD, Kale–Manupriya (2602.18946), Muşat–Boumal and Bao (2608.04382; abstracts only). The bodies of Muşat–Boumal and Bao Thm 23 were not verified. Zhang et al. Thm 3.2 was checked only through a summary. The result was introduced in commit `cab9226a` (2026-11-25).

The companion note matches the Lean statement. Its perceptron and small-step-GD separations are proved in proof modules, not as public theorems. The note openly concedes that cached rows permit a direct separator.

## Conclusion

**No optimization advantage is established; what remains is a two-step analysis of calibrated logistic GD on a hand-tailored data class.**

The strongest baseline is the trivial one in the same oracle model. The first query at the identity filter with zero readout returns each raw row, and the projected centroid `T` certifies that a strict separator exists. A linear-feasibility solve on the stored rows therefore succeeds after reading the data once:

| Method | Indexed calls to strict training separation |
|---|---|
| Read all rows, then solve the LP | `n` |
| This result (two GD passes) | `2n` |

Within the GD family the result is faster than the worst-case `O(1/γ²)`-step large-step bounds of Zhang et al., with `γ ≥ 9ε²` here. It also beats the perceptron's `Ω(1/μ)` passes. Both gains come from a class built for two steps: a single background direction, scatter at most `1/32`, and a cubic projected-centroid gap. The mechanism is a second-order expansion of the step `η(m − (η/8)Cm)`, which removes the background like a mean-centered centroid classifier. The note admits that the convolutional filter plays no role in this.

What the comparison proves is that GD beats weak or worst-case baselines on a narrow class. The literature search did not find this exact two-step statement, but Muşat–Boumal's fixed-step-count result was checked only at the abstract level. The claimable contribution is a formal two-pass separation guarantee for one calibrated GD variant. It gives no complexity or scope advantage for the classification problem itself.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
