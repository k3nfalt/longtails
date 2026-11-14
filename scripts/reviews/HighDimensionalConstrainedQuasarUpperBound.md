# Novelty assessment: HighDimensionalConstrainedQuasarUpperBound

**What is proved.** The [theorem](../../LongTails/Theorems/HighDimensionalConstrainedQuasarUpperBound.lean) applies the [high-probability method](../../LongTails/Algorithms/StochasticQuasarProgram.lean) to the [HighDimensionalConstrainedQuasar setup](../../LongTails/Setups/HighDimensionalConstrainedQuasar.lean). Every instance of that setup is also an instance of [StochasticConstrainedQuasar](../../LongTails/Setups/StochasticConstrainedQuasar.lean). The problem class is an L-smooth, γ-quasar-convex objective on a compact convex X ⊂ ℝ^d of diameter at most D. The oracle gives IID unbiased gradients with variance at most σ², plus exact projection onto X. The output satisfies Pr{x̂ ∈ X, f(x̂) − f(x⋆) ≤ ε} ≥ 1 − δ.

The proof is three lines. It maps the parameters through `toStochastic`, uses [HighDimensionalQuasarInclusion](../../LongTails/Proofs/HighDimensionalQuasarInclusion.lean) to check validity, and then calls the earlier repository result [StochasticConstrainedQuasarHighProbability](../../LongTails/Theorems/StochasticConstrainedQuasarHighProbability.lean). That result was added on 2026-11-06 in commit b7e87e14. This theorem has the same budget formula, character for character. It was added on 2026-11-14 in commit fd252a20.

**Complexity.** The parameters are as follows: L is the gradient-Lipschitz constant on X, D is the diameter of X, γ ∈ (0,1] is the quasar parameter, σ² is the variance bound, ε is the target accuracy and δ is the failure probability. The bound applies to each of the two channels, so total calls are at most twice this:

  N = O( log(1/δ) · log²(LD²/(γ²ε)) · ( √(LD²/ε)/γ + σ²D²/(γ²ε²) ) ).

Two simplifications are used, both justified by `valid`. Because δ ≤ 1/4, log(8/δ) and log(1/δ) are of the same order. Because LD²/ε ≥ 10⁸, the additive 1 is absorbed. The setup restricts the parent's class in four ways:
- Ω = Bool, meaning a two-point seed space;
- E = ℝ^d with d ≥ 2³⁴(B_low+1)⁵, where B_low is the lower-bound budget;
- σ = 0 or σD ≥ 64γε;
- δ ≤ 1/4.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository: [StochasticConstrainedQuasarHighProbability](../../LongTails/Theorems/StochasticConstrainedQuasarHighProbability.lean) (prior, 2026-11-06). Direct competitor on a strictly larger class. | O(log(1/δ)log²(2+LD²/(γ²ε))(1+√(LD²/ε)/γ+σ²D²/(γ²ε²))) → the identical formula | None: identical budget | None. The instance classes are nested: this one is a strict subset. | None: same oracle, same parameters and the same probability-1−δ output | Narrower in four ways: Ω = Bool instead of arbitrary seed spaces, a huge dimension floor, an excluded noise band 0 < σ < 64γε/D, and δ ≤ 1/4 |
| Martínez-Rubio, [AISTATS 2026](https://proceedings.mlr.press/v300/martinez-rubio26a.html), [2510.01943](https://arxiv.org/abs/2510.01943), Thm 5. Applies only at σ = 0. | Õ(√(LD²/ε)/γ) value-and-gradient calls, deterministic → O(log(1/δ)log²(LD²/(γ²ε))√(LD²/ε)/γ) | None: same order up to logs. This result pays an extra log(1/δ). | Exact deterministic oracle → finite-variance stochastic gradients (inherited from the parent) | Needs function values → gradients and projections only (inherited) | Randomized guarantee with failure probability δ, versus a deterministic guarantee |
| Fu–Xu–Wilson, [ICML 2023](https://proceedings.mlr.press/v202/fu23e.html), Cor. 3.3. Applies only to unconstrained problems with ∇f(x⋆) = 0. | Expected gap Õ(R√(L/ε)+σ²R²/(γ²ε²)). Markov's inequality at accuracy εδ gives Õ(δ^{-1/2}R√(L/ε)+δ^{-2}σ²R²/(γ²ε²)) → N with R ≤ D | Confidence dependence improves from δ⁻² to log(1/δ) on the noise term. This gain is inherited from the parent. | Unconstrained → constrained, with boundary minimizers allowed (inherited) | Expected gap → probability bound (inherited) | Needs a compact X with known D. Loses when R ≪ D. |

**Reduction check.** The result is literally a composition: the parent theorem plus an inclusion. No new algorithm, analysis, or proof step is involved. The proof ancestry lies entirely in the parent and its [review](StochasticConstrainedQuasarHighProbability.md): a constrained Moreau envelope, multilevel (MLMC) gradient estimation, continuized acceleration, and the power-barrier high-probability argument. The theorem's only role is to state the upper half of a pair. The lower half, [HighDimensionalConstrainedQuasarLowerBound](../../LongTails/Theorems/HighDimensionalConstrainedQuasarLowerBound.lean), proves Ω(√(LD²/ε)/γ + σ²D²log(1/δ)/(γ²ε²)) on the same setup. Any novelty of that pair belongs to the lower bound and is not assessed here.

**Search coverage.** I searched on 2026-11-14 across arXiv, PMLR, and OpenReview, using queries on high-probability, stochastic, constrained, and quasar-convex results. I found no newer paper that supersedes the parent. My comparisons with Martínez-Rubio and Fu–Xu–Wilson rely on the parent review's 2026-11-06 readings; I did not reread those theorems in full. The companion note claims nothing new for the upper bound, which agrees with the Lean proof. The note itself states that the Bool seed space is a restriction.

**Conclusion**

**No: this theorem restates an existing repository result on a smaller class.** The strongest baseline is the repository's own [StochasticConstrainedQuasarHighProbability](../../LongTails/Theorems/StochasticConstrainedQuasarHighProbability.lean). It proves the same high-probability guarantee with the same oracle and the same budget, for arbitrary seed spaces and any finite-dimensional space:

| | Class | Calls per channel |
|---|---|---|
| Parent (2026-11-06) | All valid parameters, any Ω | O(log(1/δ)·log²(·)·(√(LD²/ε)/γ + σ²D²/(γ²ε²))) |
| This theorem | Ω = Bool, d ≥ 2³⁴(B_low+1)⁵, δ ≤ 1/4, noise band excluded | identical |

The Lean proof calls the parent theorem through a proved inclusion. No regime gives a complexity, scope, oracle or output gain, and the class shrinks.

Whatever literature novelty exists belongs to the parent: accelerated, gradient-and-projection-only, logarithmic-confidence optimization for constrained quasar-convex problems. The research value of this commit lies in the companion lower bound, which this report does not evaluate.

The only contribution this theorem can claim is formal bookkeeping: it states the known upper bound on the lower bound's setup, so that the two can be compared directly.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
