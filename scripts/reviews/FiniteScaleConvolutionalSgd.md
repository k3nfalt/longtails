# Novelty assessment: FiniteScaleConvolutionalSgd

The [theorem](../../LongTails/Theorems/FiniteScaleConvolutionalSgd.lean) proves the following. Consider jointly trained two-tap convolutional logistic SGD, with filter `(h₁,h₂)` and readout `v`, a constant step `η = κ/(1000R)`, a huge tuned filter initialization, full validation scans and periodic restarts. On any finite signed dataset `bᵢ = (αᵢ/√2)e + μuᵢ` whose cyclic differences `(uᵢ−Puᵢ)/√2` are `κ`-separable, it returns parameters with all `N` margins positive with probability `≥ 1−q`. See the [setup](../../LongTails/Setups/FiniteScaleConvolutionalSgd.lean) and the [algorithm](../../LongTails/Algorithms/FiniteScaleConvolutionalSgd.lean).

**Proved complexity.** One call returns the exact margin and gradient for one sample. The budget is

  `O( N³ (R/g)² κ⁻³ · log(R/(κμ)) · (1 + log(1/q)) )` calls.

The parameters are as follows:
- `N`: number of samples.
- `g ≤ |αᵢ| ≤ R`: background magnitudes.
- `μ`: contrast.
- `κ ≤ 1/4`: derivative-feature margin.
- `q`: failure probability.

The bound is valid only under `μ² log²(24·10⁶R²/(κ²μ²)) ≤ κ⁵g⁴/(10²⁸N³R²)`. The readout initialization is arbitrary; the filter initialization is restricted to `|a₀| ≤ 1` and `t₀ ∈ [1, 3/2]`. The `allowedAlgorithm` restriction enforces the scanned, restarted logistic-SGD update and the frozen-output rule.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Perceptron with the differencing filter held fixed (Novikoff 1962), run through the same oracle (reduction verified below) | `N(1/κ² + 1)`, deterministic → `N³(R/g)²κ⁻³ log(R/(κμ))(1+log(1/q))` | Worse: by a factor of about `N²(R/g)²κ⁻¹ log(R/(κμ)) log(1/q)` in every admissible regime | None. The baseline covers the whole class with any `μ > 0` and needs no background bounds. | Worse: a deterministic guarantee becomes a probability-`1−q` guarantee | The selected result needs `g > 0`, the severe contrast condition and enormous initialization. The baseline fixes the filter instead of learning it. |
| Cache all `N` replies at filter `(1,0)` and `v = 0` (where `∇ᵥ` equals `bᵢ`), then solve the linear feasibility problem for `bᵢ − Pbᵢ` offline | `N` → as above | Worse: by a factor of about `N²(R/g)²κ⁻³ log(R/(κμ)) log(1/q)` | None | None. Both output strict empirical separation; the baseline does so deterministically. | The baseline's offline computation is not counted as oracle calls, and it is not an SGD method. |
| Raw-input linear perceptron through the same oracle at filter `(1,0)`, with raw margin `≥ μκ/√2` and `‖bᵢ‖ ≤ R`. This is a special-case method that ignores the convolutional structure. | `N(2R²/(μ²κ²) + 1)` → as above | Better, but only against this weak baseline: `1/μ²` becomes `log(1/μ)`. The validity condition already implies `μ² log(R/(κμ)) ≪ κg²/N²`. | None | None | The comparison is between two upper bounds and is not a lower bound for linear methods. |
| [Tyurin, arXiv 2512.11587 v2 (21 May 2026), ICML 2026](https://arxiv.org/abs/2512.11587v2), Thm 2.1 (limit of full-batch GD with infinite initialization corresponds to a quadratic perceptron) and Thm 5.1 (noisy quadratic perceptron, two specific samples, `Õ(√d/μ)` steps) | Not comparable: Thm 2.1 gives no finite call bound, and Thm 5.1 analyses a perceptron surrogate rather than logistic GD on this class | Not comparable | Two samples → arbitrary `N` with conflicting derivative directions, for the actual finite-temperature logistic SGD | Asymptotic correspondence → finite-time high-probability separation | Pure-reference samples with zero background are excluded, and the contrast condition is far stronger. |

**Reduction check.** With the filter fixed at `h = (1,−1)/√2`, the margin is `μ⟨rᵢ,v⟩` and the readout gradient is `μrᵢ`, where `‖rᵢ‖ ≤ 1`. Cyclic perceptron updates on `v` therefore make at most `1/κ²` mistakes; this bound does not depend on `μ`. Each pass without a mistake certifies separation, which gives the first row. Neither the problem class nor this oracle needs the selected method's machinery.

**What is technically new.** The new step is a finite-sigmoid stochastic analysis: a weighted-work/entry bootstrap, followed by an adapted-indicator failure bound. [Yun–Krishnan–Mobahi (ICLR 2021)](https://arxiv.org/abs/2010.02501), Corollary 4, covers two-tap linear convolutional networks only for gradient flow on a single example, and only asymptotically. [Ji–Telgarsky (arXiv 1810.02032)](https://arxiv.org/abs/1810.02032) treats fully connected deep linear networks. These are proof context rather than baselines.

**Search coverage.** The searches were run on 30 Oct 2026 UTC. They covered Tyurin v2, implicit-bias work on linear and convolutional networks, and nearby finite-time logistic-SGD results; they were targeted rather than exhaustive. I did not read the companion note's inaccessible OpenReview items. The theorem was introduced in commit `b3e3c73` (30 Oct 2026). The companion note itself concedes the `N`-call and fixed-filter baselines; I found no discrepancy between the note and the Lean statement.

## Conclusion

**No optimization advantage is established; what may be new is a finite-time analysis of joint logistic SGD for this particular convolutional model.**

On the same finite, derivative-separable class with the same oracle, a perceptron that keeps the differencing filter fixed is much cheaper:

| Method | Oracle calls |
|---|---|
| Fixed-filter perceptron (deterministic) | `N(1/κ² + 1)` |
| This result (probability `1−q`) | `N³(R/g)²κ⁻³ log(R/(κμ))(1+log(1/q))` |

The selected result loses by a polynomial factor in `N`, `R/g` and `1/κ` in every regime. It also requires nonzero backgrounds, enormous initialization and a severe small-contrast condition.

The proof does show that jointly trained logistic SGD suppresses the constant-background filter on its own. Its cost depends only logarithmically on `1/μ`, whereas a raw-input perceptron bound scales with `1/μ²`. That is a statement about this method's dynamics, not a better way to solve the problem. Prior guarantees for this model that I found are asymptotic (Tyurin Thm 2.1), cover two samples (Tyurin Thm 5.1), or concern gradient flow on one example (Yun et al.). However, priority for this method-specific analysis is plausible rather than established.

What can be claimed is a new quantitative feature-learning analysis of logistic SGD in a narrow regime, not an improved complexity bound or broader problem coverage.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
