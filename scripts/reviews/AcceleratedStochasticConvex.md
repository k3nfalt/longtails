# AcceleratedStochasticConvex: novelty assessment

[`result`](../../LongTails/Theorems/AcceleratedStochasticConvex.lean) proves the following. Take an L-smooth convex f on a real Hilbert space (complete, second-countable, Borel) with a minimizer x* satisfying ‖x₀ − x*‖ ≤ R. Give it i.i.d. unbiased stochastic gradients with variance ≤ σ², jointly measurable ([setup](../../LongTails/Setups/StochasticSmoothAndConvex.lean)). Then constant-step Nesterov acceleration in linear-coupling form outputs a point x_K with E[f(x_K)] − f* ≤ ε. The method uses weights a_k = (k+1)/2, y = (A_k x + a_k z)/A_{k+1}, x⁺ = y − g/D and z⁺ = z − a_k g/D, with D = 2L + 8Kσ²/ε ([algorithm](../../LongTails/Algorithms/Accelerated.lean), [run](../../LongTails/Algorithms/AcceleratedStochastic.lean)). x_K is the method's output sequence, not an average, and the guarantee is in expectation only.

**Complexity.** The method makes one stochastic-gradient call per iteration. The proved budget is K = max{1, ⌈4√(LR²/ε) + 64σ²R²/ε²⌉}, so

  N = O(1 + √(LR²/ε) + σ²R²/ε²),

where L is the smoothness constant, R bounds the initial distance, σ² bounds the variance and ε is the target expected gap. The bound holds for all L > 0, R ≥ 0, σ ≥ 0 and ε > 0. When σ = 0 it reduces to deterministic AGD; when R = 0 it uses one call. The tuning requires L, σ and ε, plus R through K.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan, AC-SA with stepsize (4.3) and γ = γ*_N, Prop. 7 and eq. (4.11) ([preprint, rev. June 2012](https://optimization-online.org/wp-content/uploads/2010/07/2669.pdf); SIAM J. Optim. 22(4), 2012). Specialized to X = whole space, ν = 1, M = 0, V(x₀,x*) ≤ R²/2. Prop. 7 relies on Thm 1(a), which needs only a closed convex X. | E ≤ 4LR²/N² + 4√2·σR/√N, so N = O(1 + √(LR²/ε) + σ²R²/ε²) → O(1 + √(LR²/ε) + σ²R²/ε²) | None: same order | None for the problem class. Ghadimi–Lan is stated in a finite-dimensional space, while Lean allows any Hilbert space. Their argument is dimension-free; this is a formal, not mathematical, extension. | None. Both need L, σ, R and a fixed N, and both output the aggregate point x^ag_N / x_K in expectation. | Lean proves no high-probability bound. Under light-tailed noise (A2), Ghadimi–Lan also give a high-probability bound, which needs R_X(x*). Lean uses a different update: a gradient step from y instead of AC-SA's convex combination. It has the same oracle and output type. |
| Lan, AC-SA ([Math. Program. 133, 2012](https://doi.org/10.1007/s10107-010-0434-y); preprint 2008) | Same O(√(LR²/ε) + σ²R²/ε²) order, as cited by Ghadimi–Lan | None: same order | Not verified. I did not check the theorem text for unbounded X. | None | Its constants and exact theorem number were not checked. |

**Reductions and proof ancestry.** No new mechanism is needed. The result is the standard estimate-sequence / linear-coupling potential with inexact gradients:

  E[f(x_K) − f*] ≤ 2D‖x₀ − x*‖²/(K(K+1)) + Kσ²/D

([`accelerated_expected_rate`](../../LongTails/Proofs/AcceleratedStochastic.lean)). Balancing the two terms through D is exactly Ghadimi–Lan's γ*_N tuning. Cohen–Diakonikolas–Orecchia (AGD+, [arXiv:1805.12591v3](https://arxiv.org/abs/1805.12591), Cor. 3.9, ICML 2018) give the same unconstrained additive-noise analysis; I treat it as proof ancestry. The lower bound Ω(√(LR²/ε) + σ²R²/ε²) quoted in this literature makes the order optimal, but I did not re-verify it.

**Search coverage.** On 2026-10-07 I read Ghadimi–Lan (Thm 1, Prop. 7, §4.1) and CDO (Cor. 3.9). The Lan 2012 theorem text was not opened. There is no companion note. The theorem first appears in local history at 5b7536c (2026-09-21), and the stochastic accelerated run at 21c5730 (2026-09-10). Both are far later than the 2012 baselines. Other repository theorems (StochasticGeneralizedAcceleratedConvex, FiniteVarianceGeneralizedAcceleratedConvex) target broader (L₀,L₁) classes and do not affect this assessment.

## Conclusion

**No: this is the textbook optimal accelerated-SGD bound for smooth convex stochastic optimization, re-proved for a standard variant.**

The strongest baseline is Ghadimi–Lan's AC-SA (Proposition 7 with the N-dependent stepsize γ*_N, 2012). It already covers an unconstrained domain, unbiased gradients with variance σ², and an expected gap of the aggregated output, using one sample per iteration:

| | Oracle calls for E[f(x)] − f* ≤ ε |
|---|---|
| Ghadimi–Lan AC-SA (2012) | O(1 + √(LR²/ε) + σ²R²/ε²) |
| This theorem | O(1 + √(LR²/ε) + σ²R²/ε²) |

The required information (L, σ, R, fixed horizon) and the output type are the same. Ghadimi–Lan additionally give high-probability bounds under light-tailed noise.

The only differences are a linear-coupling update instead of AC-SA's averaging step, constants, an infinite-dimensional Hilbert-space statement and a Lean formalization. None of these changes the complexity, the problem class or the output guarantee. The infinite-dimensional statement is a formal rather than a mathematical extension, because the classical proof is dimension-free. What can be claimed is a verified formalization of a known optimal result.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
