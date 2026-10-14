# Novelty assessment: batched Chebyshev-step SGD on stochastic convex quadratics

[`result`](../../LongTails/Theorems/StochasticChebyshevQuadratic.lean) proves the following. Take a finite-dimensional convex quadratic `f(x)=c+‖A(x−u)‖²/2` that is `L`-smooth and has a minimizer within distance `R` of `x0`. Give the algorithm IID, jointly measurable, unbiased stochastic gradients with variance at most `σ²`. Then the last iterate of [batched SGD with predetermined Chebyshev-root scalar steps](../../LongTails/Algorithms/BatchedChebyshev.lean) has expected objective gap at most `ε`. The algorithm uses no momentum or averaging and knows `L, R, σ, ε, x0`. See the [setup](../../LongTails/Setups/StochasticConvexQuadratic.lean).

**Complexity.** Here `L` is the smoothness constant, `R` bounds `‖x0−x⋆‖`, `σ²` is the oracle variance and `ε` is the target accuracy, with `L, ε > 0` and `R, σ ≥ 0`. The proved budget is `3+⌈4√(LR²/ε)+65536σ²R²/ε²⌉` stochastic-gradient calls:

  **N = O(1 + √(LR²/ε) + σ²R²/ε²).**

There is no logarithmic factor. When `ε ≥ LR²/2` the output is `x0`, but the `σ²R²/ε²` calls are still spent.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan, AC-SA, [SIAM J. Optim. 22(4) 2012, Proposition 7](https://optimization-online.org/wp-content/uploads/2010/07/2669.pdf) (prior) | `O(1+√(LR²/ε)+σ²R²/ε²)` → `O(1+√(LR²/ε)+σ²R²/ε²)` | None: same order | None. Prior class is all `L`-smooth convex `f` with this oracle and is a strict superset. | None. Both bound a fixed-index final iterate (`x^ag_N` there). Both need `L, R, σ` and the horizon. | Narrower class: quadratics only, finite dimension. Larger constants. Iterates can grow exponentially at intermediate steps. Only plus: no momentum (scalar-step SGD). |
| Ghadimi–Lan, RSAG, [Math. Program. 2016, Corollary 3(b), (3.22)](https://arxiv.org/abs/1310.3787) (prior) | `O(1+√(LR²/ε)+σ²R²/ε²)` → same | None: same order | None (general smooth convex) | Random-index iterate `x^ag_R` → deterministic last iterate. AC-SA above already gives a fixed-index output. | Same narrowing as above |
| Repository [`AcceleratedStochasticConvex`](../../LongTails/Theorems/AcceleratedStochasticConvex.lean) (introduced 2026-09-21, earlier than this result) | `max(1,⌈4√(LR²/ε)+64σ²R²/ε²⌉)` → `3+⌈4√(LR²/ε)+65536σ²R²/ε²⌉` | Worse: variance constant about 1000× larger | None (the repo theorem covers general smooth convex `f`) | None | Quadratic and finite-dimensional restriction |

**How the comparison was derived.** In Proposition 7, take `ν=1`, `V(x0,x⋆)≤R²/2`, `M=0` and `γ=max(2L, σN^{3/2}/R)`. This choice is admissible because `γ≥2L`. The bound becomes `E[f(x^ag_N)−f⋆] ≤ 4LR²/N² + 6σR/√N`. Only part (c) of Theorem 1 requires a compact domain, so `X=ℝⁿ` is allowed. Setting the bound to `ε` gives the row above, with each AC-SA iteration using exactly one call.

**Reduction check and proof ancestry.** No reduction turns the Chebyshev scheme into AC-SA; the problem-class bound simply follows from AC-SA directly. The method-specific step appears genuine: an `O(T)` (rather than `O(T log T)`) bound on how much descending-order Chebyshev factors amplify noise. This step is what removes a `log²T` factor from the naive batched-Chebyshev bound. The ancestry is Young/Lebedev–Finogenov root orderings and [Agarwal–Goel–Zhang, ICML 2021](https://arxiv.org/abs/2103.01338) fractal schedules, which address deterministic or adversarial stability rather than this variance bound.

**Search coverage.** Searched on 2026-10-07: AC-SA/RSAG primary texts (theorems read), Chebyshev/fractal/silver step-size literature, and the stepsize-hedging survey by Altschuler–Parrilo (June 2026), which treats no stochastic setting. The stochastic silver-step follow-ups by Bai et al. were not checked in full; the companion note says they cover only strongly convex settings. The note's statement that "the unrestricted existence … is already known" agrees with this check. Its claimed optimality "within the scalar-step family" is an informal argument and is not formalized in Lean. I found no prior stochastic last-iterate bound for momentum-free Chebyshev steps, but that absence does not establish priority.

## Conclusion

**No: this is another analysis that achieves the known accelerated rate, on a narrower problem class.**

The strongest baseline is Ghadimi–Lan's AC-SA (2012). It covers every smooth convex function with the same oracle, needs the same known parameters, and returns a fixed-index final iterate. Its call count has the same order:

| | Calls for `E[f(x̂)−f⋆] ≤ ε` | Class |
|---|---|---|
| AC-SA (2012) | `O(1+√(LR²/ε)+σ²R²/ε²)` | smooth convex |
| This result | `O(1+√(LR²/ε)+σ²R²/ε²)` | finite-dimensional convex quadratics |

The result wins in no regime of `L, R, σ, ε`. It covers no new instances, and its constants are larger. The repository already contains an accelerated stochastic theorem with the same order and a smaller variance constant.

What may be new is method-specific. Plain SGD with scalar Chebyshev steps and deterministic batch sizes, without momentum, reaches the accelerated bias–variance tradeoff with no logarithmic factor. The key ingredient is a sharp `O(T)` bound on noise amplification for the descending root order. However, the momentum-free design gives no oracle, information or output advantage, and its intermediate iterates can be numerically unstable. Its priority is plausible but not verified.

The claimable contribution is a new analysis of a restricted step-size-only method, not an improved optimization guarantee.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
