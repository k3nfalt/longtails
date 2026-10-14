# SgdConvex: averaged constant-step SGD for smooth convex stochastic minimization

The theorem ([theorem](../../LongTails/Theorems/SgdConvex.lean), [setup](../../LongTails/Setups/StochasticSmoothAndConvex.lean), [algorithm](../../LongTails/Algorithms/Sgd.lean)) proves the following. Let `f` be convex and `L`-smooth on a separable real Hilbert space, with a minimizer `x*` such that `‖x₀−x*‖ ≤ R`. Let the oracle return i.i.d. unbiased stochastic gradients with variance at most `σ²`. Then SGD with step `η = 1/(2L + 2σ²/ε)`, run for `K` steps, returns the average `(1/K)Σ_{k<K} x_k` of the queried points, and this average satisfies `E[f(x̄_K) − f(x*)] ≤ ε`.

**Complexity.** The proved budget is `K = max(1, ⌈4LR²/ε + 4σ²R²/ε²⌉)`. Each iteration makes one oracle call, so the number of stochastic-gradient calls is

  **O(1 + LR²/ε + σ²R²/ε²)**, valid for L > 0, ε > 0, R ≥ 0, σ ≥ 0.

Here `L` is the smoothness constant, `R` bounds the initial distance to a minimizer, `σ²` bounds the variance and `ε` is the target expected objective gap. The step size uses `L`, `σ` and `ε`; the budget also uses `R`. The proof ([Proofs/SgdConvex.lean](../../LongTails/Proofs/SgdConvex.lean), `stochastic_step`, `expected_average`) is the textbook argument: a one-step distance recursion `E‖x⁺−x*‖² + η(f(x)−f*) ≤ ‖x−x*‖² + η²σ²`, followed by telescoping and Jensen's inequality. This gives `R²/(ηK) + ησ²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan, *Optimal SA algorithms for strongly convex SCO I*, SIAM J. Optim. 22(4), 2012 ([preprint](https://optimization-online.org/wp-content/uploads/2010/07/2669.pdf)), Prop. 7 with `γ = γ*_N`, case `μ = M = 0`, Euclidean `V = ½‖·‖²`, `X` closed convex (may be unbounded) | AC-SA: `O(1 + √(LR²/ε) + σ²R²/ε²)` → `O(1 + LR²/ε + σ²R²/ε²)` | **Worse:** the deterministic term is `LR²/ε` instead of `√(LR²/ε)`, i.e. a factor √(LR²/ε) larger whenever `LR²/ε ≥ 1` and `LR²/ε ≥ σ²R²/ε²`. It matches only when `σ²R²/ε² ≥ LR²/ε`, i.e. `σ² ≥ Lε`. It is never better. | None. Prior work states the result in Euclidean `ℝⁿ`; the Lean version covers separable Hilbert spaces, but the proofs are dimension-free, so this adds no substantive scope. | None. Both need `L`, `σ` and `R` (AC-SA's `γ*_N` needs `V(x₀,x*)`; here `K` needs `R`), and both fix the horizon. AC-SA outputs `x^ag_N`, a single iterate; here the output is an average. | Prior work also gives light-tail high-probability bounds, which are absent here. |
| Bubeck, *Convex Optimization: Algorithms and Complexity*, FnT ML 2015 ([arXiv 1405.4980](https://arxiv.org/abs/1405.4980)), Thm 6.3 (stochastic mirror descent, smooth case) | `Rσ√(2/t) + LR²/t ≤ ε` ⇒ `O(1 + LR²/ε + σ²R²/ε²)` → same | None: same order. Only the constants differ. | None. Thm 6.3 defines `R²` as a supremum over the domain, but with `Φ = ½‖·‖²` its proof telescopes `D_Φ(x*,x₁) = ½‖x₁−x*‖²`, so it applies to the unconstrained case with `R = ‖x₀−x*‖`. | Here the step does not use `R` (step `1/(2L+2σ²/ε)` instead of `1/(L+σ√t/(R√2))`), but `R` is still needed for `K`, so the information required is the same. Same averaged output. | None |
| Repository: [AcceleratedStochasticConvex](../../LongTails/Theorems/AcceleratedStochasticConvex.lean) (same `spec`, added 2026-09-21) | `O(1 + √(LR²/ε) + σ²R²/ε²)` → `O(1 + LR²/ε + σ²R²/ε²)` | Worse, in the same regime as in row 1 | None | None | None |

**Reduction check.** The result is a direct specialization of the classical smooth stochastic-gradient bound (Bubeck Thm 6.3; also Lan's AC-SA analyses, Math. Program. 133, 2012). It follows by setting `Φ = ½‖·‖²` and choosing a step that splits `ε` evenly between the initialization term and the noise term. No new mechanism or unresolved obstacle appears. The Lean contribution is a formalization, including measurability and the i.i.d. product-measure bookkeeping.

**Search coverage (2026-10-07).** I read the theorem statements and proofs of Ghadimi–Lan Prop. 7 and Bubeck Thm 6.3. I relied on prior knowledge of Lan 2012 and Nemirovski et al. 2009 and did not re-read them. There is no companion note. The result entered the repository on 2026-09-21 (commit `5b7536c`), which is more than a decade after these sources, so priority is not in question.

**Conclusion**

**No: this is the textbook SGD guarantee and it is beaten by stochastic acceleration.** The strongest baseline is Ghadimi–Lan's AC-SA (2012). It uses the same i.i.d. unbiased, variance-`σ²` oracle on unconstrained smooth convex problems, has the same one-call-per-iteration cost and the same expected-gap criterion.

| Method | Stochastic-gradient calls |
|---|---|
| This theorem (averaged SGD) | `O(1 + LR²/ε + σ²R²/ε²)` |
| AC-SA (Ghadimi–Lan Prop. 7) | `O(1 + √(LR²/ε) + σ²R²/ε²)` |

The two bounds match only when the noise term dominates (`σ² ≥ Lε`). Otherwise this theorem is slower by a factor of up to `√(LR²/ε)`; for example, at `σ = 0` it needs `LR²/ε` calls where AC-SA needs `√(LR²/ε)`. Even among plain SGD analyses, Bubeck's Theorem 6.3 already gives the same order. There, the step is tuned with `R` rather than `ε`, which does not change the information needed overall.

The search found no added scope, adaptivity or output strength: the analysis is the standard distance recursion followed by telescoping. What can be claimed is a correct Lean formalization of a classical result, not a new mathematical guarantee.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
