# Novelty review: StrongGrowthMeanSquaredUpperBound

[`result`](../../LongTails/Theorems/StrongGrowthMeanSquaredUpperBound.lean) proves `E[f(y_K)] − f(x⋆) ≤ ε` for the last outer iterate of [ProximalStorm](../../LongTails/Algorithms/ProximalStorm.lean) on [EuclideanStrongGrowthMeanSquared](../../LongTails/Setups/EuclideanStrongGrowthMeanSquared.lean). The theorem is a direct transfer of the earlier [ProximalStormStrongGrowth](../../LongTails/Theorems/ProximalStormStrongGrowth.lean) theorem through [`inclusion`/`transfer`](../../LongTails/Proofs/StrongGrowthMeanSquaredInclusion.lean).

**Class and oracle.** `f : ℝᵈ → ℝ` is convex and differentiable, with a minimizer satisfying `‖x₀ − x⋆‖ ≤ R`. The oracle is IID and same-sample: a query `(x, y)` returns `(g(x,ξ), g(y,ξ))`. It is unbiased and satisfies strong growth (SGC), `E‖g − ∇f‖² ≤ Γ²‖∇f‖²`, and mean-squared smoothness (MSS), `E‖g(x) − g(y)‖² ≤ L̄²‖x − y‖²`. The `admissible` and `successful` predicates are reused verbatim from the parent setup [StrongGrowthMeanSquaredSmoothConvex](../../LongTails/Setups/StrongGrowthMeanSquaredSmoothConvex.lean). The only differences are in `valid`, which adds four restrictions:

- `E = ℝᵈ` instead of a general Hilbert space;
- `R > 0`;
- `2²⁶√(1+Γ²)·ε ≤ L̄R²`;
- `d ≥ (L̄R²/(√(1+Γ²)ε))³`, and `Ω` has two distinct measurable atoms.

**Budget.** The proved budget is `⌈√(2L̄R²/((1+Γ)ε))⌉·⌈(1+Γ)²(4810 + 3200 log(1+Γ))⌉` pair calls, the same as the parent theorem. Here `L̄` is the MSS constant, `Γ` the relative noise level, `R` the initial distance and `ε` the expected accuracy. On the valid regime, `√(L̄R²/ε) ≥ 2¹³(1+Γ²)^{1/4}`, so the first ceiling is within a factor `1 + 2⁻¹³` of its argument, and the parent bound's additive `(1+Γ)²log` term is dominated. The budget is therefore

> **N = O( (1+Γ)^{3/2} (1 + log(1+Γ)) √(L̄R²/ε) )**.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository: [ProximalStormStrongGrowth](../../LongTails/Theorems/ProximalStormStrongGrowth.lean) (commit `8102682`, 2026-10-18), on a superclass | `O((1+Γ)^{3/2}(1+log(1+Γ))√(L̄R²/ε) + (1+Γ)²(1+log(1+Γ)))` → the identical numeric budget, i.e. `N` | None: identical budget, same algorithm and same proof | None. The class narrows: Hilbert space → `ℝᵈ` with polynomial `d`, `R ≥ 0` → `R > 0`, all `ε` → `ε ≤ L̄R²/(2²⁶√(1+Γ²))`. | None: same last-iterate expected gap and the same known parameters | Strictly narrower scope. The restrictions exist only to fit the companion lower bound. |
| Vaswani–Bach–Schmidt, AISTATS 2019 ([arXiv 1810.07288](https://arxiv.org/abs/1810.07288)), Thm 2: accelerated SGD under SGC (single-sample, `L`-smooth `f`, `L ≤ L̄`) | `O((1+Γ²)√(LR²/ε))` → `N` | Inherited from the parent theorem: a factor ≈ `√(ΓL/L̄)/log(e(1+Γ))` when `L̄ ≪ ΓL/log²(e(1+Γ))`. Worse by a log factor when `L̄ ≳ ΓL`. | None: SGC+MSS is narrower than SGC | None | Needs MSS and the same-sample pair oracle |
| Gupta–Siegel–Wojtowytsch, NeurIPS 2024 ([arXiv 2302.05515](https://arxiv.org/abs/2302.05515)), Thm 3 (AGNES) | `O((1+Γ²)√(LR²/ε))` → `N` | Same as the row above | None | None | Same as the row above |

**Reduction check.** The theorem is a literal corollary. `transfer` applies `ProximalStorm.result` through an inclusion whose validity map only drops the new restrictions, and whose admissibility and success maps are the identity. Its proof has no new mathematical step. The only substantive mechanism is the parent's: MSS anchored at the exact prox point, with STORM inner solves inside an A-HPE outer loop (Monteiro–Svaiter 2013). The [existing review](ProximalStormStrongGrowth.md) assesses that mechanism.

**Search coverage.** On 2026-11-17 I searched arXiv and the web for accelerated or variance-reduced methods under SGC with MSS or STORM, and for SGC lower bounds. Besides the baselines in the table, the searches returned Mishkin–Pilanci–Schmidt ([2404.02378](https://arxiv.org/abs/2404.02378); v2 withdrew its `√ρ` claim), Hermant et al. ([2410.07870](https://arxiv.org/abs/2410.07870)), [2605.14800](https://arxiv.org/abs/2605.14800) (clipped/normalized SGD) and [2408.01839](https://arxiv.org/abs/2408.01839) (local PŁ). None gives an accelerated SGC+MSS upper bound, before or after 2026-10-18. I did not re-read the full theorems of these sources and relied on the existing review's checks of Vaswani et al. and AGNES.

**Companion note.** The [companion note](../../LongTails/Theorems/StrongGrowthMeanSquaredUpperBound.md) states correctly that this is "not a new upper-complexity claim". It is consistent with the Lean statement. Its tightness claim depends on the companion [lower bound](../../LongTails/Theorems/StrongGrowthMeanSquaredLowerBound.lean), which is outside this review's scope.

**Conclusion**

**No: this theorem adds no new upper bound; it restates the repository's earlier ProximalStorm guarantee on a smaller class.** The only relevant baseline is the parent theorem ProximalStormStrongGrowth, whose budget is reproduced exactly:

| | Class | Pair calls for `E f(y_K) − f⋆ ≤ ε` |
|---|---|---|
| ProximalStormStrongGrowth (2026-10-18) | SGC+MSS, any Hilbert space, any `ε` | `(1+Γ)^{3/2} log(e(1+Γ))√(L̄R²/ε) + (1+Γ)² log(e(1+Γ))` |
| This theorem | same, restricted to `ℝᵈ`, large `d`, `ε ≤ L̄R²/(2²⁶√(1+Γ²))` | identical budget |

The proof is a one-step transfer through an inclusion map. The added restrictions only align the setup with the companion lower bound and narrow the scope. Any gain over accelerated SGD under strong growth, a factor of about `√(ΓL/L̄)/log` when `L̄ ≪ ΓL`, belongs to the parent theorem and was assessed in its own review.

This file is useful as bookkeeping: together with the lower bound, it lets both halves of a tight characterization be stated for the same setup. Any novelty of that pairing lies in the lower bound. The contribution claimable for this theorem is a formal restatement of a known (repository) result on a subclass.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
