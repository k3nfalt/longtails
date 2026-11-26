# Novelty assessment: `HessianStableExpectedNewton`

[`result`](../../LongTails/Theorems/HessianStableExpectedNewton.lean) proves a guarantee for the repository's ball-anchored Newton method ([algorithm](../../LongTails/Algorithms/BallAnchoredNewton.lean)) on the [setup](../../LongTails/Setups/HighDimensionalHessianStableSkewMonotone.lean) `HighDimensionalHessianStableSkewMonotone`:
- **Problem class.** Monotone `F : ℝ^d → ℝ^d` whose Jacobian is `DF = S + H(x)`, with `S` constant skew and `H(x)` symmetric, PSD and `M`-Hessian-stable.
- **Oracle.** Exact `F` and `DF` queries.
- **Guarantee.** The method outputs a stopped iterate with `E‖F(x̂)‖ ≤ ε`. The method is deterministic, so the expectation is the deterministic value.

**Budget, per channel (both `F` and `DF` calls are counted):**

  N = O( (MD)^{2/3} · log³(MD + MΛD²/ε) )

The parameters are:
- `M`: the Hessian-stability constant;
- `D ≥ ‖x₀ − x⋆‖`;
- `ε`: the target residual;
- `Λ`: a bound on `‖DF‖` over `B(x⋆, 3D + 1/(4M))`. The algorithm does not use `Λ`.

This simplifies the Lean budget `⌈2¹⁷(1 + (MD)^{2/3}) log³(3 + MD + MΛ(D + 1/M)²/ε)⌉`. The simplification is valid because `valid` forces `MD ≥ 2⁶⁰`, so `D + 1/M ≤ 2D`, and `ε(MD)² ≤ ΛD`, so the logarithm's argument is at least `(MD)³`. `valid` also requires `d ≥ 2²¹(MD)^{10/3}`. Each Newton step's ball-constrained affine VI is not charged.

**What the proof does.** It only applies an inclusion:
- `valid` here implies `valid` of [`HessianStableSkewMonotone`](../../LongTails/Setups/HessianStableSkewMonotone.lean);
- `admissible` is copied verbatim;
- the almost-sure residual bound of [`HessianStableSkewNewton`](../../LongTails/Theorems/HessianStableSkewNewton.lean) (`run_finishes`, `total_le`, `execution_output`) is converted to a constant integrand.

The budget formula is identical to the parent's.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [`HessianStableSkewNewton`](../../LongTails/Theorems/HessianStableSkewNewton.lean) (commit 2476f596, 2026-11-06; prior within the repository). Same class, same algorithm. | `⌈2¹⁷(1+(MD)^{2/3}) log³(3+MD+MΛ(D+1/M)²/ε)⌉` per channel → the identical formula | None: identical budget | None. Space `E` (any finite dimension) → `ℝ^d` with `d ≥ 2²¹(MD)^{10/3}`. This is a restriction. | Deterministic (a.s.) `‖F(x̂)‖ ≤ ε` → `E‖F(x̂)‖ ≤ ε`. This is weaker, and it follows immediately from the parent. | Adds `MD ≥ 2⁶⁰`, `ε(MD)² ≤ ΛD` and `d ≥ 2²¹(MD)^{10/3}`. These are needed only for the companion lower bound. |
| Jiang–Yoon, second-order AEP ([arXiv:2609.30212](https://arxiv.org/abs/2609.30212) v1, Sep 2026, unrefereed; theorem numbers as recorded in the parent review). **Overlap only:** instances with a globally `L₂`-Lipschitz `DF`. | `O((L₂D²/ε)^{2/5} log(1+L₂D²/ε))` → `O((MD)^{2/3} log³(MD+MΛD²/ε))` | Same gain as the parent: polylogarithmic rather than polynomial dependence on `1/ε`. It holds when `(L₂D²/ε)^{2/5} ≫ (MD)^{2/3} log³(MD+MΛD²/ε)`. | The classes are incomparable, as for the parent. | None (both certify the residual) | This file adds nothing beyond the parent. It narrows the regime further (`MD ≥ 2⁶⁰`). |
| Carmon et al., ball acceleration ([NeurIPS 2020, arXiv:2003.08078](https://arxiv.org/abs/2003.08078)); Doikov ([arXiv:2308.14742](https://arxiv.org/abs/2308.14742), Math. Program. 2025). **Special case only:** `S = 0`. | `Õ((MD)^{2/3})` linear-solve steps → the same order | None: same order up to logarithms | `S = 0` → constant skew `S`, which the parent already provides | Objective gap → residual. This conversion costs only logarithms. | None beyond the parent |

**Reduction check.** The selected theorem is a direct corollary of `HessianStableSkewNewton`, obtained by restricting parameters and weakening a.s. accuracy to expectation. It contains no new mechanism.

**Proof ancestry.** The parent supplies all of the mathematics: the skew-robust ball-constrained Newton contraction, Jiang–Yoon's anchored potential, and Carmon et al.'s growth argument.

**Matching lower bound.** The companion [`HessianStableNewtonLowerBound`](../../LongTails/Theorems/HessianStableNewtonLowerBound.lean) uses this exact setup. It gives `⌊(MD/(2¹⁸ log(2+MD)))^{2/3}⌋` per channel, with instances from the `S = 0` subclass. Paired with this result, the remaining gap is `polylog(MD) · log³(MD + MΛD²/ε)/log³(MD)`. That novelty belongs to the lower bound, not to this file.

**Search coverage (2026-11-26).** I searched arXiv and NeurIPS/ICML/ICLR sources for ball-oracle or quasi-self-concordant methods for monotone VIs and saddle problems, and for second-order minimax methods.
- **Findings.** I found nothing after 2026-11-06 that supersedes or anticipates the parent's guarantee. The results found were [arXiv:2609.23557](https://arxiv.org/abs/2609.23557), [2608.08463](https://arxiv.org/abs/2608.08463), [2506.08362](https://arxiv.org/abs/2506.08362) and [2410.09568](https://arxiv.org/abs/2410.09568). All are polynomial in `1/ε` under Lipschitz high-order derivatives.
- **Not re-read.** I did not re-read the AEP and Carmon theorem statements for this report. Those rows rely on the parent review's checks.
- **Companion note.** It accurately states "Nothing about the algorithm or its rate" is new. The two caveats below are not stated in it, and I flag them here:
  - it calls the pair the second-order complexity "of the class", but the lower-bound instances have `S = 0` and are confined to the large-`MD`, high-dimensional regime;
  - it does not mention the parent review's correction of the exp-curvature `log³` blow-up.

## Conclusion

**No: this file is a restatement of an existing repository theorem under narrower conditions and a weaker accuracy criterion.**

The strongest relevant baseline is the repository's own [`HessianStableSkewNewton`](../../LongTails/Theorems/HessianStableSkewNewton.lean). It covers the same instance class with the same algorithm and the same budget:

| | Class / regime | Accuracy | Calls per channel |
|---|---|---|---|
| `HessianStableSkewNewton` | any finite dimension, `M, D, ε > 0` | `‖F(x̂)‖ ≤ ε` deterministically | `O((1+(MD)^{2/3}) log³(3+MD+MΛ(D+1/M)²/ε))` |
| This result | `d ≥ 2²¹(MD)^{10/3}`, `MD ≥ 2⁶⁰`, `ε(MD)² ≤ ΛD` | `E‖F(x̂)‖ ≤ ε` | identical |

The Lean proof is a short inclusion argument: valid parameters transfer and the deterministic bound integrates to itself. The point of the file is to place the upper bound in the same `NonConvergence` setup as the companion lower bound, so that the two can be paired.

The literature-level contribution is the parent's. That is a polylog-in-`1/ε`, `Õ((MD)^{2/3})` second-order guarantee for Hessian-stable monotone equations with constant skew coupling; its own review supports it with medium confidence. Any claim that the `(MD)^{2/3}` exponent is tight belongs to the lower-bound theorem.

What can be claimed here is only a bookkeeping corollary that makes the upper and lower bounds directly comparable.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
