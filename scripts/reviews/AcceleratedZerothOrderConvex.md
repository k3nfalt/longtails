# Accelerated coordinate finite differences with independent function-value noise

[`result`](../../LongTails/Theorems/AcceleratedZerothOrderConvex.lean) ([setup](../../LongTails/Setups/ZerothOrderSmoothAndConvex.lean), [algorithm `acceleratedGrid`](../../LongTails/Algorithms/AcceleratedZerothOrderConvex.lean)) proves the following. Let `f` on a `d`-dimensional Euclidean space be convex and `L`-smooth, with a minimizer within `R` of `x0`. Each oracle call returns `g(x, ω_k)` with fresh i.i.d. `ω_k`, mean `f(x)` and variance `≤ σ²`. Projected accelerated SGD on `B(x0,R)` uses randomized-offset central coordinate differences with `2d` calls per iteration, and the final accelerated iterate satisfies `E f(x_K) − f* ≤ ε`.

**Proved complexity.** All of `d, L, R, σ, ε` are known. With `budget = 2d·max(1, ⌈128√(LR²/ε) + 32768 LdR²σ/ε² + 8192 Ld²R²σ²/ε³ + 1⌉)`, the bound is

  `N = O( d + d√(LR²/ε) + L d² R² σ/ε² + L d³ R² σ²/ε³ )` noisy function evaluations (d ≥ 1, L, ε > 0, R, σ ≥ 0).

By AM–GM, the middle term is at most `½(dLR²/ε + Ld³R²σ²/ε³)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Standard reduction: AC-SA ([Lan, Math. Program. 133 (2012)](https://optimization-online.org/2008/08/2061/), preprint Cor. 3; journal numbering not checked) applied to the box-smoothed `f_h(x)=E_{z∼U[−h,h]^d} f(x+z)` (my derivation) | `O(d + d√(LR²/ε) + Ld²R²σ/ε² + Ld³R²σ²/ε³)` → same | None: same order | None | None. Both outputs are AC-SA's aggregated final iterate in expectation, and both need `L,R,σ,ε,d` | None |
| [Bach–Perchet, COLT 2016](https://arxiv.org/abs/1605.08165), Prop. 7 (unconstrained convex β=2, two-point, independent noise), after rescaling `x=x0+Ry`, `f/(LR²)` | `O(d² + d²(LR² + σ²/(LR²))³/ε³)` → `O(d + d√(LR²/ε) + Ld²R²σ/ε² + Ld³R²σ²/ε³)` | Better when `σ ≤ LR²/√d`: for `σ=0`, `d²(LR²/ε)³` → `d√(LR²/ε)`. Worse when `LR²/√d < σ < d^{1/4}LR²`, by up to a factor `d` at `σ≈LR²` | None (same class and noise model) | Their bound is untuned in `σ`. Selected gives a last accelerated iterate; their output is the iterate of eq. (5), and averaging was not resolved from the text | Selected uses `σ` for tuning and has a `d³` noise term instead of `d²` |
| [Lattimore–György, COLT 2021](https://proceedings.mlr.press/v134/lattimore21a.html), Thm. 1 (constrained stochastic BCO). Special case: sub-Gaussian noise of scale `≲LR²` | Online-to-batch on `K=B(x0,R)`, where the range is `≤2LR²`: `Õ(d⁹(LR²)²/ε²)` → selected `≈ d³(LR²/ε)³` at `σ≈LR²` | Worse in ε: theirs wins when `LR²/ε ≳ d⁶·polylog` | Selected allows finite-variance (not sub-Gaussian) noise | Theirs needs no smoothness. It outputs an averaged point | Normalizing losses to `[0,1]` with unknown `f*` was not checked |
| Repository: [`AcceleratedTwoPointZerothOrderConvex`](../../LongTails/Theorems/AcceleratedTwoPointZerothOrderConvex.lean), same `spec`, same commit `b1c09a0` | `O(1 + d√(LR²/ε) + Ld²R²σ/ε² + Ld²R²σ²/ε³)` → selected | Worse: noise term larger by a factor `d`, with no compensating regime | None | None | None |

**Reduction check.** Box smoothing satisfies `0 ≤ f_h − f ≤ Ldh²/6`, and `f_h` is convex and `L`-smooth. Averaging the central difference over the cube offset gives `∂_i f_h` exactly, by the fundamental theorem of calculus. The variance is at most `dσ²/(2h²) + O(dL²h²)`. Lan's bound `O(√(LR²/ε) + R²v/ε²)` with `h² = min(ε/(Ld), σ/L)` then reproduces every term of the budget, including the cross term. The midpoint grid only discretizes the offset law; I found no new mechanism. This is proof ancestry: AC-SA plus randomized smoothing (Hu et al. 2016, [arXiv:1609.07087](https://arxiv.org/abs/1609.07087), Prop. 3). Hu et al. Thms. 2–3 also show that `n^{-1/3}` (i.e., `ε⁻³`) cannot be beaten using only the bias/variance properties of such estimators.

**Search coverage (2026-10-07).** I searched arXiv, PMLR and Optimization Online for zeroth-order and bandit convex optimization with independent noise. Sources checked: Akhavan et al. 2023 (no plain-convex result), Gorbunov–Dvurechensky–Gasnikov (common-sample plus bounded noise; not applicable), arXiv:2607.19965 (paired samples) and Gasnikov et al.'s survey §4.4. There is no companion note. The theorem first appeared on 2026-09-21 (`ea894ff`, with an `ε⁻⁴` budget); the current form dates from 2026-09-22. All cited literature predates it.

**Conclusion**

**No: this is a routine corollary, not a new complexity bound or setup.**

The strongest baseline is a standard composition. Lan's accelerated stochastic approximation (AC-SA), run on a box-smoothed surrogate, takes randomized central differences as unbiased gradients with variance `≈ dσ²/h²`. It gives exactly the proved budget:

  `O(d + d√(LR²/ε) + L d² R² σ/ε² + L d³ R² σ²/ε³)`.

Against Bach–Perchet's published two-point bound, the result wins when `σ ≤ LR²/√d`, mainly through the accelerated noiseless term. That gain is the routine effect of acceleration plus tuning to the known `σ`, which the reduction already delivers. In the noise-dominated regime the result loses a factor `d`, both to that bound and to the repository's same-setup two-point theorem.

For high accuracy, bandit convex methods reach `Õ(poly(d)/ε²)` under sub-Gaussian noise, so the `ε⁻³` rate is not optimal for the class. The finite-variance noise model is the only scope difference I found, and I did not check whether those methods extend to it. The literature search also did not find an explicitly published accelerated statement for this exact noise model. Even so, it follows from checked theorems.

The only claimable contribution is a Lean formalization of a standard accelerated finite-difference bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
