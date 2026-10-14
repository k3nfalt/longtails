# Spectral scalar-step gradient method with quadratic window convergence

[`result`](../../LongTails/Theorems/SpectralGradientQuadraticConvergence.lean) proves the following in the [setup](../../LongTails/Setups/MinimizerRegularHessian.lean). Take a `d`-dimensional (`d ≥ 1`) real Hilbert space and a twice differentiable, μ-strongly convex function with an L-Lipschitz gradient. Assume `‖∇²f(x)−∇²f(x*)‖ ≤ M‖x−x*‖` and `‖x0−x*‖ ≤ R`, with L, μ, M, R known. Under these assumptions, the deterministic [algorithm](../../LongTails/Algorithms/SpectralGradient.lean) returns a last iterate with `f(x_out)−f* ≤ ε`. The algorithm uses only scalar steps `x ← x − η∇f(x)`: a warmup with η = 1/(2L), then repeated windows of d probing steps and d steps equal to reciprocal eigenvalues of a fitted symmetric model.

**Proved budget.** All oracle calls are exact gradient calls. With κ = L/μ, Θ = MLR/μ² and ℓ = log(1 + L²R²/(με)), the proved budget is `⌈2κ log(2+8(d+1)²(4κ²)^d Θ)⌉ + 2d⌈log₂(1+ℓ)⌉`. Its order is

  **N_sel = O( κ·log(2 + (d+1)²(2κ)^{2d}·MLR/μ²) + d·log(2 + log(1 + L²R²/(με))) ).**

For `M > 0`, the first term is of order `κ[d log(2κ) + log(d+1) + log(1+Θ)]`.

**Reduction check (finite-difference Newton).** The oracle accepts any query point, so any gradient method is admissible. First run Nesterov's accelerated gradient method ([Bubeck, Thm 3.18](https://arxiv.org/pdf/1405.4980)). It gives `‖x−x*‖² ≤ 2κR²e^{−(t−1)/√κ}`, so after `O(√κ log(2 + √(dκ)MR/μ))` calls, `r = ‖x−x*‖ ≤ μ/(12√d M)`. Next, take Newton steps with a forward-difference Hessian: query `∇f(x)` and `∇f(x+h eᵢ)` for i = 1, …, d, with `h = ‖∇f(x)‖/L ≤ r`, and symmetrize the resulting matrix. The anchored bound and the mean-value inequality for `∇f − ∇²f(x*)` give each column an error of at most `2Mr`. Therefore `‖Ĥ−∇²f(x*)‖ ≤ 2√d Mr ≤ μ/6`, and `‖∇f(x)−∇²f(x*)(x−x*)‖ ≤ Mr²`. This gives `r⁺ ≤ (6√dM/μ) r²`. As a result, `O(log log(1+L²R²/(με)))` Newton steps of `d+1` calls reach ε. This is the textbook finite-difference Newton method (Dennis–Schnabel 1983, §5.4; I did not recheck the book's exact theorem), and I verified the analysis above directly. It needs only the anchored Hessian condition and the same known parameters. If M = 0, a single Newton step is exact.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| AGD warmup + forward-difference Newton (standard reduction verified above; components predate 2026-09-29) | `O(√κ log(2+√(dκ)MR/μ) + d log(2+log(1+L²R²/(με))))` → N_sel | **Worse:** the second terms have the same order (`d+1` vs `2d` calls per round). The first term is larger by at least a factor of √κ for every parameter choice, and by about `√κ·d log κ / log(dκΘ)` when Θ ≥ 1 | None (same class, oracle and known parameters) | None (both give the last iterate and a deterministic objective gap) | The selected method uses only scalar steps along the current gradient. The baseline queries d off-iterate points and solves a d×d linear system; the selected method also solves d×d fit and eigenvalue problems. |
| Nesterov AGD, [Bubeck Thm 3.18](https://arxiv.org/pdf/1405.4980) (2015) | `O(√κ log(1+LR²/ε))` → N_sel | **Better when** `κ[d log(2κ)+log(d+1)+log(1+Θ)] + d log log(…) ≪ √κ log(1+LR²/ε)`, e.g. with d, κ and Θ fixed and ε → 0. **Worse** at moderate accuracy, or when d log κ ≳ log(LR²/ε)/√κ | AGD class is broader: L-smooth, μ-strongly convex → adds the anchored Hessian condition, finite d, and known M, R | None | The selected method needs the extra Hessian assumption and must know M and R |
| Silver stepsizes, [Altschuler–Parrilo](https://arxiv.org/abs/2309.07879) (JACM 2025) | `O(κ^{0.786} log(1+LR²/ε))` → N_sel | Same high-accuracy regime as the AGD row; AGD already beats silver | Silver is also a scalar-step schedule, on a broader class | None | Same as the AGD row |

**Ancestry and mechanism.** The companion note's genuinely new step bounds the gradient after one nonlinear window using the polynomial action of any feasible symmetric fit, without requiring the fit to converge in operator norm. It builds on known tools: Fletcher's LMSD sweeps, symmetric secant fitting ([Ferrandi–Hochstenbach 2024](https://link.springer.com/article/10.1007/s11075-024-01895-9)), bounded minimal-polynomial coefficients, and the anchored Hessian condition of [Jin–Mokhtari](https://link.springer.com/article/10.1007/s10107-022-01887-4). The reduction above shows that the window bound does not follow from these tools by simple substitution. It also shows that the window bound is unnecessary for the class-level complexity.

**Search coverage (2026-10-07).** I searched arXiv and journal sources on LMSD and spectral steps, finite-difference Newton, and silver/AGD baselines. Recent scalar-step work is quadratic-only: [Yang–Yuan, arXiv 2609.12114](https://arxiv.org/abs/2609.12114) (Sept 10, 2026), [Gu, arXiv 2609.25800](https://arxiv.org/abs/2609.25800) (Sept 22, 2026), and [arXiv 2606.25311](https://arxiv.org/abs/2606.25311). Narushima et al. give only a trajectory-conditional superlinear result. Git history shows the theorem was introduced on 2026-09-29. I did not find an earlier explicit global quadratic oracle bound for a pure scalar-gradient method. I did not access the Dennis–Schnabel text, so that citation rests on the derivation above rather than on the book. The companion note compares only against scalar-step and silver baselines and omits finite-difference Newton, which is the decisive baseline.

## Conclusion

**No: the selected result does not improve complexity on its problem class. It gives a new guarantee only for a restricted scalar-step algorithm family.**

Under exactly the same assumptions, oracle and known parameters, a standard AGD warmup followed by forward-difference Newton gives:

| | first phase | quadratic phase |
|---|---|---|
| finite-difference Newton | `√κ log(2+√(dκ)MR/μ)` | `d log log(L²R²/(με))` |
| selected | `κ·log(2+(d+1)²(2κ)^{2d}MLR/μ²)` | `d log log(L²R²/(με))` |

So, up to constants, the baseline is at least as good for every parameter value. The selected method's warmup is worse by at least a factor of √κ, and by about √κ·d log κ when MLR/μ² ≥ 1.

The selected bound does beat AGD and silver stepsizes at very high accuracy. That advantage comes from the extra Hessian assumption, and Newton-type methods exploit the same assumption more cheaply.

What is plausibly new is the first explicit, global, doubly-logarithmic oracle bound for a method restricted to scalar steps along current gradients. I found no earlier such result, but the search cannot establish priority. This is a method-specific analysis, not an improvement for the optimization problem. As with the negative examples, fixing the algorithm family does not exempt the result from comparison with stronger applicable methods.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
