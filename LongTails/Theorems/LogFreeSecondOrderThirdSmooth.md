# Log-free optimal second-order complexity under third-order smoothness

## Result and scope

[The Lean theorem](LogFreeSecondOrderThirdSmooth.lean) gives an oracle bound for finding an **ε-first-order stationary point** of a general nonconvex function on any finite-dimensional real Hilbert space. The method is a **second-order method**: it queries only function values, gradients and Hessians, never third derivatives or tensor models. It exploits a Lipschitz third derivative. The bound is dimension-free and has no multiplicative logarithm. The theorem does not assert second-order stationarity or global optimality.

**Setup.** The [setup](../Setups/ThirdDerivativeSmoothNonconvex.lean) is reused unchanged. It is the class of [LazyQuarticHessianTradeoff](LazyQuarticHessianTradeoff.md):
- f is C³ and its third derivative is globally L₃-Lipschitz in the nested operator norm;
- f(x₀) − f(x) ≤ Δ for every x;
- ‖∇²f(x₀)‖ ≤ H₀.

There is no global Lipschitz-gradient or Lipschitz-Hessian assumption, no bound on iterates, and no known minimum value. Two exact channels return (f(x), ∇f(x)) and ∇²f(x), respectively.

**Information used.** The [algorithm](../Algorithms/LogFreeProxNewton.lean) receives the public parameters (x₀, L₃, Δ, H₀, ε). Its update rules use only L₃ and ε. Δ and H₀ enter only the number of executed steps, and therefore the budget.

**Guarantee.** Write

S = Δ L₃^{1/3} / ε^{4/3},  Γ = 2 + H₀Δ/ε² + L₃Δ³/ε⁴.

The public budget is the same one-line formula on both channels:

⌈2³⁰ (1 + S + log Γ)⌉ oracle calls.

The algorithm runs ⌈2²⁷(1 + S + log Γ)⌉ steps of exactly eight queries each: six value/gradient queries and two Hessian queries. It also makes one initial query on each channel. Every probe, line-search candidate, escape candidate, landing Hessian and padding query is charged.

The output of `execute` satisfies ‖∇f(output)‖ ≤ ε. Since the answers are exact, the plan's counts fit in the budget, and `execute` then returns the full plan's output (`execute_of_counts`). The conclusion holds for every oracle seed, and the setup records it as an almost-sure statement.

**Optimality.** Carmon, Duchi, Hinder and Sidford, [*Lower bounds for finding stationary points I*](https://arxiv.org/abs/1710.11606) (Math. Program. 184, 2020), Theorem 2, give the matching lower bound Ω(ΔL₃^{1/3}ε^{-4/3}):
- it applies to any randomized algorithm that receives the value and **all** derivatives of f at each query point;
- it uses functions with L₃-Lipschitz third derivative and initial gap Δ;
- its hard instances have dimension of order T² log T, where T is the lower bound on the number of queries.

So whenever S ≥ log Γ, the bound proved here is optimal up to a universal constant, even against third- or higher-order oracles in sufficiently high dimension. The log Γ term is additive and is paid only once.

## Algorithm

**Scales.** Let
- r = (ε/L₃)^{1/3};
- u = εr = L₃r⁴ (the decrease unit);
- γ = 256 L₃r²;
- q = u/4096;
- λ*² = u/2²⁰;
- ζ_j = 2^{-(j+4)}.

**Phases.** A phase with center c works on the proximal function F(y) = f(y) + (γ/2)‖y − c‖². At the current iterate y, B = ∇²f(y) + γI, d solves Bd = −∇F(y), and λ² = ⟨Bd, d⟩ is the Newton decrement.

*Global mode:*
- **success:** if f(y) ≤ f(c) − q, the iterate becomes the new center;
- **plain escape:** if some unit v has ⟨∇²f(y)v, v⟩ ≤ −γ/4, the better of y ± rv becomes the new center;
- **tail entry:** if λ² ≤ λ*², switch to tail mode;
- **grid Newton step:** otherwise, take the Newton step capped at length r. Of the five step lengths {1, ½, ¼, ⅛, −1}, keep the one with the smallest F-value.

*Tail mode:* take full Newton steps y' = y + d, and test consecutive Hessians: −ζ_jB ≼ ∇²f(y') − ∇²f(y) ≼ ζ_jB.
- If the test passes, the level j advances.
- If it fails, take a *magnified escape*. Let w be a violating direction normalized by ⟨Bw, w⟩ = 1, and σ the sign of the violation. Let s = 8√(u/λ²) and z = y − σs·d. The best (by f-value) of the three candidates z ± r·w/‖w‖ and y + σs·d becomes the new center.

**Output.** The first iterate with ‖∇f‖ ≤ ε, kept fixed afterwards.

## Proof mechanism

| Step | Lean | Normalized bound |
|---|---|---|
| Five-point cubic line search | [LogFreeLineSearch](../Proofs/LogFreeLineSearch.lean) `grid_descent` | some point of {1, ½, ¼, ⅛, −1} decreases the cubic model by a/48 |
| Grid Newton step | [LogFreeSteps](../Proofs/LogFreeSteps.lean) `newton_grid` | F drops by ≥ min(λ²/64, 3u) |
| Plain escape | [LogFreeGeometry](../Proofs/LogFreeGeometry.lean) `plain_escape` | f drops by ≥ 31u |
| Tail contraction | [LogFreeTail](../Proofs/LogFreeTail.lean) `tail_contraction` | λ'² ≤ λ²/16 and F drops by λ²/3 |
| Magnified escape | [LogFreeEscape](../Proofs/LogFreeEscape.lean) `magnified_escape` | f drops by ≥ sζ_j u ≥ 2⁹·2^j u |
| Final tail | [LogFreeInvariant](../Proofs/LogFreeInvariant.lean) `tail_final` | ‖∇f‖ ≤ ε once j ≥ ⌈20 + 2 log Γ⌉ |
| Amortized count | [LogFreeStepGood](../Proofs/LogFreeStepGood.lean), [LogFreeExecution](../Proofs/LogFreeExecution.lean) | a measure falls by ≥ 1 per step |

**Tail contraction.** A passing test bounds the third derivative along d relative to B. Polarization and Cauchy–Schwarz for positive semidefinite forms ([LogFreeLinearAlgebra](../Proofs/LogFreeLinearAlgebra.lean)) then give λ' ≤ λ/4. The thresholds ζ_j are summable, so positive definiteness survives the drift.

**Magnified escape.** A failing test certifies that ⟨D³f(y)[d]w, w⟩ is relatively large *across the last step itself*. Extrapolating along the Newton direction costs only s²λ²/2 = 32u in the quadratic term, while the induced negative curvature produces a gain that grows like ζ_j/λ_j. A two-case split controls the cubic term T[d, d, d]: either the plane candidates z ± rw/‖w‖ or the line candidate y + σs·d works.

**Amortization.** Write base(c) = M(f(c) − f(x₀) + Δ)/q with M = 2¹⁴ + 3, and K_fin = ⌈20 + 2 log Γ⌉. The termination measure is base(c) + K_fin plus:
- 1 − j in tail mode;
- 2 + max(0, 64(F(y) − f(c) + q)/λ*² + 1) in global mode.

The measure falls by at least one at every step. A tail of length j ends with a decrease of order 2^j q, so it pays for itself. Only the final, stationary tail pays the additive log Γ term.

**Log Γ term.** A Hessian growth bound from the gap ([ThirdOrderOperatorBounds](../Proofs/ThirdOrderOperatorBounds.lean) `hessian_growth`) is combined with the a priori path length ≤ 2r·(number of steps). In any tail with j ≥ 1 the decrement satisfies λ_j² ≤ 3Δ·16^{-j}, so K_fin = O(log Γ) even when S < 1.

## Closest results and contribution

| Result | Assumptions / oracle | Bound | Relation |
|---|---|---|---|
| He–Zhang, [arXiv:2610.36256v1](https://arxiv.org/abs/2610.36256) (26 Oct 2026; unreviewed preprint), Theorem 4.7 | Global L_H-Lipschitz Hessian **and** L_T-Lipschitz third derivative; second-order oracle; (ε_g, ε_H)-SOSP | Õ(Δ max{L_T^{1/3}ε_g^{-4/3}, L_Tε_H^{-2}}); each outer iteration uses up to 1 + log₄(1 + L_Hμ/(L_Tε_g)) Newton steps | Their Concluding Remarks ask whether this logarithm can be removed. We remove it for first-order stationarity, and we also drop the global Lipschitz-Hessian assumption. We do not prove their SOSP statement. Their curvature test (10) compares ∇²f(x_{k,t}) with ∇²f(x_k) at the outer point. Ours compares consecutive iterates, with summable thresholds. |
| Birgin et al., Math. Program. 2017 (AR_p with p = 3) | Third-order oracle and approximate model minimization | O(ΔL₃^{1/3}ε^{-4/3}) | Same order, without third derivatives or tensor subproblems. |
| Doikov–Grapiglia, [arXiv:2510.07992](https://arxiv.org/abs/2510.07992) (Math. Program. 2026), Corollary 3.6 | Second-order oracle with finite-difference tensors | O(d^{1/3}S + d) | The dimension factor is removed. |
| Carmon–Duchi–Hinder–Sidford, [*Convex until proven guilty*](https://proceedings.mlr.press/v70/carmon17a.html) (ICML 2017), Theorem 2 | Gradient-only; global L₁ and L₂ (plus L₃) | O(ΔL₁^{1/2}L₃^{1/6}ε^{-5/3} log(1/ε)) up to lower-order terms | Different oracle. Hessians allow the optimal exponent. |
| Repository [LazyQuarticHessianTradeoff](LazyQuarticHessianTradeoff.md), same setup | Value/gradient and Hessian channels | 2⁹⁰(1 + S^{5/4}) log Γ value/gradient calls; 2⁶²(1 + S^{3/4}) Hessian calls | We use fewer total calls and fewer value/gradient calls, but **more Hessian calls** (S versus S^{3/4}). When a Hessian costs much more than a gradient, neither result dominates. |

**Contribution.** This is the first dimension-free second-order method with oracle complexity O(S) + O(log Γ) under third-order smoothness alone. It matches the any-order lower bound up to a universal constant. Its new technique combines three pieces:
- consecutive relative-Hessian tests with summable thresholds;
- an escape along the Newton direction whose gain grows exponentially in the tail length;
- an amortized termination measure.

## Scope requirement

This is a second-order (Hessian-oracle) method exploiting third-order smoothness, so it fits the requested scope, "second and third order optimization".

## Limitations

- **Constants.** The universal constants are enormous (2³⁰ in the budget). This is an oracle-complexity result, not a practical method.
- **Stationarity.** The guarantee is first-order only. The stop test fires before any curvature test, so the returned point need not be a tail iterate and carries no second-order guarantee. A second-order (SOSP) version would need a modified stop rule.
- **Cost model.** Exact dense Hessians are used. Eigenvector choice, linear solves and the relative-Hessian test are arithmetic, and arithmetic is not charged.
- **Padding.** The fixed-budget framework keeps querying after the output is found.
- **Hessian count.** The worst-case Hessian count is Θ(S), larger than LazyQuartic's S^{3/4}.
- **Lower-bound conditions.** Optimality relies on Carmon et al.'s high-dimensional construction.
- **Competing preprint.** The He–Zhang preprint was posted eleven days before this assessment and has not been peer reviewed.

## Literature coverage

The assessment was made on 6 November 2026 UTC and rechecked on 7 November 2026 UTC.
- **Surveyed by both agents independently:** ICML 2025/2026, ICLR 2025/2026, NeurIPS 2024/2025 and roughly the last two years of arXiv (math.OC, cs.LG), covering cubic-regularized and tensor methods, lower-order implementations, lazy and inexact Hessians, minimax and VI second-order methods, and lower bounds.
- **Read in full:** He–Zhang 2610.36256v1 (still the only version on 7 November 2026) (Theorem 4.7, Algorithm 2 and the Concluding Remarks) and Doikov–Grapiglia 2510.07992.
- **Checked:** the math.OC listing for 30 Oct–6 Nov 2026. No log-free or Lipschitz-Hessian-free dimension-free second-order result under third-order smoothness was found, and no open repository PR covers this question.
