# Gradient descent with energy-paid recovery on Hessian-Lipschitz nonconvex objectives

The [main theorem](RecoveryFractalGdStationarity.lean) proves a deterministic stationarity guarantee for positive adaptive gradient descent on general finite-dimensional smooth nonconvex objectives. Its leading oracle complexity is

\[
\widetilde O\!\left(\Delta L^{2/3}\rho^{1/6}\varepsilon^{-11/6}\right).
\]

This improves the leading exponent of the existing [fractal Chebyshev GD result](FractalChebyshevGdStationarity.lean) from `17/9` to `11/6`. It is a method-family improvement, not a new best complexity for unrestricted first-order algorithms, and not the first nonlinear or subquadratic-in-accuracy GD guarantee. The algorithm needs the gap bound `Δ` in its update tuning; the earlier fractal method does not. The complete bound below retains initialization and recovery costs.

## Problem, information, and output

We reuse exactly [SmoothHessianLipschitzGd.spec](../Setups/SmoothHessianLipschitzGd.lean), with no added assumptions. In any finite-dimensional real inner-product space, let `f` be `C²`, with

\[
\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|,\qquad
\|\nabla^2 f(x)-\nabla^2 f(y)\|_{\rm op}\le\rho\|x-y\|,
\qquad f(x_0)-f(x)\le\Delta\quad\text{for every }x.
\]

Here `L>0`, `ρ≥0`, `Δ≥0`, and `ε>0` are known upper bounds or target accuracy. A minimizer need not exist. There is no convexity, bounded-domain, strict-saddle, spectral-gap, separability, or fixed-dimension restriction. These are the standard smoothness and gap assumptions for Hessian-Lipschitz nonconvex first-order stationarity.

The oracle supplies only the exact gradient at the current iterate. The algorithm queries neither objective values nor Hessian-vector products. Every update has the form `x ← x − η∇f(x)` with `η>0`; there is no momentum, extrapolation, rewind, or zero-step stopping. The setup's `allowedAlgorithm` enforces that update family and the output-selection rule. The output is the queried point with smallest observed gradient norm, with the tie rule specified in the algorithm. The proof establishes `‖∇f(output)‖≤ε` for every oracle and algorithm seed; the framework records the consequent almost-sure guarantee for every seed distribution.

A concrete interacting nonlinear family, in every dimension `d≥2`, is

\[
f(x)=\tfrac\alpha2\|x\|^2+\beta\sum_j(1-\cos x_j)
       +\gamma(1-\cos\langle u,x\rangle),
\]

where `α>0`, `β,γ>0`, and `u` is a unit vector with all coordinates nonzero. One may take `L=α+β+γ`, `ρ=β+γ`, and `Δ=f(x₀)`. The Hessian is a varying diagonal matrix plus a varying rank-one matrix; Hessians at different points generally do not commute. When `β>α`, at `x=(π,…,π)` the Hessian is negative on vectors orthogonal to `u`, so the family is genuinely nonconvex. These dimension-independent bounds demonstrate the theorem's nonlinear scope; this family is not an additional assumption or the source of the novelty claim.

## Algorithm and exact cost

The [algorithm](../Algorithms/RecoveryFractalGd.lean) uses `X=LΔ/ε²` and `a=ρε/L²`. Choose the largest integer `k≥2` satisfying, with `n=2ᵏ` and `m=k+8`,

\[
n^2\le X,\qquad a m^2n^6\le2^{-28},\qquad
2^{16}a m^2n^{17/2}\le X.
\]

The finite search up to `⌊log₂⌈X⌉⌋` is proved exhaustive. If no such level is selected, the method uses ordinary `1/L` GD. Otherwise set `μ=L/n²`, `N=mn`, and `G=√n ε`. One epoch repeats the existing small-step-first fractal Chebyshev schedule on `[μ,L]` exactly `m` times. A trial comprises two epochs.

At an idle point with gradient norm above `G`, take an ordinary `1/L` step. Otherwise start a trial. A queried gradient above `8G` aborts the trial, including at its final endpoint. After an abort, take ordinary GD steps until the accumulated squared gradient norms reach

\[
T=4LU+16NG^2,\qquad
R=32mG/\mu,\quad E=\rho R^2,\quad
U=64NGE/\mu+2mE^2/\mu+\rho R^3.
\]

The aborting query supplies the first recovery step and is counted once. The recovery threshold uses only known parameters and observed gradient norms. A completed trial starts the next idle decision at its endpoint. All queries update the best observed point; the algorithm continues taking positive GD steps even after an accurate point has been found.

The public theorem runs this algorithm using `execute` for exactly

\[
K=\left\lceil 2^{18}\left(8+\log_2\left(2+\frac{L\Delta}{\varepsilon^2}\right)\right)^{4/3}
\left(
\frac{\Delta L^{2/3}\rho^{1/6}}{\varepsilon^{11/6}}
+\frac{\sqrt{L\Delta}}{\varepsilon}
+\frac{L^{11/17}\Delta^{15/17}\rho^{2/17}}{\varepsilon^{28/17}}
+1\right)\right\rceil
\]

gradient calls. The Lean `budget` contains this explicit formula on one line. It counts ordinary steps, both trial epochs, every recovery step, unfinished-group allowance, and the final accuracy query. No hidden Hessian, function-value, verification, restart, or output-selection calls occur.

## Mechanism beyond the earlier analysis

The proof combines four estimates rather than merely substituting a new schedule length into the previous theorem.

1. **Step-weighted impulse control.** For each positive-spectrum window, the preceding step size times the window product has norm at most `4/μ`. The proof retains a dyadic factor in the established fractal tree argument and cancels it against the location-dependent step size. The underlying tree/window theory is prior work. Applying the weighted estimate to actual gradient-difference forcing, rather than independent Taylor residuals, controls positive-gradient drift by a constant times `a m²n⁶ ε`.
2. **Low/high/negative energy separation.** Split the snapshot Hessian at `0` and `μ`. High positive curvature is suppressed by the repeated full-epoch filter, so its final energy is bounded directly by its small model-gradient norm. Low positive curvature has contractive factors and forcing error at most `S E`, where `S` is the epoch step sum. Negative curvature uses inverse-product transport with squared error at most `E² log(1+LS)`. These dimension-free estimates remain valid for the actual nonlinear trajectory through its Taylor residuals. A nonstationary midpoint therefore forces a two-epoch objective decrease of at least `ε²/(512μ)`.
3. **Recovery pays for interrupted trials.** A trial prefix may increase the objective by `U`; the algorithm cannot inspect that increase. Its large abort gradient must lie substantially in the negative snapshot subspace. Backward transport keeps that component large during ordinary-GD recovery, proving the energy threshold is reached within
   `M=N+⌈65536 a m³ n⁷√n⌉+1` updates. Smooth descent pays both the prefix increase and every trial/recovery call. The proof controls the path before crossing the threshold; the final overshooting step uses global smoothness and requires no unjustified local-radius claim.
4. **Actual execution and uniform tuning.** Completed, aborted/recovered, and ordinary groups decrease the objective by at least their update count times `nε²/(1024mL)`. A finite maximal-prefix argument yields `⌈Δ/r⌉+2N+M+1` calls, where `r=nε²/(1024mL)`. The three level caps give an upper bound `1028mX/n+4`; rejection of the next dyadic level yields the displayed explicit budget. This also proves the fallback and zero-parameter boundary cases.

The old `17/9` proof's potential reset requires a start threshold of order `nε`, rather than `√n ε`; its distance-only restart does not provide the gradient gate used here. Ordinary Abel summation in that architecture does not supply the missing path/gradient bootstrap. With the new gate but only the old raw window bound, the corresponding sufficient drift condition scales as `a n⁷` up to logarithms, giving the conditional exponent `13/7`, not `11/6`. The weighted impulse estimate and recovery accounting remove that obstruction. The previous note's speculative `15/8` rate was not a proved theorem and is not treated as one here.

## Closest results and improvement regimes

- **Existing nonlinear fractal GD.** [FractalChebyshevGdStationarity](FractalChebyshevGdStationarity.md) proves `O(X a^(1/9) log(2+1/a)+a^(-1/9)+1)` for positive `ρ`, with exact gradients and the same stationarity target on the same objective class. Its specific stopping/restart family differs. Its updates need `L,ρ,ε`, whereas ours additionally use `Δ`. The new result does not claim its first-nonlinear or first-subquadratic priority.
- **Fractal schedules on quadratics.** Agarwal, Goel and Zhang, [*Acceleration via Fractal Learning Rate Schedules*, ICML 2021](https://proceedings.mlr.press/v139/agarwal21a.html), [arXiv:2103.01338v2](https://arxiv.org/abs/2103.01338v2), Theorems 8–10 and Appendix D.2, provide the prefix/window and perturbation analysis underlying the schedule. Their quadratic theory does not by itself control nonlinear Hessian drift or aborted-trial costs. The retained dyadic factor is a refinement of their argument, not a claimed new standalone acceleration theorem.
- **Accelerated nonconvex methods.** Li and Lin, [*Restarted Nonconvex Accelerated Gradient Descent: No More Polylogarithmic Factor in the O(ε^(-7/4)) Complexity*, ICML 2022](https://proceedings.mlr.press/v162/li22o.html), and its [JMLR 2023 extension](https://jmlr.org/papers/volume24/22-0522/22-0522.pdf), Theorem 1 and Algorithm 1 ([arXiv:2201.11411v4](https://arxiv.org/abs/2201.11411v4)), obtain `O(Δ L^(1/2)ρ^(1/4)ε^(-7/4))` gradient calls without logarithmic factors. Their theorem returns norm at most `82δ`; setting `δ=ε/82` gives the same accuracy target. Its stated tuning has `η=1/(4L)` and `θ=4(δρη²)^(1/4)∈(0,1]`, so this comparison concerns the nontrivial small-accuracy regime and makes no uniform `ρ→0` claim. The theoretical algorithm uses gradients and displacement restarts, so gradient-only access is not an advantage of our result over this benchmark. It uses accelerated updates rather than positive scalar-step GD. The present positive-GD result remains `1/12` above that exponent, compared with `5/36` for the earlier `17/9` GD result. It closes 40% of that exponent gap; it does not match accelerated GD or establish a GD lower bound.
- **Large-step GD with line search.** Galli et al., [*Flatland: The Adventures of Gradient Descent with Large Step Sizes*, ICML 2026](https://proceedings.mlr.press/v306/galli26a.html), [arXiv:2606.06722v1](https://arxiv.org/abs/2606.06722v1), Theorem 2.9 and Appendix B.5, prove asymptotic gradient convergence for a nonmonotone equality line search under compact level sets. This is relevant large-step GD theory, but does not provide a competing finite oracle-complexity exponent under the present assumptions.
- **Hessian-aware GD.** [*First-ish Order Methods*, arXiv:2502.03701v3](https://arxiv.org/abs/2502.03701v3), Proposition 3.6 and Theorems 3.7/3.9, concern a global `ε^(-2)` bound and local convergence near nondegenerate minima, with Hessian information and function-value line search. Those guarantees do not imply this gradient-only global stationarity rate.
- **Chebyshev acceleration with Hessian variation.** [*Chebyshev-exact acceleration under Hessian variation, I: Sine-Jacobi method*, arXiv:2606.16671v2](https://arxiv.org/abs/2606.16671v2), Theorem 1.4 and Corollary 5.4, studies drift sensitivity and two-term momentum realizations around positive-definite reference models. Its time-ordered Hessian analysis is relevant prior work, but does not provide the present global nonconvex positive-GD guarantee. This is a preprint comparison, not a claim of conference acceptance.

In normalized variables the new bound is
`O(H^(4/3)(X a^(1/6)+√X+X^(15/17)a^(2/17)+1))`, with `H=8+log₂(2+X)`.
For `0<a≤1` and `X≥a^(-5/12)`, both extra nonconstant terms are at most `X a^(1/6)`. If additionally `X` is polynomial in `1/a`, the new leading bound divided by the old leading bound is `O(a^(1/18) log(1/a)^(1/3))`, tending to zero. Fixed positive `L,ρ,Δ` with `ε→0` is one such regime. The mixed term and the square-root term cannot be dropped outside that regime. No all-parameter domination is claimed.

At `ρ=0`, the proved budget is `O(H^(4/3)(√X+1))`. This is not a new superiority claim: a zero-Hessian-variation instance also satisfies arbitrarily small positive upper bounds on `ρ`, and retuning the old theorem can already recover approximately the square-root polynomial scale. At `Δ=0`, the initial point is stationary; the uniform budget remains valid. Constants are deliberately conservative, and no practical improvement at moderate accuracy is established.

## Scope of the contribution and remaining limitations

The contribution is a stronger worst-case guarantee for the independently important positive adaptive GD family under the standard nonlinear objective class. It improves a known GD bound through an execution-valid recovery mechanism and sharper stability/energy estimates. It does not improve unrestricted first-order complexity, remove parameter knowledge, establish optimality, or give a stochastic/noisy-gradient guarantee. Dependence on `Δ` in update tuning is a genuine adaptivity tradeoff. The nonlinear and negative-curvature controls, rather than quadratic calculations or the Lean formalization itself, are the mathematical content being claimed.

The literature assessment used the current November 2026 survey of ICML, ICLR, NeurIPS and recent arXiv work, then checked the primary versions and older results cited above. Absence from a search is not a proof of priority. The claim is relative to the strongest applicable guarantees identified and explicitly compared here; it does not rely on older repository review ratings. The existing `17/9` result is the decisive baseline even though it is a repository theorem rather than a conference-acceptance claim.

## Formal proof organization

The exact existing setup is reused, and the actual algorithm is linked to `execute` and proved to satisfy its positive-GD/output restrictions. New supporting modules are:

- [FractalChebyshevWeighted](../Proofs/FractalChebyshevWeighted.lean): weighted windows and periodic extensions.
- [GdSnapshotDynamics](../Proofs/GdSnapshotDynamics.lean) and [GdNegativeSpectrum](../Proofs/GdNegativeSpectrum.lean): actual gradient forcing and negative-spectrum transport.
- [RecoveryFractalExecution](../Proofs/RecoveryFractalExecution.lean) and [RecoveryFractalSchedule](../Proofs/RecoveryFractalSchedule.lean): state-machine execution, output, and schedule bounds.
- [RecoveryFractalLocal](../Proofs/RecoveryFractalLocal.lean) and [RecoveryFractalEnergy](../Proofs/RecoveryFractalEnergy.lean): localization and spectral energy estimates.
- [RecoveryFractalTuning](../Proofs/RecoveryFractalTuning.lean), [RecoveryFractalRecovery](../Proofs/RecoveryFractalRecovery.lean), and [RecoveryFractalCompleted](../Proofs/RecoveryFractalCompleted.lean): all tuning conditions and actual group descent.
- [RecoveryFractalConvergence](../Proofs/RecoveryFractalConvergence.lean) and [RecoveryFractalBudget](../Proofs/RecoveryFractalBudget.lean): global execution counting, fallback convergence, dyadic maximality, and the explicit budget.
