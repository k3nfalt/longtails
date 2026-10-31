# Hessian-noise-adaptive stochastic cubic acceleration

The result concerns convex minimization on a known compact convex set in arbitrary finite dimension. It removes knowledge of the Hessian oracle's error scale from an accelerated stochastic cubic method while retaining, up to logarithms, the three-term oracle complexity of the strongest tuned baseline. It does not improve that baseline's polynomial dependence when both noise scales are known.

## Formal statement and oracle model

The [setup](../Setups/HessianAdaptiveStochasticConvex.lean) specifies a globally convex differentiable objective with differentiable gradient, a minimizer `xstar` in a known compact convex set `C`, and a Hessian that is Lipschitz on `C` with known positive upper bound `ρ`. The known diameter upper bound `D` is positive; `x0` belongs to `C`. Boundary minimizers are allowed. There is no strong-convexity, separability, quadratic-objective, or fixed-dimension restriction.

Gradient samples are unbiased and have central second moment at most `σg²`. Hessian samples are self-adjoint positive semidefinite and have operator-norm second moment about the true Hessian at most `σh²`; their bias need not vanish. Both oracles are jointly measurable. The sampling law is abstract and satisfies the repository's IID structure. No product sampling law is imposed in the specification; finite-prefix product representations are derived from independence in the proofs.

The algorithm knows `C`, `x0`, `D`, `ρ`, and the valid gradient-noise upper bound `σg`. It receives neither `σh` nor the requested accuracy `ε`, and makes no objective-value queries. A gradient call and a full-Hessian call each cost one oracle call. This is not a Hessian-vector-product complexity result. Exact constrained cubic and quadratic subproblem solutions are local computations in this oracle model; their arithmetic cost is not bounded.

The [algorithm](../Algorithms/HessianAdaptiveCubic.lean) uses two independent gradient samples and one independent Hessian sample per round. Its returned point is its recursively weighted average of primal trial points, not a randomly selected iterate or the last primal subproblem solution. The [main theorem](HessianAdaptiveCubic.lean) connects that output to `execute` and proves expected objective accuracy relative to `xstar`.

For `T ≥ 1`, the supporting proofs yield

\[
\mathbb E[f(w_T)-f(x_\star)]
\le 2\cdot10^6\left(
\frac{\sigma_gD}{\sqrt T}+
\frac{\sigma_hD^2}{T^2}+
\frac{\rho D^3}{T^{7/2}}
\right)\left[1+\log\left((1+\sigma_h/(\rho D))T\right)\right].
\]

The public theorem uses the single sufficient budget `3⌈10¹⁸ Q J²⌉` with

\[
Q=1+(\sigma_gD/\varepsilon)^2+
\sqrt{\sigma_hD^2/\varepsilon}+
(\rho D^3/\varepsilon)^{2/7},\qquad
J=1+\log((1+\sigma_h/(\rho D))Q).
\]

The Lean budget expands these expressions explicitly. All three raw calls per round are counted. The constants are conservative proof constants, not practical tuning recommendations. This is an analytic complexity guarantee: the sufficient horizon depends on the hidden Hessian error bound. The algorithm is horizon-free, but the result supplies no observable certificate or stopping rule for unknown `σh`.

## Closest results and precise contribution

* [Agafonov et al., *Matching the Lower Bounds: Stochastic Contracting Cubic Newton and Its Optimal Acceleration*, arXiv:2610.11693v2](https://arxiv.org/html/2610.11693v2), October 13, 2026, Assumptions 3.1 and 3.3–3.5, Theorem 5.1, and Appendix C, is the strongest tuned baseline checked. It obtains the same three polynomial terms without our logarithmic overhead, using both gradient and Hessian noise levels in its tuning. Its bounded-domain, biased-PSD-Hessian model is the principal comparison. The source permits almost-sure PSD Hessians and a shared model-gradient/Hessian sample; our formal setup requires pointwise PSD Hessians and our execution uses separate samples, charging all three calls. Pointwise PSD holds automatically for Hessians of sampled convex component functions, but is a formally stronger formulation than the source’s almost-sure condition. This is an unreviewed preprint, not an accepted conference paper.
* [*Extra-Newton: A First Approach to Noise-Adaptive Accelerated Second-Order Methods*, NeurIPS 2022, arXiv:2211.01832v2](https://arxiv.org/html/2211.01832v2), Theorem 3.2, provides broader noise/curvature adaptivity with terms of orders `σg D / √T`, `σh D² / T^(3/2)`, and `max{ρ D³, √β₀ D} / T³`, including its initialization parameter `β₀` (with its scale parameter `γ = D`). Its Hessian oracle is unbiased; ours allows bias. Our result requires known `ρ` and `σg` but improves the Hessian and deterministic exponents to `2` and `7/2`, up to logarithms. It is not a universal improvement over that method's adaptivity.
* [Agafonov et al., *Optimal Parameter-Free Second-order Acceleration with Inexact Hessians under Generalized Smoothness*, arXiv:2609.32977v1](https://arxiv.org/html/2609.32977v1), September 26, 2026, Theorem 4.1, already provides adaptive optimal-order second-order guarantees with exact gradients on an unconstrained domain and uniformly bounded deterministic Hessian errors. It does not directly cover our entire constrained stochastic-RMS zero-gradient-noise endpoint; nevertheless, that endpoint alone is not the novelty relied upon here. The substantive extension is the finite-variance stochastic-gradient regime with unknown Hessian error. Naively replacing every exact gradient in such a method by a sufficiently accurate batch incurs additional oracle cost and does not recover the three-term bound above.
* The stochastic accelerated HPE machinery in [Carmon et al., *Optimal and Adaptive Monteiro–Svaiter Acceleration*, NeurIPS 2022, supplementary material](https://openreview.net/attachment?id=n3lr7GdcbyD&name=supplementary_material) Definition 4 and Theorem 6, requires an unbiased estimator of the exact proximal gradient with a relative-variance guarantee and an almost-sure movement condition. A stochastic approximate proximal point followed by a fresh unbiased objective gradient does not supply those conditions. That composition does not establish this result under the stated oracle model.

The standard batching check does not preserve the target accounting: obtaining gradient RMS error `ε/D` costs order `1 + σg²D²/ε²` samples per location. Repeating that at order `(ρD³/ε)^(2/7)` outer locations multiplies the stochastic cost by the outer iteration count, whereas our bound adds the stochastic and deterministic terms. Moreover, finite batching does not literally satisfy an exact-gradient theorem. This is a calculation for that reduction, not a lower bound on all possible reductions. Parallel noise-scale guesses also do not automatically yield a verified output: this model supplies no objective values for the usual value-based selection step.

Thus the contribution is a Hessian-scale adaptivity improvement at essentially the tuned stochastic cubic complexity, not a new polynomial problem-class complexity lower bound or an improvement in every parameter regime. The improvement over the adaptive baseline is meaningful when its Hessian or deterministic term is limiting; when the gradient-noise term dominates, no polynomial improvement is claimed. Logarithms and the large explicit constants matter for finite-parameter comparisons. No optimality claim is made for the logarithmic overhead or the information needed for automatic stopping.

For an explicit comparison, write `G = (σg D/ε)²`, `H = (σh D²/ε)^(1/2)`, and `R = (ρ D³/ε)^(2/7)`. Ignoring universal constants, logarithms, and Extra-Newton’s separately displayed initialization term, when `H ≥ max{1,G,R}`, our sufficient budget is of order `H`, while Extra-Newton’s displayed polynomial budget is of order `H^(4/3)`. When `R ≥ max{1,G,H}`, our sufficient budget is of order `R`, whereas Extra-Newton’s published bound contains `R^(7/6)` and its Hessian term may be larger. These are comparisons of published sufficient upper bounds, not lower bounds on those algorithms or claims of superiority for every finite choice of constants.

## New proof mechanism

A residual-based scale responds jointly to curvature and both oracle errors through the model and fresh-gradient discrepancy; it does not isolate the Hessian error. A known-gradient-noise floor grows cubically with the round index. The inverse adaptive normalizer is Lipschitz in the fresh gradient. Centering the gradient before applying that Lipschitz estimate bounds the normalization-induced bias by a harmonic term. This is necessary: the fresh noise is not a martingale difference after division by the random next scale, and assuming that cancellation would be false.

A normalized energy inequality controls cumulative movement, which in turn controls both the adaptive scale's second moment and the inverse acceleration weight's second moment. A logarithmic self-bound closes the apparent circularity. The raw, unnormalized gradient-noise sum remains a martingale and is handled separately. Cauchy–Schwarz then combines energy and inverse weights without assuming they are independent. This resolves the stochastic dependence obstruction that prevents a direct reuse of the tuned or exact-gradient analyses.

## Scope, examples, and limitations

A nonseparable nonlinear family is a convex quadratic plus a nonnegatively weighted sum of `log cosh(aᵢᵀx)` terms with nonorthogonal feature vectors, restricted to a compact convex set. Its Hessian is positive semidefinite and Lipschitz with a bound determined by the feature norms and coefficients. Additive mean-zero gradient noise with finite second moment supplies the gradient model. Randomly sampled positive semidefinite feature-Hessian terms, optionally with a fixed positive semidefinite bias, supply Hessian estimates with finite operator-norm second moment. Interacting feature directions remain in the theorem; scalar and quadratic calculations are not its scope.

The bound has no explicit dimension factor when the stated vector and operator-norm moments are dimension-independent. Those moment parameters and the cost of a full Hessian can themselves depend on dimension. Samplewise PSD Hessians, compactness, known gradient-noise and curvature bounds, exact local subproblem solves, and IID sampling are substantive restrictions. The result does not cover indefinite Hessian samples, Markov sampling, unknown gradient-noise scale, or a high-probability accuracy criterion.

Literature screening began on October 26, 2026 (UTC), independently by Researcher and Reviewer. It covered the then-public 2025/2026 editions of ICML, ICLR, and NeurIPS, approximately the preceding two years of arXiv submissions and revisions, and older foundational comparisons. Conference status was checked separately from arXiv availability. Targeted searches are not an exhaustive proof of absence; the novelty claim rests on the explicit comparisons and reduction checks above.
