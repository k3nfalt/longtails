# Constant-step normalized SAM: improved complexity and a nonlinear residual obstruction

The [main theorem](NormalizedSamStronglyConvex.lean) proves a last-iterate guarantee for normalized SAM on the standard smooth strongly convex class. A supporting lower bound identifies the sharp parameter order of its worst-case constant-step residual in a small-step regime. These are method-specific results, not an improvement over the best oracle complexity of the problem class.

## Setup, execution, and guarantee

The [specification](../Setups/NormalizedSamStronglyConvex.lean) assumes a differentiable objective on a complete real inner-product space, globally L-Lipschitz gradient, μ-strong convexity, an attained minimizer x⋆, and initial gap at most Δ. Here 0<μ≤L, ρ>0, Δ≥0, and ε>0. It includes arbitrary-dimensional nonlinear finite-dimensional objectives. There is no bounded-gradient, bounded-domain, Hessian-Lipschitz, interpolation, flat-minimum, or stochastic-noise assumption.

The oracle returns the exact gradient. The [algorithm](../Algorithms/NormalizedSam.lean) uses

\[
y_k=x_k+\rho\frac{\nabla f(x_k)}{\|\nabla f(x_k)\|},\qquad
x_{k+1}=x_k-\eta\nabla f(y_k).
\]

At zero gradient the perturbation is defined as zero. The radius and step are constant throughout the run. The setup's `allowedAlgorithm` enforces these updates and the last-state output, while leaving the positive step size free. The algorithm knows L, μ, ρ, ε, Δ, and x₀; it does not know x⋆, f⋆, or the constructed lower-bound objective. The [execution proof](../Proofs/NormalizedSamRun.lean) identifies the output after exactly 2K gradient calls with the Kth SAM iterate, including when both queries coincide. There are no function-value queries or uncounted initialization calls.

For every 0<η≤1/(2L), [SamStrongConvex.output_gap](../Proofs/SamStrongConvex.lean) proves

\[
f(x_T)-f(x^\star)\le
\max\left\{(1-\mu\eta)^T\bigl(f(x_0)-f(x^\star)\bigr),
\frac{4\eta^2L^4\rho^2}{\mu}\right\}.
\]

The public convergence theorem chooses

\[
\eta=\frac1{2L+2L^2\rho/\sqrt{\mu\varepsilon}},\qquad
K=\left\lceil\left(\frac{2L}{\mu}+\frac{2L^2\rho}{\mu\sqrt{\mu\varepsilon}}\right)
\log(1+\Delta/\varepsilon)\right\rceil.
\]

It returns x_K with objective gap at most ε using the explicit budget 2K. The [tuning proof](../Proofs/SamTuning.lean) handles Δ=0, where K=0. Writing κ=L/μ, the cost is

\[
O\!\left(1+\left[\kappa+\kappa^{3/2}\rho\sqrt{L/\varepsilon}\right]
\log(1+\Delta/\varepsilon)\right).
\]

The formal accuracy statement is almost sure because the repository permits arbitrary oracle seed spaces; exact answers make execution deterministic for every seed.

## Matching nonlinear residual and its limitations

[SamCycle.exists_residual](../Proofs/SamCycleScaling.lean) proves that, for every L>0, ρ>0, 0<μ≤L/100 and 0<η≤μ/(10L²), there exists a global L-smooth μ-strongly convex objective and two states x₀,x₁ such that SAM alternates between them and

\[
f(x_T)-f(0)=\frac{\eta^2L^4\rho^2}{5000\mu}\quad\text{for every }T\ge0.
\]

For the **same objective and cycle**, every affine combination ax₀+bx₁ with a+b=1 satisfies

\[
f(ax_0+bx_1)-f(0)\ge\frac{9\eta^2L^4\rho^2}{80000\mu}.
\]

Thus taking the best iterate or averaging cycle iterates does not eliminate the obstruction. The Lean statement takes an isometric embedding of the Euclidean plane into the ambient space; such an embedding exists in every Euclidean dimension d≥2. Constants do not depend on dimension. The upper theorem has no dimension restriction.

The lower objective depends on η and initialization is exactly on the cycle. No attraction basin, random-initialization probability, or typical training behavior is proved. Its initial gap equals the displayed residual, so it belongs to a setup with prescribed Δ only when that residual is at most Δ. The lower range does not cover every stable step. For the displayed tuned step, ε≤μρ²/25 is a sufficient condition for the small-step restriction. This is sharp residual scaling up to universal constants in that regime, **not** a matching lower bound on optimized finite-horizon oracle complexity. Arbitrary nonlinear output corrections are not covered.

## Mathematical contribution and mechanism

The upper proof uses the coupling between a gradient and its own normalized ascent perturbation. If g=∇f(x) and e=∇f(x+ρg/‖g‖)−g, cocoercivity gives

\[
\|e\|^2\le\frac{L\rho}{\|g\|}\langle g,e\rangle.
\]

[SamCocoercive](../Proofs/SamCocoercive.lean) uses this relation to prove descent whenever ‖g‖≥ηL²ρ. Below that threshold the next gradient norm is at most (5/2)ηL²ρ. Strong convexity converts this into a residual bound, while a maximum-type induction preserves contraction after any transition between the two regimes. This is what yields a last-iterate statement.

The lower construction exhibits coupled nonlinear geometry hidden by a scalar quadratic diagnostic. Normalize L=ρ=1, put m=μ and t=η/m, and prescribe

\[
x_\pm=(3t/200,\ \pm2mt/25),\quad
g_\pm=(3mt/100,\ \pm mt/25),\quad
y_\pm=x_\pm+(3/5,\ \pm4/5),\quad
h_\pm=(0,\ \pm4/25).
\]

Set f(0)=0, ∇f(0)=0, f(x±)=mt²/5000, and f(y±)=1/20. The [exact certificate](../Proofs/SamCycleInterpolation.lean) verifies all ordered smooth strongly convex interpolation inequalities for 0<m≤1/100 and 0<t≤1/10. The gradients normalize exactly to (3/5,±4/5), and the descent updates exchange x±. Their shared first coordinate produces the averaging obstruction.

These data cannot come from a separable convex function: the first partial derivative decreases from a positive value at x± to zero at y± despite increasing the first coordinate. They also cannot come from a single quadratic: differences between the two x states and between the two y states require incompatible vertical curvature. This is a genuine nonlinear family with interacting coordinates, not a quadratic example presented as a general result.

Global realization is proved in [QuadraticEnvelope](../Proofs/QuadraticEnvelope.lean) and [SmoothInterpolation](../Proofs/SmoothInterpolation.lean), following the constructive interpolation principle of [Taylor–Hendrickx–Glineur, Mathematical Programming 161 (2017), Theorem 4 and Remark 2, arXiv v6](https://arxiv.org/pdf/1502.05666v6). The proof minimizes quadratic costs over the compact convex hull of transformed data, derives differentiability and Lipschitz gradients, and restores the strong-convexity quadratic. The realization theorem is established supporting mathematics; the new contribution is the certificate and its SAM consequence, paired with the improved upper bound. Only C¹,¹ regularity is claimed.

## Closest results and comparison

[Si–Yun, NeurIPS 2023, arXiv:2306.09850v3, Theorems 3.1–3.2 and Appendix B.2–B.3](https://arxiv.org/html/2306.09850v3) study the same normalized, fixed-radius deterministic update under the same smooth strongly convex assumptions. Their best-iterate upper bound is, up to logarithms,

\[
e^{-\mu T/(2L)}\Delta+\frac{L^6\rho^2}{\mu^5T^2}.
\]

Their horizon lower bound has scale L³ρ²/(μ²T²), and they explicitly leave the condition-number gap and more sophisticated lower constructions unresolved. Our sufficient radius-dependent oracle term improves from κ^(5/2)ρ√(L/ε) to κ^(3/2)ρ√(L/ε), up to logarithms, and applies to the last iterate. The factor-κ improvement concerns the radius-dominated regime; no universal factor-κ improvement is asserted when the transient term dominates. Their scalar quadratic cycle has fixed-step scale η²L³ρ²; the new nonlinear construction has an additional factor κ. The horizon lower bound from their paper and our fixed-step lower bound have different quantifiers and are not interchangeable. [Official acceptance record](https://proceedings.neurips.cc/paper_files/paper/2023/hash/5305b7891e1098dd9773d35cd9333180-Abstract-Conference.html).

Standard reductions do not give the paired result. Treating e merely as bounded error, ‖e‖≤Lρ, yields a residual of order L²ρ²/μ that does not vanish with η. Deterministic batching adds calls without changing the gradient. Clipping or shrinking the perturbation changes the fixed-radius method. Regularizing the objective changes the queried gradients. The scalar quadratic calculation misses the extra condition-number dependence and the persistent mean offset.

Ordinary GD has O(κ log(Δ/ε)) complexity in this class, and accelerated gradient methods have O(√κ log(Δ/ε)) complexity, with conventional treatment of small initial gaps. They remain better problem-class algorithms. The reason to study this update is the specific unresolved normalized-SAM condition-number question and the nonlinear obstruction, not popularity alone or an artificial restriction on a new problem setup. No generalization or robust-objective optimization guarantee is claimed.

## Literature coverage and unresolved comparisons

The Researcher and independent Reviewer surveyed the two latest publicly available editions as of 15 October 2026 UTC: ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2024/2025, plus roughly two years of arXiv submissions/revisions and older citations. This was a targeted search, not an exhaustive guarantee. Particularly relevant scope checks included:

- [Khanh et al., NeurIPS 2024, arXiv v3, Theorem 3.2](https://arxiv.org/html/2401.08060v3): convex asymptotic convergence with a bounded nonempty level set and diminishing steps; not the present constant-step residual characterization.
- [Oikonomou–Loizou, ICLR 2025, arXiv v1](https://arxiv.org/html/2503.02225v1): stochastic expected-residual analyses. [Official proceedings](https://proceedings.iclr.cc/paper_files/paper/2025/hash/4a46787131e2f1d8cf429362f6e2a6ec-Abstract-Conference.html).
- [Oikonomou–Loizou, ICML 2026, arXiv v1](https://arxiv.org/html/2606.01827v1): formal Polyak guarantees for unnormalized SAM with different information and perturbation restrictions. [Official proceedings](https://proceedings.mlr.press/v306/oikonomou26b.html).
- [Schliserman et al., ICML 2026, arXiv v2](https://arxiv.org/html/2511.03548v2): a flat-ball minimizer assumption changes the class. [Official proceedings](https://proceedings.mlr.press/v306/schliserman26a.html).
- [Park et al., ICML 2026, arXiv v2](https://arxiv.org/html/2509.21818v2): nonconvex spurious fixed points and local dynamics. [Official proceedings](https://proceedings.mlr.press/v306/park26e.html).
- [Harada–Iiduka, arXiv:2409.09984v3, revised 12 October 2026](https://arxiv.org/html/2409.09984v3): batching and schedules for GSAM. The arXiv claim of ACML acceptance was not independently verified.
- [Adly–Le, arXiv:2608.06692v1](https://arxiv.org/html/2608.06692v1): stationarity floors and clipping mechanisms; treated as a preprint.

Additional checks covered XSAM, momentum variants, the JMLR renormalized method, local stability papers, and an author-uploaded July 2026 local-dynamics manuscript whose venue status was unverified. Some early ICML virtual-page requests were blocked; official proceedings supplied alternatives. A noncentral paywalled momentum-SAM article was accessible only at abstract level. No verified overlapping nonlinear residual theorem was found. These access limits and the possibility of missed work remain limitations of the novelty assessment, not evidence of novelty themselves.
