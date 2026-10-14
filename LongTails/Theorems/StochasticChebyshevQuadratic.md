# Stochastic acceleration using only stepsizes and batches on convex quadratics

The [Lean theorem](StochasticChebyshevQuadratic.lean) supplies the explicit [batched Chebyshev algorithm](../Algorithms/BatchedChebyshev.lean) for the [stochastic convex quadratic setup](../Setups/StochasticConvexQuadratic.lean). Its contribution concerns this restricted algorithm: predetermined nonnegative scalar SGD steps, deterministic fresh batches, and the last iterate. The setup enforces this algorithm family through `allowedAlgorithm`, and the theorem proves membership as part of `Convergence spec budget`. The unrestricted existence of an algorithm with this oracle complexity is already known.

## Setup and motivation

The objective is any attained convex quadratic on a finite-dimensional real Hilbert space, with gradient Lipschitz constant at most `L > 0`. A minimizer `xstar` satisfies `‖x0 - xstar‖ ≤ R`. The algorithm knows `L, R, σ, ε, x0`, but does not know the Hessian, its spectrum or eigenvectors, or the minimizer. One call returns `g(x, ξ)`, where fresh IID samples have an arbitrary probability law. The oracle is jointly measurable, vector-unbiased, and satisfies

\[
\mathbb E g(x,\xi)=\nabla f(x),\qquad
\mathbb E\|g(x,\xi)-\nabla f(x)\|^2\leq\sigma^2
\]

at every point, with the corresponding integrability. Neither finite support nor bounded realized errors are required. The noise distribution may depend on the query point; covariance need not commute with the Hessian. The setup reuses the existing stochastic smooth-convex objective and oracle assumptions and adds finite dimensionality and a hidden positive-semidefinite quadratic factorization. It imposes no positive lower spectral bound, samplewise smoothness, interpolation, or trajectory bound.

The setup requires the algorithm to equal its `BatchedSGD.algorithm` constructor for a nonnegative step schedule `η` and positive integer batch schedule. These choices depend only on public inputs, not on observed replies. The constructor starts at `x0`, queries each batch at the current point, applies the scalar gradient step using the batch average, and returns the last iterate. The Chebyshev witness sets its step size to zero after `T` updates; any remaining oracle calls still count toward the budget.

These are standard noisy-quadratic assumptions. For example, let `H` be positive semidefinite with norm at most `L`, and let IID random right-hand sides `bξ` satisfy `E bξ = b ∈ range H` and `E‖bξ-b‖² ≤ σ²`. Then `f(x)=⟨x,Hx⟩/2-⟨b,x⟩` and `g(x,ξ)=Hx-bξ` satisfy the oracle contract globally. This models noisy linear systems and fixed-design quadratic inverse problems. The restriction is material: generic random-design least-squares gradients have multiplicative noise and usually do not satisfy a global absolute variance bound. The uniform-variance quadratic model also appears in [Woodworth et al., ICML 2020, Sections 2–3](https://proceedings.mlr.press/v119/woodworth20a/woodworth20a.pdf); [Zhang et al., NeurIPS 2019, Section 3.1](https://arxiv.org/html/1907.04164) analyzes a more specialized additive-noise model.

## Algorithm and guarantee

If `ε ≥ LR²/2`, the output is `x0`. Otherwise set

\[
T=\left\lceil\sqrt{LR^2/\varepsilon}\right\rceil,
\quad M=\left\lceil65536\sigma^2R^2/\varepsilon^2\right\rceil,
\quad m=2T+1.
\]

For `i=1,…,T`, define

\[
r_i=\sin^2(i\pi/m),\quad
D_i=\frac{4m}{i\sqrt i}+17,\quad
b_i=1+\left\lceil\frac{MD_i}{128T}\right\rceil,
\quad \eta_i=\frac1{Lr_i}.
\]

At the current point, average `b_i` fresh replies and make the single update `x_i=x_{i-1}-η_i ḡ_i`. Return `x_T`. There is no momentum, iterate averaging, projection, restart, sample reuse, objective oracle, or spectral information in the update. Steps decrease from potentially very large values.

The proved bound before tuning is

\[
\mathbb E[f(x_T)-f(x_\star)]
\leq \frac{LR^2}{2(2T+1)^2}
 +\frac{\sigma^2}{2L}\sum_{i=1}^T\frac{D_i^2}{b_i}.
\]

The chosen batches satisfy `∑ b_i ≤ 2T+M`; if `M>0`, the variance sum is at most `16384 T²/M`. The tuning gives expected objective gap at most `ε`, with the public budget

\[
\boxed{3+\left\lceil4\sqrt{LR^2/\varepsilon}
       +65536\sigma^2R^2/\varepsilon^2\right\rceil.}
\]

Thus the oracle complexity is `O(1+√(LR²/ε)+σ²R²/ε²)`, without logarithmic factors. Zero noise gives single-sample batches. The code handles `R=0` and coarse accuracy explicitly. The repository execution interface runs for the entire public budget: after the scheduled updates finish, the point is frozen and subsequent replies are discarded. Those calls are included in the displayed budget, even in the coarse case.

## What is new

The deterministic residual and its accelerated quadratic bias are classical. Noise-moment recursions, conditional centering, and allocation of samples according to noise weights are also established tools. The substantive step is a uniform, sharp bound on the total final-energy amplification of errors under the *descending* weighted-Chebyshev factor order.

For normalized curvature `z∈[0,1]`, let

\[
P_T(z)=\prod_{j=1}^T(1-z/r_j),\qquad
S_i(z)=\prod_{j=i+1}^T(1-z/r_j),\qquad
a_i=\sup_{0\leq z\leq1}\frac{\sqrt z}{r_i}|S_i(z)|.
\]

The residual identity gives `|P_T(z)|≤1` and `zP_T(z)²≤1/(2T+1)²`. The new quantitative estimate is

\[
a_i\leq D_i,\qquad \sum_{i=1}^T D_i\leq128T.
\]

A basic sorted-factor argument already gives `|S_i(z)|≤1` and `a_i≤√(2/r_i)`. Its sum is only `O(T log T)`, yielding a derived batching baseline with a squared logarithm in the statistical cost. Removing that logarithm requires more than this contraction argument. For early indices the proof splits the spectrum into three ranges: small curvature is damped by nearby later roots; intermediate curvature is damped by a separated block; large curvature is controlled by the expanding prefix and the bounded full residual. These give `O(T/i^(3/2))` gain. The remaining indices have uniformly bounded gain. Summing these estimates gives `O(T)`.

The vector proof lifts these scalar inequalities through an orthonormal eigenbasis used only in the analysis. A backward energy argument conditions on each fresh batch, proves integrability, and cancels its centered noise before continuing. This is valid for state-dependent noise; it does not discard cross terms involving future random gradients without conditioning.

## Closest comparisons and improvement regimes

| Comparison | Scope and criterion | Difference from this result |
| --- | --- | --- |
| [Lebedev–Finogenov 1973, Sections 4–6, Theorems 1–3](https://www.mathnet.ru/eng/zvmmf6595) | Chebyshev factor ordering with a positive lower spectral bound; deterministic rounding-error and intermediate-iterate stability | Classical ordering/error-propagation lineage. It does not give the stated finite-variance, zero-lower-curvature sample complexity. |
| [Agarwal–Goel–Zhang, ICML 2021, Theorems 8–10, Corollary 11, Appendix G.3](https://arxiv.org/abs/2103.01338) | Fractal stepsize order; robustness of intermediate iterates to adversarial perturbations | Our order sacrifices intermediate stability and proves a sharper final stochastic-energy bound. It does not dominate their robustness guarantee. |
| [Liu–Zhou, Theorem 3.4 and Appendix C.1](https://arxiv.org/html/2312.08531v4) | General smooth convex last-iterate SGD; `O(LR²/N+σR/√N)` | On the quadratic subclass, the new scheduled method attains the accelerated bias–variance frontier `O(LR²/N²+σR/√N)` up to universal constants. This is a narrower objective class, not an improvement for all smooth convex functions. |
| [Bai–Zeng–Zhou, Theorems 3.2 and 3.4](https://arxiv.org/html/2511.21917), and [Bai–Zhou, 2026](https://arxiv.org/abs/2608.15035) | Two-step stochastic hedging under strong convexity; squared-distance guarantees | They establish finite-step benefits, not this growing-horizon last-objective frontier without a lower curvature bound. |
| [Woodworth et al., ICML 2020, Section 3 and Corollary 1](https://proceedings.mlr.press/v119/woodworth20a/woodworth20a.pdf) | Accelerated stochastic quadratic optimization with more general linear updates | The same unrestricted oracle frontier is known. The contribution here is attaining it using scalar gradient steps and deterministic batches alone. |

The improvement over the elementary descending-factor batching baseline is removal of its `log² T` statistical penalty; this can save that factor when its statistical term dominates its update cost. Relative to the standard last-iterate SGD budget `O(LR²/ε+σ²R²/ε²)`, the new budget is asymptotically smaller when `ε/(LR²) → 0` and `σ²/(Lε) → 0`. For `R>0`, the accelerated deterministic term controls the new budget when `σ² = O(√L ε^(3/2)/R)`. Equivalently, in the call-budget parametrization, the full `N^(-2)` bias is visible when `σ = O(LR/N^(3/2))`; the improvement over the ordinary `N^(-1)` bias persists more broadly when `σ=o(LR/√N)`. These are restricted-regime comparisons, and they apply to the quadratic subclass. No statistical improvement over unrestricted accelerated methods or ordinary SGD's `σR/√N` scale is claimed.

Additional checked results do not supply a family-preserving reduction: [Van Scoy–Lessard, Sections 2–3](https://arxiv.org/html/2109.05059) concerns fixed-parameter two-state dynamics and asymptotic noise sensitivity; [Kulunchakov–Mairal, Algorithms 1–2](https://arxiv.org/html/1906.01164) uses regularized auxiliary problems and extrapolation; [Pasechnyuk-Vilensky–Takáč, Theorems 2.1–4.2 and Section 6](https://arxiv.org/html/2606.16671) studies two-term realizations, positive lower curvature, and Hessian drift. Their guarantees are not relabeled as plain-SGD results.

## Optimality scope and limitations

Up to universal constants, the displayed complexity is optimal within the predetermined scalar-step, deterministic-batch, last-iterate family for `0<ε≤cLR²`, with a sufficiently small universal `c`. This is a classical/elementary comparison, not another novel result or a Lean-certified lower bound here. For the deterministic term, scalar quadratics `fλ(x)=λ(x-R)²/2` force a degree-`T` residual `P(0)=1`. Apply classical Bernstein polynomial extremality to `tP(Lt²)`, whose derivative at zero is one: some `λ∈[0,L]` has gap at least `LR²/[2(2T+1)²]`. Since `T≤N`, this gives the required deterministic call lower bound. See [Queffélec–Zarouf, Theorems 1.1–1.2](https://arxiv.org/html/1903.10801) for the classical inequality and its proof.

For the stochastic term, take scalar objectives `f±(x)=a(x∓R)²/2` and replies `ax∓aR+Z`, with fresh `Z∼N(0,σ²)` and `a=min(L,σ/(4R√N))`. Even granting `a` and permitting adaptive unbounded queries leaves only `N` Gaussian mean observations after subtracting `ax`. Their KL divergence is at most `1/8`; two-point testing gives worst-case gap at least `(3/64)min(LR²,σR/√N)`. These separate hard instances imply the additive call lower bound in the fine-accuracy regime. Coarse accuracy and `R=0` allow the initial point, so an untruncated positive lower bound there would be false.

Intermediate iterates can grow exponentially with the horizon even for a scalar noiseless quadratic. The result is therefore an exact-arithmetic oracle theorem, not a finite-precision stability or practical training-speed claim. The global variance assumption must hold at those queries. The theorem does not extend to general nonlinear objectives, multiplicative gradient noise, unknown tuning parameters, or an anytime schedule.

Two literature comparisons remain limited by access: the full text of the anonymous [silver zeroth-order submission](https://openreview.net/forum?id=P8EhH6ypA5) was inaccessible, and an unpublished Takáč–Takáč manuscript cited by the 2026 Hessian-variation paper was not publicly located. Their accessible descriptions concern different or deterministic guarantees, but their full contents were not independently checked. Absence of a search match is not evidence by itself that a result is new.

## Formalization map

- [Setup, permitted GD constructor, and algorithm restriction](../Setups/StochasticConvexQuadratic.lean), and [Chebyshev schedules, tuned witness, run and call definitions](../Algorithms/BatchedChebyshev.lean).
- [Residual identities](../Proofs/ChebyshevResidual.lean), [root bounds](../Proofs/ChebyshevRoots.lean), and [sharp scalar noise gains](../Proofs/ChebyshevNoise.lean).
- [Spectral lifting](../Proofs/ChebyshevEnergy.lean), [stochastic batch/iteration proof](../Proofs/ChebyshevStochastic.lean), and [expected objective guarantee](../Proofs/ChebyshevConvergence.lean).
- [Exact execution and call accounting](../Proofs/ChebyshevExecution.lean), [batch allocation](../Proofs/ChebyshevBatching.lean), and [explicit tuning algebra](../Proofs/ChebyshevAccuracy.lean).

The public theorem uses the framework's `Convergence spec budget` interface, which checks both accuracy and `spec.allowedAlgorithm` for the same algorithm witness on valid parameters. Its witness is `BatchedChebyshev.tuned`; the lemma `BatchedChebyshev.tuned_allowed` proves that it belongs to the setup's permitted GD family. The execution and expected-gap lemmas explicitly identify its last iterate. Thus the public theorem statement enforces the algorithm restriction. Other setups retain the default `allowedAlgorithm := fun _ _ => True`.
