# Nearly tight complexity with spatially Hölder gradient noise

The [upper theorem](HolderNoiseMinimaxUpper.lean) and [lower theorem](HolderNoiseMinimaxLowerBound.lean) characterize a fractional-regularity refinement of smooth stochastic nonconvex optimization, up to a squared logarithm and universal constants. The new claim is the complete fractional-noise complexity law, including the rough regime below one-half, not a new variance-reduction estimator or a new lower-bound technique.

## Problem and oracle

The [setup](../Setups/HolderNoiseNonconvex.lean), `spec`, assumes an everywhere differentiable, globally L-smooth objective on a real separable Hilbert space, with `f(x0) - f(x) ≤ Δ` for every x. A jointly measurable oracle g is unbiased, has variance at most σ², and its centered noise e(x,ξ) = g(x,ξ) − ∇f(x) satisfies

\[
\mathbb E\|e(x,\xi)-e(y,\xi)\|^2\le M\|x-y\|^{2\nu},\qquad 0<\nu\le1.
\]

Each call returns two gradients at algorithm-chosen points using one fresh common sample. Samples are IID under an abstract probability law; all necessary integrability conditions are explicit. A pair costs one call in the theorem and at most two raw stochastic-gradient evaluations. The algorithm cannot revisit a sample after the call or access function values, Hessians, the distribution, or the true gradients. Parameters L, M, ν, σ, Δ, ε and x0 are public. There is no restriction on admissible algorithms.

Success means a measurable output with integrable gradient norm and **E‖∇f(output)‖ ≤ ε**. This is an expected-norm result, not fixed-probability success. The theorem makes no high-confidence or parameter-adaptivity claim.

## Rate and matching range

Write

\[
D=L\Delta/\varepsilon^2,\quad A=\sigma^2/\varepsilon^2,\quad
S=L\Delta\sigma^2/\varepsilon^4,
\]
\[
B_-={\Delta M\over\varepsilon^3}(L/\varepsilon)^{1-2\nu},\qquad
B_+={\Delta\over\varepsilon^3}M^{1/(2\nu)}\sigma^{2-1/\nu},
\quad H=1+\log_2(2+16D).
\]

The exact public budget is

\[
\left\lceil\min\{600(1+D+A+S),\;3200H^2(1+D+A+\max\{B_-,B_+\})\}\right\rceil.
\]

At σ=0, the first branch applies; expressions with zero bases use Lean's real-power convention. No singular expression is needed to interpret the algorithm. The [companion lower bound](HolderNoiseMinimaxLowerBound.md), using the [finite-dimensional lower setup](../Setups/HolderNoiseNonconvexLower.lean), proves failure at every budget up to

\[
\left\lfloor 2^{-80}[D+A+\min\{S,\max\{B_-,B_+\}\}]\right\rfloor
\]

when D≥64 and the dimension is at least `ceil(2^30 (1+D)^3 (1+A))`. Thus the pair is matching up to H² in this common regime. Constants and the polynomial dimension bound are not optimized. This does not assert dimension-optimality or matching complexity in the near-trivial accuracy regime D<64.

For fixed positive L, M, σ, Δ and ε tending to zero, the fractional term is ε^{-(4−2ν)} for 0<ν<1/2 and ε^{-3} for 1/2≤ν≤1, before the SGD cap and base terms are applied. A genuine oracle improvement over batching requires the fractional term to be smaller than S by more than the displayed logarithmic overhead when it dominates the base terms. The exact minimum retains the log-free batching guarantee in other regimes. At ν=1, stronger existing analyses remove the logarithmic overhead; this theorem does not improve that endpoint.

## Algorithm and proof mechanism

The [algorithm](../Algorithms/HolderNoiseVarianceReduction.lean), `outputAlgorithm`, chooses the cheaper of two fully specified configurations by their actual call counts. Both use the existing dyadic variance-reduction execution. The first uses a fresh anchor batch at every step. The second uses multilevel difference batches and periodic anchors. The step length is ε/(4L), the number of updates is `ceil(16LΔ/ε²)`, and the output is an independently uniform pre-update iterate among indices 0 through K. Tuning is explicit in `DyadicHolder.tcfg` and `anchorConfig`; selection does not use unknown oracle information. The proof connects these batches and the output to `OracleTemplate.execute`, including initialization and every pair call.

The centered martingale error and normalized-descent arguments are reused from the repository. The additional rough-noise step works at the **upper bounds on path distances**, not by pretending that the oracle is globally one-half-Hölder. At level j a path has length at most 2^j η, so for ν≤1/2,

\[
M(2^j\eta)^{2\nu}\le M\eta^{2\nu-1}(2^j\eta).
\]

This lets the multilevel error proof use the one-half tuning with effective coefficient Mη^{2ν−1}. No minimum distance between actual iterates is assumed. This distinction matters for nonlinear paths, which may return arbitrarily close to an earlier point. The [scale proof](../Proofs/HolderNoiseScales.lean), [accuracy proof](../Proofs/HolderNoiseAccuracy.lean), [cost proof](../Proofs/HolderNoiseCount.lean), and [execution proof](../Proofs/HolderNoiseExecution.lean) establish the resulting rate and the cap without changing the existing framework.

## Motivation and assumptions

Smoothness of the population objective need not imply smooth sample gradients. For a concrete nonlinear family, take a finite set of nonorthogonal feature vectors a with ‖a‖≤F and responses b conditional on a distributed as N(μ(a),s²), with a common s>0 and finite means. Use the loss |aᵀx−b|^r, where 1/2<r<1. Set its stochastic derivative to zero at residual zero, a null event for each fixed query. Its second moment is finite despite its singularity near zero residual. With constants depending only on r, this family satisfies

\[
\sigma^2\lesssim_r F^2s^{2r-2},\qquad
M\lesssim_r F^{2r+1}/s,\qquad
L\lesssim_r F^2s^{r-2},\qquad \nu=r-1/2.
\]

Indeed, for h_r(t)=r sign(t)|t|^{r−1}, translation and rescaling give `∫ |h_r(t+h)−h_r(t)|² dt = C_r |h|^{2r−1}`, with finite C_r: the singularities are square integrable and the difference decays integrably at infinity. The Gaussian density is bounded by a constant divided by s, and |aᵀ(x−y)|≤F‖x−y‖. Centering can only reduce the second moment of this increment. Gaussian rescaling bounds the gradient second moment uniformly in the residual mean and bounds the derivative of the convolved population gradient, giving the displayed σ and L estimates. The nonnegative loss has finite expectation at x0, so that value supplies Δ. Multiple nonorthogonal features give nonseparable objectives in arbitrary finite dimension. Adding a deterministic quadratic preserves the centered-noise bounds, increases L by its curvature, and permits unbounded mean gradients.

Fractional residual regression is independently motivated by [Muvunza, Li and Kuruoglu, PGM 2024, §3.1.2, equations (17)–(19)](https://proceedings.mlr.press/v246/muvunza24a.html). That citation motivates the loss; its unbounded Cauchy predictors do not satisfy the bounded-feature example automatically. The example above is explanatory mathematics, not a separately formalized application theorem. The formal main theorem covers every oracle satisfying the stated assumptions, including finite-support distributions when their gradients have the required regularity.

Population smoothness, bounded initial gap, unbiasedness, variance bounds, and paired samples are standard stochastic nonconvex assumptions. Centered Lipschitz noise is an established variance-reduction assumption. The spatial exponent ν<1 is the extension studied here; it is distinct from weakening the moment order. No bounded-gradient assumption, finite-sample-space assumption, or convergence hypothesis is imposed on the upper bound.

## Closest results and reductions

- [Arjevani et al., arXiv:1912.02365v2, 27 February 2022, Theorem 3 and §4](https://arxiv.org/abs/1912.02365), published in Mathematical Programming (2023), establishes foundational bounded-variance and mean-squared-smooth nonconvex lower bounds. Our lower construction uses that paradigm; interpolation and optimizing effective smoothness are not claimed as new techniques. The fractional phase is compared under the same expected norm scale and paired information, not by equating different success probabilities.
- [Zhou, Xu and Gu, SNVRG, JMLR 21(103), 2020](https://www.jmlr.org/papers/v21/18-447.html), uses nested variance reduction under mean-squared smoothness. That hypothesis gives quadratic distance dependence. Substituting a spatial Hölder exponent into its theorem is invalid. Its hierarchy is conceptual prior art for the estimator.
- [Fradin et al., AISTATS 2026, arXiv:2512.18713v2, 31 March 2026, Assumption 2.7 and Theorem 4.2](https://proceedings.mlr.press/v300/fradin26a.html), treats centered similarity and relaxed moments. Its q exponent controls moment order with Lipschitz distance scaling, rather than the second moment with distance exponent 2ν here. Its finite-variance Lipschitz endpoint is known; changing q does not give the fractional-noise theorem.
- Standard batching gives O(1+D+A+S). A single-level difference estimator with increments of size O(ε/L) and optimized refresh period instead gives a variation term of order Δ L^{1−ν}√M σ / ε^{4−ν}, together with batching/base terms. That reduction does not reach ε^{-(4−2ν)} below one-half or the full fractional phase. Smoothing does not remove this gap without paying the corresponding bias and sampling costs. The multilevel allocation, rather than clipping or a renamed parameter, is essential to the bound.
- Population-Hölder results such as [Can SGD Handle Heavy-Tailed Noise?, arXiv:2508.04860v2, 2 October 2026](https://arxiv.org/abs/2508.04860) concern a different regularity object and restricted SGD schedules. They do not establish this paired-oracle minimax statement.

Repository history is also prior art: [PR #18](https://github.com/k3nfalt/longtails/pull/18) already implements a dyadic upper bound for raw mean-squared Hölder gradients at ν≥1/2 and explicitly leaves ν<1/2 open; its lower discussion is not a proved unrestricted lower bound. [PR #23](https://github.com/k3nfalt/longtails/pull/23) already supplies centered analysis, with user feedback warning against novelty claims defeated by standard reductions. [PR #25](https://github.com/k3nfalt/longtails/pull/25) gives a log-free ν=1 bound in its zero-relative-noise specialization. Neither centering nor the old hierarchy is claimed as new. The contribution is the completed fractional regime and its full minimax parameter dependence; formal verification alone is not its significance.

The final PR check also included [PR #185](https://github.com/k3nfalt/longtails/pull/185). Its ABC-noise lower bound covers all randomized algorithms, while its upper bound constructs SGD. Its exact setup uses fresh single-point queries and a pointwise variance bound involving objective gap and gradient norm, without a spatial-increment condition. The bounded-variance specialization gives the known SGD cap. Its lower bound over a larger, rougher oracle class does not transfer to this regularity subclass with paired access. Its whole-edge masking and prefix counting also reinforce that those techniques are not the novelty claimed here.

Research and independent review screened publicly available ICML, ICLR and NeurIPS 2025/2026 material, roughly November 2024–November 2026 arXiv submissions/revisions, cited older primary results, and relevant repository PRs as of 17 November 2026 UTC. This is targeted coverage, not a claim to have read every paper or every PR. Some OpenReview/virtual-conference pages were inaccessible; accessible primary versions were used where available. No claim relies on treating an inaccessible source as disproved or on the absence of a keyword search hit.

Specifically, the official abstract for [Median-of-Means under Structured Heavy-Tailed Noise, NeurIPS 2026](https://neurips.cc/virtual/2026/poster/148757) was accessible, but its OpenReview PDF returned HTTP 403. The abstract describes symmetric heavy-tailed and mean-zero moment components, median-of-means estimation, and high-probability clipped optimization with a bias neighborhood. This is adjacent distributional-structure work, rather than an identified result for spatial Hölder increments. Its full theorem assumptions were not checked, and no theorem-level exclusion is claimed.
