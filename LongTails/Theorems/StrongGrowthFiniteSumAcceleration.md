# Finite-sum acceleration under strong growth

The [formal theorem](StrongGrowthFiniteSumAcceleration.lean) gives an expected-objective oracle bound for a finite sum with convex smooth components, a strongly convex mean, and the global strong-growth condition. The proposed contribution is the dependence on the strong-growth constant in this problem-class bound, rather than a new analysis of a prescribed update family. The proximal stability inequality used in the proof is standard.

## Problem and guarantee

The [setup](../Setups/FiniteSumStrongGrowthStronglyConvex.lean) is
\[
 f(x)=n^{-1}\sum_{i=1}^n f_i(x),\qquad
 n^{-1}\sum_i\|\nabla f_i(x)\|^2\leq\rho\|\nabla f(x)\|^2\quad\text{for every }x.
\]
Each component is convex and differentiable with an L-Lipschitz gradient. The mean is μ-strongly convex, with μ>0, ρ≥1, and a minimizer x⋆ satisfying ‖x₀−x⋆‖≤R. The space is an arbitrary finite-dimensional real inner-product space. Individual components need not be strongly convex. Global strong growth, rather than interpolation alone or a local growth inequality, is essential to this result. At x⋆ it implies that every component gradient vanishes.

The oracle returns the exact gradient of any component requested by the algorithm. One such return costs one call. Function values, Hessians, and optimization oracles are unavailable. The public parameters include L, μ, ρ, R, and ε; the method is not adaptive to unknown versions of these constants. No algorithm-family restriction is imposed.

Write κ=L/μ and
\[
 r=\min\{n,\lceil128\rho\rceil\},\quad
 B=\operatorname{clog}_2\lceil7168(1+\kappa)\rceil,\quad
 T=\operatorname{clog}_2\lceil LR^2/\varepsilon\rceil.
\]
Here clog is the natural-number ceiling logarithm used by Lean, including its zero convention. The public budget is exactly
\[
 108\bigl(r+\lceil\sqrt{r\kappa}\rceil\bigr)BT.
\]
The theorem proves, for the returned point X and its explicit finite uniform algorithm-seed distribution, integrability and
\[
 \int [f(X)-f(x_\star)]\,dP\leq\varepsilon.
\]
It covers R=0 and T=0 without a limiting interpretation. In asymptotic notation the bound is
\[
 O\bigl((r+\sqrt{r\kappa})\log(2+\kappa)\log(2+LR^2/\varepsilon)\bigr).
\]
The probability measure in the theorem is the product of the algorithm's finite uniform seed measure and the oracle's law. Exactness makes the output independent of the latter. There is no claim for noisy component-gradient replies, high-probability accuracy, or infinite-sum sampling.

## Algorithm and proof

The [algorithm](../Algorithms/StrongGrowthBatchProx.lean) repeatedly draws r independent uniform component indices with replacement. When r=n it instead uses the entire finite sum deterministically. At an outer center c, it approximately minimizes
\[
 F_B(u)+\tfrac\mu2\|u-c\|^2
\]
using the repository's counted Katyusha implementation and an explicit quadratic prox computed by arithmetic. The number of inner epochs is fixed from public parameters. It does not depend on an unknown distance to x⋆ or an observed objective value. The final output is the last outer center, not an average or a best iterate.

The implementation translates each quadratic-prox request in the existing inner query plan into a dummy component-gradient request whose answer is ignored. Thus even those requests are charged. The inner plan uses 9r gradient calls per epoch. The execution theorem also counts any ignored fallback queries between the plan length and the simplified public budget. Neither exact proximal minimization nor free component gradients are hidden in the cost.

Let y be the exact proximal point of the population objective at c, and w the exact proximal point of a fresh batch. Strong monotonicity of the regularized batch gradient gives the standard stability bound
\[
 \mu\|w-y\|\leq\|\nabla F_B(y)-\nabla f(y)\|.
\]
Crucially, y depends on c but not on the fresh batch. Its sampling variance can therefore be bounded at this fixed point. The population optimality condition and strong growth give
\[
 \mathbb E\|w-y\|^2\leq (\rho/r)\|c-y\|^2.
\]
The exact population proximal map contracts distance to x⋆ by 1/2. Common component minimization and proximal Fejér monotonicity control the initial gap of each batch subproblem by a multiple of ‖c−x⋆‖². The inner accelerated solve has mean squared error at most ‖c−x⋆‖²/512. Combining these estimates yields a squared-distance contraction of at most 1/2 per outer step. In the capped branch r=n the batch perturbation is zero; the proof does not incorrectly assume ρ/n≤1/128.

The proof modules separate [stability and sampling](../Proofs/StrongGrowthBatchProx.lean), the [batch model](../Proofs/StrongGrowthBatchModel.lean), the [inner guarantee](../Proofs/StrongGrowthBatchInner.lean), [contraction](../Proofs/StrongGrowthBatchContraction.lean), [convergence](../Proofs/StrongGrowthBatchConvergence.lean), [budget algebra](../Proofs/StrongGrowthBatchBudget.lean), and [actual execution](../Proofs/StrongGrowthBatchExecution.lean). The unknown radius is used only to analyze the inner solve; rescaling the proof's gap parameter leaves its fixed tuning and output unchanged.

## Closest comparisons and scope of the claim

The comparison is for general nonlinear objectives, exact selectable component gradients, and expected objective error. Constants and logarithms matter near regime boundaries; the displayed asymptotic improvements are not universal dominance claims.

* Full-gradient acceleration costs O(n√κ) per accuracy logarithm. Generic finite-sum acceleration costs O((n+√(nκ))) per accuracy logarithm. For the latter comparison when only the mean is strongly convex, restart the non-strongly-convex bound in [Allen-Zhu, Katyusha, JMLR 2018, Theorem 4.1](https://jmlr.org/papers/volume18/16-410/16-410.pdf), using strong convexity to convert squared distance to objective error. Theorem 2.1 of that paper applies directly to our *inner* problems because their quadratic regularizer is strongly convex; it should not be cited directly for the outer mean-only assumption.
* Under interpolation and component smoothness, the accelerated minibatch result of [Woodworth and Srebro, NeurIPS 2021, Theorem 3, arXiv v2](https://arxiv.org/abs/2106.02720v2) has terms exp(−cT/√κ) and exp(−cbT/κ). Counting bT samples retains a κ contribution, even though optimum noise vanishes. It does not yield the bound here by choosing a batch size.
* Strong-growth acceleration bounds with linear dependence on ρ include [Hermant et al., ICLR 2025, Theorem 3, arXiv v3](https://arxiv.org/abs/2410.07870v3) and [SHANG++, Theorem 2.2, arXiv v2](https://arxiv.org/abs/2603.09355v2). Their condition number uses population smoothness where indicated. Comparisons below use instances where population and component smoothness coincide. Ordinary batching of such a bound reduces relative variance but charges for every member of the batch; it does not by itself give √ρ dependence in total calls.
* [Valls et al., arXiv 2207.11833v1, Corollary 1](https://arxiv.org/abs/2207.11833v1) requires a bounded relative-variance level below a fixed threshold; obtaining that threshold by ordinary batches costs order ρ per update. Its separate gradient-difference variance hypothesis is not a consequence of global strong growth. [MaSS, ICLR 2020, arXiv v5, Theorems 3–4](https://arxiv.org/abs/1810.13395v5) distinguishes its quadratic acceleration result from its general-convex guarantee.
* Existing minibatch/proximal analyses are close mechanisms, not interchangeable theorems. [Asi et al., NeurIPS 2020, Proposition 1 and Appendix A](https://proceedings.neurips.cc/paper_files/paper/2020/file/fa2246fa0fdf0d3e270c86767b77ba1b-Supplemental.pdf) controls sampling error at the current point and uses a smoothness step-size cap. [Yuan and Li, JMLR 2023, Appendix A.1, Lemmas 20–22](https://jmlr.org/papers/volume24/21-1219/21-1219.pdf) uses replacement-sample stability and self-bounding of random empirical outputs. Those inequalities do not give the fixed population-prox variance estimate above by direct strong-growth substitution. [Tovmasyan et al., arXiv 2502.03401v2, Appendix C, Theorems 20–21](https://arxiv.org/abs/2502.03401v2) has a stepsize restriction involving its star-similarity parameter; substitution using only strong growth and smoothness loses condition-number factors. The resolvent inequality itself is standard: the contribution claimed here is its combination with a fresh batch and a counted accelerated finite-sum inner solve to obtain the stated class guarantee.

For example, when n≫ρ, κ≫ρ, and the population smoothness is comparable to L, the leading cost here is √(ρκ), with an extra log(2+κ). Against the best of the checked bounds κ, n+√(nκ), and ρ√κ, the possible polynomial gain is limited by min{√(κ/ρ),√ρ}, before that extra logarithm. For ρ=1 or n small the extra inner logarithm can make the present result worse. No matching lower bound, optimality claim, or removal of that logarithm is proved.

Two superficially stronger historical claims require particular care. [Mishkin et al., arXiv 2404.02378v2](https://arxiv.org/abs/2404.02378v2) explicitly invalidates its earlier improved growth dependence. [Vaswani et al., arXiv 2110.11442v4, Section 7](https://arxiv.org/abs/2110.11442v4) corrects its earlier general-growth acceleration claim; the corrected analysis concerns bounded variance. The withdrawals alone are not evidence of novelty.

## Nonlinear instances and restrictions

A dimension-independent family illustrating the improvement uses x=(t,u), with u∈ℝᵈ, a(t)=Lt²/2, and
\[
 b(u)=\tfrac\mu2\|u\|^2+c\sum_j\log\cosh(v_j^\top u),\qquad
 c\sum_j\|v_j\|^2\leq\mu.
\]
Choose nonorthogonal v_j so coordinates interact, an integer q dividing n, and L≥2qμ. A fraction 1/q of the components equal a+qb; the remainder equal a. Their mean is a+b, its smoothness and the common component smoothness bound are L, and it is μ-strongly convex. Their strong-growth constant is q: the average squared gradient is |a′|²+q‖∇b‖². Flat component directions are allowed. With κ=q³ and n=q³ the displayed cost is order q² up to logarithms, versus q^(5/2) for the closest checked growth-sensitive accelerated bound. The theorem does not assume this family, a fixed spectrum, separability, or knowledge of the minimizer. This example is a mathematical illustration, not a separate formally exported theorem.

Global strong growth is restrictive: generic inconsistent finite sums and additive stochastic noise are excluded. The result retains component convexity, a known global component smoothness bound, strong convexity of the mean, a supplied radius, and selectable exact component access. Removing any of these is outside the proved claim. Neither naturalness nor significance follows merely from the existence of the example; the setup is the established global strong-growth finite-sum question.

## Literature coverage

The research and independent review searched current ICML, ICLR, NeurIPS, and arXiv literature as of 3 November 2026 UTC, followed citations to older baselines, and checked corrections and latest versions of the closest papers. The two most recent publicly available conference editions included ICML 2025/2026, ICLR 2025/2026, and the newly public NeurIPS 2025/2026 inventory. Accepted status was checked through official proceedings or OpenReview; arXiv-only claims were treated as preprints.

The NeurIPS 2026 inventory required an additional screen after its public availability was established. Relevant checks include [Perfect Parallelization in Mini-Batch SGD with Classical Momentum Acceleration, arXiv v1, Definition 1 and Theorem 1](https://arxiv.org/abs/2605.18609v1), whose model is stochastic linear contraction/consistent convex quadratics; [EMA-Nesterov, arXiv v1, Section 3.2 and Theorem 1](https://arxiv.org/abs/2605.25395v1), whose acceleration theorem uses exact gradients; and [Universal Adaptive Proximal Gradient Methods via Gradient Mapping Accumulation, arXiv v1](https://arxiv.org/abs/2605.05944v1), whose stochastic assumptions use a fixed bounded variance and whose displayed accelerated stochastic guarantee has a noise term. These do not establish the nonlinear finite-sum strong-growth bound claimed here.

The accepted NeurIPS 2026 paper [From Inexact Gradients to Byzantine Robustness: Acceleration and Optimization under Similarity](https://openreview.net/forum?id=wx2qpHOXO8) is a specific access limitation: its current OpenReview PDF returned HTTP 403 to both investigators. Its accepted abstract differs from [arXiv 2602.03329v1](https://arxiv.org/abs/2602.03329v1), so the accepted theorem statements have not been verified. The accessible earlier Algorithm 1 requests all client gradients per global query, and its similarity method uses an additional proxy objective; its communication bounds therefore do not directly establish the total component-call bound here when ρ≪n. The latest accepted version remains an explicit literature uncertainty.

Some inventory/API requests also timed out or returned access errors; official poster pages, accessible proceedings, and arXiv versions were used instead. Search coverage does not constitute a proof that no unlocated result exists. The final novelty assessment must rest on the independently checked closest theorem comparisons, not the absence of a search hit or the Lean formalization itself.
