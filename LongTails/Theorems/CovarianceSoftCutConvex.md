# Covariance-only stochastic convex optimization by soft cuts

The [main theorem](CovarianceSoftCutConvex.lean) gives a subgradient-only oracle algorithm for globally convex, Lipschitz objectives in arbitrary finite dimension. It attains error at most ε with probability at least 2/3 using

\[
N=\left\lceil 2^{32}\left(d+\frac{\sigma^2R^2}{\varepsilon^2}\right)
\left[1+\log\!\left(16d\left(1+\frac{LR}{\varepsilon}\right)\right)\right]^5\right\rceil
\]

oracle calls. The contribution is a finite-covariance extension of the dimension-additive, directional-exponential-tail guarantee of Marsden–O’Carroll–Sidford–Zhang, with logarithmic overhead. It is not a solution of their general trace-variance open problem, a new optimal logarithmic factor, or an arithmetic-time guarantee.

## Problem and oracle

The [setup](../Setups/CovarianceBoundedConvex.lean) specifies a function f : ℝᵈ → ℝ, d ≥ 1, convex and globally L-Lipschitz, with a global minimizer x⋆ satisfying ‖x⋆‖ ≤ R. The algorithm knows d, L, R, σ, ε. It receives neither objective values nor x⋆, the optimal value, or the mean subgradient field.

At query x, a fresh sample supplies g(x, ω). There exists a subgradient selection v satisfying

\[
\langle v(x),y-x\rangle\le f(y)-f(x),\qquad
\mathbb E g(x,\omega)=v(x),\qquad
\mathbb E\langle g(x,\omega)-v(x),u\rangle^2
 \le\frac{\sigma^2}{d}\|u\|^2.
\]

The setup explicitly requires joint measurability of g, integrability of g(x, ·), and integrability of the squared centered norm. These are actual conditions, not inferred from a Bochner integral inequality that could default to zero. The mean selection is measurable as a consequence of the oracle assumptions. No continuity of v or differentiability of f is required. The sampling law is an arbitrary probability measure satisfying the repository’s shared IID structure; product representations are derived in the proof. Samplewise convexity, bounded samples, symmetry, higher moments, and sample replay are unnecessary.

The covariance bound is an upper bound, not an equality or an assumption that noise is rotationally invariant. Equivalently, σ² can be chosen as d times a uniform bound on the covariance operator norm. This differs from a trace bound: for anisotropic noise, this parameter can be up to d times the trace. The theorem does not claim the same rate with σ² replaced by an arbitrary trace-variance bound.

This is the known-distance unconstrained problem. Queries lie in B(0, 2R), and the returned point lies in the convex hull of the candidate queries. The specification still assumes a globally defined objective and global oracle, matching the closest baseline’s Problem 1. It does not assert a theorem for arbitrary constrained domains.

For a concrete interacting nonlinear family, take a dense invertible matrix A and ‖a‖ ≤ R, and let f(x) = ‖A(x−a)‖, with ‖A‖op ≤ L. A valid selection is AᵀA(x−a)/‖A(x−a)‖ away from a, and zero at a. Adding independent centered Pareto coordinates of exponent between 2 and 3, scaled to covariance σ²I/d, gives an asymmetric finite-variance oracle without a finite third moment or exponential tails. Orthogonal mixing of the noise is also permitted. Smooth examples include scaled sqrt(1+‖A(x−a)‖²). These examples illustrate the broader class; the proof covers all instances of the setup.

## Algorithm, output, and cost

The [core definitions](../Algorithms/CovarianceSoftCut.lean) implement centroid queries, batched means, scalar median-of-means estimates, and a balanced comparison tree. The [complete method and tuning](../Algorithms/CovarianceSoftCutMethod.lean) specify the chronological oracle schedule and returned output.

In the nontrivial regime ε < LR, set α = ε/2 and

\[
X=24[1+d\log(16LR/\varepsilon)],\quad
H=\lceil\log X/\log2\rceil,\quad T=2^H,\quad
b=\max\{1,\lceil4096\sigma^2R^2/(d\varepsilon^2)\rceil\}.
\]

Start with uniform density on B(0, 2R). At each of T rounds, query the current density’s centroid xₜ, form the mean ḡₜ of b fresh oracle replies, retain xₜ as a candidate, and multiply the unnormalized density at y by

\[
\exp\!\left[-\frac2\alpha
 \max\{0,\langle\bar g_t,y-x_t\rangle+\alpha/2\}\right].
\]

Every finite-history density has positive mass. Its centroid is well-defined and measurable. The last generation batch is executed and counted, even though the last retained candidate precedes that batch.

A balanced binary tree then selects a single point without objective values. Each merge repeatedly bisects the segment between its current endpoints, estimating the directional mean subgradient by scalar median-of-means. A confidently positive or negative estimate retains the corresponding half; a small estimate freezes both endpoints at the midpoint. The final merge output is its midpoint. The definitions execute the fixed comparison slots even after freezing.

The tuning uses τ = ε/(2H), a = τ/(12R),

\[
K=\left\lceil\frac{\log(4LR/\tau)}{\log2}\right\rceil,\quad
n=\max\{1,\lceil8\sigma^2/(da^2)\rceil\},\quad
C=(T-1)K,\quad m=2\lceil4\log(12\max\{1,C\})\rceil+1.
\]

Each directional estimate uses m groups of n samples at one fixed pre-batch point. Useful work is exactly Tb + Cnm. The [budget proof](../Proofs/CovarianceSoftCutBudget.lean) bounds it by 2³⁰(d + σ²R²/ε²)Q⁵, where Q is the logarithmic factor in N. The public `budget` is the explicit single-line formula above. Execution uses N calls: remaining calls query zero and do not change the returned output. This padding is included in N. When ε ≥ LR, the method returns zero, which is already ε-good, and likewise performs the prescribed padding calls.

Exact centroid integration and exact real arithmetic are free in this oracle model. No polynomial arithmetic implementation or approximate-centroid robustness theorem is proved.

## New proof mechanism

The new ingredient is the combination of a shifted convex penalty, deterministic centroid mass contraction, and an expected target-log-loss argument under directional second moments.

* Each density remains logconcave. Grünbaum’s inequality gives at least 1/e mass to the positive halfspace through its centroid. The shifted hinge therefore shrinks total unnormalized mass by at least a universal factor; the formal proof uses 5/6. This holds for every reply, including a zero vector, without a simultaneous oracle-accuracy event.
* Consider the target ball B(x⋆, α/(4L)). If xₜ has gap greater than α, the true subgradient support inequality and Lipschitzness give a negative margin on this entire ball. The positive hinge caused by noise is bounded by a squared directional error divided by α. The covariance bound and batching consequently make the expected scaled target penalty at most 1/32 per round.
* The proof sums penalties multiplied by the indicator that the current query is bad. This indicator is measurable before the fresh batch. It never conditions oracle centering on the future event that every query is bad. Integrability is proved before using Fubini.
* Jensen’s inequality on the target ball converts accumulated target penalty into a lower bound on remaining mass. On the event that all T candidates are bad, deterministic global contraction forces penalty at least T/8, while its expectation is at most T/32. Markov’s inequality gives generation failure at most 1/4.
* Scalar median-of-means and a predictable-block union bound give selection failure at most C exp(−m/8) ≤ 1/12. A merge potential, min(endpoint values) + (3a/2)·segment width, bounds each merge’s error by τ. Tree depth H adds at most ε/2 to the best candidate’s error.

The [composition proof](../Proofs/CovarianceSoftCutComposition.lean) separates a finite generator prefix from the independent selection suffix using the shared IID law. The [execution proof](../Proofs/CovarianceSoftCutMethodProcess.lean) identifies this stochastic construction with the frozen framework’s actual `execute`, including padding and output measurability. The [guarantee proof](../Proofs/CovarianceSoftCutGuarantee.lean) connects it to the setup’s probability-of-error criterion.

Prékopa–Leindler, Grünbaum geometry, logconcavity of exponential hinge weights, scalar robust mean estimation, and tournament selection are established ingredients. Their formalization is not the research novelty. The adapted supporting Prékopa–Leindler source retains its original license and attribution in [PrekopaLeindler.lean](../Proofs/PrekopaLeindler.lean).

## Closest results and reductions

[Marsden–O’Carroll–Sidford–Zhang, NeurIPS 2025](https://papers.nips.cc/paper_files/paper/2025/hash/a1c0bb652b64f99e26b5bcd60ed2c68f-Abstract-Conference.html), [arXiv 2510.20745v1](https://arxiv.org/abs/2510.20745v1), Problem 1, Definition 5 and Corollary 3, is the closest sound baseline. Its directional exponential-tail model yields Õ(d + σ²R²/ε²). Such tail control implies covariance domination up to universal constants; the converse fails, including for the Pareto examples above. Our improvement is the removal of exponential-tail control while retaining the dimension-additive polynomial dependence. Our explicit fifth-power logarithmic envelope is conservative, and we do not claim sharper logarithms than that baseline. Its footnote already discusses nonsmooth objectives, so nonsmooth coverage is not a separate novelty claim.

The same paper’s literal single-threshold ISGO statement cannot be used as a valid shortcut from Chebyshev’s inequality. Definition 4 allows unbiased replies that are zero with probability 1−p and v(x)/p with probability p, with p arbitrarily below its advertised failure threshold. For the one-dimensional functions sqrt(1+(x−1)²) and sqrt(1+(x+1)²), L = R = 1 and ε = 1/10, their ε-good sets are disjoint. With N queries, the identical all-zero transcript has probability (1−p)ᴺ; average success on the two instances is at most 1−(1−p)ᴺ/2. No finite uniform bound depending only on that single-threshold model’s fixed parameters follows. The conditioning step in Lemma 1 does not preserve centering. Both the arXiv version and [official final paper](https://papers.nips.cc/paper_files/paper/2025/file/a1c0bb652b64f99e26b5bcd60ed2c68f-Paper-Conference.pdf) were checked. This objection concerns that model and reduction, not the directional exponential-tail guarantee, and is not itself the contribution delivered here.

The following standard reductions do not give the new guarantee:

| Reduction | What it provides under comparable covariance assumptions | Remaining cost or scope issue |
| --- | --- | --- |
| Ordinary averaging plus per-cut Chebyshev bounds | A reliable hard cut after accounting for roughly d cuts | The union-bound allocation loses the 1/d batching benefit, producing a dV-type noise cost. |
| Norm-robust vector mean estimation | Error controlled by trace and covariance operator norm | The trace term gives norm-scale error σ/√b, again losing the desired covariance-scale batching benefit for hard cuts. |
| Scalar median-of-means | Covariance-scale concentration in a specified direction | Generation needs one vector before the unknown direction toward the solution is supplied. Scalar estimation does suffice for selection. |
| Elementary radial clipping and Bernstein | Even ideal true-centered clipping bounds directional bias by σ²/(√d·threshold) | Balancing that bias with boundedness costs loses a √d factor. This is a limitation of that calculation, not a lower bound for all clipping methods. |

Bias of a robust vector estimator alone is not an obstruction: a biased estimator with the needed unknown-fixed-direction deviation guarantee could support hard cuts. No impossibility of that primitive is claimed. [Lugosi–Mendelson, JEMS 26 (2024)](https://doi.org/10.4171/JEMS/1321), on direction-dependent mean estimation, retains trace/eigenvalue-tail contributions and stronger moment equivalence; it does not directly supply the covariance-only primitive used in this comparison.

[Feldman–Guzmán–Vempala, SODA 2017, §5.2, Theorems 5.2 and 5.5](https://vtaly.net/papers/FGV_SQConvex.1116.pdf) uses statistical queries and bounded-range models with uniform directional control for hard cuts. [Lattimore, *Bandit Convex Optimisation*, arXiv 2402.06535v5, Chapter 9](https://arxiv.org/abs/2402.06535v5) analyzes hard-cut retention and value-based selection in a different oracle setting. Neither comparison is a conversion of one statistical query or value call into a free stochastic subgradient sample.

[Foster–Krishnamurthy, NeurIPS 2018, §3.1 and Theorem 6](https://proceedings.neurips.cc/paper/2018/file/01e9565cecc4e989123f9620c1d09c09-Paper.pdf) already uses continuous exponential weights with hinge losses to preserve logconcavity. Its contextual-bandit guarantee is not the covariance-only optimization theorem here. [Fradelizi et al., arXiv 2507.06759, Lemma 3.1](https://arxiv.org/abs/2507.06759) supplies the established log-CDF/Jensen geometry underlying the halfspace argument. [Liang–Monteiro–Zhang, arXiv 2505.17463v3, Theorems 3.1 and 4.2](https://arxiv.org/abs/2505.17463v3) studies stochastic cutting-plane models with total-gradient second-moment dependence; its multi-cut bounds do not establish this covariance-shaped dimension-additive rate.

## Improvement regimes and limitations

Write V = σ²R²/ε² and z = LR/ε. The result is Õ(d + V), under the stated operator-covariance normalization. Relative to ordinary stochastic subgradient bounds of order z² + V, its deterministic dependence is useful in low dimension and high accuracy, for example when dQ⁵ is much smaller than z² and noise does not dominate the comparison. The explicit conservative bound does not assert superiority in every parameter regime. For anisotropic noise, replacing trace variance by d‖Cov‖op may make the noise term worse than a trace-based method. No claim resolves the trace-only Õ(d + variance·R²/ε²) question.

The guarantee has fixed success probability 2/3, known public parameters, unrestricted arithmetic, and an unconstrained global objective. It does not supply adaptivity to unknown covariance scale, an optimal logarithmic factor, or an efficient numerical implementation. These limitations are separate from the assumption-removal contribution.

Literature screening was performed independently by Researcher and Reviewer through 29 October 2026, including current conference records, recent arXiv revisions, foundational references, and standard reductions. The versioned comparisons above distinguish the accepted NeurIPS baseline from unreviewed arXiv work. Yu–Ren–Zhou, *Gaussian differentially private robust mean estimation and inference*, Bernoulli 30(4), DOI [10.3150/23-BEJ1706](https://doi.org/10.3150/23-BEJ1706), was checked through the [complete author-uploaded paper](https://www.researchgate.net/publication/385454074_Gaussian_differentially_private_robust_mean_estimation_and_inference) after official PDF access failed. Theorem 2.4 requires a finite norm qth moment for q ≥ 3 and sample size at least of order effective rank plus log n, with additional Gaussian-approximation error; Theorem 2.5 requires a fourth moment. It does not provide the covariance-only high-confidence vector primitive above. No absence of a search result is used as proof of novelty.
