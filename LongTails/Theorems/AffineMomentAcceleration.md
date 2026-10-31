# Acceleration with mixed additive and multiplicative finite-moment noise

[The Lean theorem](AffineMomentAcceleration.lean) gives a high-probability oracle-complexity bound for smooth convex optimization with affine central-moment noise. The proposed contribution is an improved joint dependence on multiplicative noise and accuracy while retaining the usual additive finite-moment cost. It concerns the problem class, without restricting admissible algorithms to the constructed method.

## Problem and guarantee

The [specification](../Setups/AffineMomentConvex.lean) assumes a globally convex, differentiable objective with globally L-Lipschitz gradient, a minimizer xstar satisfying ‖x0−xstar‖≤R, and known positive L,R,ε, confidence δ∈(0,1), exponent p∈(1,2], and nonnegative noise bounds σ0,σ1. Lean uses `α` for p and `σ` for σ1. The oracle is jointly measurable, unbiased, and satisfies

\[
\int\|g(x,\omega)-\nabla f(x)\|^p\,d\rho(\omega)
\le \sigma_0^p+\sigma_1^p\|\nabla f(x)\|^p.
\]

Here ρ is the oracle probability law. The specification explicitly includes integrability and uses the repository's IID structure for an abstract sampling law. It does not require a finite sample space, finite variance when p<2, sample-gradient smoothness, sample convexity, bounded noise, function values, or knowledge of the minimizer. The formal Hilbert-space statement includes arbitrary finite dimension and separable complete real Hilbert spaces; there is no explicit dimension factor.

Write q=p/(p−1), r=p/(3p−2)=q/(q+2), T=LR²/ε, V=(σ0R/ε)^q, and ell=log(20+q+T+1/δ). The public budget is

\[
\left\lceil 2^{256q}\left[(1+\sigma_1)^q(4+T)^r+
 \left(\sigma_0\left(\frac4{LR}+\frac R\epsilon\right)\right)^q\right]
 \ell^{q+1}\right\rceil.
\]

The returned final primal iterate has f(output)−f(xstar)≤ε with probability at least 1−δ. The specification expresses failure probability as an indicator integral and requires output measurability. The budget counts every individual oracle reply, including both estimation blocks and any padding imposed by `execute`. The coarse-accuracy additive term 4σ0/(LR) is retained. For T≥1, suppressing logarithms and constants depending on p, the bound is

\[
\widetilde O_p\big((1+\sigma_1)^q T^r+V\big).
\]

The constants are deliberately conservative. This is a complexity theorem, not a practical tuning recommendation or a claim of optimal logarithmic dependence. All noise parameters are available to the algorithm; this is not an adaptivity improvement.

## Algorithm and proof mechanism

The [algorithm](../Algorithms/AffineMomentAccelerated.lean) normalizes coordinates around x0 by R and the objective by LR². It keeps a primal point in the radius-four ball and a mirror point in the unit ball. Each coupled query uses two independent batches at the same point: a robust pilot estimates direction and magnitude, while a fresh ordinary mean supplies an unbiased mirror correction. The pilot is an implementable [neighbor-count estimator](../Algorithms/AffineGradientEstimator.lean), whose comparison radii include a known positive additive floor. It does not use the true gradient in its selection rule.

With normalized accuracy e=min(ε/(LR²),1/4), the iteration count is K=ceil((2^48 log(16+q+1/e+1/δ)/e)^r). Set D=2^40 K^((2−p)/p), a_k=(k+1)/D, A_k=k(k+1)/(2D), and ν=K^(-(2p−1)/p). Each pilot group and raw correction use batches sized according to σ1+σ0/(LRν). The pilot is accurate to (‖∇f‖+ν)/8 except on a controlled event; the fresh mean has p-th moment at most 4(‖∇f‖^p+ν^p).

The primal update is a short Frank–Wolfe step toward −4h/‖h‖, with step fraction min(1,‖h‖/128); the mirror update projects z−a_k G onto the unit ball. The [mixed-error descent lemma](../Proofs/AffineMomentPrimal.lean) proves a decrease of at least ‖∇f‖²/1024−ν². It explicitly handles zero pilots and zero gradients. Primal boundedness holds even on inaccurate pilots.

The proof couples this quadratic descent reserve to the finite-p mirror remainder. The [parameter inequalities](../Proofs/AffineMomentParameters.lean) allocate half of the per-step drift to absorbing a_k^p‖∇f‖^p and half to A_{k+1}ν²+20a_k^pν^p. Both accumulated additive contributions remain bounded with the stated ν. A bounded-energy exponential argument then controls the mirror process without assuming a second moment of the raw oracle. The proof-only stopped process freezes on the first failed pilot; [failure accounting](../Proofs/AffineMomentFailures.lean) and [trajectory agreement](../Proofs/AffineMomentTrajectory.lean) transfer its guarantee to the actual algorithm. No exact-gradient repair is implemented.

The key balance is K times the batch cost: it is proportional, up to constants and logarithms, to (1+σ1)^q K+(σ0/(LR))^q K^(q+2). Since r(q+2)=q, the additive term becomes V while the multiplicative term retains exponent r. This balance, and a pilot floor compatible with both descent and finite-moment mirror concentration, are the mathematical mechanism. [Execution](../Proofs/AffineMomentExecution.lean), [probability transfer](../Proofs/AffineMomentRun.lean), and [budget algebra](../Proofs/AffineMomentBudget.lean) connect it to the public theorem.

## Closest results and precise improvement

[Lobanov, Dvinskikh and Gasnikov, arXiv:2609.33415v1](https://arxiv.org/html/2609.33415v1), September 27, 2026, Theorem 9 and Assumptions 1–3, specialize to the present smooth affine-moment setting by taking H1=0 and the gap-dependent noise coefficient zero. Their bound has terms sqrt(T), σ1^q T^(q/2), and V, up to logarithms. Their broader generalized-smoothness and gap-dependent-noise scope is not claimed here. Theorem 10 is the strongly convex comparison used in the regularization check. This is an unreviewed preprint; no conference acceptance is asserted.

[Nekrasova et al., arXiv:2610.28107v1](https://arxiv.org/html/2610.28107v1), October 20, 2026, Assumption 3.4, Theorem 5.2 and Table 1, give the same polynomial comparison for the finite-moment specialization of Clip-SSTM. Their weak-Lp alternative permits distributions excluded here, and their local smoothness formulation is more general than our global assumption. Thus this theorem improves complexity on a common established subclass, not the scope of that paper. Both latest-version pages were rechecked on October 25, 2026; each still listed v1.

For fixed p∈(1,2), fixed positive σ1, and V=T^v with r<v<q/2, the new upper bound is proportional to T^v up to logarithms, compared with T^(q/2) in these affine-noise guarantees. This is a polynomial improvement in a low-additive-noise regime. For example, p=3/2, L=R=σ1=1, σ0=η and ε=η^(3/2) give new cost approximately η^(-3/2), versus η^(-9/4), as η tends to zero. The theorem does not impose this relation between parameters; it identifies where the comparison is significant.

For fixed σ0>0 and ε tending to zero, V eventually dominates both bounds: there is no claimed fixed-noise asymptotic gain. At σ1=0, established additive-noise clipped acceleration gives approximately sqrt(T)+V and can be faster than this theorem's T^r+V; the novelty requires a positive multiplicative component. At σ0=0, the repository's [recursive relative-error result](RecursiveRelativeErrorConvex.md), composed with finite-moment median-of-means estimates, gives T^(1/2+o(1)) for fixed p and noise, which is asymptotically stronger than T^r. In the deterministic limit, ordinary accelerated gradient descent is also stronger. The p=2 endpoint is not the novelty claim: [Gupta, Siegel and Wojtowytsch, NeurIPS 2024](https://papers.nips.cc/paper_files/paper/2024/hash/24d2dd6dc9b79116f8ebc852ddb9dc94-Abstract-Conference.html) already establish acceleration with finite-variance multiplicative noise. No universal superiority or matching problem-class lower bound is claimed.

## Standard reductions checked

Batching the published affine-noise bounds reduces each moment scale by n^(-1/q), but multiplying by n leaves σ1^q T^(q/2) and V unchanged and increases the deterministic term. Uniformly replacing multiplicative noise by an additive bound on the radius-R region gives an approximately σ1^q T^q contribution. Neither gives this theorem.

Direct regularization with strength λ≈ε/R², followed by the published strongly convex theorem, recovers the same multiplicative exponent q/2. A pure-relative recursive solver does not accept a nonzero absolute floor in its oracle interface. Making each physical query uniformly accurate to ε/R pays an additive V factor per query; that calculation alone is not evidence against all adaptive allocations.

A stronger comparison uses [Kulunchakov and Mairal, NeurIPS 2019](https://papers.neurips.cc/paper/9421-a-generic-acceleration-framework-for-stochastic-composite-optimization.pdf), Proposition 4 and Equation 13. Optimizing nonuniform inner tolerances in its ordinary approximate-prox guarantee still incurs additive work VK for K outer iterations, up to logarithms. Even granting favorable multiplicative inner cost, optimizing regularization yields the comparison sqrt(T) V^(1−1/q), slower than V when v<q/2. Proposition 6 avoids that stochastic penalty using an additional lower-surrogate certificate, Equation 14 and H1/H2; function-gap accuracy of the finite-p inner solver does not provide that certificate. These are comparisons of available guarantees, not impossibility results for future recursive or surrogate methods.

## Motivation and limitations

Affine central-moment noise is the model used by the two closest primary papers; no new structural assumption is added to force the proof. A nonlinear interacting-coordinate family is f(x)=sum_j w_j log cosh(⟨a_j,x−xstar⟩), with positive weights and dense nonorthogonal vectors a_j. Its smoothness constant is bounded by the operator norm of sum_j w_j a_j a_jᵀ. The oracle (1+Z1)∇f(x)+Z0 v, for a unit vector v and centered random gains with E|Zi|^p≤2^(1−p)σi^p, satisfies the model. These gains may have infinite variance when p<2. This represents multiplicative gain error together with additive measurement noise; the theorem also permits transverse, point-dependent errors beyond this illustrative family.

The result requires known moment and geometry bounds, global smoothness and convexity, independent samples, and finite central p-th moments. It does not extend to weak-Lp tails, dependent sampling, unknown noise scales, or nonsmooth objectives. The logarithmic factors and exponential-in-q constants are not optimized. A finite-variance endpoint, formal verification by itself, or a new algorithm name is not the contribution. The substantive claim is the stated mixed-noise complexity improvement in the explicitly identified regime. An improved recursive stochastic solver or another stronger primary result could narrow that claim; the literature comparison must be assessed on its assumptions and actual oracle cost.

## Literature coverage and access

The research and independent review used targeted searches of the two latest publicly available editions at the October 25, 2026 UTC cutoff: ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2025/2026, together with roughly October 2024–October 2026 arXiv submissions and revisions. NeurIPS 2026 had a public [download listing](https://neurips.cc/Downloads/2026). Older papers were followed when foundational or stronger, including the NeurIPS 2024 multiplicative-noise result and NeurIPS 2019 stochastic Catalyst framework. This was targeted optimization coverage, not exhaustive reading of conference programs. Closest comparisons used primary assumptions, theorem statements and relevant proof interfaces, rather than search-result absence.

Some full conference indexes were tool-limited or JavaScript-only; paper-level official sources were used. The final full text of Kornilov et al., *Intermediate gradient methods with relative inexactness*, [JOTA 207, article 62 (2025)](https://doi.org/10.1007/s10957-025-02809-y), was inaccessible; the accessible comparison was [arXiv:2310.00506v1](https://arxiv.org/abs/2310.00506v1), not an assertion about identical final journal theorems. Some SNAG appendix constants were also inaccessible. Its checked finite-variance/exponential-moment results do not directly supply the arbitrary finite-p affine-noise guarantee, but unavailable refinements are not asserted absent. These access limitations remain limitations of the novelty audit.
