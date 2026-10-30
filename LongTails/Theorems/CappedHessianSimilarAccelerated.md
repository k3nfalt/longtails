# Accelerated optimization with capped participation and average Hessian similarity

The [Lean theorem](CappedHessianSimilarAccelerated.lean) proves an expected objective-gap guarantee for the [capped-client specification](../Setups/CappedHessianSimilarConvex.lean), using the [explicit randomized proximal algorithm](../Algorithms/CappedProximal.lean). Its contribution is a sharper communication-round bound under average similarity, together with coverage of general nonlinear convex clients. It is not a gradient-only oracle bound.

## Problem and guarantee

Let $F=m^{-1}\sum_{i=1}^m f_i$ on an arbitrary finite-dimensional real Hilbert space. Each $f_i$ is differentiable and convex, $F$ is μ-strongly convex, and

$$
\frac1m\sum_i\|[\nabla f_i(x)-\nabla F(x)]-[\nabla f_i(y)-\nabla F(y)]\|^2
\le \delta^2\|x-y\|^2\qquad\text{for every }x,y.
$$

Individual strong convexity, globally Lipschitz gradients, a privileged master client, and bounds on gradient offsets are not assumed. The setup supplies exact local proximal minimizers for every positive quadratic coefficient. The public parameters satisfy $m\ge1$, $1\le s\le m$, μ>0, δ≥0, Δ≥0, and ε>0, with $F(x_0)-F(x^\star)\le\Delta$. The minimizer is an analytical witness, unavailable to the algorithm.

One oracle call is a synchronous round contacting at most $s$ distinct clients. Each contacted client receives one vector, an operation tag and, for a proximal request, a positive scalar coefficient; it returns one gradient or proximal vector. Every snapshot, estimator and proximal exchange is charged. Local computation, including exact proximal solution, is unpriced. This model measures rounds, not individual gradient evaluations or wall-clock time. It has no restriction to a fixed algorithm family.

The returned point is the final primal iterate after fixed numbers of outer steps and restarts. Each inner primal update averages the current sampled local proximal replies; the output is not an average over all past iterations. Under the joint law of the algorithm seed and oracle seeds specified by the algorithm and `Template`,

$$
\int [F(\operatorname{output}(\omega))-F(x^\star)]\,dP(\omega)\le\epsilon.
$$

The public budget is

$$
\left\lceil 2^{40}
\left[1+\frac ms+\left(1+\frac{m^{3/4}}s\right)\sqrt{\frac\delta\mu}\right]
\left[1+\log\left(2+m+\frac\delta\mu\right)\right]
\left[1+\log\left(2+\frac\Delta\epsilon\right)\right]\right\rceil.
$$

Lean writes $m^{3/4}$ as `Real.sqrt ((p.m : ℝ) * Real.sqrt p.m)`. These are equal. The deliberately loose universal constant does not represent a practical performance recommendation. No dimension factor is hidden; storage, vector length, and local solution costs are outside this oracle accounting.

## Algorithm and exact accounting

Write

$$
\rho=\mu+\delta/\sqrt m,\quad q=\mu+\rho,\quad
T=\left\lceil1+64\sqrt{\frac{\delta(1+\sqrt m/s)}q}
 +\frac{2^{20}\delta^2}{s q^2}\right\rceil,\quad \lambda=qT^2/64,
$$
$$
K=\lceil8\sqrt{\rho/\mu}\rceil,\quad
J=1+\left\lceil\frac{\log(2^{20}qK^4/\rho)}{\log8}\right\rceil,\quad
N=1+\left\lceil\frac{\log(2+\Delta/\epsilon)}{\log8}\right\rceil.
$$

An inner epoch solves $H_c(u)=F(u)+\rho\|u-c\|^2/2$, starting from an anchor $w$. It first collects all client gradients at $w$ in $h=\lceil m/s\rceil$ rounds. At each of $T$ accelerated steps it uses an independent uniform size-$s$ gradient cohort to estimate the gradient at the predictor $x$ by the snapshot correction. An independent uniform size-$s$ proximal cohort produces local minimizers of

$$
f_i(u)+\frac\rho2\|u-c\|^2+
\langle g-\nabla(f_i+\rho\|\cdot-c\|^2/2)(x),u\rangle
+\frac\lambda2\|u-x\|^2.
$$

Their sampled mean is the next primal point. Weights satisfy $a^2\lambda=A_{\rm new}=A_{\rm old}+a$; the predictor is $(A_{\rm old}y+a v)/A_{\rm new}$, and the dual update is $v-a\lambda(x-y_{\rm new})$. The known common quadratic is simulated by shifting the input and coefficient of the original client proximal oracle.

The estimator costs one round, and the proximal cohort costs two sequential rounds: one to obtain gradients at $x$, then one to return the shifted proximal points. The first estimator round is retained even when its correction is zero. Each epoch therefore costs exactly $h+3T$ rounds. Repeated indices reuse a single client reply, so the distinct-client cap is respected.

Each outer step performs $J$ inner epochs, warm-started from the previous outer primal point, to approximate the proximal point of $F$ at the outer predictor. The outer weight and dual rules use ρ in place of λ. There are $K$ steps per restart and $N$ restarts. The exact non-padding plan cost is

$$
NKJ(h+3T).
$$

[CappedProximalBudget](../Proofs/CappedProximalBudget.lean) proves that the public budget dominates this cost. `Template.execute` can pad the completed plan to the public budget with empty-contact rounds; these rounds are covered by the budget and leave the output unchanged. All tuning uses only public parameters; neither a stopping certificate nor the unknown minimizer is queried.

All cohort coordinates and all time blocks are independent uniform draws with replacement, implemented by the uniform law on the finite seed-function space. This is internal algorithm randomization with deterministic exact oracle replies, not an assumed stochastic gradient oracle. The proof factors the finite uniform expectations explicitly and then identifies them with the integral. It covers arbitrary oracle seed distributions because admissibility makes every reply pointwise independent of those seeds. It does not claim an extension to stochastic or inexact local replies.

## Technical contribution

For fixed predictor $x$ and gradient estimate $g$, let $u_i$ be the corrected local proximal points, $U=m^{-1}\sum_i u_i$, $V=m^{-1}\sum_i\|u_i-U\|^2$, and $z$ their sampled mean. Common-point centering at $U$ is an established S-DANE technique. The additional step here controls the objective at the actual sampled point $z$, which is correlated with the sampled clients:

$$
\mathbb E[F(z)-F(U)]\le
\frac1m\sum_i D_{f_i}(u_i,U)
+\frac{\delta\sqrt{s-1}+\tfrac32\sqrt m\delta}{s}V.
$$

The proof removes one sampled coordinate from the average before applying common-point average similarity. Reintroducing that coordinate costs only the derived worst-client Lipschitz bound √mδ divided by $s$. Negative proximal dispersion absorbs this error. Treating the sample-dependent point as independent, or bounding the true residual by δ√V, would be invalid.

The resulting expected proximal inequality retains the predictable estimator-error inner product until the independent gradient cohort cancels it. It supports acceleration within an epoch. The epoch has expected subproblem gap at most $q\|w-x_H^\star\|^2/16$, and contracts the initial subproblem gap by $1/8$. A second potential argument handles approximate outer proximal steps using distance-based warm starts, without a global smoothness constant. Each outer phase contracts the objective gap by $1/8$. See [Certificate](../Proofs/CappedProximalCertificate.lean), [Inner](../Proofs/CappedProximalInner.lean), and [Outer](../Proofs/CappedProximalOuter.lean).

## Closest results and improvement regime

The comparisons use charged rounds and the same objective-gap accuracy. They do not identify local proximal work with a gradient call.

- **Wang, arXiv:2610.33835v1, 24 October 2026**, [Theorem 14, Corollary 15, and Appendix E](https://arxiv.org/html/2610.33835v1): Catalyst VM-SVRS gives $\widetilde O(m/s+(\sqrt{m/s}+m^{3/4}/s)\sqrt{\delta/\mu})$ on quadratic, individually strongly convex clients. The present theorem removes those two restrictions while replacing the $\sqrt{m/s}$ coefficient by a constant. This source is a preprint, not an accepted conference paper. Its cap-dependent lower bounds apply to zero-respecting local algorithms and specified parameter regimes, not unrestricted messages.
- **Lin, Han, Ye and Zhang, NeurIPS 2023**, [SVRS/AccSVRS and supplemental Appendix D](https://proceedings.neurips.cc/paper_files/paper/2023/hash/05e552739c2629f3324c1063a382b4bd-Abstract-Conference.html): average similarity and mean strong convexity are already established. The fixed-master Bregman telescope does not permit simply resampling a master: the next iterate depends on that master. This paper also permits nonconvex components in settings outside our convex-client class. Our theorem does not subsume all its guarantees.
- **Jiang, Rodomanov and Stich, NeurIPS 2024**, [S-DANE, Lemmas 15–16 and partial-participation Theorem 25](https://proceedings.neurips.cc/paper_files/paper/2024/hash/b4b75092bb44a14815be33d052aa47f5-Abstract-Conference.html): common-average centering, proximal variance absorption, and accelerated proximal methods are prior techniques. Batching full-participation acceleration under a strict cap gives a coefficient $m/s$; its partial-participation theorem uses additional gradient-dissimilarity control. Neither supplies the sampled-primal certificate above under only the present average similarity.
- **Jiang, Rodomanov and Stich, ICLR 2026**, [arXiv:2512.05327v1, Appendix A](https://arxiv.org/html/2512.05327v1): the SABER reconstruction already separates an estimator cohort from an independent proximal client. That separation is not claimed as new. Its comparison uses uniform worst-client similarity; substituting the derived √mδ bound loses the targeted participation dependence.
- **Condat, Gasanov and Richtárik**, [arXiv:2505.12409v1, Assumption 3.2 and Corollary 3.4](https://arxiv.org/html/2505.12409v1): the different-client-point similarity condition is stronger. Even identical high-curvature clients can have zero common-point δ here and a large different-point parameter there. Its rate cannot be transferred by renaming that parameter.

The substantive improvement is at intermediate caps. For $s\asymp m^{3/4}$, the prior capped VM-SVRS coefficient is of order $m^{1/8}$, while ours is constant. Taking δ/μ sufficiently larger than $m^{1/2}$ makes the $m/s$ initialization term lower order; logarithms and universal constants must also be accounted for in a numerical comparison. For small caps or full participation, known bounds already have the same polynomial dependence. We do not claim universal superiority, optimal logarithms, or an unrestricted-oracle lower bound. The result closes the identified intermediate-cap polynomial gap relative to the cited restricted lower-bound comparisons.

A direct composition of the previous nonaccelerated virtual-master epoch with outer regularization retains the $\sqrt{m/s}$ term. The contribution beyond that reduction is the sampled-primal certificate and the resulting accelerated epoch, rather than formalization or the introduction of a new name for the setup.

## Scope, examples, and literature limits

A concrete nonlinear family is
$f_i(x)=H(x)+\tfrac12\langle x,B_i x\rangle+\langle b_i,x\rangle$, with positive semidefinite $B_i$, strongly convex mean, and a shared differentiable convex $H$. Dense quartic or logistic terms in $H$ couple coordinates; common curvature may be unbounded. The squared similarity constant δ² can be taken as the operator norm of $m^{-1}\sum_i(B_i-\bar B)^2$, independently of common curvature. Individual clients can have flat directions. The theorem also covers nonquadratic client differences satisfying the displayed similarity inequality; no decomposition is required in the specification.

The assumptions come from established Hessian-similar federated optimization and strict participation accounting. No extra structural condition was introduced to complete the proof. Exact local solution is a substantive oracle assumption: this result provides neither a local computation bound nor robustness to inexact solutions. Parameters are known, and the algorithm is not adaptive to unknown δ or μ.

Literature screening covered the publicly available 2025–2026 ICML, ICLR and NeurIPS editions and approximately 2024–October 2026 arXiv work, with older foundational comparisons above. It was targeted, not an exhaustive certification of all optimization papers. The strongest capped baseline and cost-aware preprint metadata were rechecked on 30 October 2026 UTC and still list only v1. The original SABER OpenReview pages were inaccessible behind access challenges; the accessible primary reconstruction in the cost-aware paper was inspected instead. This access limitation prevents claiming a complete independent audit of every original SABER statement. No conference acceptance claim is made for unreviewed preprints.
