# Convex optimization with one known noisy direction

The [main theorem](SpikedSubGaussianSoftCutConvex.lean), `SpikedSubGaussianSoftCutConvex.result`, proves a gradient-only oracle-complexity bound for general Lipschitz convex objectives with a known one-spike directional subGaussian noise envelope. The result improves the applicable dimension dependence in an anisotropic, positive-background-noise regime. It does not solve the general covariance-trace or finite-variance problem.

## Formal statement and scope

Write $d=m+1\geq1$, $\tau=v_{\rm top}+(d-1)v_{\rm rest}$, and
$$
Q=1+\log\bigl(16d(1+GR/\varepsilon)\bigr).
$$
For $G,R,\varepsilon>0$ and $0\leq v_{\rm rest}\leq v_{\rm top}$, the algorithm uses exactly the public padded budget
$$
B=\left\lceil 2^{51}\left(d+\frac{\tau R^2}{\varepsilon^2}\right)Q^5\right\rceil
$$
and returns a measurable point $\widehat x$ satisfying
$$
\Pr\{f(\widehat x)-f(x_\star)>\varepsilon\}\leq\tfrac13.
$$
The [setup](../Setups/SpikedSubGaussianConvex.lean) states all of the following:

- $f:\mathbb R^d\to\mathbb R$ is globally convex and $G$-Lipschitz. A **global** minimizer $x_\star$ exists with $\|x_\star\|\leq R$. Neither this minimizer nor its value is given to the algorithm.
- There is a fixed subgradient selection $v(x)\in\partial f(x)$. The oracle $g(x,\omega)$ is jointly measurable, integrable, and unbiased: $\int g(x,\omega)\,dp(\omega)=v(x)$.
- For every query $x$, direction $u$, and real $t$, the directional exponential is integrable and
  $$
  \mathbb E_p e^{t\langle g(x,\omega)-v(x),u\rangle}
  \leq \exp\!\left(\frac{t^2}{2}
  [v_{\rm rest}\|u\|^2+(v_{\rm top}-v_{\rm rest})u_0^2]\right).
  $$
- Samples are fresh IID under an arbitrary probability law with the specified marginals and independence, using the repository's existing IID structure. A product representation is derived internally; the specification does not restrict users to a prescribed product probability space.

The distinguished direction is coordinate zero; a known orthogonal change of coordinates gives the interpretation for any known unit direction. The parameters, including the upper envelope and direction, are public. No values, sample replay, separate component oracle, or realized noise are available. Coordinate independence, Gaussianity, additive noise, and query-independent error distributions are **not** assumed. The matrix in the exponential bound is an upper proxy, not an assertion about the actual covariance, which can be smaller and query-dependent.

The global minimizer assumption matters: inner sections use the cylinder $[-R,R]\times B_{d-1}(R)$, and the output need not lie in the radius-$R$ Euclidean ball. This is not a theorem for an arbitrary constrained minimizer on that ball. No smoothness, strong convexity, separability, or prescribed algorithm family is imposed by the setup. The public theorem constructs the [actual algorithm](../Algorithms/SpikedSoftCutMethod.lean) and connects it to `OracleTemplate.execute`.

## Motivation and assumptions

The established question is whether dimension-sensitive convex optimization can pay a total noise scale while retaining an additive deterministic dimension term. A known dominant measurement direction with bounded background is a meaningful intermediate noise model. Here the exceptional direction restricts the noise, not the coupling or curvature of the objective. A calibrated common scalar disturbance plus background vector noise is one mechanism that gives this envelope; the theorem does not establish that such calibration is available in a particular application.

Directional matrix-proxy subGaussian models have precedent in [Mollenhauer–Schillings, arXiv:2306.11404v2, Definition 2.1 and Remark 2.4](https://arxiv.org/html/2306.11404v2), and the finite-dimensional exponential condition is the form used in [Hsu–Kakade–Zhang, arXiv:1110.2842v1, Theorem 1](https://arxiv.org/pdf/1110.2842v1). The one-spike upper envelope is the structural specialization made here. We use our own predictable directional-MGF argument, not a claim that arbitrary operator-norm domination preserves a particular proxy orientation. The remaining objective, minimizer-radius, unbiasedness, and fresh-sampling assumptions are standard stochastic convex optimization assumptions; measurability and integrability make their probabilistic meaning explicit. An unused second-moment integrability assumption was removed from the setup.

For a concrete interacting nonlinear family, take
$$
f(x)=\sum_{j=1}^J a_j\log\cosh\langle b_j,x-x_\star\rangle,
\quad a_j>0,\quad \sum_j a_j\|b_j\|\leq G,
$$
where the dense, nonorthogonal vectors $b_j$ span $\mathbb R^d$, and $\|x_\star\|\leq R$. Its global minimizer is $x_\star$, its gradient is bounded, and its coordinates interact nonlinearly. Adding independent fresh Gaussian noise with covariance $\operatorname{diag}(v_{\rm top},v_{\rm rest},\ldots,v_{\rm rest})$ gives an admissible oracle. This example demonstrates genuine nonlinear scope, not a hardness claim. Both zero background and fully zero noise are also covered, but positive background is central to the improvement.

## Algorithm, output, and accounting

Each of $K=\lceil32Q\rceil$ epochs fixes the first coordinate $a$, runs the existing soft-cut centroid generator in the remaining $m$ coordinates, and constructs a weighted certificate from its noisy replies. The [inner algorithm](../Algorithms/SpikedSoftCut.lean) chooses coefficients on a fixed finite grid using only observed points and batch means. All support points are retained. The returned inner point is their normalized weighted average.

The tuning is explicit:
$$
\alpha=\varepsilon/8,\quad T=\lceil4096dQ^2\rceil,\quad
b=\max\{1,\lceil2^{31}v_{\rm rest}R^2Q/\varepsilon^2\rceil\},
$$
$$
n=\lceil256(1+8RG/\varepsilon+T)\rceil,\quad
N_k=\max\{1,\lceil8192K v_{\rm top}R^2(5/8)^{2k}/\varepsilon^2\rceil\}.
$$
After the $Tb$ inner calls, the algorithm makes fresh scalar-direction measurements at the selected supports, allocating $\lceil N_k w_i\rceil$ samples to weight $w_i$. This costs at most $N_k+T$ calls, including rounding; zero weights need no samples. It estimates the selected true first-coordinate subgradient mean, not a derivative obtained by substituting an approximate section minimizer.

The scalar interval radius is $r_k=R(5/8)^k$. The center moves by $3r_k/8$ opposite the estimated sign. The current weighted primal point is saved **before** the move. If the estimated slope has magnitude at most $\varepsilon/(2r_k)$, that saved point is frozen permanently; otherwise a later epoch replaces it. The final output is this saved point, not the shifted center and not a minimum selected using unavailable objective values.

Epochs are padded to deterministic lengths $Tb+N_k+T$; unused slots query zero. The [budget proof](../Proofs/SpikedSoftCutBudget.lean) bounds their sum by $B$, and execution pads further to $B$. If $GR\leq\varepsilon$, the output is zero, but execution still consumes the declared padded budget. Every fresh resample, rounding term, and dummy call is included. Exact centroid integration and finite-grid maximization are unrestricted internal computation: no efficient running-time or numerical implementation claim is made.

## New technical mechanism

The contribution is a noisy, data-selected **true-subgradient certificate** at the inner operator-noise scale. The soft-cut potential itself, minimax duality, and scalar search are not new.

Let $h_i=v_i+e_i$ be the inner batch estimates at points $x_i$. A same-ball mass argument for the soft-cut density gives, uniformly over $\|y\|\leq R$, a positive lower bound on
$$
\sum_i \max\{0,\langle h_i,y-x_i\rangle+\alpha/2\}.
$$
Minimax then supplies capped, unnormalized coefficients $0\leq\theta_i\leq1$ with a positive score
$$
\sum_i\theta_i(\alpha/2-\langle h_i,x_i\rangle)
 -R\Big\|\sum_i\theta_i h_i\Big\|.
$$
The predetermined grid approximates this score with loss at most $(\alpha/2+2RM)T/n$. The retained margin is crucial. Predictable-batch concentration gives, simultaneously for **all** coefficients, an operator bound and an intercept-square bound. Together they imply
$$
\left|\sum_i\theta_i\langle e_i,x_i-y\rangle\right|^2
\leq2T(R^2V+W).
$$
The margin pays this error even though the coefficients were chosen from the same noisy data. Normalization yields
$$
\sum_i w_i\langle v_i,x_i-y\rangle\leq\alpha/2=\varepsilon/16
\quad\text{for every }\|y\|\leq R.
$$
No lower bound on each normalized weight, validity of every noisy cut, or compression based on noisy gradients is assumed. The critical formal steps are [the minimax certificate](../Proofs/SoftCutCertificateMinimax.lean), [uniform density penalty](../Proofs/SoftCutCertificateDensity.lean), [selected true certificate](../Proofs/SpikedSoftCutCertificate.lean), and [actual epoch certificate](../Proofs/SpikedSoftCutEpochCertificate.lean).

Joint convex subgradient inequalities and Jensen turn this inner certificate into
$$
f(\bar x)-f(x_\star)+s(x_{\star,0}-a)\leq\varepsilon/16,
$$
where $s$ is the weighted **true** first-coordinate mean. Global minimality makes the first term nonnegative. Fresh stratified sampling estimates $s$ accurately enough to either certify the saved primal point or preserve minimizer containment after contraction. The invariant is frozen-success **or** unfrozen-containment; it never requires containment after freezing. The final unfrozen bound uses the last queried radius $r_{K-1}$, not the subsequent radius. The [freshness](../Proofs/SpikedSoftCutFreshness.lean), [outer probability](../Proofs/SpikedSoftCutOuterProbability.lean), and [convergence](../Proofs/SpikedSoftCutConvergence.lean) modules prove these statements for the actual adaptive transcript, then the [framework guarantee](../Proofs/SpikedSoftCutGuarantee.lean) establishes the public specification.

## Closest results and precise improvement

The strongest directly applicable directional-noise baseline is Marsden–O'Carroll–Sidford–Zhang, *Isotropic Noise in Stochastic and Quantum Convex Optimization*, [NeurIPS 2025 proceedings](https://proceedings.neurips.cc/paper_files/paper/2025/hash/a1c0bb652b64f99e26b5bcd60ed2c68f-Abstract-Conference.html), [arXiv:2510.20745v1, Definition 5 and Corollary 3](https://arxiv.org/html/2510.20745v1). Its directional scale is normalized by $\sqrt d$; direct application to this envelope gives $\widetilde O(d+d v_{\rm top}R^2/\varepsilon^2)$. Its nonsmooth coverage is already discussed, so nonsmoothness is not our novelty. Its Open Problem 1 motivates total-variance dependence, but our stronger tail and known-spike assumptions do not resolve that general question. Their point guarantees do not themselves provide the selected true-gradient certificate above.

The standard stochastic subgradient upper bound is $O((G^2+\tau)R^2/\varepsilon^2)$. Comparisons must use the better of this and the directional cutting-plane bound. Here is an explicit regime with positive background:
$$
G=R=1,\quad\varepsilon=d^{-1},\quad
v_{\rm top}=d^{-1},\quad v_{\rm rest}=d^{-3}.
$$
Our nonlogarithmic factor is $2d+1-1/d$, so the new bound is $O(d\log^5d)$. The displayed SGD envelope is $d^2+d+1-1/d$, and the direct directional baseline is $\widetilde O(d+d^2)$. This is an asymptotic improvement over applicable **upper bounds**, not a lower bound on those algorithms. The large constant makes this a complexity result, not a finite-size speed prediction. There is no universal superiority; at isotropic noise the leading order is already known, and no fixed-dimension, vanishing-accuracy logarithmic improvement is claimed.

Certificate precedents are important. [Gladin–Gasnikov–Dvurechensky, arXiv:2310.00523v1](https://arxiv.org/html/2310.00523v1), published in [JOTA 204 (2025)](https://doi.org/10.1007/s10957-024-02599-9), studies inexact-oracle accuracy certificates. Its valid inexact support information is stronger than our individual noisy records. [Gladin, arXiv:2610.11448v1, Appendix B.3](https://arxiv.org/html/2610.11448v1), explicitly distinguishes simultaneous probabilistic record validity from unbiasedness. [Grimmer–Wang, arXiv:2607.20875v1, Theorem 4.1](https://arxiv.org/html/2607.20875v1), converts uniform guarantees over exact consistent first-order transcripts into certificates; noisy slopes need not be jointly interpolable exact subgradients, and our oracle supplies no exact values. None of these conversions directly proves the stochastic margin transfer at the cost above. [Burns–Liang, arXiv:2604.18321v1](https://arxiv.org/abs/2604.18321) is further precedent for accelerated certificate constructions, not this directional-noise bound.

[Zhang et al., arXiv:2610.00260v2, Theorem 2.2](https://arxiv.org/html/2610.00260v2), gives sharp heavy-tail statistical rates but retains a deterministic $G/\sqrt T$ term. [Jiang–Pananjady, arXiv:2603.25657v1](https://arxiv.org/abs/2603.25657), uses smoothness and strong convexity for instance-optimal guarantees. Those results do not subsume this nonsmooth dimension-additive regime.

## Reduction checks and limitations

Replacing the envelope by $v_{\rm top}I$, adding isotropic noise, or padding dimensions loses the desired gain. Whitening followed by a Euclidean enclosing-ball bound also cannot improve the largest-eigenvalue radius product: for invertible $A$,
$$
R^2\|A^{-1}\|^2\lambda_{\max}(A^\top\Sigma A)
\geq R^2\lambda_{\max}(\Sigma).
$$
Batching each cut until it is uniformly accurate multiplies the total-noise cost by the number of cuts. A section point guarantee alone does not certify an outer slope for a coupled nonlinear objective. Value-based profile search, sample-average approximation with replay, and separate-component gradient sliding use information absent from this oracle. Scalar bracketing becomes routine only after obtaining the true-gradient certificate; that is the gap the new proof fills.

The theorem requires the known one-spike envelope. It does not learn an unknown direction, handle several uncontrolled spikes at the same rate, give an actual-covariance-adaptive result, or prove optimal logarithms. The one-spike restriction is a limitation of the present result, not a necessity theorem. The general objective class is preserved throughout the proof. Exact real arithmetic and enormous coefficient grids make computational efficiency an unresolved issue.

Both Researcher and independent Reviewer surveyed the two most recent publicly available ICML, ICLR, and NeurIPS editions and approximately two years of arXiv work, then followed older foundational results and subsequent certificate/noise papers. Targeted checks were refreshed through **2026-11-06 UTC**. Versions used above were checked explicitly, including 2610.00260v2 (the unversioned HTML had returned stale v1). The NeurIPS 2025 baseline's accepted status was verified through official proceedings; its OpenReview forum was browser-challenged, while its PDF and proceedings were accessible. Other recent arXiv sources are treated as preprints unless publication is identified above. Searches also checked the updated deterministic geometry result [Bullins et al., arXiv:2609.20687v2, November 3](https://arxiv.org/abs/2609.20687), whose oracle does not supply this noisy certificate. No directly subsuming theorem was found; this is a documented comparison, not a claim of exhaustive literature coverage or guaranteed conference acceptance.
