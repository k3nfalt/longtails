# Hysteretic Hessian transport with affine heavy-tailed noise

The [main theorem](HystereticAffineHessianTransport.lean) gives a new parameter-dependent oracle bound for expected first-order stationarity using stochastic Hessian-vector products. It reuses the full [GeneralizedAffineHessianVector specification](../Setups/GeneralizedAffineHessianVector.lean). The improvement is over both RanSOM's applicable generalized-smooth analysis and global-sublevel localization, in a joint accuracy/initial-gap regime described below. Recovering the mixed-tail accuracy exponent at a fixed initial gap, clipping Hessian products, and formalizing those techniques are not the novelty claims.

## Problem, oracle, and output

The objective is an arbitrary finite-dimensional, lower-bounded nonlinear function with continuously differentiable gradient and

\[
\|\nabla^2 f(x)\|\le L_0+L_1\|\nabla f(x)\|,\qquad f(x_0)-\inf f\le\Delta.
\]

More precisely, the specification supplies a finite lower bound whose gap at the initial point is at most Δ; the algorithm is not given its value. Gradient replies are unbiased, with central p-th moment bounded by

\[
\mathbb E\|G(x)-\nabla f(x)\|^p\le\sigma_g^p+\alpha_g^p\|\nabla f(x)\|^p.
\]

A directional Hessian reply is unbiased for \(\nabla^2 f(x)v\), with

\[
\mathbb E\|H(x,v)-\nabla^2 f(x)v\|^q
\le(\sigma_h^q+\alpha_h^q\|\nabla f(x)\|^q)\|v\|^q,
\qquad 1<p,q\le2.
\]

All curvature/noise bounds and Δ are nonnegative; ε is positive. Joint measurability, vector integrability, and central-moment integrability are explicit. The sampling law is abstract IID; the proof derives the necessary product-law representation. There is no finite-sample-space restriction, bounded-domain assumption, Hessian-Lipschitz condition, or convexity assumption. These are the generalized curvature and affine moment conditions of [RanSOM v3, Assumptions 4.1, 4.2, and 4.4](https://arxiv.org/html/2602.06824v3), already captured by the reused specification. No additional structural assumption is imposed.

The [algorithm](../Algorithms/HystereticHessianTransport.lean) knows these bounds, p, q, ε, Δ, and the initial point. It receives only fresh gradient or directional Hessian replies. It does not query objective values, exact gradients, full Hessians, or reusable sample functions. The two estimators need not be derivatives of the same sample loss; directional replies need not arise from a sampled linear operator. Each vector reply costs one call. This is an oracle bound, not an arithmetic-cost bound. No artificial algorithm-family restriction is used.

The output is the point at the algorithm's estimator-based stopping event, with fallback to \(x_0\) if it aborts or exhausts its allocation. It is neither an average nor an unobservable minimum-gradient iterate. The formal guarantee is measurability and integrability of this output criterion and

\[
\int \|\nabla f(X(\omega))\|\,dP_{\rm execution}(\omega)\le\varepsilon,
\]

where the execution law is the product of the algorithm's internal seed law and the specified IID oracle law. The theorem invokes the actual `execute` operation. Second-order information is essential to its transport estimator; the accuracy criterion is first-order stationarity, not second-order stationarity or finding a local minimum.

## Explicit guarantee

For presentation only, write

\[
\begin{aligned}
\beta&=p/(p-1), & A&=1+\alpha_g, & S&=1+\sigma_g/\varepsilon+\alpha_g,\\
U&=\varepsilon+\sigma_g/A, & H&=L_0+\sigma_h+(L_1+\alpha_h)U, & D&=\Delta H/\varepsilon^2,\\
R&=(\sqrt{L_0\Delta}+L_1\Delta+\varepsilon+\sigma_g)/\varepsilon,
&Y&=2+S+D+R.
\end{aligned}
\]

The total oracle budget is

\[
\boxed{N=\left\lceil
2^{32\beta+16q/(q-1)+64}(\beta+1)(1+\log Y)
\left[S^\beta+D\left(S^{\beta/q}+A^2S^{\beta-2}\right)\right]
\right\rceil.}
\]

The public Lean definition expands this formula directly in the setup parameters on one line. It counts initialization, every robust-estimator group, every pilot, all gradient refreshes, all Hessian-vector batches, and padding. The execution freezes its state after the analyzed allocation; additional calls up to N remain charged. The guarantee includes zero curvature and zero noise, but makes no sharpness claim in those cases. Constants grow as p or q approaches one and are not intended as practical tuning recommendations.

Ignoring the displayed logarithm and constants depending on fixed p,q, the rate is

\[
S^\beta+\frac{\Delta H}{\varepsilon^2}
\left(S^{\beta/q}+A^2S^{\beta-2}\right).
\]

The initialization term and the second term inside the parentheses are essential. Dropping either would overstate the result.

## New mechanism and why localization alone is insufficient

The algorithm uses internal accuracy \(e=\varepsilon/2\) and internal scales \(U_e=e+\sigma_g/A\), \(S_e=1+\sigma_g/e+\alpha_g\), and \(H_e=L_0+\sigma_h+(L_1+\alpha_h)U_e\). The epoch length is the integer floor of

\[
\min\{S_e^{\beta(q-1)/q},(S_e/A)^\beta\}.
\]

The remaining batch sizes, clipping threshold, step sizes, guard, and finite allocation are explicit in `tunedConfig`; none is existentially tuned in the theorem.

Fresh medoid-of-means pilots distinguish coarse and fine modes. A pilot norm at most \(U_e/4\) enters fine mode; a pilot norm at least \(3U_e\) exits it. Coarse steps use the pilot direction and a generalized-smooth normalized step. Fine steps use a recursively tracked gradient, refreshed with a robust gradient batch and transported with clipped Hessian-vector replies at fresh uniform points on the actual step segment. A separate global pilot threshold aborts unsafe trajectories.

The substantive step is an amortized bound on repeated returns to high-gradient regions. On the simultaneous estimator-good event, entry implies true gradient norm at most \(U_e/2\), exit implies norm at least \(2U_e\), and every fine start has norm at most \(4U_e\). The potential

\[
\mathbf1_{\rm fine}\max\{0,\|\nabla f(x)\|^2-U_e^2/4\}
\]

starts at zero on entry. Fine steps increase it by at most \(24(L_0+4L_1U_e)\) times their objective decrease; each exit spends at least \(15U_e^2/4\). Gradient refreshes preserve the potential and do not require the current gradient to be as small as at entry. Consequently the number of expensive mode returns is charged to the same finite objective decrease as the optimization steps. General nonlinear trajectories can leave a small-gradient region repeatedly; a one-time localization argument cannot assume they stay there.

This charge permits gradient refresh and HVP tuning at \(U_e\), rather than at the global sublevel scale \(\sqrt{L_0\Delta}+L_1\Delta\). Balancing the epoch length pays both transport cost and relative-pilot cost, giving exactly the two displayed rate terms. The formal ledger also relates these events to completed raw oracle blocks and proves that the finite allocation suffices.

Expected accuracy requires control of bad trajectories as well. The global guard gives an unconditional second-moment estimate via an anchor process, bounded by \((2+4K)M^2\), with \(M=16(\sqrt{L_0\Delta}+L_1\Delta+U_e)\) and K the logical-block bound. Adaptive block certificates and stopped transport concentration supply failure probability at most \(e^2/((2+4K)M^2)\). A Young-inequality argument then yields expected gradient norm at most \(2e\), without assuming objective descent on bad events. Guard radius and horizon enter the logarithm rather than the polynomial batch scale. Robust means, clipping, random-segment transport, and high-probability-to-expectation conversion are established ingredients; the repeated-mode charge and its integration with full affine noise are the contribution.

## Closest comparisons and improvement regime

* [RanSOM, arXiv:2602.06824v3, §4.5, Lemma B.24 equations (54)–(56), and Remark B.26](https://arxiv.org/html/2602.06824v3), revised October 9, 2026, treats the same generalized curvature and affine moment model. For q>p in its generalized branch, the relevant sufficient bound yields accuracy exponent \(\beta+1\), with linear dependence on Δ achievable by explicit tuning. Its path-residual step/momentum coupling survives gradient minibatching. Batching reduces the gradient-noise term but does not remove that unbatched path term; optimizing the displayed bound retains the \(\varepsilon^{-(\beta+1)}\) dependence. This is a limitation of that analysis, not a lower bound on RanSOM or the problem. The paper is a preprint; no conference acceptance is asserted here.
* The existing [GuardedAffineHessianTransport theorem](GuardedAffineHessianTransport.lean) already recovers the mixed-tail exponent for this full setup. Granting routine improvements to its validation logarithms, its polynomial bound is \(S_R^\beta+\Delta H_R\varepsilon^{-2}S_R^{\beta/q}G_R^\beta\), with \(R_0=\sqrt{L_0\Delta}+L_1\Delta+\varepsilon\), \(S_R=1+(\sigma_g+\alpha_gR_0)/\varepsilon\), \(H_R=L_0+\sigma_h+(L_1+\alpha_h)R_0+\varepsilon/R_0\), and \(G_R=1+\sigma_g/R_0+\alpha_g\). This is the direct global-localization baseline. The new claim is the improved dependence on gradient scale and initial gap, not an accuracy exponent absent from that theorem.
* [Fradin et al., AISTATS 2026](https://proceedings.mlr.press/v300/fradin26a.html), [extended version 2512.18713v2, Assumptions 2.2–2.7, Theorem 5.1 and Appendix F](https://arxiv.org/html/2512.18713v2), already use mixed-tail HVP transport and clipping. Their HVP theorem assumes globally Lipschitz gradient and Hessian and uniform oracle moments; their first-order alternatives require global weak-average smoothness or gradient-difference access. These do not cover the present full affine/generalized model. The second-order direction oracle here does not grant shared-sample gradient differences.
* [Reisizadeh et al., 2303.00883v2, Theorem 3 and Appendix B](https://arxiv.org/html/2303.00883v2), provides generalized-SPIDER normalization. Robust refresh and integrated HVP differences already recover relevant q=2 uniform-gradient-noise special cases. Those special cases and normalization itself are not claimed new.
* [Localize, Restart, Accelerate, 2609.06555v1, Theorem 1 and Appendix I](https://arxiv.org/html/2609.06555v1), and [Acceleration Survives Heavy Tails and Generalized Smoothness, 2610.23301v2, Theorem 1](https://arxiv.org/html/2610.23301v2), are relevant localization precedents. They use convexity and stronger sample structure or uniform gradient noise, and their certificates concern function gap/distance. A small gradient in a nonconvex problem does not supply those certificates. These are cited as preprints, not accepted conference papers.

For a concrete strict comparison, fix p,q with q>p, fix positive \(L_1,\sigma_g,\alpha_g\) and the remaining nondegenerate curvature/noise parameters, and let \(\Delta=\varepsilon^{-d}\), d>0. Put \(m_*=\max\{\beta,2+\beta/q\}\). Up to logarithms, the new accuracy exponent is \(d+m_*\); the two applicable baselines above have exponents \(d+\beta+1\) and \((1+d)m_*\). Since \(m_*<\beta+1\) and \(m_*>1\), the new exponent is strictly smaller than both. For p=3/2, q=7/4, d=1, it is 33/7 versus 5 for RanSOM and 52/7 for global localization. All counts include initialization and use the same expected-norm accuracy criterion.

There is no claim of a new fixed-gap accuracy exponent, a state-of-the-art gain from increasing Δ with ε fixed alone, a pure-multiplicative-noise advantage when σg=0, universal dominance, or minimax optimality. The theorem also covers q≤p, without a corresponding strict-improvement claim. It does not establish a lower bound against first-order algorithms. Known parameters, IID unbiased samples, and the stated oracle costs remain limitations; no adaptivity improvement is claimed.

## Nonlinear instances and scope

For every dimension at least two, take

\[
f(x)=\exp(x_1)+\frac\mu2\|x\|^2+c\sin(x_1+x_2),\qquad c>\mu>0.
\]

This lower-bounded objective couples coordinates and has negative curvature at points with \(x_1=x_2=\pi/4\). Its Hessian is unbounded. If \(x_1<0\), then \(\exp(x_1)\le1\); if \(x_1\ge0\), its first gradient coordinate gives \(\exp(x_1)\le\|\nabla f(x)\|+c\). Hence \(L_0=1+\mu+3c\), \(L_1=1\) suffice. Varying the initial point varies Δ without changing this objective class. This is not a scalar, quadratic, or separable-only theorem.

For an oracle mechanism, consider sample losses \((1+Z_q)f(x)+Z_p\langle u,x\rangle\), with a unit vector u and independent centered variables with finite p- and q-th moments. In the improvement regime q>p, \(Z_p\) may have infinite q-th moment. The two-term moment inequality yields the stated affine gradient bounds; multiplying the Hessian bound by \(Z_q\) yields affine directional q-moment bounds. Thus better HVP tails need not imply better gradient tails. These examples explain applicability; they are not extra formal assumptions or separate formalized results. Dimension does not occur explicitly in the bound, although supplied noise and curvature constants can depend on dimension.

The literature assessment used current UTC November 4, 2026, independently surveying publicly available ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025/2026 listings, recent arXiv submissions/revisions, and foundational citations. Relevant primary statements and the latest versions above were checked; official AISTATS proceedings establish the status cited above. Some conference/OpenReview pages failed through the browser route; official downloads and alternate primary PDFs were used where available. Title searches are not exhaustive theorem coverage. The novelty claim rests on the explicit comparisons and reduction checks, not on the absence of a search hit.

The formal proof is organized in the [accuracy](../Proofs/HystereticHessianAccuracy.lean), [budget](../Proofs/HystereticHessianBudget.lean), [event ledger](../Proofs/HystereticHessianLedger.lean), and related transport, concentration, sampling, and execution modules. It preserves the original objective/oracle specification and proves the complete actual execution guarantee without new axioms or an assumed convergence condition.
