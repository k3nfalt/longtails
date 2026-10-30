# Stochastic optimization of nonsmooth hidden-convex objectives

The [theorem](NonsmoothHiddenConvexStochastic.lean) establishes an expected objective-gap guarantee with an explicit oracle budget for the [setup](../Setups/NonsmoothHiddenConvex.lean). The [algorithm](../Algorithms/NonsmoothHiddenAveraging.lean) uses stochastic subgradients, Euclidean projections onto local balls, and restarts to its initial point. It does not know or evaluate the hidden change of coordinates.

## Problem and information

Let $E$ be any finite-dimensional real inner-product space. The objective is $F=H\circ c$, where $H:E\to\mathbb R$ is convex and finite everywhere and $c:E\to E$ is a continuously differentiable homeomorphism. For all $x,y$,
\[
 \mu\|x-y\|\le\|c(x)-c(y)\|\le L_c\|x-y\|,
 \qquad \|J_c(x)-J_c(y)\|\le L_J\|x-y\|.
\]
Here $0<\mu\le L_c$, $L_J\ge0$. Neither $F$ nor $H$ must be differentiable. The map, its derivative, the hidden convex function, the selected mean subgradient, and a minimizer are instance data unavailable to the algorithm.

A jointly measurable oracle $g(x,\omega)$ has integrable replies and squared norms, mean $p(x)$, and second moment at most $G^2$, uniformly in $x$. The mean is a genuine pulled convex subgradient: there is $s_x\in\partial H(c(x))$ with
$\langle p(x),v\rangle=\langle s_x,J_c(x)v\rangle$ for every $v$. The setup states these supporting inequalities and pairings explicitly. Samples satisfy the repository's abstract IID specification under a supplied probability law; the proof derives the product laws internally. Sample spaces need not be finite, and sample norms need not be bounded almost surely.

The initial point is zero. A known $R>0$ satisfies the boundary barrier
\[
 \|y\|=R\quad\Longrightarrow\quad F(0)\le F(y).
\]
Global attainment is assumed. Existence of a minimizer $x^\star$ with $\|x^\star\|\le R$ is proved, not assumed separately. The barrier expresses localization of the initial strict sublevel; it does not assert that the entire closed sublevel is bounded. Hidden line segments show that every exterior point has value at least $F(0)$, so resetting exterior points to zero never increases the objective. This condition is weaker than BCKP's two-sphere ordering assumption A3, rather than a verbatim assumption from that paper.

The public numerical data are $\mu,L_c,L_J,G,R,\varepsilon$, with $\mu,G,R,\varepsilon>0$, $L_c\ge\mu$, and $L_J\ge0$. No initial objective gap, function value, hidden-coordinate query, inverse-map query, or Jacobian query is supplied. The setup imposes no artificial restriction on competing algorithms.

## Algorithm and guarantee

Write
\[
 \kappa=L_c/\mu,\quad \theta=L_JR/\mu,\quad S=1+64\theta,
 \quad A=\kappa S,\quad B=G^2\kappa^3R^2S/\varepsilon^2.
\]
Define
\[
 r=R/S,\quad t=(2A)^{-1},\quad
 \Delta_0=GR(1+\theta),\quad v=2G\kappa R/\varepsilon,
\]
\[
 N=\left\lceil 4194304(1+v)^2\log^2(16(1+v))\right\rceil,
 \quad K=\left\lceil2A\log(2+2\Delta_0/\varepsilon)\right\rceil,
 \quad D=G\sqrt N/r.
\]
At each epoch center $b$, initialize $x_0=z_1=b$. For $j=1,\ldots,N$, query
\[
 x_j=\frac{j-1}{j}x_{j-1}+\frac1jz_j,
 \qquad z_{j+1}=\operatorname{Proj}_{\overline B(b,2r)}(z_j-g_j/D).
\]
The next center is $x_N$ if $\|x_N\|<R$, and zero otherwise. Return the center after $K$ epochs. The implementation discards the last dual update in each epoch because it cannot affect $x_N$; it still charges that oracle call. All query points lie within distance $3R$ of zero. The state freezes after the last epoch, making any padding calls harmless but still counted.

The returned point is measurable, its objective gap is integrable, and
\[
 \mathbb E[F(\widehat x)-F(x^\star)]\le\varepsilon.
\]
The public budget, expanded directly in setup parameters in Lean, is
\[
 \left\lceil10^{10}(A+B)\log^3\!\bigl(10^{10}(2+A+B)\bigr)\right\rceil.
\]
The proof establishes $KN$ below this budget and connects the result to the framework's actual `execute`. Thus the rate is
\[
 \widetilde O\!\left((1+L_JR/\mu)
   \left[L_c/\mu+G^2L_c^3R^2/(\mu^3\varepsilon^2)\right]\right).
\]
The displayed exact bound, not the suppressed-log notation, is formalized. Constants are conservative. The result does not claim optimal logarithms, geometry dependence, or universal superiority when $L_J=0$.

## New mechanism

The substantive step is a local nonsmooth stochastic solver with an arbitrary comparator $u\in\overline B(b,r)$, without assuming that $u$ minimizes $F$. Put $M=L_J/\mu$ and
\[
 q(x,u)=J_c(x)^{-1}(c(u)-c(x))-(u-x).
\]
This is a proof device, never evaluated by the algorithm. Taylor control gives $\|q(x,u)\|\le M\|u-x\|^2$. Applying hidden convex support at the current average to both the comparator and the previous average produces
\[
 j(F(x_j)-F(u))-(j-1)(F(x_{j-1})-F(u))
 \le\langle p(x_j),z_j-u-q(x_j,u)\rangle
 -(j-1)\langle p(x_j),q(x_j,x_{j-1})\rangle.
\]
The corrected energy is
\[
 j(F(x_j)-F(u))+\tfrac D2\|z_{j+1}-u\|^2
       -D\langle z_{j+1}-u,q(x_j,u)\rangle.
\]
The comparator's projection margin absorbs the normal term. Averaging gives movement $O(r/j)$; the previous-average remainder and the drift of the correction therefore accumulate harmonically. Crucially, all coefficients multiplying the current oracle noise are predictable. Second moments suffice to integrate the energy inequality, even though the comparator gap can be negative.

For $64Mr\le1$, the proved local guarantee is
\[
 \mathbb E[F(x_N)-F(u)]\le
       16Gr(1+\log(N+1))/\sqrt N.
\]
Choose the inaccessible proof comparator $u=c^{-1}((1-t)c(b)+tc(x^\star))$. It lies within $r$ of $b$ and reduces the comparator gap by $1-t$. The local error is at most $t\varepsilon/2$, yielding epoch contraction around an $\varepsilon/2$ floor. The barrier then makes the restart valid. Globalization and the averaging architecture themselves are established ideas; the new ingredient is their nonsmooth hidden-support energy analysis giving the stochastic square-root local rate without compatible hidden geometry.

## Closest primary results and reductions

Literature assessment uses sources available on **29 October 2026 UTC**, following independent surveys of ICML 2026/2025 (PMLR 306/267), ICLR 2026/2025, and NeurIPS 2025/2024 proceedings, plus approximately two years of arXiv submissions and revisions. NeurIPS 2026 public listings and associated preprints were checked separately; its proceedings were not yet available. The survey distinguishes accepted proceedings from submissions and preprints. Publication status and theorem scopes were checked separately from search-result descriptions.

* **Bhaskara–Cutkosky–Kumar–Purohit, ICLR 2025**, [official proceedings paper](https://proceedings.iclr.cc/paper_files/paper/2025/file/c40fc068ed2b4ad43bff4f3f3206691e-Paper-Conference.pdf), Section 5, A3, Lemmas 5.1–5.3, Theorem 5.4, and Appendix C. Their generic nonsmooth hidden-convex bound has an $\varepsilon^{-3}$ leading exponent. Their averaging and epoch architecture are prior work. The present result changes this to $\widetilde O(\varepsilon^{-2})$ at fixed geometry, weakens the localization assumption, and permits second-moment rather than almost-sure oracle bounds. Their common constant $H$ bounds both hidden-function Lipschitzness and oracle norms. Our selected subgradients imply that the hidden function is $G/\mu$-Lipschitz. Normalizing the hidden map by $\mu$, the bounded-oracle overlap has $\alpha=1/\kappa,\beta=1,\rho=L_J/\mu,H=G$. Their leading expression then scales as $G^3R^4\rho\kappa^4/\varepsilon^3$. Appendix C additionally uses $R\rho\kappa\ge1$; using a larger declared $\rho$ if necessary and retaining startup terms avoids an invalid vanishing bound at $L_J=0$. This normalization is a derived comparison, not a claim of a uniform prefactor advantage.
* **Fatkhullin–He–Hu**, [arXiv:2401.00108v2](https://arxiv.org/abs/2401.00108v2), revised 9 November 2024, subsequently *SIAM Journal on Optimization* 35(4), 2025, Section 4 (A.1–A.2) and Section 4.1 (Theorem 2 and Corollary 1). Their nonsmooth guarantee controls a Moreau-envelope/proximal-point accuracy; conversion to the actual iterate requires additional accounting. Their hidden-convex framework includes less regular transformations and constrained problems beyond the present theorem. This result does not replace those broader regimes. The analyzed arXiv version is v2.
* **Fatkhullin–He–Lan–Wolf**, [arXiv:2511.10626v1](https://arxiv.org/abs/2511.10626v1), 13 November 2025, Sections 3 and Appendix B.2, Corollary 4. The nonsmooth subgradient implementation has $\varepsilon^{-3}$ complexity and uses deterministic subgradients and function values. It does not supply the claimed stochastic square-root rate. The analyzed source is the listed arXiv version; conference publication status was not independently confirmed.
* **Barakat et al.**, [arXiv:2605.26373v1](https://arxiv.org/abs/2605.26373v1), 25 May 2026, Assumption 1 and the hidden-convex online regret result. Square-root regret already gives an $\varepsilon^{-2}$ offline rate under Hessian compatibility, requiring the hidden metric $(J_cJ_c^*)^{-1}$ to be a Hessian, together with domain and regularity conditions. The present theorem does not require this compatibility. Their adversarial OGD lower bound is not an offline problem-class lower bound. The analyzed source is the listed arXiv version; conference publication status was not independently confirmed.
* **Chen–He–Hu–Ye**, [arXiv:2205.01774v3](https://arxiv.org/abs/2205.01774v3), revised 15 July 2024, the MSG method. An $\varepsilon^{-2}$ rate already exists for a separable monotone transformation model with transformation-derivative samples. That extra information and structure differ from arbitrary interacting unknown maps with a gradient-only oracle. Consequently this note does not claim the first $\varepsilon^{-2}$ result for every hidden-convex problem.

* **Wang–Tang**, [arXiv:2608.23178v1](https://arxiv.org/abs/2608.23178v1), 24 August 2026, Assumptions 1–2 and Theorem 1. Their convex-lifting proximal method obtains $O(d\varepsilon^{-3}\log(1/(\varepsilon\delta)))$ function evaluations for high-probability objective-gap accuracy. It admits auxiliary lifting variables and open nonconvex domains, including a state-feedback control application outside the present global-diffeomorphism setup. Its oracle and scope differ, and its theorem does not give the present stochastic-subgradient $\varepsilon^{-2}$ rate. The analyzed source is the listed arXiv version.

Batching or clipping the oracle does not remove the nonlinear deterministic distortion in the generic $\varepsilon^{-3}$ analyses. Directly optimizing or smoothing $H$ would require unavailable hidden coordinates and transformed subgradients. Euclidean smoothing of $F$ need not preserve its hidden-convex representation. The existing smooth local accelerated theorem in this repository requires objective smoothness, which this nonsmooth class lacks; its globalization alone was not selected as a contribution. Enumerating a covering of local regions can incur exponential dimension cost and is not the polynomial-geometry guarantee proved here. The Hessian-compatible online-to-batch and separable-transform reductions above cover meaningful subclasses but not the nonlinear family below.

## Nonlinear instances and limitations

For every $d\ge2$, take
\[
 c(x)=(x_1,x_2-a\sin x_1,x_3,\ldots,x_d)-b e_2,
 \qquad H(u)=\psi(u_1)+\sum_{j=2}^d|u_j|,
\]
where $b\ne0$ and
$\psi(t)=\tfrac12t\arctan t-\tfrac12\log(1+t^2)$.
One may use $\mu=(1+|a|)^{-1},L_c=1+|a|,L_J=|a|$.
Here $\psi''(t)=t^2/(1+t^2)^2$, $|\psi'|\le\pi/4$, and
$(\|u\|-1)/8\le H(u)\le\sqrt d\|u\|$.
The minimizer is $(0,b,0,\ldots,0)$, while $F(0)=|b|>0$. The barrier holds whenever $\mu R\ge1+9|b|$. A measurable pulled subgradient has norm at most $L_c\sqrt d$; adding centered independent noise with second moment $\sigma^2$ gives $G^2=L_c^2d+\sigma^2$. This makes the dimension dependence through the oracle bound explicit.

For $a=1$, there is negative curvature near $x_1=\pi/2,x_2<b+a$. Along the curved valley $(t,b+a\sin t,0,\ldots,0)$, the objective gap is $\psi(t)\sim t^4/12$; neither sharpness, quadratic growth, nor a PL inequality holds. The hidden metric in the first two coordinates is
\[
 \begin{pmatrix}1+a^2\cos^2u&a\cos u\\a\cos u&1\end{pmatrix}.
\]
Its mixed derivatives violate Hessian integrability when $a\ne0$. Dense orthogonal conjugation preserves these properties while mixing all coordinates. Thus the result is not restricted to scalar, quadratic, separable, or Hessian-compatible geometry. These illustrative calculations are mathematical examples, not additional assumptions in the Lean setup.

The exponent $\varepsilon^{-2}$ is consistent with stochastic convex oracle lower bounds, including the identity-map subclass; no optimality claim is made for the full geometric factors or logarithms. Global bi-Lipschitz regularity, global attainment, a known barrier radius, and uniform second moments remain substantive restrictions. Constrained domains, nonsmooth coordinate maps, Markov sampling, high-probability accuracy, and oracle models with only weaker moments are outside this theorem. A failure to find a stronger generic theorem is not by itself evidence of novelty: the claim rests on the explicit theorem and oracle comparisons above, subject to the limits of the recorded literature coverage.
