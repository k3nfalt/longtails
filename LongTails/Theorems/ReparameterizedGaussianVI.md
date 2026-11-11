# Linear condition-number complexity for first-order Gaussian black-box variational inference

**Lean files.** Theorem: [`ReparameterizedGaussianVI.lean`](ReparameterizedGaussianVI.lean) (`result : Convergence spec budget`).
Setup: [`../Setups/GaussianVariationalInference.lean`](../Setups/GaussianVariationalInference.lean).
Algorithm: [`../Algorithms/ReparameterizedProxSgd.lean`](../Algorithms/ReparameterizedProxSgd.lean).
Proofs: `../Proofs/GaussianVariational{Moments,Geometry,Expectation,Optimality,Variance,Step,Convergence,Guarantee}.lean`.

## Problem

Let $\pi\propto e^{-V}$ on $\mathbb R^d$ with $V$ differentiable, $\nabla V$ $L$-Lipschitz and $\mu$-strongly monotone
($\mu\|x-y\|^2\le\langle\nabla V(x)-\nabla V(y),x-y\rangle$), i.e. $\pi$ is $\mu$-strongly log-concave and $L$-log-smooth; $\kappa=L/\mu$.
Full-rank Gaussian variational inference with the Cholesky parameterization $q_\lambda=\mathcal N(m,CC^\top)$,
$\lambda=(m,C)$, $C$ lower triangular with positive diagonal, minimizes

$$F(\lambda)=\mathbb E_{\xi\sim\mathcal N(0,I_d)}\,V(m+C\xi)-\sum_{i}\log C_{ii}
\;=\;\mathrm{KL}(q_\lambda\,\|\,\pi)+\text{const}.$$

Oracle: the algorithm chooses points $x$ and receives $\nabla V(x)$ (pointwise first-order "black-box" access; no
Hessians, no closed-form Gaussian expectations). Cost = number of gradient evaluations. Accuracy:
expected excess reverse KL, $\mathbb E[F(\hat\lambda)]-F(\lambda^\star)\le\varepsilon$, where $\lambda^\star$ is a minimizer
of $F$ over the Cholesky family with $\|m_0-m^\star\|^2+\|C_0-C^\star\|_F^2\le R^2$. Since $F$ is $\mu$-strongly convex in
$\lambda$, this also gives $\mathbb E\|\hat\lambda-\lambda^\star\|^2\le 2\varepsilon/\mu$ and hence the same bound on
$\mathbb E\,W_2^2(q_{\hat\lambda},q^\star)$.

This is exactly the standard setting of
Domke ([ICML 2020](https://arxiv.org/abs/1901.08431)),
Domke–Gower–Garrigos ([NeurIPS 2023](https://arxiv.org/abs/2306.03638)),
Kim–Oh–Wu–Ma–Gardner ([NeurIPS 2023](https://arxiv.org/abs/2305.15349)),
Kim–Fu–Ma–Gardner–Campbell ([ICML 2026](https://arxiv.org/abs/2602.18718)) and
Park–Jang–Chen ([arXiv 2610.21020](https://arxiv.org/abs/2610.21020), Assumption 1.1); no assumption is added.
The Lean setup states exactly these hypotheses (gradient, Lipschitz gradient, strong monotonicity, existence of a
Cholesky minimizer at squared distance at most $R^2$) and the deterministic gradient oracle.

## Algorithm and output

Standard proximal SGD with the single-sample reparameterization gradient (the "SPGD + reparameterization" method of
Domke et al. and Kim et al. with $M=1$): at step $k$ draw $\xi_k\sim\mathcal N(0,I)$, query $x_k=m_k+C_k\xi_k$, receive
$g_k=\nabla V(x_k)$, and set

$$m_{k+1}=m_k-\eta_k g_k,\qquad C_{k+1}=\mathrm{prox}_{\eta_k(-\log\det)}\big(C_k-\eta_k\,\mathrm{low}(g_k\xi_k^\top)\big),$$

where the prox acts on the diagonal by $y\mapsto (y+\sqrt{y^2+4\eta})/2$. Step sizes $\eta_k=2/(\mu(k+a))$ with
$a=16L(2+\tau)/\mu+2$, $\tau=3d+8\log(48\kappa)$ (`stepSize`, `offset`, `tau` in the algorithm file). The output is the weighted average
$\hat\lambda_K=\sum_{j=1}^K(j+a-2)\lambda_j/\sum_{j=1}^K(j+a-2)$ (not the last iterate used by Kim et al.).
One gradient evaluation per iteration. The step sizes use $L,\mu,d$ (as in all compared works).

## Guarantee

With $K=\max\{1,\lceil(2+3d+8\log(48L/\mu))\,(26LR/\sqrt{\mu\varepsilon}+32dL/(\mu\varepsilon))\rceil\}$ gradient evaluations,
$\mathbb E[F(\hat\lambda_K)]-F^\star\le\varepsilon$. In order notation,

$$K=O\Big((d+\log\kappa)\Big(\sqrt{\kappa}\,\sqrt{LR^2/\varepsilon}+\frac{d\,\kappa}{\varepsilon}\Big)\Big).$$

## What is new and why

**Prior first-order guarantees are quadratic in $\kappa$.** Kim et al. (NeurIPS 2023, Lemma 3) prove convex expected
smoothness with constant $2L\kappa(d+k_\varphi)$ and (Lemma 4, after Domke 2019) variance at the optimum
$\sigma^2\le(d+k_\varphi)L^2(\|\bar z-m^\star\|^2+\|C^\star\|_F^2)$ ($\bar z$ the mode of $\pi$); Theorem 4 then gives
$T\ge\max\{O(\kappa^2(d+k_\varphi)R/\sqrt{\varepsilon_d})+8\sigma^2/(\mu^2\varepsilon_d),\,4\kappa^2(d+k_\varphi)\}$ for
$\mathbb E\|\lambda_T-\lambda^\star\|^2\le\varepsilon_d$ (Theorem 7: the constant-step analogue with an extra log).
Domke–Gower–Garrigos (NeurIPS 2023, Thm 2 and Thm 7) use a quadratic noise bound with constant $2(d+3)M^2$ and the
step $\gamma\le\mu/(2a)$, which is again $(d+3)\kappa^2$ iterations up to logarithms. The sticking-the-landing and
closed-form-entropy analyses of Kim–Ma–Gardner ([AISTATS 2024](https://arxiv.org/abs/2307.14642), Thm 5, Thm 6) are also
$\kappa^2$; their geometric rate $O(d\kappa^2\log(1/\varepsilon))$ (Cor. 2) needs a perfectly specified (Gaussian) target. Kim et al. (ICML 2026, Table 1) restate this as
$O(d\kappa^2\mathrm{tr}(\mu\Sigma^\star)/\epsilon)$ for $\mu\mathbb E W_2^2\le\epsilon$, which ranges from $d^2\kappa/\epsilon$
to $d^2\kappa^2/\epsilon$. The mean-field analysis (Kim–Ma–Campbell–Gardner, [NeurIPS 2025](https://arxiv.org/abs/2505.21721), Thm 3.2/Cor 3.3)
is also $\kappa^2$, and §5 of that paper states that "it is currently unclear whether the dependence on $\kappa$ is tight
or improvable". Park–Jang–Chen (2610.21020, §3) note that the reparameterization variance bound "scales as $\kappa^2$".

**This result: linear $\kappa$ with the plain estimator.** The two problem-specific constants are improved:

1. *Expected smoothness without $\kappa$* (`expected_smoothness`, the new step). Per sample,
   $\|g(\lambda;\xi)-g(\lambda^\star;\xi)\|^2\le(1+\|\xi\|^2)\|\Delta\|^2$ with $\Delta=\nabla V(X)-\nabla V(X^\star)$, and
   $\|\Delta\|^2\le 2L\,D_V(X,X^\star)$ by cocoercivity. The standard route to a bound in terms of
   $\mathbb E D_V$ decouples the weight $\|\xi\|^2$ from the per-sample Bregman divergence through
   $\|\Delta\|\le L\|Y\|$ and $D_V\ge\frac\mu2\|Y\|^2$ and loses a factor $\kappa$ (the constant $2L\kappa(d+k_\varphi)$ of Kim et al.,
   Lemma 3). We split at
   $\|\xi\|^2\le\tau$: below the threshold the weight is at most $1+\tau$; above it we use the crude bound
   $\|\Delta\|^2\le 2L^2\|\lambda-\lambda^\star\|^2(1+\|\xi\|^2)$ together with the $\chi^2$ moment generating function
   $\mathbb E e^{\|\xi\|^2/4}=2^{d/2}$, and $\tau=3d+8\log(48\kappa)$ makes the tail contribution at most
   $L\mu\|\lambda-\lambda^\star\|^2\le 2L\,\mathbb E D_V$. Result:
   $\mathbb E\|g(\lambda)-g(\lambda^\star)\|^2\le 2L(2+\tau)\,\mathbb E D_V(X,X^\star)$. The $\kappa$-loss is invisible for
   Gaussian targets (constant Hessian) and comes from curvature that is large exactly where $\|\xi\|$ is large.
2. *Variance at the optimum without $\kappa$* (`variance_at_optimum`). First-order optimality of $\lambda^\star$
   (Lean lemma `opt_pinner`, derived from minimality alone, by a two-sided perturbation argument) gives
   $\mathbb E\langle\nabla V(X^\star),u+U\xi\rangle=\sum_iU_{ii}/C^\star_{ii}$ for every lower-triangular $U$. With
   cocoercivity this yields $\mathbb E\|\nabla V(X^\star)-\nabla V(m^\star)\|^2\le L\,\mathbb E\langle\nabla V(X^\star),C^\star\xi\rangle=Ld$,
   hence $\mathbb E\|\nabla V(X^\star)\|^2\le Ld$, $\|\nabla V(m^\star)\|^2\le Ld$, $\|C^\star\|_F^2\le d/\mu$, and with the same
   tail split $\sigma_\star^2\le(2+\tau)Ld$. The identity $\mathrm{tr}(\Sigma^\star\mathbb E\nabla^2V)=d$ behind this step is the
   one used by Kim et al. (ICML 2026, Lemma 3.4 / App. C) for the Price estimator; we use its first-order form.

The algorithmic engine (proximal SGD with decreasing steps and weighted averaging under expected smoothness, in the
style of Gower et al. 2019 / Garrigos–Gower 2023) is standard; the contribution is the $\kappa$-free constants and the
resulting complexity.

## Comparison and regimes

| method (oracle) | guarantee | complexity (gradient evaluations) |
|---|---|---|
| Kim et al. NeurIPS'23 Thm 4, Domke et al. NeurIPS'23 Thm 7 (∇V) | $\mathbb E\|\lambda_T-\lambda^\star\|^2\le\varepsilon_d$, last iterate | $O(\kappa^2(d+k_\varphi)(1+R/\sqrt{\varepsilon_d})+(d+k_\varphi)L^2(\|\bar z-m^\star\|^2+\mathrm{tr}\Sigma^\star)/(\mu^2\varepsilon_d))$; ICML'26 Table 1: $O(d\kappa^2\mathrm{tr}(\mu\Sigma^\star)/\epsilon)$ for $\epsilon=\mu\mathbb E W_2^2$ |
| Kim–Ma–Gardner AISTATS'24 Thm 5/6 (STL, CFE; ∇V) | distance | $\kappa^2$-dependent; geometric only for Gaussian targets |
| this result (∇V) | $\mathbb E F-F^\star\le\varepsilon$ (⇒ distance $2\varepsilon/\mu$), weighted average | $O((d+\log\kappa)(\sqrt\kappa\sqrt{LR^2/\varepsilon}+d\kappa/\varepsilon))$; in distance units $O((d+\log\kappa)(\kappa R/\sqrt{\varepsilon_d}+d\kappa/(\mu\varepsilon_d)))$; in ICML'26 units ($\epsilon=\mu\mathbb E W_2^2\le 2\varepsilon$) the statistical term is $64(2+\tau)d\kappa/\epsilon=O((d+\log\kappa)d\kappa/\epsilon)$ |
| Kim et al. ICML'26 Thm 3.3, Price estimator (∇²V) | $\mu\mathbb E W_2^2\le\epsilon$ | $O(d\kappa/\epsilon+d\kappa^{3/2}\log(\kappa\Delta^2)/\sqrt\epsilon+\kappa^2\log(1/\epsilon))$ Hessian-based iterations |
| Price with finite-difference HVPs (∇V) | same | $d+1$ gradients per iteration on top of the previous iteration count; no analysis of this variant under $C^{1,1}$ alone is known (its bias needs Hessian regularity) |
| Park et al. 2610.21020 Thm 4.1/4.2 (∇V, extra Hessian-Lipschitz $L_H$) | $\mathbb E F-F^\star\le\varepsilon$ | $O((d\sqrt\kappa+\lambda_H^2d^3/\varepsilon)\log(\Delta_0/\varepsilon))$ |

* **Worst-case $\kappa$-dependence** drops from $\kappa^2$ to $\kappa$ for first-order access under only strong
  log-concavity and log-smoothness. Park–Jang–Chen (unreviewed preprint, Thm 3.1) prove that any randomized
  pointwise-derivative algorithm needs $\kappa^{1-o(1)}$ queries at a fixed KL accuracy on a family with
  $d=\Theta(\log^2\kappa)$ and bounded initial gap (so $LR^2/\varepsilon=O(\kappa)$); on that family our bound is
  $\kappa^{1+o(1)}$, so the exponent of $\kappa$ is now settled up to $\kappa^{o(1)}$ factors. Without the extra
  Hessian-Lipschitz assumption this is the first first-order bound with $\kappa^{1+o(1)}$ dependence that we found.
* **Statistical term** (in distance units, constants included): ours $\approx 64(2+\tau)d\kappa/(\mu\varepsilon_d)$ versus Kim et al.'s
  $8(d+k_\varphi)L^2(\|\bar z-m^\star\|^2+\mathrm{tr}\Sigma^\star)/(\mu^2\varepsilon_d)$. Since $L\,\mathrm{tr}\Sigma^\star\ge d$, ours is better by the factor
  $\approx(d+k_\varphi)L(\|\bar z-m^\star\|^2+\mathrm{tr}\Sigma^\star)/(8(2+\tau)d)$, which reaches order $\kappa$ (more if the mode–mean gap is large)
  on ill-conditioned posteriors with many weakly curved directions (e.g. Bayesian logistic regression
  $V(x)=\frac\mu2\|x\|^2+\sum_i\log(1+e^{-y_ia_i^\top x})$ with few strongly identified directions). When
  $L\,\mathrm{tr}\Sigma^\star\approx d$ (all directions near the top curvature) the old bound is better by a universal constant
  and a factor $(2+\tau)/(d+k_\varphi)=O(1+\log\kappa/d)$; we are uniformly no worse only up to universal constants and when
  $d\gtrsim\log\kappa$.
* **Startup term** improves from $\kappa^2(d+k_\varphi)R/\sqrt{\varepsilon_d}$ to $O((d+\log\kappa)\kappa R/\sqrt{\varepsilon_d})$, a gain of
  about $\kappa(d+k_\varphi)/(d+\log\kappa)$.
* **First-order vs. Price.** In gradient-equivalent cost the Price estimator needs $d$ HVPs per iteration, i.e.
  $\approx d^2\kappa/\epsilon$ plus $\kappa^{3/2}$ and $\kappa^2\log$ startup terms; our first-order bound matches the leading
  $d^2\kappa/\epsilon$ (up to the $(d+\log\kappa)/d$ factor and constants) without second-order access, and has a smaller startup
  term.

**Other method families checked.** Natural-gradient VI analyses either assume conjugacy (Wu–Gardner,
[ICML 2024](https://arxiv.org/abs/2406.01870)), use exact expectations and Hessians (square-root NGVI, Kumar et al.,
[TMLR 2025](https://arxiv.org/abs/2507.07853)), treat the mean-field family and stationarity (Sun–Fatkhullin–He,
[NeurIPS 2025](https://arxiv.org/abs/2510.19163)), or need relative strong convexity in an exponential family
(Guilmeau et al., [arXiv 2604.00683](https://arxiv.org/abs/2604.00683)); none gives a first-order total-query bound under
these assumptions. Bures–Wasserstein methods (Lambert et al. NeurIPS 2022; Diao et al. ICML 2023; Luu et al. ICLR 2025)
use Hessian-based (Bonnet–Price) gradients, ICML'26 has no BW theorem with the reparameterization gradient, and BW-FISTA
([arXiv 2611.08468](https://arxiv.org/abs/2611.08468), unreviewed) assumes a multiplicative noise model without a
$\kappa$-explicit first-order query bound. Structured families (Ko et al., [arXiv 2401.10989](https://arxiv.org/abs/2401.10989))
are analysed with the same $\kappa^2$ expected-smoothness constants.

## Limitations and open points

* Constants are not optimized; the extra factor $(2+\tau)/(d+1)=O(1+\log\kappa/d)$ in the statistical term relative to an
  ideal $(d+1)Ld$ variance bound comes from the $\chi^2$ tail split.
* The $d^2$ dependence of the statistical term is inherited from the scale gradient $\mathrm{low}(g\xi^\top)$; whether
  first-order GVI can achieve $d\kappa/\varepsilon$ is open (the Price estimator achieves $d\kappa/\epsilon$ iterations but uses
  Hessians).
* The guarantee is for the weighted-average output, not the last iterate. Step sizes need $L$, $\mu$ and $d$.
* The lower bound used to discuss optimality is in an unreviewed preprint and holds at a fixed accuracy; the optimal
  $\varepsilon$-dependence for first-order GVI is not settled.
* Literature search: arXiv (2023–Nov 2026; queries on black-box/Gaussian/Wasserstein/natural-gradient VI convergence
  and complexity). Read in full: Kim et al. NeurIPS'23 (2305.15349v4), Domke–Gower–Garrigos NeurIPS'23 (2306.03638v3),
  Kim–Ma–Gardner AISTATS'24 (2307.14642v7), Kim et al. NeurIPS'25 (2505.21721v2), Kim et al. ICML'26 (2602.18718v2),
  Park–Jang–Chen (2610.21020v1). Checked at abstract/theorem level: the NGVI, Bures–Wasserstein and BW-FISTA papers above.
  ICLR/NeurIPS 2026 OpenReview abstracts were not accessible, so very recent conference submissions may be missed.
* The conversion from the KL bound to the distance criterion ($F$ is $\mu$-strongly convex in $\lambda$) is standard and
  is not part of the Lean statement, which certifies the expected excess KL.
