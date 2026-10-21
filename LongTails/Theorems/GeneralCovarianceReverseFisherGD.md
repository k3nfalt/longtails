# Reverse-Fisher GD for Gaussian mixtures with a general covariance

[Lean theorem](GeneralCovarianceReverseFisherGD.lean) · [Setup](../Setups/GeneralCovarianceReverseFisher.lean) · [Algorithm and output](../Algorithms/GeneralCovarianceReverseFisherGD.lean)

This result extends the single-teacher global-convergence theorem of Tyurin (Theorem 2.1 and Corollary 2.5 of [arXiv:2606.19876v1](https://arxiv.org/abs/2606.19876v1)) from identity covariances to an arbitrary shared, known, positive-definite covariance \(\Sigma\). The setup is otherwise unchanged:
- reverse Fisher divergence;
- equal fixed weights;
- learned means;
- exact population gradient;
- plain gradient descent from an arbitrary initialization.

The proved complexity pays a factor \(\kappa^2=(s_{\max}/s_{\min})^2\) for the anisotropy. Its leading constants are smaller than those of the identity-covariance corollary, owing to a sharper tail estimate and budget accounting. The mechanism is a careful adaptation of Tyurin's Lyapunov argument rather than a new proof paradigm. The user who commissioned the task explicitly accepted a possibly straightforward generalization.

## Model, oracle, and guarantee

Fix \(d\ge1\) and \(n\ge1\). Let \(\Sigma=AA^\top\) for an invertible \(A\), so that \(\mathcal N(\mu,\Sigma)\) is the law of \(\mu+AZ\) with \(Z\) standard Gaussian. The loss depends on \(A\) only through \(\Sigma\). Write \(P=\Sigma^{-1}\). The student and teacher are

\[
 p_\theta=\frac1n\sum_{i=1}^n\mathcal N(\theta_i,\Sigma),\qquad \bar p=\mathcal N(\bar\mu,\Sigma),
 \qquad \theta=(\theta_1,\ldots,\theta_n)\in(\mathbb R^d)^n .
\]

The scores are defined in Lean as gradients of the logarithms of the unnormalized densities \(\sum_i\exp(-\tfrac12\|A^{-1}(x-\theta_i)\|^2)\). The teacher score is the same function with a single center. The objective is the actual reverse Fisher divergence

\[
 L(\theta)=\mathbb E_{X\sim p_\theta}\big\|\nabla\log p_\theta(X)-\nabla\log\bar p(X)\big\|^2
 =\frac1n\sum_{\ell=1}^n\mathbb E_{Z}\big\|\nabla\log p_\theta-\nabla\log\bar p\big\|^2(\theta_\ell+AZ).
\]

The parameter space is the Euclidean product \((\mathbb R^d)^n\), formalized as `PiLp 2`, so `gradient` is the true Euclidean gradient. One oracle call returns the exact gradient \(\nabla L(\theta)\), including the dependence of the sampling law on \(\theta\).

**Public information.** The algorithm sees:
- \(d,n\);
- spectral bounds \(0<s_{\min}\le s_{\max}\), with \(s_{\min}\|v\|^2\le v^\top\Sigma v=\|A^\top v\|^2\le s_{\max}\|v\|^2\);
- the initialization \(\theta^0\in(\mathbb R^d)^n\), which is arbitrary;
- a radius \(R\ge\max_i\|\theta^0_i-\bar\mu\|\);
- the target accuracy \(\varepsilon>0\).

The teacher mean \(\bar\mu\) and the covariance \(\Sigma\) itself are not public.

**Algorithm.** Gradient descent \(\theta^{k+1}=\theta^k-\gamma\nabla L(\theta^k)\) with the constant step

\[
 \gamma=\frac{n\,s_{\min}^2}{2(1+8\log n)} .
\]

The setup's `allowedAlgorithm` enforces the GD family:
- the first iterate equals the public \(\theta^0\);
- queries are made at the current iterate;
- updates are \(\theta\mapsto\theta-\eta\,g\) with positive \(\eta\);
- the output is the last iterate.

**Guarantee.** After exactly

\[
 K=\Big\lceil (1+8\log n)\Big(\frac{s_{\max}}{s_{\min}}\Big)^2\Big(2\log\big(1+\tfrac{R^2}{s_{\min}}\big)+\frac{4n\min\{n,d\}\,s_{\max}}{\varepsilon}\Big)\Big\rceil+1
\]

oracle calls, the returned last iterate satisfies \(\max_i\|\theta^K_i-\bar\mu\|^2\le\varepsilon\). This holds deterministically, for every admissible covariance, teacher mean, and initialization. Writing \(\kappa=s_{\max}/s_{\min}\), the rate is

\[
 K=O\Big(\kappa^2(1+\log n)\Big[\log\big(1+R^2/s_{\min}\big)+\frac{n\min\{n,d\}\,s_{\max}}{\varepsilon}\Big]\Big).
\]

## How the result meets the user's scope requirement

The requirement was to generalize the result of "Global Convergence of Gradient Descent for Score Matching in Gaussian Mixtures via Reverse Fisher Divergence" to non-identity variances, with "the same setup, but general variances".
- **Same setup.** Everything matches Tyurin's Section 1.3 and Theorem 2.1:
  - the reverse Fisher objective;
  - GMM student with equal fixed weights;
  - single-Gaussian teacher;
  - learned means only;
  - exact-gradient GD from every initialization;
  - squared Euclidean distance of every student mean to the teacher mean.
- **General variances.** The common identity covariance is replaced by an arbitrary shared, known, symmetric positive-definite \(\Sigma\), not merely \(\sigma^2I\) or diagonal. It enters both the sampling law of every component and the scores.
- **What is not covered.**
  - The multi-teacher Theorem 3.2/E.1 is not generalized; see the limitations below.
  - Learning the covariances is a different setup and is excluded.
  - Different fixed covariances per component would make the single-teacher problem misspecified.

## Relation to prior work

| Result | Statement | Relation |
|---|---|---|
| [Tyurin, arXiv:2606.19876v1](https://arxiv.org/abs/2606.19876v1), Thm 2.1, Lemmas 2.2–2.4, Cor. 2.5 | Identity covariances. With \(\gamma\le n/(4+512\log n)\), \(\|\mu^k_i-\bar\mu\|^2\le\max\{(1-\gamma/2n)^{k/2}nR_0^2,\,8n\min\{n,d\}/(\gamma k)\}\). This gives \(4096\max\{(1+\log n)\log(nR_0^2/\varepsilon),(1+\log n)n\min\{n,d\}/\varepsilon\}\) iterations. | Same setup with \(\Sigma=I\). At \(\Sigma=I\) the present budget is \((1+8\log n)(2\log(1+R^2)+4n\min\{n,d\}/\varepsilon)+2\). The polynomial order is the same, with smaller constants and no \(\log(n/\varepsilon)\) factor in the linear phase. These are bookkeeping gains, not a new rate. |
| Tyurin, Thm 3.2/E.1 | Multiple teacher components, identity covariance, random spherical initialization, \(\tilde\Omega(1)\) separation. | Not generalized here. |
| [Repository result `SymmetricReverseFisherGlobalGD`](SymmetricReverseFisherGlobalGD.md) | Reverse Fisher GD for the balanced symmetric student \(\tfrac12\mathcal N(\theta,I)+\tfrac12\mathcal N(-\theta,I)\) against a symmetric two-component teacher, identity covariance, random initialization. | A different model (tied symmetric components and a two-component teacher) with identity covariance and its own setup. Neither result implies the other. |
| Tyurin, §3.4 "non-isotropic generalization" | A product of mixture problems with different component counts. | Not about covariances; unrelated to this extension. |
| [Zhang, Xu, Zhou, Fazel, Du, ICLR 2026, arXiv:2511.22069v1](https://arxiv.org/abs/2511.22069v1) | Forward Fisher (DDPM-type) for an over-parameterized student and a single Gaussian teacher, identity covariance. Convergence depends on the noise level and initialization. | Different objective; identity covariance. |
| [Shah, Chen, Klivans, NeurIPS 2023](https://arxiv.org/abs/2307.01178v1) | DDPM objective, two symmetric components, identity covariance. | Different objective and model. |
| [Xu, Hsu, Maleki, NeurIPS 2016](https://arxiv.org/abs/1608.07630) | EM for two components with known general \(\Sigma\). | EM is affine-equivariant, so for EM a known \(\Sigma\) is without loss of generality. GD on the reverse Fisher loss is not, which is why the present extension is not a change of variables. |
| [Chen, Kontonis, Shah, arXiv:2404.18893](https://arxiv.org/abs/2404.18893) | Learning mixtures with general covariances via score-based methods. | Sampler/statistical guarantees, not GD dynamics on this objective. |

The search (performed 2026-10-20 UTC by both agents) found no prior analysis of GD on the reverse or forward Fisher divergence for Gaussian mixtures with a non-identity covariance. arXiv lists only v1 of Tyurin's paper, and its only citing work found is unrelated. This is a targeted search; full proceedings of ICML/ICLR/NeurIPS 2025–2026 were not exhaustively crawled.

## What the standard reductions give, and the mechanism

**Scalar case.** For \(\Sigma=\sigma^2I\) the problem rescales exactly to Tyurin's: \(L^\sigma(\mu)=\sigma^{-2}L^1(\mu/\sigma)\). That case contributes nothing new.

**Whitening fails for general \(\Sigma\).** Setting \(y=A^{-1}x\) turns the problem into Tyurin's identity-covariance mixture, but with:
- a \(\Sigma^{-1}\)-weighted squared score error in place of the Euclidean one;
- \(\Sigma^{-1}\)-preconditioned GD in place of plain GD.

Neither is Tyurin's problem, and no change of variables removes both.

**The κ² factor in the linear phase is unavoidable for constant-step GD.** For \(n=1\), \(L(\theta)=\|P(\theta-\bar\mu)\|^2\), whose Hessian \(2P^2\) has condition number \(\kappa^2\). Constant-step GD therefore needs order \(\kappa^2\log(1/\varepsilon)\) steps. This argument is in the note only; it is not formalized. Whether \(\kappa^2\) is also needed in the sublinear \(1/\varepsilon\) term is **open**: only the upper bound is proved.

**Mechanism.**
1. **Exact gradient.** Differentiating under the integral sign and integrating by parts on Lebesgue measure gives the exact gradient pairing
\[
 \langle\nabla L(\theta),PY\rangle=\frac2n\,\beta(Y,U),\qquad U_i=\theta_i-\bar\mu .
\]
Here \(\beta\) is a symmetric positive semidefinite bilinear form: \(\kappa_0\int \text{total}(x)\,b_x(Y,U)\,dx\), where \(b_x\) collects a \(\Sigma\)-whitened posterior-mean term and a Hadamard (tensor) term built from \(P(\theta_i-m(x))\).
2. **Lyapunov function.** The Mahalanobis Lyapunov function \(V(\theta)=\sum_i(\theta_i-\bar\mu)^\top P(\theta_i-\bar\mu)\) makes the cross term a sum of squares. This keeps Tyurin's trace–rank argument (\(\operatorname{tr}(M)^2\le\min\{n,d\}\|M\|_F^2\)) available without matrix square roots.
3. **Two spectral estimates.**
   - \(s_{\min}^2\beta(Y,Y)\le(1+8\log n)V(Y)\).
   - \(s_{\max}^2\beta(U,U)\ge\min\{V/2,\,V^2/(4n\min\{n,d\})\}\).
4. **Tail estimate (improvement over Lemma 2.3).** Tyurin's estimate gives \(128\log n\). It is replaced by
\[
 \mathbb E_{N(\theta_i,\Sigma)}\|A^{-1}(\theta_i-m(X))\|^2\le 8\log n .
\]
The proof combines three steps:
   - the pointwise bound \(r_j\le\sqrt{r_j}\le e^{(\langle z,c_j\rangle-\|c_j\|^2/2)/2}\);
   - the Gaussian moment generating function, which gives \(\mathbb E r_j\le e^{-\|c_j\|^2/8}\);
   - an entropy bound \(\sum_jp_j\log(1/p_j)\le\log n\).
5. **Recurrence.** An AM–GM/Cauchy–Schwarz step and the step size \(\gamma=n/(2c_0)\), with \(c_0=(1+8\log n)/s_{\min}^2\), give
\[
 V^{k+1}\le V^k-\frac{s_{\min}^2}{(1+8\log n)s_{\max}^2}\min\Big\{\frac{V^k}2,\frac{(V^k)^2}{4n\min\{n,d\}}\Big\}.
\]
This is solved in two phases: geometric decay while \(V>2n\min\{n,d\}\), then a reciprocal \(1/k\) phase. The final step uses \(\|\theta_i-\bar\mu\|^2\le s_{\max}\,V\).

## Limitations

- This is a modest extension of one theorem. Its mechanism closely follows Tyurin's Section 2, and the main new ingredients are the anisotropic bookkeeping and the entropy tail bound. It is not claimed as a new proof technique or a new optimization rate for the identity case.
- Only the single-teacher case is covered. The multi-teacher anisotropic case (Tyurin's Theorem 3.2) remains open and is genuinely harder. The preconditioned far-field path \(\mu^k-\bar\mu_a\approx(I-2\gamma\Sigma^{-2}/n)^k(\mu^0-\bar\mu_a)\) is curved and can leave the Mahalanobis or Euclidean Voronoi cell of the teacher nearest at initialization. The nearest-teacher assignment rule and the segment-separation event used by Tyurin can therefore fail.
- The covariance is known and shared. Only spectral bounds are used by the algorithm, but the oracle is the exact population gradient. No stochastic-gradient, finite-sample, or score-estimation guarantee is given.
- The sublinear term's \(\kappa^2\) and \(n\min\{n,d\}\) factors are upper bounds; no matching lower bound is proved for them.
- Constants are explicit but not optimized.

## Verification

The Lean development proves every analytic step:
- the multivariate standard-Gaussian density and affine change of variables;
- the gradient of the log mixture density;
- differentiation under the integral with an explicit Gaussian domination bound;
- integration by parts;
- the entropy tail lemma;
- the bilinear-form bounds;
- the recurrence and the budget sufficiency for the actual executed iterates.

The public theorem imports the setup directly and states `Convergence spec budget` with a one-line public budget. The verification commands are `./build.sh`, `./lint.sh`, and `python3 run_comparator.py GeneralCovarianceReverseFisherGD.lean`. The comparator permits only `propext`, `Classical.choice`, and `Quot.sound`.
