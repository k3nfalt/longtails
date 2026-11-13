# Acceleration under pointwise third-derivative growth

[The theorem](PointwiseHessianAcceleration.lean) proves an exact-oracle complexity guarantee for the [pointwise Hessian setup](../Setups/PointwiseHessianConvex.lean), using the [accelerated Newton homotopy algorithm](../Algorithms/PointwiseHessianAccelerated.lean). The contribution is a parameter-separated guarantee under a pointwise derivative condition: initial Hessian magnitude enters only logarithmically, and relative curvature contributes an additive transient. The classical second-order accuracy exponent and the outer acceleration scheme are already known.

## Problem and guarantee

Let $f:E\to\mathbb R$ be convex and $C^3$, where $E$ is any finite-dimensional real Euclidean space. Assume an attained minimizer $x_\star$ and

\[
\|D\nabla^2 f(x)\|\le M_0+M_1\|\nabla f(x)\|\quad\text{for every }x,
\qquad
\|x_0-x_\star\|\le R,\quad f(x_0)-f(x_\star)\le\Delta,
\quad\|\nabla^2 f(x_0)\|\le H_0.
\]

The derivative norm is the induced operator norm. Here $M_0,M_1,H_0\ge0$ and $R,\Delta,\varepsilon>0$. No strong convexity, bounded level set, global Hessian Lipschitz constant, first-order gradient-growth inequality, or pairwise local Hessian-growth certificate is assumed. The setup does not restrict the admissible algorithm family.

Define

\[
B=\frac{M_0R^3}{\varepsilon},\qquad U=M_1R^2,\qquad
Z=2+\frac{\Delta+H_0R^2+M_0R^3+M_1^2R^4\Delta}{\varepsilon}+M_1R^2,
\]
\[
K=\left\lceil 2^{45}(1+B^{2/7}+U^{3/2})(1+\log Z)^4\right\rceil.
\]

The public budget allocates **$K$ gradient calls and $K$ full-Hessian calls**, hence at most $2K$ derivative calls in total. It counts rejected outer trials, radius retries, aborted Newton steps, and terminal padding. The returned output satisfies $f(x_{\mathrm{out}})-f(x_\star)\le\varepsilon$ for every exact oracle realization. The formal setup records this as almost-sure success under the framework's explicit probability law; the proof is pointwise in all seeds, so it is not a fixed-success-probability result.

The algorithm receives $x_0,M_0,M_1,R,\Delta,\varepsilon$. It receives neither $x_\star$, $f(x_\star)$, nor $H_0$. The latter is an analysis parameter in `Params`, absent from `Public`. No function-value oracle is used. Each Hessian call returns the full linear map; exact real linear algebra is free in this oracle model. There is no dimension factor in the derivative-call bound, but matrix storage, factorization, and finite-precision costs are not bounded here.

The pointwise condition is an established second-order generalized-smoothness assumption: see Fang, Marumo, and Takeda, [arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741v1), whose target is nonconvex second-order stationarity. Convexity, existence of a minimizer, and initial distance control are the standard accelerated convex framework. The initial gap initializes a nonzero acceleration weight. The $H_0$ bound is not a global restriction: every individual $C^3$ instance has a finite initial Hessian norm. Requiring positive radius and gap bounds permits all instances also having zero actual distance or gap, by choosing positive upper bounds.

## Algorithm and proof mechanism

Initialize $A_0=R^2/(2\Delta)$, $\eta_0=1/A_0$, and $w=z=x_0$. If $\Delta\le\varepsilon$, store $x_0$ as the finished output. Otherwise use damped Monteiro–Svaiter acceleration. The center is the weighted combination of $w,z$ with trial weight $a$ satisfying $\eta a^2=A+a$. Successful outer trials update the stored weighted point $w$; reaching $A\ge R^2/\varepsilon$ returns that point. A tested gradient norm at most $\varepsilon/(1000R)$ instead returns its queried point. These are explicit output-selection rules in `update` and `accept`.

At center $c$ and trial $\tau\ge\eta$, solve the proximal equation using a Newton continuation in $b\le1/\tau$. For a trial radius $r$, use

\[
\alpha=\frac1{64(1+M_1r^2+M_0r/\tau)},\qquad
b_0=\min\left\{\frac1\tau,\frac{\alpha r}{4\|\nabla f(c)\|}\right\}.
\]

The zero-gradient case has already stopped. Newton steps solve linear systems with $I+b\nabla^2 f(x)$, and continuation increases $b$ by a factor $1+\alpha/8$, capped at $1/\tau$. A proposed point outside distance $2r$ aborts before its gradient query; its Hessian query remains charged. Radius guesses double up to $\min\{16R,\tau/(64M_0)\}$, with cap $16R$ when $M_0=0$. Failure at the cap doubles $\tau$. At the final $b$, refinement continues until the MS residual test or the gradient stopping test succeeds.

Three estimates provide the substantive mechanism:

* **Polynomial localization.** Along the minimizer-to-initial segment,
  $\|\nabla^2f(x_\star)\|\le2H_0+2M_0R+M_1^2R^2\Delta$.
  On a segment to a stored $w$, the Hessian is bounded by
  $4H_0+12M_0R+34M_1^2R^2\Delta$.
  These are derived from convexity, the pointwise condition, and the acceleration energy; they are not extra setup hypotheses.
* **Newton direction control and radius accounting.** Positive semidefiniteness controls both the Newton displacement and its image under the scaled Hessian. The actual residual contracts by $1/4$. An aborted radius certifies an insufficient radius for the exact proximal solution, which is used only in the proof. Accepted-step energy then bounds the sum of all started squared radii by $2464R^2$, including unfinished terminal episodes.
* **Center movement accounting.** The sum of accepted center displacements, plus the current displacement, is bounded by $6R[6+4\log(A_N/A_0)]$. Vector gradient growth gives a cold-start logarithm bounded by $64(1+\log Z)+\sqrt{M_1}\|c-w\|$. Charging this term through center movement avoids multiplying the leading accuracy term by worst-case relative curvature or initial Hessian magnitude.

The remaining logarithms account for finite continuation, refinement, and radius/trial retries. [The cost proof](../Proofs/PointwiseHessianCost.lean) establishes the bound for every unfinished finite prefix, proves bounded termination, and connects it to `execute`. Conditional scalar recurrences are discharged by actual state invariants. No proximal oracle, uncounted inner oracle, future successful trial, or assumed convergence is used.

## Novelty comparison and regimes

Carmon et al., [*Optimal and Adaptive Monteiro-Svaiter Acceleration*, NeurIPS 2022, arXiv v2](https://arxiv.org/abs/2205.15371v2), supplies the established acceleration background. Under uniform Hessian Lipschitzness, the $\varepsilon^{-2/7}$ exponent is already optimal. This result neither improves that exponent nor claims improved uniform-Hessian complexity; its four logarithms are a loss in that special case.

The closest generalized-smoothness baseline is Agafonov et al., [arXiv:2609.32977v1, Theorem 4.1 and Appendix F.4](https://arxiv.org/html/2609.32977v1). With exact Hessians, its local pairwise condition gives
$\widetilde O(1+(\bar M_0R^3/\varepsilon)^{2/7}+\bar M_1^{1/3}R^{2/3}+(R/\rho)^{2/3})$, including gradient accounting. Its method is parameter-free and also treats inexact Hessians. Proposition 2.7 converts pointwise TD plus $\|H(x)\|\le L_0+L_1\|g(x)\|$ to pairwise constants
$\bar M_0=M_0+M_1L_0\rho e^{L_1\rho}$, $\bar M_1=M_1e^{L_1\rho}$. Within the $C^3$ class, pairwise LH implies TD with the same coefficients. We remove the additional pairwise/first-order certificate, but require $C^3$ rather than the baseline $C^2$ regularity, known parameters, exact Hessians, and a larger relative-curvature transient.

A fair standard-reduction comparison optimizes $\rho$. Put $J=M_1L_0R^4/\varepsilon$ and $t=\rho/R\le\min\{1,1/(L_1R)\}$. Substitution yields the competing terms $J^{2/7}t^{2/7}+t^{-2/3}$. Choosing $t\asymp J^{-3/10}$ when permitted gives $J^{1/5}$, with an additional $(L_1R)^{2/3}$ scale if the cap binds. Thus the optimized certificate-level comparison is

\[
\widetilde O\bigl(1+B^{2/7}+U^{1/3}+J^{1/5}+(L_1R)^{2/3}\bigr).
\]

This calculation is a reduction to an existing upper bound, not a lower bound on its algorithm. The new guarantee is useful when the coupled stiffness term dominates $1+B^{2/7}+U^{3/2}$, allowing for logarithms. In particular, with $M_0=0$ and fixed other parameters, our accuracy dependence is logarithmic, while that generic locality reduction retains an accuracy-dependent stiffness term. Favorable instance-specific pairwise or quasi-self-concordant certificates can give much better prior bounds. The examples below are not witnesses of hardness for those methods.

A concrete uniformization reduction restricts optimization to the radius-$R$ ball about $x_0$, which contains $x_\star$. Write $H_\star=2H_0+2M_0R+M_1^2R^2\Delta$. The proved vector growth estimate gives a valid Hessian Lipschitz certificate on this ball,

\[
L_{\rm ball}=M_0+M_1(2H_\star R+4M_0R^2)e^{1+2\sqrt{M_1}R}.
\]

Applying uniform-Hessian acceleration therefore costs $O(1+(L_{\rm ball}R^3/\varepsilon)^{2/7})$ derivative calls in the exact setting. One initial Hessian query supplies the initial norm bound if it is not already given; ball projection and model algebra use no derivative oracle. This is a valid costed reduction, but retains stiffness and relative-curvature coupling. The new analysis avoids that substitution through localization and movement accounting.

Agafonov et al., [arXiv:2610.11693v2, Assumption 3.1 and Theorem 5.1](https://arxiv.org/html/2610.11693v2), gives optimal stochastic contracting-cubic acceleration on a compact convex domain with uniformly Lipschitz Hessian. Its exact specialization uses two gradients and one Hessian per outer iteration and recovers the uniform-Hessian rate. Compactification itself is not a distinction: a known radius permits a bounded feasible region. Its Hessian certificate is the relevant difference. These September and October 2026 sources are preprints; no conference acceptance is asserted for them.

The $U^{3/2}$ transient is worse than the $U^{1/3}$ term available from favorable pairwise certificates. We establish no lower bound or optimality for the relative-curvature dependence, no inexact-oracle extension, and no practical advantage from the large explicit constant. Standard acceleration and Newton continuation individually are not the novelty claim; their cost-preserving use under TD requires the localization and movement estimates.

## Nonlinear scope and further comparisons

For arbitrary dimension, dense positive-semidefinite $Q$, and $\beta>0$,
\[
f(x)=\tfrac12x^TQx+\tfrac\beta4\|x\|^4
\]
is a nonseparable convex example, including singular $Q$. It has $\|D H(x)\|\le6\beta\|x\|$ and $\|g(x)\|\ge\beta\|x\|^3$. For any $M_1>0$, taking $M_0=4\sqrt2\beta/\sqrt{M_1}$ proves TD, with no dimension factor or dependence on $\|Q\|$ in these two constants. Global Hessian Lipschitzness need not hold.

The zero-$M_0$ regime also contains genuinely nonlinear interacting objectives: $f(x)=\sum_i(\cosh x_i-1)+\tfrac12x^TQx$ for dense $Q\succeq0$. Since $\|x\|\le\|g(x)\|$ and $\|\sinh x\|\le(1+\|Q\|)\|g(x)\|$, TD holds with $M_0=0,M_1=1+\|Q\|$. This family illustrates coverage, not superiority over specialized analyses.

The final [Semenov, Jaggi, and Doikov ICLR 2026 paper](https://proceedings.iclr.cc/paper_files/paper/2026/file/1759a83b007f0685c3fbc460fa1b6395-Paper-Conference.pdf) was checked, including Theorem 2 and Appendix G.6, equation (78) and Proposition 8. Its generic convex theorem uses a structural gradient-normalized smoothness radius and a bounded initial-sublevel diameter. The G.6 specialization assumes global endpoint-gradient pairwise Hessian growth and gives a nonaccelerated convex bound; it is not a pointwise-TD accelerated guarantee. Appendix G.4 gives stronger results for generalized quasi-self-concordant subclasses. These specialized certificates may outperform our result, but no parameter-preserving reduction from general TD to them was verified.

The literature review was refreshed on 13 November 2026 after surveying current conference and arXiv work and following the older acceleration results. November 2026 first-order generalized-smoothness and nonconvex stationarity sources were also screened. The claim is the parameterized TD guarantee above, not an assertion that every prior special-case analysis is dominated.
