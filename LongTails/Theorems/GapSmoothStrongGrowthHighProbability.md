# High-probability acceleration with gap-dependent curvature and strong-growth noise

The Lean result is [`GapStrongGrowth.result`](GapSmoothStrongGrowthHighProbability.lean), for the [gap-smooth strong-growth setup](../Setups/GapSmoothStrongGrowth.lean) and the [clipped accelerated algorithm](../Algorithms/GapStrongGrowthAccelerated.lean). It concerns the last primal iterate of one uninterrupted run. It uses gradient samples only: no objective-value comparisons, restarts, projections, or access to a minimizer.

## Problem and guarantee

Let \(f:E\to\mathbb R\) be convex and differentiable with a minimizer \(x_\star\). The formal result permits a separable complete real Hilbert space, including every finite-dimensional Euclidean space. Public certificates satisfy

\[
\|x_0-x_\star\|\le R,\qquad f(x_0)-f(x_\star)\le\Delta,
\quad R,\Delta>0.
\]

Write \(F(x)=f(x)-f(x_\star)\). For \(H_0,H_1\ge0\), the population objective satisfies the local model

\[
f(y)\le f(x)+\langle\nabla f(x),y-x\rangle
 +(H_0+H_1F(x))\|y-x\|^2
\]

whenever \((2\sqrt3+\sqrt6)\sqrt{H_1}\|y-x\|\le1\). The coefficient convention is exactly the one in the Lean specification; there is no suppressed factor \(1/2\).

A jointly measurable oracle has integrable, unbiased vector replies and integrable squared noise, with

\[
\int g(x,\xi)\,dp(\xi)=\nabla f(x),\qquad
\int\|g(x,\xi)-\nabla f(x)\|^2\,dp(\xi)
 \le(\rho-1)\|\nabla f(x)\|^2,\quad \rho\ge1.
\]

The full sampling law is an arbitrary law \(P\) whose coordinates are measurable, independent, and have marginal \(p\). Product laws are derived inside the proof. No finite-sample-space assumption is made. This is stationary IID sampling, not a theorem for arbitrary adaptive or time-inhomogeneous martingale noise. No samplewise convexity, samplewise smoothness, almost-sure relative-error bound, bounded domain, strong convexity, or exponential noise moment is assumed.

For \(0<\varepsilon\le\Delta\) and \(0<\delta<1\), put

\[
N=\left\lceil 2^{27}\bigl(1+\log(1/\delta)\bigr)
 \left[(1+R\sqrt{H_1})\log(1+\Delta/\varepsilon)
       +R\sqrt{H_0/\varepsilon}\right]\right\rceil.
\]

The algorithm makes exactly \(K=N\lceil\rho\rceil\) oracle calls and returns \(x_N\), satisfying the explicit failure-probability statement

\[
\int \mathbf1\{f(x_N(\omega))-f(x_\star)>\varepsilon\}\,dP(\omega)
 \le\delta.
\]

The repository theorem includes the algorithm's independent singleton seed in the execution law, which does not change this probability. Its public budget is one explicit formula in the setup parameters. The numerical constant is conservative; neither constants nor optimal dependence on \(\rho\) or confidence are claimed.

## Algorithm

Set \(q=128\log(e/\delta)\), \(b=\lceil\rho\rceil\), \(A_0=R^2/\Delta\), and \(z_0=x_0\). At an iteration with state \((A,x,z)\), use

\[
B=1+R\sqrt{H_1}+\sqrt{H_0A},\quad
 a=\frac{A}{32768qB},\quad A^+=A+a,\quad
 y=\frac{Ax+az}{A^+}.
\]

Average \(b\) fresh oracle replies at this same \(y\), clip that average radially to norm \(R/(qa)\), obtaining \(h\), and set

\[
z^+=z-ah,\qquad x^+=y-\frac{32qa^2}{A^+}h.
\]

The Lean definition uses \(q=128(1+|\log\delta|)\), proved equal to the displayed formula on valid inputs. Batch averaging happens before clipping. [`GapStrongGrowthExecution.lean`](../Proofs/GapStrongGrowthExecution.lean) connects these iterations to every individual framework query; the cost includes every batch reply.

## Contribution and closest results

The contribution is accelerated accuracy dependence together with logarithmic confidence dependence under population gap-dependent curvature and only second-moment strong growth. The mechanism keeps a negative gradient-squared drift while controlling clipping bias and exponential fluctuations on the same evolving energy region. Localization, clipping, and exponential supermartingales are established tools; they are not separately claimed as new.

An explicit motivation is [Dvinskikh, Gasnikov, Lobanov, and Latypov, *Localize, Restart, Accelerate*, arXiv:2609.06555v1, September 6, 2026](https://arxiv.org/abs/2609.06555v1), Appendix I, Theorem 7 and Remark 14. Their convex guarantee uses almost-sure strong growth and additional component regularity. Remark 14 leaves extension of Theorems 6–7 to second-moment strong growth unresolved because robust mean estimators introduce bias inside acceleration. The present result gives a stronger convex alternative for stationary IID oracles, including that objective class, without those samplewise restrictions. It does not extend their exact algorithm or resolve their strongly convex Open Problem 2. Their Assumption 5, Lemma 6, and Corollary 1 imply our model with \(H_0=L_0,H_1=2L_1^2\): the descent coefficient is at most \(L_0+\tfrac32L_1^2F(x)\), and our allowed radius is smaller than \(1/L_1\).

The closest general oracle comparison is [Lobanov, Dvinskikh, and Gasnikov, *Accelerated Stochastic Method under (H0,H1)-Smoothness and Heavy-Tailed Noise*, arXiv:2609.33415v1, September 27, 2026](https://arxiv.org/abs/2609.33415v1), Theorem 9 and Appendix H.1. On the common IID subclass, specializing to second moments and pure strong growth leaves a stochastic term, up to logarithms and universal factors,

\[
(\rho-1)R^2\left(H_0/\varepsilon+H_1J_H\right),
\]

where, for positive curvature parameters, \(J_H=\min\{S,\lceil\max(0,\log_2(H_1\Delta/H_0))\rceil\}\) and \(S=\lceil\log_2(\Delta/\varepsilon)\rceil\); set \(J_H=0\) when \(H_1=0\). Their displayed bound also retains a cross term, equivalent up to a factor two. Their deterministic term is accelerated. Their parameter is a domain diameter \(D\); choosing the ball centered at \(x_0\) with radius \(R\) gives \(D\le2R\), so this is a constant-factor comparison on a common instance class. Our stochastic accuracy dependence is instead \(\rho R\sqrt{H_0/\varepsilon}\), with the displayed initialization and confidence terms. For fixed \(H_0>0,\rho>1\) and other parameters, sufficiently small \(\varepsilon\) gives a strict order improvement. Ignoring logarithms, the accuracy-dominated comparison improves when \(R\sqrt{H_0/\varepsilon}\gg\rho/(\rho-1)\). No uniform superiority over their broader mixed-noise model is asserted. Batching their oracle reduces variance by the batch size but multiplies calls by the same size, retaining the slower term.

[Podlipnova et al., *Smooth or Separable? Sparse Block Acceleration for Entropy-Regularized Linear Programs*, arXiv:2609.32558v1, September 26, 2026](https://arxiv.org/abs/2609.32558v1), Theorem 4.2 and Appendix C, already use stopped energy localization, growing weights, and a single-run accelerated analysis for general objectives with block gap-dependent Hessian bounds. Their auxiliary point formed with \(x_\star\) is also used here. Their single-run high-confidence cost has polynomial \(1/\delta\) dependence; amplification by repeated runs and objective selection in their Theorem 4.3 uses function values. Thus the present claim is not novelty of fixed-confidence localization: it concerns logarithmic confidence and arbitrary finite-variance strong-growth gradient replies, with no objective selection.

[Nguyen, Nguyen, Ene, and Nguyen, NeurIPS 2023](https://papers.nips.cc/paper_files/paper/2023/file/4c454d34f3a4c8d6b4ca85a918e5d7ba-Paper-Conference.pdf), Appendix D, Theorem D.1 and Lemma D.3, already develop exponential “whitebox” clipping analysis for accelerated mirror descent. Their theorem assumes global smoothness and uniform additive noise moments. Substituting a worst-case localized strong-growth variance leaves an \(\varepsilon^{-2}\) stochastic cost. Their one-step proof eliminates descent slack through Young's inequality; the present proof retains enough gradient-dependent negative drift to absorb the entire exponential correction while simultaneously localizing curvature.

[Lobanov and Koloskova, arXiv:2605.14800v2, May 26, 2026](https://arxiv.org/abs/2605.14800v2), Appendix C, already absorb clipping bias in overparameterized generalized-smooth optimization. Their Theorem C.10 is nonaccelerated and uses component convexity and component generalized smoothness. [El Bakkali El Kadi et al., arXiv:2505.20817v3, September 29, 2026](https://arxiv.org/abs/2505.20817v3) provide high-probability generalized-smooth clipped-SGD guarantees with uniform central noise moments. Bias absorption and stopped exponential arguments alone are therefore not new. Under global smoothness, [Hermant et al., arXiv:2410.07870v3, June 11, 2026](https://arxiv.org/abs/2410.07870v3), Theorem 3, already give accelerated expected complexity proportional to \(\rho R\sqrt{L/\varepsilon}\). We do not claim a new accuracy rate for the \(H_1=0\) case.

These September arXiv sources are preprints; they are not presented as accepted conference papers.

## Standard reductions and the remaining gap

Independent restarts with objective selection require information unavailable here. Plain geometric-median aggregation of points does not certify convex function gaps: for \(f(x,y)=x^2/2\), three points \((0,-1),(0,0),(0,1)\) are exact minimizers, but adding two copies of \((B,0)\), \(B>1/\sqrt3\), makes the geometric median \((1/\sqrt3,0)\), with gap \(1/6\).

Pure strong growth is not preserved by regularization: for \(f(t)=t^2/2\) and oracle \(Zt\), adding \(\lambda(t-c)^2/2\) moves the minimizer to \(u=\lambda c/(1+\lambda)\ne0\), where the new full gradient vanishes while the oracle variance remains positive if \(\operatorname{Var}Z>0\). This only prevents literal reuse of a pure-SGC solver. A mixed-noise composition is substantially stronger and does recover high-probability acceleration for globally smooth objectives.

Specifically, [Gupta and Wojtowytsch, arXiv:2410.08395v3, Theorem 15 and Appendix B.4](https://arxiv.org/html/2410.08395v3), published at [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/2f050fa9f0d898e3f265d515f50ae8f9-Abstract-Conference.html), give a mixed-noise AGNES bound. With variance bounded by \(\sigma_m^2\|\nabla h\|^2+\sigma_a^2\), its contraction is \(1-q\) and its error floor is \(\sigma_a^2q/\mu\), where \(q=\sqrt{\mu\eta/(1+\sigma_m^2)}\). Tuning the step size gives expected accuracy \(\tau\) in

\[
O\!\left(\left[(1+\sigma_m^2)\sqrt{L_h/\mu}
 +\frac{\sigma_a^2}{\mu\tau}\right]\log(C_0/\tau)\right)
\]

calls. For globally \(L\)-smooth convex \(f\), first set \(h=f+\mu\|x-x_0\|^2/2\), \(\mu=\varepsilon/(4R^2)\). Its induced oracle has \(\sigma_m^2=8(\rho-1)\) and \(\sigma_a^2=2(\rho-1)\mu^2R^2\). Thus solving proximal objectives is possible despite loss of pure strong growth.

The confidence amplification of [Davis and Drusvyatskiy, COLT 2020, Theorem 3 and Corollary 4](https://proceedings.mlr.press/v125/davis20a.html) also preserves this advantage. Put \(\kappa=(L+\mu)/\mu\), \(J=\lceil\log_2\kappa\rceil\), and \(\tau\asymp\varepsilon/(J+1)\). At stage \(i\), its penalty is \(\lambda_i=\mu2^i\), center \(c_i\), and minimizer \(p_i\) of \(h+\lambda_i\|x-c_i\|^2/2\). On successful preceding stages, \(\|c_i-p_{i-1}\|\le\sqrt{2\tau/(\mu+\lambda_{i-1})}\). The Moreau-gradient Lipschitz bound gives

\[
\|\nabla h(p_i)\|\le\|\nabla h(p_{i-1})\|
 +\lambda_i\sqrt{2\tau/(\mu+\lambda_{i-1})},
\]

starting from \(p_{-1}=\arg\min h\) and \(\lambda_{-1}=0\). Geometric summation yields \(\|\nabla h(p_i)\|^2=O(\lambda_i\tau)\) and \(\|p_i-\arg\min h\|=O(\sqrt{\tau/\mu})\). The stage oracle therefore has additive variance \(O((\rho-1)(\lambda_i\tau+\mu^2R^2+\mu\tau))\), not the much larger crude bound \(O(\rho\lambda_i^2R^2)\). Charging all weak-solver repetitions gives

\[
O\!\left(\rho(\sqrt\kappa+J+1)
 \log(2\kappa(J+1))\log((J+2)/\delta)\right)
\]

calls, up to universal constants, using gradients only. Accordingly, this work does not claim that accelerated high-probability accuracy under global smoothness is new. Relative-error reductions, including further nesting of the repository's [two-level construction](AcceleratedRelativeErrorConvex.md), are not complexity barriers; the mixed-noise composition above already gives a stronger global-smoothness benchmark.

The missing step for the present setup is a weak solver that retains polynomial gap-curvature dependence. AGNES requires a global smoothness constant. Even granting confinement to a known radius-\(R\) ball, replacing it by a smoothness constant on that ball can introduce an exponential loss. For example, consider the interacting objective

\[
f(x_1,x_2)=e^{a x_1}-a x_1-1+(x_1+x_2)^2/R^2,
\qquad x_0=(0,R),\quad x_\star=(0,0),\quad aR\ge1.
\]

Here \(\Delta=1\), and the target model holds with \(H_0=2a^2+2/R^2\), \(H_1=2a^2\). An oracle returning twice either component gradient with equal probability satisfies strong growth with \(\rho\le12(aR)^2\), by the smallest-singular-value bound for the feature rows \((a,0)\) and \((1/R,1/R)\). Yet the radius-\(R\) ball around \(x_0\) contains \((R,R)\), where the largest Hessian eigenvalue is at least \(a^2e^{aR}\). Substitution of such a distance-ball smoothness certificate introduces an \(e^{aR/2}\) factor, whereas the displayed new budget is polynomial in these parameters. A staged local-curvature replacement needs an additional localization argument; projection onto unknown objective sublevels cannot be assumed with this oracle. This example diagnoses the checked reduction, not a lower bound against every possible regularization method. The contribution is the joint polynomial gap-curvature, accelerated-accuracy, and logarithmic-confidence guarantee.

## Proof mechanism and formal correspondence

Use \(V=A F(x)+\|z-x_\star\|^2/2\), initially at most \(3R^2/2\). Only the proof freezes when \(V\ge8R^2\), freezing the iteration index as well. The algorithm never evaluates this condition.

Inside this region, the prior auxiliary-point construction bounds the extrapolated gap by \(16R^2/A\) without any separate bound on the primal radius. The local model gives \(512qa\|\nabla f(y)\|\le3R\). Batch variance is at most the squared true-gradient norm. If \(G=\|\nabla f(y)\|\), the actual energy increment is bounded by a random scalar \(U\) with

\[
\mathbb EU\le-11qa^2G^2,\qquad
\mathbb EU^2\le320a^2R^2G^2,\qquad |U|\le7R^2/q.
\]

With \(t=q/(64R^2)\), \(\exp(tU)\le1+tU+t^2U^2\) implies \(\mathbb E\exp(tU)\le1\). The stopped exponential energy therefore bounds exit probability by \(\exp(-13q/128)\le\delta\), without a union bound over time. A logarithmic-plus-square-root weight-growth potential yields \(A_N\ge16R^2/\varepsilon\). On nonexit the last primal gap is at most \(\varepsilon/2\); failure is contained in exit.

[`GapStrongGrowthLocalStep.lean`](../Proofs/GapStrongGrowthLocalStep.lean) derives the increment from the algorithm; [`GapStrongGrowthExponential.lean`](../Proofs/GapStrongGrowthExponential.lean) proves its moment and exponential bounds. [`GapStrongGrowthStopped.lean`](../Proofs/GapStrongGrowthStopped.lean) and [`GapStrongGrowthIteration.lean`](../Proofs/GapStrongGrowthIteration.lean) prove the measurable stopped-process argument. [`GapStrongGrowthAccuracy.lean`](../Proofs/GapStrongGrowthAccuracy.lean) transports the finite-product calculation to the arbitrary IID execution law and proves that the explicit public budget suffices. Integrability is proved by domination, not by compactness of Hilbert-space balls.

## Nonlinear instances and limitations

A meaningful interacting family is realizable Poisson regression:

\[
f(x)=\sum_{i=1}^n w_i\left[\exp(a_i^\top(x-x_\star))-a_i^\top(x-x_\star)-1\right],\qquad w_i>0.
\]

Let the dense feature matrix \(A\in\mathbb R^{n\times d}\) have full row rank, \(n\le d\), and put \(L=\max_i\|a_i\|\), \(W=\sum_iw_i\). One may take \(H_0=2L^2W,H_1=2L^2\). Uniform component-gradient sampling has strong-growth constant at most \(nL^2/\sigma_{\min}(A)^2\), by applying the smallest-singular-value bound to \(A^\top\). Multiplying sampled gradients by an independent nonnegative \(Z\) with \(\mathbb EZ=1\) and finite \(\mathbb EZ^2\) multiplies that constant by \(\mathbb EZ^2\); \(Z\) may have no exponential moments. The minimizer set can be an affine manifold. Along \(A(x-x_\star)=-s\mathbf1\), the gap grows while gradients remain bounded, so global strong convexity or a global PL condition is unnecessary. The theorem has no explicit dimension factor; instance-dependent \(\rho\) may depend on dimension and feature conditioning. Pure strong growth describes an interpolation regime, not all stochastic GLMs.

The theorem provides a high-probability guarantee, not an expected-gap bound. It assumes known curvature, growth, distance, and initial-gap certificates. The log-confidence factor is unnecessary for a noiseless oracle, and no noise-adaptive or optimal-confidence claim is made. An attained minimizer with \(H_0=0\) can make the class degenerate; no special linear-convergence claim is based on that edge case.

The literature audit was conducted on October 5, 2026 UTC, covering the publicly available ICML 2025–2026, ICLR 2025–2026 and NeurIPS 2024–2025 proceedings, public NeurIPS 2026 announcements, recent arXiv versions, and older stronger baselines. Two newly announced NeurIPS 2026 papers—*Median-of-Means under Structured Heavy-Tailed Noise* and *Normalized SGD in the Convex Regime*—were listed on an [author's publication page](https://eduardgorbunov.github.io/publications.html), and their official abstracts were obtained through the public NeurIPS 2026 Downloads export. The former studies a mixture of symmetric heavy-tailed and mean-zero moment-bounded noise through MoM bias and variance; the latter studies normalized methods under bounded central moments for smooth convex objectives. Neither abstract states a gap-dependent-curvature strong-growth result. Their full theorem statements remain inaccessible, so exact overlap beyond the abstracts remains unchecked. The full PDF of Yu and Lin's [rejected ICLR 2026 submission](https://openreview.net/forum?id=AlYT0ZD51A) was also inaccessible; its indexed primary text and public author revisions distinguish generalized-smooth sub-Gaussian results from expected-noise results under global smoothness. These are specific coverage limitations, not evidence of nonoverlap or a claim of exhaustive novelty verification.
