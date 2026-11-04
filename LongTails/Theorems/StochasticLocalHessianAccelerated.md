# Accelerated stochastic optimization under local Hessian variation

The [Lean theorem](StochasticLocalHessianAccelerated.lean) constructs [NoisyDampedNewton.algorithm](../Algorithms/NoisyDampedNewton.lean) for the [StochasticLocalHessianConvex specification](../Setups/StochasticLocalHessianConvex.lean). This is a second-order oracle-complexity result for general nonlinear convex objectives in arbitrary finite dimension. It permits finite-variance stochastic gradients and a deterministic inexact full Hessian. It does not restrict the admissible algorithm family.

## Problem and information

Let $f:\mathbb R^d\to\mathbb R$ be convex and $C^2$, with a minimizer $x_\star$. Public upper bounds satisfy $\|x_0-x_\star\|\le R$ and $f(x_0)-f$x_\star$\le\Delta$. For every $x,y$ with $\|y-x\|\le\rho$, assume

\[
\|\nabla^2f(y)-\nabla^2f(x)\|
 \le (M_0+M_1\|\nabla f(x)\|)\|y-x\|.
\]

Here $M_0,M_1,\delta,\sigma\ge0$, $R,\Delta,\rho,\epsilon>0$, and $0<\beta<1$. The algorithm knows these bounds, but neither the minimizer nor the objective function. A zero initial gap can be covered by any positive upper bound; if the supplied bound is at most \(\epsilon\), the initial point is returned.

The gradient channel returns $g(x,\omega)$, jointly measurable in both arguments, with
\(\mathbb E g(x,\omega)=\nabla f(x)\) and
\(\mathbb E\|g(x,\omega)-\nabla f(x)\|^2\le\sigma^2\).
The specification includes the required integrability. Samples are IID under an abstract probability law, using the repository's IID structure; the internal product-law representation is derived from independence. No bounded samples, exponential tails, samplewise smoothness, bounded domain, or uniform bound on Hessian magnitude is assumed.

The second channel returns a fixed measurable operator $H(x)$ with
\(\|H(x)-\nabla^2f(x)\|\le\delta\).
It need not be symmetric. This is a deterministic inexact-Hessian model, not an unbiased random Hessian or an arbitrary history-dependent adversary. Both channels consume a stream coordinate, including the unused random coordinate on a Hessian call. One full matrix reply counts as one Hessian call. Matrix arithmetic, inverses, and algebraic backtracking are free in this oracle model; no running-time or Hessian-vector-product bound is claimed.

The local variation assumption and inexact Hessian model originate in [Agafonov et al., arXiv:2609.32977v1, assumptions LH/IH and Theorem 4.1](https://arxiv.org/html/2609.32977v1). The unbiased finite-variance gradient assumption is standard, including [Agafonov et al., arXiv:2309.01570v3, Assumptions 1.2 and 2.3](https://arxiv.org/html/2309.01570v3). Measurability makes these oracle operations and probabilities well-defined. Known parameter bounds and the fixed map $H$ are limitations of the implemented result. No assumption asserts convergence, estimator accuracy along the realized path, or bounded cumulative errors.

## Guarantee and algorithm

Write
\[
S=1+(M_1R^2)^{1/3}+(R/\rho)^{2/3}
 +(M_0R^3/\epsilon)^{2/7}+\sqrt{\delta R^2/\epsilon},\qquad
V=\sigma^2R^2/\epsilon^2,
\]
\[
X=2+\Delta/\epsilon+\delta R^2/\epsilon+M_0R^3/\epsilon
  +M_1R^2+(R/\rho)^2+1/\beta+V.
\]
The public budgets are
\[
B_g=\lceil2^{80}(S+V)\log^3X\rceil,
\qquad B_H=\lceil2^{80}S\log^3X\rceil.
\]
They appear expanded in the Lean `budget` definition. The named `NoisyDampedNewton.output` is the output of the repository's `execute`, with those two budgets. The theorem proves its measurability and
\[
\Pr\{f(\mathrm{output})-f$x_\star$>\epsilon\}\le\beta.
\]
The output is the algorithm's maintained accelerated convex mixture, not a uniformly selected iterate or the raw Newton trial. On unsuccessful sample paths no objective-gap moment bound is asserted.

Each active cycle computes a robust grouped pilot gradient at the extrapolated point, queries one Hessian there, and solves a regularized linear system with $H+\delta I+\tau I$. Dyadic algebraic backtracking selects a displacement satisfying observable radius and curvature certificates. It does not request gradients or objective values during backtracking. A separate batch at the trial point is clipped about the model center $-\tau s$. This correction updates the accelerated momentum; damping adjusts both the primal mixture and its weight. The algorithm stops updating once its accumulated weight reaches the specified threshold. Budgeted execution can pad gradient calls afterwards without changing the output. Partial batches return the preceding mixture. The proof counts all model samples, correction samples, Hessian replies, and execution padding.

## Contribution and comparisons

The proposed contribution is a finite-variance, value-free second-order implementation retaining the $2/7$ accuracy exponent of accelerated Hessian methods, with separate Hessian and total gradient costs, under local gradient-dependent Hessian variation. It is not the first stochastic acceleration, stochastic Monteiro–Svaiter framework, clipping argument, or additive statistical oracle bound.

The closest stochastic baseline is [Agafonov et al., Theorem 3.2 and Appendix E.7, v3](https://arxiv.org/html/2309.01570v3), accepted at [ICLR 2024](https://proceedings.iclr.cc/paper_files/paper/2024/hash/8fd1a81c882cd45f64958da6284f4a3f-Abstract-Conference.html). Under globally Lipschitz Hessian it gives expected gap of order
\(\sigma R/\sqrt T+\delta R^2/T^2+M_0R^3/T^3\).
Batching its two gradient queries per iteration already gives gradient cost $O(T+\sigma^2R^2/\eta^2)$, with $T=O(1+\sqrt{\delta R^2/\eta}+(M_0R^3/\eta)^{1/3})$, and $O(T)$ Hessian calls. Take batch size of order \(\max\{1,\lceil\sigma^2R^2/(\eta^2T)\rceil\}\), and sufficiently accurate local-model solves. Setting \(\eta=\beta\epsilon\) gives comparable probability via Markov. Symmetrizing our full Hessian reply preserves its error and costs no oracle calls. Thus neither additive gradient-noise cost nor absence of a polynomial noise term in Hessian cost is new by itself.

On the common global-Hessian-Lipschitz subclass, at fixed confidence, $R=M_0=1$, fixed \(\rho,M_1\), \(0<\epsilon\le1\), \(\delta\le\epsilon^{3/7}\), and \(0<\sigma^2\le\epsilon^{12/7}\), the new upper bound is \(\widetilde O(\epsilon^{-2/7})\), compared with that batched upper bound's \(O(\epsilon^{-1/3})\). This is a comparison of guarantees, not a lower-bound separation for the older algorithm. When statistical error dominates, no strict improvement in the leading total gradient cost is claimed. The new result also covers local Hessian variation outside the global Lipschitz class. A high-probability bound alone does not imply the baseline's expected guarantee.

[Agafonov et al., 2609.32977v1, Theorem 4.1](https://arxiv.org/html/2609.32977v1) supplies the deterministic local-variation baseline with the same polynomial shape. [Optimal Convex Optimization with Inexact Second-Order Oracles, 2607.24520v3, Theorem 3.1](https://arxiv.org/html/2607.24520v3) also attains the $2/7$ exponent and square-root Hessian-error term in the global case. Their exact-gradient residual and momentum steps do not give the finite-variance total-gradient guarantee here. We pay logarithmic factors and require known tuning parameters; no deterministic-rate or adaptivity improvement over those results is claimed.

## Technical mechanism and reduction checks

The proof combines three linked steps. First, a reverse local Taylor estimate certifies
\(\|\nabla f(y)+\tau s\|\le\alpha\tau\|s\|+2e_1\)
from the observable model certificate and pilot error $e_1$, without any Hessian spectral bound. Second, model errors are paid by the *proposed* acceleration weight, while correction variance is paid by the *actual damped* weight. A telescoping ledger bounds both sums, preventing rejected/damped proposals from silently multiplying the statistical cost. Third, a finite-prefix dyadic-curvature count converts the energy dissipation into the $2/7$ stopping and oracle bounds. It proves completion from any still-active prefix rather than assuming completion to bound its cost.

The centered clipping and stopped exponential argument control the random energy and pilot failures. They are supporting ingredients, not standalone novelty claims. [Carmon et al., NeurIPS 2022, supplementary Appendix C, Definitions 3–4 and Theorem 6](https://proceedings.neurips.cc/paper_files/paper/2022/file/7ff97417474268e6b5a38bcbfae04944-Supplemental-Conference.pdf) already provides stochastic damped Monteiro–Svaiter machinery. Its unbiased exact-proximal-gradient oracle is not supplied by a clipped gradient at a single Newton trial, even for a nonlinear noiseless objective. A direct plug-in therefore does not prove the implementation or its cost. Existing debiasing/RECAPP reductions require an independently justified proximal implementation; their bounded-gradient, function-value, finite-sum or sample-smooth implementations cannot simply be presumed under this oracle. [RECAPP, ICML 2022, Definition 3.1 and Proposition 3.4](https://proceedings.mlr.press/v162/carmon22a.html) is an abstract reduction rather than that missing implementation.

Uniformly batching every deterministic iteration to gradient accuracy \(\epsilon/R\) would multiply the iteration count by the statistical sample requirement. The proposal/actual-weight ledger avoids that multiplication. Conversely, the stronger batched stochastic baseline above already avoids it with exponent $1/3$; comparison only with naive deterministic batching would overstate the contribution. First-order localization using a uniform gradient-smoothness constant can introduce Hessian-magnitude dependence absent from the stated bound. [2610.23301v2](https://arxiv.org/html/2610.23301v2) already uses high-probability stopping/clipping in generalized first-order smoothness; those devices are not claimed here as new.

## Instances, scope, and limitations

An interacting nonlinear family is
\(f_\lambda(x)=\lambda(a^Tx)^2/2+[\log\cosh(b_1^Tx)+\log\cosh(b_2^Tx)]/4\),
with $a=(1,2)/\sqrt5$, $b_1=(1,0)$, $b_2=(1,1)/\sqrt2$, and \(\lambda\ge0\). Its minimizer is zero and its Hessian-Lipschitz constant is at most one independently of \(\lambda\); its Hessian magnitude grows with \(\lambda\). Take $x_0=e_1,R=1,\Delta=\lambda+1,\rho=1,M_0=1,M_1=0$, additive mean-zero finite-variance gradient noise, and $H=\nabla^2f+\delta I$. Nonorthogonal directions produce interacting curvature. In arbitrary dimension, sums of such nonorthogonal ridge functions and positive semidefinite quadratic forms give the same phenomenon, with explicit bound $M_0\le2\sum_j w_j\|b_j\|^3$. These examples establish meaningful nonlinear scope and the distinction from Hessian-magnitude assumptions; they are not worst-case lower-bound constructions. The theorem itself has no explicit dimension factor for full-Hessian access and Euclidean norm variance; those parameters may depend on dimension in an application.

A family genuinely outside global Hessian Lipschitzness is $f(x)=\sum_{i=1}^d\cosh((Ax)_i)$ for an invertible matrix $A$ with nonorthogonal rows (for example, $A=[[1,0],[1,1]]$). It is convex, smooth, coupled, and uniquely minimized at zero. For any finite $\rho$, the local variation condition holds with $M_0=\|A\|^3e^{\|A\|\rho}$ and $M_1=M_0\|A^{-T}\|$. Indeed, along the segment from $x$ to $y$, $\max_i\cosh((Az)_i)\le e^{\|A\|\rho}(1+\|\sinh(Ax)\|_2)$, while $\sinh(Ax)=A^{-T}\nabla f(x)$ and $\|D\nabla^2f(z)[h]\|\le\|A\|^3\max_i|\sinh((Az)_i)|\|h\|$. Integration gives the stated bound. Hessian variation is unbounded along rays, so no finite global Hessian-Lipschitz constant exists. This example illustrates the additional objective scope, not a worst-case complexity construction.

The constants and logarithmic powers are conservative. The Hessian budget contains logarithmic dependence on noise through $X$. At zero noise the method still uses pilot groups and recovers deterministic exponents only up to logarithms. The result does not cover composite constraints, nonconvex stationarity, random Hessians, unknown-parameter adaptation, or expected error without additional analysis.

The main proof is [NoisyNewtonConvergence](../Proofs/NoisyNewtonConvergence.lean); [NoisyNewtonCounting](../Proofs/NoisyNewtonCounting.lean) and [NoisyNewtonCost](../Proofs/NoisyNewtonCost.lean) connect finite-prefix accounting to actual execution. The setup retains general $C^2$ convex nonlinear objectives throughout. Literature screening covered publicly available ICML, ICLR, and NeurIPS 2025–2026 material and roughly November 2024–November 2026 arXiv work, with foundational citations followed. Version checks were refreshed on 2026-11-04 UTC. The 2026 arXiv comparisons above are treated as preprints unless conference status is independently established. Search coverage is not a proof of novelty; the substantive claim requires independent review of the implementation and strongest applicable reductions.
