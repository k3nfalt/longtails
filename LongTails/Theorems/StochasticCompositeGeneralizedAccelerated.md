# Heavy-tailed acceleration for composite generalized-smooth objectives

The [Lean theorem](StochasticCompositeGeneralizedAccelerated.lean) proves a high-probability objective guarantee for minimizing

\[
F(x)=f(x)+\psi(x),\qquad x\in Q,
\]

using stochastic gradients of \(f\) and an exact proximal oracle for \(\psi+\iota_Q\). Its contribution is the combination of general nonlinear composite objectives, finite central moments, a polynomial generalized-smooth transient, and an additive statistical cost. Acceleration, affine shifting, clipping, and robust pilot estimation are established ingredients. Formal verification supports correctness; it is not the novelty claim.

## Exact model

The [setup](../Setups/StochasticCompositeGeneralizedSmooth.lean) uses a separable complete real inner-product space, including every finite-dimensional Euclidean space. The differentiable convex function \(f\) has a continuous gradient and satisfies the global symmetric segment condition

\[
\|\nabla f(x)-\nabla f(y)\|
 \le (L_0+L_1 M)\|x-y\|
\]

whenever every gradient on the segment from \(x\) to \(y\) has norm at most \(M\). Here \(L_0>0\) and \(L_1\ge0\). This is the symmetric generalized smoothness model used in the generalized-smooth acceleration literature below, not a global Lipschitz-gradient assumption. It is imposed outside the feasible set as well as inside it.

The set \(Q\) is convex and Borel. The real-valued measurable function \(\psi\) is convex on \(Q\). For every \(a>0,z,v\), the proximal oracle returns an attained minimizer in \(Q\) of

\[
\frac{\|u-z\|^2}{2a}+\langle v,u-z\rangle+\psi(u).
\]

Its positive-step input/output map is measurable. Exact prox access is an assumption, not a claim that every such subproblem is computationally cheap. The domain need not be bounded. A minimizer \(x_\star\in Q\) satisfies

\[
\|x_0-x_\star\|\le R,\quad F(x_0)-F(x_\star)\le\Delta,
\quad\|\nabla f(x_\star)\|\le G,
\]

where \(R,\Delta>0\), \(G\ge0\), and the initial point satisfies \(x_0\in Q\). Nonzero optimal smooth-component gradients and boundary minimizers are permitted.

For \(1<\alpha\le2\) and \(\sigma\ge0\), the jointly measurable gradient oracle satisfies, at every point,

\[
\int g(x,\omega)\,d\mu(\omega)=\nabla f(x),\qquad
\int\|g(x,\omega)-\nabla f(x)\|^\alpha\,d\mu(\omega)\le\sigma^\alpha.
\]

Vector integrability and integrability of the displayed moment are explicit. Samples are IID under an abstract probability law with measurable coordinates, independence, and marginal law \(\mu\). The proof derives the required product-law representation internally. There is no finite-sample-space, bounded-noise, light-tail, samplewise smoothness, sampled-value, or paired-gradient requirement.

The algorithm knows \(L_0,L_1,R,\Delta,\sigma,\alpha,\varepsilon,\delta,x_0\), with \(\varepsilon>0\) and \(0<\delta<1\). The analysis parameter \(G\) is excluded from its public inputs. This is not a parameter-free result. No restriction to a prescribed algorithm family is imposed on the problem specification.

## Algorithm and returned point

The [algorithm](../Algorithms/StochasticCompositeGeneralizedAccelerated.lean) maintains accelerated primal and proximal points \(x,z\) and weight \(A\), initially \(x=z=x_0\) and \(A=R^2/(4\Delta)\). Put

\[
\ell_k=\log\frac{64e(k+1)^2}{\delta}.
\]

Each active iteration uses two independent robust pilots, each of size \(\max\{1,\lceil16\ell_k\rceil\}\). The first estimates the gradient at \(x\), producing
\(M=L_0+L_1(\|\widehat g_x\|+96\sigma)\). Set

\[
a=\min\left\{\frac{1+\sqrt{1+16MA}}{8M},\frac{A}{1+64L_1R}\right\},
\qquad y=\frac{Ax+az}{A+a}.
\]

The second pilot estimates \(\nabla f(y)\). Fresh gradients at \(y\) are clipped around this pilot center with radius

\[
\lambda_k=\max\{384\sigma,\;2(2^{20}\sigma^\alpha R\ell_k/\varepsilon)^{1/(\alpha-1)}\},
\qquad V_k=(2\lambda_k)^{2-\alpha}\sigma^\alpha.
\]

Their clipped mean \(\widehat g_y\) uses

\[
m_k=\max\left\{1,\left\lceil2^{40}
\left(\frac{V_ka\ell_k^2}{\varepsilon}+\frac{\lambda_ka\ell_k^2}{R}\right)\right\rceil\right\}
\]

samples. One exact proximal call gives \(z^+=\operatorname{prox}_{a,\psi+\iota_Q}(z-a\widehat g_y)\); then
\(x^+=(Ax+az^+)/(A+a)\) and \(A^+=A+a\). The implementation freezes after a completed proximal step with \(A^+\ge4R^2/\varepsilon\), or immediately if \(\Delta\le\varepsilon\). Its returned output is the last stored accelerated primal point \(x\), not a retrospective best iterate. After freezing, any remaining budgeted calls are dummy gradient calls and preserve the output. Partial batches on exceptional paths also have a defined output.

## Proved guarantee and complete budget

For concise presentation define

\[
\bar L=L_0+L_1G,\quad L_s=\bar L+192L_1\sigma,\quad
q=\frac1{\alpha-1},\quad r=\frac\alpha{\alpha-1},
\]
\[
t=L_1R,\quad z=\frac{L_sR^2}{\varepsilon},\quad
d=\frac\Delta{L_0R^2},\quad v=\frac{\sigma R}{\varepsilon},\quad
H=\frac{8+t+z+d+v}{\delta}.
\]

The public Lean `budget` is one explicit formula in the setup parameters, without these abbreviations:

\[
B=\left\lceil
2^{128+128q}
\left[1+\sqrt z+(1+t)\log\bigl(2+(1+t)\sqrt d\bigr)+v^r\right]
(\log H)^{2+q}
\right\rceil.
\]

Running the named algorithm through the repository's `execute` for this budget returns a measurable output satisfying

\[
\mathbb P\{x_{\rm out}\notin Q\ \text{or}\ F(x_{\rm out})-F(x_\star)>\varepsilon\}\le\delta.
\]

The probability is the explicit algorithm/oracle joint law in the setup. The budget counts **every gradient sample and every proximal call**, both pilots, evaluation batches, and frozen padding. There is no omitted inner solver or noiseless-gradient query.

For fixed \(\alpha>1\), the parameter dependence, suppressing the displayed logarithmic factor, is

\[
\widetilde O_\alpha\!\left(
1+\sqrt{\bar L R^2/\varepsilon}
 +(1+L_1R)\log\!\left(2+(1+L_1R)\sqrt{\Delta/(L_0R^2)}\right)
 +(\sigma R/\varepsilon)^{\alpha/(\alpha-1)}
\right).
\]

Indeed \(\sqrt{192tv}\le7(t+v)\) and \(v\le1+v^r\), so the extra \(192L_1\sigma\) inside \(L_s\) is absorbed by the transient and statistical terms. The explicit constants and logarithmic exponent deteriorate as \(\alpha\downarrow1\); this is not an alpha-uniform bound. The constants are conservative proof constants, not practical tuning recommendations.

## Mathematical mechanism

The main issue is controlling a noisy accelerated **proximal** trajectory under curvature that grows with the smooth-component gradient. A global localization ball followed by a fixed-Lipschitz composite theorem can incur exponential dependence on \(L_1R\).

The proof instead derives local descent from the current composite energy and a weighted estimator-error bound before asserting the next energy bound. At evaluation phases it charges a predicted potential with the actual signed error and squared error; the following prox phase decreases that ledger. A joint induction closes the energy and local-curvature conditions without assuming a successful trajectory. Signed-error stopping retains the whole threshold-crossing batch, preventing a post-batch selection bias. Predictable batching and the all-path bound \(\sum a\le8R^2/\varepsilon\) make the statistical cost additive rather than multiplying the optimization iteration count.

A shifted-gradient comparison handles nonstationary composite minimizers. Curvature-controlled weight growth proves termination within four phases per iteration, with

\[
K=\left\lceil20\sqrt z+(6+256t)\log\bigl(2+(3+192t)\sqrt d\bigr)\right\rceil.
\]

The [growth proof](../Proofs/StochasticCompositeGeneralizedGrowth.lean) connects this count to completed proximal updates and actual execution. The [cost proof](../Proofs/StochasticCompositeGeneralizedCost.lean) bounds all paths, including failed and frozen paths, and proves the simpler public budget sufficient. The [convergence proof](../Proofs/StochasticCompositeGeneralizedConvergence.lean) connects the good-event argument to the returned output under the abstract IID law. These arguments cover nonlinear interacting coordinates, not only scalar recurrences or quadratics.

## Closest results and the remaining gap

The literature comparison was checked through **3 November 2026**, including the latest versions below and follow-up/correction searches. It supports a specific extension, not a universal priority or optimality claim.

* **Unconstrained generalized-smooth heavy-tail acceleration.** [El Bakkali El Kadi–Gorbunov, arXiv:2610.23301v2, Theorem 2 and Appendix C](https://arxiv.org/html/2610.23301v2) already establishes the central acceleration/heavy-tail combination for unconstrained smooth minimization. The new scope here is arbitrary supplied composite prox structure, including nonsmooth penalties and boundary minimizers, while retaining polynomial curvature dependence and additive statistical cost. This October 2026 source is an arXiv preprint, not an accepted-conference claim. We do not improve its unconstrained guarantees or claim a new acceleration paradigm.

* **Composite heavy-tail acceleration with fixed local smoothness.** [Gorbunov et al., arXiv:2310.01860v2, Theorem 2.7 and Assumptions 1.1–1.3](https://arxiv.org/pdf/2310.01860v2), published at ICML 2024, already permits a general composite prox and nonzero optimal component gradients. In its single-worker specialization, the relevant cost is, up to logarithms, \(\sqrt{L R^2/\varepsilon}+\sqrt{RG/\varepsilon}+(\sigma R/\varepsilon)^r\). Its fixed local Lipschitz and shifted-cocoercivity conditions on a radius-\(5\sqrt2R\) ball can be obtained from the present model with a local constant growing exponentially in \(L_1R\). Our guarantee replaces that direct reduction's exponential dependence with the explicit polynomial transient above. Removing the standalone shift term alone is not claimed as novelty: robust centering may already achieve that.

* **Other nearby models.** [Ji–Lan, arXiv:2604.06525v2, Assumption 2, equation (3.7), and Theorems 3.1/3.4](https://arxiv.org/html/2604.06525v2) retains an empirical cocoercivity condition and richer sampled-value/common-sample gradient information. These are not implied by the gradient-only moment oracle here. [He–Li–Lu, arXiv:2510.11676v2, Assumption 1 and Theorem 2](https://arxiv.org/html/2510.11676v2) uses a bounded proximal domain and global hybrid gradient modulus; its finite-moment confidence dependence differs. Neither theorem supplies the exact model/rate combination proved here. These are comparisons with the stated preprint versions, not assertions of conference acceptance.

* **Generalized-smooth benchmarks.** [Tyurin, ICML 2026](https://proceedings.mlr.press/v306/tyurin26b.html) and [Yu et al., ICML 2026](https://proceedings.mlr.press/v306/yu26s.html) establish important deterministic acceleration and generalized-smooth mirror-descent results. In [Yu et al. v4, Theorems 4.2 and 5.1](https://arxiv.org/html/2502.00753v4), the relevant stochastic objective guarantee is nonaccelerated and the composite result is a deterministic nonconvex mapping guarantee. The proximal subproblems in [ARC-SG, arXiv:2609.06555v1, Theorems 1–2](https://arxiv.org/pdf/2609.06555v1) regularize an unconstrained smooth objective; they are not arbitrary external composite prox access, and its noise is norm-subGaussian.

Affine tilting deserves an explicit qualification. Subtracting \(\langle\nabla f(x_\star),x\rangle\) from \(f\) and adding it to \(\psi\) cancels exactly in a proximal linearization. Thus not knowing this vector is not, by itself, a novelty argument. But this does not turn a nonsmooth constrained composite problem into the smooth unconstrained problem of the October theorem. Extending that proof through the noisy proximal displacement and dynamic curvature argument is the substantive task performed here. Likewise, robust mini-batching alone is not new; uniformly accurate batches at every deterministic iteration need not preserve the additive oracle cost proved here.

The improvement over the fixed-local-L reduction matters when \(L_1R\) is large and the common statistical term does not mask the curvature cost. For example, with fixed \(\alpha\), zero or sufficiently small noise, and the other displayed dimensionless quantities polynomial in \(1+L_1R\), this budget is polynomial up to logarithms whereas the direct ball-localization guarantee is exponential. This is a comparison of proved upper bounds, not a lower bound on the earlier algorithm. For \(L_1=0\), the familiar accelerated/statistical powers are already known. No new smooth-subclass rate is claimed.

## Meaningful instances and limitations

A nonlinear family is exponential-risk minimization with a sparsity penalty and a convex trust region. Let
\(f(x)=\sum_i c_i e^{\langle a_i,x\rangle}\), \(c_i>0\), with non-axis-aligned rows \(a_i\) of norm at most \(A\). If a unit vector \(u\) satisfies \(\langle a_i,u\rangle\ge b>0\), then
\(\|\nabla^2f(x)\|\le A^2\sum_i c_i e^{\langle a_i,x\rangle}\le(A^2/b)\|\nabla f(x)\|\).
Hence the symmetric condition holds with \(L_1=A^2/b\) and any positive \(L_0\). Nonnegative-feature exponential risks provide such cones when the row projections have a positive lower bound. A nonempty compact convex trust region and \(\psi(x)=\tau\|x\|_1\), \(\tau\ge0\), give attained minimizers and proximal subproblems; the model assumes exact access to the latter. Nonorthogonal rows couple coordinates. Additive centered noise with finite alpha moment supplies the stated oracle. The theorem does not add a dimension factor; dimension may enter through \(A/b,R,G,\sigma\) and the cost of implementing the supplied prox. The cone condition describes this example family, not an extra hypothesis of the theorem.

Global smoothness and global moment control, exact measurable prox access, and known initial-distance/gap and noise bounds remain material assumptions. The result does not cover arbitrary extended-real nonmeasurable penalties, dependent sampling, inexact prox, biased gradients, or merely feasible-set-local smoothness. There is no lower bound establishing necessity of the \(G\), transient, or logarithmic factors. Sharper unconstrained transients and better logarithmic/constants are possible in other analyses; this theorem does not claim global minimax optimality or universal superiority.
