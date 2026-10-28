# Inertial extragradient for stochastic monotone roots

The [main theorem](InertialMonotoneResidual.lean) proves an oracle complexity of

\[
K=\left\lceil 2^{22}\left(1+\frac{LR}{\varepsilon}
 +\frac{\sigma^2}{\varepsilon^2}\log^2\!\left(2+\frac{LR}{\varepsilon}\right)\right)\right\rceil
\]

for a terminal output satisfying \(\mathbb E\|F(z_N)\|^2\leq\varepsilon^2\). The contribution is a stochastic residual guarantee for general monotone Lipschitz operators with regularity imposed only on the mean operator. It saves one logarithmic factor in the statistical oracle cost relative to the closest general mean-only guarantees, while retaining the linear deterministic dependence on \(LR/\varepsilon\). It does not establish minimax optimality or a practical improvement with the displayed constants.

## Problem and information

The [setup](../Setups/StochasticLipschitzMonotone.lean) specifies a finite-dimensional real Hilbert space, a globally monotone, globally \(L\)-Lipschitz map \(F\), and a root \(x_*\) with \(\|x_0-x_*\|\leq R\). Here \(L>0\), \(R,\sigma\geq0\), and \(\varepsilon>0\). The algorithm knows these bounds and \(x_0\), but neither the root nor the mean operator. Each call at \(x\) returns \(g(x,\xi)\), with jointly measurable \(g\), integrable responses, \(\mathbb E g(x,\xi)=F(x)\), and \(\mathbb E\|g(x,\xi)-F(x)\|^2\leq\sigma^2\). Samples are IID under an abstract probability law; their space need not be finite. No individual sample map must be continuous, monotone, or Lipschitz. There is no same-sample requery or resolvent oracle.

These are established stochastic variational-inequality assumptions: compare [Juditsky, Nemirovski and Tauvel, §3.2, Assumption I](https://www2.isye.gatech.edu/~nemirovs/SMP.pdf), and the mean-only assumptions of the RRSEG paper below. The root and initial-radius assumptions replace compact-domain gap guarantees with unconstrained residual accuracy. Uniform variance is a real restriction; state-dependent variance, dependent samples, constraints and composite inclusions are not covered here. The specification places no artificial restriction on competing algorithms.

## Algorithm and actual cost

The [algorithm](../Algorithms/InertialRegularizedExtragradient.lean) uses

\[
N=\lceil4096+2048LR/\varepsilon\rceil,\quad
 t_k=N+128-k,\quad \mu_k=128LN/t_k^2,
\]
\[
r_k=2[(t_k/(t_k-1))^2-1],\quad \eta_k=2r_k/\mu_k,\quad
 b_k=\max\{1,\lceil4096\sigma^2(1+\log(N+128))/(\varepsilon^2(t_k-1))\rceil\}.
\]

Starting with \(x=z=x_0\), at each \(k<N\) take two disjoint fresh batches of size \(b_k\), denoted by averages \(G_1,G_2\), and set

\[
y=z-\eta_k[G_1(z)+\mu_k(z-x)],\qquad
w=z-\eta_k[G_2(y)+\mu_k(y-x)],
\]
\[
x^+=x+\frac{3r_k}{2(2+r_k)}(w-x),\qquad
z^+=x+\frac{4+3r_k}{2(2+r_k)}(w-x).
\]

The returned point is \(z_N\), not an average or a point selected using unknown residuals. It need not itself have been queried. There are exactly \(2\sum_{k<N}b_k\) useful raw oracle calls. The repository's `execute` pads to the public budget without changing this output; those calls are included in \(K\). The proved bounds are

\[
2\sum b_k\leq2N+8192(\sigma/\varepsilon)^2(1+\log(N+128))^2\leq K.
\]

Thus batching has not been treated as a unit-cost oracle. This is a finite-horizon, parameter-tuned algorithm, not an anytime or fixed-number-of-raw-queries-per-update result.

## Mathematical mechanism

For analysis only, let \(p\) solve \(F(p)=\mu(x-p)\). Existence and uniqueness follow from monotonicity, continuity and positive regularization. Define
\(\Psi=\mu^2\|z-p\|^2+\|F(p)\|^2\).
A fresh two-stage extragradient response to \(H(z)=F(z)+\mu(z-x)\) satisfies

\[
\mathbb E[\|w-p\|^2\mid x,z]\leq(1-\eta\mu)\|z-p\|^2+3\eta^2\sigma^2/b
\]

when \(2\eta\mu+2\eta^2(L+\mu)^2\leq1\). With \(\eta=2r/\mu\) and \(r\leq1/16\), its corrected response \(S=\mu(1+r)(w-p)\) obeys
\(\mathbb E\|S\|^2\leq\mu^2\|z-p\|^2+14r^2\sigma^2/b\).
The observable affine updates above and \(\mu^+=\mu(1+r/2)\) then imply

\[
\Psi^+\leq\|S\|^2+\|F(p)\|^2,\qquad
\mathbb E\Psi_N\leq\Psi_0+14\sum_{k<N}r_k^2\sigma^2/b_k.
\]

The root-transport algebra is inherited from [Yang et al., arXiv:2609.28543v1, Appendix B.4.5, equation (179)](https://arxiv.org/html/2609.28543v1). It is not a new inequality here. The new step is an observable, affine-corrected fresh extragradient response that satisfies this energy inequality using mean monotonicity and Lipschitz continuity, replacing their cocoercive response estimate (183). The raw extragradient map is not assumed nonexpansive. Strongly monotone extragradient contraction and finite-batch variance reduction are established ingredients.

The schedule proves \(\eta L\leq1/4\), \(\eta\mu\leq1/8\), and hence the contraction condition. It also gives \(\mu_N\geq L\), \(\mu_0R\leq\varepsilon/16\), and \(\sum r_k^2\sigma^2/b_k\leq25\varepsilon^2/4096\). Consequently

\[
\mathbb E\|F(z_N)\|^2\leq2\mathbb E\Psi_N
 \leq(191/1024)\varepsilon^2\leq\varepsilon^2.
\]

The argument controls the adaptive second query using its fresh batch, rather than asserting independence of that query point and the first batch. Nonnegative integrable envelopes establish integrability before Fubini. The formal proof derives finite-prefix product laws from the public abstract IID assumption and connects every batch to the actual query plan and `execute`.

## Closest guarantees and precise scope of improvement

Write \(\kappa=LR/\varepsilon\) and \(V=\sigma^2/\varepsilon^2\). Logarithms below are understood with a positive offset; comparisons concern asymptotic orders, not constants.

| Primary result | Guarantee and access | Relation to this result |
|---|---|---|
| [Chen and Luo, JMLR 25(387), 2024, RAIN](https://www.jmlr.org/papers/v25/22-1126.html) | Recursive regularization for stochastic minimax residuals; the expected-squared-residual conversion is explicitly derived in RRSEG Appendix A.1, with order \(\widetilde O(\kappa)+O(V\log^3(2+\kappa))\); JMLR Theorem 4.2 retains a deterministic iterated-logarithm factor. | The applicable mean-only statistical term loses one logarithm here. RAIN has extensions outside the present monotone root setup. |
| [Lee and Kim, arXiv:2609.35631v1, Theorem 6.1 and Corollary 6.2](https://arxiv.org/html/2609.35631v1) | RRSEG: squared residual \(O(L^2R^2/T^2+\sigma^2\log^3T/T)\), with two fresh raw calls per update; includes composite inclusions. | Same mean-only root class when the composite part is zero. This result improves statistical total cost using growing batches; it does not solve their fixed-query-per-update problem. Their VRAF needs stronger same-sample noise regularity and has a different deterministic tradeoff. |
| [Ji, Lan and Zhu, arXiv:2609.04188v2, §2.3, Theorem 2.2](https://arxiv.org/html/2609.04188v2) | Accumulative regularization gives squared strong residual accuracy; its uniform-noise specialization has a cubic-log statistical term, with further logarithmic factors in the stated complexity. | This result sharpens the unconstrained uniform-variance specialization. Their constrained, state-dependent-noise and high-probability results are not subsumed. |
| [Yang et al., arXiv:2609.28543v1](https://arxiv.org/html/2609.28543v1) | Stochastic inertial Krasnosel'skii–Mann iteration for nonexpansive maps has residual \(O(T^{-1}+\sigma\log T/\sqrt T)\), with a bias term when present. | Its direct operator interpretation requires cocoercivity, which general monotone Lipschitz maps lack. This result extends the inertial energy mechanism to that larger class using two fresh batched queries. |
| [Yoon and Loizou, arXiv:2609.36033v1, Corollary 3.6](https://arxiv.org/html/2609.36033v1) | Dual-anchor acceleration has order \(\kappa\log(2+\kappa)+V\log^2(2+\kappa)\), with samplewise monotonicity, uniform sample Lipschitz continuity and same-sample access. | Here the mean-only class is larger, fresh samples suffice, and the deterministic logarithm is absent. No claim is made about their other tradeoffs. |

The gain is meaningful as \(\kappa\to\infty\) when the statistical term matters, for example with fixed positive \(L,R,\sigma\) and \(\varepsilon\downarrow0\). If \(V\log^2(2+\kappa)\gg\kappa\), the comparison with a cubic-log statistical baseline saves a full logarithmic factor. At bounded \(\kappa\) there is no asymptotic logarithmic separation. When \(\sigma=0\), the cost is \(O(1+\kappa)\). The deterministic black-box lower bound in [Yoon and Ryu, ICML 2021, Theorem 4](https://proceedings.mlr.press/v139/yoon21d.html) explains this dependence in its stated deterministic, sufficiently high-dimensional regime; it is not asserted as a randomized lower bound. No optimal logarithmic exponent is proved here.

### Why direct reductions do not already give the bound

Batching the cubic-log guarantees reduces variance and multiplies raw cost by the batch size, preserving their statistical logarithm. Replacing \(F\) by a fixed resolvent makes a nonexpansive map but changes the oracle: a raw unbiased response for \(F\) is not an unbiased resolvent response. A standard strongly monotone inner solve with root RMS error \(\delta_k\) costs order \(\sigma^2/(L^2\delta_k^2)\). Treating that error as bias in iKM requires a weighted error sum. For weights \(r_k\), minimizing this certificate under \(\sum r_k\delta_k\leq e\) gives \((\sum r_k^{2/3})^3/e^2\); the source schedule yields an extra horizon factor. This is a limitation of that reduction, not an impossibility theorem for all resolvent implementations.

An unbiased-resolvent shortcut also needs additional justification. For a scalar piecewise-linear strongly monotone map whose inverse is \(h(s)=cs+d|s|\), \(d\ne0\), Gaussian sample means give an antithetic level difference with second moment \(d^2\sigma^2(1/2-1/\pi)/n\) and cost proportional to \(n\). Thus the usual single-term multilevel construction cannot have both finite variance and finite expected work. The strict decay condition in [Blanchet, Glynn and Pei, Assumption 1](https://arxiv.org/abs/1904.09929) is unavailable. Truncated bias reduction as in [Asi et al., NeurIPS 2021, Theorem 1 and §2](https://proceedings.neurips.cc/paper/2021/file/597c7b407a02cc0a92167e7a371eca25-Paper.pdf) incurs logarithmic variance and cost penalties; even granting a corresponding general monotone inner solver does not directly yield the bound above. The present algorithm never asks for a resolvent sample.

## Nonlinear scope and assumption necessity

A concrete family in every dimension \(d\geq2\) is \(F(z)=Q^\top\tanh(Qz)+Sz\), with dense invertible \(Q\) and a nonzero skew-symmetric \(S\). It is monotone and Lipschitz with \(L\leq\|Q\|^2+\|S\|\), has root zero, and has interacting nonlinear coordinates. Along a direction on which \(S\) is nonzero, the squared operator norm grows quadratically while \(\langle F(tv),tv\rangle\) grows at most linearly. Thus this class is not positively cocoercive. Adding centered Rademacher noise \(\sigma\xi\operatorname{sign}(a^\top z)u\), with unit \(u\), preserves the oracle assumptions while allowing discontinuous sample maps. This demonstrates strict separation, not an application by itself.

A population saddle problem giving a more concrete mechanism is
\[
\Phi(x,y)=\mathbb E\log\cosh(a^\top x)-\mathbb E\log\cosh(b^\top y)
 +x^\top Cy-d^\top x+e^\top y.
\]
Finite second moments of the features imply mean Lipschitz continuity and uniformly bounded gradient noise, because \(|\tanh|\leq1\). Unbounded features need not admit a uniform sample Lipschitz constant. The bilinear coupling supplies interacting coordinates. For square invertible \(C\), the saddle operator is an invertible skew linear map plus a bounded continuous perturbation, so it has a root; the theorem still requires a supplied initial-radius bound. This is a derived example, not a claim that a cited paper studied this exact model. Constants such as feature second moments may depend on dimension.

No added structural assumption repairs the proof: root existence, global mean Lipschitz continuity, monotonicity, IID sampling and uniform second moments each enter its regularized-root, contraction or variance arguments. Their necessity for every possible algorithm is not claimed. Only the finite-dimensional version is formalized. The result does not imply pointwise convergence, gap accuracy, high-probability accuracy, parameter adaptivity, or an infinite-dimensional theorem.

## Formalization and literature coverage

The single public theorem names the setup's `spec` and constructs `inertialExtragradient`; `terminalPoint` names its executed output. Supporting modules are [step contraction](../Proofs/InertialMonotoneStep.lean), [root transport](../Proofs/InertialMonotoneTransport.lean), [moments](../Proofs/InertialMonotoneMoments.lean), [sampling](../Proofs/InertialMonotoneSampling.lean), [potential](../Proofs/InertialMonotonePotential.lean), [execution](../Proofs/InertialMonotoneExecution.lean), [IID iteration](../Proofs/InertialMonotoneIteration.lean), [schedule and budget](../Proofs/InertialMonotoneSchedule.lean), and [accuracy](../Proofs/InertialMonotoneAccuracy.lean). The public law is abstract; finite prefixes in the proof index the number of draws, not a finite sample-space restriction. The nonlinear examples and literature comparisons are explanatory and are not additional formal theorems.

Literature checks used the UTC date 28 October 2026, independently surveying the two latest publicly available conference editions and recent arXiv work before selection, then following older baselines and subsequent work. The September 2026 papers above are preprints, not claimed accepted conference papers. The checked latest versions were 2609.28543v1 (22 September), 2609.35631v1 and 2609.36033v1 (28 September), and 2609.04188v2 (17 September). Official JMLR and PMLR records establish the publication statuses stated above. Some conference virtual pages were inaccessible; available official proceedings, OpenReview records and primary PDFs were used instead. Search coverage cannot prove the absence of an unlocated result. The novelty claim concerns the specified mean-only RMS residual bound and observable corrected-response mechanism; it does not concern formalization alone, a new name, or universal superiority over all oracle models.
