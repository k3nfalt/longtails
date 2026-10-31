# Accelerated finite-sum optimization under interpolation and generalized smoothness

The result targets the established convex, componentwise symmetric generalized-smooth interpolation model. It gives a gradient-only oracle bound

\[
 O\!\left(\left[n(1+L_1^2R^2)+\sqrt{nL_0R^2/\varepsilon}\right]
 \log\left(2+n+L_0R^2/\varepsilon+L_1^2R^2\right)\right)
\]

for ordinary objective-gap accuracy with probability at least \(2/3\). The contribution is an amortized bound on the gradient work needed to implement accelerated component-envelope optimization. Component smoothing, variance reduction, and acceleration are established ingredients; the claimed new guarantee is their implementation with an additive generalized-curvature cost under this oracle model.

The formal statement is [the convergence theorem](AcceleratedInterpolatedGeneralizedFiniteSum.lean), using [the setup](../Setups/InterpolatedGeneralizedFiniteSum.lean) and [the algorithm and output](../Algorithms/ComponentEnvelope.lean). The final probability and objective-transfer proofs are in [ComponentEnvelopeGuarantee](../Proofs/ComponentEnvelopeGuarantee.lean), with [budget algebra](../Proofs/ComponentEnvelopeBudget.lean).

## Problem, information, and guarantee

Let \(F(x)=n^{-1}\sum_{i=1}^n f_i(x)\) on any finite-dimensional real Hilbert space. Each component is convex and differentiable and has continuous gradient. The common constants satisfy \(L_0>0\), \(L_1\ge0\). Symmetric generalized smoothness means that, for every segment from \(x\) to \(y\) and every bound \(M\) on the component-gradient norm throughout that segment,

\[
 \|\nabla f_i(x)-\nabla f_i(y)\|\le(L_0+L_1M)\|x-y\|.
\]

There is a common component minimizer \(x_\star\), and the supplied radius satisfies \(\|x_0-x_\star\|\le R\), with \(R>0\). The algorithm knows \(n,L_0,L_1,R,\varepsilon,x_0\) and may query any exact component gradient. It does not receive objective values, a minimizer, a component minimum value, or a proximal oracle. The setup places no restriction on the algorithm family. Continuity is redundant for differentiable convex functions in finite dimension; it is explicit in the Lean specification to support segment estimates.

For \(\varepsilon>0\), the proved budget is exactly

\[
 K=\left\lceil 2^{30}
 \left[n(1+L_1^2R^2)+\sqrt{nL_0R^2/\varepsilon}\right]
 \log\left(2+n+L_0R^2/\varepsilon+L_1^2R^2\right)\right\rceil.
\]

Writing \(\widehat x=\texttt{ComponentEnvelope.output}\), the theorem guarantees
\(\Pr\{F(\widehat x)-F(x_\star)\le\varepsilon\}\ge2/3\).
The probability is the product of the algorithm's explicit finite uniform seed law and the oracle's seed law. Oracle replies are exact irrespective of their history or seeds. The finite seed restriction is internal to this randomized algorithm; there is no stochastic-gradient noise assumption. The result is a fixed-confidence upper bound, with no claim of optimal dependence on \(n\) or \(L_1R\).

## Algorithm and proof mechanism

Set
\[
 \mu=L_0+8nL_1^2\varepsilon,\qquad
 S=\left\lceil\sqrt{7200\mu R^2/(n\varepsilon)}\right\rceil,\qquad
 \zeta=\frac{\mu R}{2^{20}n(S+4)^3}.
\]
The analysis uses component Moreau envelopes
\(h_i(c)=\min_z\{f_i(z)+\mu\|z-c\|^2/2\}\), with mean \(H\). They share the original minimizer and have \(\mu\)-Lipschitz gradients. These envelopes are analysis objects; the algorithm computes their gradients approximately using only component-gradient queries.

An inner solve starts at \(z=c\). After querying \(g=\nabla f_i(z)\), it forms \(r=g+\mu(z-c)\), stops if \(\|r\|\le\zeta\), and otherwise uses
\[
 z^+=z-\frac{r}{16(L_0+\mu+L_1\|g\|+L_1\|r\|)}.
\]
The returned estimate is \(\mu(c-z)\). The algorithm has an explicit finite inner fuel, sufficient to reach this observable residual test. Put
\(Q=L_1R\) and
\(\ell=\log(4+Q+\mu R(1+Q)/\zeta)\).
Each solve, including its final residual evaluation, uses at most
\(4096\ell(1+q_i(c)^2)\) gradient calls, where
\(q_i(c)=L_1\|c-\operatorname{prox}_i(c)\|\).
The proof combines a squared-distance decrease for large residuals with contraction for smaller residuals, allowing arbitrary interleaving of these cases.

All outer points are projected onto the known ball \(\overline B(x_0,R)\). A warmup makes \(4n\) component-envelope queries with step \(1/(2\mu)\) and averages the queried points. The main loop has \(S\) epochs, each with a full cache of \(n\) component estimates and \(n\) fresh uniform component queries. For \(\tau_s=2/(s+4)\), its query is
\(x=\tau_s z+\tfrac12w+(\tfrac12-\tau_s)y\).
With the cached variance-reduced estimate \(v\), the updates are
\(y^+=\Pi(x-v/(6\mu))\) and
\(z^+=\Pi(z-v/(6\mu\tau_s))\).
The next snapshot averages the new \(y\)-iterates; the last \(y,z\) are carried forward. The returned completed-plan output is the final snapshot.

The crucial accounting identity is
\[
 q_i(c)^2\le\frac{2L_1^2}{\mu}\,[h_i(c)-h_i(x_\star)].
\]
A robust projected coupling tolerates the biased, index-dependent inner errors. Its starting potential controls the sum of gaps at **both** cached snapshots and accelerated query points. The query estimate
\[
 H(x)-H(x_\star)\le H(w)-H(x_\star)+H(y)-H(x_\star)
   +\mu\tau_s^2\|z-y\|^2
\]
lets the weights \(\tau_s^2\) be summed. This charges difficult inner solves to a summable quantity instead of multiplying every outer call by a worst-case inner cost.

The formal proof gives expected envelope gap at most \(\varepsilon/60\) and expected nominal gradient cost at most
\[
 4096\ell\,[n(4+2S)+752nQ^2].
\]
There are exactly \(4n+2nS\) component solves, and each solve's gradient calls are counted. On \(H(x)-H(x_\star)\le\varepsilon/5\), every component prox displacement is locally small and \(F(x)-F(x_\star)\le5[H(x)-H(x_\star)]\). A joint Markov argument gives probability at least \(3/4\) that accuracy and nominal cost \(\le K\) both hold. On this event the actual capped `execute` output equals the completed plan's output. `execute` can use padding calls after completion; the expected-cost statement concerns nominal work, while the public theorem grants the full deterministic budget \(K\).

## Closest comparisons and significance

[Gorbunov et al., ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/f21a5fedfbcb55406ddaf51cf90d494a-Abstract-Conference.html), [arXiv v2](https://arxiv.org/html/2409.14989v2), Assumption 7.1 and Appendix H.1, provide the directly comparable individual-smooth interpolation class. Their clipped-SGD conditional descent inequality, followed by an independent uniform output choice and Markov's inequality, already yields ordinary-gap success probability \(2/3\) with
\(\lceil24L_0R^2/\varepsilon+192nL_1^2R^2\rceil\) component-gradient calls. Thus ordinary-gap accuracy itself is not new here.

With \(\kappa=L_0R^2/\varepsilon\), the new guarantee replaces the \(\kappa\) accuracy dependence by \(\sqrt{n\kappa}\), at the price of an \(n\) overhead and a logarithm, retaining the additive \(nQ^2\) transient. A sufficient asymptotic improvement regime is
\(\kappa/n\gg\log^2(2+n+\kappa+Q^2)\) and
\(\kappa\gg nQ^2\log(2+n+\kappa+Q^2)\).
There is no universal dominance: large curvature transients or low accuracy can favor clipped SGD. This is a finite-sum acceleration result for an established class, not an acceleration theorem as general as classical AGD.

[Katyusha, JMLR 18(221)](https://www.jmlr.org/papers/volume18/16-410/16-410.pdf), Lemmas 2.3–2.7 and Appendix C.1, supplies the smooth finite-sum acceleration baseline. Applying it to exact component envelopes presupposes a stronger oracle. Charging a uniform inner bound gives a multiplicative \((1+Q^2)\) cost on the accuracy-dependent number of solves. The summed query-gap argument above removes that multiplication. The interpolation warmup also removes the initial-objective-gap term from the starting potential.

Component-envelope methods are already present in [FedExProx, NeurIPS 2024](https://proceedings.neurips.cc/paper_files/paper/2024/file/e0b6f389739496e363a89155c9448a8a-Paper-Conference.pdf) and [Deng–Gao, arXiv:2512.09720v3](https://arxiv.org/html/2512.09720v3), Sections 4.2–4.3 and 6. Their existence is not claimed as novel. The latter's general local-curvature reduction does not furnish the polynomial amortized component-gradient cost proved here. [Tovmasyan et al., arXiv:2502.03401v2](https://arxiv.org/html/2502.03401v2), Theorem 5.4 and Appendix B.2.1, analyzes inexact stochastic proximal points; its generalized-smooth inner local bound contains exponential distance factors and its convex outer guarantee is not the accelerated finite-sum bound above.

The more recent [inexact FedExProx analysis, arXiv:2410.15368v2 (18 April 2026)](https://arxiv.org/html/2410.15368v2), [accepted at ICLR 2026](https://openreview.net/forum?id=PHsFWKJhGv), studies inexact component-envelope optimization under ordinary individual global smoothness and a PL condition on the averaged envelope. Those restrictions exclude the general convex, globally unbounded-curvature instances here; its inexactness analysis does not supply this generalized-smooth amortized gradient bound. [Catalyst, JMLR 18(212)](https://www.jmlr.org/papers/volume18/17-748/17-748.pdf), Proposition 12, Corollary 13, and Proposition 15, controls inner initialization through warm starts; removing initialization logarithms does not establish the additive generalized-curvature accounting needed here.

Recent stochastic acceleration is not absent from the literature. [Tyurin, arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884v2), listed in the [ICML 2026 official program](https://icml.cc/Downloads/2026), addresses deterministic objective-gradient acceleration. [ARC-SG, arXiv:2609.06555v1](https://arxiv.org/html/2609.06555), Theorems 1 and 4, assumes objective generalized smoothness and additive norm-sub-Gaussian noise; Appendix I, Assumption 7 and Eq. (50), uses almost-sure strong growth. Neither mean-objective smoothness with the same constants nor strong growth is imposed or implied here. Uniform component sampling is not a zero-noise oracle for the mean objective. Exact full-gradient emulation costs \(n\) calls per gradient. The ARC-SG source is a preprint, not a verified conference acceptance.

## Instances, boundaries, and audit scope

A nonlinear family is noiseless realizable exponential regression:
\(f_i(x)=\exp(a_i^\top x)-b_i a_i^\top x\), with \(A,B>0\),
\(b_i=\exp(a_i^\top x_\star)\), \(\|a_i\|\le A\), and \(b_i\le B\).
It satisfies the assumptions with \(L_0=BA^2\), \(L_1=A\). Nonorthogonal feature vectors yield interacting coordinates in arbitrary dimension; the Hessian bound follows from
\(\|a_i\|^2\exp(a_i^\top x)\le BA^2+A\|\nabla f_i(x)\|\).
This describes realizable data, not generic noisy Poisson regression. Its global curvature is unbounded. The displayed rate has no explicit dimension factor; dimension enters through the problem constants and the cost of vector operations, which are not gradient calls.

Interpolation does not imply a controlled strong-growth constant even with fixed \(n=2\): for rank-one quadratic components with rows
\(a_\pm=(\delta,\pm\sqrt{1-\delta^2})\), at \(x=(1,0)\) the ratio of mean squared component-gradient norm to squared mean-gradient norm is \(1/\delta^2\). This diagnostic excludes a reduction to strong-growth acceleration with constants controlled by the stated parameters. It is not the nonlinear scope of the theorem.

At \(L_1=0\), the bound recovers the known smooth finite-sum order up to the retained logarithm; that boundary is not new. At \(n=1\), no improvement over the strongest deterministic generalized-smooth acceleration results is claimed. The novelty claim concerns the joint finite-sum and generalized-smooth regime.

The result requires known parameters, exact selectable component gradients, a common minimizer, and a radius certificate. It does not cover noninterpolation, noisy component queries, unknown-parameter adaptivity, or an infinite-component sampling oracle. No claim is made of a matching lower bound, optimal logarithms, practical constants, or empirical speedup. The explicit constant is deliberately loose.

The literature assessment used the UTC date 2026-10-26, independently surveyed publicly available ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025/2026 material and approximately two years of arXiv submissions/revisions, then followed older foundational results. Conference status was checked through official proceedings/programs or OpenReview; preprints were treated as prior art regardless of acceptance. Some OpenReview pages were browser-challenge inaccessible, including the Tyurin page, so official conference listings and accessible arXiv versions supplied the check. Search coverage cannot prove absence of all prior work. The substantive comparison is the complete gradient-only amortized guarantee, not novelty of its individual standard ingredients or of Lean formalization.
