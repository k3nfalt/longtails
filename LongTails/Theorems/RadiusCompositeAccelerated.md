# Radius-only acceleration with an ordinary composite proximal oracle

[The theorem](RadiusCompositeAccelerated.lean) proves an objective-gap guarantee for convex composite optimization with generalized smoothness, using only exact gradients and an ordinary joint proximal oracle. The [setup](../Setups/RadiusCompositeGeneralizedSmooth.lean) and [algorithm](../Algorithms/RadiusCompositeAccelerated.lean) are explicit. The guarantee is deterministic for every admissible oracle response; the framework expresses this as almost-sure success under its explicit seed law.

Let

\[
F(x)=f(x)+\psi(x),\quad x\in Q,\qquad
\kappa=L_1R,\quad M=L_0+L_1G,\quad \tau=MR^2/\varepsilon.
\]

For an attained minimizer \(x_\star\), assume \(\|x_0-x_\star\|\le R\) and \(\|\nabla f(x_\star)\|\le G\). The returned feasible point satisfies \(F(x)-F(x_\star)\le\varepsilon\) after at most

\[
\left\lceil32768\big((1+\kappa)^{4/3}+\sqrt\tau\big)
        \log^2\!\big(128(1+\kappa+\tau)\big)\right\rceil
\]

**total gradient and proximal calls**, including initialization, unsuccessful trials, and padding after termination. This is a proved upper bound, not an optimal complexity claim.

## Assumptions and information

The space is an arbitrary real Hilbert space, hence includes every finite dimension. The smooth part is globally convex and continuously differentiable with continuous gradient. Its symmetric generalized-smoothness condition is: whenever the gradient norm on the segment from \(x\) to \(y\) is bounded by \(H\),

\[
\|\nabla f(x)-\nabla f(y)\|\le(L_0+L_1H)\|x-y\|.
\]

For twice differentiable finite-dimensional objectives the familiar Hessian condition \(\|\nabla^2 f(x)\|\le L_0+L_1\|\nabla f(x)\|\) implies this segment condition. We require \(L_0,R,\varepsilon>0\), \(L_1,G\ge0\), a convex feasible set \(Q\), convexity of \(\psi\) on \(Q\), and \(x_0\in Q\). The oracle returns an exact minimizer, for every positive \(a\), of

\[
\psi(u)+\langle g,u-z\rangle+\|u-z\|^2/(2a),\qquad u\in Q.
\]

Existence of these proximal points is part of the oracle assumption. This is a **joint** proximal oracle for \(\psi+\iota_Q\); separate access to the prox of \(\psi\) and projection onto \(Q\) would not suffice in general. No ball-restricted prox, Hessian, objective-value query, bounded domain, bounded regularizer subgradient, or initial objective-gap bound is assumed. The algorithm receives \(L_0,L_1,R,\varepsilon,x_0\); \(G\) appears only in the analysis and public budget. There is no restriction to a prescribed algorithm family.

Convexity, attained solutions, radius information and exact proximal access are standard composite assumptions; see the accelerated composite setting of [Monteiro–Svaiter, Sections 4–5](https://optimization-online.org/wp-content/uploads/2011/05/3030.pdf) and [Deng–Gao, Section 6.1](https://arxiv.org/html/2512.09720v3). Generalized smoothness and radius-based complexity are established in [Rudomanov et al., Theorem 3.7](https://arxiv.org/html/2610.21461v2). The quantity \(G\) accounts for the fact that the smooth gradient need not vanish at a composite optimizer; setting it to zero without an additional condition would strengthen the result incorrectly. No assumption is imposed to ensure that a particular trial search succeeds: its termination and cost are proved.

A nonquadratic family in arbitrary dimension is

\[
f(x)=\sum_i[\exp((Bx)_i)-(Bx)_i-1],
\]

where \(B\) is dense orthogonal. It has \(L_0=L_1=1\), independently of dimension. Combining it with \(\psi(x)=\lambda\|x\|_1\), or a positive semidefinite quadratic that does not commute with the coordinates of \(B\), gives an interacting composite problem with unbounded smooth curvature and an ordinary exact prox. For these examples \(x_\star=0\) and \(G=0\). Rotating to separate \(f\) does not separate the whole composite objective. General constraints and other regularizers are covered when the specified joint prox is available; the theorem is not limited to this example family.

## Algorithm, output and proof mechanism

Write \(g_0=\nabla f(x_0)\), \(S_0=L_0+L_1\|g_0\|\). One gradient and one proximal call initialize

\[
a_0=(S_0e^\kappa+L_0)^{-1},\quad
u=\operatorname{prox}_{a_0(\psi+\iota_Q)}(x_0-a_0g_0),\quad
A_0=(8S_0e^{4\kappa})^{-1}.
\]

Both primal and momentum points start at \(u\). The exponential initial weight is an analysis-safe initialization; its logarithm is accounted for in the complexity.

At weight \(A\), primal point \(x\), and momentum \(v\), a trial \(0<a\le A\) forms

\[
B=A+a,\quad y=(Ax+av)/B,\quad
p=\operatorname{prox}_{a(\psi+\iota_Q)}(v-a\nabla f(y)),\quad d=p-v.
\]

It accepts when both \(a^2(L_0+L_1\|\nabla f(y)\|)/B\le1/32\) and \(L_1a\|d\|/B\le1/32\). The update is \(x^+=(Ax+ap)/B\), \(v^+=p\). The output is this maintained primal point at the first weight \(A\ge4R^2/\varepsilon\); it is an accumulated convex combination, not the momentum or a randomly selected iterate. Subsequent calls leave it unchanged.

The search grows from a proved safe trial, caches the safe/unsafe bracket, and refines it a specified finite number of times. It does not assume monotonicity of acceptance as the extrapolated query changes. The next safe starting weight is the accepted weight divided by \(128(1+4\kappa)\). Every evaluated trial costs one gradient and one prox; cached endpoints incur no hidden evaluation.

The decisive energy inequality retains both payments:

\[
E^+ +\tfrac14\|d\|^2+aD_f(x_\star,y)\le E,
\qquad E=A(F(x)-F(x_\star))+\tfrac12\|v-x_\star\|^2.
\]

Here \(D_f(x_\star,y)=f(x_\star)-f(y)-\langle\nabla f(y),x_\star-y\rangle\) is the **reverse** Bregman divergence. It is not bounded above by the forward objective gap in general. Generalized smoothness gives a logarithmic curvature payment in this reverse divergence. For \(w(A)=\max\{1,\log(1/(256MA))\}\), the potential

\[
J(A)=\log A+w(A)-\log w(A)
\]

controls the sum of weighted progress fractions. This bounds high-curvature boundary steps by \(444\kappa\sqrt\ell\), with \(\ell=\log(128(1+\kappa+\tau))\). Low-curvature steps number at most \(79\sqrt\tau\). Squared proximal movement and Hölder counting bound displacement-boundary steps by \(123(1+\kappa)^{4/3}\ell\); cap steps contribute at most \(9(1+\kappa)\ell\). The overlapping categories cover every accepted step and give \(N\le1024((1+\kappa)^{4/3}+\sqrt\tau)\ell\).

Finite search, restart safety, and telescoping of all trial charges then give the displayed oracle budget. The proof handles an already-finished initialization separately and chains the actual state machine only up to its first stopping index. Supporting modules run from [energy](../Proofs/CompositeAdaptiveEnergy.lean) and [geometry](../Proofs/CompositeAdaptiveGeometry.lean) through [counting](../Proofs/CompositeAdaptiveCounting.lean), [search](../Proofs/CompositeAdaptiveSearch.lean), [execution](../Proofs/CompositeAdaptiveExecution.lean), [complexity](../Proofs/CompositeAdaptiveComplexity.lean), and [completion](../Proofs/CompositeAdaptiveCompletion.lean).

## Novelty comparison and limitations

The contribution is the joint radius-only, ordinary-prox oracle guarantee with a \(\kappa^{4/3}\) transient. Generic acceleration, the energy template, Hölder counting, and search amortization are prior tools. The new analysis combines a logarithmically weighted reverse-divergence payment with a finite adaptive search controlling actual composite proximal movement, without function values or an initial gap certificate.

* **Smooth radius-only optimum.** [Descending Everest, Part I, v2, November 5, 2026, Theorem 3.7](https://arxiv.org/html/2610.21461v2) gives a near-linear \(\kappa\) transient for unconstrained smooth objectives. Its gradient-specific construction does not supply an arbitrary composite prox theorem. Our result extends the objective/oracle scope but loses a factor \(\kappa^{1/3}\), up to logarithms, relative to that smooth guarantee. We do not improve the smooth problem-class complexity. This source is a preprint; no conference acceptance is claimed.
* **Accelerated local-smooth composite methods.** [Deng–Gao, v3, January 25, 2026, Algorithm 3, Proposition 6.2 and Theorem 6.1](https://arxiv.org/html/2512.09720v3) already provide accelerated composite line search. Their bound uses maximal local curvature over an invariant radius ball and their test uses function values. Direct generalized-smoothness substitution makes that curvature exponential in \(\kappa\). Our bound avoids that worst-ball substitution. A specialized alternative analysis of their algorithm is not ruled out. Publication status was not independently established; we cite the preprint.
* **Generalized mirror descent.** [Yu et al., ICML 2026](https://proceedings.mlr.press/v306/yu26s.html), [v4, May 30, 2026, Sections 3 and 5](https://arxiv.org/html/2502.00753v4), treats generalized smoothness and includes a composite nonconvex gradient-mapping guarantee in Theorem 5.1. That is a different accuracy target from the accelerated convex objective gap here. Their smooth acceleration does not directly give this radius-only composite conclusion.
* **Large-step acceleration.** [Monteiro–Svaiter, Theorem 4.1 and Sections 5–7](https://optimization-online.org/wp-content/uploads/2011/05/3030.pdf) supplies established accelerated hybrid-proximal machinery. Its first-order specialization uses global Lipschitz smoothness; second-order implementations use stronger subproblems. Its generic theorem does not directly supply the reverse-entropy payment or the counted ordinary-prox search proved here.

An explicit repository comparison is [CompositeGeneralizedAccelerated](CompositeGeneralizedAccelerated.lean): its initial-gap-dependent upper bound has a \(\kappa\log\Delta\) transient. A counted proximal initialization provides an exponential-in-\(\kappa\) gap certificate from radius data, yielding a quadratic transient. The present bound reduces that transient to \(\kappa^{4/3}\), up to logarithms, while retaining \(\sqrt\tau\). For \(\kappa\gg1\) and \(\tau\le\kappa^{8/3}\), this gives a meaningful polynomial improvement over that constructed upper bound. This is not a lower bound for the previous algorithm or the composite class. Parameter-free backtracking methods use less prior information; our known \(L_0,L_1,R,\varepsilon\) are a tradeoff, not an adaptivity improvement.

A stronger standard reduction must also be considered on a smaller subclass. If \(Q\) is the whole space and \(\psi\) is globally \(G_\psi\)-Lipschitz, Moreau smoothing with \(\lambda=\varepsilon/(4G_\psi^2)\) and quadratic regularization \(\mu=\varepsilon/(4R^2)\) yields a smooth minimizer within \(\sqrt2R\). Applying the smooth radius-only theorem gives, up to logarithms,

\[
1+\kappa+\sqrt{(L_0+L_1G_\psi)R^2/\varepsilon}+RG_\psi/\varepsilon,
\]

counting a gradient and prox per smoothed gradient. Thus smoothing can be better at fixed accuracy. For the dense orthogonal exponential example with fixed dimension and fixed positive \(\ell_1\) penalty, \(R\to\infty\) and \(\varepsilon=R^{-2/3}\), our displayed bound scales as \(\widetilde O(R^{4/3})\) versus \(\widetilde O(R^{5/3})\) for this reduction. This compares two upper bounds, not all possible smoothing methods. General constraints and regularizers with unbounded subgradients lack the uniform envelope-bias and feasibility guarantee used in that reduction.

The result does not cover noisy or inexact proximal oracles. It is not claimed to be optimal; a near-linear composite transient remains unresolved by this proof. Literature screening by both agents covered the two most recent publicly available conference editions and recent arXiv work, followed foundational citations, and checked the listed theorem versions through November 12, 2026. No matching bound was found in the checked sources; search coverage alone is not a proof of novelty. The mathematical comparison and completed reductions, rather than the formalization alone, support the contribution claim.
