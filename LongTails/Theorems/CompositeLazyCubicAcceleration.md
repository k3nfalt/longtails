# Composite acceleration with reused Hessians

The [Lean theorem](CompositeLazyCubicAcceleration.lean) constructs [CompositeLazyCubic.algorithm](../Algorithms/CompositeLazyCubic.lean) for the [CompositeLipschitzHessian specification](../Setups/CompositeLipschitzHessian.lean). It bounds separately the number of gradient, Hessian, and generalized proximal-model queries needed to minimize a smooth convex function plus an arbitrary closed convex term. The proposed contribution is extending the near-optimal polynomial dependence of lazy second-order optimization to this general composite class, with explicitly counted model queries and additional logarithmic factors. The accuracy exponent itself is established prior work.

Let \(F=f+\psi\) on a convex domain \(C\) in an arbitrary finite-dimensional real inner-product space. The assumptions are:

- \(f\) is globally convex and \(C^2\), with \(\|\nabla^2 f(x)-\nabla^2 f(y)\|\le H\|x-y\|\).
- \(\psi:C\to\mathbb R\) is convex and its epigraph in the ambient space times \(\mathbb R\) is closed. Equivalently, its extension by \(+\infty\) outside \(C\) is proper closed convex. The set \(C\) itself need not be closed.
- A minimizer \(x_\star\in C\) exists. The public initial point satisfies \(x_0\in C\) and \(\|x_0-x_\star\|\le R\).
- \(H,R,\varepsilon>0\) and the integer Hessian-cost parameter \(m\ge1\) are known.

There is no bound on gradients, subgradients, the domain, a level-set radius, or the initial objective gap. Strong convexity, an interior solution, and a constraint qualification are not required. The minimizer is private problem data used in the guarantee, not supplied to the algorithm. These are standard composite Newton assumptions; the primary general-composite reference is Monteiro–Svaiter, Section 6, conditions C1–C3, described below. Our global ambient smoothness assumption is stronger than their allowance for smoothness on a suitable set containing the nonsmooth domain.

**Oracle access and its cost.** Channels 0 and 1 return exact gradients and Hessians of \(f\). Channel 2 returns the unique minimizer of

\[
 \alpha\psi(u)+\langle g,u-y\rangle
 +\tfrac12\langle u-y,B(u-y)\rangle
 +\tfrac{\sigma}{3}\|u-y\|^3,\qquad u\in C.
\]

The query supplies \(y,g,B,\sigma,\alpha\), with \(\alpha>0\), symmetric positive-semidefinite \(B\), and \(\sigma\ge0\). Either \(\sigma>0\) or \(B\) must be uniformly positive definite. The specification expresses its solution by the equivalent convex first-order variational inequality; existence and uniqueness are proved in [CompositeModel](../Proofs/CompositeModel.lean). This oracle accesses only the fixed nonsmooth term and the supplied coefficients. It does not minimize the unknown smooth function. It includes exact variable-metric prox when \(\sigma=0\) and exact cubic composite models when \(\sigma>0\).

Every model solve is charged. This access is stronger than an ordinary Euclidean prox oracle, and exact model solves need not be cheap. The weighted accounting is \(G+M+m\mathcal H\), where \(G,M,\mathcal H\) count gradient, model, and Hessian queries. The theorem is an oracle-complexity result, not a runtime, memory, or floating-point implementation guarantee. In particular, it does not bound the work of solving the models by their query count. Exact cubic-model access is also used by established composite cubic Newton methods; exact metric-prox access suffices for the fresh-Hessian comparison below.

**Algorithm and output.** The algorithm uses cubic regularization with \(\gamma=H/m^3\), fixed-parameter damped accelerated outer steps, and a finite inner solver that reuses Hessian snapshots. Its outer parameter is \(\mu=\gamma^{4/7}\varepsilon^{3/7}/R^{2/7}\). Each cubic subproblem uses two initial exact cubic-model steps, geometrically decreasing gap epochs, and one final cubic-model step. An epoch reuses one Hessian across accelerated proximal steps with a finite guarded residual search. All trial queries, including discarded trials, and all three bridge steps are counted. Early exits use the explicitly counted padding in the query plan.

The output is the last damped outer point, or the certified optimum returned by the early zero-displacement branch. It is feasible and satisfies \(F(\mathrm{output})-F(x_\star)\le\varepsilon\). This holds for every oracle seed sequence satisfying the exact oracle specification, hence also almost surely under the explicitly quantified execution probability law. There is no stochastic independence assumption. Neither function values nor values of \(\psi\) are queried. The algorithm never uses the local subproblem minimizers that appear internally in the proof.

For the exact budgets, write

\[
 q=\frac{HR^3}{m^3\varepsilon},\quad
 j=3+\lfloor\log_2(m^3+4)\rfloor,\quad
 B_q=3+\lfloor\log_2(2+\lceil q^{4/7}\rceil)\rfloor,\quad
 C_q=1+\lceil q^{2/7}\rceil.
\]

The public Lean budget expands these expressions directly in the setup parameters and proves

\[
 G\le2^{39}m j^4 B_q C_q,\qquad
 M\le2^{39}m j^4 B_q C_q,\qquad
 \mathcal H\le4160j B_q C_q.
\]

The fixed outer horizon is \(16B_qC_q\). Thus the weighted cost is at most
\[
 (2^{40}j^4+4160j)mB_qC_q
 =\widetilde O\!\left(m+m^{1/7}(HR^3/\varepsilon)^{2/7}\right).
\]
The explicit constants are deliberately conservative; this implementation is not tuned for practical constants. The suppressed factors include \((1+\log m)^4\) and \(1+\log(2+q)\). The latter is an additional accuracy-dependent factor relative to the closest smooth lazy theorem.

**What requires a new proof.** The starting point is the smooth lazy framework of Zhang, Chen, Liu, and Zhang. Two obstacles prevent simply inserting an ordinary proximal update into its analysis. Extrapolating the full composite objective would require evaluating \(\psi\) outside its domain or solving a sum of transformed nonsmooth terms. Also, the reused metric controls curvature only on a sublevel region, whereas a residual segment search evaluates additional points that need not remain in that region.

The proof resolves the first obstacle by shifting the smooth and nonsmooth terms by opposite affine functions at an analysis-only cubic-subproblem minimizer. Both shifted terms are nonnegative. The extrapolated surrogate evaluates only the smooth term at extrapolated points and uses one scaled copy of the original \(\psi\). A feasible comparator contracts the original composite gap, while the actual algorithm uses the corresponding unshifted quantities. All affine shifts cancel from objective differences and gradient certificates.

For the second obstacle, the guarded search treats failure of a checkable local descent certificate as an upper endpoint. Its lower endpoint remains certified and decreases the surrogate objective. A quantitative neighborhood argument extends the local Hessian bound from the lower endpoint's proximal point to nearby trials, making a sufficiently close upper endpoint certified as well. A residual continuity bound then supplies the two approximate orthogonality inequalities needed by acceleration. The proof derives a finite search depth from the acceleration potential and a coarse \(\kappa^3\) distance bound, with \(\kappa=m^3+4\); this relaxation changes only logarithmic search constants. No bounded-subgradient assumption supplies the missing neighborhood control.

The implementation fixes \(J=j-1\), \(32768m(J+1)\) accelerated inner steps, \(128(J+1)\) search rounds, and \(256(J+1)\) gap epochs. The proved cubic residual is at most \(\gamma\|z-y\|^2/32\). The outer proof telescopes its damped potential and counts failed steps in dyadic weight intervals, including interval-crossing increments. This yields the stated finite horizon without an unobservable objective-based stopping rule. These links, including actual execution and each channel's cost, are in [CompositeLazyCubicConvergence](../Proofs/CompositeLazyCubicConvergence.lean), [CompositeCubicAcceleration](../Proofs/CompositeCubicAcceleration.lean), and [CompositeLazyCubicExecution](../Proofs/CompositeLazyCubicExecution.lean).

**Comparison with primary results.**

| Prior result | Applicable guarantee and assumptions | Difference here |
| --- | --- | --- |
| [Zhang–Chen–Liu–Zhang, arXiv:2610.03222v1, 2 October 2026](https://arxiv.org/html/2610.03222v1), Theorem 4.1, Lemmas 4.5, 4.6, 4.8 | Smooth unconstrained convex lazy second-order complexity \(\widetilde O(m+m^{1/7}(HR^3/\varepsilon)^{2/7})\), with displayed \(\log^{11/3}m\) factor. Unreviewed preprint. | Same polynomial powers for general closed-convex composite objectives, with counted generalized model access and larger logarithmic factors. No improvement is claimed on its smooth subset. |
| [Monteiro–Svaiter, SIOPT 2013, May 24, 2012 revision](https://optimization-online.org/wp-content/uploads/2011/05/3030.pdf), Theorems 6.4 and 7.15, Section 7.4 | General proper closed convex composite acceleration already attains the \(\varepsilon^{-2/7}\) exponent. Exact quadratic-model prox implements its Newton black box using fresh Hessians, giving weighted \(\widetilde O((m+1)(1+(HR^3/\varepsilon)^{2/7}))\). | Reduces the polynomial Hessian-cost dependence in this general composite setting. Neither general composite acceleration nor removal of a bounded-subgradient restriction from this 2013 theorem is new. |
| [Doikov–Chayti–Jaggi, ICML 2023](https://proceedings.mlr.press/v202/doikov23a/doikov23a.pdf), Appendix F | Composite cubic models and lazy-Hessian subgradient inequalities are already established. Convex gap results use different rates and bounded-level geometry. | The accelerated weighted tradeoff above uses only initial minimizer distance, without importing a level-set radius. The cubic bridge inequalities themselves are supporting prior techniques. |
| [Chen–Liu–Luo–Zhang, COLT 2026](https://proceedings.mlr.press/v336/chen26a.html), [arXiv:2501.17488v3, 13 July 2026](https://arxiv.org/html/2501.17488v3) | Smooth convex lazy rate with Hessian-cost exponent \(13/21\); smooth nonconvex results have a different stationarity criterion. | The October smooth result is the stronger applicable technical baseline. The older convex exponent is not used to inflate the improvement. |
| [Alphonse–Dvurechensky–Sirotenko, arXiv:2602.08069v1](https://arxiv.org/html/2602.08069v1), Theorem 3.4 | Composite lazy semismooth method with a \(1/k\) convex bound, bounded initial sublevel, and different regularity and initialization terms. Listed in the official NeurIPS 2026 program. | This does not imply the present accelerated initial-distance bound; conversely, the present theorem does not cover its weaker semismooth regularity. |

For a direct polynomial comparison, put \(T=HR^3/\varepsilon\). Against fresh composite acceleration, the ratio of the polynomial cost terms is at most \(T^{-2/7}+m^{-6/7}\). It can tend to zero when both \(T\) and \(m\) grow, provided these gains dominate the displayed logarithmic factors and the baseline's own search factors. This is not a universal finite-constant superiority claim. At \(m=1\) there is no polynomial improvement over classical composite acceleration. The additive startup cost remains necessary in the comparison, and the theorem is slower logarithmically than the strongest smooth-only upper bound.

The smooth lower-bound benchmark in Theorem 3.1 of the October preprint has the same polynomial powers, for deterministic algorithms in sufficiently high dimension. Its transfer to this model is an inference: on the subclass \(\psi=0,C=E\), every model reply is determined uniquely by supplied coefficients and contains no additional information about \(f\), so it can be simulated internally by a gradient/Hessian oracle algorithm. This is not a new formalized lower bound and does not establish randomized minimax optimality or a fixed-dimension lower bound.

**Scope, reductions, and examples.** A concrete interacting nonlinear family is
\[
 f(x)=\frac1n\sum_{i=1}^n\log\cosh(a_i^\top x-b_i)+\tfrac12x^\top Qx+c^\top x,
 \qquad \psi(x)=\lambda\|Dx\|_1+\iota_C(x),
\]
with an integer \(n\ge1\), \(\lambda\ge0\), at least one nonzero feature, nonorthogonal features, a general linear map \(D\), \(Q\succeq0\), and a nonempty polyhedron \(C\). For example, compact \(C\), or positive-definite \(Q\), ensures attainment. A valid Hessian-Lipschitz bound is \(H=(2/n)\sum_i\|a_i\|^3\). The rate has no separate dimension factor; feature norms, distance, model-solve work, and the chosen Hessian-cost weight can still depend on dimension. This family includes boundary optima and nonseparable regularization, where eliminating affine constraints alone does not reduce the problem to the smooth theorem.

Standard reductions were checked before choosing this direction. Affine-domain coordinate elimination is routine and is not the contribution. Direct smooth penalties and barriers require uncontrolled slope or boundary-slack parameters: adding an arbitrary affine term leaves \(H\) unchanged. A cubic distance penalty with coefficient \(\rho\) typically needs \(\rho\) of order \(G^3/\varepsilon^2\) to transfer projection accuracy under a slope bound \(G\), which is absent here and can spoil the desired rate. This calculation is an obstruction to that reduction, not an impossibility theorem about penalty methods. Moreau smoothing is not generally Hessian-Lipschitz, and a proximal oracle for the entire unknown objective is unavailable. [Bok–Altschuler's generic composite conversion](https://link.springer.com/article/10.1007/s10107-026-02377-7), Theorem 3.4, requires global cocoercivity and certificate conditions that do not directly apply to these local, changing Hessian metrics. Proximal residual searches and accelerated potentials are themselves prior techniques; the contribution depends on the complete local certificate argument above.

The result reduces full-Hessian requests by reusing snapshots across many gradient/model queries. Partial Hessian entries, Hessian-vector sampling, approximate model solves, numerical stability, and total computational speedups remain outside the guarantee. In particular, an arbitrarily ill-conditioned quadratic can have arbitrarily small Hessian-Lipschitz constant, so simulating the exact metric-model oracle using Euclidean prox does not have a condition-number-free cost justified by this theorem.

**Literature coverage and limitations.** Independent Researcher and Reviewer searches were conducted on 18 October 2026 UTC, before candidate selection, over the two latest publicly available ICML, ICLR, and NeurIPS editions (2025 and 2026) and approximately October 2024–October 2026 arXiv submissions and revisions, then followed older primary sources. Conference status was checked through official proceedings, OpenReview, or the [NeurIPS 2026 download index](https://neurips.cc/Downloads/2026). The exact versions used in the closest comparisons are listed above. Additional checks included the 2024 composite A-NPE implementation, the August 2026 primal Newton acceleration preprint, and October 2026 stochastic contracting-cubic and nonconvex oracle-tradeoff preprints; their stronger or different hypotheses and oracle models do not establish this guarantee.

Some conference poster pages were inaccessible, and an indexed 2026 affine-invariant weak-learner manuscript could not be retrieved from its author page. The stochastic contracting-cubic HTML endpoint was unavailable, but its PDF was examined. These access limitations are not evidence of novelty. The comparison is bounded literature-search evidence, not a proof that no other result exists. The strongest novelty objection is that this is a routine proximal conversion of the October smooth theorem; the response must be the quantitative, fully derived shifted-surrogate and finite local-search mechanism, rather than formalization or a new setup name alone.
