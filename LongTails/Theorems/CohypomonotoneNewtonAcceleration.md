# Residual acceleration with additive inversion cost for cohypomonotone equations

The [Lean theorem](CohypomonotoneNewtonAcceleration.lean) gives an oracle-complexity guarantee for globally cohypomonotone equations with a Lipschitz Jacobian, without a global Lipschitz bound on the operator. The contribution is the amortized cost of implementing residual acceleration through an approximate inverse transformation. The transformation, damped Newton primitive, and monotone acceleration exponent are established ingredients.

## Problem, information, and guarantee

The [specification](../Setups/CohypomonotoneNewton.lean) concerns a continuously differentiable map $F:E\to E$ on an arbitrary finite-dimensional real Hilbert space. For all $x,y\in E$,

\[
\|DF(x)-DF(y)\|\le H\|x-y\|,\qquad
\langle F(x)-F(y),x-y\rangle\ge-\rho\|F(x)-F(y)\|^2.
\]

There is a root $x_\star$ with $\|x_0-x_\star\|\le R$. The public inputs are $H>0$, $\rho\ge0$, $R>0$, $\varepsilon>0$, and $x_0$. The algorithm does not know the root. Each oracle call returns the exact pair $(F(x),DF(x))$, including the entire Jacobian. Linear solves and one finite-dimensional convex quadratic trust-region minimization are arithmetic operations, not additional oracle access. This is a full-Jacobian oracle model, not a value-only or Jacobian-vector-product guarantee. Its arithmetic and storage costs depend on dimension; the oracle-call bound has no explicit dimension factor.

Write $p=\rho HR$ and $Q=HR^2/\varepsilon$. The proved budget is

\[
K=\left\lceil 10^{14}\bigl[(1+p)^2+(1+Q)^{2/5}\bigr]
             \bigl[1+\log(2+p+Q)\bigr]^2\right\rceil.
\]

The [algorithm's named output](../Algorithms/CohypomonotoneNewton.lean) is the original-space point returned by `execute` after this budget. It satisfies $\|F(\mathrm{output})\|\le\varepsilon$. The setup states this almost surely under the explicit seed law in the framework; the proof actually establishes it for every seed because admissible oracle replies are exact and independent of history and seeds. It returns a stopped endpoint, not an average, a best-iterate existence statement, or a transformed-space residual.

Every value/Jacobian call is counted, including initialization, all rejected search trials, and endpoint inversions. The framework continues querying after a program has finished; the bound proves completion by $K$, and these padded calls are included in the actual $K$-call execution. Constants are conservative and are not a claim of practical efficiency.

## Mathematical contribution

Set $\gamma=2\rho+1/(HR)$, $T=I+\gamma F$, $q=\gamma HR=1+2p$, and $G=F\circ T^{-1}$. The globally defined inverse is used only in the analysis. Expansiveness of $T$ gives its nonexpansive inverse; $G$ is monotone, has Lipschitz constant at most $HR$, and has an $H$-Lipschitz Jacobian. No exact inverse oracle is supplied to the algorithm.

The implementation combines affine-model residual acceleration with approximate graph evaluations. A damped Newton inversion returns a queried $x$, so its pair $(T(x),F(x))$ lies exactly on the transformed graph, although $T(x)$ only approximates the requested point. A robust merit test tolerates this displacement. Search starts at the previous accepted step, doubles or halves to obtain a bracket, then bisects. It solves an endpoint inversion only after accepting a trial. The approximate merit need not be continuous or monotone; separation of rejected low and high values follows from comparison with the exact, continuous merit.

The central estimate is the perturbed accelerated energy inequality

\[
V_{k+1}+\frac7{16}\left(\frac{A_{k+1}}{a_k}\right)^2d_k^2
 \le V_k+\frac{R^2}{(k+1)^2},\qquad
V_k=A_k\langle g_k,y_k-x_0\rangle+\frac{A_k^2}{2}\|g_k\|^2.
\]

It controls the radius of every accepted graph endpoint and yields a local displacement bound $d_k\le3R\alpha_k$, where $\alpha_k=a_k/A_{k+1}$. Midpoint inversion starts have residual at most $8R\alpha(a)$; endpoint inversion starts have residual at most $4R\alpha_k$, including the terminal branch. Every step queried during a completed search is at most the maximum of the previous accepted step and twice the newly accepted step. Consequently, all rejected-trial costs can be charged to adjacent accepted fractions. Their sum is logarithmic because $\sum\alpha_k\le1+\log(A_{\rm end}/a_0)$.

A trust-region affine initializer gives initial inversion residual at most $R+2\gamma HR^2$, independently of $\|F(x_0)\|$ and $\|DF(x_0)\|$. Its cost is quadratic in $q$, rather than a repeated per-iteration transient. Uniform positive tolerances give logarithmic inversion accuracy costs. The resulting count is

\[
O\bigl(Q^{2/5}\ell^2+q\ell^3+q^2\ell+1\bigr),\qquad
\ell=1+\log(2+q+Q),
\]

which implies the displayed budget by an explicit absorption inequality. The regular-step energy and large-step condition give $N^5\le1572864A_N^2H^2R^2$; this proves residual accuracy within $\lceil64(1+Q)^{2/5}\rceil$ outer steps. The terminal branch has its own residual proof and does not assume the regular lower merit threshold.

The new claim is an additive inverse-simulation cost for the full nonlinear problem class. Merely invoking the classical inverse transformation and then charging a uniform inversion cost at every accelerated query does not establish this bound.

## Closest results and completed reduction comparisons

The comparison uses supplied $R,H,\rho,\varepsilon$ and the same full-Jacobian oracle whenever possible. It does not claim an adaptivity improvement.

* [Jiang–Yoon, arXiv:2609.30212v1](https://arxiv.org/abs/2609.30212v1), Theorem 3.2, Lemma 4.1, and Theorems 4.4/4.6, supplies the accelerated proximal framework and monotone second-order residual exponent $2/5$. Its Subroutine 1 begins each search at the upper trial, rather than reusing the previous accepted step. Section 7 discusses weakly nonmonotone extensions broadly; the precise amortized full-Jacobian question here is an inferred theorem-scope gap, not a quoted open problem. This September 2026 paper is a preprint. The concurrent [arXiv:2609.23557v1](https://arxiv.org/abs/2609.23557v1) is also part of the monotone higher-order baseline; matching the known monotone exponent is not itself novelty.
* [Matching Higher-Order Oracle Complexity, arXiv:2609.13462v2](https://arxiv.org/abs/2609.13462v2), Sections 4–9 and Theorem 8.1, is a particularly close amortization precedent. Its distance-sensitive regularized solver and Halpern second-difference analysis must be credited. They do not directly supply the present nested graph-oracle implementation: $T$ need not be strongly monotone, (T^{-1}) need not be firmly nonexpansive, and the costs of the complete Jacobian-query paths inside rejected trials are not supplied by that theorem. This is a preprint comparison, not an accepted-conference attribution.
* [Combettes–Pennanen (2004)](https://nms.kcl.ac.uk/teemu.pennanen/cohSICON.pdf), Lemma 2.4, provides the classical connection between cohypomonotonicity and inverse/Yosida transformations. That connection is not new here. [Polyak–Tremba, arXiv:1703.07810v2](https://arxiv.org/abs/1703.07810v2), Section 4, Theorem 4.1, equation (18), and Corollary 4.2, provides the relevant globally damped Newton analysis. Neither primitive alone gives the amortized accelerated oracle count.
* The global pairwise cohypomonotonicity assumption is established in the accelerated nonmonotone-equation literature, including [Lee–Kim, NeurIPS 2021](https://arxiv.org/abs/2106.02326) and [Alacaoglu–Kim–Wright, ICML 2024](https://proceedings.mlr.press/v235/alacaoglu24a.html), with [latest checked arXiv version 2402.05071v3](https://arxiv.org/abs/2402.05071v3). Their first-order guarantees use a global operator Lipschitz constant and restrictions involving its product with the nonmonotonicity parameter. We retain global pairwise cohypomonotonicity, remove the global operator-Lipschitz requirement, and add Lipschitz-Jacobian regularity with a stronger oracle. Thus this is not an improvement under identical first-order assumptions. Jacobian Lipschitzness is the standard second-order regularity in the higher-order monotone baselines above.
* The repository's [adjoint-based cohypomonotone result](AdjointAcceleratedCohypomonotone.md) is an additional relevant amortized-inversion precedent. Its global Lipschitz assumption and adjoint-vector oracle differ. It is not replaced by this full-Jacobian theorem.

Two explicit reductions are useful for assessing the gain. A generic bounded-ball implementation of monotone second-order acceleration through the inverse transformation gives the reconstructed upper bound

\[
\widetilde O\bigl(q^2+(1+q)Q^{2/5}\bigr).
\]

Applying inverse-Halpern instead gives $\widetilde O(q^2+Q/q)$. Optimizing its shift subject to $q\ge q_{\min}=1+2\rho HR$ yields $\widetilde O(\max\{q_{\min}^2,Q^{2/3}\})$. These are upper bounds obtained by composing established ingredients, not published lower bounds on wrappers or on Halpern implementations. The present analysis obtains

\[
\widetilde O\bigl(q_{\min}^2+Q^{2/5}\bigr).
\]

For example, when $Q\to\infty$ and $q_{\min}=\Theta(Q^\alpha)$, $0<\alpha<1/5$, it gives exponent $2/5$, versus $2/5+\alpha$ for uniform-cost accelerated simulation and $2/3$ for optimized inverse-Halpern. At bounded $q_{\min}$, uniform accelerated simulation already has exponent $2/5$. When the quadratic initialization term dominates, the new bound need not improve total complexity. These are comparisons up to logarithms and universal constants, not pointwise dominance of numerical budgets.

## Scope, examples, and limitations

Global pairwise cohypomonotonicity is stronger than a weak-Minty condition relative to one root. The theorem does not cover arbitrary nonconvex–nonconcave games, stochastic oracles, constraints, nonsmooth inclusions, or an unknown radius. The root and radius assumptions are the standard distance-based normalization for residual oracle complexity. Positive $H$ may be any valid upper bound, so affine maps with zero actual Jacobian variation are included. The assumptions impose neither bounded cumulative errors nor a convergence certificate.

A nonlinear interacting family in every even dimension is obtained by taking an orthogonal skew-symmetric map $J$, $m>3$, and

\[
F(x)=\nabla(1+\|x\|^2)^{3/2}-mx+4mJx.
\]

It has root zero, globally Lipschitz Jacobian with an absolute upper bound $H=12$, unbounded Jacobian norm, and is nonmonotone near zero. For a displacement $d$, the gradient difference is $Sd$, with symmetric $S$ whose eigenvalues lie in $[\lambda,2\lambda]$ for some $\lambda\ge3$. If $\lambda\ge2m$, the component of the operator difference along $d$ has magnitude at least $m\|d\|$; if $\lambda<2m$, its orthogonal skew component has magnitude at least $3m\|d\|$, using $\|(S-3\lambda I/2)d\|\le\lambda\|d\|/2$. Hence $\|F(x)-F(y)\|\ge m\|x-y\|$, while its inner product with $x-y$ is at least $-m\|x-y\|^2$, giving cohypomonotonicity with $\rho=1/m$. The radial term couples the coordinates. This family illustrates nonlinear, nonmonotone, unbounded-Jacobian scope; it may admit easier specialized methods and is not a hardness or application claim. The setup's motivation is the established cohypomonotone equation problem, not a restriction inferred from this example.

The proof and guarantee hold in arbitrary finite dimension, without separability, a prescribed spectrum, or a quadratic restriction. Dimension-dependent cutting-plane methods can be preferable in fixed dimension. No universal optimality, optimal dependence on $\rho$, randomized lower bound, or superiority to all specialized algorithms is claimed. The contribution requires both the full-Jacobian access and the new accounting of its nested calls; deleting either qualification would overstate it.

The literature assessment used the publicly available 2026 and 2025 ICML, ICLR, and NeurIPS material and approximately the preceding two years of arXiv submissions/revisions, then followed older primary references. Conference status was checked through official proceedings/downloads or OpenReview; arXiv-only work above is labeled accordingly. Some virtual-conference pages were inaccessible, so official proceedings/downloads were used. The comparison is current to the task's 27 October 2026 survey and does not treat a missing search hit as evidence of novelty.

## Formal proof organization

The [algorithm](../Algorithms/CohypomonotoneNewton.lean) contains all executable choices and uses only public parameters and observed replies. The specification does not restrict admissible algorithms to this implementation. The transformation and inverse lemmas are in [Transform](../Proofs/CohypomonotoneNewtonTransform.lean) and [Inverse](../Proofs/CohypomonotoneNewtonInverse.lean); [Geometry](../Proofs/CohypomonotoneNewtonGeometry.lean), [Energy](../Proofs/CohypomonotoneNewtonEnergy.lean), [Search](../Proofs/CohypomonotoneNewtonSearch.lean), and [Outer](../Proofs/CohypomonotoneNewtonOuter.lean) establish the robust estimates. [Run](../Proofs/CohypomonotoneNewtonRun.lean) proves accuracy of the actual program. [Work](../Proofs/CohypomonotoneNewtonWork.lean), [Cost](../Proofs/CohypomonotoneNewtonCost.lean), and [Budget](../Proofs/CohypomonotoneNewtonBudget.lean) count the active execution prefix and simplify its cost; [Execution](../Proofs/CohypomonotoneNewtonExecution.lean) connects it to `execute`. The analysis-only inverse and continuing trajectory are never supplied as oracle information, and cost bounds are applied only before the actual stopping point.
