# Accelerated composite optimization with total-gap curvature

[The theorem](CompositeGapAccelerated.lean) proves an oracle-complexity guarantee for convex composite optimization under a local curvature bound controlled by the **total composite objective gap**. The [setup](../Setups/CompositeGapSmooth.lean) permits arbitrary real Hilbert spaces, hence general nonlinear objectives in every finite dimension. The [algorithm](../Algorithms/CompositeGapAccelerated.lean) uses exact gradients and ordinary Euclidean proximal queries. Its output is the final accelerated primal point, not the last prox point or a best iterate selected using function values.

## Statement and information model

Minimize $F=f+\psi$ over a convex set $Q$. The smooth part is globally convex and differentiable; $\psi$ is real-valued and convex on $Q$. There is a minimizer $s\in Q$, an initial feasible point $x_0$, and known bounds

\[
\|x_0-s\|\le R,\qquad F(x_0)-F(s)\le\Delta,
\qquad R,\Delta,\varepsilon>0,\quad H_0,H_1\ge0.
\]

For every feasible anchor $x$ and every **ambient** point $y$ with $\sqrt{H_1}\|y-x\|\le1$, assume

\[
f(y)\le f(x)+\langle\nabla f(x),y-x\rangle
  +[H_0+H_1(F(x)-F(s))]\|y-x\|^2.
\]

This is an explicit local quadratic-model assumption, not a claim that a Hessian bound at a single point implies the displayed neighborhood inequality. The ambient quantifier is essential: feasible-pairs-only smoothness does not justify the shifted-gradient self-bound used in the proof. When $H_1=0$, the neighborhood restriction disappears. No bound on $\nabla f(s)$, nonsmooth subgradients, or the diameter of $Q$ is imposed. Proximal minimizers are assumed to exist for all positive steps and centers; no separate closedness assumption is used.

A gradient query returns $\nabla f(x)$. A prox query $(a,c,v)$ returns a minimizer over $Q$ of

\[
\frac{\|u-c\|^2}{2a}+\langle v,u-c\rangle+\psi(u),\qquad a>0.
\]

Each is one oracle call. The method knows $H_0,H_1,R,\Delta,\varepsilon,x_0$, but not $s,F(s),\nabla f(s)$, function values, or a prox operator for intersections with extra balls. Exact replies may be represented using arbitrary oracle seed spaces; the guarantee holds for every seed realization. The setup places no artificial restriction on competing algorithms.

The returned point $\widehat x\in Q$ satisfies $F(\widehat x)-F(s)\le\varepsilon$ within

\[
\left\lceil8192\bigl(1+R\sqrt{H_0/\varepsilon+H_1}\bigr)
\log\bigl(4+R^2(H_0/\varepsilon+H_1)\bigr)
\log\bigl(2+\Delta/\varepsilon\bigr)\right\rceil
\]

calls. There is no dimension factor. This is an upper bound, not an optimality claim. Both logarithms are retained; in particular, the $\sqrt{H_0/\varepsilon}$ term also carries the restart logarithm.

## Algorithm and technical contribution

In a phase with starting center $c$, gap bound $d$, and distance bound $R$, set

\[
M=H_0+H_1d+d/R^2,\quad D=MR^2/d,\quad
\theta=[128(1+\sqrt D)]^{-1},\quad A_{\rm goal}=R^2/d.
\]

The first gradient/prox update has weight $a_0=1/(16M)$. Subsequently choose
$a=\min\{A_{\rm goal}-A,A\theta/(1-\theta)\}$, query
$y=(Ax+az)/(A+a)$, accumulate $v^+=v+a\nabla f(y)$, and compute

\[
z^+=\operatorname{prox}(A+a,c,v^+/(A+a)),\qquad
x^+=(Ax+az^+)/(A+a).
\]

The cumulative weight stops at $A_{\rm goal}$. Each phase executes the fixed number

\[
N=\left\lceil256(1+\sqrt{1+2H_0R^2/\varepsilon+H_1R^2})
\log[32(1+2H_0R^2/\varepsilon+H_1R^2)]\right\rceil
\]

of two-call updates. After reaching the cap, counted padding queries preserve the output. There are $S=\lceil\log(\Delta/\varepsilon)/\log2\rceil_+$ phases with $d_k=\Delta/2^k$. For $\varepsilon\ge\Delta$, $S=0$ and the output is $x_0$. The proof counts all $2NS$ calls and any padding to the public budget.

Accelerated dual averaging, affine shifts, and geometric restart are established techniques. The new part is the control of nonsmooth values at extrapolation points under total-gap curvature, without a stronger prox oracle:

1. For analysis only, write $h=f-f(s)-\langle\nabla f(s),\cdot-s\rangle$ and $j=\psi-\psi(s)+\langle\nabla f(s),\cdot-s\rangle$. Then $h\ge0$ everywhere, $j\ge0$ on $Q$, and $h+j=F-F(s)$. The ambient local model yields a shifted-gradient bound on each composite sublevel set.
2. Compare the cumulative prox objective at its minimizer $z$ with the phase center $c$. If accumulated shifted gradients are bounded by $AG$, this gives $j(z)\le d+2RG$, with **no $1/A$ term**. The all-comparator estimate sequence separately keeps $F(x)\le F(c)$ and both primal/prox distances to $s$ at most $R$. The short extrapolation therefore has $F(y)-F(s)\le2d$.
3. Before assuming the new energy inequality, strong convexity of the old cumulative model and optimality of the new prox point give
$\|z^+-z\|^2/2\le aG\|z^+-z\|+a j(z)$.
The chosen weight makes $\|z^+-z\|\le R$, establishing the local model at the actual updated point without circularity. Only then does the accelerated energy inequality follow.
4. At the cap, the energy gives gap at most $d/2$, and the same minimizer-distance bound survives restart. Initialization has its own prox-comparison/self-bound argument, so it does not assume the invariant it establishes.

The key modules are [geometry](../Proofs/CompositeGapGeometry.lean), [shifted models](../Proofs/CompositeGapModel.lean), [phase localization](../Proofs/CompositeGapPhase.lean), [active updates](../Proofs/CompositeGapAdvance.lean), [weight growth](../Proofs/CompositeGapGrowth.lean), [execution](../Proofs/CompositeGapRun.lean), and [budget algebra](../Proofs/CompositeGapBudget.lean). All minimizer-dependent shifts and certificate constants are proof-only.

## Motivation, comparison, and limitations

The assumption captures exponential losses with ordinary convex regularization. For $f(x)=\sum_i w_i e^{\langle a_i,x\rangle}$, $w_i>0$, $\|a_i\|\le\alpha$, and nonnegative $\psi$ with $\psi(0)=0$, one has $F(s)\le W=\sum_iw_i$, $f(x)\le F(x)-F(s)+W$, and neighboring Hessians bounded by $\alpha^2e^{\alpha\|y-x\|}f(x)$. Consequently $H_0=e\alpha^2W$, $H_1=e\alpha^2$ suffice for the stated ambient model when $\alpha>0$. The constants come from the data; no optimal value is required. They can be conservative. Constraints may be included when $0\in Q$ and the required prox is available.

A concrete comparison regime is

\[
f_\delta(x,y)=e^{x+\delta y}+e^{-x+\delta y},\qquad
\psi_\delta(x,y)=|x|+2\delta|y|,\qquad 0<\delta\le1.
\]

Its unique minimizer is $(0,0)$, $F(s)=2$, and $\nabla f(s)=(0,2\delta)$. From $x_0=(0,1/\delta)$, take $R=1/\delta$, $\Delta=2e$. The ambient model holds with $H_0=2e,H_1=e$, uniformly in $\delta$. Along $(0,y)$ as $y\to\infty$, every finite global Hessian bound $\|\nabla^2f\|\le L_0+L_1\|\nabla f\|$ requires $L_1\ge1/\delta$. Thus the displayed startup term of the existing [composite generalized-smooth guarantee](CompositeGeneralizedAccelerated.md), $(1+L_1R)\log(2+\cdots)$, is at least order $\delta^{-2}$. At the joint accuracy regime $\varepsilon=\delta$, the new budget is $O(\delta^{-3/2}\log^2(1/\delta))$. The regularizer has global Lipschitz constant $G_\psi=\sqrt{1+4\delta^2}$, so the uniform Moreau-smoothing reduction below also has a displayed $RG_\psi/\varepsilon=\Theta(\delta^{-2})$ term. Thus this regime gives a polynomial separation from both checked generic guarantees. This is **not a lower bound on algorithms or smoothing**, and does not compare against solvers exploiting the example's special geometry. In particular, at fixed accuracy Moreau smoothing matches the new bound's polynomial dependence on $\delta$; no separation is claimed there. The fixed coefficient of $|x|$ is an ordinary sparsity penalty and does not grow with the comparison parameter. Dense nonorthogonal spanning features in $2e^{\delta y}\sum_iw_i\cosh(\langle b_i,u\rangle)$ give interacting nonlinear examples in arbitrary dimension with bounded feature norms.

The nearest primary analyses and checked reductions are:

- Xiao, [Dual Averaging Methods for Regularized Stochastic Learning and Online Optimization, JMLR 2010](https://jmlr.org/papers/v11/xiao10a.html), Section 7.1 and Appendix B, already develops accelerated regularized dual averaging and its cumulative-model proof under global smoothness. The algorithmic template and one-step energy algebra are prior work; the contribution here is the additional localization mechanism needed when curvature depends on the total composite gap.

- Lobanov, [arXiv:2608.04884v1](https://arxiv.org/html/2608.04884v1), Section 4.1 and Appendix B, establishes accelerated smooth-only gap-curvature bounds using low-dimensional relaxation. Lobanov, Dvinskikh, and Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/html/2609.33415v1), Theorems 9–10 and Appendix H.3, supplies stronger stochastic and deterministic specializations with projection/localization. These are preprints, not asserted conference acceptances. Their square-root curvature dependence is already known. The present contribution is its composite extension under the explicitly stated ambient local model using ordinary prox calls. It does not improve their smooth-only accuracy dependence; extra logarithms and exact-oracle restrictions remain.
- Li and Lan, [AC-FGM, arXiv:2310.10082v3](https://arxiv.org/abs/2310.10082v3), Corollary 1 and equation (2.13), already gives adaptive accelerated composite guarantees in terms of the largest encountered local curvature and uses function values. That bound alone does not bound the total composite gap at extrapolated queries. Substituting $H_0+H_1d$ before proving query localization would assume the missing property. We do not claim that AC-FGM cannot enjoy a better specialized analysis.
- Bok and Altschuler, [Mathematical Programming, June 2026](https://link.springer.com/article/10.1007/s10107-026-02377-7), Theorem 3.4 (Theorem 2.6 in arXiv:2506.23756v1), gives a composite conversion based on global cocoercivity and method-specific rank-one/positive-semidefinite certificates. Those premises do not provide the local total-gap query bound here; it is not a blanket conversion of every local smooth-only acceleration theorem.
- The existing [gradient-only composite backtracking result](BacktrackingCompositeGeneralized.md) already removes function-value access in the gradient-dependent smoothness setting. Gradient-only access by itself is therefore not the novelty. Its $L_1R$ startup guarantee and the stronger composite result above are included in the comparison, rather than comparing only with unaccelerated proximal gradient.

A concrete smoothing reduction is available on the smaller unconstrained class with globally $G_\psi$-Lipschitz $\psi$, $G_\psi>0$ (constant regularizers need no smoothing). Its Moreau envelope obeys $0\le\psi-\psi_\lambda\le\lambda G_\psi^2/2$. Taking $\lambda=\varepsilon/G_\psi^2$ and solving $f+\psi_\lambda$ to gap $\varepsilon/2$ gives original gap at most $\varepsilon$. The smoothed objective satisfies the ambient model with $H_0'=H_0+H_1\varepsilon/2+G_\psi^2/(2\varepsilon)$ and unchanged $H_1$: use $F-F_*\le F_\lambda-F_{\lambda,*}+\lambda G_\psi^2/2$ and the envelope's $1/\lambda$ gradient-Lipschitz bound. Each smoothed gradient costs one original gradient and one prox. When a comparable radius bound for a smoothed minimizer is available, applying smooth-only gap-curvature acceleration gives, up to its logarithms, $R\sqrt{H_0/\varepsilon}+RG_\psi/\varepsilon+R\sqrt{H_1}$ plus phase-count terms. For the displayed family, the smoothed minimizer has $x_\lambda^*=0$ and $y_\lambda^*\in[-2\lambda\delta,0]$, from the scalar condition $y/\lambda+2\delta e^{\delta y}=0$; hence its initial distance is at most $R+2\lambda\delta=O(R)$ in the stated regimes. A comparable smoothed-minimizer radius is not asserted for the general class. This explains both the matching fixed-accuracy behavior and the weaker joint regime above. The present theorem needs no Lipschitz regularizer assumption and has no $G_\psi/\varepsilon$ term. Without that extra assumption there is no uniform envelope-error bound of this form; with constraints, smoothed queries can also leave the set of allowed model anchors. A Moreau envelope of the full objective would require a joint prox unavailable from the stated oracle. These observations block the checked standard reduction, not every possible more refined reduction.

Replacing the local model by a global smoothness constant on a radius-$R$ ball can be much weaker: even the exponential family has exponentially large curvature on that ball. Restricting iterates by a ball-intersection prox would change the oracle model. Applying a smooth-only result to $F$ is invalid for nonsmooth $\psi$; regularizing $\psi$ changes smoothness and introduces accuracy-dependent approximation and oracle costs. None supplies the proved cumulative-prox localization by direct substitution. A more efficient general reduction remains possible; no lower bound excluding one is claimed.

The literature comparison was checked through 26 October 2026, including the two latest publicly available editions surveyed for ICML, ICLR, and NeurIPS, recent arXiv work, and foundational composite analyses. The precise local composite assumption is a new formulation motivated by these established models, not attributed verbatim to a prior smooth-only theorem. The result does not cover merely feasible-pair curvature, stochastic or inexact prox oracles, unknown tuning bounds, or barriers without a globally defined differentiable smooth part. It offers a new general composite guarantee and the explicit parameter regime above, not universal superiority or an optimal rate.
