# Nesterov acceleration under local strong aiming without projection regularity

The result extends ordinary, fixed-parameter Nesterov acceleration from an affine minimizer set to a minimizer set with no separately imposed geometric regularity. The objective may be nonconvex and need not have a continuous Hessian. In particular, neither differentiability nor uniqueness of nearest-point projection is assumed. The new ingredient is an exact distance-potential cancellation, which avoids approximating the minimizer set by tangent spaces.

The formal result is [LocalStrongAimingNesterov.lean](LocalStrongAimingNesterov.lean), with [setup](../Setups/LocalStrongAiming.lean), [algorithm and output](../Algorithms/NearestAimingNesterov.lean), and [execution/compliance proof](../Proofs/NearestAimingExecution.lean).

## Setup and guarantee

Let $E$ be any finite-dimensional real Euclidean space. The globally differentiable objective $f:E\to\mathbb R$ attains its minimum $f_*=f(x_*)$, and $M=\{x:f(x)=f_*\}$. Write $d(x,M)$ for Euclidean distance and $U_r=\{x:d(x,M)<r\}$, where $r>0$. Assume $0<\mu\le L$, and, for all $x,y\in U_r$,

\[
\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|,
\qquad
f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle
 -\sqrt{\mu L}\|y-x\|^2.
\]

Thus the weak-convexity constant is $2\sqrt{\mu L}$. For every $x\in U_r$ and every nearest minimizer $p\in M$, assume the established **strong aiming** condition

\[
\langle\nabla f(x),x-p\rangle
 \ge f(x)-f_*+\frac\mu2\|x-p\|^2.
\]

These are objective conditions on the tube, not conditions on the generated trajectory. The tube need not be convex; the two-point inequalities above are required for all its pairs. The initialization satisfies

\[
x_0\in U_r,\qquad f(x_0)-f_*\le\Delta,
\qquad 0\le\Delta\le\frac{\mu r^2}{256}.
\]

Both initial tube membership and the gap condition are explicit. A small gap alone does not certify membership in a locally controlled region.

Set $\eta=1/(4L)$, $q=\sqrt{\mu\eta}$, and $\beta=(1-q)/(1+q)$. Starting with $v_0=0$, the algorithm executes

\[
y_k=x_k+\sqrt\eta\,v_k,\qquad
x_{k+1}=y_k-\eta\nabla f(y_k),\qquad
v_{k+1}=\beta\bigl(v_k-\sqrt\eta\nabla f(y_k)\bigr).
\]

Equivalently, $y_{k+1}=x_{k+1}+\beta(x_{k+1}-x_k)$. This is ordinary Nesterov momentum, with no restarts. Its output is the last primal iterate $x_K$, named `nesterovOutput` in Lean. Each update queries exactly one gradient at $y_k$. There are no value, Hessian, projection, or line-search queries, and no extra initialization query.

All primal and extrapolated query points remain in $U_r$, and the supporting induction proves

\[
f(x_K)-f_*\le 2\Delta
 \left(1-\frac12\sqrt{\frac\mu L}\right)^K.
\]

The public accuracy theorem uses the single explicit budget

\[
K=\left\lceil 2\sqrt{\frac L\mu}
 \log\left(1+\frac{2\Delta}{\varepsilon}\right)\right\rceil,
\qquad \varepsilon>0,
\]

and establishes $f(x_K)-f_*\le\varepsilon$ after exactly $K$ oracle calls. This includes $\Delta=0$, when $K=0$. Dimension enters only through the specified problem constants.

The update receives only $E,L,\mu,x_0$. The tube radius and gap bound are analysis parameters. The theorem prescribes an external horizon using $\Delta,\varepsilon$; it does not provide an observable stopping certificate when the gap is unknown.

The frozen repository predicate `Convergence` existentially quantifies an algorithm. The setup additionally specifies `FollowsNesterov` through exact initial-state, query, update, and output equations. The theorem's witness is the value of `certifiedNesterov`, whose subtype carries a proof of those equations. `execute_nesterov` identifies its actual output with `nesterovOutput` and its actual call count with $K$, for every oracle seed. The generic framework has not been changed to restrict all existential witnesses to this algorithm family.

## Technical mechanism

For any nonempty closed $M\subset E$, define

\[
\phi(z)=\frac12\bigl(\|z\|^2-d(z,M)^2\bigr)
 =\sup_{p\in M}\{\langle z,p\rangle-\tfrac12\|p\|^2\}.
\]

This function is convex even when $M$ is nonconvex. Every nearest point $p_y$ is a subgradient of $\phi$ at $y$. Consequently

\[
D_\phi(x,y)=\phi(x)-\phi(y)-\langle p_y,x-y\rangle\ge0.
\]

The Lean proof derives the supporting-plane inequality and convexity directly from nearest-point optimality; it does not assume projection smoothness or a convergence-related geometry bound. See [NearestSetPotential](../Proofs/NearestSetPotential.lean).

Writing $a=\sqrt\mu$, $s=\sqrt\eta$, use the energy

\[
\mathcal E(x,v)=f(x)-f_*+
 \frac12\|v+a(y-p_y)\|^2+\frac asD_\phi(x,y),\qquad y=x+sv.
\]

Although this expression uses a selected nearest point, its value is selection-independent:

\[
\mathcal E(x,v)=f(x)-f_*+\frac{1+q}{2}\|v\|^2
 +\frac{q(1+q)}{2\eta}d(y,M)^2
 -\frac q{2\eta}d(x,M)^2.
\]

Let $z=x_{k+1}$, $w=v_{k+1}$, and $Y=z+sw$. The exact correction to the squared-norm part when the footpoint changes from $p_y$ to $p_Y$ is

\[
\frac12\|w+a(Y-p_Y)\|^2-\frac12\|w+a(Y-p_y)\|^2
=-\frac q\eta(1+q)D_\phi(Y,y)
-\frac q\eta D_\phi(z,Y)
+\frac q\eta D_\phi(z,y).
\]

The Nesterov recurrence gives $z=\frac{1+q}{2}Y+\frac{1-q}{2}x$. Convexity in the first argument bounds the last divergence by the corresponding weighted sum at $Y,x$. Together with descent, strong aiming, and weak convexity, this yields the exact contraction $\mathcal E_{k+1}\le(1-q)\mathcal E_k$. This is proved in [NearestSetEnergy](../Proofs/NearestSetEnergy.lean); no uncontrolled curvature remainder is discarded.

Strong aiming implies local quadratic growth by applying its scalar differential inequality along the segment from a nearest minimizer to $x$. Hence $\mathcal E_0\le2\Delta$. Energy controls both momentum and query distance. The explicit small-gap condition ensures the entire next gradient segment and extrapolated point stay in the tube, closing the induction without assuming containment. See [local calculus](../Proofs/NearestSetLocal.lean), [containment](../Proofs/NearestSetContainment.lean), and [convergence](../Proofs/NearestAimingConvergence.lean). The budget proof reuses the repository's established geometric-decay tuning lemma.

## Closest results and precise contribution

* **Gupta–Wojtowytsch, ICLR 2025**, [arXiv:2410.08395v3, 13 May 2025](https://arxiv.org/abs/2410.08395v3), Theorem 11 and Appendix B.2, is the main baseline. Its ordinary-NAG theorem uses the same strong aiming condition and weak-convexity threshold $\rho\le\sqrt{\mu/\eta}$, but assumes an affine nearest projection. Its guarantee contracts at factor $1-\sqrt{\mu\eta}$ per exact gradient call, and its energy separates velocity with constant tangent/normal projectors. At our step size this is the same factor $1-\tfrac12\sqrt{\mu/L}$. The present result removes that affine-projection assumption and imposes no replacement projection regularity. The baseline is global under its global objective conditions; our local objective assumptions require the explicit local initialization condition above. Thus the contribution broadens minimizer geometry while retaining the accelerated rate locally, rather than enlarging every aspect of the baseline class. No improvement in the already accelerated condition-number exponent is claimed.
* **Feng–Yuan**, [arXiv:2603.21516v1, 23 March 2026](https://arxiv.org/abs/2603.21516v1), Theorems 2.1–2.2, proves local ordinary-NAG convergence under $C^2$ regularity and PL, with an implicit sufficiently small neighborhood. The classes are incomparable: the present theorem permits discontinuous Hessians and nonsmooth projection, but strong aiming and weak convexity are stronger objective hypotheses than PL alone. It does not improve their sharp local spectral rate on their class.
* **Hermant et al.**, [arXiv:2512.16533v2, 6 January 2026](https://arxiv.org/abs/2512.16533v2), Theorem 20 and Remark 22, relaxes minimizer geometry for a continuized, randomized-parameter method and discusses local projection extensions. **Hermant**, [arXiv:2602.10022v2, 11 June 2026](https://arxiv.org/abs/2602.10022v2), studies PL with fixed-minimizer or trajectory-averaged aiming. Neither supplies the present fixed-parameter Euclidean NAG theorem for moving nearest minimizers.
* **Aujol et al.**, [arXiv:2403.06930v2, 16 January 2025](https://arxiv.org/abs/2403.06930v2), Theorems 1–2 and Section 5, already uses moving-projection distance energies for convex composite quadratic-growth problems. Novelty here is not the use of a distance energy. Their convex-set projection sign is unavailable for nonconvex minimizer sets: on the unit circle, $p=(1,0)$, $x=(1-\delta,0)$, and $z=(\cos\theta,\sin\theta)$ give $\langle x-p,z-p\rangle=\delta(1-\cos\theta)>0$. The convex distance-complement correction above replaces that sign argument.
* **Necoara–Nesterov–Glineur**, [arXiv:1504.06298v4](https://arxiv.org/abs/1504.06298v4), published in *Mathematical Programming* in 2019, Section 5.2.1 and Theorem 14, requires the auxiliary iterates to have a common projection for its accelerated guarantee. The present proof does not assume this trajectory property.

The new guarantee concerns a standard method under inherited objective conditions, with the geometric restriction removed by an exact discrete identity. Ordinary smoothness on a tube, coordinate flattening, or a $C^2$ spectral theorem does not reproduce this result: flattening changes Euclidean momentum, and the examples below need not have a continuous Hessian or differentiable projection. A tangent-space perturbation argument requires additional geometric control that this proof does not use. The result is not a claim that PL alone permits acceleration, or that every closed set can occur under the objective assumptions.

## Nonlinear instances with interacting coordinates

Let $u\in\mathbb R^d$, $v\in\mathbb R^k$, and $r(u,v)=v-\psi(u)$, where $\psi$ is globally $C^{1,1}$, $\|D\psi\|\le A$, and $D\psi$ is $B$-Lipschitz. For weights $0<m\le a_i^\pm\le H$, set

\[
h(r)=\tfrac12\sum_i[a_i^+(r_i^+)^2+a_i^-(r_i^-)^2],\qquad f(u,v)=h(r(u,v)).
\]

This is a nonlinear residual-fitting objective with asymmetric quadratic penalties. Its minimizer set is the graph of $\psi$. Different weights allow arbitrarily different normal stiffnesses. Dense nonlinear features in $\psi$ couple coordinates; neither the theorem nor this family is restricted to quadratics or fixed dimension.

For $B>0$, take $D=\sqrt{1+A^2}$, tube radius $r_0=m/(4HBD)$, $\mu=m/2$, and $L=HD^2+m/4$. For any nearest point $p$, the vertical graph point and the residual Lipschitz bound give

\[
d(x,M)\le\|r(x)\|\le Dd(x,M),\qquad
\|Dr(x)(x-p)-r(x)\|\le\tfrac B2 d(x,M)^2.
\]

Since $\langle\nabla h(r),r\rangle=2h(r)\ge m\|r\|^2$, $\|\nabla h(r)\|\le H\|r\|$, and $\nabla h$ is $H$-Lipschitz, these inequalities prove strong aiming on the tube. The gradient product rule gives the pairwise Lipschitz constant $HD^2+HBD r_0=L$. Convexity of $h$ and the Taylor remainder for $\psi$ give pairwise weak convexity with constant $HBD r_0=m/4\le2\sqrt{\mu L}$. These verifications require no convexity of the tube or uniqueness of nearest points.

For a concrete scalar feature, $\sigma(t)=t_+^2/(1+t_+^2)$ is $C^{1,1}$ but not $C^2$, with $|\sigma'|\le1$ and $\operatorname{Lip}(\sigma')\le2$. Dense sums of these features provide such maps $\psi$; normalized coefficients keep $A,B$ independent of dimension. Unequal $a_i^+,a_i^-$ additionally make the objective Hessian jump at zero residual.

The loss of projection differentiability is real. For the graph $\psi(u)=b\sigma(u)$, the nearest point to $(0,v)$, for $0<v<1/(2b)$, is $(0,0)$. Under horizontal perturbations, the nearest horizontal coordinate has left derivative $1$ and right derivative $1/(1-2bv)$. Thus arbitrarily near this graph the projection need not be differentiable. Dense vector-valued residual models retain the same curvature-jump mechanism.

An initialization $x_0=(u_0,\psi(u_0)+e)$ with $\|e\|\le r_0\sqrt{m/H}/16$ has gap at most $\mu r_0^2/256$ and lies in the tube. This supplies a nonempty polynomial-size basin under explicit constants. Curvature can affect the radius on which the objective hypotheses hold; the theorem adds no separate projection-curvature parameter or shrinkage.

## Scope and literature checks

The result is local, requires supplied $L,\mu$, and does not weaken strong aiming to PL. The tube-wise two-point weak-convexity condition remains essential to this proof. The all-nearest-point formulation adds no selection smoothness: if aiming holds for some nearest point at every point of an open tube, then a fixed nearest point becomes uniquely nearest at interior points of its radial segment; continuity extends the inequality to the endpoint for every nearest point.

Literature was checked independently by the Researcher and Reviewer on 30 September 2026 UTC. Topical coverage included ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025 proceedings and the 2026 public accepted-title list, and arXiv submissions/revisions from approximately September 2024 onward, following older foundational results. NeurIPS 2026 proceedings were not presumed published. This was a targeted survey, not exhaustive reading of every paper.

An author-hosted [PL acceleration companion](https://tobotis.github.io/PL-Accelerated-Nesterov/) by Obreiter, Steinbrecher, and Förster was also checked. Its linked source statements cover $C^2$ objectives and smooth minimizer manifolds, with an existential local neighborhood and modified momentum. The linked manuscript PDF returned 404, so its full paper proof could not be inspected. Its accessible scope does not contain the nonsmooth-projection result above. The 2026 arXiv works are treated as preprints unless acceptance was separately verified; their strength, rather than venue status, determines the comparisons.
