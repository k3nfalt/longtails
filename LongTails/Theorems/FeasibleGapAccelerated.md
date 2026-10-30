# Acceleration under feasible-domain Hessian–gap bounds

The [Lean theorem](FeasibleGapAccelerated.lean) constructs the [accelerated proximal algorithm](../Algorithms/FeasibleGapAccelerated.lean) for the [feasible Hessian–gap specification](../Setups/FeasibleHessianGapComposite.lean). The contribution is a parameter-explicit guarantee for constrained composite optimization when curvature is controlled only on feasible points. It is not a claim that constrained acceleration or acceleration under local smoothness was previously unknown.

## Problem and oracle

Minimize $F=f+\psi$ over a convex set $Q$, with a minimizer $s\in Q$, feasible initial point $x_0$, and known bounds

\[
\|x_0-s\|\le R,\qquad F(x_0)-F(s)\le\Delta.
\]

Both terms are convex on $Q$. At every feasible point the smooth term has a gradient and a Fréchet derivative of its gradient, represented by a positive semidefinite bounded linear operator $H(x)$, satisfying

\[
\|H(x)\|\le H_0+H_1(F(x)-F(s)).
\]

The specification requires this derivative at feasible points, not a globally convex extension or a globally bounded Hessian. It does not require continuity of the Hessian. The theorem covers real Hilbert spaces, in particular arbitrary finite dimension. Exact proximal minimizers are assumed available; closedness of $Q$ is not separately assumed.

One oracle call returns either the gradient at a feasible query or the ordinary Euclidean proximal minimizer of

\[
\psi(u)+\langle v,u-z\rangle+\|u-z\|^2/(2a),\qquad u\in Q,
\]

for $a>0$. No objective values, full-objective proximal map, extra level-set projection, or minimizer coordinates are supplied. Gradient answers outside $Q$ may be arbitrary. The proof establishes feasibility of every gradient query, including padding queries within the prescribed plan. Known parameters are $H_0,H_1,R,\Delta,\varepsilon$; the algorithm does not adapt to unknown versions of these bounds.

## Algorithm and guarantee

The algorithm uses cumulative linear models of $f$, the exact regularizer prox, convex combinations for primal and query points, and predetermined halving restarts. Its returned output is the final primal iterate, rather than a selected best iterate. Every active step costs one gradient and one prox call. Completed phases retain their state and count both unused padding calls.

For $H_0,H_1\ge0$ and $R,\Delta,\varepsilon>0$, the public budget is

\[
\left\lceil 2^{24}\left(1+R\sqrt{H_0/\varepsilon+H_1}\right)
\log^2\!\left(4+R^2(H_0/\varepsilon+H_1)\right)
\log\!\left(2+\Delta/\varepsilon\right)\right\rceil.
\]

The output is feasible and satisfies $F(x_{\rm out})-F(s)\le\varepsilon$. The formal specification expresses this almost surely under the framework's oracle seed law; the proof actually holds for every seed sequence. It is a deterministic guarantee and assumes no stochastic error model. If $\Delta\le\varepsilon$, no phase is needed.

The large universal constant simplifies rounding and parameter expressions; no practical constant-factor advantage is claimed. There is no dimension factor in the oracle count, but the cost of implementing one proximal call is outside this oracle model.

## Proof mechanism

Analysis shifts the objective into two nonnegative feasible-domain terms:

\[
h(x)=f(x)-f(s)-\langle\nabla f(s),x-s\rangle,
\quad j(x)=\psi(x)-\psi(s)+\langle\nabla f(s),x-s\rangle.
\]

Their sum is the objective gap. These shifts are not computed by the algorithm. A dyadic decomposition of the feasible segment from $s$ to $x$, with positive semidefinite Hessian bound $M$, proves

\[
\|\nabla h(x)\|\le K\sqrt{Md}+MR2^{-K}
\]

when the segment has objective gap at most $d$ and length at most $R$. This replaces an ambient-space gradient self-bound whose usual descent-point proof may leave the feasible domain.

A cumulative proximal certificate controls $j$ at the auxiliary prox point. A compact-maximum argument on each short feasible segment absorbs the unknown maximum of $h$ into the Hessian bound. Thus the local quadratic model is derived before using it in the accelerated energy inequality. Comparing the new prox minimizer with the old one controls its displacement before asserting the new energy certificate. Initialization uses a separately smaller step. These steps prevent circular assumptions about the gap at extrapolated or tentative points.

The dyadic estimate and potential algebra are supporting ingredients, not separate claimed research contributions. The central claim is their combination into a feasible-domain, parameter-explicit accelerated guarantee under this oracle model.

## Comparisons and limitations

The motivating [Yu–Lin preprint, arXiv:2610.33761v1](https://arxiv.org/html/2610.33761v1), Definition 1 and deterministic Theorem 1, analyzes Nesterov acceleration under relaxed smoothness including objective-gap-dependent curvature. This result changes the setting to composite constrained problems with curvature required only on feasible points. It does not improve that paper's deterministic iteration exponent on its original unconstrained class. Conference acceptance status of the motivating manuscript was not verified from the inaccessible OpenReview forum.

The existing repository [CompositeGapAccelerated theorem](CompositeGapAccelerated.lean) and [contribution note](CompositeGapAccelerated.md) use an ambient local quadratic model. The present result replaces that ambient model by curvature control on feasible points, but also explicitly assumes gradient differentiability and a positive semidefinite Hessian. Consequently its instance class is not literally a superset of that earlier differentiability-only model class. The new guarantee covers intrinsic constrained-domain examples unavailable to an ambient convex-extension argument, at the cost of an additional logarithmic factor and the Hessian formulation. This comparison concerns the actual assumptions, rather than the names of the setups.

[Lobanov–Dvinskikh–Gasnikov, arXiv:2609.33415v1](https://arxiv.org/abs/2609.33415v1), Theorem 9, is a stronger direct baseline for objective-gap-dependent curvature than the motivating manuscript alone. Its deterministic specialization has accelerated smooth ambient-space dependence of order $J+R\sqrt{H_0/\varepsilon}+R\sqrt{H_1}J$ up to its logarithmic factors, where $J$ is the stage count. We do not improve that smooth ambient guarantee. The difference is the constrained composite oracle model and a proof using only feasible Hessian control; transferring the ambient result would require a suitable extension or stronger proximal operations. The extra logarithmic overhead here must be retained in this comparison.

[Lu–Mei, arXiv:2206.01209v3](https://arxiv.org/abs/2206.01209), Theorems 1–2, already establishes accelerated proximal convergence under local Lipschitz smoothness. Its quoted complexity uses a local Lipschitz constant over a solution-centered region and its enlargement. The distinction here is an explicit bound in $H_0,H_1,R,\Delta,\varepsilon$, without objective-value queries. A large local-ball curvature need not force the older algorithm to run slowly; the comparison is between proved guarantees.

[Auto-conditioned fast gradient, arXiv:2310.10082v3](https://arxiv.org/abs/2310.10082), Section 2, equation (2.13), and Corollary 1, gives adaptive composite acceleration in terms of encountered curvature. Its displayed curvature estimator uses function values, and its smoothness conditions include an asymmetric gradient/Bregman bound. A feasible PSD Hessian bound supplies symmetric cocoercivity; it does not automatically provide that stronger extension property. Substitution into its rate leaves the required localization unresolved.

[Lan's accelerated bundle-level framework, arXiv:1309.5547](https://arxiv.org/abs/1309.5547), uses objective values and projections with additional level constraints. Such operations are not the ordinary regularizer prox assumed here. Replacing the domain with an unknown low objective sublevel set would therefore change the oracle. Generic bounded-subgradient optimization loses the square-root curvature dependence. These observations rule out those direct reductions, not all possible future reductions.

Classical globally smooth constrained accelerated proximal methods are sharper when $H_1=0$: this guarantee adds logarithmic factors. No optimality or matching lower bound is asserted. The relevant improvement is the parameter dependence and feasible-domain scope, not universal superiority over accelerated methods.

## Intrinsic nonlinear family

Let $Q=\{(u,t):t\ge1\}$, with dense invertible $A$, nonzero $a$, and

\[
f(u,t)=\|Au\|^2/t+e^{a^Tu},\qquad
\psi(u,t)=\lambda t-a^Tu,\quad\lambda>0.
\]

The minimizer is $(0,1)$. The gap is

\[
\|Au\|^2/t+e^{a^Tu}-a^Tu-1+\lambda(t-1).
\]

Using $e^q\le2(e^q-q-1)+2$, the Hessian bound holds with
$H_0=4\|A\|^2+2\|a\|^2$, $H_1=4+2\|a\|^2$.
The perspective Hessian norm is bounded by $4\|A\|^2+4\|Au\|^2/t$ on $t\ge1$. Coordinates interact through dense $A$ and $a$; this is not a scalar or quadratic-only family. The regularizer prox is an affine shift followed by projection onto $t\ge1$.

Normalize $\|A\|=\|a\|=\lambda=1$ and start at $(-Ra,1)$. Then $H_0=H_1=6$ suffice and $\Delta\le R^2+R$, whereas the feasible ball of radius $R$ around the minimizer contains $(Ra,1)$, where curvature is at least $e^R$. The new bound is polynomial in $R$, up to logarithms, rather than inserting this exponential local curvature into a generic local-smoothness bound.

Nor can a finite globally convex extension agreeing with this smooth term on $Q$ be assumed for free. Tangent planes at interior points $(u,2)$, evaluated at $(0,-1)$, have value $\|Au\|^2/4+(1-a^Tu)e^{a^Tu}$. Taking $u=-ra$ sends these values to infinity. A finite convex extension would have to dominate all of them. This is a substantive domain obstruction. The example calculations motivate and compare the setup; the general convergence proof is formalized, while these example calculations are explanatory mathematics.
