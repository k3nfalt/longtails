# Local acceleration for noninterpolating generalized-smooth finite sums

The [Lean theorem](LocalFiniteSumAcceleration.lean) gives an expected objective-error guarantee for minimizing a convex finite sum with componentwise symmetric generalized smoothness. The contribution is a smaller generalized-curvature startup cost in accelerated finite-sum optimization without interpolation. It does not improve the fixed-parameter accuracy exponent, prove optimality, or assert historical significance comparable to the introduction of accelerated gradient descent.

## Problem and oracle

The [specification](../Setups/GeneralizedSmoothFiniteSum.lean) concerns
\(F(x)=n^{-1}\sum_{i=1}^n f_i(x)\), with convex continuously differentiable components on a real Hilbert space. In particular it covers arbitrary finite dimension and nonlinear, nonseparable objectives. Each component gradient satisfies the symmetric condition
\[
 \sup_{0\le t\le1}\|\nabla f_i(x+t(y-x))\|\le M
 \quad\Longrightarrow\quad
 \|\nabla f_i(x)-\nabla f_i(y)\|\le(L_0+L_1M)\|x-y\|.
\]
The known parameters obey \(L_0,R,\Delta,\epsilon>0\), \(L_1,G\ge0\), and there is a minimizer \(x_*\) with
\[
 \|x_0-x_*\|\le R,\qquad F(x_0)-F(x_*)\le\Delta,
 \qquad n^{-1}\sum_i\|\nabla f_i(x_*)\|\le G.
\]
The algorithm knows these bounds, not the minimizer or its value. An oracle call chooses a component and point and returns the exact pair \((f_i(x),\nabla f_i(x))\). Component values are paid for; this is not a gradient-only guarantee. Exactness is required for every history and oracle seed. The setup does not restrict algorithms to the construction below.

Convexity, initial-distance bounds, and selectable component oracles are standard finite-sum assumptions. The symmetric smoothness condition follows [Gorbunov et al., ICLR 2025, Assumption 1.3 and the componentwise condition in Assumption 7.1](https://arxiv.org/html/2409.14989v2). Our model omits their common-minimizer requirement. The first-moment parameter \(G\) is a new parameterization here, not an assumption attributed verbatim to that paper. It can be bounded by the usual root-mean-square optimum component-gradient norm; it permits nonzero component gradients at the optimizer. It is finite for every fixed finite sum with an attained differentiable minimum, but a usable bound must be supplied. There is no global gradient bound, global Lipschitz-gradient constant, bounded feasible domain, prescribed safe trajectory, strong convexity, or projection onto an optimizer-containing set. The formalization needs continuity of gradients, not existence of component Hessians.

## Algorithm, output, and cost

The [algorithm module](../Algorithms/LocalFiniteSumAcceleration.lean) defines `localAcceleration`, its oracle state machine, and `amplifiedOutput`. Write
\[
 q=L_1R,\quad \bar L=L_0+L_1G,\quad T=\bar LR^2/\epsilon,
 \quad \ell=\log(2+\Delta/\epsilon).
\]
Each independent trial starts from \(x_0\), with \(A_0=R^2/\Delta\). At epoch \(k\), put
\[
 a_k=\min\{A_k/[1024(1+q)],\sqrt{nA_k/(1048576\bar L)}\},\qquad A_{k+1}=A_k+a_k.
\]
Query all component pairs at the snapshot \(s\), store their gradients, and set \(w_i=L_0+L_1\|\nabla f_i(s)\|\). The sampler uses integer counts \(c_i=\lfloor nw_i/\sum_jw_j\rfloor+1\), total \(D=\sum_i c_i\le2n\), and probabilities \(c_i/D\). During each of the \(n\) inner steps, query at
\[
 y=(A_ks+a_kz)/A_{k+1},\quad
 v=\nabla F(s)+\frac{D}{nc_i}(\nabla f_i(y)-\nabla f_i(s)),\quad
 z^+=z-(a_k/n)v.
\]
Average the \(n\) points \((A_ks+a_kz^+)/A_{k+1}\) to form the next snapshot; carry the dual iterate forward. Thus only one new component call is needed per inner step.

Use
\[
 N=\lceil65536(1+q)\ell+65536\sqrt{T/n}\rceil,
 \qquad J=\lceil\log(2\max\{1,\Delta/\epsilon\})/\log4\rceil.
\]
Evaluate \(F(x_0)\), run \(J\) independent trials of \(N\) epochs, and evaluate every final snapshot fully. Return the point with smallest value among these snapshots and \(x_0\), with the earlier point winning ties. When \(\Delta\le\epsilon\), return \(x_0\). The output is either the initial point or a selected trial's last snapshot, itself formed by averaging its final epoch's primal points; it is not the last dual iterate.

The exact useful-call bound is \(n+J(2nN+n)\). An absorbing state makes additional budgeted calls harmless; the framework still counts them. The one-line public Lean budget is
\[
 K=\left\lceil 16777216\left[n(1+q)\ell^2+\sqrt{nT}\,\ell\right]\right\rceil.
\]
The theorem proves measurable output, integrability, and
\[
 \int \bigl[F(\operatorname{output}(\omega))-F(x_*)\bigr]\,dP(\omega)\le\epsilon,
\]
where \(P\) is explicitly the product of the algorithm's finite uniform seed law and the oracle's law. Each trial row has \(Nn\) independent coordinates, each uniform on \(\mathrm{Fin}((2n)!)\); replicated slots implement the stated probabilities exactly. Oracle randomness cannot change exact replies. The factorial seed representation is a formal finite-support implementation, not an efficient random-bit or arithmetic-complexity claim. No finite-space restriction is placed on the objective domain or the oracle's seed spaces.

## Proof mechanism

The new mechanism combines snapshot-measured importance sampling with moving local query balls and a stopped accelerated energy. The individual ingredients—variance reduction, similar-triangles coupling, local shifted descent, and independent amplification—are established tools.

The local lemmas give snapshot-anchored component cocoercivity with constant \(12w_i\), variance at most \(24M\) times the aggregate Bregman divergence, and
\[
 M=n^{-1}\sum_iw_i\le3\bar L+34L_1^2(F(s)-F(x_*)).
\]
The minimizer need not lie in the small local ball where descent is applied. A partial-epoch energy includes accumulated primal objective errors, the unspent snapshot error, and the dual distance. Its epoch-start gap is retained as a separate invariant; it cannot be recovered from a coefficient that vanishes at the epoch end. The chosen increment keeps the query and descent step inside the local ball even on the step that first exits the safe energy region.

Stopping the nonnegative energy at its first threshold crossing bounds the probability of any excursion by \(1/4\), without a union bound over epochs. The epoch average decreases energy at boundaries. Weight growth ensures \(A_N\ge12R^2/\epsilon\), so a safe trial has objective error at most \(\epsilon/2\). Independent trials and selection against \(x_0\) give expected error at most \(\epsilon/2+\Delta4^{-J}\le\epsilon\), including failed trajectories. Probability calculations use an analytic core that does not expose future seeds; a separate execution proof matches it to the state machine and counts all calls.

## Comparison and scope of novelty

The strongest relevant comparisons include older results and reconstructed compositions, not only recent paper statements.

* [Gorbunov et al., ICLR 2025, Theorem 7.2 and Assumption 7.1](https://arxiv.org/html/2409.14989v2) analyze normalized component SGD with a shared minimizer. Their displayed criterion is a minimum over iteration indices of an expected truncated objective error, whereas ours is expected untruncated error of the returned selected point. The theorem here permits noninterpolation and establishes the explicit accelerated cost above, using a different algorithm and paid component value-plus-gradient access; it does not establish the same extension for their SGD update. Section 8 identifies stochastic extensions beyond the shared-minimizer setting as a research question. The numbering here is from arXiv v2; the conference version uses different numbering. Their deterministic aggregate-objective results cannot be substituted directly: cancellation means the average objective need not satisfy their condition in terms of its own gradient norm.
* [Song, Jiang, and Ma, VRADA, NeurIPS 2020](https://proceedings.neurips.cc/paper_files/paper/2020/file/093b60fd0557804c8ba0cbf1453da22f-Paper.pdf) provide the accelerated finite-sum coupling under global smoothness, including the \(\sqrt{nT}\) accuracy term. Our claim is not the invention of that term. Fixed-global-curvature arbitrary-sampling acceleration likewise does not itself certify the moving local trajectory.
* [Vainsencher, Liu, and Zhang, NeurIPS 2015, Theorem 5 and Remark 7](https://proceedings.neurips.cc/paper/2015/file/286674e3082feb7e5afb92777e48821f-Paper.pdf) exploit local smoothness using an optimizer-containing projected region controlled by strong convexity. With accuracy-scale regularization, its radius need not be \(O(1/L_1)\). Applying a single global radius bound in the present model can incur exponential dependence on \(q\). Their excursion issue is addressed here by stopped stochastic accelerated energy, without that projection.
* A standard reduction uses componentwise centered gaps and convex smooth extension on a low sublevel, followed by accelerated variance reduction. For sublevel height \(D\), individual centered component gaps can be \(nD\), giving average extension curvature \(L_{\rm ext}=O(\bar L+nL_1^2D)\). The crude choice \(D=O(nR^2/A)\) gives the startup \(n\sqrt n\,q\), but this is **not the strongest checked reduction**. A sharper self-consistent calculation at snapshot gap \(\delta\asymp R^2/A\) uses \(b=a\sqrt{\bar L/A}\), query gap \(D=O(\delta(1+b^2))\), and \(b^2=O(n\bar L/L_{\rm ext})\). Solving gives
  \(L_{\rm ext}=O(\bar L+nL_1^2\delta+n\sqrt{\bar L L_1^2\delta})\).
  The resulting stronger reconstructed bound is
  \(O([n(1+q)\ell+\sqrt{nT}+n\sqrt q\,T^{1/4}]\ell)\).
  This composition uses [convex smooth extension](https://arxiv.org/abs/1603.00241), accelerated variance reduction, local query estimates, and stopping; it is a reconstructed comparison, not a theorem quoted from either paper and not a lower bound. Our guarantee eliminates its mixed \(n\sqrt q\,T^{1/4}\) term. Simply requiring \(D=O(\delta)\) does not remove that term for free: the finite-sum increment allows \(b^2\) as large as \(n\); forcing it to be constant loses accelerated finite-sum scaling. Snapshot-anchored component weights avoid needing a component extension simultaneously valid on the entire sublevel.
* A full-gradient similar-triangles analysis using the same component-average curvature gives the reconstructed bound \(O(n[(1+q)\ell+\sqrt T])\). Full-gradient warmup followed by constant-curvature variance reduction does not eliminate the relevant gap: balancing its costs gives a term \(n^{5/4}\sqrt q\,T^{1/4}\). These are upper-bound comparisons, not impossibility statements about all warmup strategies.

Extending only a small ball around the snapshot does not directly resolve this comparison: a globally smooth extension on that ball need not preserve the original minimizer or an equally good comparator outside the ball. Adding minimizer interpolation data requires further component Bregman control over distance \(R\). The proof here keeps global convex support for the comparator while using only local descent for actual queries; it never assumes that a small query ball contains the minimizer.

For \(q\ge1\), \(T\asymp nq^2\), and \(\ell=O(\log n)\), the new bound is \(O(nq\log^2n)\), versus \(n^{5/4}q\) up to logarithms for the stronger self-consistent extension comparison (and \(n^{3/2}q\) for full-gradient or the displayed warmup comparison). The conservative improvement factor grows as \(n^{1/4}/\log^2 n\); the displayed universal constant makes this an asymptotic regime claim, not a practical crossover claim. At sufficiently high accuracy the shared \(\sqrt{nT}\) term dominates, and no new accuracy exponent is obtained. For \(n=1\), ordinary globally smooth instances, or other parameter regimes, specialized existing methods can be better. No optimality or universal dominance is claimed.

Additional threats checked include [ARC-SG, arXiv:2609.06555v1, Appendix F](https://arxiv.org/html/2609.06555v1), whose accelerated bound retains a \(\sqrt{1+q}\) multiplier and uses an aggregate-objective condition; [Reusing Samples in Variance Reduction, Section 6](https://arxiv.org/abs/2509.02526), which uses fixed global component smoothness constants; and [ball optimization oracle acceleration, Theorems 6 and 9](https://arxiv.org/abs/2003.08078), whose cheap ball solver needs stronger Hessian stability and linear-system access. None of these supplies the claimed same-oracle result by the checked substitutions. This is evidence from a targeted literature search, not a proof that no undiscovered prior theorem exists.

## Nonlinear instances and limitations

A standard example is noninterpolating Poisson loss
\(f_i(x)=\exp(a_i^Tx)-b_i a_i^Tx\), with dense, nonorthogonal spanning features, \(\|a_i\|\le B\), and \(b_i\in[1,2]\). Inconsistent equations \(a_i^Tx=\log b_i\) rule out a common minimizer. The data imply \(L_0=2B^2\), \(L_1=B\), \(G=6B\), and, at \(x_0=0\), \(\Delta=1\). One coarse computable radius is \(R=3n/\sigma_{\min}(A)\), for the matrix with rows \(a_i^T\). Fenchel's inequality bounds the average exponential at the optimum, yielding the stated \(G\); coercivity of the spanning losses gives the radius. Choosing \(\epsilon=8/n\) gives \(T=nq^2\). This demonstrates a natural interacting family in the comparison regime, not a matching hard instance. Dimension enters through feature geometry and the supplied radius, not an additional explicit factor in the oracle budget. Richer generalized-linear-model oracles may enable other algorithms.

Known radius, initial gap, and optimum heterogeneity bounds are genuine requirements; the algorithm is not adaptive to them. Removing exactness, obtaining a gradient-only selection rule, reducing amplification logarithms, efficient random-bit implementation, and closing lower-bound gaps remain unresolved here. The literature survey covered the publicly available 2025/2026 ICML, ICLR, and NeurIPS materials and roughly two years of arXiv work as of 26 October 2026, with older foundational follow-ups. Public 2026 submissions or preprints were not treated as accepted papers merely because they were available. The principal generalized-smooth baseline was checked at arXiv:2409.14989v2 (25 December 2024), and VRADA at arXiv:2006.10281v4 (7 March 2021); these were the latest versions found in the survey. Search coverage was targeted rather than exhaustive.
