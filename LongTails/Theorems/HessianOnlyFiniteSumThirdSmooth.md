# Finite-sum third-order smoothness with a second-order oracle

The [Lean theorem](HessianOnlyFiniteSumThirdSmooth.lean) proves a dimension-free component-oracle bound for minimizing an individually convex finite sum with Lipschitz third derivatives. The algorithm queries only component gradients and Hessians. Its contribution is an explicit implementation and proof of a bound uniform in the number of components, including all model-solver queries and a fixed logarithmic exponent. The exponent suggested by earlier multi-function hyperfast sliding is not itself claimed as a new discovery.

## Problem and guarantee

The [setup](../Setups/FiniteSumThirdSmoothConvex.lean) considers
\[
f(x)=\frac1n\sum_{i=1}^n f_i(x)
\]
on any finite-dimensional real Hilbert space. Each component is convex and three times continuously differentiable, and
\[
\|D^3f_i(x)-D^3f_i(y)\|\le L\|x-y\|.
\]
The mean has a minimizer \(x_\star\), and \(\|x_0-x_\star\|\le R\), with \(R>0\). The target is \(\varepsilon>0\). Public nonnegative bounds \(G,H\) satisfy
\(\|\nabla f(x_0)\|\le G\) and \(\|\nabla^2f(x_0)\|\le H\).
The algorithm knows these bounds, \(n,L,R,\varepsilon,x_0\), and the space; it does not know the minimizer or minimum value. There is no strong convexity, global gradient or Hessian bound, bounded component variance, or global Hessian-Lipschitz assumption.

A query chooses an index and point and returns the exact pair
\((\nabla f_i(x),\nabla^2 f_i(x))\). One such pair costs one call, including queries made solely to obtain a gradient. No function-value, third-derivative, or component-proximal oracle is supplied. Oracle answers are exact for every history and oracle seed. Randomness is internal to the algorithm, on an explicitly defined finite uniform seed space; the theorem's success probability includes the oracle's arbitrary probability law as well.

Put
\[
U=LR^4/\varepsilon,\qquad
Q=2+n+GR/\varepsilon+HR^2/\varepsilon+U,
\qquad \ell=1+\lceil\log Q\rceil.
\]
The public budget is
\[
B=2^{38}\bigl(n+\lceil(n^4U)^{1/5}\rceil\bigr)\ell^2.
\]
The theorem constructs the [public algorithm](../Algorithms/HessianOnlyFiniteSumThirdSmooth.lean), runs it through `execute`, and proves
\[
\Pr\{f(\mathrm{output})-f(x_\star)\le\varepsilon\}\ge 2/3
\]
within \(B\) component calls. Thus the bound is
\(O((n+n^{4/5}U^{1/5})\log^2 Q)\), with a universal constant and no dimension factor. The additive \(n\) term remains when \(L=0\). This is a constant-success-probability objective guarantee, not an expected-gap or almost-sure statement.

## Algorithm and proof mechanism

The algorithm uses quartic regularization with
\(M=L+\varepsilon/R^4\), \(\gamma=M/n\), and
\(N=\lceil64(1+((U+1)/n)^{1/5})\rceil\) outer trials. Its outer step is a known adaptive Monteiro–Svaiter acceleration mechanism. Each trial approximately solves
\(f(x)+\gamma\|x-c\|^4/4\). The [trial](../Algorithms/QuarticProximalTrial.lean) combines tensor-free model solves with variance-reduced stages. It maintains exact full-gradient and full-Hessian snapshots and samples component Taylor remainders. The cache contains only quadratic models, so every cached operation is available from the stated oracle.

The key [self-bound](../Proofs/ThirdSmoothJensen.lean) is
\[
\|\nabla f_i(w+s)-\nabla f_i(w)-\nabla^2f_i(w)s\|^2
\le 2L\|s\|^2 D_{f_i}(w+s,w).
\]
It follows by viewing the convex Jensen gap as a nonnegative function of its base point. Third-order smoothness bounds its Hessian; smooth nonnegative-function self-bounding and a limiting argument give the displayed estimate. In contrast to a generic Taylor norm bound, it controls the variance by a component Bregman divergence and is insensitive to an arbitrarily large convex quadratic part. This permits a quadratic cache to exploit third-order smoothness without querying third derivatives.

The [stage proof](../Proofs/QuarticFiniteSumStage.lean) uses this estimate inside a localized, regularized variance-reduction argument. Projected updates bound every trajectory, including failed ones. Restarted stages shrink the gap geometrically, with their error probabilities charged before passing to adaptive outer trials. Finite differences of gradients implement the remaining cubic-model contractions in the [tensor-free solver](../Algorithms/TensorFreeModel.lean); the [termination proof](../Proofs/TensorFreeModelTuning.lean) derives its stopping budget from the public data and proved local derivative bounds. Third-order tensors occur in analysis, not in oracle replies or hidden free subproblem access.

The [outer execution](../Algorithms/AcceleratedQuarticNewton.lean) returns an accelerated primal point, or an earlier point certified accurate by the trial. It need not be the last queried point or a uniform average of outer iterates. The quartic coefficient \(\gamma\) is strictly positive. A zero effective Monteiro–Svaiter parameter \(\lambda=\gamma\|y-c\|^2\) is handled explicitly by an exact stationary-point branch. The [rate proof](../Proofs/QuarticAccelerationRate.lean) derives the fifth-power growth bound from actual accepted trial certificates and the adaptive parameter sequence. These acceleration and finite-difference ideas are established tools; they are not claimed as separate new results.

Every full snapshot, finite-difference probe, gradient check, restart, and padded terminated round is counted. A trial costs at most \(2^{29}n\ell^2\), and the [budget algebra](../Proofs/HessianOnlyFiniteSumTuning.lean) proves that the public formula covers all \(N\) trials. The [integration proof](../Proofs/HessianOnlyFiniteSumConvergence.lean) derives the trial hypotheses from the setup rather than assuming a convergence contract. The finite adaptive failure calculation bounds total bad probability by \(1/4\); the public statement uses the weaker success threshold \(2/3\).

## Closest results and the contribution boundary

**Hyperfast methods and sliding.** [Kamzolov and Gasnikov, arXiv:2002.09050v3, 28 June 2020](https://arxiv.org/abs/2002.09050v3), Theorem 2, establishes a Hessian-only full-objective method under third-order smoothness with \(\widetilde O(U^{1/5})\) calls. Full-batch implementation therefore costs \(\widetilde O(nU^{1/5})\) component calls. Theorem 3 and equations (14)–(15) separate two summands' costs. The sentence immediately following that theorem explicitly suggests extending the method to many functions. Formally substituting component constants \(L/n\) into a uniform multi-function separation formula would suggest exactly \(n^{4/5}U^{1/5}\). That suggestion is relevant prior art and prevents claiming that this exponent was previously unanticipated.

The checked two-term construction does not itself provide the present bound uniformly in variable \(n\). [Kamzolov, Gasnikov and Dvurechensky, WIAS preprint 2710, 2 April 2020](https://www.wias-berlin.de/preprint/2710/wias_preprints_2710.pdf), Theorem 5 and equations (11)–(13), gives the two-term composition analysis; the earlier [arXiv version](https://arxiv.org/abs/2002.01004v1) presents the inner cost in equation (13). Splitting off one component leaves a composite oracle costing \(n-1\) calls, so the literal two-term application retains \(\widetilde O(nU^{1/5})\). Recursively applying the theorem multiplies inner restart constants and logarithms with depth. Those cannot be hidden in constants independent of \(n\).

There is a further oracle-accounting issue even if inherited quartic regularization improves the recursive conditioning. Previously formed cubic Taylor models require contractions of their third derivatives in new directions. Under a gradient/Hessian oracle, these contractions require fresh component-gradient probes unless full third-order tensors were reconstructed at dimension-dependent cost. Treating an arbitrarily large collection of those models as free known polynomials changes the cost model. The present quadratic-cache argument avoids both an increasing stack of cubic models and a logarithmic exponent depending on the component count. These observations identify the gap in the checked standard composition; they are not a lower bound against every possible sliding implementation. No claim is made that the earlier two-function theorem is false. The novelty claim is the proved, dimension-free implementation with all component calls and a fixed \(\log^2 Q\) factor, rather than the bare exponent or a formalization of that earlier claim.

**Individual Hessian smoothness.** [Zhang, Chen, Li and Zhang, arXiv:2610.42040v1, 30 October 2026](https://arxiv.org/abs/2610.42040v1), Lemma 5.1 and Theorem 5.1, proves a second-order self-bound and an accelerated Taylor-corrected lazy Newton guarantee of \(\widetilde O(n+n^{5/7}V^{2/7})\), where \(V=L_2R^3/\varepsilon\), under individual convexity and globally \(L_2\)-Lipschitz Hessians. That theorem returns an accurate point almost surely and bounds expected query cost; our theorem instead fixes the query budget and guarantees constant success probability. Truncating the former at a constant multiple of its expected cost gives a comparable constant-success guarantee, so the polynomial comparison does not rely on confusing these criteria. This is a preprint, not an accepted-conference claim. Its chosen-index second-order oracle matches ours; restrictions used for its lower bound are not restrictions of our problem. The present proof builds on its Jensen-gap and variance-reduction approach. The new estimate uses third-order smoothness to replace the distance factor by its square while retaining a quadratic cache. The resulting quartic subproblem analysis and charged tensor-free implementation are the substantive extension.

The two smoothness classes are not nested without extra assumptions. On their intersection, ignoring logarithms and assuming the iterative terms dominate, our bound is smaller when
\(U^7<n^{-3}V^{10}\). It is not uniformly superior: it requires third-order smoothness and may lose when \(U\) is large relative to \(V\). Full-batch hyperfast complexity improves by a factor \(n^{1/5}\) in the iterative term, again subject to logarithms and the additive floor. No unrestricted optimality or matching lower bound is proved here.

**Other reductions.** Localizing a Hessian-Lipschitz analysis using third-order smoothness retains dependence on initial curvature; it does not directly yield this quadratic-insensitive polynomial rate. Subtracting a cached quadratic can destroy component convexity, so the individual-convexity theorem cannot simply be reapplied to the residuals. Stochastic tensor methods with actual third-derivative access, such as [Agafonov et al., arXiv:2012.15636v4](https://arxiv.org/abs/2012.15636v4), Theorem 3 and its sampling corollaries, have different oracle and batch costs. [Lupu and Necoara, arXiv:2103.07984v3](https://arxiv.org/abs/2103.07984v3), Theorem 5.5, gives a higher-order surrogate recursion whose degree-four specialization contains \(L_h/(6\sigma_4)\); with \(\sigma_4\) of order \(L/n\), it does not give the needed linear contraction. Its exact surrogate minimization also needs an implementation under the present oracle. These results are not free substitutes for the charged quartic solver.

The outer acceleration follows established work, including [Carmon et al., NeurIPS 2022](https://arxiv.org/abs/2205.15371v2). The formalization and explicit universal constants support correctness; neither is used as a substitute for mathematical significance.

## Motivation, assumptions, and examples

Individual convexity and derivative Lipschitz conditions are standard finite-sum and tensor-optimization assumptions in the cited results. Their combination describes smooth convex empirical objectives, rather than restricting an algorithm to manufacture novelty. Third-order smoothness is stronger regularity than the Hessian-smooth baseline on the overlap, and is stated explicitly. Finite-dimensionality, an attained minimizer, and a distance bound are the standard global convex oracle-complexity setting. The initial \(G,H\) bounds supply finite-difference tolerances and enter only logarithms; they are information supplied to the algorithm, not unknown constants suppressed from the statement. They impose no global curvature bound. Their removal from the public tuning is not proved here.

A nonlinear family is a sum of quartic ridge losses \((a_i^Tx-b_i)^4\) and positive-semidefinite quadratic terms. Nonorthogonal rows give interacting coordinates in arbitrary dimension. Each component has globally Lipschitz third derivative, while its Hessian need not be globally Lipschitz. Consequently this family is not covered merely by asserting a global \(L_2\) for the Hessian-smooth baseline.

For an overlap example, take unit rows and
\[
f_i(x)=\phi(a_i^Tx),\qquad
\phi(t)=t^2/2-t\arctan t+\tfrac12\log(1+t^2).
\]
Here \(\phi''(t)=t^2/(1+t^2)\), so the losses are convex and have bounded third and fourth derivatives, but no positive global strong-convexity modulus. A fixed positive fraction of rows can equal one unit direction, with the remaining nonorthogonal rows spanning the space. The constants \(L_2,L\) then stay of constant order as \(n\) grows, with interacting coordinates and arbitrary dimension up to the available number of rows. Choose \(x_0\) at unit distance from the minimizer zero and \(\varepsilon=n^{-2}\); then \(G,H=O(1)\). The compared class bounds are \(O(n^{6/5}\log^2 n)\) here, \(\widetilde O(n^{9/7})\) for the individual Hessian-smooth result, and \(\widetilde O(n^{7/5})\) for full-batch hyperfast optimization. This illustrates a parameter regime, not hardness of that particular family.

The result addresses both requested orders: the objective assumption concerns third derivatives and the accelerated rate exploits it, while the algorithm uses a second-order oracle only. It is not a scalar, quadratic, separable, or fixed-dimension theorem. There is no artificial `allowedAlgorithm` restriction.

## Limitations and literature coverage

The guarantee concerns exact real-valued component oracles and oracle-call complexity. It does not bound arithmetic work, memory, conditioning of numerical subproblem solvers, or floating-point robustness. The conservative constant \(2^{38}\) and internal tolerances are proof choices, not practical performance recommendations. The finite randomness is an algorithmic construction, not a restriction to a finite-dimensional stochastic data distribution. The objective itself is a finite sum.

The literature check used the UTC date 4 November 2026, surveyed the publicly available 2025 and 2026 ICML, ICLR and NeurIPS editions and approximately two years of arXiv work, and followed relevant references to older primary sources. Conference status was checked separately from preprint status. The strongest comparisons above use the stated versions, including the late-October finite-sum preprint and the older sliding claim. This is a targeted research survey, not a proof of exhaustive coverage. The unresolved possibility of a sharper multi-function sliding analysis is not excluded by a lower bound; the comparison identifies why the inspected published reductions do not establish the explicit theorem proved here.
