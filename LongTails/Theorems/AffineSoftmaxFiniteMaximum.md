# Centered affine softmax estimates for smooth finite maxima

The [main theorem](AffineSoftmaxFiniteMaximum.lean) gives a randomized first-order oracle bound for minimizing the maximum of finitely many smooth convex functions. The contribution is an improved oracle-complexity bound in an intermediate range of component counts, under standard assumptions. It is not a new problem definition, an optimality claim, or a runtime improvement.

## Problem, information, and output

The [setup](../Setups/SmoothFiniteMaximum.lean) specifies

\[
 \min_{x\in X} f_{\max}(x),\qquad f_{\max}(x)=\max_{i\le m}f_i(x),\qquad X=\overline B(x_0,R).
\]

The space is an arbitrary finite-dimensional real inner-product space. There are at least two components; each is convex on the ball, differentiable at every point of the ball, has gradient norm at most \(G>0\), and has \(L\)-Lipschitz gradient there, with \(L\ge0\). The radius and accuracy are positive, and the public failure probability satisfies \(0<\delta<1\). A minimizer exists on the ball and is represented by the hidden `xstar`. No Hessian, strong convexity, component similarity, near-active-set, or separation assumption is imposed. No regularity outside the ball is used. This is a standard smooth finite-maximum ball model. The precise scopes of the compared results differ: COLT 2021 introduces globally convex, Lipschitz losses and a nearby global minimizer, whereas this setup requires the component assumptions only on the public ball and compares with its constrained minimizer. The comparison applies in the common global subclass as well; the globally Lipschitz Huber examples below show that the improvement is not obtained merely by changing local versus global assumptions.

One oracle call specifies an index and a feasible point and returns that component's exact value and gradient. The oracle may depend on history and have arbitrary internal randomness, but must give that exact pair on every feasible query and every history. The algorithm knows only the public space, ball, component count, bounds, target accuracy, and failure probability. Neither losses nor a minimizer are algorithm inputs. The setup permits unrestricted algorithms with this access.

The [algorithm and named output](../Algorithms/AffineSoftmaxFiniteMaximum.lean) use the repository's `execute`. The result is measurable, feasible almost surely, and satisfies

\[
 \Pr\{f_{\max}(\mathrm{output})-f_{\max}(x_\star)\le\varepsilon\}\ge1-\delta
\]

over the explicitly specified independent algorithm and oracle laws. The returned point is the least original maximum among \(n=1+\lceil\log_2\lceil1/\delta\rceil\rceil\) independent guarded runs; evaluating their exact scores costs \(nm\) calls. If \(\varepsilon\ge2GR\), the planner returns \(x_0\). Execution padding at \(x_0\) is included in the stated budget.

## Proved budget

Write \(a=GR/\varepsilon\), \(b=LR^2/\varepsilon\), and

\[
 h=1+\left\lceil\log_2\left\lceil2+m+a+b\right\rceil\right\rceil,
 \quad S=m+mb^{1/3}+m^{3/4}\sqrt b+m^{6/7}(ab)^{2/7}+a.
\]

Here the logarithmic ceiling is exactly `Nat.clog 2`. Let \(n=1+\lceil\log_2\lceil1/\delta\rceil\rceil\). The public budget, written as one explicit formula in the Lean theorem, is

\[
 \boxed{n\left\lceil 2\cdot10^{21}h^7 S\right\rceil.}
\]

Thus the dimension-free oracle rate is \(O(h^7S\log(2/\delta))\), with the dependence on confidence displayed explicitly. For fixed confidence it is \(\widetilde O(S)\). The large constant and seventh logarithmic power are conservative proof bounds. This does not establish practical speedups. All cache construction, stochastic numerator and reciprocal samples, inner solves, search validation, final scoring, and padding calls are counted. There is no uncharged exact proximal oracle. The [public-budget](../Proofs/AffineSoftmaxPublicBudget.lean) and [final-assembly](../Proofs/AffineSoftmaxFiniteMaximum.lean) proofs bound actual execution, rather than just an iteration count or an expectation conditional on success.

## Mechanism and proof

Smooth the maximum with temperature \(\tau=\varepsilon/(2\log m)\). At a center \(z\), cache all \(f_i(z),a_i=\nabla f_i(z)\), costing \(m\) calls. For a current nearby point \(x\), let

\[
 \ell_i=f_i(z)+\langle a_i,x-z\rangle,\quad
 q_i=\frac{e^{\ell_i/\tau}}{\sum_j e^{\ell_j/\tau}},\quad
 b_x=\sum_iq_i a_i,\quad w_i=e^{(f_i(x)-\ell_i)/\tau}.
\]

Convexity and smoothness imply \(1\le w_i\le2\) when \(Lr^2\le\tau\) and \(\|x-z\|\le r\). For an independent index \(I\sim q\), use the centered numerator

\[
 N_I=w_I(\nabla f_I(x)-a_I)+(w_I-1)(a_I-b_x).
\]

Independently sample \(K\ge0\) with \(\Pr(K=k)=2^{-k-1}\) and \(J_1,\ldots,J_K\sim q\). Set \(T=\prod_{j=1}^K(2-w_{J_j})\), with empty product one. Then \(0\le T\le1\), \(\mathbb ET=1/\mathbb E_qw\), and \(H=b_x+TN_I\) is an unbiased gradient of the actual smoothed objective. It costs two fresh joint oracle calls in expectation. The [moment proofs](../Proofs/AffineSoftmaxMoments.lean) establish

\[
 \mathbb E\|H-\nabla F_\tau(x)\|^2
 \le V:=8\left(L^2r^2+\frac{G^2L^2r^4}{\tau^2}\right).
\]

For this estimator the second term is necessary in general; an \(O(L^2r^2)\)-only claim is false. Moving Gibbs probabilities prevent simply importing an old-anchor variance estimate. The independent reciprocal and centered score preserve unbiasedness while controlling this change of weights.

Constrained stochastic acceleration and restarts solve regularized local problems. Finite multilevel estimates supply approximate proximal gradients. A validated regularization search and an accelerated outer potential give, up to logarithms, the reference expected call count

\[
 m(D/r)^{2/3}+D\sqrt{(L+2G^2/\tau)/\eta}+VD^2/\eta^2,
 \qquad D=2R,\quad\eta=\varepsilon/2.
\]

The public radius is \(r=2R/z\), where

\[
 z=\max\left\{1,\sqrt{8b\log m},
 (64b^2/m)^{3/8},
 (1024a^2b^2(\log m)^2/m)^{3/14}\right\}.
\]

Balancing these terms gives \(S\), retaining both the radius restriction and quadratic-variance term. The formulas handle \(L=0\) without division by \(L\).

All adaptive integration is under the original seed law. An analysis-only repaired process handles bad searches; the proof never conditions stochastic unbiasedness on future search success. Each run checks a seed-only upper bound on its entire oracle cost and returns a feasible fallback if the cap would be exceeded. This bound includes bad-search paths. Markov's inequality and coupling give failure at most \(23/60<1/2\) for each guarded run. Independence and exact minimum selection give failure at most \(2^{-n}\le\delta\). The integer logarithm and both ceilings are handled explicitly in Lean. The conservative constant covers all ceiling and scoring terms. The score cost \(nm\) is included in actual execution. [Query safety](../Proofs/AffineSoftmaxQuerySafety.lean), [execution refinement](../Proofs/AffineSoftmaxCompilerExecution.lean), and [final assembly](../Proofs/AffineSoftmaxFiniteMaximum.lean) connect these mathematical processes to history-dependent oracle execution. The analysis-only measurable oracle extension and exact proximal points are not supplied to the algorithm.

## Prior work and precise improvement

The individual ingredients are not all new. [Carmon et al., COLT 2021](https://proceedings.mlr.press/v134/carmon21a/carmon21a.pdf), arXiv:2105.01778v1, Theorem 6, gives a smooth finite-maximum oracle bound through ball optimization; Theorem 10 supplies the relevant lower obstruction. [Carmon et al., SODA 2024](https://arxiv.org/abs/2311.10886), arXiv:2311.10886v1, Sections 2 and 7 and Theorem 8.1, already use affine caches and moving Gibbs sampling on larger balls and identify larger-ball variance reduction as a remaining direction. Its theorem concerns expected error and a high-probability runtime threshold. The present result changes the local estimator and the resulting global query bound; it does not claim to introduce affine Gibbs sampling or ball acceleration.

The reciprocal product is a specialization of [Moka, Kroese, and Juneja, WSC 2019, equation (1)](https://www.informs-sim.org/wsc19papers/035.pdf), arXiv:1907.01843, which also credits earlier work. Stochastic acceleration, strong-convexity restarts, finite multilevel estimation with controlled bias, and confidence amplification are established tools. The local-to-global proximal-gradient and multilevel framework follows [Carmon and Hausler, NeurIPS 2022, Proposition 1 and Appendix B](https://arxiv.org/abs/2203.13225). Their complete proofs here support the new global result; their formalization alone is not the contribution.

For a transparent comparable regime, fix \(G=L=R=1\) and any constant \(\delta\in(0,1)\), let \(\varepsilon\to0\), and ignore polylogarithmic factors only. The strongest inspected envelope includes full-batch accelerated linearization, the COLT bound, and the SODA bound:

| Bound | Joint component-query order |
|---|---|
| Accelerated linearization | \(m\varepsilon^{-1/2}\) |
| COLT 2021, Theorem 6 | \(m\varepsilon^{-2/3}+\sqrt m\varepsilon^{-1}\) |
| SODA 2024, Theorem 8.1, query component | \(m\varepsilon^{-1/3}+\varepsilon^{-2}\) |
| This theorem | \(m+m\varepsilon^{-1/3}+m^{3/4}\varepsilon^{-1/2}+m^{6/7}\varepsilon^{-4/7}+\varepsilon^{-1}\) |

The accelerated-linearization row is given in COLT 2021 Section 1.1, Table 1, and Appendix A.3, citing Nesterov (2018), Section 2.3.1; SODA 2024 Table 1 repeats it as “AGD on linearization.” Ordinary softmax AGD is not the strongest full-batch comparator. Arithmetic for the linearized subproblem is not counted as component-oracle access. The related heterogeneous-composition analysis of [Zoll and Grimmer](https://doi.org/10.1093/imanum/drag062), arXiv:2503.07566v3, Section 3.4, Theorem 3.4 and Corollaries 3.5–3.6, was also inspected. Its perturbed-composition optimality criterion in equation (1.8) differs from direct maximum-objective error; those corollaries are not being substituted as the proof of the table row.

Set \(m=\varepsilon^{-\alpha}\), \(\alpha\ge0\). The new exponent is
\(\max\{1,\alpha+1/3,(6\alpha+4)/7\}\).
The inspected baseline exponent is
\(\min\{\alpha+1/2,\max(\alpha+2/3,\alpha/2+1),\max(\alpha+1/3,2)\}\).
The improvement is strict for **\(1/2<\alpha<5/3\)**. At \(\alpha=1\), the exponent decreases from \(3/2\) to \(10/7\), while the lower benchmark is \(4/3\). At \(\alpha=3/2\), it decreases from \(2\) to \(13/7\), leaving a gap of \(1/42\) above \(11/6\). There is no claim of universal superiority, optimality, or optimal dependence on \(\delta\). The full formula retains all parameter terms outside this normalized comparison.

Probability criteria require alignment. COLT already provides constant-probability accuracy. SODA's expected-error and high-probability runtime guarantee can be converted to constant success with a cutoff and constant repetition. Conversely, applying the present theorem at accuracy \(\varepsilon/2\) with failure probability \(\min\{1/2,\varepsilon/(4GR)\}\), and using the bounded feasible gap \(\le2GR\), gives expected error at most \(\varepsilon\). The resulting confidence cost is logarithmic, and selection calls are already included in the theorem’s budget. This expected-error implication and the baseline conversions are comparison reductions, not additional formal claims of the sole main theorem. Appending one output query aligns returned-point accuracy with the COLT query-point lower bound.

Batching does not remove the centered estimator's radius-dependent total variance cost: dividing variance by batch size multiplies the cost per estimate. Direct substitution into the known local-to-global cost expression gives the displayed pre-radius formula; it does not yield the new rate without the improved \(V\). Capping the reciprocal itself would bias it, so the proof instead guards whole runs and accounts for abort probability. No algorithm family was restricted to obtain the improvement. Arbitrary-confidence amplification is standard; the new optimization contribution remains the centered-estimator global oracle rate, not the confidence wrapper.

## Scope, examples, and limitations

A nonlinear family in arbitrary dimension is the maximum over groups of weighted Huber regression losses,
\(f_i(x)=\sum_j c_{ij}h_\kappa(u_{ij}^{\mathsf T}x-v_{ij})\), with nonnegative weights. Valid public bounds are any positive \(G\ge\max_i\kappa\sum_jc_{ij}\|u_{ij}\|\) and
\(L\ge\max_i\sum_jc_{ij}\|u_{ij}\|^2\).
Dense nonorthogonal features give interacting coordinates. Threshold crossings inside the ball produce Hessian jumps, so the setup covers functions without Lipschitz Hessians. This illustrates the class, not an extra assumption or an empirical claim. Expensive aggregate black-box evaluations motivate the query model; access to individual data samples or an explicit recoverable model changes the comparison.

Cached mixtures may require \(O(md)\) arithmetic per point with a conventional implementation. The categorical sampler is a measurable representative chosen independently of the hidden instance; executable sampling runtime is not verified. Projection and other internal arithmetic are outside the oracle count. In the affine case \(L=0\), all components can be recovered with \(m\) queries; this uniform algorithm is deliberately not the best algorithm for that special case.

Recent alternatives were checked rather than inferred absent. [Gladin et al., ICML 2026](https://proceedings.mlr.press/v306/gladin26a.html), arXiv:2509.24894v4 (18 June 2026), Assumption 2.8 and Theorem 2.9, optimize a SoftPlus surrogate with a concentration parameter and an objective bracket. For uniform components that concentration can grow with \(m\). Corollary 2.5's unnormalized sum becomes a normalized surrogate with parameter divided by \(m\); it does not provide a free dimension-independent stochastic reduction. [Gladin, Popova, and Babinskii](https://arxiv.org/html/2609.32872v1), 26 September 2026 preprint, Theorem 2, exploit a near-active top-\(k\) condition absent here and retain an \(\varepsilon^{-2}\) gradient count. Neither theorem directly implies the displayed intermediate-\(m\) rate.

The survey covered the publicly available 2025 and 2026 ICML, ICLR, and NeurIPS editions and approximately two years of arXiv submissions and revisions, following older primary results and later citations, through 6 November 2026. Stronger sample-reuse oracles revealing entire functions, second-order oracles, finite-sum means, and Lipschitz-Hessian assumptions were kept distinct from this point-query finite maximum. In particular, arXiv:2610.42040v1 is a second-order finite-sum result, not this baseline. An unidentified OpenReview source `ddRfkfiMsf` remained inaccessible despite forum, PDF, API, and exact-ID search attempts; it was not inspected or excluded. The novelty claim is supported by the inspected primary comparisons and reductions, not an assertion that every potentially relevant source was accessible.
