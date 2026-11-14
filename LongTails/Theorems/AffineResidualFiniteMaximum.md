# Residual saddle solves for smooth finite maxima

The [main theorem](AffineResidualFiniteMaximum.lean) proves an improved component-oracle bound for smooth convex finite-maximum optimization. It reuses the existing [SmoothFiniteMaximum specification](../Setups/SmoothFiniteMaximum.lean) exactly. The proposed contribution is the global oracle rate obtained from a local residual saddle solver; neither a new problem definition nor the formalization of established acceleration machinery is the novelty claim.

## Problem and guarantee

Let \(X=\overline B(x_0,R)\) in an arbitrary finite-dimensional real inner-product space, and minimize \(f_{\max}(x)=\max_{i\le m}f_i(x)\) on \(X\). There are \(m\ge2\) components, convex on \(X\), differentiable at every point of \(X\), with \(\|\nabla f_i(x)\|\le G\) and \(L\)-Lipschitz gradients on \(X\). The parameters satisfy \(G,R,\varepsilon>0\), \(L\ge0\), and \(0<\delta<1\). No Hessian, component similarity, strong convexity, active-set concentration, or dimension restriction is added. The component assumptions need hold only on the ball. The comparator is its constrained minimizer \(x_\star\).

A query specifies an index and a feasible point and returns that component's exact value and gradient. This is one joint component call. Even history-dependent randomized oracles are allowed, provided their replies equal that pair on every feasible query and every history. The algorithm receives only public parameters, not component formulas, the minimizer, or an exact optimization oracle. The setup imposes no algorithm-family restriction.

The [algorithm and named output](../Algorithms/AffineResidualFiniteMaximum.lean) use `execute`. The [execution proof](../Proofs/AffineResidualFiniteMaximum.lean) establishes measurable output, feasibility, and

\[
 \Pr\{f_{\max}(\mathrm{output})-f_{\max}(x_\star)\le\varepsilon\}\ge1-\delta
\]

under the explicit product of the algorithm's seed law and the oracle's law. The returned point has the smallest exact original maximum among independent budgeted runs. If \(\varepsilon\ge2GR\), the planner returns \(x_0\).

Write \(a=GR/\varepsilon\), \(b=LR^2/\varepsilon\),

\[
 h=1+\left\lceil\log_2\left\lceil2+m+a+b\right\rceil\right\rceil,
 \qquad n=1+\left\lceil\log_2\left\lceil1/\delta\right\rceil\right\rceil,
 \qquad S=m+mb^{2/5}+m^{3/4}\sqrt b+b^{2/3}.
\]

The logarithmic ceiling denotes Lean's `Nat.clog 2`. The public budget is exactly

\[
 \boxed{n\left\lceil10^{22}h^8 S\right\rceil.}
\]

Thus the oracle rate is \(\widetilde O(m+mb^{2/5}+m^{3/4}\sqrt b+b^{2/3})\), with confidence cost \(O(\log(2/\delta))\) displayed separately. The conservative constant and eighth logarithmic power preclude a practical-speedup claim. The [budget proof](../Proofs/AffineResidualPublicBudget.lean) includes caches, local samples, search scoring, all multilevel samples, independent repetition, final scoring, rounding, and execution padding.

## Local mechanism

Use temperature \(\tau=\varepsilon/(2\log m)\). At an anchor \(z\), cache all component values and gradients, costing \(m\) calls. On \(C=X\cap\overline B(z,r)\), set

\[
 \ell_i(x)=f_i(z)+\langle\nabla f_i(z),x-z\rangle,
 \quad d_i(x)=f_i(x)-\ell_i(x),\quad D_r=Lr^2/2.
\]

Convexity and smoothness give \(0\le d_i\le D_r\) and \(\|\nabla d_i\|\le Lr\). The regularized smoothed objective is represented by the saddle function

\[
 \Phi(x,p)=\sum_i p_i f_i(x)+\frac\mu2\|x-z\|^2-\tau\sum_i p_i\log p_i,
 \qquad p\in\Delta_m.
\]

The cached affine coupling is handled implicitly. Only its nonlinear residual is sampled: independently draw \(I\sim p\) and uniform \(J\), and use primal estimate \(\nabla d_I(x)\) and dual estimate \(m(D_r-d_J(x))e_J\). These require two fresh component calls. The shift \(D_r\mathbf1\) leaves simplex pairings unchanged and makes the sampled dual perturbation nonnegative. Its entropy conjugate remainder admits a global quadratic bound. In particular, this solver does **not** require \(Lr^2\le\tau\).

A bound for each fixed comparator would not suffice: the dual best response to the returned random point depends on future samples. The proof uses a predictable auxiliary FTRL sequence and a uniform, weighted regret inequality before selecting that comparator. With

\[
 \beta=1+\lceil16mD_r/\tau\rceil,
 \quad\Delta_0=2\mu r^2+\tau\log m,
 \quad V=(Lr)^2/\mu+mD_r^2/\tau,
\]

the weighted local output after \(N\) steps satisfies expected regularized objective gap at most

\[
 3\beta^2\Delta_0/N^2+32V/N.
\]

The [weighted proof](../Proofs/AffineResidualWeighted.lean), [actual moment calculations](../Proofs/AffineResidualMoments.lean), and [local guarantee](../Proofs/AffineResidualLocal.lean) derive this bound from the algorithm. The horizon is \(\lceil4\beta\sqrt{\Delta_0/\alpha}+64V/\alpha+1\rceil\) for requested local accuracy \(\alpha\). The initialization term is retained; replacing its quadratic decay by a linear transient loses the claimed global rate.

The implicit cached saddle solve and constrained minimizations are internal computation using cached affine data, entropy, and a known ball. They do not evaluate hidden losses. This is an oracle-complexity result, not a bound on their arithmetic or executable runtime. Generic FTRL, entropy stability, and implicit treatment of a known affine operator are established tools. The substantive mechanism is their combination with residual sampling and the uniform future-comparator bound, with its retained initialization cost, to improve this problem's oracle complexity.

## From local solves to the public budget

Multilevel estimates, validated regularization search, and outer acceleration turn the local solver into a global method. With \(D=2R\), inner accuracy \(\eta=\varepsilon/2\), \(b_0=LD^2/\eta=8b\), and \(r=D/z\), the full pre-balance cost, apart from logarithms, retains

\[
 mz^{2/3}+z+mb_0/z+b_0^2/z^2+mb_0^2/z^{8/3}.
\]

The radius uses

\[
 B=\max\{1,b_0\},\qquad
 z=\min\{B^{2/3},\max\{B^{3/5},(B^2/m)^{3/8}\}\}.
\]

The cap controls the initialization term \(z\) without silently dropping it. [Radius algebra](../Proofs/AffineResidualRadius.lean) bounds all five terms by a constant times \(S\), including \(L=0\) and \(b<1\). The bound on \(G\) remains in logarithms and search parameters; it has not been removed from the setup.

All stochastic inequalities are integrated under the original law. An analysis-only repaired search process supports coupling and is not available to the algorithm. Each run checks a measurable, seed-only upper bound on its complete cost before making queries, returning the feasible initial point when its cap is exceeded. The [cutoff proof](../Proofs/AffineResidualBudgetGuarantee.lean) gives deterministic cost at most \(K=\lceil12B_{\rm mean}\rceil\) and failure at most \(13/60+1/12=3/10\). Independent trials and exact score selection give failure at most \(2^{-n}\). The actual selection cost is \(n(K+m)\), including scoring aborted trials. The smoothing error is \(\tau\log m=\varepsilon/2\). [Query safety](../Proofs/AffineResidualQuerySafety.lean) and [amplification](../Proofs/AffineResidualAmplification.lean) require neither correctness nor measurability of arbitrary replies outside the feasible set. The measurable extension used in execution refinement is analysis only.

## Closest results and improvement regimes

[Carmon et al., COLT 2021](https://proceedings.mlr.press/v134/carmon21a/carmon21a.pdf), arXiv:2105.01778v1, Theorem 6 and Appendix A.3, provide the smooth finite-maximum and accelerated-linearization baselines. [Carmon et al., SODA 2024](https://arxiv.org/abs/2311.10886), arXiv:2311.10886v1, Sections 2 and 7 and Theorem 8.1, already use affine caches and moving Gibbs distributions; those ideas are not new here. [Carmon and Hausler, NeurIPS 2022](https://arxiv.org/abs/2203.13225), Proposition 1 and Appendix B, supply the local-to-global and multilevel framework. [Lan and Ouyang](https://arxiv.org/abs/2111.00996), v1, develop mirror-prox sliding; merely invoking generic norm-based stochastic mirror-prox bounds does not give the residual entropy calculation used here.

The existing [centered affine-softmax result](AffineSoftmaxFiniteMaximum.md) is also a stronger comparator than the older published envelope in some regimes. It gives
\(\widetilde O(m+mb^{1/3}+m^{3/4}\sqrt b+m^{6/7}(ab)^{2/7}+a)\).
It is a repository result, not evidence of conference acceptance. Its moving-Gibbs gradient estimator retains a \(G^2L^2r^4/\tau^2\) variance term and a radius restriction. This theorem instead solves the residual saddle problem on larger balls. Batching that prior estimator divides variance while multiplying query cost; it does not remove that term. Applying known global machinery to the new local guarantee yields the displayed five-term cost, but the prior local guarantees do not supply that guarantee. Generic clipping or smoothing alone does not justify discarding either initialization or dual noise.

For fixed \(G=L=R=1\), fixed confidence, and \(m=\varepsilon^{-\gamma}\), the inspected comparator orders are:

| Result | Component-query order, ignoring logarithms |
|---|---|
| Accelerated linearization | \(m\varepsilon^{-1/2}\) |
| COLT 2021, Theorem 6 | \(m\varepsilon^{-2/3}+\sqrt m\varepsilon^{-1}\) |
| SODA 2024, Theorem 8.1 | \(m\varepsilon^{-1/3}+\varepsilon^{-2}\) |
| Repository centered affine-softmax result | \(m+m\varepsilon^{-1/3}+m^{3/4}\varepsilon^{-1/2}+m^{6/7}\varepsilon^{-4/7}+\varepsilon^{-1}\) |
| This theorem | \(m+m\varepsilon^{-2/5}+m^{3/4}\varepsilon^{-1/2}+\varepsilon^{-2/3}\) |

The new exponent is \(\max\{\gamma+2/5,3\gamma/4+1/2,2/3\}\). It strictly improves the minimum of these inspected comparators for **\(1/6<\gamma<6/5\)**. At \(\gamma=2/5\), the exponent improves from \(9/10\) to \(4/5\); at \(\gamma=3/4\), from \(17/14\) to \(23/20\); at \(\gamma=1\), from \(10/7\) to \(7/5\). The theorem is not uniformly better: it has an eighth logarithmic power versus the repository comparator's seventh, and the latter has a better large-component-count regime. No optimality claim is made. Dimension-dependent cutting-plane methods can be preferable in low dimension; the improvement is in dimension-free component complexity, and dimensions may grow with accuracy.

Accuracy comparisons use direct objective error. The present tunable-confidence result implies expected error at most \(\varepsilon\) by running at accuracy \(\varepsilon/2\) and failure probability \(\min\{1/2,\varepsilon/(4GR)\}\): every feasible objective gap is at most \(2GR\). This costs only additional logarithms, with selection already counted. This is a comparison reduction, not a second main formal theorem. SODA's expected-error and high-probability cost guarantees can similarly be compared at constant success using Markov bounds and a cost cutoff. COLT's global assumptions and nearby global minimizer differ from the ball-local specification; the rate comparison also holds on their common global subclass.

## Motivation, coverage, and limitations

A standard nonlinear family is grouped weighted Huber regression:
\(f_i(x)=\sum_j c_{ij}h_\kappa(u_{ij}^{\mathsf T}x-v_{ij})\), \(c_{ij}\ge0\).
One may take \(G\ge\max_i\kappa\sum_jc_{ij}\|u_{ij}\|\) and \(L\ge\max_i\sum_jc_{ij}\|u_{ij}\|^2\). Dense, nonorthogonal features give interacting coordinates in arbitrary dimension. Threshold crossings allow Hessian discontinuities. These losses are globally convex and Lipschitz, so the improvement is not solely an artifact of ball-local assumptions. Expensive aggregate component evaluations motivate the model; access to individual data samples or whole component formulas is different oracle access.

The surveys independently covered publicly available 2025 and 2026 ICML, ICLR, and NeurIPS results and approximately November 2024–November 2026 arXiv submissions and revisions, following foundational papers and later citations. Checks ran through 12 November 2026 UTC. The comparison used primary theorem scopes, not venue status as a ranking rule. [Gladin et al., ICML 2026](https://proceedings.mlr.press/v306/gladin26a.html), arXiv:2509.24894v4 (18 June 2026), Assumption 2.8 and Theorem 2.9, use concentration and objective-bracket information for a SoftPlus surrogate; uniform-component concentration can grow with \(m\). [Gladin, Popova, and Babinskii](https://arxiv.org/html/2609.32872v1), a September 2026 preprint, Theorem 2, assumes a near-active top-\(k\) condition and retains an \(\varepsilon^{-2}\) gradient term. [Zoll and Grimmer](https://doi.org/10.1093/imanum/drag062), arXiv:2503.07566v3, Section 3.4, use a perturbed-composition criterion; it is not automatically direct maximum-objective accuracy. These are not substitutes for the table's strongest applicable baseline.

An unidentified OpenReview source `ddRfkfiMsf` remained inaccessible despite multiple access methods and was not excluded by a theorem comparison. The novelty claim is relative to the inspected primary literature, with this access limitation explicit. Full-function sampling, second-order access, finite-sum means, and Lipschitz-Hessian assumptions were kept separate. Sampling representatives and exact cached subproblem solvers are mathematically specified; executable runtime and practical efficiency are not proved. In particular, the \(L=0\) case admits direct recovery with \(m\) queries, and this uniform construction need not be the best implementation for that case.
