# Stochastic nonlinear inequalities with quadratic value-noise transfer

The result concerns minimizing a smooth, possibly nonconvex function subject to finitely many smooth nonlinear inequalities, when objective gradients, constraint values, and constraint Jacobians are all stochastic. It gives a constant-probability approximate KKT guarantee with an inverse-cubic accuracy term in **every primitive oracle**, including constraint values. The qualification is substantial: the full mean constraint Jacobian must be uniformly surjective everywhere, and its Frobenius norm and the objective gradient must be globally bounded. This is a result for that class, not for general MFCQ or active-set LICQ problems.

The formal entry points are [the theorem](SurjectiveStochasticInequalityKkt.lean), [the setup](../Setups/StochasticSurjectiveInequalities.lean), and [the algorithm and output](../Algorithms/SurjectiveProxLinear.lean). The setup leaves the algorithm family unrestricted.

## Specification and oracle

The decision space is any finite-dimensional real Hilbert space. There are `m ≥ 1` inequalities `c_i(x) ≤ 0`. A known bound `H ≥ 1` simultaneously bounds the mean objective gradient, the Frobenius norm of the mean Jacobian, their Lipschitz constants, and the reciprocal smallest singular value of the mean Jacobian:

\[
\|\lambda\|\le H\|J(x)^*\lambda\|\quad\text{for every }x,\lambda.
\]

This applies to all rows, including inactive constraints. It excludes redundant rows, `m` larger than the decision dimension, and many compact feasible sets. It is stronger than the local active-set regularity used in much SQP work. No rank condition is imposed on sampled Jacobians.

A sample supplies the triple `(g(x,ω),v(x,ω),D(x,ω))`. Its mean is `(∇f(x),c(x),J(x))`. The sum of the three squared errors has expectation at most `σ²`. The sum of the squared same-sample differences between two points has expectation at most `H²‖x-y‖²`. The three components may be correlated. They are jointly measurable in point and sample; first moments and the relevant squared moments are explicitly integrable. These are finite-variance, mean-square-smooth oracle assumptions, without bounded samples or exponential tails.

A query is a pair of points evaluated with the **same** fresh sample. Different replies use IID samples. The specification permits an arbitrary IID stream law; the proof derives its product-law representation from independence and the marginal laws. The independent algorithm seed chooses the output time. There is no restriction to a finite sample space.

Set `ρ=4H(H+1)` and `F(x)=f(x)+ρ∑_i[c_i(x)]_+`. The initial condition is `F(x₀)-F(x)≤Δ` for all `x`, with known `Δ≥0`. It does **not** require `f` to be bounded below separately. The target accuracy is `0<ε≤1`.

Assumption provenance is distinct from literal equivalence. [Zhang–Xiao v2](https://arxiv.org/abs/2004.04357v2), Assumption 5, uses finite variance and mean-square Lipschitzness of mappings and Jacobians; Assumption 3 supplies a composite-objective lower bound. [SmALM](https://optimization-online.org/wp-content/uploads/2026/06/SmALM-5.pdf), Assumption 1.1, bounds the mean objective gradient, constraint values, and objective below on an iterate-containing open convex region; Assumption 1.2 gives unbiased triples with separate variance and mean-square smoothness conditions; Assumption 1.4 bounds the full Jacobian's smallest singular value on that region. Here we strengthen the spatial requirement to the **whole decision space**, impose a **Frobenius** mean-Jacobian bound, and use a common supplied upper bound `H`; these are our stated global restrictions, not verbatim SmALM assumptions. We remove bounded constraint values and a separate objective lower bound, retaining only the penalty lower bound, and do not impose SmALM's Hessian-Lipschitz Assumption 1.3. The joint-sum constants collect the three usual moments without component independence. IID samples and paired reuse are standard recursive variance-reduction access; measurability and integrability are explicit technical conditions. The separately stated mean gradient/Jacobian Lipschitz bounds follow from unbiasedness and joint mean-square smoothness, so add no mathematical restriction to the oracle model.

## Guarantee and accounting

The returned pair `(x,λ)` satisfies, with probability at least `3/4`,

\[
\lambda\ge0,\qquad
\|\nabla f(x)+J(x)^*\lambda\|\le\varepsilon,\qquad
\|[c(x)]_+\|\le\varepsilon,\qquad
\sum_i|\lambda_i c_i(x)|\le\varepsilon.
\]

The public paired-call budget is

\[
\left\lceil69+
\frac{2^{29}m^2H^{10}\Delta+2^{44}m^4H^{18}\sigma^2}{\varepsilon^2}
+\frac{2^{48}m^4H^{19}\Delta\sigma}{\varepsilon^3}\right\rceil.
\]

Each paired reply costs at most two evaluations of **each** primitive, or six primitive evaluations when all three costs are summed. The initialization batch and fresh certificate batch are included. The implementation freezes its output after certification but `execute` continues issuing padding queries: the displayed budget counts these too. It is not merely the useful-prefix length. No objective-value or Hessian oracle is used. Exact finite-dimensional convex subproblem solves are uncharged computational operations in this oracle model.

For fixed `m,H,Δ,σ>0`, every primitive has `O(ε^{-3})` cost. At zero noise the bound is `O(1+m²H¹⁰Δ/ε²)`. The separate startup term `m⁴H¹⁸σ²/ε²` remains; there is no claim of optimal conditioning, optimal dependence on `m`, unknown-parameter adaptivity, or practical numerical superiority.

## Algorithm and mechanism

The method uses a recursive same-sample variance-reduced estimate of the full triple. The estimator itself is never clipped. The gradient and Jacobian estimates are clipped separately only when constructing the prox-linear subproblem; constraint-value estimates remain raw. A small positive ridge on the box dual makes the sampled minimizer unique and continuous even when the sampled Jacobian loses rank. The update is relaxed. A uniform time is selected independently, and a fresh ordinary mean batch estimates the triple at that point for the final multiplier.

The technical issue is the effect of stochastic **constraint values** at active-set switches. Generic nonsmooth-composite arguments control model-objective error, where value errors appear linearly. The proof instead combines true-dual strong convexity from mean-Jacobian surjectivity with a Moreau-envelope potential. If `s(x)` is the exact prox-linear step and `ŝ(x)` the sampled regularized step, the proved bound is

\[
\|\hat s-s\|^2\le C(\|\hat g-g\|^2+\|\hat c-c\|^2+
\|\hat J-J\|_F^2+\tau^2),\qquad C=1024m^2H^{12}.
\]

No strict complementarity or fixed active set is used. For `γ=1+H+ρmH`, the true Moreau proximal point `z` and exact linear-model point `x+s` satisfy

\[
\|x+s-z\|^2\le\tfrac35\|z-x\|^2-\tfrac15\|s\|^2.
\]

Consequently, the relaxed perturbed update decreases the Moreau envelope by a multiple of `‖s‖²`, up to a **quadratic** step-estimation error. Combining this with the recursive estimator variance gives a Lyapunov inequality and an average squared-step bound `r²/128`, where `r=ε/(64mH³)`. The fresh certificate error exceeds its threshold with probability at most `1/8`; the chosen exact step exceeds `r/4` with probability at most `1/8`. A union bound gives the simultaneous KKT guarantee. Independence between these two success events is not assumed.

The distinction from a model-gap substitution is real. With `c(x)=x`, `f(x)=-a tanh(x)`, `0<a<ρ`, and `x=0`, a value perturbation `0<e<η(ρ−a)` moves the model step from zero to `-e`. Its distance error is `e`, but its true regularized model-objective gap is `ae+e²/(2η)`, and its exact-penalty increase is `a tanh(e)`. Thus a quadratic model-gap or exact-penalty-descent claim would be false. The Moreau potential is the essential change.

## Comparison and novelty boundary

The claimed improvement is the stochastic constraint-**value** exponent, under the stated stronger global regularity, relative to applicable nonsmooth-composite and stochastic-inequality analyses. It is not a new variance-reduction estimator, a new QP perturbation theorem in isolation, or an optimality claim.

- Zhang and Xiao, [arXiv:2004.04357v2](https://arxiv.org/abs/2004.04357v2), revised May 14, 2021, subsequently *Mathematical Programming* 195 (2022): Section 4, Theorem 3, equation (48), printed page 20 gives `O(t^(-5/2))` inner-value cost and `O(t^(-3/2))` derivative cost for squared-stationarity tolerance `t`. Setting `t` proportional to `ε²` gives inverse-fifth value cost and inverse-cubic derivative cost on the norm scale. Section 5, Theorem 5's quadratic inner-value-error treatment requires the smooth-outer Assumption 6, which the hinge penalty violates. Their composite lower-bound assumption is compatible with our penalty lower bound. The linear objective coordinate can be handled analytically in a composite formulation; we do not use the lack of an objective-value oracle as a novelty argument.
- Wu and Grimmer, [arXiv:2412.15008v2](https://arxiv.org/abs/2412.15008v2), October 14, 2025; *SIAM Journal on Optimization* 36(3), 1619–1646 (2026), [DOI](https://doi.org/10.1137/25M1727606): Theorem 3.1 retains linear mapping-error dependence, and Assumption 2.3 uses subproblem objective accuracy. The scalar example above blocks simply inserting a squared step-distance error into that assumption. The latest arXiv text was checked; publisher full-text access was unavailable during review.
- Shi and Wang, [arXiv:2511.03210v2](https://arxiv.org/abs/2511.03210v2), November 7, 2025: Theorem 7 gives inverse-cubic derivative cost and inverse-fifth constraint-value cost for fully stochastic equality constraints with nonnegative bounds, under stronger samplewise assumptions and StrongMFCQ. This is a stronger derivative-cost comparison than the later heavy-tail table below. Our robust improvement claim concerns **constraint values only**. Their bounded-constraint and objective-lower-bound conditions require comparison on common subclasses, rather than treating their theorem as applicable to every penalty-only instance here.
- Han, Wang, Xu, and Zhang, [NS-SQP preprint](https://optimization-online.org/wp-content/uploads/2026/10/NS-SQP-1.pdf), October 2026: Table 1 is stated for `1<p<2`; its primitive exponents tend to `(gradient, Jacobian, value)=(3,5,5)` for inequalities and `(3,3,5)` for equalities as `p↑2`. These are limiting exponents, not a finite-variance theorem attained by substitution. The table also conditions completion of the prescribed iterations with probability at least `1−ε`. It is recent related context, not the main finite-variance baseline. Lemma 8 already treats sensitivity without strict complementarity under near-active regularity. Our rank assumption is stronger: full mean-Jacobian rank everywhere. Bounded constraint values and a lower bound on the objective in the SQP analysis also differ from our assumptions; comparisons concern common subclasses. We do not claim that nonsmooth QP sensitivity itself is new.
- Cui, Shi, Wang, and Xiao, [SmALM preprint](https://optimization-online.org/wp-content/uploads/2026/06/SmALM-5.pdf), June 2026: all-primitive inverse-cubic results for equality constraints are important prior art. Their Hessian-Lipschitz and equality framework does not directly give this C¹,¹ inequality theorem. Squared slacks lose rank at active constraints; linear slacks introduce nonnegative bounds requiring a constrained extension. The result does not improve the already-known equality exponent.
- Facchinei and Kungurtsev, [arXiv:2307.02943v3](https://arxiv.org/abs/2307.02943v3), July 28, 2025: Theorem 3.2 debiases nonlinear SQP directions under Assumption 3.2, including sample LICQ, strict complementarity, and exponential-moment conditions; the overarching convergence result is asymptotic. This is prior art on estimating nonlinear solution maps, but not the present finite-variance, finite-cost, active-switching guarantee.

The meaningful comparison regime fixes the conditioning and dimension parameters and lets accuracy decrease with positive noise and positive initial gap. The inverse-cubic value bound then improves the inverse-fifth value bounds above. Its large constants and powers of `H,m` can dominate at moderate accuracy. Exact-constraint subclasses and equality-only problems already admit inverse-cubic results and are not improvement claims here. There is no lower bound establishing optimality for this exact globally bounded-gradient class.

Projection and chart reductions were also checked. [R-SPIDER (AISTATS 2019)](https://proceedings.mlr.press/v89/zhou19a.html)'s exact supplied manifold operations do not charge stochastic constraint-value queries. A submersion theorem supplies local coordinates, not a known global chart or a cheap noisy projection. Freshly estimating an affine noisy boundary to accuracy `δ` alone costs order `σ²/δ²`; repeatedly doing this is not a free oracle reduction. This observation is a check on a particular reduction, not a lower bound for algorithms that reuse information. The [one-projection preprint, arXiv:2609.34099v1](https://arxiv.org/abs/2609.34099v1), and [deterministic-constraint stochastic SQP preprint, arXiv:2611.04403v1](https://arxiv.org/abs/2611.04403v1), likewise do not supply the missing all-primitive inequality guarantee.

## Nonlinear instances and limitations

A concrete family has variables `(x,y)` and constraints `c(x,y)=y-A tanh(Bx)`, with dense matrices `A,B`. The identity block in `y` gives full row rank uniformly; the other block couples the coordinates nonlinearly. The mean Jacobian Frobenius norm is at most `sqrt(m+‖A‖_F²‖B‖²)`, and its Lipschitz constant is at most `2‖A‖_F‖B‖²`. For `z=(x,y)`, choose `f(z)=N⁻¹∑ₖ Huberδ(aₖᵀz+bₖ tanh(wₖᵀz)−rₖ)` with dense predictors involving both blocks. Its gradient is bounded by `δ N⁻¹∑ₖ Aₖ` and is Lipschitz with constant at most `N⁻¹∑ₖ(Aₖ²+δ Bₖ)`, where `Aₖ=‖aₖ‖+|bₖ|‖wₖ‖` and `Bₖ=2|bₖ|‖wₖ‖²`. These objectives are C¹,¹ and need not even be C² at transverse Huber knots. A nonnegative loss ensures the penalty lower bound.

Random matrices `Aω` with mean `A` and finite Frobenius second moment, together with mean-zero additive finite-variance value noise `ζ`, provide stochastic values and Jacobians without bounded samples. The same sample at two points cancels additive value noise; bounded `tanh` and its derivatives give uniform joint variance and mean-square smoothness, with bounds determined by the matrix moments. Choose `H,σ` to dominate the combined objective and constraint constants. The identity block can represent recourse/capacity variables; this is an illustrative interpretation, not a claimed empirical application. We choose objectives depending on both `x` and `y` to give an interacting example; the theorem itself does not require dependence on every coordinate.

The weaker penalty-only lower bound also permits epigraph constraints `c(x,y)=h(x)-y`, `f(x,y)=y`, for C¹,¹, bounded-gradient, lower-bounded `h`. Here `inf f=-∞` while the exact penalty is lower bounded. This illustrates the scope of the lower-bound assumption, not a separate complexity novelty claim.

The global full-rank and bounded-derivative assumptions remain the principal limitation. The proof does not extend silently to redundant inequalities, compact feasible regions, active-set LICQ alone, biased oracles, or arbitrary nonsmooth constraints. All parameter bounds are supplied to the algorithm. The formal proof supports correctness of the stated theorem; it does not by itself establish literature novelty or conference acceptance.
