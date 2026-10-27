# Envelope cubic minimax under an inner PL condition

The [main theorem](EnvelopeCubicNonconvexPL.lean) proves a full-Hessian oracle bound for second-order stationarity of the value function of a nonconvex minimax problem. The inner problem satisfies a uniform Polyak–Łojasiewicz (PL) inequality; it need not be concave or have a unique maximizer. The contribution is an extension of envelope cubic minimax analysis from strong concavity to PL, including the regularity and approximate-oracle arguments needed when the inner Hessian is singular.

## Problem and guarantee

The [specification](../Setups/NonconvexPLSecondOrder.lean) takes arbitrary finite-dimensional real Hilbert spaces and a function `f(x,y)` with globally L-Lipschitz joint gradient and ρ-Lipschitz joint Hessian. The gradient is differentiable. Every inner maximum is finite and attained. With Φ(x)=max_y f(x,y), the uniform condition is

`2μ(Φ(x)−f(x,y)) ≤ ‖∇ᵧf(x,y)‖²` for every x,y.

The supplied parameters satisfy 0<μ≤L, ρ>0, ε>0, Δ,D≥0, with Φ(x₀)−Φ(x)≤Δ for every x and Φ(x₀)−f(x₀,y₀)≤D. There is no convexity assumption in x or y, no maximizer-selection oracle, and no rank, unique-solution, or Morse–Bott hypothesis. These are global assumptions, not guarantees for arbitrary learning objectives.

One oracle call returns the exact value, joint gradient, and full joint Hessian at a queried pair. Internal linear algebra and global minimization of finite-dimensional models are free in this oracle model. The theorem does not give an arithmetic-complexity or Hessian-vector-product bound.

Let κ=L/μ and

`R = 2+κ+ρ²(Δ+D)/μ³+ρε/μ²+μ²/(ρε)`.

The explicit public budget is

`K = ceil(10¹⁰ [1+κ+Δ√ρ κ^(3/4)/ε^(3/2)+Δρ²/μ³] log² R)`.

The returned primal point x satisfies

`‖∇Φ(x)‖ ≤ ε`, and `∇²Φ(x) ⪰ −√(100ρ√κ(4+κ)ε) I`.

The theorem also establishes that Φ is twice differentiable. The deterministic guarantee holds for every oracle seed; the framework states it almost surely under its explicit execution law. All K calls are counted, including initialization, refinement, intermediate tracking points, and harmless padding after termination. There is no dimension factor in the number of full-Hessian calls; each reply itself has dimension-dependent size.

## Algorithm and proof mechanism

The [algorithm and output](../Algorithms/PLMinimaxMethod.lean) use the proximal envelope E(z)=min_u[Φ(u)+L‖u−z‖²]. Initialization alternates a prescribed number of primal gradient steps and dual ascent steps for the regularized saddle problem. Cubic steps use approximate envelope gradient and Hessian jets. Each proposed center displacement is divided into a prescribed number of tracking segments, with residual-model Newton refinement at each segment. The output is the refined primal component of the terminal regularized saddle approximation, rather than the envelope center.

The [finite-dimensional models](../Algorithms/PLMinimaxCubic.lean) depend only on available oracle replies and public parameters. The algorithm uses a regularized inverse of the joint Hessian, not an exact unknown saddle point or a supplied pseudoinverse of its limiting Hessian. All tolerances and iteration counts are explicit in `tuning`.

The main analytical step is to recover envelope second-order regularity despite nonunique inner maximizers. Uniform PL gives a joint residual error bound for the regularized problem. Nearby saddle points admit bounded lifts of center displacements, of order √κ. At a saddle, the kernel of the joint Hessian has zero primal component. Consequently its linearized saddle equation has a unique primal derivative even when its full solution is nonunique. Difference quotients and quantitative remainder estimates yield an envelope Hessian Lipschitz constant

`M = 6ρ√κ(4+32κ)`.

This is the same κ^(3/2) order as in the strongly concave envelope analysis. A Tikhonov regularization controls the approximate Hessian without imposing a nonzero spectral gap on the entire saddle Hessian. Residual refinement and segmented tracking supply the required jets with logarithmic work per segment. A separate inverse-proximal argument establishes differentiability of ∇Φ and transfers negative-curvature guarantees to the actual returned primal point. The proof does not assume value-function smoothness, convergence of iterates, or an oracle error bound that already encodes convergence.

The supporting derivations are grouped in the `PLMinimax*` [proof modules](../Proofs/PLMinimaxConvergence.lean). The [budget proof](../Proofs/PLMinimaxBudget.lean) connects the simplified expression above to the exact execution count. Its large universal constant pays for conservative rounding and logarithmic bounds; it is not a claim about practical performance.

## Closest results and novelty boundary

The principal comparison is Zhou–Chen–Luo–Liu, [*Envelope Cubic Regularized Newton Method for Nonconvex–Strongly-Concave Minimax Optimization*, arXiv:2610.20345v1](https://arxiv.org/html/2610.20345v1), dated October 14, 2026. This is a preprint with no verified conference acceptance. Lemmas 4–5 give saddle-lift and envelope-Hessian regularity under strong concavity; Proposition 3 transfers curvature to a proximal primal point; Theorem 11 gives a true-value second-order guarantee with leading full-Hessian cost of order Δ√ρ κ^(3/4)ε^(−3/2), subject to its accuracy regime. The present result preserves that leading order while replacing strong concavity by uniform PL. It does not improve the leading rate on the strongly concave subclass. The new difficulty is precisely the singular, nonunique, potentially nonconcave inner problem, for which the usual inverse-Hessian argument is unavailable.

Zhang et al., [*Matching Full-Hessian Oracle Complexity for Nonconvex–Strongly-Concave Minimax Optimization*, arXiv:2610.16771v2](https://arxiv.org/html/2610.16771v2), revised October 19, 2026, gives a broader parameter-dependent frontier for first-order stationarity. It is a preprint with no verified conference acceptance. Its first-order frontier must not be quoted as a second-order guarantee. The present theorem neither improves that frontier on its original class nor proves matching lower bounds.

Uniform inner PL is established in minimax research: Nouiehed et al., [NeurIPS 2019](https://proceedings.neurips.cc/paper_files/paper/2019/hash/25048eb6a33209cb5a815bff0cf6887c-Abstract.html), Lemma A.5, establish value differentiability; Yang–Orvieto–Lucchi–He, [AISTATS 2022](https://proceedings.mlr.press/v151/yang22b.html), study smoothed gradient descent-ascent with a first-order stationarity guarantee of order LΔκ/ε². The current assumptions add global Hessian regularity and stronger oracle access, and the target also controls negative curvature. A comparison with that first-order theorem alone would not establish the contribution.

Degenerate implicit differentiation is not itself new. Arbel–Mairal, [NeurIPS 2022](https://papers.nips.cc/paper_files/paper/2022/hash/349a45f211fb1b3850da1ccd829e869e-Abstract-Conference.html), develop pseudoinverse differentiation for parametric Morse–Bott bilevel problems. Rebjock–Boumal, [arXiv:2303.00096v2](https://arxiv.org/abs/2303.00096v2), revised September 9, 2024, connect local PL, error bounds, quadratic growth, and Morse–Bott structure. Here the quantitative global envelope regularity, oracle approximation, and full execution bound are derived directly from the minimax PL assumptions; a separate structural hypothesis is not supplied.

The residual-model Newton tracker is also established technology, related to Bellavia–Cartis–Gould–Morini–Toint, [SIAM Journal on Numerical Analysis](https://doi.org/10.1137/080732432), and Bellavia–Morini, [IMA Journal of Numerical Analysis 35(2), 2015](https://doi.org/10.1093/imanum/dru021). Its local error-bound convergence is supporting machinery, not the claimed novelty. A global invocation of local Newton convergence would be invalid; initialization and tracking costs are retained explicitly.

## Standard reductions and improvement regimes

A direct cubic method on Φ, using the standard value-Hessian Lipschitz scale ρκ³, has leading first-order cost of order Δ√ρ κ^(3/2)ε^(−3/2), but its default curvature tolerance is weaker than ours. Retuning this method alone to our curvature target gives a substantially worse bound. That weaker retuned comparison is not used as the strongest baseline.

A stronger reconstructed reduction combines direct-value first-order cubic steps with targeted negative-curvature escapes. At an inner maximizer, write the Hessian blocks as `[A B; Bᵀ −C]`. On a negative-curvature direction v of the value Hessian, the lift w=C†Bᵀv satisfies ‖w‖²≤κ‖v‖². Joint Taylor expansion and PL then control an escape with cubic remainder of scale ρκ^(3/2) and quartic correction of scale ρ²κ²/μ. For a curvature tolerance η of order √(ρκ^(3/2)ε) with η≤cL for a sufficiently small universal c, the escape cost and direct-value first-order cost are both bounded, up to logarithmic refinement, by

`Δ√ρ κ^(3/2) ε^(−3/2)`,

with a tracking term of order Δρ²/μ³. This is a reconstructed combination of known techniques, not a theorem attributed verbatim to one paper. Approximate maximization and derivative estimation require slack and refinement. Accounting for this stronger reduction leaves a conservative κ^(3/4) improvement in the leading accuracy-dependent term of the present guarantee. The crucial advantage is the envelope's global Hessian regularity, rather than a new scalar negative-curvature escape calculation.

The term Δρ²/μ³ is dominated by the new accuracy term when ε is at most a constant times L²/(ρκ^(3/2)). An improvement in the total oracle bound additionally requires the accuracy term to dominate κ initialization and the retained logarithms. Thus the result is a high-accuracy, sufficiently nontrivial-gap improvement, not universal superiority over every parameter regime or every algorithm. D occurs in the logarithmic factor. There is no claim that these initialization and tracking terms are lower bounds.

Pan–Li, [arXiv:2608.26799v1](https://arxiv.org/pdf/2608.26799v1), dated August 27, 2026, prove first-order NC–PL lower bounds. Their C¹,¹ hard instances do not directly furnish a Hessian-Lipschitz lower bound with the present full-Hessian oracle. No same-class optimality claim follows from those results.

## Strictly broader nonlinear instances

For q(t)=t²/2+2(1−cos t), q is nonconvex since q″(π)=−1, but satisfies a global PL inequality with μq=(1−2/π)²/3. Indeed q(t)≤3t²/2 and |q′(t)|≥(1−2/π)|t|. Consider

`f(x,y)=h(x)−Σᵢ q((Ay−Bx)ᵢ)`,

where A is surjective, possibly noninjective, B couples coordinates, and h is a bounded-below smooth nonlinear function with bounded second and third derivatives. For example h can be a sum of cosine potentials of interacting linear forms. With σmin(A) denoting the smallest positive singular value of A, the inner PL constant is μq σmin(A)²; a joint gradient Lipschitz constant is Lh+3‖[−B A]‖² and a Hessian Lipschitz constant is ρh+2‖[−B A]‖³. This family works in arbitrary finite dimensions and has nonlinear, nonconcave inner objectives and nonunique maximizers when A has a kernel. It is excluded by strong concavity. These examples establish strict inclusion and nonlinear scope; they are not hardness constructions or claims of practical acceleration on that particular family.

The specification does not assume affine maximizer sets: the regularity argument accommodates curved sets as well. Neither a scalar calculation nor the special affine-residual family is used to prove the general theorem.

## Limitations and verification scope

All assumptions are global and the oracle is exact. The result does not cover stochastic Hessians, nonsmooth constraints, approximate PL, unattained inner suprema, or only local PL without an invariant-region argument. The algorithm uses known parameter bounds and noncomputable exact finite-dimensional model minimizers in the oracle-complexity sense. It is not a practical implementation claim or an adaptive parameter-free method.

The Lean result verifies the stated bound and its execution under the specification. It does not formalize literature novelty, the reconstructed comparison algorithm, or conference acceptance. Those require independent mathematical and literature assessment. The closest preprints above are identified by their reviewed versions and publication status; the claimed gain is the PL extension and the associated same-class high-accuracy bound, not formalization alone.
