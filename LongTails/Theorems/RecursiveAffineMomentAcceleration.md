# Recursive acceleration with affine finite-moment gradient noise

This result concerns smooth convex optimization with an unbiased stochastic gradient whose heavy-tailed error has both an additive component and a component proportional to the population gradient. It reuses the established [AffineMomentConvex specification](../Setups/AffineMomentConvex.lean); it does not introduce a new noise assumption. The proposed contribution is an improved oracle-complexity upper bound in mixed additive/relative heavy-tail regimes. The construction has enormous constants and is not a claim of practical computational efficiency.

## Statement and information model

Let `1 < p ≤ 2` and `q=p/(p−1)`. The objective is convex and globally `L`-smooth on a separable real Hilbert space, with a minimizer `xstar` satisfying `‖x0−xstar‖≤R`. The gradient oracle is jointly measurable, integrable, unbiased, and has an integrable central `p`-moment satisfying

`E‖g(x,ξ)−∇f(x)‖^p ≤ σ0^p + σ^p‖∇f(x)‖^p`.

Samples are IID under an abstract probability measure, with the shared repository IID structure recording independence, measurability, and marginal laws. The proof derives a product representation internally. No symmetry, density condition, finite sample space, samplewise smoothness, common sample minimizer, population strong convexity, bounded domain, function-value access, Hessian access, or paired evaluations with the same sample is required. The algorithm knows bounds `L,R,σ0,σ,p` and requested `ε,δ`; this is not an adaptation result.

Put

`T=LR²/ε`, `V=(σ0R/ε)^q`, `M=4+T+V+1/δ`, `W=2+q+log M`.

The [main theorem](RecursiveAffineMomentAcceleration.lean) uses the explicit integer budget

`K = ceil(exp(2^32 q^4 (1+sqrt(log M)) log W) * ((1+σ)^q sqrt(T)+1+V) / δ)`.

Under the product of private algorithm randomness and the specified IID sample law, the returned output satisfies

`P(f(output)−f(xstar)>ε) ≤ δ`.

The formal specification expresses this probability as the integral of the failure indicator. The bound is on actual raw oracle calls in `Template.execute`, not merely virtual queries or expected work. An execution that cannot complete within the cap returns `x0`; its probability is included in the guarantee. When `T≤1`, the algorithm returns `x0` directly.

## Algorithm and proof mechanism

The [algorithm](../Algorithms/StochasticEnvelope.lean) constructs a recursive family of unbiased stochastic gradients for Moreau envelopes. Its plans and their raw call accounting are in [StochasticEnvelopeProgram](../Algorithms/StochasticEnvelopeProgram.lean). The output is obtained by recovering approximate proximal points back through the envelope levels. It is not a last iterate of SGD, and the setup imposes no artificial restriction on admissible algorithms.

The essential local construction solves the regularized problem `f(x)+μ‖x−y‖²/2` using an observable robust pilot, localized clipped accelerated stages, and replicated distance selection. If `z=prox(y)`, its distance error has the scale

`E‖X_n−z‖^p ≤ 2^18 (s/μ+a‖y−z‖)^p n^(−(p−1))`.

This local bound requires an incoming exponent `1<p≤2`, `μ>0`, `κ=(L+μ)/μ≥2`, `n≥1`, and `0<a≤κ^(−2)`. Public initial batching and recursive tuning establish these numerical conditions; they are not additional restrictions on the original problem. Here `s,a` are the incoming oracle's additive and relative scales. The algorithm never observes `z`, the population gradient, or the true distance `‖y−z‖`. A pilot radius and fourth-moment bounds control failures of localization, including the zero-scale case. The radius is not an additional assumption supplied by the problem.

Three independent approximate solves and a geometrically randomized multilevel difference produce an exactly unbiased envelope-gradient oracle. A slight loss in moment exponent makes both its moment and expected work finite. The proof preserves the joint random-level/output law; it does not assume unbiasedness conditional on a fixed multilevel seed. Across successive envelopes, attenuation of the additive error scale cancels the growth in virtual-query work. This cancellation yields an additive statistical cost instead of paying the original additive-noise complexity independently for every envelope query.

The depth is `ceil(sqrt(log M))` in the nontrivial regime. Internal moment exponents drift by a factor `(1+1/d²)^i` in their conjugates. Publicly selected batches, localization radii, repetition counts, geometric level probabilities, and all tuning inequalities are derived explicitly. Every replica, pilot call, one of the three multilevel solves, inactive padded stage, and nested raw query is counted. The proof first bounds expected random work and then applies a deterministic execution cap; this is the source of the `1/δ` cost.

Moreau smoothing, accelerated proximal methods, median-of-means selection, and multilevel debiasing are established ingredients. The contribution claim concerns the localized affine-preserving oracle construction and its recursive mixed-noise complexity accounting, not those ingredients separately. Supporting proofs are organized in [Oracle](../Proofs/StochasticEnvelopeOracle.lean), [Recursion](../Proofs/StochasticEnvelopeRecursion.lean), [Budget](../Proofs/StochasticEnvelopeBudget.lean), and [Run](../Proofs/StochasticEnvelopeRun.lean), with the local analytic and sampling lemmas in the adjacent StochasticEnvelope proof modules.

## Closest comparisons and improvement regimes

The strongest same-setup repository baseline is [AffineMomentAcceleration](AffineMomentAcceleration.lean). Up to its explicit constants and logarithms, for `T≥1` its budget is

`(1+σ)^q T^(q/(q+2)) + V`.

The additional term involving `1/(LR)` in that theorem is at most a constant multiple of its `R/ε` term when `T≥1`. The comparison is between the same unbiased affine central-moment model, probability-of-objective-error criterion, and raw stochastic-gradient calls. This result preserves that earlier theorem.

For fixed `p∈(1,2)`, fixed positive `σ`, and fixed confidence, the new overhead is `M^o(1)`. If `V=T^v` along a family of instances, the leading powers of `T` change from `max(q/(q+2),v)` to `max(1/2,v)+o(1)`. Thus there is a strict asymptotic improvement when `v<q/(q+2)`, including the mixed regime `1/2<v<q/(q+2)`. For `p=3/2` and `v=.55`, the powers are `.6` versus `.55+o(1)`.

This is not universal superiority. With fixed positive additive noise and `ε→0`, `V` grows proportionally to `T^q` and already dominates both guarantees. If `δ=T^(−w)`, the new cap loses an additional power `w`; improvement requires `w+max(1/2,v)<q/(q+2)`. The previous logarithmic confidence dependence can be much better. The explicit overhead is subpolynomial only for fixed `p`, is enormous numerically, and supplies no useful practical crossover claim.

Pure-relative near-acceleration can already be obtained from [RecursiveRelativeErrorConvex](RecursiveRelativeErrorConvex.lean) under [RecursiveRelativeErrorSmoothConvex](../Setups/RecursiveRelativeErrorSmoothConvex.lean) and robust batching; no novelty is claimed for `σ0=0`. Finite-variance acceleration is also established, including [AGNES, NeurIPS 2024](https://papers.nips.cc/paper_files/paper/2024/hash/24d2dd6dc9b79116f8ebc852ddb9dc94-Abstract-Conference.html). The intended new regime is genuinely heavy-tailed mixed noise, not a renamed finite-variance theorem.

[Asi, Carmon, Jambulapati, Jin, and Sidford, NeurIPS 2021](https://proceedings.neurips.cc/paper/2021/file/597c7b407a02cc0a92167e7a371eca25-Paper.pdf), Theorem 1 and Section 2.3, provide the foundational unbiased optimization-estimator construction. [Kulunchakov and Mairal, NeurIPS 2019](https://proceedings.neurips.cc/paper_files/paper/2019/file/4a1c2f4dcf2bf76b6b278ae40875d536-Paper.pdf), Proposition 4, equation (13), and Proposition 6, equation (14), give generic stochastic acceleration mechanisms. For the cited finite-variance Catalyst reduction, equation (13) has a statistical term `Bσ²/(qC^(3/2)τε)`, where `qC=μ/(μ+κ)`; Proposition 6 under the stronger surrogate condition (14) improves its denominator to `qC τε`. For ISTA with `κ=L−μ`, `B=1/L`, and constant `τ`, the former pays an extra `sqrt(L/μ)` over `σ²/(με)`. This identifies an interface requirement in that particular reduction, not a lower bound on all proximal compositions or an impossibility for finite-`p` acceleration. Constructing another suitable finite-`p` surrogate interface is not ruled out. The present proof supplies an affine unbiased envelope-gradient interface instead. Applying a variance-based result to a single finite-`p` gradient is invalid when `p<2`; ordinary arithmetic averaging does not make its second moment finite. Robust distance medoids can acquire finite higher moments, but generally introduce bias; unbiasedness must be recovered and proved.

[Lobanov, Dvinskikh, and Gasnikov, arXiv:2609.33415v1, September 27, 2026](https://arxiv.org/html/2609.33415v1), Assumption 3 and Theorem 9, give related affine/generalized-noise guarantees. In the matched convex affine specialization, the relevant published-preprint scale is `sqrt(T)+σ^q T^(q/2)+V`, weaker than the repository baseline used above. [Nekrasova et al., arXiv:2610.28107v1, October 20, 2026](https://arxiv.org/html/2610.28107v1), Assumptions 3.4–3.5 and Theorem 5.2, consider finite-moment and broader weak-tail settings and discuss unresolved relative-noise dependence. These are preprints, not asserted conference acceptances.

## Nonlinear examples and model motivation

For arbitrary finite dimension at least two, consider dense, nonorthogonal feature vectors `a_j` spanning the space and

`f(x)=λ〈b,x−θ〉²/2 + Σ_j w_j log cosh(〈a_j,x−θ〉)`,

where `λ,w_j>0` and `b≠0`. This is a smooth robust residual objective with a rank-one quadratic penalty. Its minimizer is `θ`, and one may take `L=λ‖b‖²+‖diag(sqrt(w))A‖op²`. Its Hessian varies with the point and generally has noncommuting dense terms. For generic feature vectors, curvature tends to zero along an appropriate direction orthogonal to `b`, so the function is not globally strongly convex; its gradient is unbounded in other directions. This example witnesses a meaningful nonlinear class, not a lower bound or worst-case improvement for that particular loss.

A concrete oracle is

`g(x)=[1+c(U−1)]∇f(x)+b0 Z e`,

where `0<c≤1`, `b0>0`, `e` is a unit vector, `U` is a mean-one positive Pareto gain, and `Z` is an independent centered Pareto perturbation. Choose tail exponent `α` with `p<α<2`. The underlying gain and perturbation have finite `p`-moments and infinite variance. The multiplicative term vanishes at stationary points; the independent additive term gives infinite oracle-noise variance everywhere, including at the minimizer. The oracle is the gradient of a random convex loss with a nonnegative random gain and a heavy-tailed linear perturbation. The algorithm sees only its gradient reply. With `m1=E|U−1|^p` and `m0=E|Z|^p`, the exact assumption holds for `σ^p=2^(p−1)c^p m1` and `σ0^p=2^(p−1)b0^p m0`. Symmetry is unnecessary. This mechanism motivates the affine model; it does not assert that arbitrary heavy-tailed regression data automatically satisfy it.

## Search coverage

Both Researcher and Reviewer independently surveyed the two most recent publicly available ICML, ICLR, and NeurIPS editions and roughly October 2024–October 2026 arXiv submissions/revisions, then followed foundational and stronger older results. Conference status was checked through official proceedings/OpenReview where accessible. Existing repository results and open/closed PRs were checked separately; they were not treated as evidence that an extension was open.

The novelty assessment is relative to the primary results compared above. The StructuredMoM paper was excluded from the review scope at the user’s explicit direction; no non-overlap claim about that excluded paper is made.
