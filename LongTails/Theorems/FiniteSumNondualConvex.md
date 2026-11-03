# Finite-sum convex optimization with Euclidean smoothness on an ℓ₁ ball

## Statement and scope

The [Lean specification](../Setups/FiniteSumNondualSmoothConvex.lean) describes minimization of

\[
F(x)=\frac1n\sum_{i=1}^n f_i(x),\qquad x\in Q=R B_1^d,
\]

where every component is globally convex and differentiable with an L-Lipschitz Euclidean gradient. The positive parameters d,n,L,R,ε and the ball are public. An oracle call chooses a component and a feasible point and returns that component's exact gradient. Queries and the returned point must belong to Q. Function values, component proximal maps, a minimizer, and the minimum value are unavailable. There is no bound on gradient magnitudes, no interpolation assumption, and no restriction to a prescribed update family. In particular, large affine terms are permitted.

The [main theorem](FiniteSumNondualConvex.lean), `result : Convergence spec budget`, constructs the [algorithm](../Algorithms/FiniteSumNondual.lean) and proves

\[
\int \bigl(F(\operatorname{runOutput}(\omega))-F(x_*)\bigr)\,dP(\omega)\le\varepsilon.
\]

Here x* is a constrained minimizer, whose existence follows from continuity and compactness. P is explicitly the product of the algorithm's uniform finite private-tape law and the oracle's law. Exact replies make the output independent of the latter. Measurability and integrability are proved, not imposed on an internal selector. `runOutput` is the actual execution through `LongTails/Template.lean`.

Set A=LR²/ε and ℓ=1+⌊log₂(2+d+n+⌈A⌉)⌋. The exact public budget is

\[
2^{40}n\left(1+\left\lceil(A/n)^{1/3}\right\rceil\right)\ell^4.
\]

Thus the upper bound is O((n+n^(2/3)A^(1/3))ℓ⁴). The large universal constant is explicit and conservative; it is not a practical efficiency claim. The result counts component-gradient calls, including full snapshots, initialization, certification, and padding after the internal program terminates. It does not bound arithmetic time or the cost of exact convex-body operations.

## Matching lower bounds and the contribution

The contribution is a classification, up to logarithmic factors, of this finite-sum nondual oracle problem. The upper bound alone is a composition of established proximal nondual optimization and variance reduction, and is not claimed as an independently novel method. The substantive lower-bound claim concerns arbitrary randomized feasible-query algorithms, without linear-span, zero-respecting, stationary-sampling, or measurable-intermediate-query restrictions.

The complete supporting proofs include two precise impossibility statements for the same specification:

* [`component_not_convergence`](../Proofs/FiniteSumNondualLowerAffine.lean): for any valid parameters, a uniformly successful budget cannot satisfy 4T≤n, where T is its value at those parameters.
* [`normalized_not_convergence`](../Proofs/FiniteSumNondualLowerBound.lean): for any positive integer k, uniform success is impossible if
  \[
  8T\le nk,\quad d\ge k+1+1024(T+1)(k+1)^3,\quad
  32n(k+1)^3\varepsilon<LR^2.
  \]

These are Lean lemmas about `¬ Convergence spec budget`, not assumptions used to obtain the upper bound. They imply the lower scaling Ω(n+n^(2/3)A^(1/3)) in sufficiently high dimension, with the stated integer and dimension conditions. The claim is not fixed-dimensional optimality, exact logarithmic optimality, or a lower bound for algorithms allowed to query outside Q. No dimension condition is needed for the upper bound.

The hard family consists of globally convex C¹ flat-zone chains on randomly hidden coordinates, with links assigned independently to hidden component owners. A failed component search reveals no future owner; a successful search advances only one link. The proof combines this search delay with an ℓ₁-coordinate hiding argument that remains valid for arbitrary adaptive queries. The key scope issue is maintaining both kinds of concealment in the same actual transcript, rather than imposing a zero-chain restriction on the algorithm.

For k links, K=k+1 coordinates, a=R/K, and dead-zone width R/(8K²), incomplete exposure forces gap at least LR²/(16nK³). A serial-search potential bounds the probability of completion by 1/4 when 8T≤nk. The dimension condition bounds all premature coordinate exposures, including the returned output, by 1/32. The surviving mass gives a finite-instance average gap at least 23LR²/(512nK³). The auxiliary affine hidden-component family supplies Ω(n), including when ε is large relative to LR²; its slope is not bounded by smoothness.

The framework permits nonmeasurable intermediate algorithm operations. Consequently the lower proof fixes a private seed, averages over a finite hard-instance family independent of that seed, and only then integrates actual final gaps, whose integrability follows from the hypothetical convergence guarantee. It never conditions on potentially nonmeasurable transcript events or chooses a different adversarial instance for each seed.

## Upper algorithm and proof mechanism

The algorithm smooths the constrained objective through a proximal envelope with μ=L/n. Each requested center is feasible. The quadratic and ball indicator are treated as a known regularizer, leaving the component smoothness equal to L. A cached ProxSVRG solver uses step 1/(12L), 144n updates per epoch, and 512ℓ epochs. Initialization and the final residual certificate instead use step 1/L. One solver call costs exactly (145·512ℓ+3)n gradients, including both full-gradient evaluations needed for certification.

A certificate contains a feasible point w, its exact full gradient, and a residual r satisfying

\[
\nabla F(w)+\mu(w-c)+v=r,\quad v\in N_Q(w).
\]

The observable acceptance test is ‖r‖≤ρ, where

\[
m=64\left(1+\lceil(A/n)^{1/3}\rceil\right)\ell,\qquad
\rho=\min\left\{\frac\varepsilon{128mR},\sqrt{\frac{\mu\varepsilon}{32m}}\right\}.
\]

This controls both envelope-gradient error and proximal value error. The solver proof handles constrained minimizers through the normal cone; it never assumes their gradient vanishes. The expected squared residual is bounded by 16L²R²(3/4)^(512ℓ), uniformly over every feasible center, even with arbitrary affine slopes.

The outer algorithm maintains gradient cuts of a nested convex body. A selector movement bound and gradient-only bisection produce a phase with at most 10m successful trials. Empty cuts yield convex-combination weights obtained from compact convex separation; this returned point requires no function values. A descent-energy sum and Hölder counting contradict a nonempty body after the full phase. The proof does not assume that the constrained minimizer remains in every cut body. There are ℓ halving phases, and bisection uses at most 64ℓ+2 proximal requests per trial.

Fresh rectangular blocks of a finite private tape supply each adaptive solver request. The total request bound is M=ℓ·10m·(64ℓ+2). A failed certificate aborts to a deterministic projected-gradient fallback, computed with n initial calls, whose gap is at most LR²/2. The per-request failure bound is 1/(AM); hence the failure contribution to expected loss is at most ε/2. On successful executions the phase proof gives ε/2. This argument also covers A so small that 1/(AM)>1; the bound is then loose but valid. The [budget proof](../Proofs/FiniteSumNondualBudget.lean), [program proof](../Proofs/FiniteSumNondualPlan.lean), and [probability-law bridge](../Proofs/FiniteSumNondualGuarantee.lean) establish the actual costs and expectation.

## Comparison with primary work

The following distinctions are essential to the novelty claim.

* Loginov et al., [arXiv:2609.32910v1](https://arxiv.org/abs/2609.32910v1), September 2026, is an unreviewed preprint. Appendix E.4, Proposition E.8 supplies the gradient-only proximal deep-cut architecture, and Appendix D.5 contains hidden-support lower constructions. Neither the selector architecture, the gradient-only separation output, nor support hiding by itself is claimed here as new. The finite-sum component model and its n-dependent minimax classification are the extension at issue.
* Martínez-Rubio et al., [arXiv:2609.21880v1](https://arxiv.org/abs/2609.21880v1), September 2026, is an unreviewed preprint on nondual cubic acceleration. Applying a full-gradient nondual guarantee to the mean costs roughly nA^(1/3), up to its logarithmic factors. The proposed classification improves the n-dependence by a factor n^(1/3) in the nontrivial high-accuracy regime, before logarithmic overheads.
* Martínez-Rubio and Guzmán, [arXiv:2609.20701v1](https://arxiv.org/abs/2609.20701v1), September 2026, give stable movement methods and approximate selectors for nondual Lipschitz convex optimization. This is additional prior art for the outer geometry, not a finite-sum classification. Our exact selector construction makes no polynomial-runtime claim.
* Xiao and Zhang, [SIAM Journal on Optimization 24(4), 2014, Theorem 3.1 and Corollary 3.5](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/96179.pdf), supply ProxSVRG. Substituting μ=L/n and the stated step/epoch length gives contraction 5/8+1/(288n)<3/4. This standard reduction is explicitly used; it is not a new variance-reduction theorem. The formal proof additionally connects the cache, residual test, and every oracle call to execution.
* Woodworth and Srebro, [NeurIPS 2016, arXiv:1605.08003v3](https://arxiv.org/abs/1605.08003v3), April 2019 revision, Appendix C.3, establish randomized finite-sum lower-bound machinery using dead zones and hiding in Euclidean geometry. This is foundational prior machinery. A Euclidean embedding into an ℓ₁ ball loses radius with the hard-chain dimension, so the Euclidean √(nA) claim cannot simply be transferred unchanged to this domain. The present lower proof reconstructs the needed ℓ₁ hiding and serial component exposure explicitly.
* Han, Xie, and Zhang, [JMLR 25(2), 2024](https://www.jmlr.org/papers/v25/21-0264.html), §3, Definition 11, use linear-span and fixed-sampling restrictions. Such a restricted algorithm model is insufficient for the unrestricted classification here.
* Zhou, [arXiv:2610.04944v1](https://arxiv.org/abs/2610.04944v1), October 2026, Appendix C, Lemma 2 and §5.2, already uses serial hidden component owners and adaptive search delay. It is a preprint concerning a nonconvex–strongly-concave, zero-respecting model, and explicitly leaves unrestricted lifting separate. The serial-search lemma alone is therefore not a novelty claim here. The relevant distinction is the globally convex finite-sum ℓ₁ problem and the unrestricted transcript coupling.

Ordinary accelerated variance reduction applied with the Euclidean radius bound gives O(n+√(nA)), modulo the relevant standard logarithmic factors. The polynomial crossover is A≈n. With this theorem's ℓ⁴ overhead retained, an asymptotic improvement over n+√(nA) requires A/n to dominate ℓ²⁴, as well as the fixed constants. Relative to nA^(1/3), a sufficient comparison ignoring that baseline's own logarithms requires n to dominate ℓ¹² and A large enough that the additive n term is negligible. The theorem does not claim universal superiority near the crossover, in small dimension, or with its deliberately conservative constants.

The two agents independently surveyed the two latest publicly available ICML, ICLR, and NeurIPS editions and approximately the preceding two years of arXiv work, then followed older primary references. Searches also checked Peng's [arXiv:2609.00045v3](https://arxiv.org/abs/2609.00045v3) and Wu's [arXiv:2610.16991v2](https://arxiv.org/abs/2610.16991v2); their unrestricted nonconvex-component constructions do not establish the globally convex claim above. Preprint status is not conference acceptance. The claim depends on the precise comparison above, not on absence from a search result or novelty of a Lean formalization.

## Natural instances and limitations

Sparse constrained empirical risk minimization is a standard instance: components log cosh(aᵢᵀx−bᵢ)+cᵢᵀx with ‖aᵢ‖₂²≤L are globally convex and Euclidean L-smooth. Nonparallel dense feature vectors give nonlinear interacting coordinates in arbitrary finite dimension. The ℓ₁ constraint encodes a sparse coefficient budget; the linear terms illustrate why gradient-magnitude bounds would be an unwarranted strengthening. These examples motivate the setup independently of the lower-bound chain.

The upper algorithm is an oracle-complexity construction with exact projections, selectors, body-emptiness decisions, and separation weights. No polynomial arithmetic implementation is asserted. The guarantee is expected objective accuracy, not a high-probability or last-SVRG-iterate guarantee. The output is the outer cut-combination point, or the certified fallback on failure. Lower-bound dimension grows with T and k. Logarithmic optimality and improvements to the explicit constants remain unresolved. The individual upper ingredients, dead-zone construction, and component-search principle are known; significance rests on the complete matched finite-sum classification under the stated unrestricted feasible-query model.
