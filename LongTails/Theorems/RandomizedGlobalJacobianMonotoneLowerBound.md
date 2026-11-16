# Randomized global Jacobian-oracle lower bound

## Result and model

The [Lean theorem](RandomizedGlobalJacobianMonotoneLowerBound.lean) concerns global root finding for continuously differentiable monotone operators on arbitrary finite-dimensional Euclidean spaces. The [specification](../Setups/GlobalJacobianMonotoneExpected.lean) assumes

- `⟨F(x) − F(y), x − y⟩ ≥ 0` everywhere;
- `‖DF(x) − DF(y)‖ ≤ L ‖x − y‖` everywhere;
- a zero `xstar` with `‖x0 − xstar‖ ≤ R`.

One oracle call returns the exact pair `(F(x), DF(x))`. Queries and outputs may lie anywhere in the space. Algorithms may randomize, adapt to all previous replies, and perform unrestricted computation between calls. There is no span restriction, prescribed update family, or bound on query norms. Success means an integrable residual norm with `E‖F(output)‖ ≤ ε`, under the explicit algorithm/oracle seed measure used by `execute`.

Write `Q = LR²/ε` and `N = floor((Q/4096)^(2/5))`. For `Q ≥ 4096` and `d ≥ 4096(N+2)^5`, the theorem proves failure at every componentwise budget at most `N`: for each algorithm there is an admissible fixed operator for which the stated expected-accuracy condition fails. The operator may depend on the algorithm and budget, but cannot depend on its realized random seed. This is an `Ω(Q^(2/5))` randomized joint-oracle lower bound in the stated high-dimensional regime. The dimension condition is sufficient for the construction; no necessity or low-dimensional optimality is claimed. The valid regime is nonempty: `L=4096`, `R=ε=1`, `x0=0`, and `d=995328=4096·3^5` give `N=1` and satisfy every parameter condition.

## Closest results and the remaining gap

[Jiang and Yoon, *Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems*, arXiv:2609.30212v2, 8 November 2026](https://arxiv.org/abs/2609.30212v2), Theorem 6.1, proves the corresponding global deterministic lower bound. Its negative-wrap chain and flat gates, developed in Lemmas 6.2–6.3, are prior techniques. The present contribution extends the global lower bound to arbitrary randomized adaptive algorithms with unrestricted joint value/Jacobian probes and expected residual accuracy. It does not improve the deterministic exponent or introduce the chain itself. The finite random embedding needs a larger sufficient dimension, polynomial of degree five in the call budget, compared with the deterministic construction's linear dimension.

[*Matching Higher-Order Oracle Complexity for Smooth Monotone Variational Inequalities*, arXiv:2609.13462v2, 19 October 2026](https://arxiv.org/abs/2609.13462v2), Theorem 11.3, gives a randomized higher-order lower bound with queries restricted to a compact feasible domain. Remark 11.4 explicitly excludes arbitrary unbounded probes. Its constrained tangent residual and feasible-query oracle model differ from global root finding. Neither a restriction to a ball nor a change of residual is silently identified with the present model. In particular, an unconstrained algorithm could query outside the compact domain. A generic projection of an operator does not preserve monotonicity, and evaluating a resolvent is not a one-call reduction to the given oracle.

[Jang and Ryu, arXiv:2607.05947v1](https://arxiv.org/abs/2607.05947v1) supplies earlier higher-order fixed-point lower-bound techniques. These chain ideas are reused, rather than claimed as new. The cited versions are arXiv sources; this note does not claim conference acceptance for them.

The global upper bound is already available: Jiang–Yoon Theorem 5.1, specialized to zero set-valued term and Lipschitz Jacobian, and the repository's [LazyAnchoredExtraProximal theorem](LazyAnchoredExtraProximal.lean), [setup](../Setups/UnconstrainedLipschitzJacobianMonotone.lean), and [algorithm](../Algorithms/LazyAnchoredExtraProximal.lean). Set its reuse parameter to `m = 1` and its distance parameter to `D = R`. With `K = ceil(Q^(2/5)) + 1` and `log2 K = Nat.log2 K` (the floor of the base-two logarithm), the existing theorem budgets `K` Jacobian calls and `2^16 K (log2 K + 1)^2` operator calls. Each separate call can be simulated by one joint call, discarding the unused component, so the total joint cost is at most `K + 2^16 K (log2 K + 1)^2`. Its deterministic residual guarantee gives an integrable, bounded residual with expected norm at most ε. No restart or probabilistic output selection is needed.

Consequently the new lower bound and the existing upper bound close this global joint-oracle complexity question up to logarithmic factors in the stated high-dimensional accuracy regime. No new upper-bound theorem is added because that direction is already proved. A sharper compact-domain upper bound must not be imported into the global setting merely from informal prose suggesting an unconstrained extension.

## New mechanism and proof

The hard-instance construction is in [LocalizedMonotoneConstruction](../Proofs/LocalizedMonotoneConstruction.lean), [LocalizedMonotoneRadial](../Proofs/LocalizedMonotoneRadial.lean), and [LocalizedMonotoneInstance](../Proofs/LocalizedMonotoneInstance.lean). Set `m = N+2`, `a = R/(4m√m)`, and `γ = La/4`. The established flat scalar gate is continuously differentiable, is zero together with its derivative on `[-a,a]`, is nondecreasing and 1-Lipschitz, and has derivative Lipschitz constant at most `2/a`. A negative-wrap chain `G` built from these gates is nonexpansive and has an explicit fixed point of norm at most R.

The localization-plus-coercivity argument uses a smooth radial nonexpansive map `P` that equals the identity on the ball of radius `4R`, has image in the ball of radius `6R`, and has globally Lipschitz derivative with constant at most `8/R`. Define the hard field by `F = γ(Id − G∘P)` and translate it by the public initial point. Nonexpansiveness implies monotonicity of this field. The complete derivative calculation gives `Lip(DF) ≤ γ(2/a + 8/R) ≤ L`.

Localization alone could create easy outputs away from the original chain. The essential additional argument is the [global coercivity estimate](../Proofs/LocalizedMonotoneCoercivity.lean). For every radial contraction factor `t∈[0,1]`, the negative-wrap recurrence implies

`‖x‖ ≤ √m c + (2m+1) ‖x − G(tx)‖`,

where the explicit chain offset satisfies `√m c ≤ 3R/2`. Thus a residual below `R/(2m)` forces the output into the identity region of `P`. There the terminal hidden-coordinate obstruction applies. The resulting field residual is at least `LR²/(32m²√m)` whenever the final coordinate remains hidden. The argument treats all coordinates and their nonlinear interaction, rather than only scalar or quadratic instances.

[LocalizedMonotoneJets](../Proofs/LocalizedMonotoneJets.lean) proves equality of the complete joint reply to a prefix simulation when future projected coordinates lie in the flat region. The radial derivative depends on the known query but does not reveal additional hidden axes: it multiplies a chain Jacobian whose future gate derivatives are exactly zero. [LocalizedMonotoneSimulation](../Proofs/LocalizedMonotoneSimulation.lean) proves exact coupling to adaptive execution, including zero calls and arbitrary output rules.

A finite random injection of m coordinate axes replaces continuous random rotations. Every projected query has norm at most `6R`; the raw output is tested only when its norm is small, since coercivity already handles large outputs. The coordinate count is `(6R)²/a² = 576m³`. At most m observations and m hidden axes give a bad-count numerator at most `576m^5`. With denominator `2048m^5` and `d ≥ 4096m^5`, at least half of the embeddings satisfy the required hiding conditions. The [finite averaging proof](../Proofs/LocalizedMonotoneAveraging.lean) is pointwise in the algorithm seed. The [expectation proof](../Proofs/LocalizedMonotoneExpectation.lean) then assumes integrability for each candidate instance and integrates the finite sum. It needs no measurability assumption about auxiliary bad events and selects the hard instance before the seed is realized.

The [budget algebra](../Proofs/LocalizedMonotoneBudget.lean) uses `q=Q/4096≥1` and `m=floor(q^(2/5))+2` to prove `m²√m≤16q`. The residual threshold therefore exceeds twice ε, sufficient for a strict contradiction after half-good averaging. The [execution and admissibility proof](../Proofs/LocalizedMonotoneLowerBound.lean) connects the constructed joint oracle to the frozen `execute` implementation and proves every setup condition.

## Motivation, scope, and limitations

Global smooth monotone equations are an established framework for unconstrained convex optimization, convex–concave saddle problems, and monotone systems; see [Jiang–Mokhtari, Mathematical Programming, 2026](https://doi.org/10.1007/s10107-026-02396-4). The assumptions above are those of the cited global higher-order theory. No additional structural condition is imposed to make the lower bound work. The accuracy and dimension inequalities state the quantitative regime of hardness rather than a restriction on the form of the objective or update rule.

For a nonlinear interacting family within this class, consider the saddle operator of

`f(x,y) = ψ(aᵀ(x−θ)) + Σ_i log cosh(a_iᵀ(x−θ)) + (x−θ)ᵀB(y−ζ) − Σ_j log cosh(c_jᵀ(y−ζ))`,

with `ψ(t)=(1+t²)^(3/2)/3`, dense feature vectors and a dense coupling matrix. Its saddle operator has a zero at `(θ,ζ)`, is monotone, and has globally Lipschitz Jacobian because the scalar third derivatives are bounded. The Jacobian itself need not be bounded: ψ has unbounded second derivative. The Lipschitz-Jacobian parameter depends on the feature norms and scalar third-derivative bounds. Choose the shifts within distance R of the public initial point and rescale the operator by a positive constant to meet any prescribed positive L. This illustrates the breadth of the setup, not a claim that the constructed hard operator is a saddle gradient. The theorem is for general monotone operators and does not establish a lower bound for the saddle-gradient subclass.

The lower and upper bounds have comparable expected norm accuracy and joint-oracle accounting. A fixed-success-probability guarantee is not substituted for expected accuracy. Expected norm at most ε implies success at threshold `3ε` with probability at least two-thirds by Markov's inequality, but the reverse implication is not claimed. The result does not settle low-dimensional complexity, remove logarithms from the upper bound, or give separate optimal value-versus-Jacobian tradeoffs.

The literature screening covered the two most recent publicly available ICML, ICLR and NeurIPS editions and approximately two years of arXiv submissions/revisions, followed by primary-source checks of the cited global and compact-domain results. The novelty comparison rests on their actual query restrictions and theorem quantifiers, not absence of search hits or the Lean formalization. The latest checked versions are the dated versions linked above.
