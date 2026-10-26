# Variance reduction under relative noise energy without raw moments

The [main theorem](FairRelativeEnergyNonconvex.lean) proves expected gradient-norm accuracy for a smooth, lower-bounded, generally nonlinear objective with a symmetric heavy-tailed gradient oracle. The new result replaces absolute moment control of coupled noise increments by mean-square **relative** increment control. It does not improve the known finite-variance rate under unchanged assumptions, and it is not an optimality claim.

## Problem and information

The [specification](../Setups/RelativeEnergySymmetricNonconvex.lean) takes a complete, second-countable real Hilbert space, hence includes every finite dimension. Write F=∇f and ζ(x,ω)=g(x,ω)−F(x). The objective is differentiable, F is L-Lipschitz, and f(x₀)−f(x)≤Δ for every x. Parameters satisfy L,ε>0 and κ,r,Δ≥0. The jointly measurable oracle obeys, uniformly over x,y,

- ζ(x,·) and −ζ(x,·) have the same distribution;
- P(‖ζ(x,·)‖>r)≤1/64;
- E[(‖ζ(x,·)−ζ(y,·)‖/(r+‖ζ(x,·)‖+‖ζ(y,·)‖))²]≤κ²‖x−y‖².

Division by zero is defined as zero; its numerator is then also zero. The normalized ratio is bounded by one. Neither a raw noise moment nor a raw increment moment is assumed. In particular, an unbiased raw expectation need not exist. Symmetry identifies the intended center without such an expectation. Symmetry is marginal at each point, not symmetry of the entire random field or of paired differences.

The relative-energy assumption is the new modeling condition. It is a momentless analogue of centered mean-square noise similarity, not a claim that ordinary minibatch gradients satisfy it. The central quantile and symmetry are familiar robust-estimation assumptions; the numerical 1/64 is an inessential fixed normalization. Global uniform r and κ, exact symmetry, known tuning parameters, and shared randomness are substantive restrictions. Finite-moment similarity and this class are incomparable: finite moments do not imply symmetry, and this model permits undefined first moments.

The oracle supplies one gradient vector per call. An abstract IID stream with arbitrary joint probability space is duplicated over consecutive pairs: both replies use the same fresh sample. The algorithm fixes both query points before either reply. Pairing is additional access compared with a fresh-sample-only stochastic oracle. The specification states this dependence explicitly; product-block laws are derived internally from IID. Even an unused second reply at a refresh is charged.

## Algorithm, output and bound

The [algorithm](../Algorithms/FairVarianceReduction.lean) uses the classical radial Fair location: for a block a₁,…,aₘ, its location z solves Σᵢ(aᵢ−z)/(R+‖aᵢ−z‖)=0. Existence, uniqueness and measurability are proved. This score is classical, not a new estimator. At refreshes, it averages clipped block locations. Otherwise it averages clipped differences of locations computed from shared blocks at the current and previous points. A normalized step follows. It returns a uniformly selected **pre-update iterate**, independently selected using the algorithm's random seed. No true gradient, ideal truncation event, or population expectation is available to the algorithm.

The [explicit tuning](../Algorithms/FairTuning.lean) uses R=r+ε, η=ε/(64L), T=max{1,⌈512LΔ/ε²⌉}, and q=⌈L/(κε+L/T)⌉. Let A=(R²+LΔ)/ε²≥1. Blocks have size m=4(1+⌈log(2¹²¹A³)/log4⌉). Refresh batches have ⌈2²⁰R²/ε²⌉ blocks; increment batches have 1+⌈2⁴³qκ²R²/L²⌉ blocks. The increment clipping radius is 2²⁹R²/ε; refresh clipping uses G+3R, where G=√(2LΔ)+LTη bounds gradients on the reachable path. When q=1 all iterations refresh, and no increment batch is used.

The public budget is the single explicit formula

**K = ⌈2⁶⁶(1+log A)[A+min{κε,L}R²Δ/ε⁴]⌉.**

The theorem constructs this algorithm through the repository's `execute` and proves measurability, integrability and

**∫ ‖∇f(output)‖ d(algorithm law × oracle law) ≤ ε.**

[Execution](../Proofs/FairExecution.lean) and [budget](../Proofs/FairBudget.lean) proofs count 2m times every used block, including paired refresh calls. Execution freezes after the planned calls, so excess budget does not change the output. The budget includes robust initialization and iteration costs. It does not count arithmetic or solving the Fair root: the implementation specifies the unique exact root noncomputably. Consequently this is an oracle-complexity theorem, not a numerical solver or wall-clock performance guarantee. Constants are conservative and no empirical practicality claim is made.

Ignoring the displayed logarithm and universal constants, the cost is

R²/ε² + LΔ/ε² + min{κε,L}R²Δ/ε⁴.

For κε≪L and a dominant stochastic iteration term, the latter becomes κR²Δ/ε³ instead of the refresh-only LR²Δ/ε⁴. This is a restricted-regime improvement; initialization can dominate. At κ=0 only robust initialization and deterministic-order iteration costs remain. For large κ, the cap recovers refresh-only behavior without a spurious κ-dependent initialization term. With r=0, R=ε retains the iteration cost. There is no dimension factor outside the setup parameters, but r can depend on dimension.

## New mechanism and standard reductions

The technical contribution is preservation of centered spatial noise regularity by a finite-block robust location under only marginal symmetry. On a block with at least three quarters of samples within R of the true center, the centered location has norm at most 3R. Set this centered location to zero on the complementary event **only for analysis**. The resulting measurable ideal noise is bounded and odd, so each marginal mean is zero even when the raw mean is undefined.

For two good blocks using identical samples, [relative root stability](../Proofs/RadialFairStability.lean) bounds their centered-location difference by 2048R times the sample average of the normalized raw increments. Squaring and integrating yields [relative-energy transfer](../Proofs/FairRelativeEnergy.lean): a centered noise increment second moment bounded by a universal constant times R²κ²‖x−y‖² plus an exponentially small failure term. Translation equivariance is essential: L does not enter this stochastic coefficient. Conditional adaptive batching, clipped-observation discrepancies, accumulated bias and martingale variance are then handled separately in the [tracking proof](../Proofs/FairTrackingBounds.lean). The complete [convergence assembly](../Proofs/FairConvergence.lean) derives the guarantee from the raw assumptions.

Batching undefined raw means is insufficient. Marginal robustification alone yields bounded error but supplies no small coupled increments; refreshing every step gives the ε⁻⁴ term above. Clipping raw responses without controlling shifted-center bias does not produce an unbiased gradient field. Robustifying raw paired differences works in a jointly symmetric subclass, but marginal symmetry alone does not make those differences symmetric. Independently re-pairing the endpoints restores symmetry while losing their shared-noise continuity. Thus applying an existing finite-moment variance-reduction theorem with “variance R²” and “similarity κR” is not a valid substitution until the transfer and implementable-observation bias bounds are proved. Normalized descent, periodic tracking, clipping and biased variance reduction themselves are established tools.

## Meaningful nonlinear instances and limitations

A concrete coupled-simulator family is g(x)=∇f(x)+A∇W(x) on ℝᵈ, d≥3. Here W is a centered stationary Gaussian potential with covariance ℓ²exp(−‖x−y‖²/(2ℓ²)), and A is any independent nonnegative finite random amplitude, including distributions with no positive moments. The objective can be any smooth lower-bounded nonlinear function with interacting coordinates, for example a positive quadratic plus bounded cosine terms cos(aⱼ·x) with nonorthogonal aⱼ. The scalar simulator f(x)+AW(x) is symmetric about f(x), making f a median response even when a mean is unavailable.

The scale cancels from the relative ratio upper bound. For V=∇W, its marginal covariance is I and cross-covariance is M=e^(−t²/2)(I−hhᵀ/ℓ²), t=‖h‖/ℓ. Gaussian regression and E‖V‖⁻²=1/(d−2) give

E[‖V(x)−V(y)‖²/‖V(x)‖²] ≤ ‖I−M‖op²+tr(I−M²)/(d−2).

For t≤1 this is at most (45/4)t²; for t≥1 the normalized ratio is at most one. Thus κ=4/ℓ suffices. A uniform finite central quantile r exists without amplitude moments. This infinite-rank field permits cancellation and unbounded random derivative-to-noise ratios; it is not a fixed finite-dimensional distortion canceled by a few queries. The d≥3 restriction belongs to this example's inverse-norm calculation, not the theorem. These illustrative calculations are mathematical motivation; the Lean theorem assumes the oracle inequalities rather than formalizing Gaussian processes.

Gaussian scale mixtures are established models, including [Shah, Wilson and Ghahramani, AISTATS 2014](https://proceedings.mlr.press/v33/shah14.html), Section 3 and Lemma 4. Their Student-process parameterization uses ν>2; the arbitrary-amplitude extension above is our calculation, not their theorem. This example is jointly symmetric and admits simpler robust-difference methods. It motivates the relative-energy condition but does not demonstrate practical necessity of the full marginal-only result. Shared randomness does not in general imply joint symmetry; the full theorem avoids imposing it. No claim is made that generic nonlinear regression or neural-network SGD satisfies these assumptions.

### Why marginal symmetry does not imply symmetric differences

A conservative random-phase field gives a scope diagnostic. Fix a unit vector a, β>0, ρ>0 with c=ρ(1+β)<1, and h(t)=sin t+β sin(2t). Let S be a fair sign, U uniform on [0,2π], and A≥0 independent of both. Set k₊=1, k₋=2 and

ζ(x)=ASa[1+ρh(kₛ⟨a,x⟩+U)].

Uniform phase makes every marginal centrally symmetric even though frequency depends on sign. Its norm lies between A(1−c) and A(1+c); a central quantile of A gives r. Since |h′|≤1+2β, the relative-energy condition holds even pathwise with κ=ρ(1+2β)/(1−c). It is the gradient of AS[⟨a,x⟩+(ρ/kₛ)H(kₛ⟨a,x⟩+U)], where H(t)=−cos t−(β/2)cos(2t), so this is not a nonconservative-vector-field artifact. The objective f can still have arbitrary nonlinear interacting coordinates.

For A=1, let d=⟨a,y−x⟩. Direct phase integration gives E[(h(U+d)−h(U))³]=6βsin²(d/2)sin d. Consequently ⟨a,ζ(y)−ζ(x)⟩ has third moment 3βρ³/2 at d=π/2, and is not symmetric. A sufficiently small mixture of A=1 with an independent amplitude having no positive moments preserves asymmetry: a bounded odd test separating the bounded base increment law from its reflection remains nonzero under sufficiently small contamination. This argument does not take a nonexistent third moment in the heavy-tailed mixture.

This constructed family establishes strict scope beyond symmetric paired increments; it is not evidence of a common practical noise mechanism or a separate contribution. Its scalar sample responses need not be symmetric about f, so the median-response interpretation of the Gaussian example must not be transferred to it. The theorem concerns a nominal objective with centered gradient observations. Neither this diagnostic nor the Gaussian example is required by the formal specification.

## Closest results and literature coverage

- [Fradin et al., arXiv:2512.18713v2, 31 March 2026](https://arxiv.org/abs/2512.18713v2), Assumptions 2.3 and 2.7, Theorem 4.2 and Lemma F.4; accepted [AISTATS 2026 proceedings](https://proceedings.mlr.press/v300/fradin26a.html). Their centered p/q-moment framework and double-clipped algorithm already separate objective smoothness from noise similarity. Our guarantee recovers that useful noise-sensitive structure under a different, symmetric momentless model; it does not introduce that separation or improve their unchanged problem class. Their lower bounds do not automatically transfer to this symmetric class. In the p=q=2 case, writing σ for the raw noise scale and s for centered mean-square similarity, their bound is O[σ²/ε²+(L+s)Δ/ε²+sσΔ/ε³]. The formal substitution σ=R and s=κR gives our uncapped parameter powers because κRΔ/ε²≤κR²Δ/ε³ when R≥ε. That substitution becomes meaningful only after our robust coupling transfer and implementable-observation bounds; the raw oracle need not meet their assumptions. Our theorem pays the explicit logarithmic block factor and caps the coupling term by refresh-only cost.
- [Kornilov et al., arXiv:2402.02461v5, 5 December 2025](https://arxiv.org/abs/2402.02461v5), Assumption 3, Lemma 2 and Appendix B.1, robustify paired function differences under symmetry and polynomial density-envelope assumptions on the differences themselves. The present theorem assumes neither those difference laws nor a polynomial tail envelope, but uses a gradient oracle rather than their function-value oracle. Their evaluation costs cannot be compared as if these oracles were identical.
- [Armacki et al., arXiv:2507.09093v2, 10 February 2026](https://arxiv.org/abs/2507.09093v2) study nonlinear SGD with state-dependent marginal symmetry and positive-density assumptions, with an ε⁻⁴ stationarity complexity. The present shared-randomness and spatial regularity assumptions are additional structure; this is not an improvement under their unchanged oracle model.
- [Puchkin et al., AISTATS 2024](https://proceedings.mlr.press/v238/puchkin24a.html) stabilize structured marginal heavy-tailed noise. Such marginal bias/variance guarantees do not by themselves establish the centered coupled-location transfer proved here. Classical Fair M-location theory likewise supplies the estimator, not this optimization guarantee.
- [Hu, Zhang, Chen and He, *Biased Stochastic First-Order Methods for Conditional Stochastic Optimization and Applications in Meta Learning*, NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/file/1cdf14d1e3699d61d237cf76ce1c2dca-Paper.pdf), Theorem 3.4 (BSpiderBoost), is an established biased variance-reduction baseline. Our contribution is the momentless oracle transformation and its resulting model-specific guarantee, not generic biased tracking.

The independent researcher and reviewer surveys used current UTC date 25 October 2026, covered publicly available ICML/ICLR/NeurIPS 2025 and 2026 material and approximately the preceding two years of arXiv submissions/revisions, then followed older foundational and stronger applicable results. The closest arXiv versions above were rechecked. ArXiv references are not labeled accepted solely because they are posted there. Search coverage supports a novelty judgment, not proof of exhaustive priority.

One material access limitation remains: the official NeurIPS 2026 listing and abstract of *Median-of-Means under Structured Heavy-Tailed Noise* were available, but its [OpenReview full text](https://openreview.net/forum?id=vGEUrQdO7l) returned access errors. Its full theorem and proof comparison could not be verified. The available description concerns structured marginal noise and clipped optimization; it does not settle whether a related spatial transfer appears in the inaccessible text. This uncertainty must remain part of the novelty assessment.

The claimed contribution is therefore a new relative-energy oracle class with a dimension-independent robust coupling transfer and the explicit momentless stationarity guarantee above. It is an assumption-replacement result with meaningful coupling-regime gains, not universal superiority, a new Fair estimator, a general claim about practical training noise, or a matching lower bound.
