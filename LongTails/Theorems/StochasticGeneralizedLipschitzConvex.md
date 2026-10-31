# Cubic stochastic localization for generalized-Lipschitz convex optimization

The [main theorem](StochasticGeneralizedLipschitzConvex.lean) constructs a stochastic first-order algorithm for convex objectives with gap-dependent oracle growth. It returns an ε-optimal point with probability at least 9/10 using a fixed, explicit number of oracle calls. Write κ = max{1, RG₁} and b = RG₀/ε. Its complexity is

\[
\widetilde O(\kappa^3+\kappa^2b+b^2).
\]

The contribution is a cubic-cost localization phase under the existing oracle model, followed by a warm-start optimization phase. It is a problem-class oracle-complexity result: the specification does not restrict admissible algorithms to the constructed implementation. It is not a new expected-objective guarantee or an optimality claim.

## Problem and oracle

The [setup](../Setups/StochasticGeneralizedLipschitzConvex.lean) specifies a continuous convex function f, an attained minimizer x⋆, a known initial point x₀ and radius R with ‖x₀−x⋆‖≤R. The parameters satisfy R>0, G₀>0, G₁≥0, ε>0. The algorithm knows these parameters, but does not know x⋆, f(x⋆), function values, true gradient norms, or oracle moments.

The jointly measurable oracle X(x,ω) has an integrable mean that is a subgradient of f at x. For each x there are measurable random vectors u,v with

\[
X(x,\omega)=u(\omega)+v(\omega)\quad\text{a.s.},\qquad
\mathbb E\|u\|^2\le G_0^2,\qquad
\|v\|\le G_1(f(x)-f(x_\star))\quad\text{a.s.}
\]

The decomposition is existential and is not revealed to the algorithm. Neither u nor v is required to be centered. These are the substantive conditions in Assumption 2 of [Kovalev, *Stochastic Non-Smooth Convex Optimization with Unbounded Gradients*, arXiv:2605.15522v2](https://arxiv.org/abs/2605.15522v2). They are stronger than a bound on the oracle's second moment alone; the almost-sure bound on v is essential to the pilot argument. There is no fourth-moment or bounded-support assumption on u. The setup requires IID samples with an abstract probability measure and explicit measurability, independence, and marginal laws; it does not prescribe a product sample space or restrict it to finitely many outcomes.

The intended scope includes arbitrary finite-dimensional nonlinear convex objectives. The Lean proof works in a separable real Hilbert space, with continuity stated explicitly. This extension of ambient space is not the novelty claim. Positive R and G₀ exclude degenerate parameter cases; users may supply positive upper bounds. No smoothness, strong convexity, separability, or quadratic structure is assumed.

A concrete interacting nonlinear family is

\[
f(x)=\frac1n\sum_{i=1}^n\bigl(e^{\|A_i(x-\theta)\|}-1\bigr),\qquad \|A_i\|\le A.
\]

The matrices can be dense with noncommuting Gram matrices. Sample i uniformly and return e^{rᵢ}qᵢ+ζ, where rᵢ=‖Aᵢ(x−θ)‖, qᵢ=AᵢᵀAᵢ(x−θ)/rᵢ when rᵢ>0 and qᵢ=0 otherwise. Independent centered noise with E‖ζ‖²≤σ² is allowed. Taking u=qᵢ+ζ and v=(e^{rᵢ}−1)qᵢ verifies G₀²=A²+σ² and G₁=nA; θ is a minimizer. This illustrates exponential residual growth with interacting coordinates and potentially unbounded noise. It is a coverage example, not a hardness example; the n-dependence can be pessimistic.

## Algorithm, output, and guarantee

The [algorithm module](../Algorithms/GeneralizedLipschitzConvex.lean) defines `tunedAlgorithm`, its two phases, the cap, and `output`. All tuning depends only on public inputs. It uses G=max{G₁,1/R} and κ=RG.

The first phase runs T=⌈204800κ²⌉ iterations in the radius-R ball around x₀, with pilot failure allowance δ=1/(100T). Each iteration uses a raw-sample bracket, capped descending scales, robust scalar second-moment and vector-mean tests, and a fresh independent average for the update. The [pilot module](../Algorithms/GeneralizedLipschitzPilot.lean) specifies every batch and repetition count. It freezes when its stopping certificate fires. All unused scale tests and frozen iterations remain counted. Except with probability 1/50, its returned point has gap at most 128RG₀ and is within distance 2R of x⋆.

The second phase is the [projected weighted adaptive method](../Algorithms/GeneralizedLipschitzWarmStart.lean). With D=2R, e=ε/20, τ=⌈(96DG)²⌉, it uses

\[
\alpha=\min\left\{\frac1{16\tau DG},\left(\frac e{24DG_0}\right)^2,\frac e{1536\tau DG_0}\right\},\qquad
K=\left\lceil\frac2\alpha\log\max\{2,1024DG_0/e\}\right\rceil.
\]

Its output is the stored weighted primal point after K calls, not a retrospectively selected best iterate. Conditional on a certified initialization, its expected gap is at most e, so Markov's inequality bounds failure at ε by 1/20. The [composition proof](../Proofs/GeneralizedLipschitzComposition.lean) derives the prefix/tail product law from the abstract IID assumption and connects these points to actual `execute`. It charges both initialization failure and second-phase failure, obtaining at most 7/100, and hence at most 1/10. No expected-gap bound is asserted on failed initialization paths.

The public budget is the single explicit formula

\[
N=\left\lceil 2^{66}\left((1+RG_1)^3+(1+RG_1)^2\frac{RG_0}{\varepsilon}
 +\left(\frac{RG_0}{\varepsilon}\right)^2\right)
\left(1+\log\left(2+RG_1+\frac{RG_0}{\varepsilon}\right)\right)^3\right\rceil.
\]

The [complexity proof](../Proofs/GeneralizedLipschitzComplexity.lean) proves that N covers the exact first-phase call count plus K. The capped execution pads to N calls without changing the output. The theorem's probability measure includes the algorithm's trivial seed and the explicitly specified IID oracle law. Constants are conservative and very large; no practical efficiency claim follows.

## New mechanism and relation to prior work

The closest baseline is Kovalev v2, Assumption 2 and Corollary 4: expected ε-accuracy in approximately κ⁴+b² calls, with logarithmic factors suppressed. Applying Markov's inequality at a constant rescaling of ε gives the comparable constant-confidence baseline. Theorem 6 and its proof in Appendix G.6 retain an initialization-dependent logarithm; Theorem 7 and equations (29)–(30) retain a κ²b term. An arbitrary radius-bounded start can have exponentially large gap, so dropping that logarithm is not a valid cubic bound.

The new localization removes that initialization penalty at constant confidence without adding structural assumptions. Let g=‖EX‖ and S²=E‖X‖² at the current point. The pilot maintains g≤m and S²≤16κm², and certifies a scale comparable to max{g,S/√κ}, rather than insisting on relative estimation of g. A raw batch of order κ times a logarithm detects a suitable scale despite only a second moment for u. Its upper bracket is polynomial, so only logarithmically many scales are visited.

At each scale, clipping at 256κm permits a robust scalar estimate of the clipped second moment q with error q/4+κm²/64. A variance trigger can accept before the mean is accurately resolved. After scalar rejection, an independent robust vector estimate is accurate enough to test the mean; rejecting both tests preserves the invariant at the next halved scale. Either acceptance certifies G(f(x)−f⋆)/m≥1/16. A fresh unbiased average of order κ samples, with step 1/(128Gm), then gives conditional squared-distance decrease at least 1/(2048G²). A killed-potential argument bounds the probability of exhausting order κ² iterations without a valid stopping certificate. This yields cubic localization cost, including all pilot work.

Ordinary relative-gradient simulation is insufficient: the model permits S/g of order κ, requiring order κ² samples per relative estimate. Composing this with order κ² normalized steps recovers quartic cost. Nor can an unknown RMS be estimated relatively from a fixed number of finite-variance samples without further assumptions. The variance-or-mean scale certificate and independent unbiased update avoid these two obstructions. Scalar median trees, vector medoids, concentration inequalities, the warm-start phase, and Markov conversion are established ingredients, not individually claimed innovations.

Related independent-normalization methods in [Gao and Deng, ICML 2024, arXiv:2401.13971v2](https://arxiv.org/abs/2401.13971v2), particularly the assumptions of Theorems D.3 and D.5 in Appendix D, require different uniform reference-Lipschitz fluctuation controls; they do not give this polynomial guarantee under the stated decomposition. [Bollapragada, Byrd and Nocedal, *Adaptive Sampling Strategies for Stochastic Optimization*, arXiv:1710.11258](https://arxiv.org/abs/1710.11258) analyzes smooth optimization and population norm tests; those tests do not provide the finite-variance pilot certificate here. Grimmer's [*Convergence Rates for Deterministic and Stochastic Subgradient Methods without Lipschitz Continuity*, Theorem 6](https://arxiv.org/abs/1712.04104) uses a second-moment bound linear in objective gap, which does not cover the quadratic-gap growth above with comparable constants. These are mechanism or assumption comparisons, not claims that all adaptive sampling methods are inferior.

Ignoring logarithms, the improvement over the dimension-free quartic baseline is a factor κ when b≤κ and κ²/b when κ<b<κ². There is no asymptotic gain when b≥κ². Dimension-dependent reductions also matter: robust center cuts give localization cost approximately dκ², followed by a warm phase costing κ³+κ²b+b²; direct ε-accuracy cuts give approximately d(κ²+b²). Thus low-dimensional methods can be better. For b≤κ, a conservative regime of improvement over these cuts is d≫κ. For the intermediate regime, d≫max{κ,b} is a sufficient conservative comparison regime. No unproved total bound dκ²+b² is used as a baseline. There is no lower bound establishing optimality of the new rate.

## Search coverage and limits

Researcher and Reviewer independently surveyed the publicly available 2025 and 2026 ICML, ICLR, and NeurIPS material, using official proceedings or OpenReview to check conference status, and searched approximately the preceding two years of arXiv work and revisions. Citation trails led to older normalization, adaptive sampling, nonsmooth stochastic optimization, and cutting-plane results. The most recent focused refresh was 30 October 2026 UTC. Kovalev's arXiv record still listed v2, submitted 26 May 2026; its PDF is dated 27 May. It was listed as a preprint, and conference acceptance was not verified. No checked follow-up, correction, or stronger matching guarantee was found. This is a documented literature comparison, not proof of exhaustive coverage: a Semantic Scholar citation request returned HTTP 429, and the arXiv HTML was unavailable, although the primary PDF and relevant theorem proofs were read.

The remaining limitations are constant confidence, a gain confined to particular parameter and dimension regimes, a substantive almost-sure growth-component assumption, large constants, and limited uptake of this recent model. Formal verification supports correctness and faithful cost accounting; it is not evidence of novelty by itself.
