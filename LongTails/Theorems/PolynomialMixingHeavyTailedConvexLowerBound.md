# Tight complexity under polynomial average mixing and heavy-tailed noise

The [lower-bound theorem](PolynomialMixingHeavyTailedConvexLowerBound.lean) establishes a finite-budget oracle lower bound for smooth convex stochastic optimization with stationary Markov samples, polynomial **stationary-average** total-variation mixing, and a bounded stationary centered α-moment, 1 < α ≤ 2. Together with the existing [accelerated upper bound](AcceleratedHeavyTailedMarkovConvex.lean), it gives matching parameter exponents in the noise- and mixing-dominated regime below. Constants depend on α and β; the comparison is not uniform as either exponent approaches its boundary.

## Setup and guarantee

The [specification](../Setups/PolynomialMixingHeavyTailedConvex.lean) reuses `HeavyTailedMarkovSmoothAndConvex` without changing its objective class, admissible oracle, success criterion, or allowed algorithms. Objectives are convex and globally L-smooth, with a minimizer within R of the initial point. The ambient space can be any supported nontrivial Hilbert space, including arbitrary finite dimension. The noise space need only contain two distinct measurable singleton witnesses; it is not restricted to a finite space.

The samples follow a stationary Markov trajectory with invariant probability π and kernel κ. The required mixing bound is

\[
\int \sup_{A\text{ measurable}}|\kappa^t(z,A)-\pi(A)|\,d\pi(z)
\le (1+t/\tau)^{-\beta}.
\]

The jointly measurable oracle satisfies, at every query x,

\[
\int g(x,z)\,d\pi(z)=\nabla f(x),\qquad
\int\|g(x,z)-\nabla f(x)\|^\alpha\,d\pi(z)\le\sigma^\alpha.
\]

These are stationary marginal conditions, not conditional unbiasedness or a uniform-in-state mixing condition. The algorithm observes oracle replies, not the underlying samples or a reset interface. Every transition consumed by execution counts as an oracle call, including calls made merely to advance the chain.

Write z = σR/ε, T = LR²/ε, S = z^{α/(α−1)}, and D = 2^{4α−1}. Besides the original validity conditions, the setup requires R, σ > 0 and

\[
16\le T\le S,\qquad D\le z^\alpha,\qquad
\beta(D/z^\alpha)^{1/[\beta(\alpha-1)]}\le\tau.
\]

The regime is nonempty: α = 2, β = 1, R = ε = 1, L = 16, σ = 16, τ = 2 satisfies these inequalities. The formal inclusion `polynomialMixing_inclusion` uses [the repository's inclusion interface](../Includes.lean) to relate this specification to the original setup.

For **every** valid parameter choice, every randomized adaptive oracle algorithm and every componentwise budget b no larger than

\[
B=\left\lfloor\frac{\tau}{\beta}
\left(\frac{(\sigma R/\varepsilon)^\alpha}{2^{4\alpha-1}}\right)^{(\beta+1)/[\beta(\alpha-1)]}\right\rfloor,
\]

there is an admissible objective and oracle for which the returned output fails the expected-gap criterion. This includes b = 0 and b = B. The hard instance is chosen independently of the realized algorithm seed. If the output is measurable and its objective gap integrable, failure means expected gap greater than ε. Nonmeasurable or nonintegrable outputs also fail the existing specification.

## Construction and proof

All hard instances and supporting lemmas are in [PolynomialMixingLowerBound.lean](../Proofs/PolynomialMixingLowerBound.lean). There is no restriction to a prescribed optimization method.

Choose a unit vector v, h = R/4, m = 4ε/R, and the two nonlinear objectives

\[
f_\pm(x)=m\sqrt{(\langle v,x-x_0\rangle\mp R)^2+h^2}.
\]

Their minimizers include x₀ ± Rv. They have gradient norm at most m and smoothness at most m/h ≤ L. The sum of their objective gaps at any common output is at least 6ε. These are nonquadratic ridge instances in arbitrary dimension; coordinates interact when v has multiple nonzero coordinates. The hard family is deliberately simple and does not assert that nonlinear geometry itself creates the information obstruction.

Let p = [2(m/σ)^α]^{1/(α−1)} and r = β(4p)^{1/β}/τ. The stationary law gives a rare atom probability p and a common atom probability 1−p. The chain keeps its current state with probability 1−r and refreshes from the stationary law with probability r. Both oracles return zero at the common atom and ∇f±(x)/p at the rare atom. Their centered moment is at most 2p^{1−α}m^α = σ^α, uniformly in x.

The stationary-average TV distance is bounded by 2p(1−p)(1−r)^t. Calibrating r to p makes this satisfy the prescribed polynomial envelope. The probability that all states through time N are common is at least 1−p−Npr, hence at least 1/2 for N ≤ 1/(4pr). The formal proof uses the actual trajectory law and proves execution equality on this event for every adaptive query rule and every seed. Integrating over the independent algorithm seed and the shared trajectory gives a sum of expected gaps at least 3ε, so both instances cannot succeed. The explicit displayed budget is proved equal, before flooring, to 1/(4pr).

## Matching upper bound and limitations

The existing upper theorem applies directly because admissibility and success are unchanged and the new validity conditions imply the old ones. It constructs the repository's accelerated clipped Markov method, with all skipped transitions counted. Its budget is

\[
\max\{1,\lceil\sqrt{32T}+256^k S\rceil\}
\max\{1,\lceil\tau(256T+64\,256^k S)^{1/\beta}\rceil\},
\qquad k=\alpha/(\alpha-1).
\]

For fixed α, β the upper and lower budgets are therefore

\[
\Theta_{\alpha,\beta}\!\left(\tau S^{1+1/\beta}\right)
=\Theta_{\alpha,\beta}\!\left(
\tau(\sigma R/\varepsilon)^{\alpha(\beta+1)/[\beta(\alpha-1)]}\right)
\]

on the stated regime. For an explicit constant comparison, set c = (2·4^α)^{1/(α−1)}, d = β(4c)^{1/β}, A = 256^k and C = 4β·4^{1/β}c^{1+1/β}. The real lower budget is τS^{1+1/β}/C and is at least 1, so flooring loses at most a factor two. The upper budget is at most (A+2)[(256+64A)^{1/β}+1/d]τS^{1+1/β}. This gives an explicit upper/lower ratio depending only on α and β.

This is restricted-regime tightness, not a characterization of every parameter regime. The condition r ≤ 1 selects the mixing-dominated regime; it is not intrinsically necessary for hardness. Capping r would cover an IID regime but requires retaining the separate IID term. No tight claim is made here for deterministic-dominated complexity, uniformly over α and β, for high-probability accuracy, or for stronger conditional or uniform-mixing oracle models.

## Prior work and precise contribution

The contribution is the sharp finite-budget, all-algorithm oracle lower bound under this polynomial stationary-average mixing model, closing the parameter-exponent gap to the existing upper bound. The rare-state construction, mean-estimation reduction and two-instance argument reuse established ideas.

* [Sarkar, Chakrabartty and Aggarwal, arXiv:2606.26316v1](https://arxiv.org/html/2606.26316v1), Theorem 4 and Appendix H.4, use sticky-state hardness with stationary moments for a PL problem and prescribed uniform geometric mixing. Those assumptions and accuracy scaling differ. The new statement calibrates the refresh rate jointly with the rare mass under the stationary-average polynomial envelope; it does not claim to invent the construction.
* [Lerasle and Oliveira, arXiv:1112.3914](https://arxiv.org/abs/1112.3914), Section 6, Proposition 16, obtain a root-n β-mixing mean guarantee with a fourth moment and weighted mixing summability. Their finite-variance alternative uses stronger φ-mixing assumptions. These do not cover the stationary α-moment model here.
* [Lovas and Tukora, arXiv:2610.15974v1](https://arxiv.org/html/2610.15974v1), Lemma 2.2 and Theorem 2.4, give polynomial α-mixing upper bounds. Their single-mean exponent is min(β,1)(α−1)/(2α), rather than β(α−1)/[α(β+1)], and they do not establish this finite-budget minimax lower bound.
* [Rio, *Inequalities and limit theorems for weakly dependent sequences*](https://cel.hal.science/cel-00867106/file/ILTWDS.pdf), Theorem 9.4 and Corollary 9.3, demonstrate classical mixing–moment interaction and asymptotic CLT failure through regenerative constructions. This is important precedent, not a novelty claim for the interaction itself. The direct HAL PDF was access-blocked during review; indexed theorem text was inspected, leaving a source-access limitation for the full proof.

The literature comparison distinguishes these arXiv preprints from conference acceptance claims. Searches covered the recent ICML, ICLR and NeurIPS editions, recent arXiv work and older dependent-mean references. No identical finite-budget theorem was found in the inspected primary statements; that is not a claim of exhaustive priority certainty. Formal verification supports correctness and faithful quantifiers, rather than substituting for the mathematical novelty assessment.
