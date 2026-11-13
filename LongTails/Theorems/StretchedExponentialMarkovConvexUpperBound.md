# Matching upper bound for stretched-exponential Markov gradients

The [theorem](StretchedExponentialMarkovConvexUpperBound.lean) proves convergence for the same [setup](../Setups/StretchedExponentialMarkovConvex.lean) as the [paired lower bound](StretchedExponentialMarkovConvexLowerBound.lean). It gives an explicit algorithmic upper bound matching that new lower bound up to constants depending on fixed α and γ. This upper result is a proved specialization of an existing theorem, not a separately novel optimization algorithm or convergence analysis.

## Setup and output

Objectives are convex and L-smooth on arbitrary positive finite-dimensional Euclidean spaces, with a minimizer within R of x₀. The jointly measurable gradient oracle has stationary mean ∇f(x) and stationary centered α-moment at most σᵅ, where 1<α≤2. Its stationary real-state Markov trajectory obeys average total-variation mixing at most exp[−(t/τ)^γ], with τ≥1 and 0<γ≤1. Mixing need not be uniform over starting states, and gradients need not be conditionally unbiased given the history. The algorithm has gradient replies and public parameters, without access to latent states or restarts of the chain. All consumed transitions count as oracle calls.

As in the lower theorem, write z=σR/ε, k=α/(α−1), S=zᵏ, and T=LR²/ε. The specified regime is z≥32 and 4≤T≤S, with L,R,σ,ε>0. These are parameter restrictions, not restrictions to a prescribed algorithm. The setup retains general nonlinear objectives, for example smooth convex sums of log-cosh terms in nonorthogonal directions plus a scaled quadratic, translated near x₀ and driven by admissible additive Markov noise. Dimension appears in the objective space but not the bound.

Success is measurable output with an integrable objective gap and **expected objective gap at most ε** relative to a minimizer. It is not a fixed-success-probability guarantee or a stationarity criterion.

## Algorithm and exact budget

Define

\[
Q=(256\sigma R/\varepsilon)^k,\quad W=256T+64Q,
\quad N=\lceil\sqrt{32T}+Q\rceil,\quad
m=\left\lceil e\tau\left({\log W\over\gamma}\right)^{1/\gamma}\right\rceil.
\]

The inherited [acceleratedMarkov algorithm](../Algorithms/AcceleratedMarkov.lean) uses

\[
D=2L+{\varepsilon N^2\over16R^2},\qquad
C=4LR+{\varepsilon Q\over R}.
\]

At effective iteration j it queries the existing accelerated combination, clips the gradient reply at norm C, takes its weighted update with weight (j+1)/2 and scale D, and projects the auxiliary point into the ball of radius R about x₀. It retains the corresponding accelerated primal point. The spaced wrapper updates only at raw-call indices 0,m,2m,…,(N−1)m. Every intervening reply still consumes a call and advances the chain. It returns the primal point `(clippedRun ... N).2.1` after exactly Nm raw calls; it does not select a best point using unavailable objective values.

The public budget is the single explicit product

\[
U=\left\lceil\sqrt{32LR^2/\varepsilon}+(256\sigma R/\varepsilon)^k\right\rceil
\left\lceil e\tau\left(
{\log[256LR^2/\varepsilon+64(256\sigma R/\varepsilon)^k]\over\gamma}
\right)^{1/\gamma}\right\rceil.
\]

All tuning depends only on public parameters. Both factors are positive in the stated regime. The new theorem transfers the existing existential algorithm construction and its actual `execute` guarantee; it does not assume accuracy is preserved by running an arbitrary algorithm for additional calls.

## Proof and matching characterization

The [inclusion proof](../Proofs/StretchedExponentialMarkovInclusion.lean) proves, for every β>0,

\[
\exp[-(t/\tau)^\gamma]
\le \left(1+{t\over\tau(\beta/\gamma)^{1/\gamma}}\right)^{-\beta}.
\]

It therefore maps this specification into the existing [polynomial heavy-tail Markov specification](../Setups/HeavyTailedMarkovSmoothAndConvex.lean), retaining the objective, oracle, success criterion, and unrestricted algorithm family. The map is an actual `Inclusion` from [Includes.lean](../Includes.lean), with τpoly=τ(β/γ)^{1/γ}.

Choose β=log W>0. The [upper proof](../Proofs/StretchedExponentialUpper.lean) invokes [AcceleratedHeavyTailedMarkovConvex](AcceleratedHeavyTailedMarkovConvex.lean) at these public parameters. The identity W^{1/log W}=e gives exactly the displayed spacing m. Positive ceilings remove the old `max 1` factors, with proof. Thus the displayed U equals the inherited execution budget, including spacing, rather than merely bounding an unexplained iteration count.

Let A=256ᵏ and D₀=256+64A. Since S≥1024 and T≤S, N≤(A+2)S, W≤D₀S and log W≤(1+log D₀)log S. Consequently

\[
U\le(A+2)\left[e\left({1+\log D_0\over\gamma}\right)^{1/\gamma}+1\right]
\tau S(\log S)^{1/\gamma}.
\]

The paired lower theorem rules out every budget through its explicit floor B. Its real pre-floor expression is at least τS(log S)^{1/γ}/(32·8ᵏ·5^{1/γ}). Successful worst-case complexity must therefore be at least B+1, which exceeds that expression. This establishes Θ_{α,γ}(τS(log S)^{1/γ}) on the same instance class, oracle, and expected-error target. The floor B itself can be zero, so the comparison is not a bounded ratio U/B.

## Contribution, prior work and limitations

The novelty belongs to the lower/upper characterization as a whole, specifically the countdown lower construction proving the logarithmic dependence cannot be removed. The upper is already obtainable by clipping, acceleration, spacing and the displayed inclusion. It should not be described as a new state-of-the-art algorithmic improvement over the inherited theorem.

The [lower contribution note](StretchedExponentialMarkovConvexLowerBound.md) gives the complete primary-source comparison and the distinction from [PR #162](https://github.com/k3nfalt/longtails/pull/162). That PR's polynomial sticky-refresh bound does not imply the new stretched-exponential lower bound; the corresponding substitution is short by a factor log S and inclusion does not transfer hardness. Its general testing lemmas are reused. [Adamczak, Section 3.3](https://arxiv.org/pdf/0709.3110v2) supplies precedent for deterministic excursions and logarithmic empirical-sum obstructions. [Sarkar et al., Theorem 4 and Appendix H.4](https://arxiv.org/html/2606.26316v1) supply sticky-state heavy-tail testing precedent under a different uniform-mixing PL model. The close [CVaR preprint, Theorem 3.4 and Appendix B.5](https://arxiv.org/html/2602.18053v1), and the information-reduction issue in its inspected lower argument, are explicitly discussed in the lower note; no unrestricted priority claim for all logarithmic dependent-mean bounds is made.

The pair meets the requested direction through a new all-algorithm lower bound for a standard stronger-mixing specialization of a popular repository setup, a formal inclusion, and matching bounds. It introduces no `allowedAlgorithm` restriction. Tightness is limited to the noise-dominated small-error regime, with constants depending on α,γ; it does not extend automatically to uniform mixing, conditional moment assumptions, confidence guarantees, unknown-parameter tuning, or deterministic-dominated regimes. The general nonlinear objective class is retained throughout. Literature coverage and inaccessible-source qualifications are recorded in the lower note, as of 13 November 2026 UTC.
