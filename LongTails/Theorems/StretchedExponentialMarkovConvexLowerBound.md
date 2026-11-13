# Tight complexity under stretched-exponential average Markov mixing

The [lower theorem](StretchedExponentialMarkovConvexLowerBound.lean) and [upper theorem](StretchedExponentialMarkovConvexUpperBound.lean) characterize expected-error oracle complexity, in a noise-dominated regime, as

\[
\Theta_{\alpha,\gamma}\!\left[\tau(\sigma R/\varepsilon)^{\alpha/(\alpha-1)}
\{\log((\sigma R/\varepsilon)^{\alpha/(\alpha-1)})\}^{1/\gamma}\right].
\]

The new contribution is the all-algorithm lower bound. The upper bound follows from the existing accelerated Markov theorem through a proved inclusion and exact parameter substitution. The pair concerns one problem and the same expected objective-gap criterion; it does not claim a new accelerated method or a uniform improvement over algorithms for stronger oracle models.

## Problem and oracle

The [setup](../Setups/StretchedExponentialMarkovConvex.lean) specifies arbitrary finite-dimensional Euclidean spaces, convex globally L-smooth objectives, and a minimizer within distance R of the public initial point x₀. The Markov state space is real Borel space; the problem class is not restricted to finite-state or quadratic instances. The jointly measurable gradient oracle satisfies, for every query x,

\[
\int g(x,z)\,d\pi(z)=\nabla f(x),\qquad
\int\|g(x,z)-\nabla f(x)\|^\alpha\,d\pi(z)\le\sigma^\alpha,
\quad 1<\alpha\le2.
\]

The samples form the actual stationary trajectory of a kernel κ with invariant probability π. The dependence assumption is stationary-average total-variation mixing:

\[
\int\sup_{A\text{ measurable}}|\kappa^t(z,A)-\pi(A)|\,d\pi(z)
\le \exp[-(t/\tau)^\gamma],\qquad t\in\mathbb N,\quad0<\gamma\le1.
\]

Unbiasedness and the moment condition are stationary marginal conditions, not conditional-on-history guarantees. Mixing is averaged, not uniform over starting states. The algorithm receives gradient replies, not latent states, transitions, a reset interface, or objective values. Every consumed transition costs an oracle call, including calls used only for spacing. All adaptive randomized algorithms in the framework are allowed. Success requires measurable output, integrable objective gap, and expected gap at most ε relative to a minimizer; the lower bound does not merely establish fixed-probability failure.

Write z=σR/ε, k=α/(α−1), S=zᵏ and T=LR²/ε. Valid parameters have positive dimension, L,R,σ,ε>0, τ≥1, 0<γ≤1, 1<α≤2, and

\[
4\le T\le S,\qquad z\ge32.
\]

These restrictions isolate a nonempty small-error, noise-dominated regime, rather than restricting the optimization method. The formal witness has dimension one, L=R=σ=τ=γ=1, α=2, ε=1/1024. No tight claim is made outside this regime or uniformly as α approaches one or γ approaches zero.

The assumptions follow the repository's [heavy-tailed Markov setup](../Setups/HeavyTailedMarkovSmoothAndConvex.lean), replacing polynomial average mixing with the established stretched-exponential envelope. Stationary moment/mixing formulations appear in Sarkar et al. and the CVaR preprint discussed below; the latter's Assumption 2.2 explicitly uses stretched-exponential β-mixing. The setup does not combine conditional unbiasedness with dependence. The constants 4 and 32 are technical parameter restrictions; the structural noise-dominated regime is needed for the stated matching comparison. τ≥1 fixes the discrete-time scale.

Natural nonlinear instances include scaled sums of a convex quadratic and terms log cosh(aⱼᵀx), with nonorthogonal aⱼ and coefficients chosen so the Hessian norm is at most L. Translate their minimizer near x₀ and add stationary mean-zero Markov noise of bounded α-moment. They satisfy the same model in arbitrary finite dimension, with interacting coordinates. The hard instances below are quadratics because the obstruction is information in the oracle, not nonlinear geometry. The upper theorem covers the entire nonlinear class.

## Lower bound and hard instance

For every valid parameter choice, every allowed algorithm, and every componentwise budget b≤B, the theorem constructs an admissible instance and oracle failing success, where

\[
B=\left\lfloor {\tau\over32}
\left({\sigma R\over8\varepsilon}\right)^k
\left({\alpha\log(\sigma R/(8\varepsilon))\over2(\alpha-1)}\right)^{1/\gamma}
\right\rfloor.
\]

This includes b=0 and b=B. The sign of the hard instance can depend on the algorithm but never its realized seed. If an output is measurable and integrable, failure is expected gap strictly larger than ε; other outputs fail the same specification's measurability or integrability requirements.

Set q=(8ε/(σR))ᵏ≤1/16, C=τ(log(1/q)/2)^{1/γ}, H=⌊C⌋ and p=q/[H(1−q)]. The [countdown kernel](../Proofs/CountdownMarkov.lean) has common state zero. From zero it jumps to H with probability p; a positive integer state decrements deterministically. Its stationary probabilities are 1−q at zero and q/H at each integer 1,…,H. The kernel is defined on all real states, while this invariant measure has finite support.

The [mixing proof](../Proofs/CountdownMixing.lean) represents actual kernel powers by a positive averaging operator. A block of H no-jump transitions coalesces every supported state at zero. Its common mass is at least (1−p)ᴴ, so the range of any bounded test function contracts by at most Hp per block. Weighting by stationarity preserves the small initial rare-state factor:

\[
\text{average-TV}(t)\le 2q(Hp)^{\lfloor t/H\rfloor}
\le(2Hp)^{\lfloor t/H\rfloor+1}.
\]

The [calibration](../Proofs/CountdownCalibration.lean) proves 2Hp≤√q≤exp[−(H/τ)^γ]. Supermultiplicativity of the stretched-exponential profile then proves the required envelope at every integer time, not just at multiples of H. The [trajectory proof](../Proofs/CountdownPath.lean) gives

\[
\Pr(Z_0=\cdots=Z_n=0)\ge1-q-nq/H\ge7/8
\quad\text{for }n\le\lfloor C/(32q)\rfloor.
\]

Choose a displacement c of norm R and μ=4ε/R². The [objectives and replies](../Proofs/CountdownHardInstance.lean) are

\[
f_\pm(x)={\mu\over2}\|x-x_0\mp c\|^2,\qquad
g_\pm(x,z)=\mu(x-x_0)\mp\mathbf1_{z\ne0}{\mu c\over q}.
\]

They are L-smooth, have admissible minimizers, and have the correct stationary mean. The centered α-moment is bounded by

\[
2q^{1-\alpha}(\mu R)^\alpha
=2^{1-\alpha}\sigma^\alpha\le\sigma^\alpha.
\]

On the common-state event, both oracles give the same reply at every possible query. The [execution proof](../Proofs/CountdownTesting.lean) establishes identical outputs for every seed and adaptive query history. At a common output, f₊+f₋≥μR²=4ε. Integrating over the shared trajectory and independent algorithm seed yields summed risks at least 7ε/2, so both instances cannot have risk at most ε. The [model proof](../Proofs/StretchedExponentialLowerModel.lean) chooses a failing sign only after this integration and handles every smaller budget. The displayed budget is proved exactly equal to ⌊C/(32q)⌋ in [parameter algebra](../Proofs/StretchedExponentialLowerParameters.lean).

## Matching upper and constants

The [upper note](StretchedExponentialMarkovConvexUpperBound.md) specifies the inherited clipped accelerated algorithm, its returned output, all tuning, and exact call count. Let A=256ᵏ and D=256+64A. Its budget U satisfies

\[
U\le (A+2)\left[e\left({1+\log D\over\gamma}\right)^{1/\gamma}+1\right]
\tau S(\log S)^{1/\gamma}.
\]

Indeed S≥1024, so √(32T)≤S, the first ceiling is at most (A+2)S, and W=256T+64AS≤DS implies log W≤(1+log D)log S. The second ceiling adds at most one, absorbed because τ(log S)^{1/γ}≥1.

The real expression inside the lower floor is at least

\[
{\tau S(\log S)^{1/\gamma}\over32\,8^k\,5^{1/\gamma}},
\]

because z≥32 implies log(z/8)≥(2/5)log z. The lower floor can be zero at boundary parameters. Thus the matching statement compares necessary successful complexity **B+1**, which is strictly larger than the real expression inside the floor, with U; it does not assert a bounded ratio U/B. Both constants depend only on fixed α,γ, and neither rate has a dimension factor. The construction is valid in every positive finite dimension.

## Prior work and distinction from PR #162

* [PR #162](https://github.com/k3nfalt/longtails/pull/162) proves the polynomial-average-mixing lower bound τS^{1+1/β} using sticky refresh. This result is not repeated here. Its explicit real budget has a 1/β factor. Even substituting τpoly=τ(β/γ)^{1/γ} and β proportional to log S yields only order τS(log S)^{1/γ−1}; moreover, class inclusion transfers upper bounds, not hardness. A fixed sticky-refresh chain has average-TV proportional to q exp(−λt). Fitting the stretched envelope requires λτ of order at least (log(1/q))^{1−1/γ}; at γ=1 it requires λτ≥1. Hence that mechanism lacks the extra logarithm. Finite countdown excursions provide rare residence H of order τ(log(1/q))^{1/γ} while preserving rapid contraction after each excursion. General first-exit, identical-execution, integration and rare-moment algebra from #162 are reused and credited; they are not the claimed novelty.
* [Sarkar, Chakrabartty and Aggarwal, arXiv:2606.26316v1](https://arxiv.org/html/2606.26316v1), Theorem 4 and Appendix H.4, use sticky-state two-instance hardness with a stationary moment assumption and prescribed uniform geometric mixing for PL optimization. This is precedent for the testing mechanism. Uniform mixing is stronger than the averaged model here; its lower-bound calibration does not establish the countdown logarithm.
* [Adamczak, arXiv:0709.3110v2](https://arxiv.org/pdf/0709.3110v2), Section 3.3 of the published EJP paper, uses deterministic excursions to show logarithms can be necessary in Bernstein bounds for empirical sums of geometrically ergodic chains. The countdown idea and logarithmic phenomenon are established. That result concerns empirical sums and regenerative variance; it is not this finite-budget lower bound against every adaptive optimizer under a stationary α-moment. No claim is made to have invented excursions or first discovered a mixing logarithm.
* [On Generalization and Robustness in CVaR, arXiv:2602.18053v1](https://arxiv.org/html/2602.18053v1), Assumption 2.2, Theorem 3.4 and Appendix B.5, claims a related logarithmic heavy-tail minimax rate under stretched-exponential β-mixing. This is a close prior claim, not omitted evidence. The inspected lower proof discards gaps and treats retained blocks as individual iid observations without constructing a fixed-constant stationary process that makes the full observed sample no more informative. Discarding observations does not establish a lower bound for estimators seeing all observations; even under IID data, a block with a observations retains a times the one-sample KL information. Its displayed exponent also does not resolve the γ-dependent factor proved here. This identifies a gap in the inspected argument, not a counterexample to the paper's theorem. The present claim is the fully constructed adaptive optimization result with precise γ dependence, not an unrestricted priority claim for a log-n mean-estimation bound.
* [Banerjee and Alquier, arXiv:2610.30119v1](https://arxiv.org/html/2610.30119v1), Sections 6 and 8, analyze regenerative processes, with bounded losses, observed iid cycles, a regeneration start and additional cycle moments in the compared minimax result. Those assumptions and information differ from the stationary, latent-state, heavy-tail oracle here.

The closest upper baseline is the repository's [AcceleratedHeavyTailedMarkovConvex](AcceleratedHeavyTailedMarkovConvex.lean); its substitution already gives the matching upper rate. Batching, clipping and spacing therefore account for the upper completely. They do not remove the lower-bound excursion event, which is proved against all permitted algorithms. The contribution is a sharp necessity result, not a new upper algorithm or an artificially restricted method analysis.

The independent surveys covered the publicly available 2025–2026 ICML, ICLR and NeurIPS editions, approximately two years of arXiv submissions/revisions, and older sources reached through citations, as of 13 November 2026 UTC. The numbered arXiv sources above were checked at the stated versions and are treated as preprints, not as accepted conference papers. An earlier classical Rio source was not fully accessible; no novelty conclusion relies on having checked its unavailable proof. The close CVaR claim remains an explicit priority caveat. Final significance rests on the exact oracle theorem, stronger γ-dependent lower bound and matching model, not the Lean implementation alone.
