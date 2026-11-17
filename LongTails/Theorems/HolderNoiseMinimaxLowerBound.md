# Lower bound for spatially Hölder stochastic gradient noise

The [main theorem](HolderNoiseMinimaxLowerBound.lean) proves `NonConvergence spec budget` for the [Hölder-noise setup](../Setups/HolderNoiseNonconvexLower.lean). Together with the [upper theorem and its comparison note](HolderNoiseMinimaxUpper.md), it gives one coherent minimax characterization of a fractional-regularity refinement of smooth stochastic nonconvex optimization. The novelty claim concerns the complete fractional phase, especially the upper bound below one-half; the lower-bound machinery is an adaptation of established techniques.

## Exact scope and guarantee

The objective is a general nonlinear L-smooth function on ℝᵈ, bounded below with initial gap at most Δ. Each fresh IID call returns an unbiased gradient pair at any two algorithm-selected points. The variance is bounded by σ² and the centered noise increments have second moment at most M‖x−y‖^{2ν}, where 0<ν≤1. The formal lower setup reuses precisely the upper setup's admissibility and expected-norm accuracy predicates, specializing its sample space to Bool and its domain to finite-dimensional Euclidean space.

There is **no restriction to zero-respecting, linear-span, deterministic, gradient-descent, or bounded-query algorithms**. Public parameters and an arbitrary initial point are known. The hard instance may depend on the algorithm and the chosen budget, but not on its realized random seed. The Boolean sample is an oracle-internal random variable; its realization is not supplied separately to the algorithm.

Let D=LΔ/ε², A=σ²/ε² and

\[
R=\min\left\{{L\Delta\sigma^2\over\varepsilon^4},\;
 {\Delta\over\varepsilon^3}\max\left\{M(L/\varepsilon)^{1-2\nu},\;
 M^{1/(2\nu)}\sigma^{2-1/\nu}\right\}\right\}.
\]

At σ=0, take R=0, consistently with the formal real-power convention and the batching cap.

For every valid parameter choice satisfying

\[
D\ge64,\qquad d\ge\left\lceil2^{30}(1+D)^3(1+A)\right\rceil,
\]

and every allowed algorithm, at **each** integer pair budget

\[
0\le N\le\left\lfloor(D+A+R)/2^{80}\right\rfloor,
\]

there is an admissible instance on which the actual execution is unsuccessful. Success includes measurability and integrability and requires E‖∇f(output)‖≤ε. When these regularity requirements hold, the proof forces the expected norm to exceed ε strictly. The theorem is not merely the negation of an existential convergence guarantee.

The matching upper bound costs at most a squared logarithm more in this common regime and has a separate log-free batching cap. One pair means two fresh-common-sample gradient evaluations at most, so the comparison changes by only a constant if charged per evaluation. The dimension requirement is sufficient, not asserted necessary. The lower bound is not claimed for fixed small dimension or near-trivial accuracy D<64. Its parameter regime is nonempty for every 0<ν≤1, including M=0 or σ=0 by choosing Δ and d sufficiently large. Very small real budgets can round to zero; this is explicitly covered.

## Hard construction and proof

The construction starts with a C¹,¹ nonconvex chain with interacting neighboring coordinates, built from bounded polynomial ramps. A frontier mask hides the **whole frontier edge**, including the previous coordinate's derivative. Hiding just one coordinate would leak the next hidden coordinate through that derivative. The correction has bounded norm and a dimension-independent Lipschitz constant: at each point at most one masked block survives, and comparing the two possible surviving blocks controls its global variation.

A smooth radial projection and a quadratic wall make the construction valid for arbitrarily large queries and arbitrary returned points. The projection derivative is included in both the true gradient and the noise correction. A Bernoulli multiplier B/p−1 on that correction preserves unbiasedness. Its variance and centered increment moments are computed exactly. Boundedness plus Lipschitz continuity of the correction implies its fractional Hölder increment bound by interpolation.

The scaled chain uses an effective smoothness ℓ≤L, objective scale 140800ε²/ℓ, spatial scale 17600ε/ℓ, and Bernoulli probability p=2²⁴/v. With m=ceil(8Np)+1 chain coordinates, an undiscovered terminal coordinate forces gradient norm at least 4ε. The gap fits when Δℓ/ε²≥2²² and N≤(Δℓ/ε²)v/2⁶⁰. The valid dimension guarantees enough unused coordinates to hide the chain from arbitrary queries.

The finite embedding argument counts bad coordinate observations for both queried points **and the output**, at every time. A clipped lookahead simulator reveals at most one additional coordinate when B=1. It has an unconditional prefix property, so it is valid even on paths where an algorithm probes large hidden coordinates. On good paths it agrees with the real oracle. Averaging over the finite embeddings yields a pointwise gradient-norm lower bound proportional to one minus the number of Bernoulli revelations divided by m. Integrating this inequality under the common algorithm-seed and IID-coin law gives E[number of revelations]=Np. At least one embedding then fails. The chosen embedding is fixed before the algorithm seed is realized. No measurability assumption on bad-query events is silently added; the proof integrates actual output-gradient norms under the success hypothesis.

The parameter optimization is explicit. Set U=M(ε/L)^{2ν}/ε² and α=1/(2ν). Then

\[
R=D\min\{A,\max\{U,U^\alpha A^{1-\alpha}\}\}.
\]

For ν≤1/2 take ℓ=L and v=min(A,U). For ν>1/2, take ℓ=L and v=A when U≥A; otherwise take ℓ=L(U/A)^α and v=A. The latter branch uses positive A,U. In all cases the optimized chain cost is D(ℓ/L)v=R. If chain length or noise strength is too small for this construction, R is already absorbed by an initialization or deterministic term. The proof does not impose an artificial high-noise regime to discard those cases.

A deterministic chain supplies the D term. A pair of translated quadratics with spatially constant noise supplies the A term and the zero-query case, including M=0. At σ=0 the deterministic oracle is used. These alternatives, proved under the same public setup, yield failure at every componentwise budget below the displayed floor. Constants are intentionally loose but universal in ν, including as ν tends to zero.

Principal proof modules are [chain profiles](../Proofs/FrontierChainProfiles.lean), [chain geometry](../Proofs/FrontierChainGeometry.lean), [masked noise](../Proofs/FrontierChainNoise.lean), [radial projection](../Proofs/SoftRadialProjection.lean), [wall separation](../Proofs/FrontierChainWall.lean), [oracle simulation](../Proofs/FrontierChainSimulation.lean), [finite embedding bound](../Proofs/HolderNoiseHiding.lean), [hard-instance admissibility](../Proofs/HolderNoiseHardAdmissible.lean), [execution connection](../Proofs/HolderNoiseHardExecution.lean), [integrated failure](../Proofs/HolderNoiseHardLower.lean), [phase optimization](../Proofs/HolderNoisePhase.lean), and [final case reduction](../Proofs/HolderNoiseLowerBound.lean).

## Assumptions, prior work, and limitations

The model is motivated independently of this construction: smooth population objectives can have sample gradients that are only Hölder in mean square, for example fractional residual regression with bounded nonorthogonal features and continuously distributed responses. The upper companion note explains a nonlinear family and its limitations. The lower hard oracle is a general unbiased vector oracle; it is **not claimed to be the gradient of a sampled scalar loss**. Thus the lower bound does not close the narrower conservative-oracle problem. A finite Boolean hard oracle proves hardness for the larger abstract-sample model because that model includes this subclass; it does not restrict the upper theorem to finite samples.

The main antecedent is [Arjevani et al., arXiv:1912.02365v2, 27 February 2022, Theorem 3, §4 and Lemmas 6, 7, 16](https://arxiv.org/abs/1912.02365), published in Mathematical Programming (2023). Probabilistic chains, protection against arbitrary queries, and smoothness/variance interpolation are established techniques. Our C¹,¹ profiles do not meet the C² premise of their projection lemma verbatim; the projection and wall estimates are proved directly. The fractional parameter optimization and finite-coordinate implementation are not presented as a new general lower-bound method.

[Fradin et al., AISTATS 2026, arXiv:2512.18713v2, Assumption 2.7 and Theorem 4.2](https://proceedings.mlr.press/v300/fradin26a.html), already treats centered similarity and relaxed moments. Its moment exponent is not the spatial exponent ν in this theorem. The ν=1 endpoint is known, and the matching upper in this pair is logarithmically worse than available endpoint methods. The proposed significance is the full fractional class and the previously uncovered rough-noise upper rate, not a stronger endpoint lower bound.

The repository's [PR #18](https://github.com/k3nfalt/longtails/pull/18) contained a lower-bound sketch, but not the unrestricted randomized theorem or the full parameter caps proved here. [PR #23](https://github.com/k3nfalt/longtails/pull/23) already supplied centered analysis, and [PR #25](https://github.com/k3nfalt/longtails/pull/25) supplies the log-free ν=1 upper comparison. Their user-reviewed limitations inform this claim. Reusing their techniques and infrastructure does not itself establish novelty.

The later [PR #185](https://github.com/k3nfalt/longtails/pull/185) proves an all-randomized-algorithm lower bound for pointwise ABC noise under single-point queries. It does not impose spatial Hölder increments or provide paired variance reduction. Its whole-edge masking and finite-prefix counting overlap the implementation paradigm here; neither is claimed as a new technique. Its lower theorem does not automatically restrict to the smaller Hölder-noise class or survive granting the stronger paired oracle.

This result meets the requested upper/lower scope through a common objective, oracle, accuracy scale and explicit matching parameter range. It addresses a natural refinement of a popular optimization setup, not a claim that this exact fractional formulation was a longstanding named open problem. The remaining squared logarithm, dimension requirement, conservative-oracle question, and trivial-accuracy range are genuine limitations. Literature coverage and source-access limitations are recorded in the upper companion note; neither formal compilation nor a search without a duplicate is by itself evidence of conference-level novelty.
