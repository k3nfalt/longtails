# Finite-moment stochastic optimization near nonisolated PL minima

The [theorem](KappaFreeHeavyTailedPLHessian.lean), [setup](../Setups/HeavyTailedPLHessian.lean), and [algorithm](../Algorithms/HeavyTailedPLHessian.lean) concern gradient-only optimization of globally smooth Polyak–Łojasiewicz (PL) objectives with a Lipschitz Hessian. The result removes a fourth-moment requirement from a Hessian-assisted, condition-number-free leading statistical rate. It also covers finite centered p-th moments with 1 < p < 2, including infinite variance. It does not establish a condition-number-free total complexity or an optimal deterministic or curvature transient.

## Setup and guarantee

Work in an arbitrary finite-dimensional real Hilbert space. The objective has an attained minimum f*, an L-Lipschitz gradient, a differentiable gradient with ρ-Lipschitz derivative, and the global PL inequality

    2 μ (f(x) − f*) ≤ ‖∇f(x)‖²,     0 < μ ≤ L.

An initial point satisfies f(x₀) − f* ≤ Δ. The jointly measurable stochastic gradient is unbiased and obeys

    ∫ g(x,ω) dp(ω) = ∇f(x),
    ∫ ‖g(x,ω) − ∇f(x)‖^p dp(ω) ≤ σ^p.

The setup includes the corresponding integrability conditions and an abstract IID stream law. It does not prescribe the stream law as a product measure; the proof derives the required block distribution from independence and the marginal laws. There is no convexity, isolated-minimizer, bounded-domain, symmetry, samplewise-smoothness, interpolation, or fourth-moment assumption. The algorithm knows L, μ, ρ, σ, p, Δ, ε and x₀, but receives neither objective values nor a minimizer.

Write κ = L/μ and q = p/[2(p−1)]. The returned point is a uniformly selected iterate from a final window, and its unconditional expected objective gap is at most ε. Counting every raw gradient call, the bound has order

    O_p((κ^(5/4) + (κ^(5/2) σ²ρ²/μ⁴)^q + (σ²/(με))^q)
        · log(2 + √κ Δ/ε)).

The Lean `budget` is one explicit rounded formula, including the factor 65. Its constants are very large; this is a theoretical guarantee, not a numerical speedup claim. Zero noise, zero curvature, and zero initial gap are included. In particular, no noise-dependent initialization ratio is hidden in the curvature term.

For σ > 0, the statistical term dominates both transients when, up to p-dependent constants,

    ε ≲ min{σ²/(μ κ^(5/(4q))), μ³/(κ^(5/2)ρ²)}.

The second condition is omitted at ρ = 0. This is a dominance regime, not a universal comparison against every competing algorithm. At σ = 0, the deterministic κ^(5/4) bound is worse than ordinary GD's κ dependence.

## Algorithm and proof mechanism

Each update queries 65 fresh gradients at its current point. The first 64 form eight groups of eight. A sum-distance medoid is computed within each group, and a second medoid combines these eight representatives. The last gradient is clipped around that pilot. The update subtracts η times the clipped estimate. No loss oracle, paired evaluation at a previous point, or access to the noise realization is used.

Here are the explicit proof parameters, with C = 2^64, s = √κ, and a = s^5:

    t = [36864 ρ²/μ³ + 1/(a ε)]^−1,
    ν = [2^17/ε + 3200 a/t]^−1,
    h = [8 s^(5/2) + (C^(2/p) σ²/(μν))^q]^−1,
    η = h/μ,     τ = σ(C/h)^(1/p),
    n = ceil[(64/h) log(1 + 48 s Δ/ε)],
    m = ceil(8/h).

The output is x_(n+J), with J uniform on {0,…,m}, independent of the stream. The actual oracle program freezes updates after the selected iterate; its full prescribed execution still counts every later query. At most n+m batches are needed before padding to the explicit budget. Each batch costs 65 calls, including the pilot samples.

The nested medoid and clipping construction is reused robust-estimation machinery, not a new estimator. For σ > 0, its integrated moment bounds give estimator error e with

    ‖E e‖ ≤ B = C σ^p τ^(1−p),
    E‖e‖² ≤ V = C σ^p τ^(2−p),
    E‖e‖⁴ ≤ Q = C σ^p τ^(4−p).

When σ = 0, the raw oracle and processed estimator equal the gradient almost surely; set B = V = Q = 0. This handles τ = 0 without interpreting its negative powers in ordinary real arithmetic. Lean uses its totalized real-power convention and proves this case separately.

Clipping creates bias. Generic biased-PL descent would retain κ in the statistical term. The proof instead controls this bias inside a global potential combining squared distance to the entire minimizer set with a smoothed objective-gap term. With λ = 32√κ/μ, its one-step bound is

    E W(x⁺) ≤ (1 − μη/64) W(x) − η(f(x)−f*)/2 + 290η²V.

The parameter balance gives B² = μηV and μη²Q = ηV². The threshold t and noise level ν control the local aiming region and the fourth moment of the *processed* oracle. This does not assume a fourth moment of the raw oracle. The proof uses a nearest minimizer pointwise to bound distance; it requires no measurable nearest-minimizer selection. The initial potential is bounded by 48√κΔ/μ uniformly in t. Burn-in and window telescoping then yield the stated expectation bound without conditioning on remaining in a local neighborhood.

## What changes relative to prior work

The closest same-geometry comparison is the repository's existing [KappaFreeSgdPLHessian](KappaFreeSgdPLHessian.md), which already proves the Hessian-assisted statistical scaling for plain SGD with variance σ² and fourth moment Kσ⁴. Its rate is

    O((κ^(5/4) + Kκ^(3/2)σ²ρ²/μ⁴ + σ²/(με)) log(2+√κΔ/ε)).

The new contribution is uniformity without K, and extension to finite p-th moments. At p = 2 the curvature term changes from Kκ^(3/2) to κ^(5/2), ignoring constants. Thus the old guarantee can be preferable for small known K; this is not uniform dominance on the common class. The present setup allows all algorithms and makes an attainable problem-class guarantee, rather than claiming novelty from restricting an update family.

For broader smooth PL classes, [Masiha–Kiyavash–Thiran, arXiv2606.28278v3, Theorem4.3 and Remark4.6](https://arxiv.org/html/2606.28278v3) establish a κ-dependent bounded-variance lower bound without the Hessian regularity conclusion. [Ou–Wang, arXiv2609.03990v2, Theorems3.1 and4.3](https://arxiv.org/pdf/2609.03990v2) give finite-p results and lower bounds in the broader smooth PL setting. Writing S = (σ²/(με))^q, Theorem4.3 has a bound of roughly κ[log(Δ/ε)+S] times confidence logarithms; Theorem3.1 gives an expected-gap lower bound of order κlog(Δ/ε)+κS in sufficiently large dimension. Their upper bound is a high-probability last-iterate guarantee, whereas ours is an unconditional expected gap of a random window iterate. Their dimension-dependent refinements also preclude a claim of being the first κ-free noise guarantee in every dimension. Both cited 2026 works are preprints; Ou–Wang explicitly says under review. Neither broader-class lower bound is asserted here for uniformly fixed ρ.

The standard reduction through [Demidovich et al., NeurIPS2023, Theorem4, equation22](https://papers.nips.cc/paper_files/paper/2023/file/484d254ff80e99d543159440a06db0de-Paper-Conference.pdf) retains a floor of order κηV+B²/μ after robust-estimator substitution. It does not yield the displayed potential contraction. Local aiming geometry is established in [Liu et al., arXiv2306.02601v1, Theorem2.2](https://arxiv.org/html/2306.02601v1); its stochastic analysis uses interpolation and samplewise smoothness, which are absent here.

Local nonisolated-minimum results are also relevant. [Fehrman–Gess–Jentzen, JMLR2020, Corollary6](https://www.jmlr.org/papers/volume21/19-636/19-636.pdf) use repeated initialization and stochastic loss selection. [Ko–Li, arXiv2203.10973v2, Theorems3.3–3.4](https://arxiv.org/html/2203.10973v2) give survival-weighted bounds with an escape term. [Dereich–Kassing, Theorem2.6](https://arxiv.org/pdf/1912.09187) give a stable CLT on the convergence event. These are not direct unconditional, gradient-only finite-budget substitutes. Ko–Li's 2023 publication and Dereich–Kassing's EJP2023 publication were confirmed, but the exact comparisons use their accessible arXiv texts because final publisher full text was inaccessible. The [Gadat–Panloup revised manuscript dated February8,2022, Theorem2](https://www.tse-fr.eu/sites/default/files/TSE/documents/doc/wp/2017/wp_tse_856.pdf) assumes a unique critical point, invertible minimizer Hessian, covariance regularity and stronger moments; it excludes the curved nonisolated examples below.

No published black-box localization composition yielding this guarantee was identified in the checked sources. This is not an impossibility claim: a new stopped-process analysis might provide a different proof. Restart selection and aggregation across a curved minimizer set require justification and cannot be treated as free operations.

## Nonlinear scope and limitations

A concrete nonconvex family is

    r(x,y) = y − a sin(x) χ(y),
    f(x,y,z) = r(x,y)²/2 + ‖z‖²/2,

where χ is smooth, equals one on [−1,1], vanishes outside [−2,2], and 0 < a ≤ min{1/2,1/(2‖χ′‖∞)}. Since ∂yr ≥ 1/2, this family is globally PL with μ = 1/4. Its minimizers form the curved unbounded graph y = a sin(x), z = 0. The cutoff bounds all nonquadratic derivatives, giving global gradient and Hessian Lipschitz constants. Appending arbitrarily many z coordinates and applying a dense orthogonal change of coordinates preserves these properties. Thus the theorem is not restricted to quadratics, scalar problems, separable objectives or isolated minima. This family illustrates nonlinear least-squares geometry; it is not itself evidence of research significance.

Additive centered Pareto noise with tail exponent between p and2 gives finite p-th moment and infinite variance when p < 2. At p = 2, a tail exponent3 gives finite variance and infinite fourth moment. Truncations of the latter have uniformly bounded variance but diverging fourth moments, so a guarantee involving K is not uniform on this family. Symmetry is convenient for this example and is not a theorem assumption.

A standard two-point mean-estimation reduction on scalar quadratics gives a lower bound of order (σ²/(με))^q. Set x₀ = 0. For N calls, let θ=1/(2N), A=σ/(2θ)^(1/p), and Y take ±A with probability θ and zero otherwise, using a fixed sign for each of two instances. With mean m, use f(x)=μ(x−m/μ)²/2 and gradient reply μx−Y. The centered p-th moment is at most σ^p. On the all-zero sample event, of probability at least1/2, the two adaptive transcripts coincide. Their worst expected objective gap is at least σ²N^(−2(p−1)/p)/(16μ). The hard pair may depend on N; for a fixed positive Δ it fits the initialization bound for sufficiently large N. This establishes only the statistical exponent and is not a new lower bound or a full optimality claim.

Global PL, global smoothness and global Hessian regularity remain substantial restrictions. The constants, 65-call estimator overhead, curvature transient and logarithmic factor are not optimized. The theorem gives neither a high-probability bound nor a last-iterate guarantee. Its substantive claim is the uniform finite-moment expected guarantee under this established geometry, not the novelty of Lean formalization, the estimator, or the local aiming lemma.
