# Stationarity with mixed relative and smooth stochastic increments

The result concerns smooth lower-bounded nonconvex optimization with a shared-sample stochastic-gradient oracle. It separates relative noise, which vanishes near stationary points, from smooth residual noise in the oracle complexity. The algorithm receives only the combined oracle; a decomposition is a sufficient condition for the assumptions, not information supplied to the algorithm.

The formal objects are the [setup](../Setups/MixedRelativeSmoothNonconvex.lean), [algorithm](../Algorithms/MultiscaleRepresentatives.lean), and [main theorem](MixedRelativeSmoothNonconvex.lean). Supporting proofs are grouped in the `MixedNoise*` modules under `LongTails/Proofs`.

## Problem and oracle

Let f have L-Lipschitz gradient, L>0, and f(x₀)−inf f≤Δ. For an unbiased jointly measurable oracle g(x,ξ), write e(x,ξ)=g(x,ξ)−∇f(x). The assumptions are, for every x,y,

\[
\mathbb E\|e(x,\xi)\|^2\le r\|\nabla f(x)\|^2+\sigma^2,
\qquad
\mathbb E\|e(x,\xi)-e(y,\xi)\|^2
\le r(\|\nabla f(x)\|^2+\|\nabla f(y)\|^2)+M^2\|x-y\|^2.
\]

Here r,M,σ,Δ≥0. The second inequality is the new mixed centered-increment condition. It does not require a Lipschitz sample gradient or a global variance bound σ². No convexity, PL inequality, bounded gradient, or access to a minimizer is assumed. The theorem covers arbitrary finite-dimensional Euclidean spaces; its Hilbert-space specification also permits complete second-countable spaces with their Borel measurable structure. Dimension dependence enters through the displayed problem and oracle parameters.

Success means a measurable output X with integrable gradient norm and E‖∇f(X)‖≤ε. The setup quantifies over an abstract probability measure P on sample streams and the repository's IID structure. Product-measure representations are derived internally. Consecutive calls 2j and 2j+1 use the same fresh ξⱼ; different pairs are IID. Each of these calls costs one gradient evaluation. The oracle interface permits an adaptive second query, although this construction fixes both points before reading either reply. The algorithm's auxiliary random choices are independent of this stream. This coupling is substantive: the result is not a guarantee for an oracle that supplies only unrelated samples at different points.

## Guarantee and execution

If 2LΔ≤ε² the algorithm returns x₀ without an oracle call. Otherwise the public bound is

\[
2^{24}\left\lceil 1+\frac{(1+r)L\Delta}{\varepsilon^2}
 +\frac{\sigma^2}{\varepsilon^2}
 +\min\left\{\frac{M\sigma\Delta}{\varepsilon^3},
              \frac{L\Delta\sigma^2}{\varepsilon^4}\right\}\right\rceil.
\]

The theorem constructs a nested variance-reduced method with step size η=1/(2L). It returns a uniformly sampled **pre-step iterate**, not the last iterate. All tuning parameters are explicit functions of L,r,M,σ,Δ,ε. The code retains the trajectory, using O(Td) vector storage in dimension d; no memory-efficiency or parameter-adaptivity claim is made.

For reproducibility, put C=4096, N=⌈16LΔ/ε²⌉. If σ=0 choose m=0; if σ>0 and M=0 choose m=⌊log₄N⌋; otherwise choose m=⌊log₄(min{N,max{1,⌊2Lσ/(Mε)⌋}})⌋. Write q=4ᵐ and T=q⌈N/q⌉. At scale l, a representative is sampled uniformly from the preceding completed block of length 4ˡ; before the first completed block it is x₀. Level zero is the current iterate. Edge l estimates the gradient difference between consecutive levels and refreshes every 4ˡ iterations. The root estimates a raw gradient every q iterations. A coarser refresh also refreshes all finer edges, so their means telescope to the current gradient.

Regular edge batches have size max{1,⌈C(r2ˡ+M²η²2ᵐ2³ˡ)⌉}; early edges with t<4ˡ⁺¹ additionally receive ⌈Cr2ᵐ2ˡ⌉ samples. Root batches have size B=max{1,⌈C(r+σ²/ε²)⌉}; the initial root uses max{B,⌈C(rq+σ²/ε²)⌉}. Initial zero differences need no edge queries. The actual scalar-call implementation nevertheless spends two calls per raw-root sample, and the bound counts them. Padding to the public budget freezes the returned state and still consumes oracle calls. The cost proof retains both initialization and all early-edge samples.

## Why the mixed assumption is meaningful

Affine variance is an established model; see Liu, Jagabathula and Zhou, [arXiv:2302.06032v2](https://arxiv.org/abs/2302.06032v2), Assumption 4B. The mixed pair condition is new and should not be confused with ordinary mean-squared smoothness.

The strong-growth condition is established in [Vaswani, Bach and Schmidt, AISTATS 2019](https://proceedings.mlr.press/v89/vaswani19a.html), equation (1) and Theorem 3. Their raw second-moment constant corresponds to 1+ρ for the centered condition below. One sufficient mechanism starts with an unbiased strong-growth oracle h satisfying E‖h(x)−∇f(x)‖²≤ρ‖∇f(x)‖². Add a residual z that is conditionally centered given the whole clean sample field, has variance at most σ², and satisfies E‖z(x)−z(y)‖²≤M²‖x−y‖². Then g=h+z satisfies the two conditions with r=2ρ: conditional centering cancels the cross terms and the clean difference costs at most 2ρ times the two endpoint gradient energies. Independent clean and residual fields suffice. Generic interpolation alone does not imply this strong-growth property. The question is robustness of a strong-growth oracle to smooth residual corruption, not a theorem covering arbitrary interpolating learning problems.

A further sufficient mechanism uses an independent unbiased random linear compressor C with E‖C(v)−v‖²≤ω‖v‖² and a centered residual z with variance σ_z² and centered increment constant M_z. The combined oracle C(∇f+z) satisfies the assumptions with r=2ω, σ²=(1+ω)σ_z² and M²=(1+ω)M_z². For random-k sparsification ω=d/k−1. This supplies provenance for the model; it is **not** a new communication-complexity claim. Standard distributed algorithms often expose richer information, including local uncompressed gradients, shifted compressor queries, and possibly masks.

A nonlinear arbitrary-dimensional diagnostic uses a shifted and rotated periodic graph-coupled objective, with terms 1−cos xᵢ and λ(1−cos(xᵢ−xⱼ)) on a cycle with d≥3 and λ≥0. It is globally smooth and lower bounded, with L≤1+4λ and Δ≤2d(1+λ), and has nonoptimal stationary points, so it need not satisfy PL. Let aξ(s) be a centered stationary Gaussian process with covariance a²exp(−κ_g²(s−t)²/2), where a,κ_g,τ≥0 and κ>0; a,κ_g,κ are fixed in the small-τ comparison. The oracle g(x,ξ)=∇f(x)+aξ(f(x)/d)∇f(x)+τ∇φξ(x), with independent Gaussian potential φξ, is a conservative sample-gradient oracle. Normalize φ's covariance to exp(−κ²‖x−y‖²/2)/(dκ²). Its gradient variance is one and its increment second moment is at most 3κ²‖x−y‖². Thus r=2a², σ=τ, M=√3τκ suffice. Unknown shifts and rotations avoid a publicly known stationary point. At a stationary point with nonzero Hessian H, the gain component forces every centered mean-squared increment constant δ to satisfy δ≥a‖H‖, independently of τ; smoothness of the stated gain covariance and bounded derivatives of f give a finite such constant. This example establishes nonlinear scope and parameter separation, not practical prevalence, hardness, or a lower bound for any competing algorithm.

## New mechanism and comparisons

Nested variance reduction itself is established: see Zhou, Xu and Gu, [SNVRG, JMLR 2020](https://www.jmlr.org/papers/v21/18-447.html), Algorithm 1, Theorem 12, and Lemmas 39/42. The contribution is the treatment of mixed increments through independently selected representatives of **previous completed blocks**, with startup-aware allocation across scales. A representative's accumulated relative-noise charge is bounded by gradient energy averaged over its preceding block. Its spatial charge is instead bounded by path energy over adjacent blocks. These two charges can be allocated separately without a logarithmic hierarchy penalty.

Concretely, if S=ΣₜE‖∇f(xₜ)‖², V=ΣₜE‖vₜ‖², and R=ΣₜE‖vₜ−∇f(xₜ)‖², the formal proof gives

\[
R\le\frac5C S+\frac6C\|\nabla f(x_0)\|^2+\frac{81}{C}V+\frac{T\varepsilon^2}{C}.
\]

The displacement energy is exactly η²V. Smooth descent absorbs S and V, using ‖∇f(x₀)‖²≤2LΔ, and yields average squared gradient norm at most ε². Fresh batch errors are orthogonal after fixing the selectors; selector exposure is averaged using the earlier, pre-boundary history. These are distinct conditioning arguments. Charging initial representatives as though they already came from a completed block would invalidate the rate; the explicit startup batches address that issue.

Ordinary consecutive-difference STORM/PAGE analysis under the mixed inequality requires a relative-noise batch contribution proportional to the estimator horizon. Optimizing this standard reduction produces a cubic coefficient involving σ√(rL²+M²), rather than Mσ alone. A two-level uniformly selected reference has a spatial-distance term proportional to its squared refresh length and gives an ε⁻¹⁰ᐟ³ tradeoff in the relevant balancing regime. These calculations explain the obstruction addressed by the hierarchy; they are not lower bounds on those algorithm families. Prior history-dependent batching is also known, for example [Ji et al., ICML 2020](https://proceedings.mlr.press/v119/ji20a.html), Theorems 1–2 and supplementary equation (12); novelty is not claimed for using past information alone.

The strongest directly compared affine-variance primary baseline is Liu–Jagabathula–Zhou, v2, Theorem 3.3/Corollary 3.4 and Appendix B.2 equation (11). Its literal formulation uses gradients of random functions, so the comparison applies directly to the conservative diagnostic family above. Extending its inspected moment/descent argument to general vector oracles would be routine, and is not claimed as a contribution here. Its smooth-objective specialization combines affine variance with **raw** mean-squared smoothness. With centered constant δ, a valid raw constant is √(L²+δ²); one must not replace it by δ without another analysis. Writing K_r=max{1,⌈64r⌉} and G₀=‖∇f(x₀)‖, its paired-call rate contains

\[
O\!\left(\frac{(\sigma+\sqrt r G_0)\sqrt{K_r}}\varepsilon
+\frac{\Delta\bar L K_r}{\varepsilon^2}
+\left[\Delta\bar L+\frac{\sigma^2+\sigma\sqrt rG_0}{\sqrt{K_r}}\right]
\frac\sigma{\varepsilon^3}\right).
\]

The new guarantee permits rough relative noise without charging its global increment constant in the cubic term. It does not dominate every affine-noise guarantee: its deterministic term is linear in r. The separately developed repository [PR #21](https://github.com/k3nfalt/longtails/pull/21), `RecursiveMomentumAffineVariance.result`, assumes full mean-squared smoothness and has bound O(1+r²+σ²/ε²+(L+L̄)(1+√r)Δ/ε²+(L+L̄)σΔ/ε³), up to the constant factor converting pair calls to scalar calls. Thus the new guarantee can lose in its r dependence and does not supersede that stronger-regularity result; this repository artifact is not a published primary baseline. With fixed r,L,Δ and residual M,σ both proportional to τ, ε=τ³ yields a τ⁻⁷ upper bound here versus the applicable affine/raw-MSS τ⁻⁸ bound when the gain's smoothness stays bounded away from zero. This compares proved upper bounds; it is not an instance lower bound.

Bounded-variance centered-smoothness results, including Fradin et al., [AISTATS 2026](https://proceedings.mlr.press/v300/fradin26a.html), [arXiv:2512.18713v2](https://arxiv.org/abs/2512.18713v2), Theorems 4.1–4.4 and D.1, cannot use σ as a uniform variance bound for the full mixed oracle. At r=0 the present rate reduces to an established variance-reduction regime; at σ=0 its order is the established strong-growth rate. The claim concerns their mixed regime, not novelty of either endpoint.

Compression/sampling separation already occurs in [DASHA](https://arxiv.org/html/2202.01268v2), ICLR 2023, Assumptions 5.5–5.6, Theorem 6.7 and Theorem H.19. In particular its SYNC-MVR analysis separates the centered sampling increment constant from compression/population terms. [MARINA](https://proceedings.mlr.press/v139/gorbunov21a.html), ICML 2021, Definition 1.1 and Section 3.2, also uses explicit compressor and local-gradient operations. These are stronger interfaces than the generic combined oracle here. The present claim must not be read as discovering that compression and sampling errors can be separated.

Other checked neighboring results include [Stab-SGD](https://papers.neurips.cc/paper_files/paper/2025/hash/1c4c25619b2a88d99975dc0b1797a961-Abstract-Conference.html) (NeurIPS 2025, Assumption 1/Theorem 3: affine noise with SGD-like stochastic order), SHANG++ [v2](https://arxiv.org/abs/2603.09355v2) (Definition 1.1, Theorems 2.1–2.3: multiplicative noise in convex/strongly convex classes), and the [2026 MICE analysis](https://doi.org/10.1007/s00245-026-10451-x) (Assumption 7/equation (76) and Corollary 5: gradient-difference relative noise with PL structure). Their extra oracle operations or structural assumptions must be retained in comparisons.

## Limits

This is an expected-stationarity theorem with known tuning parameters and shared-sample access. It provides neither high-probability bounds nor an adaptive, memory-efficient, or practically validated implementation. The mixed condition is sufficient, not characterized as necessary. The synthetic interacting family is not an application theorem. Lower bounds for simultaneous shared-seed queries or zero-respecting methods do not establish unrestricted minimax optimality for this setup, whose second query may be adaptive. No universal optimality or universal superiority is claimed.
