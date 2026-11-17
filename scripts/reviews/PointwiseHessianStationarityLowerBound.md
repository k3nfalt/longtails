# Novelty assessment: PointwiseHessianStationarityLowerBound

The [theorem](../../LongTails/Theorems/PointwiseHessianStationarityLowerBound.lean) proves the following, using the [setup](../../LongTails/Setups/PointwiseHessianStationarity.lean) and the hard-instance construction in [RelativeHessianHardness](../../LongTails/Proofs/RelativeHessianHardness.lean) (no algorithm is restricted). Take any randomized adaptive algorithm that knows all parameters and receives exact (f, ∇f, ∇²f) at each query. For every budget b ≤ ⌊Δ√(L₀+L₁ε)/(2³⁹ε^{3/2})⌋, there is an admissible C³ objective that may depend on the algorithm and on b, but not on the seed. On that objective the output fails to satisfy 𝔼‖∇f(X)‖ ≤ ε.

**Necessary budget.** The theorem needs
Ω( Δ√(L₀+L₁ε) ε^{-3/2} ) ≍ Ω( Δ√L₀ ε^{-3/2} + Δ√L₁ ε^{-1} ) joint value/gradient/Hessian calls.

The parameters are:
- the objective satisfies ‖D³f(x)‖ ≤ L₀ + L₁‖∇f(x)‖ at every x, with L₀, L₁ ≥ 0 and L₀ + L₁ > 0;
- Δ ≥ f(0) − inf f is the initial gap;
- G ≥ ‖∇f(0)‖ bounds the initial gradient;
- d is the dimension.

The bound holds in this regime: G ≥ 16ε, Δ√(L₀+L₁ε)ε^{-3/2} ≥ 2³⁹, and d ≥ 2¹⁴⁰(1+⌈Δ√(L₀+L₁ε)ε^{-3/2}⌉)⁴. The regime includes L₀ = 0.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon–Duchi–Hinder–Sidford, *Lower Bounds for Finding Stationary Points I* ([arXiv:1710.11606](https://arxiv.org/abs/1710.11606), Math. Program. 2020), Thm 2 with p = 2. **Applies only to the subclass where the Hessian is L₀-Lipschitz** (the case L₁ = 0). | Lower bound Ω(Δ√L₀ ε^{-3/2}); undefined if L₀ = 0 → Ω(Δ√L₀ ε^{-3/2} + Δ√L₁ ε^{-1}) | Larger necessary budget by a factor ≍ √(1 + L₁ε/L₀). The gain is polynomial when L₁ε ≫ L₀. The bound is new when L₀ = 0. | Third derivative bounded uniformly by L₀ → bounded pointwise by L₀ + L₁‖∇f‖ (a hard instance for the larger class) | None. Both use expected or constant-probability failure for randomized methods; Carmon's bound converts to expected accuracy by Markov's inequality. | Needs d ≳ (Δ√(L₀+L₁ε)ε^{-3/2})⁴, versus roughly T²·log T for Carmon. Constants of order 2³⁹. Needs G ≥ 16ε. |
| Fang–Marumo–Takeda ([arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741), preprint, 12 Jul 2026), Assumption 1 and eq. (7)/Corollary 1 with δ = ∞. Upper bound under the same pointwise condition, with L₀ > 0. | Upper bound O(Δ√L₀ε^{-3/2} + Δ√L₁ε^{-1}) + Õ(1) versus the new lower bound Ω(same) | Gap closed for the polynomial terms. The upper bound's additive logarithm is not matched. | None (the classes coincide when L₀ > 0) | Not applicable. Their method is parameter-free; the lower bound holds even for algorithms that know every parameter. | Lower bound only in the stated high-dimensional regime. No curvature (δ) term. |
| Repository [PointwiseHessianStationarity](../../LongTails/Theorems/PointwiseHessianStationarity.lean), the companion upper bound (same `spec`) | ⌈10⁵Δ√(L₀+L₁ε)ε^{-3/2}⌉ + 2⌈log(1+L₁G/(L₀+L₁ε))/log(4/3)⌉ + 200 versus the lower bound ⌊Δ√(L₀+L₁ε)/(2³⁹ε^{3/2})⌋ | Tight up to a universal constant and the additive term log(1 + L₁G/(L₀+L₁ε)) | None | None | Whether the logarithmic G-term is necessary remains open. |

Semenov–Jaggi–Doikov (ICLR 2026, cited in the Fang–Marumo–Takeda paper) obtain the same upper rate under a stronger two-point condition. I did not re-check that rate, and it does not affect the lower bound.

**Reduction check.** I found no standard reduction. Rescaling a Carmon instance whose Hessian is Lipschitz with constant L₁ε fails, because the class requires ‖D³f‖ ≤ L₀ + L₁‖∇f‖ even at stationary points. With L₀ small, the third derivative must essentially vanish wherever ∇f ≈ 0. Ordinary chains and quadratic guards violate this.

**Proof ancestry.** The closest mechanism is in Liang–Luo ([arXiv:2610.21692](https://arxiv.org/abs/2610.21692), v1 15 Oct 2026, v2 15 Nov 2026, preprint), Lemmas 3.2–3.4. It is a first-order lower bound Ω(L₀Δε⁻² + L₁Δε⁻¹) for first-order (L₀,L₁)-smoothness with a first-order oracle, so it is not a competitor for this class. Their saturating tanh chain is diagonal when every coordinate is saturated, and it bounds ∇² by ‖∇f‖ only up to a μ·log(1/μ) residual that L₀ > 0 absorbs.

The selected proof moves this idea up one derivative order. Its arctan profile makes the guarded gradient vanish exactly where q″ vanishes (|q″| ≤ 12|at − q|). A compact cutoff removes the residual, which is why the bound covers L₀ = 0. The coordinate-hiding and averaging steps are standard; the arctan/cutoff compatibility appears to be the genuinely new technical step. I did not verify the Lean proofs or run any audit or build.

**Search coverage and discrepancies.** I searched on 2026-11-17 UTC: arXiv and the ICLR 2026 proceedings for lower bounds under generalized or relative Hessian smoothness, read Fang–Marumo–Takeda v1 and Liang–Luo v2, and searched for higher-order and first-order lower bounds. I did not re-fetch Carmon et al. Thm 2 this session; its statement is taken from the standard result. The Fang–Marumo–Takeda Section 7 open question was confirmed only through a summary, not verbatim.

The companion note calls the d ∝ S⁴ requirement "weaker" than Carmon's d ∝ S²·log S. It is actually a stronger dimension requirement, so the result is weaker in this respect. The note also omits Liang–Luo, which is the closest mechanism and appeared before this result was introduced (commit e6e32a49, 17 Nov 2026). Git history only gives the date the result entered this repository.

**Conclusion**

**Yes: this proves a stronger necessary oracle complexity than any lower bound I found for this class.** The strongest applicable prior lower bound is Carmon et al.'s Ω(Δ√L₀ε^{-3/2}), which uses only the uniform part L₀ of the third-derivative bound.

| | Necessary joint calls for 𝔼‖∇f‖ ≤ ε |
|---|---|
| Carmon et al. (subclass where L₁ is unused) | Ω(Δ√L₀ ε^{-3/2}) |
| This theorem | Ω(Δ√L₀ ε^{-3/2} + Δ√L₁ ε^{-1}) |
| Known upper bounds (Fang–Marumo–Takeda; repository) | O(Δ√L₀ ε^{-3/2} + Δ√L₁ ε^{-1}) plus an additive logarithm |

The gain is a factor of about √(L₁ε/L₀) when L₁ε ≫ L₀, and it is new at L₀ = 0. It settles, for first-order stationarity, the necessity question about the Δ√L₁/ε term raised by Fang–Marumo–Takeda; their curvature term is not addressed. The theorem holds only when the dimension is at least about (Δ√(L₀+L₁ε)ε^{-3/2})⁴, which is a larger requirement than the classical construction needs, and when G ≥ 16ε. The upper bound's additive log(1 + L₁G/(L₀+L₁ε)) term is not matched.

The comparison establishes the gain. Priority is less certain, because this area is moving fast: Liang–Luo's first-order analogue appeared a month earlier and uses a related saturation mechanism. No higher-order version of it was found. What can be claimed is a lower bound for every randomized second-order method under pointwise Hessian growth. It makes the polynomial complexity tight, and it rests on a new hard instance whose third derivative vanishes at its stationary points.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
