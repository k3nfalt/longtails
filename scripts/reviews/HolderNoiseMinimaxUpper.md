# Novelty assessment: `HolderNoiseMinimaxUpper`

[`result`](../../LongTails/Theorems/HolderNoiseMinimaxUpper.lean) proves that [`outputAlgorithm`](../../LongTails/Algorithms/HolderNoiseVarianceReduction.lean) returns a uniformly random iterate with **E‖∇f(x_out)‖ ≤ ε**. The algorithm picks whichever of two batch configurations needs fewer calls: per-step anchors, or dyadic multilevel difference batches with a one-half-Hölder retuning when ν ≤ 1/2. The guarantee covers every L-smooth f on a separable Hilbert space with sup-gap Δ and an unbiased, jointly measurable, IID paired oracle. The noise e = g − ∇f has variance σ² and satisfies **E‖e(x)−e(y)‖² ≤ M‖x−y‖^{2ν}**, with 0 < ν ≤ 1 ([setup](../../LongTails/Setups/HolderNoiseNonconvex.lean)). One call returns g at two points using one shared sample.

**Proved budget**, with universal constants suppressed. Here L is population smoothness, Δ the initial gap, σ² the noise variance, (M, ν) the centered-noise Hölder constant and exponent, and ε the target:

$$
O\Big(\min\Big\{1+\tfrac{L\Delta+\sigma^2}{\varepsilon^2}+\tfrac{L\Delta\sigma^2}{\varepsilon^4},\;
\log^2\!\big(2+\tfrac{L\Delta}{\varepsilon^2}\big)\Big[1+\tfrac{L\Delta+\sigma^2}{\varepsilon^2}+\tfrac{\Delta}{\varepsilon^3}\max\big\{M(\tfrac{L}{\varepsilon})^{1-2\nu},\,M^{\frac1{2\nu}}\sigma^{2-\frac1\nu}\big\}\Big]\Big\}\Big).
$$

Write ρ = σ²L^{2ν}/(Mε^{2ν}): the noise variance divided by the increment variance at the step scale ε/L. Dividing the bracketed fractional term by LΔσ²/ε⁴ gives exactly ρ^{-min(1, 1/(2ν))}.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Minibatch SGD, [Ghadimi–Lan 2013, SIAM J. Optim., Cor. 2.2](https://arxiv.org/abs/1309.5549) (random iterate, E‖∇f‖² converted by Jensen); covers the full target class | O(1 + LΔ/ε² + LΔσ²/ε⁴) → the bound above | Speedup ≈ ρ^{min(1,1/(2ν))}/log²(2+LΔ/ε²) when ρ ≫ log²(2+LΔ/ε²), σ ≥ ε and LΔ ≥ ε² (the S term dominates). Example: L=M=σ=Δ=1, ν=1/4 gives ε⁻⁴ → ε^{-7/2} log²(1/ε). For ν ≥ 1/2 the exponent is ε⁻⁴ → ε⁻³. | None (SGD needs no M) | None | Uses paired same-sample queries and the centered Hölder assumption. Otherwise the cap keeps the SGD order. |
| NSGD-MVR, [Fradin et al., arXiv:2512.18713v2 (31 Mar 2026), Thm. 4.2](https://arxiv.org/abs/2512.18713), p = q = 2, (2,δ)-similarity; **ν = 1 only** | O(σ²/ε² + (L+√M)Δ/ε² + √MΔσ/ε³) → same up to log² (for ν ≥ 1/2, min{S, max(B₋,B₊)} ≤ M^{1/(2ν)}Δσ^{2−1/ν}/ε³) | None at ν = 1: the orders agree after taking the min. **Worse** by a log² factor. | Only ν = 1 is covered: linear distance scaling → exponent ν ∈ (0,1). Fradin's q is a moment order, not a distance exponent, so Hölder noise does not embed for ν < 1. | None | log²(2+LΔ/ε²) overhead at the endpoint |
| Repository [`DyadicVarianceReductionHolder`](../../LongTails/Theorems/DyadicVarianceReductionHolder.lean) (Oct 2026), raw MSH, ν ∈ [1/2,1] | O(log²(2+LΔ/ε²)[1 + (LΔ+σ²)/ε² + ΔM^{1/(2ν)}σ^{2−1/ν}/ε³]) → no worse, and capped by the SGD rate | For ν < 1/2: new, rate ε^{-(4−2ν)} where nothing was proved before. For ν ≥ 1/2: never worse, and better only when SGD is cheaper. | Raw E‖g(x)−g(y)‖² ≤ M d^{2ν} → centered condition. The raw version forces global ν-Hölder ∇f, excluding e.g. quadratic f plus Hölder noise. Range ν ≥ 1/2 → ν > 0. | None | None found |

**Reductions and mechanism.** I checked the obvious single-level shortcut. SPIDER-style differences with step ε/L and an optimized refresh period give Δ L^{1−ν} √M σ ε^{ν−4}, which is ε^{-(4−ν)}; that is worse than ε⁻³ for ν ≥ 1/2 and than ε^{-(4−2ν)} for ν < 1/2. Shorter steps make it worse. The ν ≤ 1/2 case comes from plugging the path-length bound M(2^jη)^{2ν} ≤ Mη^{2ν−1}·2^jη into the repository's existing dyadic (one-half) analysis. That substitution is short, and the technically new part is small. Proof ancestry: SPIDER/SNVRG-style nested differences and normalized descent, together with the repository's dyadic estimator.

**Search coverage.** On 17 Nov 2026 UTC I searched arXiv, JMLR, PMLR and NeurIPS sources for variance reduction or lower bounds under Hölder or fractional mean-square continuity of stochastic gradients, plus multilevel-Monte-Carlo gradient methods. I read the theorem statements of Fradin et al. (v2) directly and found no Hölder-distance variant. I did not re-read Ghadimi–Lan; its corollary number is cited from memory. I did not find a prior paper with ν < 1 for this oracle model, but the search was keyword-limited. The companion note is consistent with the Lean statement; its lower-bound pairing (D ≥ 64, large dimension) was not audited here. The result was introduced in commit c870310f on 17 Nov 2026.

**Conclusion**

**Yes: for rough noise (ν < 1) the proved complexity beats every applicable bound I checked, though the mechanism is a modest extension of an existing estimator.** The strongest baseline on the full class is minibatch SGD; at ν = 1 it is NSGD-MVR.

$$
\underbrace{\tfrac{L\Delta\sigma^2}{\varepsilon^4}}_{\text{SGD}}\;\longrightarrow\;\log^2\!\big(2+\tfrac{L\Delta}{\varepsilon^2}\big)\,\tfrac{L\Delta\sigma^2}{\varepsilon^4}\,\rho^{-\min(1,1/(2\nu))},\qquad \rho=\tfrac{\sigma^2L^{2\nu}}{M\varepsilon^{2\nu}}.
$$

The gain survives when ρ is larger than the log² factor and the noise term dominates (σ ≥ ε, LΔ ≥ ε²). For fixed constants that means ε⁻⁴ → ε^{-(4−2ν)} for ν < 1/2 and ε⁻⁴ → ε⁻³ for ν ≥ 1/2. At ν = 1 it only matches Fradin et al. and loses a log². Its class is broader than the repository's earlier raw-Hölder result, because centering admits unbounded, non-Hölder mean gradients.

What is established is a rate improvement over SGD on a natural class that published variance-reduction theorems do not cover. What is uncertain is priority: no prior ν < 1 paper turned up, but keyword search cannot rule one out. Technically, the new step is a short rescaling of an existing analysis, and the ν ∈ [1/2,1) rate was already in the repository. The claimable contribution is the first variance-reduction rate I found for ν < 1/2, extended to centered Hölder noise, and nearly tight according to the companion lower-bound theorem, which this review did not audit.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
