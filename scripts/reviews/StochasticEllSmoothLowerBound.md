# Novelty assessment: StochasticEllSmoothLowerBound

[`result`](../../LongTails/Theorems/StochasticEllSmoothLowerBound.lean) is a `NonConvergence` statement on [HighDimensionalStochasticEllSmoothNonconvex](../../LongTails/Setups/HighDimensionalStochasticEllSmoothNonconvex.lean), which is [StochasticEllSmoothNonconvex](../../LongTails/Setups/StochasticEllSmoothNonconvex.lean) on ℝᵈ. It quantifies over every randomized algorithm (no `allowedAlgorithm`) and every budget b ≤ ⌊(2−ρ)T̄·max{1,(σ/(2¹³ε))^{p/(p−1)}}/2³²⌋, with T̄ = Δℓ(ε)/ε². For each such pair it gives an f and an IID, unbiased, jointly measurable gradient-only oracle with p-th central moment ≤ σ^p such that E‖∇f(x̂)‖ > ε. The instance has ‖∇²f(x)‖ ≤ ℓ(‖∇f(x)‖) and f(x⁰) − inf f ≤ Δ. It depends on the algorithm and on b, but not on the seed. There is no separate algorithm module: the hard instance is in [StochasticEllSmoothLower](../../LongTails/Proofs/StochasticEllSmoothLower.lean) and [StochasticEllSmoothMask](../../LongTails/Proofs/StochasticEllSmoothMask.lean).

**Proved necessary budget.** ℓ is the curvature profile: nondecreasing, with ℓ(u)/u^ρ nonincreasing and ℓ(0) > 0. ρ ∈ [0,2), p ∈ (1,2] is the noise moment order, σ the noise scale, Δ the initial gap and ε the target E‖∇f‖.

  Ω_p((2−ρ)·(Δℓ(ε)/ε²)·(1 + (σ/ε)^{p/(p−1)})). For ℓ = L₀ + L_ρu^ρ this is Ω_p((2−ρ)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})(1 + (σ/ε)^{p/(p−1)})).

The constant 2^{−13p/(p−1)} depends on p. Validity requires 2²⁸ε² ≤ (2−ρ)Δℓ(ε), and the budget is nonzero only when it exceeds 2³². It also requires d ≥ 2⁵⁶(Y/2²⁷+1)⁶(ℓ(ε)/ℓ(0))⁴, where Y is 2³² times the budget. I checked by hand that the regime is nonempty: take L_ρ > 0, small ε and large d. No Lean lemma proves this. The [upper bound](../../LongTails/Theorems/StochasticEllSmoothUpperBound.lean) on the same base class leaves a gap of 2^{O(p/(p−1))}·log(2+T̄)/(2−ρ)².

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liang–Luo, [arXiv:2610.21692](https://arxiv.org/abs/2610.21692) v2 (15 Nov 2026, preprint, prior), Thm 4.5: randomized, p-BCM, E‖∇f‖. *Applies to ρ ∈ (1,2) only via the embedding L₀/2 + L₁′u ≤ L₀ + L_ρu^ρ, with L₁′ ≍ L_ρ^{1/ρ}L₀^{(ρ−1)/ρ}.* Its hard function satisfies a Hessian bound (Lemma 3.3, eq. 15), so it lies in the ℓ-class | Ω((1+(σ/ε)^r)(L₀Δ/ε² + L_ρ^{1/ρ}L₀^{(ρ−1)/ρ}Δ/ε)) → Ω_p((2−ρ)(1+(σ/ε)^r)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})), r = p/(p−1) | For ρ ∈ (1,2) and L_ρε^ρ ≥ L₀: larger by (L_ρε^ρ/L₀)^{(ρ−1)/ρ}. For ρ ≤ 1: none, same order | None: same Hessian-type class and p-BCM oracle | None | Loses the factor (2−ρ) and p-dependent constants. Dimension of degree 6 in the budget, versus ≈ T + R² log T for Liang–Luo |
| Repository [EllSmoothNonconvexLowerBound](../../LongTails/Theorems/EllSmoothNonconvexLowerBound.lean) (σ = 0), combined by max with Arjevani et al. ([Math. Program. 2023](https://arxiv.org/abs/1912.02365), Thm 3; L = ℓ(0)) or the p-BCM version above | Ω((2−ρ)Δℓ(ε)/ε² + (σ/ε)^r(L₀Δ/ε² + L_ρ^{1/ρ}L₀^{(ρ−1)/ρ}Δ/ε)) → same as above | Larger by roughly min{(σ/ε)^r, (L_ρε^ρ/L₀)^{(ρ−1)/ρ}}, up to (2−ρ) and constants, when σ ≫ ε and L_ρε^ρ ≫ L₀. Example: ρ = 3/2, p = 2, L_ρε^{3/2} = 10⁶L₀, σ = 10⁶ε gives a factor ≈ 100 | None | None | Same as above. The gain needs σ ≳ 2¹³ε to register in the stated constants |
| Fradin et al., [arXiv:2512.18713](https://arxiv.org/abs/2512.18713) v2 (31 Mar 2026), Thms 3.1–3.3. *Special case:* L-smooth or mean-squared-smooth classes, zero-respecting algorithms | Ω(LΔ/ε²·(1+(σ/ε)^r)) at L = ℓ(0) → above | Same as the ρ = 0 row, i.e. none beyond the generalized-smoothness factor | ρ = 0 → ρ < 2 | None | Their classes are not nested with this one (samplewise smoothness) |

**Reduction check and proof ancestry.** No class embedding of the ρ ≤ 1 hard instances yields the product (σ/ε)^r·L_ρΔ/ε^{2−ρ}. A max of known bounds gives a sum, not a product, and an L-smooth instance with L = ℓ(ε) violates ‖∇²f‖ ≤ ℓ(‖∇f‖) near small gradients. The proof composes two inherited pieces: the ρ-adapted Carmon-type chain of the repository's deterministic bound, and the Bernoulli-mask probabilistic zero-chain of Arjevani et al. (via repository PR #185). The genuinely new step is a uniform bound ‖∇f − K_s‖ ≤ 4096ε on the masked frontier field of that chain, which makes the masked oracle fit the p-BCM budget. Given those two pipelines, the step is fairly routine.

**Search coverage (2026-11-25).** I searched arXiv and the web for stochastic and heavy-tailed lower bounds under ℓ-, (ρ,L₀,L_ρ)-, α-symmetric and (L₀,L₁)-smoothness. I read Liang–Luo v2's class, Thm 4.5 and Lemmas 3.3–4.4, and the theorem list and algorithm class of Fradin et al. I cited Arjevani et al. from the published version without rereading it. I found no stochastic lower bound for ρ ∈ (1,2). The result entered the repository on 2026-11-24 (f5b3e4a4), after both preprints. The companion note matches the Lean statement. It omits that Liang–Luo's class is the local gradient-difference condition, and its table groups Fradin et al. under "randomized", although their theorems are stated for zero-respecting algorithms.

**Conclusion**

**Yes, for ρ ∈ (1,2) the necessary budget is polynomially larger than anything previously known; for ρ ≤ 1 it adds nothing.** The strongest baseline is Liang–Luo's randomized p-BCM (L₀,L₁) lower bound, transferred to the ρ-class by the best linear minorant of L₀ + L_ρu^ρ:

  Ω((1+(σ/ε)^r)(L₀Δ/ε² + L_ρ^{1/ρ}L₀^{(ρ−1)/ρ}Δ/ε))  →  Ω_p((2−ρ)(1+(σ/ε)^r)(L₀Δ/ε² + L_ρΔ/ε^{2−ρ})).

When L_ρε^ρ ≫ L₀, the new bound is larger by (L_ρε^ρ/L₀)^{(ρ−1)/ρ}. It also exceeds the max of the deterministic ρ-bound and the noisy L₀-bound whenever both σ ≫ ε and L_ρε^ρ ≫ L₀. Together with the companion upper bound, it pins the complexity down to log(2+T̄)/(2−ρ)² and p-dependent constants.

Several limits remain. The constant degrades as ρ → 2, and the result needs ℓ(0) > 0 and dimension polynomial of degree 6 in the budget. The method is a combination of two existing lower-bound pipelines plus one new uniform masking bound, so the technical novelty is modest even though the conclusion is new.

The comparison proves a gain over every checked bound. My search found no prior stochastic bound for ρ > 1, but that does not establish priority. What can be claimed is the first checked heavy-tailed stochastic lower bound for ℓ-smoothness of order ρ ∈ (1,2) that captures the product of the noise factor and the ℓ(ε) term.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
