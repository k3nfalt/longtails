# Novelty assessment: DirectionalHeavyTailedSecondOrder

[`result`](../../LongTails/Theorems/DirectionalHeavyTailedSecondOrder.lean) proves the following. For `f : ℝᵈ → ℝ` with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian and `f(x₀) − inf f ≤ Δ`, and for fresh IID stochastic gradients and Hessian-vector products (HVPs) that are unbiased and have directional central `p`-moments `E‖g−∇f‖^p ≤ σg^p` and `E‖(H−∇²f)v‖^p ≤ σh^p‖v‖^p` with `1 < p ≤ 2` ([setup](../../LongTails/Setups/HeavyTailedHessianVector.lean)), the [algorithm](../../LongTails/Algorithms/HeavyTailedSosp.lean) ([tuning](../../LongTails/Algorithms/HeavyTailedSospTuned.lean)) outputs a random cycle-start point. With probability at least 2/3, that point satisfies `‖∇f‖ ≤ ε` and `λ_min(∇²f) ≥ −√(ρε)`.

**Budget.** Let `r = p/(p−1)`, and let `ℓ = log(2 + (L+√(ρε))²/(ρε))` and `ℓ_d = log(2+d)`. Suppressing only the factor `2^{64r²}` (a constant for fixed `p` that blows up as `p ↓ 1`), the proved budget is

```
O( (1+σg/ε)^r + (1+Δ(L+√ρε)/ε²)·[ 1 + (1+σg/ε)^{r−1}(σh/(L+√ρε) + ρε/(L+√ρε)²)
   + (σh/(L+√ρε) + ρε/(L+√ρε)²)^r + ℓ·ℓ_d·(L+√ρε)/√(ρε)
   + ℓ·ℓ_d^r·(σh/√(ρε))^r + ℓ²(1+(σh/√(ρε))^r) ] )
```

Each gradient or HVP query counts as one call. For fixed `L, ρ, Δ, σg, σh > 0` and `p`, the leading term is `Δσh σg^{r−1}/ε^{r+1}`. The curvature terms are `Õ(ΔLσh^r ℓ_d^r/(ρ^{r/2}ε^{2+r/2}))`, and since `r ≥ 2` their exponent is never larger than `r+1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani et al., [COLT 2020 / arXiv 2006.13476](https://arxiv.org/abs/2006.13476), Thm 4 (Oja-based method using HVPs only; special-case baseline, `p = 2` only) | With `γ = √(ρε)`: `Õ(Δσgσ̄h/ε³ + Δ(σ̄h+L)²/(√ρ ε^{5/2}) + ΔL/ε²)` → at `p=2`: `O(σg²/ε² + ΔL/ε² + Δσh(σg + Lσh ℓ_d² ℓ/ρ)/ε³ + ΔL²ℓℓ_d/(√ρ ε^{5/2}) + …)` | Worse at `p=2`: the `ε⁻³` coefficient grows by a factor of order `1 + Lσh/(ρσg)`, up to logarithms, and there are extra log-d factors | Almost-sure bounded operator-norm Hessian noise `‖H−∇²f‖_op ≤ σ̄h` → finite directional variance; also `p<2` (infinite variance) | None (both give a constant-probability SOSP; their probability is 5/8, here 2/3) | Their theorem needs `ε ≤ min(σg, √(ΔL))` and `√(ρε) ≤ min(σ̄h, L, ρ)`. This result needs a `2^{256}` constant at `p=2` |
| Sadiev–Richtárik–Fatkhullin, [NeurIPS 2025 / arXiv 2510.10690 v1](https://arxiv.org/abs/2510.10690), Thm 2 (FOSP only) | `O(Δ(L+σh)/ε²·(1+(σg/ε)^{r−1}) + (σg/ε)^r)` for averaged `E‖∇f‖ ≤ ε` → the bound above | None on the first-order terms (same order); the curvature terms are extra | Operator-norm `p`-moments `E‖H−∇²f‖_op^p ≤ σh^p` → directional `p`-moments (broader class) | Average-iterate expected gradient norm → second-order stationarity with probability ≥ 2/3 (new criterion; their footnote 3 leaves SOSP for future work) | Requires a `ρ`-Lipschitz Hessian, which they do not. Adds the curvature terms, `2^{64r²}` and log-d factors. No arbitrary `δ` |

The repository has no other heavy-tailed SOSP theorem. [EnergyHessianReuse](../../LongTails/Theorems/EnergyHessianReuse.lean) and related files concern other setups.

**Reduction check and proof ancestry.** The first-order part follows the known mechanism: normalized steps plus an HVP transport/recursive estimator, as in Arjevani et al. (Alg. 1) and Sadiev et al. (Alg. 1). Negative-curvature interleaving follows Carmon et al. and Allen-Zhu–Li, as Arjevani's Alg. 4 does. The missing step is heavy-tailed negative-curvature detection with polylogarithmic dependence on `d`:
- Arjevani's Oja analysis needs almost-sure bounded noise.
- Gu et al. ([arXiv 2609.26508](https://arxiv.org/abs/2609.26508), 22 Sep 2026, preprint) need second moments.
- Clipping or median-of-means applied per HVP destroys linearity or unbiasedness.
- A noisy power method with adversarial per-step error seems to need error `≲ γ/√d`, which suggests polynomial dependence on `d`. I did not derive this.

So the new part is the `p`-moment Oja/energy argument. Garber's log-growth potential (ORL 2025) is only proof ancestry.

**Search coverage.** On 2026-10-25 UTC I searched arXiv and the web for heavy-tailed SOSP, saddle escape, Hessian clipping and heavy-tailed Oja/PCA. I read the theorem statements of Arjevani et al. and Sadiev et al. from the PDFs. I checked Gu et al. at abstract level only, and did not open Fradin et al. (AISTATS 2026, FOSP) or Garber. I found no prior SOSP guarantee for `p < 2`. The companion note's citations match what I checked, and its claim that the FOSP exponent "is not new" is accurate. The result was introduced in commit `70088d3` (2026-10-25).

## Conclusion

**Yes, in scope: this appears to be the first second-order-stationarity guarantee under infinite-variance (`p<2`) stochastic HVPs, but the rate is not improved.**

The strongest baselines solve neighbouring problems:

| | Criterion | Noise | Leading cost |
|---|---|---|---|
| Sadiev et al. 2025 | first-order, averaged, in expectation | operator-norm `p`-moments | `Δ(L+σh)σg^{r−1}/ε^{r+1}` |
| Arjevani et al. 2020 | second-order | `p=2`, a.s. bounded | `Δσgσ̄h/ε³` |
| This result | second-order, prob. ≥ 2/3 | directional `p`-moments | `Δσhσg^{r−1}/ε^{r+1}` + lower-order curvature terms |

So the result adds the curvature criterion at the known heavy-tailed first-order exponent `ε^{−(2p−1)/(p−1)}`. It needs only directional moments, which is weaker than an operator-norm assumption, and pays only polylogarithmic factors in `d`.

It loses in several places:
- At `p=2` it is worse than Arjevani's HVP-only bound by a factor of order `1 + Lσh/(ρσg)` in the `ε⁻³` term, though that bound needs almost-surely bounded noise.
- The constant `2^{64r²}` is astronomically large.
- The confidence is fixed at 2/3.
- In the noiseless case it is far worse than accelerated deterministic methods.

The comparison shows that the guarantee extends existing ones. Priority rests on a targeted search that found no heavy-tailed SOSP result; it is not exhaustive. I did not check whether a robust power-method composition could give a dimension-dependent alternative.

The claimable contribution is a new problem-class guarantee: heavy-tailed directional HVP noise suffices for second-order stationarity at the heavy-tailed first-order rate, with logarithmic dependence on dimension.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
