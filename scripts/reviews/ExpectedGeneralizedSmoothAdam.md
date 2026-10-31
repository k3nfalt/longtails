# Novelty review: ExpectedGeneralizedSmoothAdam

[`result`](../../LongTails/Theorems/ExpectedGeneralizedSmoothAdam.lean) proves this. Take uncorrected coordinate Adam ([algorithm](../../LongTails/Algorithms/GeneralizedSmoothAdam.lean)) with m₀=0, v₀=(1+σ²)𝟙, damping 1, β₂=1−1/T, η=a/√T and a given first-moment coefficient β∈[0,1). Its output is a uniformly selected point among x₀,…,x_{T−1}, and it satisfies E‖∇f(output)‖² ≤ ε². This holds for every differentiable f on ℝᵈ with ‖∇f(y)−∇f(x)‖ ≤ (L₀+L₁‖∇f(x)‖)‖y−x‖ whenever L₁‖y−x‖≤1, with f(x₀)−inf f ≤ Δ, and with an IID, jointly measurable, unbiased oracle of central variance ≤σ² ([setup](../../LongTails/Setups/GeneralizedSmoothAdam.lean)). `allowedAlgorithm` enforces this Adam family and the uniform pre-update output, and the theorem proves compliance.

**Complexity.** The proof makes exactly T stochastic-gradient calls, with

N = O( (d+1)²(1+L₀+L₁)¹⁰(1+σ²)(1+Δ)¹² / ((1−β)⁴ε⁴) + 1/(1−β) ).

Here d is the dimension, L₀,L₁ are the smoothness constants, Δ is the initial gap, σ² is the variance bound, β is the momentum coefficient and ε is the RMS-gradient accuracy. There are no logarithmic factors. The bound is not scale-invariant: it uses 1+L, 1+Δ and 1+σ².

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jin–Cheng–Chen–Luo–Zhou–Zhang, [arXiv:2609.37787](https://arxiv.org/abs/2609.37787) (v1 29 Sep 2026, v2 5 Oct 2026; prior), Thm B.2 / Claim B.1: same Adam recursion and calibration | **Restricted to p<1** in L₀–L_p smoothness. For p<1: O(d²·poly(P,R)·log²T/ε⁴), where P ≥ (1−β)⁻²+Δ+‖∇f(x₀)‖+L₀+L_p+σ²; at p=0 the explicit bound scales like d²P¹¹²/ε⁴. **At p=1: no expectation bound** → N above | Not comparable on the full class. On the p<1 overlap the proved polynomial degrees are much smaller and log T disappears, but both sets of constants are unoptimized | L₀–L_p with p<1 → p=1 (p<1 is nested inside p=1). This adds e.g. f=cosh with additive finite-variance noise | None. Both give the same averaged E‖∇f‖² | Oracle narrows: adapted conditional ABC second moment → IID with bounded central variance. vinit=1+σ² and damping 1 are fixed, where Jin allows any vinit,ϵ>0 |
| Same paper, Thm B.1 at p=1 (prior) | With probability 1−δ: avg ‖∇f‖² ≲ d·poly(P,R)/(√(δT)) (up to logs). The step prefactor shrinks with log(1/δ) → expectation bound N | Not comparable: the criteria differ | None | Prob. 1−δ with δ-dependent tuning → expectation for one fixed run. Integrating over δ is invalid, because each δ changes the algorithm | Same oracle narrowing as above |
| Zhang–Zhou–Zou, [TMLR 02/2025](https://openreview.net/pdf?id=QIzRdjIWnS) ([arXiv:2404.01436v3](https://arxiv.org/abs/2404.01436)), Thm 2 (prior) | (1/T)ΣE‖∇f‖ ≤ O(ε) at T=O(ε⁻⁴), requires small ε. Its L,Δ,d dependence sits in appendix constants that I did not extract → N | Not comparable: constants not extracted, and the criteria differ | Global coordinatewise \|∂ᵢf(x)−∂ᵢf(y)\| ≤ (L₀/√d+L₁\|∂ᵢf(x)\|)‖x−y‖ for all x,y (gradients grow at most linearly, so cosh is excluded) → local Euclidean condition with radius 1/L₁ | Mean gradient norm → RMS gradient norm | Their noise is broader (coordinatewise affine variance, conditional). Their damping sits inside the square root, a different variant |
| Hübler–Yang–Li–He, [AISTATS 2024](https://proceedings.mlr.press/v238/hubler24a.html), Cor. 16 (NSGD-M, problem-class method; prior) | (1/T)ΣE‖∇f‖ ≤ ε at O(log⁴T·(L₁Δ+σ+L₀/L₁)⁴/ε⁴), L₁>0. On that same mean criterion (implied by RMS ≤ ε via Jensen) → N | **Worse** by a factor (d+1)², and in L and Δ (Δ⁴ → (1+Δ)¹²). Better only in σ (σ⁴log⁴T → σ²), when σ² ≳ (d+1)²(1+L₀+L₁)¹⁰(1+Δ)¹²/(1−β)⁴. That comparison is against parameter-agnostic tuning only | None. On C² functions both are the class ‖∇²f‖ ≤ L₀+L₁‖∇f‖ up to constants (their Lemma 1) | Mean norm → RMS norm, which NSGD-M does not certify | Dimension-dependent. Requires Adam's v₀ initialization, which uses σ |

**Standard-reduction check.** Jin et al.'s expectation calibration δ_T = T^{−A_tail}, with A_tail > 1/2 + 2/(1−p), blows up at p=1. Their Prop. B.2 obstruction uses growing variance (ρ₂=3), not bounded variance. The p=1 class is not contained in any p<1 class. Applying a smooth-case theorem to log(1+f−f_lower) changes Adam's moment histories. So I found no substitution or reduction that yields this result. The new mechanism is a uniform 16th-moment bound on the objective height along the original trajectory, obtained through a log-potential, an exponential-martingale maximum and a denominator envelope. The proof's lineage, meaning self-normalization, horizon-length β₂ and the retained v₀, comes from Jin et al. (2026) and its predecessor [arXiv:2603.03099](https://arxiv.org/abs/2603.03099). Those works supply the template but not the p=1 moment control.

**Search coverage.** I searched on 23 Oct 2026 (UTC) across arXiv, OpenReview, TMLR, PMLR and NeurIPS for Adam, RMSProp and normalized-momentum methods under (L₀,L₁) or generalized smoothness. I read the theorem statements cited above. I also checked these and excluded them as baselines:
- [Li–Rakhlin–Jadbabaie, NeurIPS 2023](https://arxiv.org/abs/2304.13972), Assumptions 3–4: almost-surely bounded or sub-Gaussian noise, high-probability results.
- [Hong–Lin](https://arxiv.org/abs/2402.03982), (A3): exponential-moment noise, high-probability results.
- [Li et al., NeurIPS 2023](https://arxiv.org/abs/2306.01264), SGD Thm 5.3: high probability with poly(1/δ) tuning.
- [Jin et al., NeurIPS 2021](https://arxiv.org/abs/2110.12459), Thm 3.5: ΔL₀σ²ε⁻⁴ on a global no-radius class, mean criterion.
- [Peng et al., arXiv:2507.05966v1](https://arxiv.org/abs/2507.05966), Cor. 3.2: global smoothness and a trajectory lower bound on |m|/√v.

I did not verify the NeurIPS 2026 acceptance of 2609.37787 that the companion note claims. The theorem file was introduced in commit e3aa5fd on 23 Oct 2026, after Jin et al. v2. The companion note's descriptions of these papers match what I read.

## Conclusion

**This is a new guarantee for Adam, not an optimization improvement.** It extends Jin et al.'s (Sep 2026) expected squared-gradient guarantee for the same uncorrected, horizon-calibrated Adam from generalized-smoothness exponent p<1 to the boundary p=1, i.e. standard (L₀,L₁)-smoothness. The cost is narrowing the oracle to IID samples with bounded central variance.

Instances such as f=cosh with finite-variance noise now have an expected-RMS certificate for Adam. No checked theorem gave one: the earlier Adam results need bounded or sub-Gaussian noise, only give high-probability guarantees with δ-tuned steps, or need global smoothness conditions that exclude exponential growth.

For the problem class, normalized SGD with momentum is much cheaper on the weaker mean-norm criterion:

| | mean-norm cost |
|---|---|
| NSGD-M (Hübler et al., Cor. 16) | O(log⁴T·(L₁Δ+σ+L₀/L₁)⁴/ε⁴) |
| This result | O((d+1)²(1+L₀+L₁)¹⁰(1+σ²)(1+Δ)¹²/((1−β)⁴ε⁴)) |

The selected bound wins only in σ against parameter-agnostic tuning, and known-parameter momentum tuning likely removes that gain. Whether any method already certifies the RMS criterion in expectation on this class is unchecked.

The contribution that can be claimed is closing the p=1 bounded-variance expectation case for this widely used Adam variant with a new moment-control argument. It is a modest, boundary extension of a weeks-old framework, at the same ε⁻⁴ rate, with a narrower oracle and no complexity gain.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
