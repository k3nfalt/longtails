# Novelty assessment: SplitRobustHeavyTailedAcceleration

[`result`](../../LongTails/Theorems/SplitRobustHeavyTailedAcceleration.lean) proves the following. Take an `L`-smooth convex `f` on a separable Hilbert space with a minimizer `xstar`, `‖x0−xstar‖ ≤ R`, and IID unbiased gradient samples satisfying `E‖g(x,ω)−∇f(x)‖^p ≤ ρ‖∇f(x)‖^p` with `1<p≤2` ([setup](../../LongTails/Setups/HeavyTailedStrongGrowthConvex.lean)). Then the planned last descent iterate of [`SplitRobustAcceleration`](../../LongTails/Algorithms/SplitRobustAcceleration.lean) satisfies `∫ f(lastIterate) − f(xstar) dP ≤ ε`. The method uses a median-of-block-means descent direction and a separately clipped mirror direction, and its parameters depend on `L,R,ρ,p,ε`.

**Proved budget** (T = LR²/ε, H = max{1,T}; the indicator 1[ρ>0] turns off the second term when ρ = 0):

  N = O( √H + 1[ρ>0]·(1 + (2³⁴ρ)^{1/(p−1)})·(1 + log H)·H^{p/(3p−2)} ).

The factor 2^{34/(p−1)} becomes enormous as p→1. The bound is discontinuous at ρ = 0: for every ρ > 0 the run pays at least of order (1+log H)·H^{p/(3p−2)} calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nekrasova et al., [arXiv:2610.28107v1](https://arxiv.org/html/2610.28107v1) (20 Oct 2026, prior by 4 days), Thm 5.2 / Table 1, Clip-SSTM with σ₀=0 and σ₁^p=ρ | Õ(√T + ρ^{1/(p−1)} T^{p/(2(p−1))}) → O(√H + ρ^{1/(p−1)} H^{p/(3p−2)} log H) | Exponent of T drops by p²/[2(p−1)(3p−2)] for 1<p<2. Example: at p=3/2 it falls from 1.5 to 0.6. The gain holds only for large T, because of the p-dependent constants. At p=2 both bounds are ρT. | None: their class is broader (additive σ₀, weak-L^p tails) | None. Their guarantee is stronger: high probability with log(1/β) cost, versus expectation only here | Worse when ρ ≲ T^{−p²/(2(3p−2))}, up to logs, because this budget never drops to √T for ρ>0. Excludes additive noise. |
| Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/html/2609.33415v1) (27 Sep 2026), Thm 9 and App. F eq. (60) | Õ(√T + ρ^{1/(p−1)} T^{p/(2(p−1))}), taking K ≍ √T in bK + σ₁^q K^q → same as above | Same exponent gain as the row above. App. F explicitly says it does "not state a general finite-p matching theorem" for this model. | None: their class is broader ((H₀,H₁)-smoothness, additive and gap noise) | None. Theirs is high probability with single-sample steps. | Same losses as the row above |
| AGNES, Gupta–Siegel–Wojtowytsch, [NeurIPS 2024, arXiv:2302.05515](https://arxiv.org/abs/2302.05515), Thm 3 (applies only at p=2) | n ≍ (1+ρ)√T in expectation → O(√H + ρ√H log H) | Worse by a factor log T at p=2, for ρ > 0 | None at p=2. AGNES does not cover p<2. | None: both give expected last-iterate accuracy | Batched median-of-means pilot sampling |
| Standard reductions (reconstructed; not published theorems): regularized robust GD; a common pilot-clipped estimator inside a biased accelerated analysis ([Beznosikov et al., arXiv:2305.15938v2](https://arxiv.org/html/2305.15938v2), App. B.3, per the companion note) | Õ(ρ^{1/(p−1)} T^{min{1, p/(4(p−1))}}) → Õ(ρ^{1/(p−1)} T^{p/(3p−2)}) | Smaller exponent for every 1<p<2 | None | None | Checked only at the level of exponent algebra |

**Reduction check and mechanism.** Plugging σ ≲ ρ^{1/p}LR into additive heavy-tail accelerated methods gives exponent p/(p−1) ([Sadiev et al., ICML 2023](https://arxiv.org/abs/2302.00999); Nekrasova Cor. I.9). The two published affine bounds give p/(2(p−1)) ≥ 1. Median-of-means combined with deterministic relative-error acceleration costs (√T + α²T)·(ρα^{−p})^{1/(p−1)}, which is minimized at constant α and gives exponent 1. So the exponent p/(3p−2) does not follow from any of the checked reductions.

The new ingredient is the split itself. The descent step uses a low-error robust direction with step 1/L, and only the mirror weight pays the clipped variance V ≍ Λ^{2−p}. Balancing the multiplicative bias growth (1+α²/V)^N, with α ≍ Λ^{1−p} and N ≍ √(VH), gives Λ = H^{1/(3p−2)}; I checked this algebra. Proof ancestry is linear coupling and estimating-sequence accelerated gradient (they supply the energy), plus median-of-means and clipping (they supply the estimator). These sources do not supply the rate. The thinning lower bound Ω((1+ρ^{1/(p−1)})√T) (Lobanov eq. 59) leaves a gap of T^{(2−p)/(2(3p−2))}.

**Search coverage (24 Oct 2026, UTC).** I searched arXiv and NeurIPS/ICML heavy-tail and multiplicative-noise acceleration work from 2020–2026. I read the theorem and appendix statements of the two 2026 affine-noise papers and AGNES. I confirmed that [arXiv:2606.00520](https://arxiv.org/abs/2606.00520) and [arXiv:2510.11676](https://arxiv.org/abs/2510.11676) assume only additive σ^p noise.

Not verified:
- the full text of the NeurIPS 2026 MoM paper ([poster 148757](https://neurips.cc/virtual/2026/poster/148757)); its abstract describes additive structured noise;
- the Beznosikov B.3 lemmas;
- the companion note's Mishkin et al. and Bollapragada–Gupta citations.

The note's claims agree with what I checked.

**Conclusion**

**Yes, for the purely multiplicative heavy-tailed model with p<2, the proved accuracy exponent is polynomially better than every published guarantee I checked.** The strongest baselines are Clip-SSTM under affine heavy tails (Nekrasova et al., Thm 5.2) and Lobanov et al.'s universal construction. Both reach:

  ρ^{1/(p−1)}·T^{p/(2(p−1))}  →  this result: ρ^{1/(p−1)}·T^{p/(3p−2)}·log T  (T = LR²/ε)

For example, at p = 3/2 the exponent falls from 1.5 to 0.6. Standard reductions (regularized robust GD, a common clipped estimator) give at best min{1, p/(4(p−1))}.

The gain survives logarithms only for large T, because the constant 2^{34/(p−1)} is huge. It is lost for very small ρ > 0, roughly ρ ≲ T^{−p²/(2(3p−2))}, and at p = 2, where AGNES is a log factor faster. The competitors also give high-probability guarantees and cover additive noise; this result covers only expected error with purely gradient-proportional noise. That model was posed explicitly and left open in Lobanov et al., App. F.

The exponent comparison and the reductions are established. Priority is less certain: the search was not exhaustive, one NeurIPS 2026 full text was unavailable, the closest competitor appeared only four days earlier, and a gap to the √T lower bound remains. What can be claimed is the first checked accelerated rate T^{p/(3p−2)} for the pure relative p-th-moment model, obtained by splitting the descent and mirror estimators.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
