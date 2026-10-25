# Novelty assessment: AffineMomentAcceleration

The [theorem](../../LongTails/Theorems/AffineMomentAcceleration.lean) (setup: [AffineMomentConvex](../../LongTails/Setups/AffineMomentConvex.lean); algorithm: [AffineMomentAccelerated](../../LongTails/Algorithms/AffineMomentAccelerated.lean)) proves the following. For a convex function f with globally L-Lipschitz gradient and a minimizer within R of x₀, take an IID, unbiased, jointly measurable oracle with 𝔼‖g−∇f‖^p ≤ σ₀^p + σ₁^p‖∇f‖^p, where p∈(1,2]. The returned **last primal iterate** then satisfies f(x)−f* ≤ ε with probability ≥ 1−δ. The algorithm uses robust pilot batches and fresh-mean mirror batches.

**Complexity.** In the formula below, q=p/(p−1) and T=LR²/ε. The budget is derived from the proved Lean budget, which counts every oracle reply:

$$N=O\Big(2^{256q}\Big[(1+\sigma_1)^q(1+T)^{\frac{p}{3p-2}}+\Big(\tfrac{\sigma_0}{LR}+\tfrac{\sigma_0R}{\varepsilon}\Big)^q\Big]\log^{q+1}\!\big(20+q+T+\tfrac1\delta\big)\Big).$$

The method needs L, R, ε, δ, p, σ₀ and σ₁. Here p/(3p−2) = q/(q+2) ∈ [½,1).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nekrasova et al., [arXiv:2610.28107v1](https://arxiv.org/abs/2610.28107) (20 Oct 2026, prior by 5 days), Clip-SSTM, Assumption 3.4, Thm 5.2 / Table 1. Direct competitor. | Õ(√T + (σ₀R/ε)^q + σ₁^q T^{q/2}) → Õ_q((1+σ₁)^q T^{q/(q+2)} + (σ₀R/ε)^q) | Multiplicative term T^{q/2} → T^{q/(q+2)}. Speedup ≈ min{T^{q/2−q/(q+2)}, σ₁^qT^{q/2}/(σ₀R/ε)^q} when σ₁ ≥ 1, σ₀ ≪ σ₁√(Lε) and T is large. **Worse** when σ₁ ≲ T^{1/(q+2)−1/2}, including σ₁=0 (√T vs T^{q/(q+2)}). | None. Their class is broader: weak-L^α tails and smoothness only on B_{3R}(x*). | None. Both give a high-probability last-iterate guarantee and both need the noise parameters. | Global smoothness is required; log^{q+1} vs their (unverified-power) ln(K/δ); 2^{256q} constant. |
| Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/abs/2609.33415) (27 Sep 2026, prior), Thm 9 with H₁=σ₂=0, Q=B(x₀,R). | Õ(√T + (σ₀R/ε)^q + σ₁^qT^{q/2}) → as above | Same as the previous row | None. Theirs also covers (H₀,H₁)-smoothness and gap-dependent noise. | None. Both return a final point with high probability. | They need a projection set and Δ₀; for this class those cost nothing extra (D=2R, Δ₀≤LR²/2). |
| Gupta–Siegel–Wojtowytsch, [NeurIPS 2024](https://arxiv.org/abs/2302.05515), Thm 3 (AGNES). Special case: p=2, σ₀=0. | O((1+σ₁²)√T) in expectation; Markov gives O((1+σ₁²)√(T/δ)) → O((1+σ₁)²√T log³(T/δ)) | Same order in T and σ₁. Confidence dependence improves from 1/δ (via Markov) to log(1/δ). | Covers p<2 and σ₀>0, which AGNES does not. | Expected accuracy → high probability | Three extra log factors. Not the novelty claim. |
| Sadiev et al., ICML 2023 (clipped SSTM). Special case: σ₁=0. | Õ(√T + (σ₀R/ε)^q) → Õ(T^{q/(q+2)} + (σ₀R/ε)^q) | Worse when √T dominates | None | None | — |

**Reductions.** Batching the 2026 bounds multiplies the √T term and leaves σ₁^qT^{q/2} unchanged. Converting the multiplicative noise into additive noise on a radius-R region gives σ₁^qT^q. Neither reproduces this bound.

There is one repository overlap ([RecursiveRelativeErrorConvex](../../LongTails/Theorems/RecursiveRelativeErrorConvex.md) combined with median-of-means). It gives T^{1/2+o(1)} when σ₀=0 and beats this result there; it does not accept an absolute error floor.

**Mechanism.** The new mechanism is a deliberately slowed linear coupling with weights a_k=(k+1)/(2⁴⁰K^{(2−p)/p}), so the method runs K≈T^{q/(q+2)} iterations. Each iteration uses a robust pilot for a Frank–Wolfe-type primal step and an unbiased fresh mean for the mirror step, with a decaying floor ν=K^{−(2p−1)/p}. This makes the additive cost total (σ₀R/ε)^q rather than √T·(σ₀R/ε)^q.

**Proof ancestry, not checked as baselines.** The stochastic Catalyst framework (Kulunchakov–Mairal 2019) and intermediate gradient methods with relative inexactness ([Kornilov et al., arXiv:2310.00506](https://arxiv.org/abs/2310.00506)) are related. I did not check whether intermediate relative-error methods, combined with median-of-means and absolute-error accumulation, could reproduce this balance. That combination is the main unchecked reduction.

**Search coverage.** I searched on 25 Oct 2026 UTC: arXiv up to October 2026, plus targeted searches for heavy-tailed, affine/multiplicative-noise and accelerated methods. I read the theorem statements of both 2026 preprints and of AGNES Theorem 3. I did not read Nekrasova's Corollary I.2 (exact log powers) or the JOTA version of Kornilov et al. El Bakkali–Gorbunov ([arXiv:2610.23301](https://arxiv.org/abs/2610.23301)) appears to treat additive noise only. The companion note's citations and its regime claims match what I checked.

## Conclusion

**Yes: when the multiplicative noise term dominates, the proved complexity is polynomially better.** The strongest baseline is Clip-SSTM under affine p-th-moment noise (Nekrasova et al., 2026), and Lobanov et al. give the same order:

| | multiplicative term | additive term |
|---|---|---|
| Prior | σ₁^q (LR²/ε)^{q/2} | √T + (σ₀R/ε)^q |
| This result | (1+σ₁)^q (LR²/ε)^{q/(q+2)} | (σ₀R/ε)^q |

The gain holds when σ₁ ≳ 1, σ₀ ≪ σ₁√(Lε) and T is large, with logarithmic factors ignored. For example, take p=3/2 with L=R=σ₁=1, σ₀=η and ε=η^{3/2}: the cost falls from about η^{−9/4} to η^{−3/2}. The result is worse for small σ₁, including pure additive noise (T^{q/(q+2)} vs √T), and it carries log^{q+1} and enormous q-dependent constants. Its problem class is narrower than the competitors', because it assumes global smoothness and finite moments.

The comparison establishes this gain against the checked published bounds. Priority is less certain: both competitors appeared in the five weeks before the result, and I did not check whether an intermediate-gradient reduction could reproduce the balance.

What can be claimed is a new mixed-noise complexity bound that improves the multiplicative-noise exponent from q/2 to q/(q+2) in the regime above.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
