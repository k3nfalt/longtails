# Novelty review: RecursiveAffineMomentAcceleration

[`result`](../../LongTails/Theorems/RecursiveAffineMomentAcceleration.lean) proves the following under [`AffineMomentConvex.spec`](../../LongTails/Setups/AffineMomentConvex.lean). Let f be convex and globally L-smooth on a separable Hilbert space, with a minimizer within R of x0. The oracle is IID, unbiased, and jointly measurable, with E‖g−∇f‖^p ≤ σ0^p + σ^p‖∇f‖^p for some 1<p≤2. Under these assumptions, the recursive Moreau-envelope method [`StochasticEnvelope.algorithm`](../../LongTails/Algorithms/StochasticEnvelope.lean) returns a point with P(f(out)−f* > ε) ≤ δ. All raw oracle calls are counted. The method uses the known values of L, R, σ0, σ, and p.

**Complexity.** Write q = p/(p−1) and M = 4 + LR²/ε + (σ0R/ε)^q + 1/δ. The proved budget is exactly

N = (2+q+log M)^{2³²q⁴(1+√log M)} · [(1+σ)^q √(LR²/ε) + 1 + (σ0R/ε)^q] / δ  (trivial when LR² ≤ ε).

For fixed p, the prefactor is M^{o(1)}. Its exponent constant is 2³²q⁴, though, so it falls below even T^{0.1} only once log M ≳ 10^{26}–10^{29}, where T = LR²/ε (computed for q = 2, 3).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/abs/2609.33415) (27 Sep 2026, preprint; **prior**), Thm 9, specialized to H₁=0, σ₂=0 | Õ_δ(√(LR²/ε) + (σ0R/ε)^q + σ^q(LR²/ε)^{q/2}), polylog(1/δ) → N | σ^q T^{q/2} → (1+σ)^q T^{1/2}·M^{o(1)}/δ. For σ ≥ 1 and (σ0R/ε)^q ≤ σ^qT^{q/2}, the gain factor is about T^{(q−1)/2}·δ/M^{o(1)}. The proved bound is smaller only when log M ≳ 10^{26}. For σ ≤ T^{−1/(2p)}, both are √T+V and N is worse | None (their class is broader) | None (both use known parameters and certify the final point) | Confidence cost 1/δ instead of log(1/δ). Astronomically large M^{o(1)} factor. Narrower: no (H₀,H₁)-smoothness or gap-dependent noise |
| Nekrasova et al., [arXiv:2610.28107v1](https://arxiv.org/abs/2610.28107) (20 Oct 2026, preprint; **prior**), Thm 5.2 / Table 1, Clip-SSTM | Õ(√T + (σ0R/ε)^q + (σ²T)^{q/2}), log(1/δ) → N | Same σ-term gain and regimes as row 1. At σ=0 they get √T+V with log(1/δ), so N is worse by M^{o(1)}/δ | None. Their weak-L^α tails strictly contain the moment class | None | Same as row 1. They also allow local smoothness on Q |
| Repository [AffineMomentAcceleration](../../LongTails/Theorems/AffineMomentAcceleration.lean) (introduced 25 Oct 2026; same setup) | 2^{256q}[(1+σ)^q(4+T)^{q/(q+2)} + (σ0(4/(LR)+R/ε))^q]·log^{q+1}(20+q+T+1/δ) → N | Exponent of T goes from max(q/(q+2), v) to max(1/2, v)+o(1), where V = T^v. For p=3/2 that is 0.6 → 0.5+o(1). Crossover near log T ≈ 10^{29} | None | None | Confidence cost 1/δ instead of polylog. Repository result, not literature |

**Reductions and mechanism.** Mini-batching cannot reach the new bound. Averaging n calls scales σ0 and σ by n^{−1/q} (von Bahr–Esseen), so rows 1–2 become n√T + V + σ^qT^{q/2} with no gain. Replacing relative noise by a uniform bound σ0+2σLR on the R-ball gives an additive (σT)^q term. I found no reduction that yields (1+σ)^q√T+V for p<2. The proof's own contribution, which I did not recheck line by line, is an exactly unbiased envelope-gradient oracle. It is built from localized clipped solves, median selection, and randomized multilevel differences, and it keeps the additive/relative noise structure while its additive scale shrinks geometrically across ⌈√log M⌉ levels. The proof ancestry is multilevel debiasing of proximal points ([Asi et al., NeurIPS 2021](https://arxiv.org/abs/2106.09481), Thm 1), Catalyst-style stochastic acceleration (Kulunchakov–Mairal, NeurIPS 2019), and median-of-means. These supply ingredients, not this complexity. The work-capping step (a Markov bound on random work) is what causes the 1/δ. Boosting to log(1/δ) would need an output-selection certificate, and I did not check whether one exists.

**Search coverage.** Searched on 2026-10-26: arXiv 2024–Oct 2026 on heavy-tailed, affine, relative and multiplicative noise with acceleration, NeurIPS/ICML/ICLR proceedings links, and He–Li–Lu ([arXiv:2510.11676v2](https://arxiv.org/abs/2510.11676), additive σ only, bounded domain) and El Bakkali–Gorbunov ([arXiv:2610.23301v2](https://arxiv.org/abs/2610.23301), additive only). I read the theorem statements of rows 1–2 in the HTML versions, not their proofs. I did not check finite-variance state-dependent results (Ilandarideva–Juditsky–Lan–Li) because p=2 is not the claim; [AGNES, NeurIPS 2024](https://papers.nips.cc/paper_files/paper/2024/hash/24d2dd6dc9b79116f8ebc852ddb9dc94-Abstract-Conference.html) covers multiplicative finite variance. The companion note matches the Lean budget and is candid about the 1/δ and σ0=0 caveats. It compares mainly with the repository predecessor and understates how large the M^{o(1)} prefactor is in practice.

## Conclusion

**Yes. Asymptotically, this is a large exponent improvement for heavy-tailed noise with both additive and relative components, but the proved bound is smaller only for astronomically large T and costs 1/δ.**

The strongest prior guarantees under the same affine p-th-moment model are Lobanov–Dvinskikh–Gasnikov (Thm 9) and Nekrasova et al. (Thm 5.2). Both pay σ^q(LR²/ε)^{q/2} for the relative part. This result replaces that with a near-accelerated term:

| | relative-noise term | confidence |
|---|---|---|
| Prior (Sep–Oct 2026 preprints) | σ^q T^{q/2} | log(1/δ) |
| This result | (1+σ)^q T^{1/2} · M^{o(1)} | 1/δ |

For p<2, σ ≥ 1, and fixed δ, this cuts the exponent of T by (q−1)/2; at p=3/2 that is T^{1.5} → T^{0.5+o(1)}. It also beats the repository's own T^{q/(q+2)} bound. Mini-batching and uniform noise bounds do not recover it.

The gain is asymptotic. Because the prefactor exponent is 2³²q⁴√(log M), the proved bound is smaller only when log T exceeds about 10^{26}. When σ is small or zero, existing clipped acceleration is better by M^{o(1)}/δ. The comparison establishes the exponent gain. The search found no prior result giving √T-type dependence under heavy-tailed relative noise, but both main baselines are recent unrefereed preprints, and I did not audit the proofs.

What can be claimed is the first T^{1/2+o(1)} high-probability complexity for smooth convex optimization under heavy-tailed noise with both additive and relative components. It requires known parameters and pays 1/δ confidence and an impractically large subpolynomial overhead.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
