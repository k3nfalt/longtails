# Novelty review: bounded-centre brackets for χ²-constrained DRO

[`ChiSquareBoundedCentreDro.result`](../../LongTails/Theorems/ChiSquareBoundedCentreDro.lean) proves the following ([setup](../../LongTails/Setups/ChiSquareConstrainedDro.lean), [algorithm](../../LongTails/Algorithms/ChiSquareBoundedCentreDro.lean)). Take an arbitrary population law P₀, the χ² ball ½E(w−1)² ≤ ρ, and losses that are convex on a closed convex domain with values in [0,B] and sampled subgradients bounded by G. A minimizer lies within R of x₀. Each call returns the projected point, one fresh IID loss value and one subgradient. The algorithm then returns a feasible point x̂ with E L(x̂) − L(x⋆) ≤ ε, using a deterministic number of calls.

**Complexity.** Here ρ is the radius, B the loss range, G the subgradient bound, R the initial distance and ε the expected excess robust risk. The proved budget, which is 0 if min(B,GR) ≤ ε, is

  N = O( (1+ρ)(G²R² + B²) ε⁻² · log(2 + B/ε) ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Levy–Carmon–Duchi–Sidford, [NeurIPS 2020, arXiv v2](https://arxiv.org/pdf/2010.05893), Thm. 4 (§6): penalty doubling over λ with SGD/MLMC, then selection | G²R²(ρB + ε log(B/ε)) ε⁻³ log²(1+ρB/ε²) ∇ℓ calls (holds w.p. ≥ 1−ε/B; selection cost argued in prose) → (1+ρ)(G²R²+B²) ε⁻² log(B/ε) | ε⁻³ → ε⁻². When ρB ≥ ε and GR ≥ B, the speedup is ≳ ρB/((1+ρ)ε), about B/ε for ρ ≥ 1. **Worse** when B² ≫ G²R²(1+ρB/ε), for example ρ ≤ ε/B and B ≫ GR, by up to a factor B²/(G²R²) | Domain diameter ≤ R → only ‖x₀−x⋆‖ ≤ R, so unbounded domains are covered | Random call count (high probability) → deterministic budget. Output: the same expected-suboptimality criterion | None checked beyond the B²ε⁻² term |
| Repository [`ChiSquareBracketedDro`](../../LongTails/Theorems/ChiSquareBracketedDro.lean) (2026-11-07, same setup) | (1+ρ)(G²R² + B²(1+1/ρ)) ε⁻² log²((1+ρ)B/(√ρ ε)) → (1+ρ)(G²R²+B²) ε⁻² log(B/ε) | Removes the B²/ρ term and one logarithm. Gain factor ≈ (1 + B²/(ρG²R²))·log when ρ ≪ 1. Same order when ρ ≳ 1, GR ≳ B, up to one log | None (identical setup) | Adds a zero-call branch when min(B,GR) ≤ ε | None |
| Carmon–Hausler, [arXiv 2203.13225](https://arxiv.org/pdf/2203.13225), Thm. 3 / Cor. 1 (finite support only) | Õ(N(GR/ε)^{2/3} + (GR/ε)²) with indexed access to N stored losses → not applicable | Not comparable: requires finite N and re-evaluation of stored samples, which a fresh-sample oracle cannot do | Finite empirical P₀ → general P₀ | None | Not comparable |

**Reduction check.** Plugging Levy et al.'s χ²-penalty rate λ⁻¹ε⁻² into λ ≳ ε/ρ simply recovers their ρε⁻³ bound. Naive joint SGD over (x, centre, λ) fails because the x-subgradient v·g has v up to 1+B/λ. The new mechanism is a self-bounding estimate E v² ≲ (Q−L)/λ + ρ + 1, which projected SGD absorbs inside dyadic λ-brackets starting at ε/(8ρ). Clamping the centre to [0,B] removes the B²/ρ term that the sibling theorem carried. A seeded tournament with geometrically growing batches then selects among O(log(B/ε)) candidates. Generic SGD analyses under relative noise ("A + K(f−f⋆)" conditions) are proof ancestry. They do not supply the perspective bound or the bracket design.

**Lower bounds.** The companion note converts Duchi–Namkoong [arXiv 1810.08750](https://arxiv.org/pdf/1810.08750), Thm. 6, into Ω(ρM²/ε²) for ρ > 1/2 with GR ≍ B ≍ M. I did not re-verify that conversion. If it holds, the gap for ρ ≳ 1 and GR ≍ B is one log(B/ε) factor. Whether the separate B²ε⁻² term is necessary at small ρ is open.

**Search coverage (2026-11-26).** I read Levy et al. Thm. 4 and the gap remarks in §§6 and 8 directly from the PDF. I checked Qi et al. ([TMLR 2023](https://arxiv.org/abs/2210.05740)) through the HTML text: its O(ε⁻²) results are KL-only, and its claim that Levy et al. reach Õ(ε⁻²) for the χ² constraint contradicts Levy's own Table 1. From search results and the companion note only (not re-read), I also considered Im–Grigas ([2305.16584](https://arxiv.org/abs/2305.16584), a relaxed set with a coordinate floor and feasibility gap) and Zhang et al. ([AAAI 2024](https://arxiv.org/abs/2404.01200), nonconvex stationarity). No published ε⁻² guarantee for this population problem turned up. The only hit was this repository's own [PR #144](https://github.com/k3nfalt/longtails/pull/144). The companion note's "strictly smaller at every valid parameter" claim refers to the sibling budget; I did not check it in Lean.

## Conclusion

**Yes: compared with the published state of the art, the proved complexity drops from ε⁻³ to ε⁻².** The baseline is Levy et al.'s Theorem 4, whose authors list this gap as open.

| | calls for E L(x̂) − L⋆ ≤ ε |
|---|---|
| Levy et al. | G²R²(ρB + ε log(B/ε)) ε⁻³ · log² |
| This result | (1+ρ)(G²R² + B²) ε⁻² · log(B/ε) |

For ρ ≥ 1 and GR ≈ B, the gain is about a factor B/ε. If Duchi–Namkoong's Ω(ρM²/ε²) bound applies as the note claims, this rate is within one logarithm of optimal. The result loses only when B ≫ GR and ρB/ε is small, where its B²ε⁻² term exceeds Levy's near-ERM cost.

Much of the ε⁻² breakthrough already appeared in this repository's earlier `ChiSquareBracketedDro`. What this theorem adds is removing that result's B²/ρ penalty and one logarithm. That makes the bound robust as ρ → 0 rather than blowing up. The comparison establishes the gain. My search found no prior published ε⁻² result, which supports priority but cannot prove it.

The claimable contribution is a near-optimal Õ((1+ρ)(G²R²+B²)ε⁻²) streaming complexity for χ²-ball DRO with general P₀ and unbounded domains. It is built on a new self-bounding analysis of the perspective weights.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
