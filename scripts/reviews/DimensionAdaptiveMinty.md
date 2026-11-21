# Novelty assessment: DimensionAdaptiveMinty (upper bound)

[`result`](../../LongTails/Theorems/DimensionAdaptiveMinty.lean) proves the following. Take any dimension d ≥ 1, any L-Lipschitz F: ℝᵈ→ℝᵈ with a root z satisfying ‖z−x₀‖ ≤ R and ⟨F(x),x−z⟩ ≥ −ρ‖F(x)‖², where 0 ≤ ρL ≤ 1/20 and 0 < ε < LR. A deterministic algorithm then returns a queried point with ‖F(x̂)‖ ≤ ε on every run (so also in expectation), using 2⌈1024 d log(1+L²R²/(dε²))⌉ exact operator evaluations. Sources: [setup](../../LongTails/Setups/FiniteDimensionalWeakMinty.lean), [base predicates](../../LongTails/Setups/EuclideanWeakMinty.lean), [algorithm](../../LongTails/Algorithms/DimensionAdaptiveMinty.lean).

**Complexity** (d is the dimension, L the Lipschitz constant, R the bound on the distance from x₀ to the root, ε the residual target):

$$N = O\!\left(d\,\log\!\left(1+\frac{L^2R^2}{d\,\varepsilon^2}\right)\right)\quad\text{for } \varepsilon<LR.$$

This is O(L²R²/ε²) when d ≥ L²R²/ε², and O(d log(LR/(ε√d))) when d is smaller. The updates need L, ε, R and d (d and t = LR/ε also decide which branch runs). Centroids of a soft-cut density are computed by exact integration; their arithmetic cost is not bounded.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| EG+ for weak MVI: Diakonikolas–Daskalakis–Jordan, [AISTATS 2021, Thm 3.2](https://proceedings.mlr.press/v130/diakonikolas21a/diakonikolas21a.pdf); repo version [EuclideanWeakMintyExtragradient](../../LongTails/Theorems/EuclideanWeakMintyExtragradient.lean) | O(L²R²/ε²) → O(d log(1+L²R²/(dε²))) | Better whenever d ≤ L²R²/ε². The gain is a factor of order t²/(d log(1+t²/d)), with t = LR/ε. For d ≥ L²R²/ε²: none, same order | None. The repo version needs d ≥ 257 and 28ε ≤ LR, but that is a formalization artifact, not a gap in the literature | None. Both return a queried point; the best-iterate EG residual is observable, so it can be selected | ρL ≤ 1/20 is narrower than the range allowed by DDJ’s EG+ analysis (its exact constant was not re-verified here). Each round needs an exact high-dimensional centroid; EG has O(d) arithmetic per step |
| Standard composition: DDJ-style look-ahead separating cut (cf. [Anagnostides et al., v4 §4.2–4.3, Lemma 4.12 per companion note, not re-read](https://arxiv.org/html/2504.03432v4)) + center of gravity, with the better of this and EG chosen by d vs t² | O(min{L²R²/ε², d log(2+LR/ε)}) → O(d log(1+L²R²/(dε²))) | None (≤ constant factor) unless d ≥ (LR/ε)^{2−o(1)}. Best case is d ≍ t²/log t: t² → t² log log t / log t, a gain of order log t/log log t (≈ 5× at t = 10⁶, small next to the constant 2048) | None | None | Same exact-centroid cost. A hard centroid cut also needs exact centroids |

**Ratio check.** Write d = t²/s with s ≥ 1. The baseline over this result is min(s, log t)/log(1+s). That is O(1) for s ≤ t^{o(1)} unless s is near log t, and it peaks at Θ(log t/log log t). If d ≤ t^{2−δ}, both bounds are Θ_δ(d log t).

**Reduction check and proof ancestry.** A failing query gives a cut with the root at depth a = ε/(16L) ([separation lemma](../../LongTails/Proofs/MintySeparatingCut.lean)). The ball B(z,a) survives every such cut, so plain center of gravity already gives d log(t). The √d inside the logarithm instead comes from three pieces: continuous exponential weights on hinge losses, a comparator that is uniform on a ball of radius a√d/16 (its directional variance is about a²/d), and Grünbaum's bound. Each piece is standard in exponential-weights regret analysis and cutting-plane theory. I found no published statement of this combined bound for operator root finding or for margin-feasibility, but I did not prove that it is absent from the learning-theory literature (online learning of margin halfspaces).

**Search coverage (21 Nov 2026 UTC).** I checked DDJ 2021; Anagnostides–Farina–Sandholm–Zhang (arXiv 2504.03432 v4, 2 Oct 2026, to appear at FOCS 2026: poly(d, log(B/ε), log L), constrained SVI gap, d enters polynomially); Soleymani–Farina–Jaillet ([arXiv 2611.11691](https://arxiv.org/abs/2611.11691), NeurIPS 2026: resolvent oracle, O(d² log) and d log(dR²/(ηε)), not this oracle model); Blanchard–Zhang–Jaillet ([2306.10096](https://arxiv.org/abs/2306.10096)) and Blanchard ([2404.06720](https://arxiv.org/abs/2404.06720)), which state Θ(d log 1/ε) feasibility complexity only for ε ≤ 1/√d; and Lobel et al. (Prop. 3.1, as cited in the companion note). Some later sections of these papers were read only through summaries. I did not resolve whether the Littlestone dimension of margin halfspaces is known to be min(1/γ², d log(1/(γ√d))). The companion note's description of DDJ and Anagnostides et al. agrees with what I checked. Its novelty claim (a "sharp joint dimension and accuracy rate") depends on the paired [lower bound](../../LongTails/Theorems/DimensionAdaptiveMintyLowerBound.lean), which I did not audit. Both theorems entered in commit dbb83b0d (21 Nov 2026). I did not run a build or the comparator.

## Conclusion

**Yes, but only slightly: the gain over the obvious combination of known methods is at most a log t/log log t factor, in a narrow range of dimensions.**

The strongest baseline takes the better of extragradient (DDJ Theorem 3.2) and center-of-gravity cuts built on the standard look-ahead separation:

$$\min\{L^2R^2/\varepsilon^2,\; d\log(2+LR/\varepsilon)\}\;\to\; d\log(1+L^2R^2/(d\varepsilon^2)).$$

These agree up to constants unless (LR/ε)^{2−o(1)} ≤ d ≤ (LR/ε)². At d ≍ t²/log t the speedup is Θ(log t/log log t), with the same class, oracle, and accuracy criterion. The price is exact centroid computation, plus a smaller weak-Minty allowance ρL ≤ 1/20.

What the comparison proves is a strict but sub-logarithmic gain, obtained with standard tools: exponential weights with a larger comparator ball, and Grünbaum's bound. The bound's main interest is that it is the matching upper half of the dimension-sharp characterization claimed by the paired lower-bound theorem. That pairing, not this upper bound alone, carries most of the significance, and I assessed it only from its statement. I found no prior statement of d log(1+t²/d) for this problem, but the learning-theory analogue (margin halfspaces) was not fully checked.

The claim this result supports is a new, slightly tighter upper bound that closes a log t/log log t gap near d ≈ t². By itself it is a modest step.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
