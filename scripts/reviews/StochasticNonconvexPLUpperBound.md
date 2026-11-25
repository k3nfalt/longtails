# Novelty assessment: StochasticNonconvexPLUpperBound

[`result`](../../LongTails/Theorems/StochasticNonconvexPLUpperBound.lean) proves the following. Take a jointly ℓ-smooth function f(x, y), with x in a finite-dimensional space and y in a separable Hilbert space, that is μ-PŁ in y, has an attained inner maximum, and has Φ = max_y f bounded below. Give the algorithm an unbiased, IID, jointly measurable stochastic gradient oracle with total variance σ². Then stochastic Smoothed-AGDA, outputting the auxiliary iterate z_J at a uniformly random index J, achieves E‖∇Φ_{1/(2ℓ)}(z_J)‖ ≤ ε, i.e. E[2ℓ·dist(z_J, prox)] ≤ ε. The setup is [StochasticNonconvexPL](../../LongTails/Setups/StochasticNonconvexPL.lean) and the algorithm is [nonconvexPLSmoothedAgda](../../LongTails/Algorithms/NonconvexPLSmoothedAgda.lean).

**Complexity.** The budget is 2⌈2⁴⁴·ℓ²Δ/(με²)·(1 + ℓσ²/(με²))⌉ stochastic gradient-pair calls, which is

  O( 1 + ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴) ).

The parameters are:
- ℓ: joint gradient Lipschitz constant.
- μ: PŁ constant in y, with 0 < μ ≤ ℓ, so κ = ℓ/μ ≥ 1.
- σ²: oracle variance.
- ε > 0: target accuracy.
- Δ ≥ 2Φ(x₀) − Φ* − f(x₀, y₀) + ‖∇ₓf(x₀, y₀)‖²/ℓ, where Φ* = min_x max_y f. This dominates both the primal gap and the dual gap at (x₀, y₀).

The step sizes use ℓ, μ, σ and ε, and the iteration count also uses Δ.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Yang, Orvieto, Lucchi, He, [arXiv:2112.05604](https://arxiv.org/abs/2112.05604) v1 (Dec 2021; AISTATS 2022), Thm 4.1 for Stoc-Smoothed-AGDA; prior work, same algorithm | O(ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴)) for E[‖∇ₓf‖² + κ‖∇_y f‖²] ≤ ε², which converts to the Moreau criterion at x̂ by the reduction below → O(1 + ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴)) | None: same order | None. Both use the same assumptions (Asm. 2.1–2.3) and the same single-sample oracle | None. Both output a random iterate with an expected stationarity guarantee. Yang outputs x_t; this result outputs z_J, also without post-processing | Yang states its bound with Φ(x₀) − Φ* and a gap term b₀ in place of Δ. Admissibility of using Δ as a common upper bound in Yang's step sizes was not rechecked line by line |
| Yang et al., same paper, Cor. 4.1 (‖∇Φ‖ via an AGDA post-processing stage); prior | Õ(ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴) + ℓ⁵σ²/(μ⁵ε²)) for E‖∇Φ(x̂)‖ ≲ ε → O(1 + ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴)) for the Moreau criterion | Not comparable: different criterion. ‖∇Φ_{1/(2ℓ)}‖ ≤ 2‖∇Φ‖, so the selected criterion is weaker | None | Weaker output criterion | The κ⁵σ²/ε² and log terms are saved only because the target is weaker |
| Huang et al., [arXiv:2303.03984](https://arxiv.org/abs/2303.03984) v4 (AISTATS 2025), Thm 1 (MSGDA); prior | Õ(ε⁻³), with κ factors hidden, for a proximal-gradient-mapping criterion → O(… + ℓ³σ²Δ/(μ²ε⁴)) | Worse in ε (ε⁻⁴ vs ε⁻³) when per-sample smoothness holds | Per-sample ℓ-smooth components (mean-squared smoothness, Asm. 2) → only the expected gradient is ℓ-Lipschitz. This covers oracles whose individual samples are non-smooth | None | Huang's κ exponent is not made explicit. Its criterion differs, and no conversion was checked |

**Standard-reduction check.** The guarantee follows from Yang et al. Theorem 4.1 by a short argument (here ‖d‖ = ‖x − x̄‖):
- Φ is ℓ-weakly convex, so for the proximal point x̄ of x, (ℓ/2)‖x − x̄‖² ≤ [Φ + ℓ‖· − x‖²](x) − [Φ + ℓ‖· − x‖²](x̄).
- By ℓ-smoothness of f(·, y) and PŁ (Φ(x) − f(x, y) ≤ ‖∇_y f‖²/(2μ)), the right side is at most ‖∇_y f‖²/(2μ) + ‖∇ₓf‖‖d‖ − (ℓ/2)‖d‖² ≤ ‖∇_y f‖²/(2μ) + ‖∇ₓf‖²/(2ℓ).
- Hence ‖∇Φ_{1/(2ℓ)}(x)‖² ≤ 4(‖∇ₓf(x, y)‖² + κ‖∇_y f(x, y)‖²), which is exactly Yang's Theorem 4.1 criterion.

Jensen's inequality then gives the selected bound at the same order, with no post-processing. The note's claim that avoiding post-processing is an addition is therefore not a new mathematical step.

The proof ancestry is the Smoothed-AGDA potential of Yang et al. and the smoothing of Zhang et al. ([arXiv:2010.15768](https://arxiv.org/abs/2010.15768)). Within the repository, it reuses the step analysis of [StochasticTwoSidedPLSmoothedAgda](../../LongTails/Theorems/StochasticTwoSidedPLSmoothedAgda.lean) (2026-10-14) with the x-side PŁ assumption removed. I found no genuinely new technical mechanism.

**Search coverage.** The search ran on 2026-11-25 and covered arXiv and proceedings for single-loop and variance-reduced stochastic nonconvex–PŁ minimax methods. I read Yang et al. v1 (HTML) Theorem 4.1, Corollary 4.1 and Tables 1–2. I read the Huang et al. assumptions, Theorem 1 and Table 1; its middle sections were only partly read verbatim. I could not locate or verify the companion note's citation "Ha, arXiv:2610.07814". I did not check the Pan–Li lower bound (arXiv:2608.26799), which bears only on the companion lower bound. The companion note itself states that the rate is Yang et al.'s, which matches this assessment. Its suggestion that the Moreau criterion and the absence of a conversion step add something is overstated, given the reduction above. The theorem was introduced in commit 7b957e92 (2026-11-25), long after Yang et al. (2021).

## Conclusion

**No: this is another proof of a known guarantee, not a complexity or scope improvement.** The strongest baseline is Yang, Orvieto, Lucchi and He's Theorem 4.1 for the same algorithm (stochastic Smoothed-AGDA), under the same assumptions and the same single-sample unbiased oracle.

That theorem bounds E[‖∇ₓf‖² + κ‖∇_y f‖²] at a random iterate. A three-line weak-convexity and PŁ argument shows this quantity dominates (1/4)‖∇Φ_{1/(2ℓ)}‖². So Yang et al. already give the selected criterion at the same order:

  Yang et al. (2021) via the reduction: O(ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴))  →  this result: O(1 + ℓ²Δ/(με²) + ℓ³σ²Δ/(μ²ε⁴)).

The two bounds are the same order in every regime, and neither the information the algorithm needs nor the output type improves. Avoiding the κ⁵σ²/ε² post-processing term of Yang's Corollary 4.1 only reflects the weaker Moreau target. Compared with that corollary, the selected result is strictly weaker in output. One point remains uncertain: I did not recheck line by line that Yang's step sizes admit the single initialization bound Δ. This could change constants, not the order or the verdict.

What can be claimed is a self-contained formal proof, with explicit constants, of Yang et al.'s known Smoothed-AGDA rate for the Moreau criterion. Its value is as the matching upper half for the companion lower bound, not as new mathematics.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
