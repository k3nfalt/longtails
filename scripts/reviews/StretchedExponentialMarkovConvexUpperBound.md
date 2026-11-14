# Novelty assessment: `StretchedExponentialMarkovConvexUpperBound`

[`result`](../../LongTails/Theorems/StretchedExponentialMarkovConvexUpperBound.lean) concerns convex L-smooth f on ℝᵈ (d ≥ 1) with a minimizer within R of x₀ ([setup](../../LongTails/Setups/StretchedExponentialMarkovConvex.lean)). Gradients g(x,ξₜ) come from a stationary real-state Markov chain whose stationary law π makes them unbiased with centered α-moment ≤ σᵅ. The chain also satisfies ∫TV(κᵗ(z,·),π)dπ(z) ≤ exp[−(t/τ)^γ]. Under these assumptions, the clipped, ball-projected accelerated method that uses every m-th sample ([algorithm](../../LongTails/Algorithms/AcceleratedMarkov.lean)) returns its last accelerated iterate y_N with 𝔼f(y_N) − f* ≤ ε.

**Proved budget.** Let k = α/(α−1). Here L is the smoothness constant, R is the initial distance, σ is the noise level with moment order α ∈ (1,2], τ ≥ 1 is the mixing scale with stretch exponent γ ∈ (0,1], and ε is the expected-gap target. The budget is

  U = ⌈√(32LR²/ε) + (256σR/ε)ᵏ⌉ · ⌈eτ(γ⁻¹ log[256LR²/ε + 64(256σR/ε)ᵏ])^{1/γ}⌉.

The valid region is 4ε ≤ LR², 32ε ≤ σR and LR²/ε ≤ (σR/ε)ᵏ, so the deterministic term is dominated and U = O_{α,γ}(τ(σR/ε)ᵏ log^{1/γ}((σR/ε)ᵏ)). The constants 256ᵏ and γ^{−1/γ} are not universal as α→1 or γ→0.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [`AcceleratedHeavyTailedMarkovConvex`](../../LongTails/Theorems/AcceleratedHeavyTailedMarkovConvex.lean) (2026-09-21, prior). Polynomial averaged mixing (1+t/τ_p)^(−β); covers this class through the proved inclusion with τ_p = τ(β/γ)^{1/γ}. | With β = log W, where W = 256LR²/ε + 64(256σR/ε)ᵏ, the inherited budget is N·⌈τ(β/γ)^{1/γ}W^{1/β}⌉ = U exactly → U | None: identical budget, algorithm and output | None. Stretched-exponential averaged mixing is a sub-case of the polynomial class. | None | Narrower: ℝᵈ instead of Hilbert space, plus the noise-dominated regime restrictions |
| Solodkin–Veprikov–Beznosikov, [arXiv:2408.01848](https://arxiv.org/abs/2408.01848) v2, Thm 2/Cor 2 (as read in the repository's earlier review). **Special case:** γ = 1, α = 2, noise ≤ σ a.s., uniform geometric mixing. | Õ(√(LR²/ε) + τσ²R²/ε²) → O(τ(σR/ε)² log(σR/ε)) | None established. Since LR²/ε ≤ (σR/ε)², both are τσ²R²/ε² up to logarithms. I did not recheck the log power hidden in Õ. | Bounded noise, uniform mixing → α-moment under π, averaged stretched-exponential mixing. The classes are incomparable, because Solodkin et al. also cover non-Euclidean geometry. | None | The deterministic term pays τ·log. The paired lower bound does not apply to their stronger model. |
| Duchi et al., ergodic mirror descent, [arXiv:1105.4681](https://arxiv.org/abs/1105.4681) (SIAM J. Optim. 2012), Thm 1/(12). **Special case:** ‖g‖ ≤ G a.s., uniform mixing, no smoothness required. | With τ_TV(δ) = τ log^{1/γ}(1/δ): O(τ(GR/ε)² log^{1/γ}(GR/ε)) for the averaged iterate → O(τ(GR/ε)² log^{1/γ}(GR/ε)), since σ ≤ 2G at α = 2 | None: same order | Bounded gradients, uniform mixing → α-moment, averaged mixing. The classes are incomparable. | Averaged iterate → last iterate | Requires smoothness and a stationary start |

**Reduction check and proof ancestry.** The proof is literally a standard reduction. [`StretchedExponentialMarkovInclusion`](../../LongTails/Proofs/StretchedExponentialMarkovInclusion.lean) proves exp[−(t/τ)^γ] ≤ (1+t/(τ(β/γ)^{1/γ}))^{−β}, and [`StretchedExponentialUpper.transfer`](../../LongTails/Proofs/StretchedExponentialUpper.lean) applies the earlier theorem at β = log W, using W^{1/log W} = e. The earlier theorem itself composes data dropping, clipping and projected similar triangles. No new mechanism appears here.

**Search coverage.** I searched on 2026-11-14 UTC in arXiv and general web search for Markov, subgeometric, stretched-exponential, heavy-tailed and clipped convex SGD. I found no prior convex heavy-tailed Markov guarantee under stretched-exponential mixing. Debavelaere et al. ([EJS 2021](https://projecteuclid.org/journals/electronic-journal-of-statistics/volume-15/issue-1/On-the-convergence-of-stochastic-approximations-under-a-subgeometric-ergodic/10.1214/21-EJS1827.full)) give asymptotic convergence only. The CVaR preprint ([arXiv:2602.18053](https://arxiv.org/abs/2602.18053)) gives statistical risk bounds, not oracle complexity. In this session I did not re-read the full theorem texts of Solodkin et al. or Duchi et al.; those rows rely on the repository's earlier review. The [companion note](../../LongTails/Theorems/StretchedExponentialMarkovConvexUpperBound.md) already calls this result a "proved specialization" and credits any novelty to the paired lower bound. That is consistent with the Lean proof.

## Conclusion

**No: this is a direct corollary of the repository's existing polynomial-mixing theorem, with an identical budget.**

Stretched-exponential averaged mixing implies polynomial averaged mixing for every exponent β. Choosing β = log W in [`AcceleratedHeavyTailedMarkovConvex`](../../LongTails/Theorems/AcceleratedHeavyTailedMarkovConvex.lean) reproduces exactly

  U ≍ τ(σR/ε)^{α/(α−1)} · log^{1/γ}((σR/ε)^{α/(α−1)})  (noise-dominated regime).

The algorithm, tuning and output are inherited unchanged. The only new work is a one-line envelope inequality and the algebra that removes `max 1`.

On the overlaps with the literature, the bound matches known rates up to logarithms. These are Solodkin et al. for bounded noise with geometric mixing, and Duchi et al. for bounded gradients with averaged output. Neither covers the heavy-tailed, averaged-mixing class, but that scope gain was already supplied by the earlier repository theorem. Its value here is as the matching upper half of the paired lower bound, which is a separate contribution not assessed in this report.

The claimable contribution is a formal specialization that makes the tightness pair explicit, not a new optimization guarantee.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
