# SCENT for compositional entropic risk: a moment-ratio complexity bound

[`result`](../../LongTails/Theorems/ScentCompositionalEntropicRisk.lean) shows that SCENT ([algorithm](../../LongTails/Algorithms/Scent.lean)) with constant steps, `B` sequential with-replacement anchor draws per iteration, and averaged output `w̄` reaches `E[F_CERM(w̄) − F_CERM(w⋆)] ≤ ε` ([setup](../../LongTails/Setups/CompositionalEntropicRisk.lean)). Here `F_CERM(w) = (1/n)Σᵢ log E e^{sᵢ(w;ζ)}`. The scores are convex in `w` with values in `[c₀,c₁]`, and the oracle draws the anchor uniformly.

**Parameters.** `Δ = c₁ − c₀` is the score range, `G²` bounds `E‖∇sᵢ‖²`, and `κ` bounds `E e^{2s}/(E e^s)²`. `σ²` (the paper's `σ′²`) bounds `E[e^{2s}‖∇s‖²]/(E e^s)²`. `R ≥ ‖w₀ − w⋆‖`, `n` is the number of anchors, and `B ≥ 1` is the batch size. The proved budget `(B+1)⌈…⌉` counts every sample call (one anchor, two samples) and every projection call. It gives

```
N = O( B + [ (B+1)κG²R²(1+e^Δ ε) + (e^Δ min(σ², e^Δ G²) R² + n e^Δ (1+(1+Δ)(κ−1)))(1+ε) ] / ε² ).
```

Oracle calls are minimized at `B = 1`. Larger `B` reduces only the iteration count, toward `κG²R²/ε²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SCENT, Wei–Zhou–Wang–Lin–Yang, [arXiv 2602.02877](https://arxiv.org/abs/2602.02877) (v1 Feb 2026, v2 Jun 2026, ICML 2026), Thm 3.6, with Assumption 4.1's constants substituted into its `σ_t², δ_t²` (our derivation; prior work, direct competitor) | Calls at `B=1`: `O([e^{2Δ}min(σ²,G²)R² + n(1+Δ)e^{2Δ}min(κ−1,1)]/ε² + ne^Δ/ε)` → `O([κG²R²(1+e^Δε) + e^Δ min(σ²,e^ΔG²)R² + ne^Δ(1+(1+Δ)(κ−1))]/ε²)` | Primal term divided by up to `e^Δ` when `κG² ≤ e^Δσ² ≤ e^{2Δ}G²`. Anchor term divided by `≈ e^Δ(1+Δ)min(κ−1,1)/(1+(1+Δ)(κ−1))`, a gain when `(1+Δ)(κ−1)e^Δ ≫ 1` and `ε ≤ e^{−Δ}`. **Worse** when `(1+Δ)(κ−1)e^Δ ≪ 1` and `n ≫ e^ΔG²R²`: at `κ=1`, `ne^Δ/ε` becomes `ne^Δ/ε²` | None: same assumptions (the constants `κ, σ` always exist with `κ ≤ e^Δ`, `σ ≤ e^ΔG`) | None: same averaged output, same expected gap; both tunings need the constants | Batch is with replacement and sequential, not the paper's uniform subset (identical at `B=1`). Extra burn-in term `e^ΔκG²R²/ε` |
| Joint projected SGD on the min–min form over `W×[c₀,c₁]ⁿ` (robust SA, Nemirovski–Juditsky–Lan–Shapiro, SIAM J. Optim. 2009, §2.2; a standard reduction) | `O(e^{2Δ}(GR + √n Δ)²/ε²)` → as above | Gain at least as large as against SCENT Thm 3.6, which already improves `nΔ²` to `n(1+Δ)` | None | None | None beyond the row above |

**Reduction check and proof ancestry.** Substituting `Var(z) ≤ (κ−1)m²` and `σ_t² ≤ e^{2Δ}σ²` into Thm 3.6 yields only the first row's "previous" bound. The `e^Δ` savings need two steps that the paper leaves open for `n ≥ 2` (§4 closes them only for `n=1` or a fixed `w`; Lemma 4.2 is quadratic in the gap). The first is a variance bound that grows only linearly with the suboptimality gap, applied to the "virtual" dual coordinates. The second is a bias-to-dual-gap inequality. Together they close the recursion `Σ gap ≤ X + ½Σ gap`. Self-bounding variance is a familiar device, but we did not find it applied to this problem. Thm 3.6 and Lemma 3.5 (the dual-regret lemma, reproved per sub-step) are proof ancestry, not a competing bound.

**Example (checked).** Take `sᵢ(w;ζ) = ⟨aᵢ,w⟩ + u(ζ)⟨bᵢ,w⟩` with `u = ±1` (Rademacher), `‖aᵢ‖, ‖bᵢ‖ ≤ 1`, and `W` the ball of radius `r`. This instance has `Δ = 4r`, `κ ≤ 2`, `G² ≤ 2`, `σ² ≤ 4` and a nonlinear objective `⟨aᵢ,w⟩ + log cosh⟨bᵢ,w⟩`. For `ε ≤ e^{−Δ}`, both terms improve by a factor of order `e^Δ = e^{4r}`.

**Other methods (not comparable).** BSGD (Hu et al., NeurIPS 2020) and MLMC (Hu–Chen–He, NeurIPS 2021) give `n`-free bounds. They need many samples from a chosen anchor, and MLMC also needs smooth scores; this oracle supplies neither. ALEXR (ICML 2025) needs convex outer functions, and MSVR needs smoothness.

**Search coverage.** On 2026-10-22 we searched arXiv, ICML 2026 and the general web for SCENT follow-ups and for κ-dependent CERM, KL-DRO and LogSumExp analyses. We read SCENT's Thm 3.6, Lemmas 3.4, 3.5 and 4.2, Thms 4.3 and 4.5, and the definitions of `σ_t, δ_t`. We did not read BSGD, MLMC or ALEXR in full. The theorem entered this repository in commit `754cdc2` (2026-10-22). We found no later or competing κ-explicit joint bound.

The companion note's comparison is too weak. It instantiates Thm 3.6 with `e^{2c₁−c₀}/4` instead of `(κ−1)`, so it overstates the gain in the anchor term as `κ → 1`. It also misses the `κ ≈ 1` regime where SCENT's own Thm 3.6 bound is better. In addition, the note calls MSVR's arXiv 2609.15723 a "revision"; it is a v1 posted in September 2026.

## Conclusion

**Yes, in a large parameter regime the proved oracle complexity is better, by a factor of up to about `e^Δ`, but the gain is not uniform.** The baseline is SCENT's own Theorem 3.6, strengthened by plugging in the paper's moment constants `κ, σ`. The algorithm, assumptions, averaged output and accuracy criterion are all the same.

| term (calls at `B=1`, ×ε⁻²) | Thm 3.6 + κ,σ | this result |
|---|---|---|
| primal | `e^{2Δ}min(σ²,G²)R²` | `κG²R² + e^Δ min(σ², e^ΔG²)R²` |
| anchors | `n(1+Δ)e^{2Δ}min(κ−1,1)` (+`ne^Δ ε`) | `ne^Δ(1+(1+Δ)(κ−1))` |

The gain holds when scores vary within each anchor (`(1+Δ)(κ−1)e^Δ ≫ 1`), when `κG² ≲ e^Δσ²`, and when `ε ≤ e^{−Δ}`. The linear-score example above gains a factor of about `e^{4r}`. The new bound loses for nearly deterministic scores (`κ ≈ 1`) with many anchors (`n ≫ e^ΔG²R²`): there the anchor term worsens from `ne^Δ/ε` to `ne^Δ/ε²`.

The comparison establishes the gain. The literature search found no prior κ-explicit joint bound, but it cannot rule one out. SCENT is also the strongest end-to-end method we found for this oracle. Because both tunings use known constants, a user can run whichever bound is smaller, so the new regime adds to the best available guarantee. The remaining uncertainty is about priority; we did not rebuild or re-audit the Lean proof.

What can be claimed is a new analysis of SCENT for `n ≥ 2`. It turns exponential `e^{2Δ}` factors into moment-ratio factors with a single `e^Δ`, with the same `ε⁻²` rate and `n/ε²` structure, and it is worse when `κ ≈ 1`.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
