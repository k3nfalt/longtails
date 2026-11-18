# Novelty assessment: DistributedWeightedInterpolation

The [theorem](../../LongTails/Theorems/DistributedWeightedInterpolation.lean) works in a coordinator–worker star with per-call compute times `hᵢ`, latency `ℓ` and per-bit cost `b` ([setup](../../LongTails/Setups/DistributedWeakInterpolation.lean)). Each `fᵢ` is convex and `Lᵢ`-smooth, and the `fᵢ` share a minimizer set `S` within distance `R` of `x₀`. The average `f` has quadratic growth `μ` relative to `S`, and the stochastic gradients are unbiased with variance `σ²`. Under these assumptions the actual execution of speed-weighted two-phase minibatch SGD ([algorithm](../../LongTails/Algorithms/WeightedInterpolationSgd.lean), [weights](../../LongTails/Algorithms/WeakInterpolationDesign.lean)) returns the fixed-index iterate `x_{2J}` with `E dist(x_{2J},S)² ≤ ε` within the elapsed-time budget below.

**Proved time.** Let `c ≥ 0` solve `Σᵢ min(Lᵢ, c hᵢ) = nμ`. This threshold is implicit, but it is computed by sorting the breakpoints `Lᵢ/hᵢ`. Write `uᵢ = min(Lᵢ, c hᵢ)` and `H = maxᵢ hᵢ`. The proved time is

```
T = O( σ² / (ε Σᵢ uᵢ²/hᵢ)
     + K · (1 + log(1 + R²/ε)) · (H + ℓ + b d log(2 + d + K + (R² + σ²(maxᵢuᵢ)²/(maxᵢuᵢLᵢ)²)/ε)) ),
K = 2 (maxᵢ uᵢLᵢ)(Σⱼ 1/hⱼ) / (Σᵢ uᵢ²/hᵢ).
```

The updates need `Lᵢ, μ, hᵢ, σ, R, ε`, so the method is not adaptive.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Malenia SGD, [Tyurin 2609.17483v1, Thm F.2](https://arxiv.org/abs/2609.17483) (prior, Sep 2026). It needs only global smoothness `L̄ = mean Lᵢ` and global PL, so it covers our class via convex QG ⇒ PL up to constants. | At `ℓ = b = 0`: `O((H L̄/μ + σ²Σhᵢ/(n²μ²ε)) log(R²/ε))` → `T` above | **Uncapped profile** (`c hᵢ ≤ Lᵢ` for all i): the statistical terms are equal, since `Σuᵢ²/hᵢ = (nμ)²/Σh`, and only the `log(R²/ε)` factor on that term is removed.<br>**Capped profile:** the statistical term is smaller by `(Σuᵢ²/hᵢ)·Σh/(nμ)²`, which can be unbounded. Example: N workers with `h = 1`, N with `h = s ≥ 2`, `Lᵢ = 1`, `μ = 3/4`. Then `O((s + σ²s/(Nε)) log(R²/ε))` → `O(σ²/(Nε) + s log(1 + R²/ε))`. | None: Malenia's class contains ours (weak interpolation is an extra restriction) | None. Both give distance-to-solution-set accuracy for a fixed iterate | Needs weak interpolation and per-worker `Lᵢ`.<br>Initialization term can be worse: in the uncapped equal-`L` case `K H = 2H·mean(1/hⱼ)·(H L/μ)`, so it is larger by a factor `2H·mean(1/hⱼ)` (between 2 and `2H/minⱼhⱼ`). At `σ = 0` this is a pure loss.<br>Charges communication, which Malenia does not model. |
| Rennala-type weighted SGD, [same paper, Thm 3.8](https://arxiv.org/abs/2609.17483) | Only on the overlap with strong interpolation plus local PL: `O(min_m (m⁻¹Σ_{i≤m}1/hᵢ)⁻¹(L_max/μ + σ²/(mμ²ε)) log(R²/ε))` → `T` | Worse on that overlap. Example: one worker with `h = 1`, the rest with `h = s ≫ n`, and `μ < L/(2n)`; ours is larger by a factor `≈ s/n`. | Strong interpolation plus local PL → weak interpolation plus aggregate growth. Instances whose local functions are degenerate (no local PL) become covered. | None | Thm 3.8 does not cover our class. Thms 3.6–3.7 show its harmonic time is impossible without those assumptions. |
| Lower bound, [same paper, Thm 3.2](https://arxiv.org/abs/2609.17483) (regime `μ < L_max/(2n)`; read only through an extracted summary) | Necessary time `Ω(σ²Σhᵢ/(n²μ²ε))` | Matched in that regime. With equal `Lᵢ` the profile there is uncapped. | — | — | The selected result exceeds this bound only outside its regime. |

**Reduction check.** Under weak interpolation, any positively weighted sum `Σwᵢfᵢ` keeps `S` as a common minimizer set. The rest of the proof is standard minibatch SGD with batches proportional to `1/hᵢ`, followed by a constant-step phase and then a decreasing-step phase. The decreasing phase removes the logarithm in the usual way (Stich-type schedules). The missing step is not standard: a water-filling choice of weights gives the reweighted sum quadratic growth `Σuᵢ²/hᵢ` relative to `S`, even though each local gap profile may vary by direction. I found this lemma in neither Malenia's analysis nor Tyurin's Section 3. The proof ancestry (Malenia's batching and the SGD recurrences) supplies only the stochastic-descent part.

**Search coverage.** The search was run on 2026-11-18 over arXiv 2024–2026 and over Tyurin–Richtárik, Rennala/Malenia, Ringmaster/Ringleader, Rescaled ASGD and DuDe-ASGD. Appendix F of 2609.17483 was read verbatim. Its Section 3 statements (Thms 3.2 and 3.6–3.8) were read only through an extracted summary and remain unverified. Git dates the result to commit `0ef42e47` (2026-11-18 UTC), so the preprint is prior work. The companion note's own lower bound for the capped regime is an informal derivation, not formalized, and I did not verify it.

## Conclusion

**Yes. When the smoothness caps bind, the statistical time is better than the strongest applicable baseline, and the gain can be polynomial.** That baseline is Malenia SGD (Tyurin, Thm F.2), which already applies to this class:

| Regime (`ℓ = b = 0`) | Malenia | This result |
|---|---|---|
| Uncapped (e.g. `μ < L/(2n)` with equal `L`) | `(HL̄/μ + σ²Σh/(n²μ²ε)) log(R²/ε)` | same statistical term without the log |
| N workers with `h = 1`, N with `h = s`, `L = 1`, `μ = 3/4` | `(s + σ²s/(Nε)) log(R²/ε)` | `σ²/(Nε) + s log(1 + R²/ε)` |

In the uncapped regime the result only removes a logarithm, and Tyurin's lower bound shows that nothing better is possible there. The gain appears when `μ` is comparable to the `Lᵢ` or when the `Lᵢ` differ, so that slow workers cannot carry their proportional share of curvature. It then requires `σ²/(Nε) ≳ s log(R²/ε)`.

The losses are real: the initialization term can be up to `H/min h` times worse, so the deterministic case (`σ = 0`) is slower. It is also worse than Tyurin's Thm 3.8 wherever strong interpolation and local PL hold. The comparison shows the gain over Malenia; the literature search supports priority but does not establish it. Tyurin's Section 3 was checked only through a summary, and no matching lower bound has been verified for the capped regime.

What can be claimed: under weak interpolation with only aggregate quadratic growth, smoothness-capped speed weighting improves the variance-dominated time over Malenia SGD whenever the caps bind.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
