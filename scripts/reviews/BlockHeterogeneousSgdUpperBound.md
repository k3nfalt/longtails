# Novelty assessment: BlockHeterogeneousSgdUpperBound

The [theorem](../../LongTails/Theorems/BlockHeterogeneousSgdUpperBound.lean) concerns a differentiable `f` on `ℝ^d` with an arbitrary partition into `B` blocks. `f` satisfies the two-sided block bound `|f(y)−f(x)−⟨∇f(x),y−x⟩| ≤ ½Σ_j L_j‖P_j(y−x)‖²` and `f(x₀)−inf f ≤ Δ` ([setup](../../LongTails/Setups/BlockHeterogeneousNonconvex.lean)). The oracle is an IID, jointly measurable, unbiased stochastic gradient with per-block variance `≤ σ_j²`. Under these assumptions, SGD with block step sizes `η_j = 1/(L_j + β(L_jσ_j²)^{1/3})` and a uniformly sampled iterate as output ([algorithm](../../LongTails/Algorithms/BlockSgd.lean), [tuning](../../LongTails/Proofs/BlockSgdConvergence.lean)) achieves `E Σ_j‖P_j∇f(x̂)‖ ≤ ε`. The theorem holds for every `L_j>0`, `σ_j≥0`, `Δ≥0`, `ε>0`.

**Complexity.** The proved budget is `⌈8‖L‖₁Δ/ε² + 20S³Δ/ε⁴⌉ + 1` stochastic-gradient calls, i.e.

  `O( 1 + (Σ_j L_j)Δ/ε² + (Σ_j L_j^{1/3}σ_j^{2/3})³ Δ/ε⁴ )`.

Here `L_j` is the block smoothness constant, `σ_j` the block noise level, `Δ` the initial gap, and `ε` the target sum of block-gradient norms. The method needs all of `L_j, σ_j, Δ, ε`. By Hölder's inequality, `S³ := (Σ_j L_j^{1/3}σ_j^{2/3})³ ≤ ‖L‖₁‖σ‖₁²`, with equality iff `L_j ∝ σ_j`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| AdaGrad, [Jiang–Maladkar–Mokhtari, COLT 2025, Thm 3.1/Eq. 14](https://arxiv.org/abs/2406.04592) (v3, Jun 2025). **Applies only to blocks of size 1** | `Õ(‖L‖₁Δ/ε² + ‖L‖₁‖σ‖₁²Δ/ε⁴ + ‖σ‖₁⁴/ε⁴)` → `O(1 + ‖L‖₁Δ/ε² + S³Δ/ε⁴)` | Noise term `‖L‖₁‖σ‖₁²` → `S³`; drops `‖σ‖₁⁴/ε⁴` and the log. Gain when `max(S³, ‖L‖₁ε²) ≪ ‖L‖₁‖σ‖₁²` or `‖σ‖₁⁴ ≫ max(S³Δ, ‖L‖₁Δε²)` | Coordinates → arbitrary blocks | None for output (average ≡ random iterate) | Prior updates use no `σ_i`; the stated rate's `η` uses `Δ, ‖L‖₁`. This result needs `L_j, σ_j, Δ, ε`. Jiang Thm 3.2 shows AdaGrad's own lower bound already contains `S³`, so no separation from AdaGrad is proved |
| SignSGD, [Tao–Yu–Zhang, arXiv 2605.06615 v1, Thm 1, Eq. 9](https://arxiv.org/abs/2605.06615) (May 2026). **Applies only to blocks of size 1**, via separable ⇒ ℓ∞ smoothness with `L∞ = ‖L‖₁` (Lemma 1) | `O(‖L‖₁Δ/ε² + ‖L‖₁‖σ‖₁²Δ/ε⁴)` calls including batches → `O(1 + ‖L‖₁Δ/ε² + S³Δ/ε⁴)` | Factor `‖L‖₁‖σ‖₁²/S³` on the noise term. Example: `B/2` blocks `(L,s)` and `B/2` blocks `(L/B³, Bs)` give a ratio `≍ B²` | Coordinates → blocks. ℓ∞ smoothness → block-diagonal two-sided bound (incomparable classes) | None | Both are tuned. Prior needs only `L∞` and `‖σ‖₁`, not per-coordinate `L_i, σ_i` |
| LANTON, [Hao et al., arXiv 2510.14009 v2, Thm 5.3](https://arxiv.org/abs/2510.14009) (Feb 2026). Layer-wise; **requires a.s. bounded noise** `‖noise_j‖ ≤ σ̄_j` | `Õ(‖L‖₁Δ/ε² + ‖L‖₁‖σ̄‖₁²Δ/ε⁴ + ‖σ̄‖₁⁴/(‖L‖₁Δε²))` with `log(T/δ)` → (taking `σ_j = σ̄_j`) `O(1 + ‖L‖₁Δ/ε² + S̄³Δ/ε⁴)` | Same noise-term factor `‖L‖₁‖σ̄‖₁²/S̄³`, and no logarithms | Almost-sure per-layer noise bound → per-block variance | **Worse output**: the prior bound holds with probability ≥ 1−δ, while this one is in expectation | Prior is noise-adaptive (uses `Δ, ‖L‖₁`, not `σ̄`); general layer norms. This result needs `σ_j` |

At `B = 1`, the bound reduces to the optimal `LΔ/ε² + LΔσ²/ε⁴` of [Ghadimi–Lan 2013](https://arxiv.org/abs/1309.5549) and [Arjevani et al. 2023](https://arxiv.org/abs/1912.02365). Single-step SGD, measured in the `ℓ_{2,1}` criterion via `Σ_j‖a_j‖ ≤ √B‖a‖`, costs `O(B·maxL·Δ/ε² + B²·maxL·‖σ‖₂²Δ/ε⁴)`, which is never better here.

**Standard-reduction check.** Running Ghadimi–Lan's analysis in rescaled coordinates `y = D^{-1/2}x` gives the noise term `(max_j L_jτ_j)(Σ_j τ_jσ_j²)` instead of `Σ_j L_jτ_j²σ_j²`. I checked this with `L = (1,ℓ)`, `σ = (s,0)`: the rescaled bound is at least `ℓs²Δ/ε⁴` for every choice of steps `τ`, while `S³ = s²`. The bound is therefore not a substitution corollary. The actual proof is nevertheless routine: the descent inequality is the setup assumption itself (the ESO form used in block-coordinate methods), and Cauchy–Schwarz and Hölder tuning do the rest. No new mechanism is involved; the proportional allocation `∝ (L_jσ_j²)^{1/3}` already appears in Jiang et al.'s Thm 3.2 lower-bound construction.

**Search coverage.** The search was run on 2026-11-19. It covered arXiv and venue pages for Jiang et al., Liu–Pan–Zhang ([2406.15244](https://arxiv.org/abs/2406.15244), coordinate-wise, scalar-step SGD baseline only), Gluon ([2505.13416](https://arxiv.org/abs/2505.13416), single `σ`), Hao et al., Tao et al., Jin ([2608.09004](https://arxiv.org/abs/2608.09004), Euclidean, single `σ`), and general searches for per-coordinate or layer-wise tuned SGD. None of these sources states an `S³` upper bound. The search did not verify Gluon's Appendix D or the non-Euclidean normalized-momentum rates (Kovalev, Scion). Those rates should be `‖L‖₁‖σ‖₁²`-type, but this is unchecked. The companion note's citations and its comparisons match what I found. The theorem was introduced in commit `24ba0905` (2026-11-19); every cited work predates it.

## Conclusion

**Yes, the proved complexity beats every published bound I checked, but the derivation is short and standard.** The strongest comparable baselines are AdaGrad (Jiang et al., coordinate case), tuned SignSGD (Tao et al.) and LANTON (Hao et al., layer-wise). All three pay `‖L‖₁‖σ‖₁²` in the noise term:

| | Noise term (calls) |
|---|---|
| Prior best checked | `‖L‖₁‖σ‖₁² Δ/ε⁴` |
| This theorem | `(Σ_j L_j^{1/3}σ_j^{2/3})³ Δ/ε⁴` |

The two coincide when `L_j ∝ σ_j`, and the gain can be a factor of `B²` when smoothness and noise are misaligned across blocks. The deterministic term `‖L‖₁Δ/ε²` is unchanged.

The tradeoff is that the step sizes require `L_j`, `σ_j`, `Δ` and `ε`. AdaGrad and LANTON are noise-adaptive, and LANTON also gives a high-probability guarantee. This result therefore does not show that those methods are actually worse. The block model with per-block variance is a reasonable generalization of the coordinate model in those papers.

The proof is the textbook descent inequality with a diagonal step, followed by Cauchy–Schwarz and Hölder tuning. Naive rescaling of Ghadimi–Lan does not reproduce it, but nothing in it is technically new. I found no prior statement of this bound, but the literature search alone does not establish priority. The result matters mainly as the achievability half of the companion lower bound, which makes `S³` the class complexity in its regime.

What can be claimed is a known-parameter `O(‖L‖₁Δ/ε² + S³Δ/ε⁴)` upper bound for block-heterogeneous smoothness and noise, which improves the published `‖L‖₁‖σ‖₁²` noise dependence by a routine argument.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
