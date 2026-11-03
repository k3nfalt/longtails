# Novelty assessment: TailObliviousRootFinding

**Guarantee.** [`result`](../../LongTails/Theorems/TailObliviousRootFinding.lean) concerns a monotone, `L`-Lipschitz operator `F` on a finite-dimensional Euclidean space with a zero `x⋆`, `‖x0−x⋆‖ ≤ R`. The oracle draws IID samples and is unbiased, jointly measurable and has central α-th moment at most `σ^α`, for some `α ∈ (1,2]` ([setup](../../LongTails/Setups/TailObliviousMonotoneRootFinding.lean)). At the stated budget, the last completed epoch `Z` of a clipping-free, restarted, recursively anchored stochastic extragradient method ([algorithm](../../LongTails/Algorithms/TailObliviousExtragradient.lean)) satisfies `∫‖F(Z)‖^α dP ≤ ε^α`, so `E‖F(Z)‖ ≤ ε`. The updates use only `x0` and `L`. The budget depends on `α, σ, R, ε`.

**Complexity.** Write `ℓ = 1 + log(1 + LR/ε + σ/ε)`. The parameters are: `L` the Lipschitz constant, `R` the initial distance, `σ` the noise scale, `α` the moment order, `ε` the residual accuracy. The proved budget is, with universal constants suppressed and using `2^{20/(α−1)}·64^{2α/(α−1)} ≤ 2^{44/(α−1)}`:

  N = O( (1 + LR/ε)·(α/(α−1))⁴·ℓ² + 2^{44/(α−1)}·(σ/ε)^{α/(α−1)}·((α/(α−1))²·ℓ)^{2α/(α−1)} ).

When `σ = 0` the noise term vanishes.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Chen & Luo, RAIN, [JMLR 25 (2024), arXiv 2208.05925v4](https://arxiv.org/abs/2208.05925), Thm 4.2. Applies only to the special case α = 2 (finite variance). The paper notes it extends to monotone Lipschitz VIs. | `O(LR/ε·loglog(LR/ε) + σ²/ε²·log³(LR/ε))` for `E‖F‖ ≤ ε` → at α = 2: `O((1+LR/ε)ℓ² + (σ/ε)²ℓ⁴)` | None: same order, apart from polylogarithmic factors. At α = 2 this result is worse by about `ℓ²/loglog` on the `LR/ε` term and by about one `log` on the `σ²/ε²` term. | Variance `≤ σ²` → central α-th moment `≤ σ^α` with α ∈ (1,2], so infinite variance is allowed (e.g. Student-t noise with ν ≤ 2) | RAIN sets `N₀, K_s` from `σ, D, ε` → the updates need only `L, x0` (the budget still needs `α, σ, R, ε`). Also `E‖F‖ ≤ ε` → `E‖F‖^α ≤ ε^α`. | Expectation only. Finite-dimensional Euclidean space. Large constants: `2^{44/(α−1)}`, and a log degree `2α/(α−1)` that blows up as α→1. Proved only at the stated budget. |
| Sadiev et al., clipped-SEG, [ICML 2023, arXiv 2302.00999v2](https://arxiv.org/abs/2302.00999), Thm 4.1 Case 1 / Thm G.2 | `Õ(LR²/ε′ + (σR/ε′)^{α/(α−1)})` for restricted gap `Gap_R(x̄_avg) ≤ ε′` with probability `≥ 1−β` → `N` above for the expected residual | Not comparable: different criterion. Residual ⇒ gap would need a bound on `‖Z−x⋆‖`, which is not proved. Gap does not imply residual. | Same operator and noise class (Lipschitz and α-moment are needed only on a ball there) | Clipping level and step depend on `σ, α, R, K` → no clipping, and steps use only `L`. Averaged gap → last-completed-epoch residual. | Loses high probability (`log(1/β)`) and gives an expectation bound only |

**Reduction check.** A standard reduction does not reproduce this bound. A von Bahr–Esseen sample mean is α-oblivious, but feeding it into deterministic anchored EG or Halpern gives the *multiplicative* cost `(LR/ε)(σ/ε)^{α/(α−1)}` by my own calculation. Anchoring combined with the α-free forward stochastic approximation of [Chandak et al. 2026 (preprint), Thm 2](https://arxiv.org/abs/2603.19648) requires strong monotonicity and steps `∝ μ/L²`, so it loses on the deterministic term. Anchoring combined with Sadiev's quasi-strongly monotone clipped-SEG (Thm G.4) plausibly gives the same rate with high probability, but only with `σ, α` known, and I found no source that carries out this composition. The new mechanism is the pathwise extragradient inequality, in which the subadditivity of `t^{α/2}` replaces `E‖ζ₁‖²`, together with an α-power-smoothness lemma in [TailObliviousNoise.lean](../../LongTails/Proofs/TailObliviousNoise.lean). Proof ancestry: the recursive anchoring of RAIN (stage structure), and α-th-moment SGD analyses such as [Fatkhullin–Hübler–Lan, arXiv 2508.04860v2 (SIOPT)](https://arxiv.org/abs/2508.04860), which cover strongly convex minimization only.

**Search coverage.** The search was run on 2026-11-03 over arXiv, ICML/NeurIPS/ICLR and JMLR. It covered clipped VI methods (Gorbunov et al. 2022, Sadiev et al. 2023), clipping-free heavy-tail minimization (Liu–Zhou ICLR 2025, Liu arXiv 2606.00520), heavy-tailed min-max (Zhu et al. 2609.06064, nonconvex SGDA only; checked from the abstract only), and VIs without bounded variance ([Alacaoglu–Kim, ICML 2026](https://arxiv.org/abs/2602.05531), which still assumes finite variance). None of these gives an α-oblivious residual guarantee for monotone operators. The theorem was introduced in commit `eadaae86` on 2026-11-03. The companion note's citations match what I checked. Its claim that "both terms match lower bounds" holds only for α bounded away from 1.

**Conclusion**

**Yes. The rate is not new, but the information requirement and the noise class are: this is the first α-, σ-, R- and ε-free update rule I could find with an optimal-order residual bound for monotone operators under infinite-variance noise.**

The closest baseline is RAIN (Chen & Luo). It needs finite variance and tunes on `σ, D, ε`. At α = 2 both results cost

  `LR/ε + σ²/ε²`  (up to logarithms),

so there is no complexity gain, only slightly worse logarithmic factors. For α < 2 RAIN does not apply. Clipped SEG covers that case but certifies a high-probability gap, not a residual, and needs `σ, α` for clipping.

The cost is substantial: the guarantee is in expectation only, the noise term carries `2^{44/(α−1)}` and a log power `2α/(α−1)`, and the stopping budget still needs all parameters. A known-parameter construction (anchoring + clipped SEG) would likely match the rate with high probability, so the contribution is adaptivity of the updates plus a genuinely clipping-free heavy-tailed extragradient estimate. No standard reduction gives it. Priority is supported only by a search on the day of introduction, in a fast-moving area.

What can be claimed: a tail-index- and scale-oblivious method for heavy-tailed monotone root finding with expected residual `Õ(LR/ε + (σ/ε)^{α/(α−1)})` for fixed α > 1. It does not improve the complexity.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
