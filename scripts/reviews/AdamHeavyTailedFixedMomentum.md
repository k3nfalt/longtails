# Novelty assessment: AdamHeavyTailedFixedMomentum

The [theorem](../../LongTails/Theorems/AdamHeavyTailedFixedMomentum.lean) proves the following for every `d`, every `L`-smooth `f : ℝ^d → ℝ` with `f(x₀) − inf f ≤ Δ`, and every jointly measurable, unbiased, IID oracle with `E Σᵢ|gᵢ − ∂ᵢf|^p ≤ σ^p` for `p ∈ (1,2]` ([setup](../../LongTails/Setups/HeavyTailedAdam.lean)). Coordinate [Adam](../../LongTails/Algorithms/Adam.lean) has no bias correction, `β₁ = 0.9`, `β₂ = 1−ρ`, and damping `τ` outside the square root. Run for `K` single-sample steps, it returns a uniformly random pre-update iterate `x_I` with `E‖∇f(x_I)‖₂ ≤ ε`.

**Proved budget.** Here `L` is the smoothness constant, `Δ` the initial gap, `σ` the coordinate-aggregated `p`-th central-moment scale, and `ε` the target. Substituting `ρ = (10¹² + (10⁵σ/ε)^{p/(p−1)})⁻¹`, `τ = ε/(10⁵√ρ)`, and `η = τρ/(10⁵L)` gives

  `K ≤ 2 + 4·10²⁰ ΔL/ε² + 4·10⁸·10^{5p/(p−1)} ΔL σ^{p/(p−1)} / ε^{(3p−2)/(p−1)}`.

The algorithm uses all of `L, Δ, σ, p, ε`. The constant `10^{5p/(p−1)}` blows up as `p → 1`. Because `‖e‖₂ ≤ ‖e‖_p`, the oracle class is contained in the Euclidean class with `σ₂ ≤ σ`. Conversely, a Euclidean scale `σ₂` only gives `σ ≤ d^{1/p−1/2}σ₂`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Hübler–Fatkhullin–He, NSGD-M, [AISTATS 2025; arXiv v3, App. D.2, Cor. 19](https://arxiv.org/html/2410.13849v3) | `O(ΔL/ε² + ΔLσ₂^{p/(p−1)}/ε^{(3p−2)/(p−1)})` (applies with `σ₂ ≤ σ`) → `O(1 + ΔL/ε² + ΔLσ^{p/(p−1)}/ε^{(3p−2)/(p−1)})` | None: same order. Lower bound `Ω` of this order for the Euclidean class (Zhang et al. 2020, cited there; transfer to the coordinate subclass not verified) | None | None: both need `Δ,L,σ,p` and give the same random-iterate expectation | Narrower noise class. On a Euclidean scale, the noise term is multiplied by `d^{(2−p)/(2(p−1))}`. Much larger constants. Gain is algorithmic only: fixed `β₁`, no normalization, versus NSGD-M's horizon-tuned `β` |
| Vanilla SGD: Liu, [arXiv 2606.00520 v1, Thm 4.1](https://arxiv.org/html/2606.00520v1); SGD-specific lower bound for non-increasing steps in Fatkhullin–Hübler–Lan, [NeurIPS 2025 / SIOPT, arXiv 2508.04860](https://arxiv.org/abs/2508.04860) (different algorithm, same class) | `O(ΔL/ε² + (σ₂√(LΔ)/ε²)^{p/(p−1)})` → bound above | Noise term smaller by `(√(LΔ)/ε)^{(2−p)/(p−1)}`. Measured at the Euclidean scale, the gain is `(√(LΔ)/(√d ε))^{(2−p)/(p−1)}`, so it requires `√(LΔ) > √d·ε` and `p < 2`. None at `p = 2` | None | None | Coordinate noise. SGD's criterion `E(avg‖∇f‖²)^{p/2}` is slightly stronger |
| Pang, plain vector Adam, [arXiv v2, Thm 6.4; UAI 2026 per companion note, unverified](https://arxiv.org/html/2607.27383v2) | `ε^{−(5p/(3p−4)+3/2)}`, `p > 4/3`, for `(ρ,ε)`-stationarity of `G`-Lipschitz `f` → bound above | Not comparable: different criterion and class | Not comparable. Pang needs no smoothness but needs bounded gradients; this result needs smoothness but not bounded gradients | Ordinary `E‖∇f‖` versus Goldstein-type stationarity | Pang uses bias correction, vector form, and fixed stabilizer; here `τ` grows with `1/ε` and `1−β₂ ≤ 10⁻¹²` |

**Reductions and mechanism.** No reduction reproduces the bound. Batching, clipping, or composing with NSGD-M changes the update. Fang–Demmel–Lavaei ([arXiv 2602.13413](https://arxiv.org/abs/2602.13413)) need normalization. If `τ` always dominated `√v`, the method would be SGDM, which is analyzed only at SGD's `ε^{−2p/(p−1)}` rate (Liu 2606.00520, Thm 4.3). Therefore, the spike suppression by `√v` and the historical coupling between numerator and denominator under asymmetric noise, with `β₂ ≫ β₁`, are genuinely used. Yu et al. ([arXiv 2606.23676](https://arxiv.org/html/2606.23676v1)) identify exactly this unequal-memory case as unresolved, though for the `ℓ₁` criterion. Large damping as bias control is credited in the note to H. Yang's AdaGrad preprint, which I did not access.

**Search coverage.** I searched arXiv, PMLR, NeurIPS/ICML/ICLR, and author pages on 2026-10-19, covering heavy-tailed Adam, AdaGrad, RMSProp, SGD, SGDM, and normalized/preconditioned methods. Git places the result at commit d9544cf (2026-10-19), so every cited work is prior. I read theorem statements only through HTML excerpts. I did not read FHL's smooth-case theorem, Liu's [2606.22326](https://arxiv.org/abs/2606.22326) beyond its abstract, or Yang's preprint. The companion note's citations and its "no class-level advance" statement agree with what I checked.

## Conclusion

**The problem-class complexity is unchanged; what is new is that unmodified coordinate Adam with fixed `β₁ = 0.9` provably reaches the heavy-tail-optimal accuracy exponent.**

| Method (same class) | Noise-dominated cost |
|---|---|
| NSGD-M (Hübler et al., Cor. 19) | `ΔLσ^{p/(p−1)}/ε^{(3p−2)/(p−1)}` |
| Vanilla SGD (Liu, Thm 4.1; FHL lower bound) | `(σ√(LΔ))^{p/(p−1)}/ε^{2p/(p−1)}` |
| This Adam result | `ΔLσ^{p/(p−1)}/ε^{(3p−2)/(p−1)}` |

Normalized momentum already achieves this order, under the weaker Euclidean noise assumption and with far smaller constants. As an optimization guarantee, the result therefore adds nothing. Its significance is method-specific. Plain SGD cannot reach this exponent for `p < 2` with non-increasing steps, and recent Adam analyses either use relaxed stationarity (Pang) or leave the `β₂ ≫ β₁` case open (Yu et al.). Here Adam's own second-moment denominator does the clipping work.

There are real limits. The noise assumption is coordinatewise, which costs `d^{(2−p)/(2(p−1))}` relative to Euclidean-noise baselines. The tuning sets `1−β₂ ≤ 10⁻¹²` and uses a damping `τ` that grows as `ε` shrinks, so this is not practical Adam and it shows no benefit from adaptive preconditioning. My search found no earlier proof of this guarantee, but that does not establish priority.

What can be claimed is a first-found, method-specific separation: Adam without bias correction, with fixed `β₁`, attains the minimax heavy-tail exponent that vanilla SGD provably misses.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
