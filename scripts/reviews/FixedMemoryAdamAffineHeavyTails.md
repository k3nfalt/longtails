# Novelty assessment: FixedMemoryAdamAffineHeavyTails

The [theorem](../../LongTails/Theorems/FixedMemoryAdamAffineHeavyTails.lean) concerns bias-corrected coordinatewise Adam with `β₁ = 0.9`, `β₂ = 0.999`, damping `δ = ε/(8(d+1))` outside the square root, step `η = ε/(2²⁹(L₀+L₁ε))`, and arithmetic minibatches of size `B` ([algorithm](../../LongTails/Algorithms/AffineHeavyTailedAdam.lean)). It runs `T` updates, returns a uniformly random pre-update iterate `x_I`, and proves `E‖∇f(x_I)‖₁ ≤ ε`. The [setup](../../LongTails/Setups/AffineHeavyTailedAdam.lean) assumes the following:

- `f` is differentiable on `ℝᵈ` with `f(x₀) − f(x) ≤ Δ` for all `x`.
- Anchored local `(ℓ∞→ℓ₁)` generalized smoothness: `‖∇f(y)−∇f(x)‖₁ ≤ (L₀+L₁‖∇f(x)‖₁)‖y−x‖_∞` whenever `L₁‖y−x‖_∞ ≤ 1`.
- IID, jointly measurable, unbiased oracle with coordinate affine moments `E|gᵢ−∂ᵢf|ᵖ ≤ σ₀,ᵢᵖ + σ₁ᵖ|∂ᵢf|ᵖ`, where `p ∈ (1,2]`.

**Proved budget.** Let `s₀ = Σᵢσ₀,ᵢ` and `C = 2¹⁷`. Exactly `B·T` oracle calls suffice, where `B = 1+⌈(C(σ₁+s₀/ε))^{p/(p−1)}⌉` and `T = 1+⌈2³²Δ(L₀+L₁ε)/ε²⌉`. In O-notation:

  `N = O( [1 + Δ(L₀/ε² + L₁/ε)] · [1 + (Cσ₁ + Cs₀/ε)^{p/(p−1)}] )`.

The constant `C^{p/(p−1)}` is not universal: it blows up as `p → 1`. When noise dominates, `N ≍ ΔL₀ s₀^{p/(p−1)}/ε^{(3p−2)/(p−1)}`, which is the known heavy-tail accuracy exponent.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Minibatch signSGD: [Kornilov et al., arXiv 2502.07923v2, Thm 1](https://arxiv.org/html/2502.07923v2) (special case: Euclidean `(L₀ᴱ,L₁ᴱ)`, `σ₁ = 0`). The note's reduction gives the same bound on the **exact** setup; I checked it (sketch below) | Kornilov: `O((ΔL₀ᴱd/ε² + ΔL₁ᴱd^{3/2}/ε)(1+(‖σ₀‖₁/ε)^{p/(p−1)}) log(1/δ))` w.p. `1−δ`. Exact-setup reduction: `O([1+Δ(L₀/ε²+L₁/ε)][1+(σ₁+s₀/ε)^{p/(p−1)}])` → `N` above | None: same order (`ℓ∞` constants satisfy `L₀ ≤ dL₀ᴱ`) | None. Sign methods already cover this class | None. Kornilov even gives a high-probability average | Adam's constants are far larger. The only gain is that the update is canonical Adam rather than sign |
| Adam, finite variance: [Li–Dong–Lin, arXiv 2505.11840v4 (27 Sep 2026; NeurIPS 2025 earlier version), Thm 1/Cor. 1](https://arxiv.org/html/2505.11840v4) (special case: `p = 2`, `σ₁ = L₁ = 0`, Euclidean `L`, `ℓ₂` variance `σ²`) | `O(d²LΔσ²/ε⁴ + dLΔ/ε²)` single-sample steps → `O((1+ΔL₀/ε²)(1+s₀²/ε²))` | Not worse whenever `dLΔ ≥ ε²`, since `L₀ ≤ dL` and `s₀ ≤ √d σ` (if `dLΔ < ε²`, the extra term `dσ²/ε²` can be worse). In the other direction, `L ≤ L₀` and `σ ≤ s₀`, so the gain is up to a factor `d²`, achieved when `L₀s₀² ≪ d²Lσ²` (ℓ∞-favourable geometry) | `p = 2` → all `p ∈ (1,2]`. Additive → affine noise. `L`-smooth → anchored `(L₀,L₁)` | None. Both are uniformly random-iterate `E‖∇f‖₁` guarantees with known parameters. Their `β`'s are tuned to the horizon; here memories are fixed | Batch `≈ (s₀/ε)²` versus single samples. Damping vanishes as `ε → 0` and the step is about `2⁻²⁹ε/L₀` |
| Plain vector Adam: [Pang, UAI 2026 / arXiv 2607.27383v2](https://proceedings.mlr.press/v337/pang26a.html) | Polynomial rate for `(ρ,ε)`-Goldstein stationarity, assuming bounded gradients and `p > 4/3` → `N` | Not comparable: different criterion and class | Incomparable classes: nonsmooth with bounded gradients there, smooth with unbounded gradients here | Ordinary `E‖∇f‖₁` instead of relaxed stationarity | Pang uses random step multipliers. Here the batches grow |

**Reduction check and ancestry.** Batched signSGD reaches `N` on this exact setup. The proof combines `⟨g,sign(g+e)⟩ ≥ ‖g‖₁−2‖e‖₁`, anchored descent with `‖Δx‖_∞ = η ≤ 1/(2L₁)`, and the von Bahr–Esseen bound `E‖ē‖₁ ≲ B^{−(p−1)/p}(s₀+σ₁‖g‖₁)`.

No existing Adam theorem transfers. Finite-variance analyses (Li–Dong–Lin, Zaheer et al. NeurIPS 2018) break down because a finite batch still has infinite variance. Deterministic fixed-`β₁²<β₂` Adam ([Wang et al., arXiv 2403.15146v1, Thm 7](https://arxiv.org/html/2403.15146)) is norm-Adam with a scalar conditioner, without bias correction, and uses exact gradients. It is proof ancestry for the idea that fixed memories suffice, not a baseline.

The new mechanism is pathwise residual recursions for `|m̂−g|` and `|√v̂−|g||` driven only by first absolute errors. With `B` this large, `E‖ζ‖₁ = O(ε)`, so the step is a perturbation analysis of near-deterministic Adam. It is not the small-batch problem posed by [Yu et al., arXiv 2606.23676v1](https://arxiv.org/html/2606.23676v1). That paper's target is stated in `BT` for general `B`, and its Prop. 5 corridor shows plain `ℓ₁` failure at fixed noise.

**Search coverage.** I searched on 2026-10-25 UTC across arXiv, PMLR/UAI, NeurIPS/ICLR/ICML 2023–2026, and generalized-smooth and heavy-tailed sign/Adam work. The result was introduced in commit fb6231a (2026-10-25), so every work cited here is prior. I read theorem statements in HTML excerpts. I did not read Kornilov's later sections, [2605.06615](https://www.emergentmind.com/papers/2605.06615) beyond a summary, or Pang's proofs. The companion note matches what I checked: it concedes the signSGD baseline and that the fixed-batch problem is unresolved.

## Conclusion

**No complexity improvement for the problem class; the contribution is a large-batch guarantee for canonical fixed-memory Adam.**

The strongest baseline is minibatch signSGD (Kornilov et al. Thm 1, plus the exact-setup reduction). It attains the same total budget:

| Method | Oracle calls for `E‖∇f‖₁ ≤ ε` |
|---|---|
| Batched signSGD | `O([1+Δ(L₀/ε²+L₁/ε)][1+(σ₁+s₀/ε)^{p/(p−1)}])` |
| This Adam result | same order, with constants of order `2^{17p/(p−1)}·2³²` |

Within the Adam family, the comparison does prove a gain. Against Li–Dong–Lin's finite-variance Adam, it extends scope to `p < 2`, affine noise and `(L₀,L₁)` curvature. On their `p = 2` overlap it is no worse when `dLΔ ≥ ε²` and up to `d²` better under ℓ∞-favourable geometry, at the price of batches of size about `(s₀/ε)²`.

The gain is modest for a concrete reason. Batches of size about `(s₀/ε)^{p/(p−1)}` shrink the first-moment noise to `O(ε)`, so Adam behaves like a perturbed sign method. That sidesteps the arbitrary-batch question that Yu et al. identify as open, and the accuracy-dependent damping and tiny step make the regime far from practical Adam. My search found no earlier theorem of this exact form, but that does not establish priority.

What can be claimed: unmodified bias-corrected Adam with default memories matches batched signSGD's heavy-tail complexity under affine noise and generalized smoothness, when it is given accuracy-sized batches.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
