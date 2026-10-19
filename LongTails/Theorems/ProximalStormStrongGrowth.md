# Accelerated stochastic proximal extragradient under strong growth and mean-squared smoothness

**Lean:** [`result`](ProximalStormStrongGrowth.lean) ·
[setup](../Setups/StrongGrowthMeanSquaredSmoothConvex.lean) ·
[algorithm](../Algorithms/ProximalStorm.lean) ·
proofs `LongTails/Proofs/ProximalStorm*.lean`

## Setting

The objective `f : E → ℝ` lives on a real Hilbert space `E` of arbitrary dimension. It is convex and differentiable, with a minimizer `xstar` satisfying `‖x0 − xstar‖ ≤ R`.

The oracle receives a query `(x, y)` and returns `(g(x, ξ), g(y, ξ))`, using the same fresh IID sample `ξ` for both points. The stochastic gradient satisfies:

- **unbiasedness:** `E g(x, ξ) = ∇f(x)`;
- **strong growth (SGC):** `E‖g(x, ξ) − ∇f(x)‖² ≤ Γ² ‖∇f(x)‖²`, following [Schmidt–Le Roux 2013](https://arxiv.org/abs/1308.6370) and [Vaswani et al. 2019](https://arxiv.org/abs/1810.07288);
- **mean-squared smoothness (MSS):** `E‖g(x, ξ) − g(y, ξ)‖² ≤ L̄² ‖x − y‖²`, as in [Arjevani et al.](https://arxiv.org/abs/1912.02365) and SPIDER/STORM;
- joint measurability, plus integrability of the quantities above.

No separate `L`-smoothness is assumed. MSS already gives `‖∇f(x) − ∇f(y)‖ ≤ L̄‖x − y‖` by Jensen (`Hyp.grad_lip`). Below, `L ≤ L̄` denotes the true smoothness of `f`, and all comparisons use it.

The accuracy criterion is `E[f(output) − f(xstar)] ≤ ε`. The expectation is over the oracle samples and an internal uniform seed.

## Algorithm

Write `Γ̂ = 1 + Γ` and `λ = Γ̂/L̄`. The method is an inexact accelerated proximal point scheme of A-HPE type ([Monteiro–Svaiter 2013](https://doi.org/10.1137/110833786)) with the large constant step `λ`. Each of the `K` outer steps does three things:

1. **Extrapolate.** Set `a = (λ + √(λ² + 4λA))/2` and `x̃ = (A y + a z)/(A + a)`. These are `aNext` and `mixPt`.
2. **Approximate the prox step.** Run unnormalized STORM on `φ(x) = f(x) + ‖x − x̃‖²/(2λ)` for `T0 + W` pair calls, with momentum `a_in = 1/(400Γ̂²)` and step `η = 1/(60Γ̂L̄)`. Take `y⁺` to be the inner iterate with index `T0 + τ`, where `τ` is uniform in `{0, …, W−1}` and drawn from the algorithm's seed. Here `T0 = ⌈800Γ̂²(5 + 4 log Γ̂)⌉` and `W = ⌈800Γ̂²⌉ + 1`.
3. **Extragradient step.** Set `z⁺ = z − (a/B) Σ_{i<B} g(y⁺, ξ_i)`, using `B = ⌈6Γ̂²⌉` fresh samples. Then `A⁺ = A + a`.

The output is `y_K`. All updates use only the oracle replies and the public constants `L̄`, `Γ`, `R`, `ε`, `x0`. The prox point, `φ` and the potentials appear only in the analysis.

## Guarantee

`result : Convergence spec budget` proves that `E[f(y_K) − f(xstar)] ≤ ε` after

```
⌈√(2 L̄ R² / ((1+Γ) ε))⌉ · ⌈(1+Γ)² (4810 + 3200 log(1+Γ))⌉
```

oracle calls. Every inner pair call and every batch call is counted. In order notation the budget is

  **`O( (1+Γ)^{3/2} √(L̄R²/ε) · log(e(1+Γ)) + (1+Γ)² log(e(1+Γ)) )`.**

## What is new

**Baselines on the same class.**

- **SGD** under SGC costs `O((1+Γ²) L R²/ε)` ([Vaswani et al. 2019](https://arxiv.org/abs/1810.07288)).
- **Accelerated methods** under SGC cost `O((1+Γ²) √(LR²/ε))`. This rate is obtained by Vaswani et al.'s accelerated method and by [AGNES (Gupta–Siegel–Wojtowytsch, NeurIPS 2024)](https://arxiv.org/abs/2302.05515), Thm. 3 and Fig. 1.
- **[Mishkin–Pilanci–Schmidt](https://arxiv.org/abs/2404.02378), v2 (Jan 2025)**, withdrew their claimed `ρ → √ρ` improvement because of a bug. Their abstract and App. D state that it is unknown whether the `ρ = 1 + Γ²` dependence of stochastic AGD is tight.
- **None of these methods uses MSS.** I found no accelerated method under SGC that exploits the same-sample pair oracle.

**New rate.** This result replaces `(1+Γ²)√L` by `(1+Γ)^{3/2}√L̄` up to `log(1+Γ)`. It improves on accelerated SGD under SGC by a factor

  `≈ √(Γ L / L̄) / log(e(1+Γ))`, whenever `L̄ ≲ Γ L`.

There is no improvement when `L̄ ≳ Γ L`. For example, coordinate-sampling oracles have `L̄ ≈ ΓL`.

**Mechanism.** The rate is the online analogue of Katyusha X's sum-of-nonconvex rate `n + n^{3/4}√(L/σ)` ([Allen-Zhu 2018](https://arxiv.org/abs/1802.03866), Thm. 1), with `n ↔ Γ²`. That analogy fails if Katyusha X is transferred directly. A fixed SVRG snapshot leaves a bias whose size is relative to `‖∇f‖` at the snapshot. SGC allows that bias to sit in low-curvature directions, so absorbing it needs batches of size `Γ³L/L̄`. The proof avoids this in three steps.

1. **Outer step (`Hyp.hpe_step`, `Hyp.block_path`).** The A-HPE inequality is linear in `E‖λ∇φ(y⁺)‖²` and `E‖y⁺ − x̃‖²`, so a mean-square relative-error condition is enough. The fresh batch makes the extragradient noise unbiased. Its variance `(a²Γ²/(2B))‖∇f(y⁺)‖²` is absorbed into the A-HPE slack once `B ≥ 6Γ²`.
2. **Inner step: the key estimate (`Hyp.noise_bound`).** Apply MSS from the exact prox point `x⋆_φ`, where `‖∇f(x⋆_φ)‖ = D/λ` and `D = ‖x̃ − x⋆_φ‖`. This gives

     `E‖g(x) − ∇f(x)‖² ≤ 2Γ²D²/λ² + 2L̄²λ²‖∇φ(x)‖²`.

   The inner noise is therefore affine in `∇φ`. Its relative constant is `2L̄²λ² = 2Γ̂²`, and its floor is relative to `D`. The smoothness `L` never enters.
3. **Inner solver (`Hyp.inner_relative`).** STORM with the Lyapunov function `gap + (η/a)‖e‖² − 4ηaΓ̂²‖∇φ‖²` charges the fresh relative noise to the next descent step. The strong convexity `1/λ` gives contraction. Averaging over a window of length `W` gives

     `E[λ²‖∇φ(y⁺)‖²] ≤ E[D²]/6`,

   at cost `O(Γ̂² log Γ̂)`, because the condition number of `φ` measured with `L̄` is `L̄λ = Γ̂`.
4. **Finiteness of the ENNReal terms.** A truncation `1{D² ≤ M}` together with monotone convergence keeps every term finite. No second-moment assumption on the iterates is needed.

**Lower bound and tightness (not formalized; zero-respecting algorithms only).**

- Construction:
  - Take Nesterov's convex zero-chain with smoothness `L′`.
  - Mask each gradient coordinate independently: `g_j = (ξ_j/p) ∂_j f`, with `ξ_j ~ Bernoulli(p)` and `p = 1/(1+Γ²)`.
- Properties:
  - SGC holds with equality.
  - MSS holds with `L̄ = √(1+Γ²) L′`.
  - The pair oracle shares the mask, so it reveals nothing extra.
  - Each query reveals the next chain coordinate with probability `p`.
- Consequence: any zero-respecting method needs `Ω((1+Γ²) √(L′R²/ε))` calls, with `L′ = min(L, L̄/√(1+Γ²))`. That is `Ω(min{(1+Γ²)√L, (1+Γ)^{3/2}√L̄} · R/√ε)`. So the rate above is tight up to `log(1+Γ)` on the branch `L̄ ≤ ΓL`.
- With `L′ = L`, the same construction shows `ρ√(L/ε)` is tight for SGC oracles without MSS. This answers the question of Mishkin et al. for zero-respecting methods and general SGC oracles.
- Extending the bound to randomized algorithms needs the standard rotation argument (Carmon et al.; Arjevani et al.), which is not written out here.

## A natural instance

Realizable regression with a loss that is flat at zero residual, a smoothed `ℓ₄` regression. The model is `f(x) = E ψ(⟨a, x − x⋆⟩)`, with Gaussian design `a ~ N(0, Σ)`, `Σ ≻ 0`, in any dimension. The loss is

- `ψ(t) = t⁴/12` for `|t| ≤ 1`,
- `ψ(t) = t²/2 − 2|t|/3 + 1/4` otherwise,

which is C² with `0 ≤ ψ″ ≤ 1`, so the sample functions are convex.

**Strong growth.** Write `v = x − x⋆`, `s² = vᵀΣv` and `m(s) = Eψ″(sZ)`. By Stein's lemma, `∇f = Σv · m(s)`. Decompose `a = (Z/s)Σv + a_⊥`. Then

  `E‖g‖² ≤ E[ψ′(sZ)²Z²]·‖Σv‖²/s² + E[ψ′(sZ)²]·trΣ`.

The two ratios needed are bounded analytically:

- `ψ′(t)² ≤ min(t⁶/9, t²)`.
- `m(s) ≥ c₀ s²` for `s ≤ 1`, with `c₀ = E[Z²; |Z| ≤ 1] ≈ 0.199`.
- `m(s) ≥ P(|Z| ≥ 1) ≈ 0.317` for `s ≥ 1`.
- Hence `h₁ = Eψ′²/(s²m²) ≤ 42` and `h₂ = Eψ′²Z²/(s²m²) ≤ 296` for all `s`.

Numerically the bounds are `5/3` and `35/3`. Since `‖Σv‖² ≥ λ_min s²`, SGC holds with `Γ² ≤ 296 + 42 trΣ/λ_min`.

**Smoothness constants.**

- MSS: `|ψ′(u) − ψ′(w)| ≤ |u − w|` gives `L̄² ≤ (trΣ + 2λ_max) λ_max`.
- True smoothness: `L = λ_max`.
- Weak growth: `ψ′² ≤ 2ψ` gives `ℒ ≍ trΣ`.

The problem is not PL: `f − f* ≍ (vᵀΣv)²` near `x⋆`.

The instance has `L̄ ≈ √(trΣ λ_max) ≪ Γ L ≈ λ_max √(trΣ/λ_min)` whenever `κ_Σ = λ_max/λ_min` is large. With the IID oracle (no finite support), the rates are:

| Method (same oracle) | Calls, up to constants and logs |
|---|---|
| SGD under weak growth (ℒR²/ε; [Vaswani et al.](https://arxiv.org/abs/1810.07288) Thm. 5, [Gower et al. 2019](https://arxiv.org/abs/1901.09401)) | `trΣ · R²/ε` |
| SGD under SGC with step `1/(ρL)`, no restart (hand argument, not formalized) | `≍ trΣ · λ_max / (λ_min² √ε)` |
| Accelerated SGD under SGC (Vaswani et al.; AGNES) | `(trΣ/λ_min) √(λ_max) · R/√ε` |
| **This result** | `trΣ · λ_max^{1/4} λ_min^{-3/4} · R/√ε` |

The SGD row uses the instance's growth. It satisfies `‖∇f‖² ≳ λ_min · min(f − f*, (f − f*)^{3/2})`. With descent `E f_{k+1} ≤ E f_k − E‖∇f‖²/(2ρL)` and Jensen, plain SGD already reaches an `ε^{-1/2}` rate.

- **Against accelerated SGD:** the gain is `κ_Σ^{1/4}/log` at every accuracy.
- **Against SGD:**
  - SGD under weak growth costs `trΣR²/ε`. This result beats it when `√ε ≲ R λ_min^{3/4}/λ_max^{1/4}`.
  - Plain SGD under SGC uses the growth above and has the same exponent `ε^{-1/2}` as this result. This result beats it only when `R ≲ λ_max^{3/4}/λ_min^{5/4}`, up to constants.
  - So the instance-level `κ_Σ^{1/4}` gain is over accelerated SGD (and over restarted accelerated SGD, for the restarted versions). It is not uniform over SGD.
- **Excluded alternatives.** Finite-sum methods (Katyusha, Katyusha X) and least-squares-specific acceleration ([Jain et al. 2018](https://arxiv.org/abs/1704.08227)) do not apply to this oracle.
- **Woodworth–Srebro.** [Woodworth–Srebro 2021](https://arxiv.org/abs/2106.02720) prove `Ω(HR²/ε)` for individually smooth convex interpolation, but their hard family violates SGC.

**Caveat: restarted baselines.** Near `x⋆` this instance satisfies a Hölder error bound of exponent 4. So restarted methods are the relevant comparison at very small `ε`. Sharpness restarts follow [Roulet–d'Aspremont 2017](https://arxiv.org/abs/1702.03828). The following rates are not formalized:

| Restarted method | Calls |
|---|---|
| Restarted accelerated SGD | `≍ trΣ λ_max^{1/2} λ_min^{-3/2} ε^{-1/4}` |
| Restarted version of this method | `≍ trΣ λ_max^{1/4} λ_min^{-5/4} ε^{-1/4}` |

SGD already reaches `ε^{-1/2}` without restarts, as in the table above, but it does not reach `ε^{-1/4}`. The instance-level gain over the strongest restarted baseline is again `κ_Σ^{1/4}`, but it holds only for restarted versions on both sides, and that corollary is not formalized.

The same behaviour holds for other `ℓ_p` losses with `p > 2`, and should extend to hypercontractive designs (Stein's lemma is only a convenience). Losses with `ψ″(0) > 0`, such as the squared, Huber or log-cosh losses, give quadratic growth near `x⋆`. There SGD's `ℒ/μ · log(1/ε)` wins, and this result is not the right tool.

## Limitations

- **Logarithmic factor.** The upper bound is tight only up to `log(1+Γ)`, and only on the branch `L̄ ≤ ΓL`. When `L̄ ≳ ΓL`, accelerated SGD under SGC is as good or better.
- **Unformalized claims.** The lower bound, the answer to Mishkin et al., the instance computations and the restarted comparisons are hand arguments. The lower bound covers zero-respecting algorithms only.
- **Oracle.** The method needs the same-sample pair oracle and the parameters `L̄` and `Γ`.
- **Constants.** The constants (4810, 3200) are large and not optimized.
- **Regimes not formalized.** Only the convex case is formalized; the strongly convex version (restarts) is not.
- **Literature coverage.** The search covered arXiv, NeurIPS/ICML/ICLR proceedings and OpenReview up to Oct 2026. It found no accelerated method exploiting MSS under SGC, but absence of a result does not prove priority.
