# Novelty assessment: SGD under curvature-aligned noise (`CurvatureAlignedSgdNonconvex`)

[`result`](../../LongTails/Theorems/CurvatureAlignedSgdNonconvex.lean) proves the following for constant-step SGD with a uniformly random output iterate ([`WindowSgd`](../../LongTails/Algorithms/WindowSgd.lean), step `η = ε²/(L_g ε² + 2L_ξσ²)`). On a differentiable, lower-bounded `f` with a pointwise global upper model `f(x+u) ≤ f(x)+⟨∇f(x),u⟩+½⟨Q(x)u,u⟩`, it attains `∫‖∇f(x̂)‖ dP ≤ ε`. The oracle is IID, unbiased, and has variance `≤ σ²` ([setup](../../LongTails/Setups/CurvatureAlignedNoiseNonconvex.lean)).

**Proved budget:** `⌈4L_gΔ/ε² + 8L_ξσ²Δ/ε⁴⌉ + 1`, which is

  **O(1 + L_gΔ/ε² + L_ξσ²Δ/ε⁴)** stochastic-gradient calls.

The parameters are:
- `L_g`: a bound on `⟨Q(x)∇f,∇f⟩/‖∇f‖²`;
- `L_ξ`: a bound on `E⟨Q(x)ζ,ζ⟩/E‖ζ‖²` for the noise `ζ = g − ∇f`;
- `Δ`: the initial gap to a lower bound;
- `σ²`: the variance.

The domain is `L_g > 0`, `L_ξ, σ, Δ ≥ 0`, `ε > 0`. `Q(x)` may be nonsymmetric, indefinite, and not uniformly bounded; no global `L` appears. `Q` and `f` are only required to exist, so the algorithm needs `L_g, L_ξ, σ, Δ, ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan, [SIAM J. Optim. 23(4), 2013](https://arxiv.org/abs/1309.5549), Cor. 2.2: randomized SGD. Special-case baseline: requires `L`-Lipschitz `∇f` (same order: Khaled–Richtárik, [arXiv 2002.03329](https://arxiv.org/abs/2002.03329), Cor. 1). | `O(1 + LΔ/ε² + Lσ²Δ/ε⁴)` → `O(1 + L_gΔ/ε² + L_ξσ²Δ/ε⁴)`. On the overlap, take any admissible `Q` with `L_g, L_ξ ≤ L` (`Q ≡ LI` always works). | Never worse, up to constants. The speedup is `L(ε²+σ²)/(L_gε²+L_ξσ²)`; it is at least `L/(2L_ξ)` when `L_ξσ² ≥ L_gε²`. This is an instance-dependent factor; the `ε` exponents do not change. | `∇f` `L`-Lipschitz → only a pointwise upper model with directional constants. This also admits non-Lipschitz-gradient `f` such as `x² − \|x\|^{3/2}` (`Q ≡ 2`). However, the textbook proof already uses only the upper inequality. | None. Both use the same random-iterate output and the same parameter knowledge. | You must certify a global `Q(x)` with small `L_ξ`; the local Hessian is not valid globally for nonconvex nets. `L_ξ` is a joint condition on the problem and the oracle. |
| Liu–Pan–Zhang, [ICLR 2025](https://arxiv.org/abs/2406.15244), Eq. (7)/Thm. D.2: SGD under vector smoothness `∇²f ⪯ diag(L_i)` with coordinate noise `σ_i`. Special-case baseline. | `O(1 + ‖L‖_∞Δ/ε² + ‖L‖_∞‖σ‖₂²Δ/ε⁴)` → `O(1 + L_gΔ/ε² + (Σ_i L_iσ_i²)Δ/ε⁴)`, using `Q = diag(L)`. | Noise-term factor `‖L‖_∞‖σ‖₂²/Σ L_iσ_i²`, up to `d` when the noise lies in low-curvature coordinates. The improvement holds in the noise-dominated regime. | Diagonal, constant `Q` → general, state-dependent `Q(x)`. | None. | None on the overlap. Their paper targets AdaGrad; its SGD bound is a comparison, not tight. |

**Standard-reduction check.** No published theorem gives this bound by substitution. However, the proof is the Ghadimi–Lan descent argument with `L‖u‖²` replaced by `⟨Q(x)u,u⟩`; the cross term vanishes by unbiasedness, giving `E f⁺ ≤ f − η‖∇f‖² + (η²/2)(⟨Q∇f,∇f⟩ + E⟨Qζ,ζ⟩)`.

**Proof ancestry.**
- **Same quantities.** McCandlish et al. ([arXiv 1812.06162](https://arxiv.org/abs/1812.06162), §2.2, Eqs. 2.6–2.8) write exactly this one-step expansion, with `GᵀHG` and `tr(HΣ)`, as a local quadratic heuristic, not a theorem.
- **Matrix-smoothness descent lemmas.** These appear in Safaryan–Hanzely–Richtárik ([NeurIPS 2021](https://arxiv.org/abs/2102.07245)) for compression noise.
- **Optimality.** The companion note's minimax claim (for `L_ξ ≤ L_g`) embeds Carmon et al. and Arjevani et al. ([Math. Program. 2023](https://arxiv.org/abs/1912.02365)) instances via `Q ≡ cI`. It is plausible but not formalized. It also says nothing about methods that exploit anisotropy.
- **AdaGrad.** Jiang–Maladkar–Mokhtari ([COLT 2025](https://arxiv.org/abs/2406.04592), Thm. 4.1) give an SGD *lower* bound and AdaGrad bounds in the `ℓ₁`-gradient criterion. That criterion is not comparable here.

**Search coverage (2026-10-19 UTC).** I searched arXiv, ICLR, COLT, and SIAM sources for nonconvex SGD bounds with matrix or anisotropic smoothness and Hessian-weighted noise. I read the relevant statements in Khaled–Richtárik, Jiang–Maladkar–Mokhtari, McCandlish et al., and Liu–Pan–Zhang (Liu–Pan–Zhang via the HTML version). I did not reread the Ghadimi–Lan text; its corollary is cited from standard knowledge. For Tao–Yu–Zhang ([arXiv 2605.06615](https://arxiv.org/abs/2605.06615)) and Hamza–Goel ([arXiv 2606.30455](https://arxiv.org/abs/2606.30455)), I checked only the abstracts; neither states such an upper bound. The result was introduced in commit `47a53ce` on 2026-10-19. The companion note's citations match what I checked. Its realism measurements are not part of the Lean result. Its "minimax-optimal" claim is paper-level only.

## Conclusion

**It sharpens the classical SGD bound on suitable instances, but this is a routine refinement of the textbook analysis.**

The strongest baseline is Ghadimi–Lan's `L`-smooth SGD bound. The new theorem replaces the single constant `L` with the curvature along the gradient (`L_g`) and the curvature seen by the noise (`L_ξ`):

| | calls for `E‖∇f(x̂)‖ ≤ ε` |
|---|---|
| Ghadimi–Lan (`L`-smooth) | `O(LΔ/ε² + Lσ²Δ/ε⁴)` |
| This result | `O(1 + L_gΔ/ε² + L_ξσ²Δ/ε⁴)` |

The new bound is never worse, up to constants. It gains a factor of about `L/L_ξ` when the noise dominates (`L_ξσ² ≥ L_gε²`). In a two-dimensional quadratic whose noise lies only in its flat direction, this gain is unbounded. The accuracy exponents are unchanged.

The gain is modest for a concrete reason. The proof keeps the quadratic form in the standard descent lemma, and McCandlish et al. (2018) already wrote this same one-step expansion. Exploiting it also requires a *global* model `Q(x)` with small `L_ξ`. The note certifies one only for a softmax output layer, where the gain is 2–2.6×. No ε-exponent or problem-class improvement over other methods is shown.

The search found no earlier published theorem stating this exact `(L_g, L_ξ, σ, Δ)` bound, but that does not prove priority. What can be claimed is a clean, formally verified, instance-dependent refinement of SGD's constant: it is valid under one-sided, curvature-weighted assumptions.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
