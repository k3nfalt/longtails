# Novelty assessment: GeneralizedMintyExtragradient

**Guarantee.** [The theorem](../../LongTails/Theorems/GeneralizedMintyExtragradient.lean) proves the following for every continuous `F : ℝᵈ → ℝᵈ` in [the setup](../../LongTails/Setups/GeneralizedLipschitzMinty.lean). Assume `F` is 1-symmetric (L₀,L₁)-Lipschitz on segments and has a root `z` with `‖x₀−z‖ ≤ R` and `⟨F(x), x−z⟩ ≥ 0` for every `x` (the Minty condition). Then [extragradient](../../LongTails/Algorithms/GeneralizedMintyExtragradient.lean) with step `η = 1/(4(L₀+L₁‖F(x)‖))`, frozen once `‖F(x)‖ ≤ ε`, returns a point with `‖F(x̂)‖ ≤ ε`. This holds deterministically, so also in expectation, after exactly `2(1+⌈32R²(L₀/ε+L₁)²⌉)` exact operator calls.

**Simplified complexity.** Here L₀ > 0 and L₁ ≥ 0 are the generalized-Lipschitz constants, R is the bound on the initial distance to the root, and ε is the target residual:

  O(1 + L₀²R²/ε² + L₁²R²).

The updates use L₀, L₁ and ε (ε is needed for the freeze). The budget uses R as well.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Choudhury–Loizou, [NeurIPS 2025 / arXiv:2510.22421v1](https://arxiv.org/abs/2510.22421), Thm 3.6 (stated for monotone `F`). Its proof (Lemma D.6, eqs. (53)–(56), App. D.3.2) uses monotonicity only through `⟨F(x̂ₖ), x̂ₖ−x*⟩ ≥ 0`, so it applies verbatim under Minty. | 2⌈2R²(L₀/ε+L₁)²/ν²⌉ ≈ 2⌈9.9R²(L₀/ε+L₁)²⌉ calls (ν e^ν = 1/√2) → 2(1+⌈32R²(L₀/ε+L₁)²⌉) | None: same order. The constant is about 3× worse. | None after the verified reduction. Relative to the theorem as stated: monotone → Minty, but the published proof already covers this. | Best iterate `min_k‖F(x_k)‖` → frozen point. No real gain: `F(x_k)` is queried every iteration, so the best iterate can be tracked at no extra cost. | Freezing needs ε inside the updates. The step is 0.25/(…) instead of 0.45/(…). |
| Choudhury–Loizou, same paper, Thm 3.8 (weak Minty, ρ = 0). Condition (17) holds automatically at ρ = 0. | O(1 + L₀²R²(1+L₁R e^{L₁R})²/ε²) for `min_k‖F(x̂_k)‖ ≤ ε` → O(1 + L₀²R²/ε² + L₁²R²) | Exponential → polynomial whenever L₁R ≫ 1. However, row 1 already gives the polynomial bound. | None (same class at ρ = 0) | None | None |
| Special case L₁ = 0. Repository [EuclideanWeakMintyExtragradient](../../LongTails/Theorems/EuclideanWeakMintyExtragradient.lean) (EG+, Diakonikolas–Daskalakis–Jordan, AISTATS 2021, Thm 3.2; not re-read here). Covers only globally Lipschitz `F`. | 2 + 2⌈200L²R²/ε²⌉ → 2(1+⌈32L₀²R²/ε²⌉) | None: same order. | L₁ = 0 → L₁ ≥ 0: covers operators whose local Lipschitz constant grows with ‖F‖. Row 1 already covers these. | None | None |

**Reduction check and mechanism.** The selected proof ([GeneralizedMintyDescent](../../LongTails/Proofs/GeneralizedMintyDescent.lean), `decrease`) and Choudhury–Loizou's argument follow the same steps:

- Expand the corrector step.
- Apply the Minty inequality at the predictor point.
- Bound `‖F(x)−F(y)‖` along the short predictor segment using only the regularity assumption.
- Sum the resulting per-step decrease of `‖x−z‖²`.

The only change is a cruder local bound (`‖F(x)−F(y)‖ ≤ ‖F(x)‖/2`) in place of their exp(2ν) estimate. I found no new mechanism and no unresolved obstacle. Their Thm 3.8, not 3.6, is the source of the exponential factor.

**Search coverage (2026-11-21).** I read the full texts of these papers:

- Choudhury–Loizou arXiv v1: Section 3 and Appendix D.3.
- Greenberg–Loizou, [arXiv:2610.16886v1](https://arxiv.org/abs/2610.16886) (Oct 2026): monotone constrained VIs. Its related work credits weak-Minty results only to Choudhury–Loizou.
- Yoon et al., [arXiv:2609.26581v1](https://arxiv.org/abs/2609.26581): monotone only.
- Rudomanov et al., [arXiv:2611.20296v1](https://arxiv.org/abs/2611.20296) (15 Nov 2026): monotone. It cites Thm 3.6 as O(1+(L₀R/ε+L₁R)²).

Vankov et al. (ICML 2024) assume p-quasi-sharpness, which is a strict subclass of Minty; I did not re-read it. The result was added in commit `a0d524d3` on 2026-11-21. The companion note's attribution matches what I verified: it already credits the Thm 3.6 proof. Its ε⁻²-versus-ε⁻¹ and L₁^{6/5} comparisons come from the paired lower bound and the class difference, not from this upper bound.

**Conclusion**

**No: this is a known bound in a slightly relabelled form.** The rate is the same, and so is the proof.

The strongest baseline is Choudhury–Loizou's Theorem 3.6. Its statement assumes monotonicity, but its proof uses only `⟨F(y), y−x*⟩ ≥ 0` at the extrapolation point, which is exactly the Minty condition. Applied verbatim to Minty operators it gives:

| | Operator calls for ‖F(x̂)‖ ≤ ε |
|---|---|
| Choudhury–Loizou Thm 3.6 proof, under Minty | ≈ 2⌈9.9 R²(L₀/ε+L₁)²⌉ |
| This theorem | 2(1+⌈32 R²(L₀/ε+L₁)²⌉) |

That is the same order with a somewhat worse constant, in every parameter regime. The extension from monotone to Minty operators genuinely enlarges the class: rotational fields `e^{a‖v‖}Jv` are Minty but not monotone. But the published argument already reaches that class without changes. The frozen output adds nothing either, because the best iterate can be observed for free.

What is established is a Lean-verified, deterministic statement of a known polynomial extragradient bound for (L₀,L₁)-Lipschitz Minty operators. Any novelty for this research question rests on the separate lower-bound theorem, not on this upper bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
