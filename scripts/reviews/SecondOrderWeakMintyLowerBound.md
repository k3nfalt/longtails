# Novelty assessment: SecondOrderWeakMintyLowerBound

The [theorem](../../LongTails/Theorems/SecondOrderWeakMintyLowerBound.lean) proves `NonConvergence` on the [setup](../../LongTails/Setups/HighDimensionalWeakMintySecondOrder.lean); there is no algorithm restriction, and the hard instance is built in [SecondOrderMintyLowerBound](../../LongTails/Proofs/SecondOrderMintyLowerBound.lean). Take any randomized adaptive algorithm that makes b ≤ ⌊M/2¹⁵⌋ exact calls, each returning either `F(x)` or the Jacobian `J(x)`. Then some operator `F : ℝᵈ → ℝᵈ` with all of the following makes it fail, meaning E‖F(x̂)‖ > ε or the residual is not integrable:
- F is L₁-Lipschitz, with an L₂-Lipschitz Jacobian;
- F has a zero x⋆ with ‖x₀ − x⋆‖ ≤ R;
- F satisfies the Minty condition (ρ = 0), and therefore every weak-Minty condition with ρ ≥ 0.

**Proved necessary calls.** Here L₁ and L₂ are the Lipschitz constants of F and of J, R bounds the initial distance, ε is the expected-residual target and d is the dimension. The theorem gives

  N ≥ Ω( min{ L₂R²/ε, L₁²R²/ε² } ),

valid when min{L₂R²/ε, L₁²R²/ε²} ≥ 2¹⁵, d ≥ min{…}³ and ρL₁ ≤ 1. The second term is the smaller one exactly when ε ≥ L₁²/L₂. The regime is nonempty: L₁ = L₂ = R = 1, ε = 2⁻¹⁶ and d = 2⁴⁸ satisfy it.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhang et al., [arXiv:2609.13462](https://arxiv.org/abs/2609.13462) (Sep 2026, preprint, prior). **Monotone special case**; I checked the abstract only. | Ω((L₂R²/ε)^{2/5}) → Ω(min{L₂R²/ε, L₁²R²/ε²}) | Larger by a factor (L₂R²/ε)^{3/5} when ε ≤ L₁²/L₂. Example: L₁ = L₂ = R = 1 gives ε^{-2/5} → ε^{-1}. | Monotone hard instances → non-monotone Minty instances (a non-gradient chain) | Both cover randomized algorithms | Needs d ≥ M³, a stronger dimension requirement; I did not check theirs. Accuracy criterion and constants in their abstract not verified. |
| Repository [EuclideanWeakMintyLowerBound](../../LongTails/Theorems/EuclideanWeakMintyLowerBound.lean) (2026-11-17, unpublished) | Ω(min{L₁²R²/ε², d^{1/3}}), **F-only algorithms** → bound above, for algorithms with Jacobian access | Not comparable (different oracle). It adds the L₂R²/ε term, which is smaller when ε < L₁²/L₂. | Lipschitz-only class → the subclass with a C^{1,1} operator. The p=1 chain is not C¹. | Value-only queries → value plus full-Jacobian queries | The full-dimension range d ≥ 257 is lost; this result needs d ≥ M³ |
| Upper bounds: Vyas–Bullins [arXiv:2304.08389](https://arxiv.org/abs/2304.08389) Thm 3.5 (p=2, defect 0); Lin–Jordan [Perseus](https://arxiv.org/abs/2205.03202) Thm 3.7 (bounded domain); DDJ [AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html) EG+; repository [upper theorem](../../LongTails/Theorems/SecondOrderWeakMintyUpperBound.lean) | Upper O(1 + min{L₂R²/ε, L₁²R²/ε²}) vs. lower ⌊M/2¹⁵⌋ | Not an improvement over an upper bound. It certifies that the upper bound is optimal up to a factor of about 2⁴² when M ≥ 2¹⁵ and d ≥ M³. | None | None | The constant gap is large. Nothing is shown for d < M³. |

**Reduction check.** Known lower bounds do not transfer:
- Monotone instances admit (L₂R²/ε)^{2/5}-type methods.
- Linear instances are useless here, because one Jacobian query reveals the whole operator.
- The Carmon et al. higher-order chains are gradients of nonconvex functions, and they are not Minty.
- The repository's p=1 Minty chain is not C¹, and its Jacobian would leak information.

The new mechanism is a C^{1,1} gated chain that is Minty everywhere, with exactly flat gates, so that both values and Jacobians reveal only a prefix. It also needs a smooth radial wall that preserves the Minty condition and the residual floor, and a link length r = R/√m chosen so that both the L₁ and the L₂ constraints bind. The proof ancestry is credited correctly in the note:
- flat-gate jet hiding, from Carmon–Duchi–Hinder–Sidford and [arXiv:2609.28246](https://arxiv.org/abs/2609.28246);
- the random-injection and prefix-simulation counting, from the repository's PR #176;
- the dead-zone Minty chain, from PR #182.

Given PR #182, the construction is a natural smoothing of an existing idea rather than a new paradigm.

**Search coverage.** I searched on 2026-11-19 for Minty, weak-Minty, nonmonotone, higher-order, second-order and Jacobian combined with "lower bound".
- I read Perseus v7 (Thm 3.7, the monotone-only Thm 3.11, and Remark 3.13, which calls the Minty lower bound "largely unexplored and missing"), Vyas–Bullins and Agafonov et al. [arXiv:2405.15990](https://arxiv.org/abs/2405.15990) (whose Thm 4.3 lower bound is monotone only).
- I also read Anagnostides et al. [arXiv:2504.03432](https://arxiv.org/abs/2504.03432) (FOCS 2026). It gives poly(d, log(1/ε)) methods for constrained Minty VIs, so some high-dimension condition is necessary. Its Ω(2^d) bound concerns a different (MVI) target.
- For 2609.13462, 2609.28246 and Soleymani–Farina–Jaillet [arXiv:2611.11691](https://arxiv.org/abs/2611.11691) I checked abstracts only.

None of these gives a Minty lower bound for value-plus-Jacobian oracles. The result entered the repository in commit 26b45d27 (2026-11-19). The companion note's monotone exponent 2/5 is consistent with the 2609.13462 abstract. Its claim that the result "settles" Lin–Jordan's question applies only to p = 2, the unconstrained residual criterion and d ≥ M³. Perseus itself treats bounded constrained VIs.

## Conclusion

**Yes: this is a new lower bound showing that second-order Minty and weak-Minty problems, in high dimension, are no easier than the known upper bounds.**

The strongest previous applicable lower bound comes from the monotone special case, which is weaker by a polynomial factor. The best upper bounds come from combining second-order Minty methods (Vyas–Bullins, Perseus) with extragradient:

| | calls for E‖F(x̂)‖ ≤ ε, with value and Jacobian calls counted |
|---|---|
| Previous lower (monotone instances) | Ω((L₂R²/ε)^{2/5}) |
| This result (any randomized method, d ≥ M³) | Ω(min{L₂R²/ε, L₁²R²/ε²}) |
| Upper (prior methods; repository hybrid) | O(1 + min{L₂R²/ε, L₁²R²/ε²}) |

So, in that dimension regime, the complexity is Θ(min{L₂R²/ε, L₁²R²/ε²}) up to a universal constant of roughly 2⁴². The bound also separates the Minty class from the monotone class by a factor (L₂R²/ε)^{3/5}.

The limits are the requirement d ≥ M³ and the restriction to p = 2; low-dimensional methods show that the dimension caveat is real. Within this repository, the result smooths the earlier p=1 Minty chain. In the literature I found no lower bound of this kind, and Lin–Jordan explicitly list one as open, but a search cannot prove priority. What can be claimed is the first verified high-dimensional lower bound for Minty VIs with second-order oracles, matching known upper bounds.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
