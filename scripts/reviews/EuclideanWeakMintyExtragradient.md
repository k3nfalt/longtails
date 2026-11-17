# Novelty assessment: EuclideanWeakMintyExtragradient

[`result`](../../LongTails/Theorems/EuclideanWeakMintyExtragradient.lean) proves the following ([setup](../../LongTails/Setups/EuclideanWeakMinty.lean), [algorithm](../../LongTails/Algorithms/EuclideanWeakMintyExtragradient.lean)). Let `F : ℝᵈ → ℝᵈ` be `L`-Lipschitz with a root `x⋆` satisfying `‖x⋆−x₀‖ ≤ R` and `⟨F(x),x−x⋆⟩ ≥ −ρ‖F(x)‖²` for all `x`, where `0 ≤ ρ ≤ 1/(20L)`, `28ε ≤ LR` and `d ≥ 257`. Then the deterministic EG+ iteration `y = x − F(x)/(2L)`, `x⁺ = x − F(y)/(10L)`, returning the queried base point with the smallest residual, gives `E‖F(x̂)‖ ≤ ε`. The randomness is trivial, so in fact `‖F(x̂)‖ ≤ ε` holds surely.

**Complexity.** Here `L` is the Lipschitz constant, `R` bounds the initial distance, `ρ` is the weak-Minty parameter, and `ε` is the residual target. The Lean budget is `2+2⌈200L²R²/ε²⌉` exact operator calls:

  `O(1 + L²R²/ε²)`, valid for `ρL ≤ 1/20`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Diakonikolas–Daskalakis–Jordan, AISTATS 2021 / arXiv:2011.00364v2](https://arxiv.org/abs/2011.00364), Thm 3.2 (EG+). Prior. Their `ρ` is twice ours. | `min_i‖F(ū_i)‖² ≤ 2L R²/((k+1)(1/(4L)−2ρ))`. At `ρL ≤ 1/20` this needs about `27L²R²/ε²` calls. `O(1+L²R²/ε²)` → `O(1+L²R²/ε²)` | None: same order (worse constant, `≈400` vs `≈27`) | None | None (both best iterate, same residual) | Narrower: `ρL ≤ 1/20` vs `ρL < 1/8`. The extra `d ≥ 257` and `28ε ≤ LR` are needed only by the companion lower bound. |
| [Pethick et al., ICLR 2022 / arXiv:2302.09831](https://arxiv.org/abs/2302.09831) (CEG+); [Pethick–Mavrothalassitis–Cevher, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf). Prior. | `O(1+L²R²/ε²)` → `O(1+L²R²/ε²)` (theorem statements not re-read in full) | None: same order | None; prior results also allow constraints | None | Prior admissible range is much wider (`ρL` up to about `1/2`, and beyond for the ICLR 2025 method). |
| Repository: [NonEuclideanWeakMintyExtragradient](../../LongTails/Theorems/NonEuclideanWeakMintyExtragradient.lean). Prior (commit `865fd38`, 2026-10-20). | Take `h=½‖·‖²`, `μ=1`, `D=R²/2`: `2+2⌈400L²D/(με²)⌉ = 2+2⌈200L²R²/ε²⌉`, the identical budget | None: identical | None (Euclidean special case) | Sure residual → expected residual (weaker, equivalent here) | None |

**Reduction check and mechanism.** The result is a direct substitution into the repository's non-Euclidean theorem. The [proof module](../../LongTails/Proofs/EuclideanWeakMintyExtragradientRun.lean) computes the Euclidean Bregman divergence, transports `F` through the Riesz map, and calls the existing `execute_accuracy` lemma. Mathematically it is DDJ's EG+ analysis with a smaller ρ range. No new mechanism is involved. The only role of the theorem is to restate the known upper bound in the setup and expected-residual criterion of the companion [lower bound](../../LongTails/Theorems/EuclideanWeakMintyLowerBound.lean).

**Search coverage.** On 2026-11-17 (UTC) I checked DDJ (arXiv v2, AISTATS 2021). Its Assumption 1 was read verbatim, but the Thm 3.2 constants came from a partial HTML extraction, and the factor of 2 between the two ρ conventions comes from that reading. I also ran searches covering Pethick et al. (ICLR 2022, 2025), Böhm (TMLR 2023, OGDA+, also `O(ε⁻²)`) and Lee–Kim (FEG, which requires comonotonicity and does not apply here). The companion note says plainly that the rate is not new, and that agrees with this assessment. The theorem was introduced in commit `98684e93` (2026-11-17). I did not assess novelty claims for the lower bound.

**Conclusion.**

**No: this gives the known EG+ rate again, with a narrower parameter range.** The strongest baseline is Diakonikolas–Daskalakis–Jordan's EG+ (Theorem 3.2). It covers the same unconstrained Lipschitz weak-Minty class with a best-iterate residual guarantee:

| | allowed `ρL` | calls for `‖F(x̂)‖ ≤ ε` |
|---|---|---|
| DDJ EG+ (2021) | `< 1/8` | `O(1+L²R²/ε²)` |
| this result | `≤ 1/20` | `2+2⌈200L²R²/ε²⌉ = O(1+L²R²/ε²)` |

It also follows exactly from the repository's earlier non-Euclidean weak-Minty theorem by taking the Euclidean mirror. That substitution reproduces the budget term for term.

Its only purpose is to pair with the companion lower bound, which uses the same setup and criterion. Any novelty in the pair belongs to that lower bound, which I did not assess here. The rate is unchanged, the scope is narrower (smaller ρ range, extra conditions on dimension and accuracy) and the output is still best-iterate, so no independent advantage remains today.

The only defensible claim is a formal statement of the known `O(L²R²/ε²)` EG+ upper bound in the lower bound's setup.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
