# Novelty assessment: FullRangeWeakMintyFirstOrder

[`result`](../../LongTails/Theorems/FullRangeWeakMintyFirstOrder.lean) concerns an unconstrained, finite-dimensional operator `F` ([setup](../../LongTails/Setups/WeakMintySecondOrder.lean)) that is `L₁`-Lipschitz, has an `L₂`-Lipschitz Jacobian and has a root `x⋆` with `‖x₀−x⋆‖ ≤ R` and `⟨F(x),x−x⋆⟩ ≥ −(ρ/2)‖F(x)‖²` for all `x`, where `ρL₁ < 2`. For such `F` the theorem proves that a public selector ([algorithm](../../LongTails/Algorithms/FullRangeWeakMintyFirstOrder.lean)) surely returns a point with `‖F(x_out)‖ ≤ ε`. The selector runs either a value-only optimistic (Popov / OGDA+) iteration that stops at the first point passing the residual test, or the repository's earlier value-plus-Jacobian hybrid.

**Complexity.** Write `δ = 1−ρL₁/2 ∈ (0,1]` for the margin to the boundary of the full range. The theorem counts value and full-Jacobian calls, at one call each. The Lean budget gives

- `O(1 + L₁²R²/(δ²ε²))` value calls when `L₁²/ε ≤ 2¹⁷L₂log(2/δ)/δ³`; in this case the bound is also at most `HL₂R²/ε + 1`, where `H = 2²⁰log(2/δ)/δ⁵`;
- `O(δ⁻⁵log(2/δ)(1 + L₂R²/ε))` value and Jacobian calls otherwise.

One formula valid in both cases is `O(δ⁻⁵log(2/δ) + min{L₁²R²/(δ²ε²), δ⁻⁵log(2/δ)L₂R²/ε})`. The value-only lemma (`value_execute_accurate`) proves the first bound for every parameter choice and uses neither `J` nor `L₂`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Böhm, OGDA+, [arXiv:2201.12247v3](https://arxiv.org/abs/2201.12247) (Jun 2023; TMLR 2023), Thm A.1. Prior. Same half-defect convention. | Bound `(1/k)Σ‖F(u_i)‖² ≤ ‖u₀+aF(u₀)−u⋆‖²/(kaγ(aλγ−ρ))`. Its constraints `aλγ>ρ`, `λγ≤2` and (11) force `γ=O(δ²)` and `aλγ−ρ=O(δ/L₁)`. Optimizing them gives **`O(1+L₁²R²/(δ³ε²))`** single calls (my derivation) → `O(1+L₁²R²/(δ²ε²))` | Factor `δ⁻¹`. The gain is asymptotic only as `δ→0`; for `δ ≥ c` (e.g. `ρL₁ ≤ 1`) the order is the same. | None (same class and range) | None. Both methods need `L₁` and `ρ`. Best iterate versus first certified iterate is interchangeable because `F(u_k)` is queried anyway. | Same recurrence, but with relaxation `≈δ/4` instead of `O(δ²)`, which lies outside A.1's admissible region. The public theorem additionally assumes an `L₂`-Lipschitz Jacobian. |
| Alacaoglu–Kim–Wright, [arXiv:2402.05071v2](https://arxiv.org/abs/2402.05071) (Aug 2024; ICML 2024), Thm 3.1 / Cor 3.2. Prior. Defect `ρ/2`. | `Õ((1+ηL₁)R²/(ε²(η−ρ/2)²(1−ηL₁)))`. With `η` at the midpoint this is `Õ(L₁²R²/(δ³ε²))`, with an inner-loop logarithm in `1/ε` → `O(1+L₁²R²/(δ²ε²))` | `δ⁻¹` and a logarithm | None on the overlap. AKW also allow constraints `G`. | Their criterion is a resolvent residual. A `‖F‖` conversion (Remark 3.4) exists but I did not read it. | None on the unconstrained overlap |
| Pethick–Mavrothalassitis–Cevher, [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), Thm 5.5 / Cor 6.3. Prior. | `O((1+L₁²R²/ε²)δ⁻³log(2/δ))`, taken from an earlier repository reconstruction and not re-derived here → `O(1+L₁²R²/(δ²ε²))` | `δ⁻¹log(2/δ)` | None on the overlap. They also handle constraints. | Their guarantee bounds a squared residual; it is equivalent after a square root. | None on the overlap |
| Repository: [FullRangeSecondOrderWeakMinty](../../LongTails/Theorems/FullRangeSecondOrderWeakMinty.lean) (`85dcf51`, 2026-10-16). Same setup. | `⌈H(1+L₂R²/ε)⌉` → never larger (the note's argument checks out) | Strict gain when `L₁²R²/(δ²ε²) = o(δ⁻⁵log(2/δ)(1+L₂R²/ε))`. Example: fixed `L₁,L₂,R,ε` with `δ→0` gives `δ⁻⁵log(1/δ) → δ⁻²`. | None | None | None |

On the half range `ρL₁ < 1`, EG+ ([DDJ 2021, Thm 3.2](https://arxiv.org/abs/2011.00364)), CEG+ and Choudhury et al.'s SPEG ([arXiv:2302.14043](https://arxiv.org/abs/2302.14043)) already give `O(1+L₁²R²/ε²)`. There the value-only bound adds nothing.

**Reduction and mechanism.** Retuning Böhm's Theorem A.1 cannot give `δ⁻²`. Its constraints bound `γ(aλγ−ρ)` by `O(δ³/L₁)`. Inexact-proximal frameworks (AKW, Pethick et al.) pay an extra `δ⁻¹` for their inner solves. What is new is the potential `‖u+ah‖²+‖g−h‖²−2ab‖h‖²`, whose cross term is negative and which permits relaxation of order `δ`. The proof uses only nonexpansiveness of `F/L₁` and weak Minty. The proof module has no `sorry`, but I did not run the build or the axiom audit.

**Search coverage (2026-11-25 UTC).** I read Böhm v3 (Thms 3.1, 3.3, A.1, 4.1, through an HTML transcription), AKW v2 (Section 3 through a summarized extraction), Tran-Dinh's [survey](https://arxiv.org/abs/2303.17192) (past-EG only for `ρL ≲ 1/12`), Choudhury's [2025 thesis](https://arxiv.org/abs/2512.12235) (only `ρL₁ < 1` in this convention, and only partly read), RAPP ([arXiv:2310.13459](https://arxiv.org/abs/2310.13459), which needs cohypomonotonicity, a stronger assumption) and [arXiv:2611.11691](https://arxiv.org/abs/2611.11691) (a different oracle model). I did not re-read Pethick et al. 2025. The companion note's claims (Böhm cubic, AKW and Pethick cubic up to logarithms) agree with my checks. Git dates the value branch to commit `2ebc3c38` (2026-11-26 commit date).

## Conclusion

**Yes, but only near the boundary: the margin cost over the full weak-Minty range improves from cubic to quadratic.**

The strongest prior baseline is Böhm's OGDA+ (Theorem A.1), which uses the same single-value-call recurrence and reaches the full range `ρL₁ < 2`. The inexact-proximal methods of Alacaoglu–Kim–Wright and Pethick et al. are no better in `δ`.

| | value calls for `‖F‖ ≤ ε` |
|---|---|
| Böhm OGDA+, optimized (prior) | `O(1 + L₁²R²/(δ³ε²))` |
| this value branch | `O(1 + L₁²R²/(δ²ε²))` |

The speedup is a factor `1/δ`, so it matters only when `ρL₁` approaches 2. For `ρL₁ ≤ 1` the bound is the long-known EG+ order. The mechanism is a new potential that allows a much larger relaxation than Böhm's analysis. The public theorem assumes a Lipschitz Jacobian and selects this branch only when `L₁²/ε ≲ L₂log(2/δ)/δ³`, although the underlying lemma needs neither condition.

The comparison establishes the `δ⁻¹` gain over the checked analyses. The search does not establish priority, and no lower bound on the margin exponent is known. What can be claimed is a better proved margin dependence for an existing algorithm family on an existing class: a real but modest refinement in a boundary regime.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
