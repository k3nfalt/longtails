# Novelty assessment: FullRangeSecondOrderWeakMinty

[`result`](../../LongTails/Theorems/FullRangeSecondOrderWeakMinty.lean) proves the following. Take an unconstrained, finite-dimensional operator `F` that is `L₁`-Lipschitz, has an `L₂`-Lipschitz Jacobian, and satisfies the standard weak Minty condition `⟨F(x),x−x⋆⟩ ≥ −(ρ/2)‖F(x)‖²` for all `x`, with `ρL₁ < 2` ([setup](../../LongTails/Setups/WeakMintySecondOrder.lean)). Using exact value and full-Jacobian queries, the [hybrid cubic-model/Picard method](../../LongTails/Algorithms/WeakMintyHybrid.lean) returns a queried point with `‖F(x_out)‖ ≤ ε`.

**Complexity.** Let `R ≥ ‖x₀−x⋆‖` and `δ = 1−ρL₁/2 ∈ (0,1]`. The total number of value and Jacobian calls is

  `O( (1 + L₂R²/ε) · δ⁻⁵ · log(2/δ) )`

This follows directly from the Lean budget `⌈2²⁰(1+L₂R²/ε)log(2/δ)/δ⁵⌉`. The bound has no other dependence on `L₁`, and the algorithm does not need to know `R`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vyas–Bullins, [arXiv:2304.08389v1](https://arxiv.org/abs/2304.08389v1) (Apr 2023, preprint), Thm B.1 (q=p=2, standard weak MVI). **Special case:** needs ρ small relative to `D = max_k L₁‖z_{k+½}−z⋆‖` | Our reconstruction with consistent scaling, assuming Fejér iterates `‖z_k−z⋆‖ ≤ R`: `O(1+L₂R²/ε)` when `ρ√(L₁L₂R) ≲ 1` → `O((1+L₂R²/ε)δ⁻⁵log(2/δ))` | None: same order wherever B.1 applies (we lose `δ⁻⁵log(2/δ)`) | `ρ ≲ 1/√(L₁L₂R)`, a trajectory-dependent condition → `ρL₁ < 2` for every `R`. This covers large initial distances. | None (both give a best/first-certified residual) | Same Jacobian oracle and cubic-root subproblem. The paper's displayed condition and its proof scaling disagree. |
| Same paper, Thm 3.5 (p=2, weak MVI with defect `ρ'‖F‖^{3/2}`) | `O(1+L₂R²/(c₁ε))` with `c₁ = 15/16 − O(ρ'√L₂)` → `O((1+L₂R²/ε)δ⁻⁵log(2/δ))` | None on the overlap. At ρ=0 (Minty) the two match up to `δ`-factors. | The classes are **incomparable**. Squared and 3/2-power defects swap strength depending on residual scale. Unbounded `F` with a squared defect, such as the note's rotation field, violates every global 3/2-power condition. | None | This result additionally needs a global `L₁`-Lipschitz `F`. Thm 3.5 does not. |
| Vyas–Bullins, [arXiv:2603.13491v1](https://arxiv.org/abs/2603.13491v1) (Mar 2026, prior preprint), Thm B.3 | Requires `sup‖F‖ ≤ D` and ρ small relative to D (the draft still carries "fix constants") → as above | None where it applies | Globally bounded `F` plus a D-dependent bound on ρ → unbounded `F` with `ρL₁ < 2` | None | None beyond the above |
| Pethick–Mavrothalassitis–Cevher, [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), Thm 6.1 / Cor 6.3 with A=0 (first-order, same range `ρL₁<2`) | Squared-residual `O((1+n)R²/(γ²(·)²ε))` with `n = O(δ⁻¹log(3/δ))`. In norm accuracy, our reconstruction gives `O((1+L₁²R²/ε²)δ⁻³log(2/δ))` F-calls → `O((1+L₂R²/ε)δ⁻⁵log(2/δ))` | Better exponent: `ε⁻²` → `ε⁻¹`. The gain holds when `ε ≪ δ²L₁²/L₂` and `ε ≲ L₂R²`. Example: fixed δ, `L₁ = L₂ = R = 1`, ε→0 gives a `1/ε` speedup. | None (same class, apart from smoothness) | None | Needs an `L₂`-Lipschitz Jacobian and **full Jacobian queries**, each counted as one call (not Hessian-vector products). Exact cubic-root solves are via choice, with no arithmetic cost. Worse in `δ` and when `ε ≳ L₁²/L₂`. Pethick et al. also handle constraints. |

**Reduction check.** Plugging into Vyas–Bullins B.1 does not work, because its defect absorption needs `ρ√(L₂·L₁·dist)` small along the whole trajectory, and the weak Minty condition alone does not shrink distances. The obvious two-phase scheme (first-order until `‖F‖ ≤ G`, then cubic steps) also fails, because the residual is not monotone. The genuinely new step is a per-attempt argument:
- every cubic-model root at an anchor with residual at most `G = δ²L₁²/(64L₂)` gives an admissible relaxed-proximal step;
- the charging inequality `‖F(x)‖² ≥ εG` makes every non-terminal attempt, cubic or Picard, pay `Ω(δ⁴ε/L₂)` of squared distance.

The relaxed inexact-proximal correction and the `O(1)`-step Picard solver come from Pethick et al. 2025, which is proof ancestry rather than the source of this rate. I verified the separating example's weak Minty constant (`ρ = 2/10001`) and `L₁ = 1601`. Finiteness of `L₂` is clear, but I did not check the stated constant 4000.

**Search coverage.** The search was run on 2026-10-16. It covered arXiv, ICLR/NeurIPS proceedings, Perseus ([Lin–Jordan, Math. Prog. 2024](https://arxiv.org/abs/2205.03202), Thm 3.7: Minty only, bounded constraint set), Agafonov et al. NeurIPS 2024 (Minty only), and targeted queries for second-order and weak-Minty work from 2024–2026. I found no prior second-order result for the standard weak Minty condition without a smallness restriction. Git dates the result to commit `85dcf51` (2026-10-16). The companion note's citations and its description of the B.1 inconsistency match what I read. Its first-order δ-exponent is a reconstruction that I did not re-derive in full.

## Conclusion

**Yes: for the standard weak Minty class over its full range `ρL₁ < 2`, this is the first checked second-order guarantee, and it beats the first-order rate for small ε.**

The strongest applicable prior guarantee on the full class is the first-order method of Pethick–Mavrothalassitis–Cevher (ICLR 2025). Prior second-order analyses (Vyas–Bullins 2023/2026) need ρ to be small relative to a trajectory scale or to a global bound on `‖F‖`.

| | norm-residual calls |
|---|---|
| Pethick et al. (F-calls) | `O((1+L₁²R²/ε²)·δ⁻³log(2/δ))` |
| This result (F + Jacobian calls) | `O((1+L₂R²/ε)·δ⁻⁵log(2/δ))` |

The gain holds for `ε ≪ δ²L₁²/L₂`. In return, the result needs a Lipschitz Jacobian and pays for full Jacobian queries; it is worse in δ and for large ε. Where the earlier second-order theorems apply, the rate is the same up to δ-factors. The contribution there is coverage: large initial distances and unbounded operators. One example (a radially contracting, rotating field) satisfies every assumption here and none of the earlier second-order ones.

The comparison establishes the gain over the checked baselines. The search found no prior result of this kind, but that does not prove priority, and no matching lower bound is known. What can be claimed is an inverse-linear second-order residual complexity for the standard weak Minty condition with no smallness restriction, obtained through a new charging argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
