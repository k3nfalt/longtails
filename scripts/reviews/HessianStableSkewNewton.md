# Novelty assessment: `HessianStableSkewNewton`

[`result`](../../LongTails/Theorems/HessianStableSkewNewton.lean) proves the following. Let `F` be a monotone operator on a finite-dimensional space whose Jacobian is `DF = S + H(x)`, with `S` constant skew and `H(x)` symmetric PSD and `M`-Hessian-stable ([setup](../../LongTails/Setups/HessianStableSkewMonotone.lean)). Then the deterministic method [`BallAnchoredNewton`](../../LongTails/Algorithms/BallAnchoredNewton.lean) outputs a stopped iterate `ẑ` with `‖F(ẑ)‖ ≤ ε`, using exact `F`/`DF` queries.

**Budget (per channel; both `F` and `DF` calls are counted):**

  N = O( (1 + (MD)^{2/3}) · log³(3 + MD + MΛ(D + 1/M)²/ε) )

The parameters are:
- `M`: the Hessian-stability constant;
- `D ≥ ‖x₀ − x⋆‖`;
- `ε`: the target residual;
- `Λ`: a bound on `‖DF‖` over `B(x⋆, 3D + 1/(4M))`. `Λ` is used only in the budget.

Each Newton step also solves a strongly monotone affine VI over a Euclidean ball, which is charged no oracle cost.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jiang–Yoon, AEP, p = 2 ([arXiv:2609.30212v1](https://arxiv.org/abs/2609.30212), 24 Sep 2026, Thm 4.4/4.6; prior, unrefereed). **Overlap:** instances whose `DF` is globally `L₂`-Lipschitz (e.g. logistic–bilinear–logistic). | `O((L₂D²/ε)^{2/5} log(1+L₂D²/ε))` → `O((1+(MD)^{2/3}) log³(3+MD+MΛ(D+1/M)²/ε))` | ε-dependence improves from polynomial to polylogarithmic. The gain holds when `(L₂D²/ε)^{2/5} ≫ (1+MD)^{2/3}·log³(…)`, e.g. fixed instance and `ε → 0`. | Classes are incomparable. AEP needs a global Lipschitz Jacobian but allows any monotone `F`. This result needs constant skew plus Hessian stability, and it covers exp-type losses that have no global `L₂`. | None. Both require exact oracles and certify a residual (tangent residual = `‖F‖` here). AEP's `Ω((L₂D²/ε)^{2/5})` lower bound is for the Lipschitz-Jacobian class and does not apply here. | Constant-skew restriction excludes nonlinear coupling. Loses when `(MD)^{5/3}` is large relative to `L₂D²/ε`. Ball-VI subproblem is free. |
| Yoon–Ryu, EAG ([ICML 2021, arXiv:2102.07922](https://arxiv.org/abs/2102.07922), Thm 1). **Overlap:** `F` globally `L`-Lipschitz, with `L ≥ Λ`. | `O(LD/ε)` `F`-calls → the budget above | Polylog vs `1/ε` when `LD/ε ≫ (1+MD)^{2/3} log³(…)`. | Same incomparability as the AEP row. | None | Uses second-order (`DF`) queries instead of first-order ones. |
| Carmon et al., ball acceleration ([NeurIPS 2020, arXiv:2003.08078](https://arxiv.org/abs/2003.08078), Thm 6, Def 7, LB Thm 24 in v1); Doikov ([arXiv:2308.14742](https://arxiv.org/abs/2308.14742), Math. Program. 2025). **Special case only:** `S = 0` (minimization), with an objective-gap criterion. | `Õ((MD)^{2/3})` Newton/linear-solve steps (Carmon); `O(MD log(1/ε))` (Doikov) → same order `Õ((MD)^{2/3})` | None on the `S = 0` overlap: same order, possibly with more logarithms. | `S = 0` gradient fields → arbitrary constant skew `S` (bilinearly coupled QSC saddles, `F = ∇h + Sz + b`). | Function gap → residual `‖F‖`. On the overlap, this conversion costs only logarithms. | None beyond the free subproblem |

**Reduction check.** I found no standard reduction:
- Dualizing one block of `f(x) + xᵀBy − g(y)` gives `f + g*∘Bᵀ`, and `g*` (e.g. the entropy for logistic `g`) is not Hessian-stable with bounded `M`.
- Regularization or first-order methods keep polynomial dependence on `1/ε`.

**Proof ancestry.** Jiang–Yoon's anchored potential and Carmon et al.'s ball-step growth argument are proof ancestors rather than baselines. Two pieces appear to be new and are the part not implied by those works:
- the skew-robust ball-constrained Newton contraction, which uses polarization of the self-adjoint difference `H(u) − H(ξ)`;
- the step search based on a displacement modulus.

**Search coverage (2026-11-06).** Searched arXiv, NeurIPS/ICML/ICLR and journal results for: ball oracle × monotone/VI/minimax; Hessian-stable/QSC × saddle/VI; second-order monotone-inclusion methods. Limits and discrepancies:
- I read the Carmon, Jiang–Yoon and Doikov theorems only partly. Some theorem numbers come from a v1 HTML summary.
- I did not check [arXiv:2609.23557](https://arxiv.org/abs/2609.23557) or the self-concordant convex–concave path-following literature (Nesterov–Nemirovski), which covers a different, barrier-type class.
- Mismatches with the companion note:
  - It cites Carmon et al. as "Thm 1/Thm 3".
  - It claims that `Λ ≈ e^{MD}` gives `Õ((MD)^{5/3})`. The `log³` factor actually gives `O((MD)^{2/3}(MD + log(1/(Mε)))³)`, i.e. about `(MD)^{11/3}`.
- The result was committed today (2476f596), so every cited work is prior.

## Conclusion

**Yes: on this class, the dependence on accuracy drops from polynomial to polylogarithmic.** The strongest applicable prior guarantee is Jiang–Yoon's second-order AEP, which needs a globally Lipschitz Jacobian. On the instances both cover (e.g. logistic losses with bilinear coupling):

| | Calls to reach `‖F‖ ≤ ε` |
|---|---|
| AEP (prior) | `Õ((L₂D²/ε)^{2/5})` |
| This result | `O((1+(MD)^{2/3}) log³(3+MD+MΛ(D+1/M)²/ε))` |

The gain holds once `ε` is small enough that `(L₂D²/ε)^{2/5}` exceeds `(MD)^{2/3}` times the cubed logarithm. AEP still wins at moderate accuracy when `MD` is large. When `Λ` grows like `e^{MD}` (exp-type losses), the logarithm adds a factor of about `(MD)³`. Each Newton step also solves a ball-constrained affine VI that is not charged to the budget.

The scope is narrower than general monotone problems, because the skew part must be constant. When the skew part is zero (minimization), the result only matches Carmon et al.'s ball-oracle rate. I found no published method for monotone VIs or saddle problems with polylogarithmic ε-dependence under Hessian stability, and no reduction to minimization or to known theorems. That is evidence of priority but not proof: arXiv:2609.23557 and the self-concordant saddle literature were not fully checked.

What can be claimed is the first checked `Õ((MD)^{2/3})`, polylog-in-`1/ε` second-order guarantee for Hessian-stable monotone equations with constant skew coupling.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
