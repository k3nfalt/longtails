# HighDimensionalHeavyTailedNcscUpperBound: novelty assessment

The [theorem](../../LongTails/Theorems/HighDimensionalHeavyTailedNcscUpperBound.lean) shows that the repository's heavy-tailed NC–SC solver `saddleAlgorithm` ([algorithm](../../LongTails/Algorithms/HeavyTailSaddleEstimator.lean)) returns `X` with `P(‖∇Φ(X)‖ > ε) ≤ δ` on the [restricted setup](../../LongTails/Setups/HighDimensionalHeavyTailedNcsc.lean). That setup is the general [HeavyTailedNcsc](../../LongTails/Setups/HeavyTailedNcsc.lean) class with `E = F = ℝ^d`, `Ω = ℝ` and `x₀ = y₀ = 0`, plus extra lower-bound regime conditions. The proof is a three-line call to [HeavyTailedNcscAccelerated](../../LongTails/Theorems/HeavyTailedNcscAccelerated.lean), and the budget is identical.

**Complexity.** The parameters are:
- L: joint gradient-Lipschitz constant
- μ: strong-concavity constant in y
- p ∈ (1,2]: central-moment order, with σ the moment scale
- Δ: initial primal gap
- G: bound on ‖∇_y f(x₀,y₀)‖
- ε: gradient-norm accuracy
- δ: failure probability

Up to universal constants, the number of joint stochastic-gradient calls is

N = O( (2⁸⁰p/(p−1))^{(3p−2)/(p−1)} · ℓ^{(5p−3)/(p−1)} · [ √(L/μ)·(1 + LΔ/ε² + ℓ₀) + (LΔ/ε²·(L/μ)^{p/(2(p−1))} + (L/μ)^{p/(p−1)})·(σ/ε)^{p/(p−1)} ] ),

where
- ℓ₀ = log(2 + L⁴(Δ+G²/μ)/(μ³ε²))
- ℓ = 1 + log(2 + L/μ + 1/δ + LΔ/ε² + (Lσ/(με))^{p/(p−1)} + ℓ₀)

The theorem only applies when all of these hold: 8μ ≤ L, δ ≤ 1/4, LΔ ≥ 2³²ε², G√(L/μ) ≥ 4176ε, and d ≥ 2⁴⁰(1 + LΔ/ε²·(1 + (√(L/μ)σ/ε)^{p/(p−1)}))⁴. The budget does not depend on d.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [HeavyTailedNcscAccelerated](../../LongTails/Theorems/HeavyTailedNcscAccelerated.lean) (added 2026-11-07, commit a8f18312) | Same formula N → same formula N (the Lean `budget` is the same expression with local `let` names) | None: identical | None. The general class has arbitrary finite-dimensional E, F, any sample space Ω and any x₀, y₀; the selected class is strictly contained in it. | None: same algorithm, information and selected-point high-probability output | Narrower: d-dimensional Euclidean spaces, Ω = ℝ, zero initialization, κ ≥ 8, δ ≤ 1/4, LΔ ≥ 2³²ε², a lower bound on G, a huge-d condition |
| Liu–Luo N²SGDA, [arXiv:2509.14952](https://arxiv.org/abs/2509.14952), Thms 4.1/4.2. Rate as quoted in the repository notes; I did not re-read it. | Õ(κ^{(2p−1)/(p−1)} σ^{p/(p−1)} ε^{−(3p−2)/(p−1)}) → leading term Õ(κ^{p/(2(p−1))}·LΔσ^{p/(p−1)}/ε^{(3p−2)/(p−1)}) | Inherited from the parent theorem, not new here: the condition-number factor drops by κ^{p/(2(p−1))+1} when LΔ/ε² ≥ κ^{p/(2(p−1))} and σ ≥ ε | None beyond the parent | None beyond the parent | Large p-dependent constants and ℓ^{(5p−3)/(p−1)} logarithms. The parent note also cites a JMLR 27(233) Liu–Luo theorem with κ^{r+1}+κ² terms; that citation discrepancy is unresolved. |
| Wu et al., [arXiv:2610.00229](https://arxiv.org/abs/2610.00229) v2 (revised 19 Oct 2026), Thm 3.4. This is a p = 2 special-case baseline; the rate is quoted from the repository notes. | Θ̃(√κA + κAσ²/ε² + κ²σ²/ε² + √κ log₊(G/(ε√κ))), with A = LΔ/ε² → the same order at p = 2 | None: same order up to logarithms at p = 2 | None. Their oracle model is conditional; this one is IID. | Confidence δ is tunable here; theirs fixes 2/3 | Extra logarithmic factors |

**Reduction check and proof ancestry.** The result follows from the parent theorem by plain instantiation. `admissible` and `successful` are definitionally the parent's predicates at `toGeneral q`, so the proof needs no new mechanism. All of the technical content belongs to the parent proof: the multilevel clipped estimators, the accelerated dual epochs and the recursive saddle certificate. This file's only role is to put the upper bound on the same specification as the [lower bound](../../LongTails/Theorems/HeavyTailedNcscLowerBound.lean).

**Search coverage.** On 2026-11-24 I ran web searches for heavy-tailed and finite-variance NC–SC upper and lower bounds. They confirmed that 2509.14952, 2609.06064, 2610.00229 and 2609.35206 exist and gave their titles. I did not read their theorem statements myself, so the rates quoted for these papers come from the repository notes. The companion note itself says "This is not a new optimization result," which agrees with the Lean proof.

## Conclusion

**No: this theorem adds no new complexity, instances or analysis; it restates an existing repository theorem on a smaller class.** The strongest baseline is the repository's own HeavyTailedNcscAccelerated theorem. It proves the same budget, for the same algorithm and the same high-probability criterion `P(‖∇Φ(X)‖>ε) ≤ δ`, on a strictly larger class: any finite-dimensional spaces, any sample space and any starting point.

| | Class | Budget |
|---|---|---|
| Parent (2026-11-07) | general HeavyTailedNcsc | N |
| Selected (2026-11-24) | ℝ^d, Ω = ℝ, x₀ = y₀ = 0, lower-bound regime | N (identical) |

The only value is bookkeeping: the upper and lower bounds now share one specification, so their parameter ranges, oracle model and criterion line up exactly. Whether the parent's improvement in the condition-number exponent (κ^{r+1} → κ^{r/2}, with r = p/(p−1)) is new to the literature is a separate question. Answering it would mean checking the primary theorems of Liu–Luo and Zhu–Xu–Ji, which I did not do here. That open question does not change this verdict, because this file contributes nothing beyond the parent.

What can be claimed is a convenience corollary that pairs the existing upper bound with the companion lower bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
