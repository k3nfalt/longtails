# Novelty assessment: KnownGapGeneralizedSmoothUpperBound

[`result`](../../LongTails/Theorems/KnownGapGeneralizedSmoothUpperBound.lean) shows the following. Take a convex function on ℝᵈ whose gradient is differentiable with ‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖, an exact gradient oracle, and known bounds ‖x₀ − x*‖ ≤ R and f(x₀) − f* ≤ Δ. Restrict to the valid regime of the [setup](../../LongTails/Setups/GeneralizedSmoothConvexKnownGapPolynomialDimension.lean), which the lower bound needs: L₁R ≥ 2²⁰, Δ ≥ ε(2+L₁R)², Δ ≥ ε√(L₀R²/ε), 16ε ≤ L₀R², and d polynomially large. In that regime, the [selection algorithm](../../LongTails/Algorithms/KnownGapSelection.lean) outputs a deterministic point whose expected gap is at most ε, with this number of gradient calls:

**N = O( √(L₀R²/ε) + min{ (1 + (L₁R)^{2/3}) · log(2 + Δ/ε), (1 + L₁R) · log(2 + L₁R) } ).**

The parameters are:
- L₀, L₁: the smoothness constants;
- R: the bound on the initial distance to the minimizer;
- Δ: the known bound on the initial gap;
- ε: the target accuracy.

The constant 1 is absorbed because L₁R ≥ 2²⁰. The formula is read directly from the budget min{2⌈4096(…)⌉, ⌈64√· + 32768(…)⌉}.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, *Descending Everest I*, [arXiv 2610.21461](https://arxiv.org/abs/2610.21461) (v1 15 Oct 2026, v2 5 Nov 2026; preprint). Takes the minimum of Thm 3.7 (on 𝒫_R ⊇ 𝒫_Δ) and Thm B.7(b) (on 𝒫_Δ). | min{ √(L₀R²/ε) + (1+L₁R)log(2+L₁R), [1 + √(L₀R²/ε) + (L₁R)^{2/3}log^{2/3}(2Δ/ε)]·log(2 + L₀R²/ε + L₁R) } → N above | Mixed, and the gain is inherited from the repository's [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean). The √(L₀R²/ε) term loses the factor log(2+L₀R²/ε+L₁R). The Δ-branch is better when log^{1/3}(Δ/ε) < log(2+L₀R²/ε+L₁R) and worse by up to log^{1/3}(Δ/ε) otherwise. The radius branch has the same order. | None. 𝒫_Δ restricted to ℝᵈ with the lower-bound regime is a subclass of both source theorems' classes. | None. Both methods need L₀, L₁, R, ε, and the Δ-branch also needs Δ. The output is deterministic in both. | It is narrower: finite dimension, L₁R ≥ 2²⁰, two lower bounds on Δ, and large d. Its expected-gap criterion is weaker than the almost-sure gap in the source repository theorems (the two are equivalent here because the output is deterministic). Everest's Thm 3.7 is gradient-only. I could not read the oracle used in B.7(b). |
| Repository [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean) (Hilbert space, known Δ) together with [RadiusFreeGeneralizedAccelerated](../../LongTails/Theorems/RadiusFreeGeneralizedAccelerated.lean) (radius-only) | The same two budgets, run separately → their minimum | None: the minimum of two existing budgets. Both are computable from public parameters. | None. Both source classes contain this one. | None. Note that the radius-free method needs neither R nor ε in its updates, but here the budget selection uses both. | It is narrower, as in the row above. |

**Standard-reduction check.** The theorem follows directly from the two existing guarantees. 𝒫_Δ ⊆ 𝒫_R, and every parameter is public, so the algorithm can compare the two budgets and run the cheaper method. The Lean proof does exactly that: it replays `accelerated_gap` and `sherpa_gap` via `combine_execute_left/right`. It contains no new algorithm, estimate, or proof mechanism. The proof ancestry is Everest's Algorithm 4 and SHERPA, plus their repository formalizations.

**Search coverage (17 Nov 2026).** I read Everest I v2 directly: Section 2, Thm 3.7, Table 1, and Section 5. I could not retrieve the statement text of Thm B.7 in Appendix B.5, so I took its bound and its known-Δ requirement from Table 1 and the Appendix B intro. I did not find an explicit "minimum of the two bounds" remark in the parts I read. I also ran a web search on accelerated (L₀,L₁) methods: Gorbunov et al., ICLR 2025, [arXiv 2409.14989](https://arxiv.org/abs/2409.14989); [arXiv 2410.10800](https://arxiv.org/abs/2410.10800); [arXiv 2508.06884](https://arxiv.org/abs/2508.06884). I did not read their theorem statements closely, and none is needed to decide this verdict. The companion note is accurate: it says this is "a transfer of two existing repository results, not a new upper-complexity claim."

**Conclusion**

**No: this theorem gives no new complexity, scope, or analysis; it is the minimum of two existing upper bounds.**

The strongest prior baseline is Everest I's pair: Theorem 3.7 on the radius-only class and Theorem B.7(b) on the known-gap class. Because the known-gap class sits inside the radius-only class and every parameter is known, running whichever method has the smaller budget is immediate:

  Everest: min{ √A + q·log q, (√A + q^{2/3}log^{2/3}(Δ/ε))·log(A+q) }  →  here: √A + min{ q^{2/3}log(Δ/ε), q·log q },

with A = L₀R²/ε and q = L₁R.

The differences against Everest are a logarithm saved on √A and a log^{1/3}(Δ/ε) lost when log^{1/3}(Δ/ε) > log(2+A+q). Both come entirely from the earlier repository theorem GeneralizedAcceleratedConvex, not from this one. The setup is also narrower than both sources, because it is restricted to the lower bound's parameter regime and to finite dimension.

What can be claimed is a formal upper-bound companion for the paired lower bound: within the lower bound's regime, it makes that lower bound's distance from the best available upper bound explicit, up to logarithms. It is not a mathematical contribution of its own.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
