# Novelty review: first-order stationarity under pointwise Hessian growth (upper bound)

[`result`](../../LongTails/Theorems/PointwiseHessianStationarity.lean) proves the following. Let `f` be C³ on `ℝ^d` with `‖D³f(x)‖ ≤ L₀ + L₁‖∇f(x)‖` for all `x`, `f(0) − inf f ≤ Δ` and `‖∇f(0)‖ ≤ G`. Each oracle call returns `(f, ∇f, ∇²f)` exactly. With known parameters, the [algorithm](../../LongTails/Algorithms/JointHessianStationarity.lean) runs the repository's EnergyHessianReuse with reuse length `m = 1`. It returns the point with the smallest observed gradient, and that point satisfies `‖∇f‖ ≤ ε` deterministically, hence also in expectation ([setup](../../LongTails/Setups/PointwiseHessianStationarity.lean)).

**Complexity.** Here `L₀, L₁ ≥ 0` (not both zero) are the absolute and relative third-derivative constants, `Δ` is the initial gap, `G` bounds the initial gradient and `ε` is the target gradient norm. The proved budget `⌈10⁵Δ√(L₀+L₁ε)ε^{-3/2}⌉ + 2⌈log(1+L₁G/(L₀+L₁ε))/log(4/3)⌉ + 200` is

`O( Δ√L₀ ε^{-3/2} + Δ√L₁ ε^{-1} + log(2 + L₁G/(L₀+L₁ε)) )` joint calls.

The public `spec` also requires `G ≥ 16ε`, `Δ√(L₀+L₁ε)ε^{-3/2} ≥ 2³⁹` and `d ≥ 2¹⁴⁰(1+⌈Δ√(L₀+L₁ε)ε^{-3/2}⌉)⁴`. These are shared with the lower-bound theorem and not needed by the upper proof (`success` holds on `broadSpec`), but they narrow the stated theorem.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fang–Marumo–Takeda, [arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741) (12 Jul 2026, preprint), Assumption 1, Thm. 2, Cor. 1. Same class and same joint `(f,∇f,∇²f)` oracle. Backtracking trials are counted. | In Cor. 1 take `δ = √(L₀ε) + √L₁ε`, so the δ-terms are dominated, and `σ_init = L₀+L₁ε`: `O(Δ√L₀ε^{-3/2} + Δ√L₁ε^{-1} + log(2 + L₁G/(L₀+L₁^{3/2}Δ)))` → `O(Δ√L₀ε^{-3/2} + Δ√L₁ε^{-1} + log(2 + L₁G/(L₀+L₁ε)))` | None: same order. The two additive logarithms differ by at most `log(1 + ε/(Δ√L₁) + Δ√L₁/ε)`, which never changes the order beyond an additive log. | None. Fang assumes `L₀ > 0`, but the `L₀ = 0` case follows by applying Fang with `L₀' = L₁ε`, giving the same bound. | Worse. Fang's updates need no `L₀, L₁, Δ`; this result needs `L₀, L₁, Δ, G, ε`. Fang also certifies `λ_min(∇²f) ≥ −δ`, while this result is first-order only. Fang proves some iterate up to `K` is stationary; since `‖∇f(x_k)‖` is observed, stopping at the first such iterate needs only `ε`. Deterministic `‖∇f‖ ≤ ε` implies the expectation criterion either way. | Larger constants (10⁵). The public theorem is restricted to `G ≥ 16ε`, `S ≥ 2³⁹` and huge `d`. |
| Semenov–Jaggi–Doikov, [ICLR 2026](https://openreview.net/forum?id=Epu8Lm6VMK). **Special case only**: the two-point condition `‖∇²f(y)−∇²f(x)‖ ≤ (L₀+L₁‖∇f(x)‖)‖y−x‖` for all `x, y`. Bound as tabulated by Fang et al. (Table 1); I did not read their theorem. | `O(Δ(√L₀ε^{-3/2} + √L₁ε^{-1})) + Õ(1)` → same order | None: same order | Two-point condition → pointwise condition. This covers, e.g., `x⁴/4`, but Fang already covers it. | Their updates are parameter-free; this result needs parameters. | None beyond the above |
| Repository [EnergyHessianReuse](../../LongTails/Theorems/EnergyHessianReuse.lean) (separate gradient and Hessian channels, `L₀ > 0`) | At `m = 1`: `O(Δ(√L₀ε^{-3/2} + √L₁ε^{-1}) + log(2+L₁G/L₀))` per channel → the same, paid in joint calls | None (the parameter substitution `L₀ → L₀+L₁ε`) | Allows `L₀ = 0` by that substitution | None | None |

**Reduction check.** The theorem is EnergyHessianReuse at `m = 1` with `L₀` replaced by `L₀+L₁ε` and each channel call charged as one joint call. The [budget lemma](../../LongTails/Proofs/JointHessianBudget.lean) shows this; it adds no new mechanism. The same rate also follows directly from Fang et al. Cor. 1 by choosing `δ` large, as derived in the table. Proof ancestry: Doikov et al. and Fang et al. through EnergyHessianReuse; nothing new is added here.

**Search coverage.** On 2026-11-17 UTC I searched arXiv and conference proceedings for cubic/Newton methods under generalized (L₀,L₁) Hessian or third-derivative smoothness. I read the text of Fang et al. Cor. 1, Thm. 2, eq. (41) and Section 7 from the arXiv PDF. Gratton–Jerad–Toint ([arXiv:2505.04807](https://arxiv.org/abs/2505.04807), EJCO 2026) uses a local two-point condition, has an extra `|log ε|` factor and assumes bounded negative curvature; I did not verify its full theorem. Fang et al. (July 2026) predates this theorem (commit e6e32a49, 2026-11-17). The companion note agrees: it claims no upper-bound novelty and calls the result a transfer. Its claimed contribution is the separate lower bound, which is not assessed here.

**Conclusion**

**No: this upper bound gives the same complexity as an existing method, with a weaker guarantee and more required knowledge.** The strongest baseline is Fang–Marumo–Takeda's parameter-free cubic Newton (Cor. 1). It works for the identical class with the same value/gradient/Hessian oracle, and the comparison below counts its backtracking calls:

| | joint oracle calls |
|---|---|
| Fang et al. (δ chosen large) | `Δ√L₀ε^{-3/2} + Δ√L₁ε^{-1}` + additive log of `L₁G` |
| This result | `Δ√L₀ε^{-3/2} + Δ√L₁ε^{-1}` + additive log of `L₁G` |

Fang's method needs no smoothness constants or gap in its updates, and it also guarantees approximate second-order stationarity. The new theorem needs all of `L₀, L₁, Δ, G, ε`, has only first-order accuracy, and its public form is restricted to a narrow high-dimensional regime. The `L₀ = 0` boundary is not a scope gain: replacing `L₀` by `L₁ε` in Fang's bound covers it at the same rate. No regime is better in either direction except for additive logarithms.

The comparison establishes that there is no improvement. Chronology also shows the rate was public before this theorem. What can be claimed is a formal, fully counted transfer of the repository's EnergyHessianReuse bound to a joint oracle, which serves as the upper half of the paired lower-bound result.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
