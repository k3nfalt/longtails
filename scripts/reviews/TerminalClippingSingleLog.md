# TerminalClippingSingleLog: novelty assessment

[`result`](../../LongTails/Theorems/TerminalClippingSingleLog.lean) proves the following for clipped projected stochastic subgradient descent ([algorithm](../../LongTails/Algorithms/TerminalClippingSingleLog.lean)) in the [TerminalClippingConvex setup](../../LongTails/Setups/TerminalClippingConvex.lean). The setup has a convex `f` on a closed convex `X ⊆ ℝᵈ`, a minimizer `u` with `‖x₀−u‖ ≤ R`, exact projections onto `X`, and IID relative-subgradient samples with full second moment `E‖g(x)‖² ≤ G² + B²‖x−x₀‖²`. The method uses a known horizon, linearly decaying steps `η_t ∝ R(T−t+1)`, and a clipping level `C = M√(T/q)`. Its actual last iterate `x_T` is feasible and satisfies `P(f(x_T) − f(u) > ε) ≤ δ`.

**Complexity.** One call is one subgradient sample or one projection. With `B, G, ε > 0`, `R ≥ 0` and `0 < δ < 1`:

  N = 0 if GR ≤ ε, otherwise N = 2⌈576 R²(G² + 16B²R²) log(8/δ)/ε²⌉ = O(R²(G² + B²R²) log(8/δ)/ε²).

The parameters are: `G²`, the moment level at `x₀`; `B`, its growth rate in the distance from `x₀`; `R`, the initial distance; `ε`, the target accuracy; and `δ`, the failure probability. The updates use `R, B, G, δ` and `T` (and therefore `ε`).

**Localization used in the table.** On `K = X ∩ B̄(x₀,4R)`, the full second moment is at most `M² = G² + 16B²R²`. The companion note's extension `f̃(x) = sup_{y∈K}{f(y) + ⟨h(y), x−y⟩}`, where `h` is the mean subgradient, is convex, `M`-Lipschitz and equal to `f` on `K`. The centered variance on `K` is at most `M²`. On the good event of Jiang–Bai–Li, their bounds `P_s < 2R²/T²` keep every iterate within `(1+2√2)R < 4R` of `x₀`. I checked this arithmetic. Projection onto `K` therefore coincides with projection onto `X`, so the coupled trajectory is exactly the allowed algorithm (same linear-decay step and clipping form).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jiang–Bai–Li, [arXiv:2610.18555v1](https://arxiv.org/html/2610.18555v1) (13 Oct 2026, preprint), Thm 2, eqs. (7)–(9), with `p = 2`, `r = ι_K`, Lipschitz and noise constants both `M`; prior | `2⌈(256RM(1+√log(4/δ))/ε)²⌉ = O(R²(G²+B²R²) log(4/δ)/ε²)` → `O(R²(G²+B²R²) log(8/δ)/ε²)` | None: same order. Only the universal constant is smaller, by a factor of at least 75 (tending to about 114 as δ → 0) | None, once the localization above is applied | None. Both give a high-probability gap at the last iterate of the same clipped method | Theirs is stated for globally Lipschitz `f` with centered moments; the bridge is the localization above |
| Z. Liu, [arXiv:2610.21026v1](https://arxiv.org/abs/2610.21026) (14 Oct 2026; arXiv comment says NeurIPS 2026), Thm 1, classical case `σ_s = σ_l`, localized in the same way; prior | `O(R²M²/ε² + R²M² log(1/δ)/ε² + RM log(1/δ)/ε)` → same order, since `RM ≥ GR > ε` | None: same order | None | None. Both give a last-iterate high-probability bound | Liu's bound separates the Lipschitz and noise terms. Under a full-moment model the localization gives both the value `M`, so that refinement is lost |
| Parletta–Paudice–Pontil–Salzo, [arXiv:2208.08567v2](https://arxiv.org/abs/2208.08567) (SIMODS 2024), Thm 2(iii) and Cor. 1, localized (see the repository [DistanceGrowingSubgradientUpperBound review](DistanceGrowingSubgradientUpperBound.md)); prior | `O(R²(G²+B²R²) log(1/δ)/ε²)` → same order | None: same order | None | Averaged iterate → last iterate. This matters only for the method; the problem-class complexity is unchanged | None |
| Repository [ClippedBgLastIterate](../../LongTails/Theorems/ClippedBgLastIterate.lean) (same setup; repository-only) | `O((BR² + G²/B)² log²(8/δ)/ε²)` → `O(R²(G²+B²R²) log(8/δ)/ε²)` | Removes one `log(1/δ)` factor and the `G⁴/(B²ε²)` term, for every valid input | None | That theorem's updates use `B, G, δ, T` but not `R` or `ε`. This one needs `R` and `ε` | Requires knowing `R` |

**Reductions and mechanism.** The result is Jiang–Bai–Li's Theorem 2 combined with a routine localization. The algorithm is the same: linear-decay steps with clipping at `M√(T/log)`. The proof mechanism is also the same: a moving comparator `z' = ((m−1)z + 2y′)/(m+1)`, two stopped exponential martingale bounds, and an induction on the good event. The new elements are the coupling argument, which avoids projecting onto `X ∩ ball`, the tighter constant 576, and the machine-checked formalization. The moving-comparator telescope descends from Liu–Zhou ([arXiv:2312.08531](https://arxiv.org/abs/2312.08531), ICLR 2024). That work supplies the energy argument but not the heavy-tail concentration.

**Search coverage.** On 2026-11-26 UTC I searched arXiv, NeurIPS 2026, ICLR 2026 and OpenReview for high-probability last-iterate bounds for clipped SGD and subgradient methods under heavy tails. Coverage has gaps:
- Jiang–Bai–Li: I read Theorem 2 and equations (7)–(9), (25) and (55) verbatim. Equation (63) and the bibliography I saw only in summary.
- Liu: I read Theorem 1 from the HTML version. Tuning (13) I saw only in summary.
- Chezhegov et al. (ICLR 2026) requires smoothness, so I did not use it as a baseline.

The theorem was introduced in commit `e8c5b7a6` on 2026-11-26, after both October 2026 preprints. The companion note's citations match what I checked. The note itself concedes that the localized Jiang–Bai–Li proof "already gives that confidence exponent".

## Conclusion

**No: this result is a known guarantee with a better constant.** The strongest baseline is Jiang–Bai–Li (Oct 2026), Theorem 2. Restrict to the ball of radius `4R` around `x₀`, where the moment bound becomes the uniform constant `M² = G² + 16B²R²`. Their analysis of the same clipped, linearly decaying method then gives the same last-iterate guarantee:

| | Calls for `P(f(x_T) − f* > ε) ≤ δ` |
|---|---|
| Jiang–Bai–Li, after localization | `O(R²(G²+B²R²) log(4/δ)/ε²)` |
| This theorem | `O(R²(G²+B²R²) log(8/δ)/ε²)` |

On a common setup the two bounds have the same order in every parameter regime. They require the same known parameters and give the same output. Neither has an asymptotic advantage over the other in either direction, and Liu (Oct 2026) gives the same order as well. The only measurable gains are an explicit constant at least 75 times smaller, and, relative to the repository's earlier last-iterate theorem, one fewer `log(1/δ)` factor and no `G⁴/B²` term.

I checked the localization step myself, so the comparison is established. Priority rests on two October 2026 preprints, parts of which I read only in summary; that makes confidence medium rather than high. What can be claimed is a formally verified, constant-sharpened version of a recently published last-iterate bound for clipped SGD, extended to the distance-growing moment model by a routine localization.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**
