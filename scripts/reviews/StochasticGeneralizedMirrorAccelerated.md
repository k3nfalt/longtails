# Novelty assessment: StochasticGeneralizedMirrorAccelerated

[`result`](../../LongTails/Theorems/StochasticGeneralizedMirrorAccelerated.lean) proves the following for the [setup](../../LongTails/Setups/StochasticGeneralizedMirror.lean) and the [accelerated clipped Bregman-prox algorithm](../../LongTails/Algorithms/StochasticGeneralizedMirror.lean). Take a convex composite problem `F = f + ψ` over a convex `Q` in any finite-dimensional normed space, where `f` is globally convex and `(L₀,L₁)`-smooth in the dual norm, and the stochastic gradients are unbiased with central α-moment at most `σ^α`. Then the **last iterate** `x` satisfies `P{x ∉ Q or F(x) − F* > ε} ≤ δ`.

**Complexity.** Gradient plus Bregman-prox calls, derived from the Lean budget `⌈2³³ S log²(2³³S/δ)⌉`:

```
N = O( [ (1+L₁R)·log(1+Δ/ε) + √((L₀+L₁G)R²/ε) + 256^{1/(α−1)}(σR/ε)^{α/(α−1)} + 1 ]
       · log²( [ (1+L₁R)(1+Δ/ε) + (L₀+L₁G)R²/ε + 256^{1/(α−1)}(σR/ε)^{α/(α−1)} ] / δ ) )
```

The parameters are:
- `R² ≥ 2D_h(x*,x₀)`, where `h` is 1-strongly convex relative to the norm (no diameter needed);
- `Δ ≥ F(x₀) − F*`;
- `G ≥ ‖∇f(x*)‖_*`, which the updates use;
- the noise level σ and moment order α ∈ (1,2];
- the confidence level δ ∈ (0,1).

The algorithm is given all of these parameters, and each phase draws `⌈8ℓ⌉` pilot gradients.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| El Bakkali El Kadi–Gorbunov, [arXiv:2610.23301v2](https://arxiv.org/abs/2610.23301) (v1 Oct 16, 2026; preprint; prior), Thm 2/Rem. 1. **Special case: Euclidean, unconstrained** (`ψ=0`, `Q=E`, `h=½‖·‖²`, `G=0`) | `Õ(1+L₁R + √(L₀R²/ε) + (σR/ε)^{α/(α−1)})` → `O([(1+L₁R)log(1+Δ/ε) + √(L₀R²/ε) + 256^{1/(α−1)}(σR/ε)^{α/(α−1)}]·log²(·/δ))` | None: same order up to logarithms. I did not verify their exact log powers. | Euclidean unconstrained → arbitrary norm with a Bregman prox, a composite `ψ`, a constraint set `Q`, and boundary minimizers with `∇f(x*) ≠ 0` | None (both are last-iterate; both have known parameters) | `G` must be supplied; needs an exact Bregman-prox oracle; global `(L₀,L₁)`-smoothness on all of `E`; finite dimension only |
| Repository [`StochasticCompositeGeneralizedAccelerated`](../../LongTails/Theorems/StochasticCompositeGeneralizedAccelerated.lean) (Nov 3, 2026). **Euclidean composite**, repository overlap only | `O(2^{128/(α−1)}[1 + √((L₀+L₁σ+L₁G)R²/ε) + (1+L₁R)log(2+(1+L₁R)√(Δ/(L₀R²))) + (σR/ε)^{α/(α−1)}]·log^{2+1/(α−1)}(·/δ))` → this result | Removes a `log^{1/(α−1)}(·/δ)` factor and the `2^{120/(α−1)}`-type constant on the non-statistical terms. The `√(L₁σR²/ε)` term was already dominated (AM–GM). The transient logs are incomparable. | Hilbert norm → general norm and Bregman geometry | Worse: `G` was used only in the budget before; now the updates need it | Separable Hilbert space (possibly infinite-dimensional) → finite dimension only |
| Nguyen et al., [NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/file/4c454d34f3a4c8d6b4ca85a918e5d7ba-Paper-Conference.pdf), Thm D.1. **Special case: `L₁=0`, `ψ=0`, `∇f(x*)=0`** (Assumption 5′) | `O(log(1/δ)·[√(LR²/ε) + 26^{1/(α−1)}(σR/ε)^{α/(α−1)}])` → `O([log(1+Δ/ε) + √(LR²/ε) + 256^{1/(α−1)}(σR/ε)^{α/(α−1)}]·log²(·/δ))` | Worse: one extra logarithmic factor plus an additive `log(Δ/ε)` | `L`-smooth with `∇f(x*)=0` → `(L₀,L₁)`-smooth composite problems with arbitrary constrained minimizers | Worse: Nguyen et al. also have an unknown-`T` (anytime) variant | Needs `Δ` and `G`, and finite dimension |
| Yu et al., [arXiv:2502.00753v4](https://arxiv.org/html/2502.00753v4) ([ICML 2026](https://proceedings.mlr.press/v306/yu26s.html)), Thm 3.7. **Deterministic `σ=0` special case, no `ψ`** | `O(√(ℓ(4G₀)R²/ε))`, where `G₀² ≲ (L₀+L₁G₀)Δ`, i.e. `O(√((L₀+L₁²Δ+L₁√(L₀Δ))R²/ε))` → `O([(1+L₁R)log(1+Δ/ε) + √((L₀+L₁G)R²/ε)]·log²(·/δ))` | When `G=0` and `L₁R√(Δ/ε) ≫ (1+L₁R)log²(Δ/(εδ))`: the factor `L₁R√(Δ/ε)` becomes `L₁R·polylog`. When `G` is large: not comparable. | None on this overlap | None | At `σ=0`, still pays `log²(1/δ)` and needs `G`. I took the formula for `G₀` from a summary of v4, not verbatim. |

**Standard-reduction check.** The Euclidean results do not cover this setup without a substitution step.
- Transferring them by norm equivalence adds dimension factors.
- Transferring Nguyen et al.'s classical mirror bound through a localized smoothness constant fails twice: it needs `∇f(x*)=0`, and it introduces a factor `e^{Θ(L₁R)}`.

I verified the companion note's simplex instance. Take `f = e^{Ma·x} + e^{Mb·x}` on the simplex with entropy geometry, `M = log d`, `ε = 1/d`, and `σ = 0`.
- Generalized smoothness holds globally: `‖∇²f‖_{1→∞} ≤ M‖∇f‖_∞`.
- The setup assumptions hold: Pinsker's inequality gives the strong-convexity condition, `R² = 2 log d`, and `G = 2M`.
- This budget is `O(√d·log^{7/2} d)`.
- The Euclidean composite bound has a curvature term of `Ω(d log d)`, because `B₂ ≥ M²(d−2)/4` at `x* = e₁`.

That is a comparison of upper bounds, not a lower bound.

**Mechanism.** The technical ingredients are known:
- the accelerated potential (Lan's accelerated mirror descent; Yu et al.);
- clipping (Nguyen et al.);
- pilot centering (Gorbunov et al., [arXiv:2310.01860](https://arxiv.org/abs/2310.01860));
- the one-phase `L₁R` schedule (2610.23301).

The new part is closing the argument in a general norm: an analysis-only tilt `f − ⟨∇f(x*),·⟩`, scalar dual-functional concentration in place of vector variance, and a provisional prox radius that works with one-sided Bregman control. I did not find a theorem that implies this combination.

**Search coverage (Nov 12, 2026).**
- **Sources:** arXiv and the 2023–2026 NeurIPS/ICML proceedings.
- **Read closely:** 2610.23301, 2609.33415, 2510.11676, 2502.00753v4, and Nguyen et al.'s Thm D.1, which I read in full text.
- **Not comparable:** Lobanov et al. ([2609.33415](https://arxiv.org/abs/2609.33415)) use `(H₀,H₁)` smoothness with Euclidean mixed-moment noise. He–Li–Lu ([2510.11676](https://arxiv.org/abs/2510.11676)) give a Euclidean composite result with bounded domain, Hölder smoothness, and polynomial dependence on `1/δ`.
- **Not exhaustive:** OpenReview/ICLR 2026 coverage is incomplete.
- **Companion note:** its claims match the Lean statement and its comparisons are correct, but its two dimension-dependent examples compare upper bounds only.

**Conclusion**

**Yes, but as a scope extension rather than a faster rate.** No result I checked gives accelerated high-probability guarantees under heavy-tailed noise for `(L₀,L₁)`-smooth problems in non-Euclidean, composite, or boundary-minimizer settings. This theorem does.

The closest baseline is El Bakkali El Kadi–Gorbunov (Oct 2026), which covers only the Euclidean unconstrained case. There both bounds read

```
(1+L₁R)·polylog + √(L₀R²/ε) + (σR/ε)^{α/(α−1)},
```

so on the overlap nothing improves. At `L₁ = 0`, the result drops the requirement `∇f(x*) = 0` in Nguyen et al.'s accelerated mirror theorem, at the cost of an extra logarithm.

The gain comes from geometry. In a verified simplex instance with `M = log d`, `ε = 1/d`, and `σ = 0`, the mirror bound is `O(√d·log^{7/2} d)`, against `Ω(d log d)` for the Euclidean composite curvature term. This shows that respecting the ℓ₁ geometry can remove polynomial dimension factors. The tradeoffs:
- `G ≥ ‖∇f(x*)‖_*` must be supplied to the updates;
- the method needs exact Bregman-prox access;
- it pays `log²(1/δ)` even without noise;
- nothing is adaptive.

The ingredients are familiar, but I found no reduction that yields the result. Given how fast this area is moving (several relevant preprints from Sep–Oct 2026), priority is not certain. The contribution that can be claimed is the first checked high-probability heavy-tailed accelerated guarantee for generalized-smooth composite problems in arbitrary mirror geometry, matching the Euclidean rate structure.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
