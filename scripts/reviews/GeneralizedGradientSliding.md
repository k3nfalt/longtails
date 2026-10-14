# Gradient sliding under (L₀,L₁)-smoothness: novelty assessment

[`result`](../../LongTails/Theorems/GeneralizedGradientSliding.lean) proves the following. Take F = f + h on a convex set Q in a Hilbert space, where f is convex and symmetric-(L₀,L₁)-smooth on all of E, and h is reached only through adversarial subgradients that are M-bounded and valid on Q. Projections onto Q are exact. Under these assumptions the sliding method ([setup](../../LongTails/Setups/SlidingGeneralizedSmooth.lean), [algorithm](../../LongTails/Algorithms/GeneralizedGradientSliding.lean)) returns a deterministic point x_K ∈ Q with F(x_K) − F* ≤ ε. It uses at most 8K + ⌈768M²R²/ε²⌉ oracle calls, of which at most 2K are gradient calls (certified by `allowedAlgorithm`).

**Complexity.** The parameters are: R ≥ ‖x₀−x*‖, Δ ≥ F(x₀)−F*, G ≥ ‖∇f(x*)‖, and M is the subgradient bound of h. All are required with L₀, R, Δ, ε > 0. The bound is

- ∇f calls: O(√((L₀+L₁G)R²/ε) + (1+L₁R)·log(2+(1+L₁R)√(Δ/(L₀R²))))
- total calls (subgradients and projections included): the same expression + O(M²R²/ε²)

The updates use L₀, L₁, M, R, Δ and ε. G is used only in the gradient-count cap.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lan, *Gradient sliding*, [Math. Program. 159 (2016)](https://arxiv.org/abs/1406.0919), Cor. 1(a). Needs a global L on X (eq. 1.2). Applied here only after restricting to X = Q∩B(x₀,2R), where the local constant is L ≤ (L₀+L₁G)e^{3L₁R} (Grönwall bound from x*; tight up to the constant in the exponent for cosh(L₁⟨c,x⟩)/L₁²) | ∇f: √((L₀+L₁G)e^{3L₁R}R²/ε) → √((L₀+L₁G)R²/ε) + L₁R·log(…). h′: M²R²/ε² + the ∇f term in both | Gradient count drops by a factor of about e^{1.5L₁R} when L₁R ≫ 1 and the √ term dominates. The total count improves only when that term also beats the shared M²R²/ε². At L₁R ≲ 1: same order | Globally L-smooth f → (L₀,L₁)-smooth f, with no exponential constant | None. Both use deterministic averaged-sequence output | Lan's version needs projection onto Q∩ball (not in this oracle model). Lan covers Bregman geometry, an extra simple prox term and stochastic subgradients; this result is Euclidean and deterministic only. Adds an additive log(2+√(Δ/(L₀R²))) term at L₁=0 |
| Grimmer, normalized subgradient method, [SIAM J. Optim. 29 (2019)](https://arxiv.org/abs/1712.04104), Thm. 2 (cf. Cor. 11), applied to F with g = ∇f + h′ | Each of ∇f, h′, Π_Q, plus F values to select the best iterate: (G+M)²R²/ε² + (L₀+L₁G)R²/ε + L₁²R² → selected bound above | ∇f calls: ε⁻² → ε⁻¹ᐟ². Total, case Q = E: G ≤ M, so same order unless ε(L₀+L₁G) ≫ M² or εL₁ ≫ M. Constrained Q: better when G ≫ M | None (both polynomial on the same class) | Best iterate, which needs a function-value oracle → one computable iterate with no F values | Grimmer's updates need only R and T, not L₀, L₁ or Δ. Its L₁²R² term is smaller only when log(Δ/(L₀R²)) ≳ L₁R |

Derivation of the Grimmer row: by Grönwall, ‖∇f(x)−g*‖ ≤ (e−1)(L₀+L₁G)t for ‖x−x*‖ = t ≤ 1/L₁. Hence D_F(t) ≤ (G+M)t + (L₀+L₁G)t². Taking t = R/√(T+1) ≤ 1/L₁ gives the row. Contrary to the companion note, plain subgradient methods are therefore *not* exponential in L₁R. They lose only on gradient count and in needing function values to pick the output.

**Reduction check and mechanism.** I found no substitution or composition of known theorems that gives polynomial-constant sliding. Lan's GS needs a global L. The companion note's sublevel-set obstruction (prox-sequence points leave polynomial sublevel sets) is plausible, but I did not verify it independently. The new step is a locality argument (‖ũ−x*‖ ≤ 19R, steps capped by A/(1+80L₁R)) for an inexact prox point whose error is controlled only in aggregate. The outer weights are chosen online, with inner lengths T_k ∝ M²a_k/ε. Proof ancestry: Lan's PS inner procedure and the repository's exact-prox composite (L₀,L₁) acceleration ([CompositeGeneralizedAccelerated](../../LongTails/Theorems/CompositeGeneralizedAccelerated.lean)). That result needs a prox of h, which avoids the M²R²/ε² term but uses a stronger oracle.

**Search coverage (2026-10-09).** I searched arXiv and the web for sliding or gradient skipping under (L₀,L₁), local or generalized smoothness, 2014–Oct 2026. I read Lan Cor. 1 and Grimmer Thm. 2 directly. I checked the abstract-level assumptions of PFUGS ([2603.23492 v2](https://arxiv.org/abs/2603.23492): global L) and Takahashi ([2601.20443 v2](https://arxiv.org/abs/2601.20443): LMO, compact set, no nonsmooth h); neither covers this setup. Both predate the result's introduction in commit 24cba27 (2026-10-08). Very recent preprints may be under-indexed.

## Conclusion

**Yes: for gradient-call complexity on this class, the proved bound is new and substantially better than any guarantee I could check.**

The strongest sliding baseline is Lan's gradient sliding. It needs a global smoothness constant, so on (L₀,L₁)-smooth f it only gives exponential constants. The only polynomial alternative found, Grimmer's normalized subgradient method, uses ε⁻² gradients and needs function values to select its output:

| | ∇f calls | total calls |
|---|---|---|
| Lan GS (local L on a 2R-ball) | √((L₀+L₁G)e^{3L₁R}R²/ε) | + M²R²/ε² |
| Grimmer subgradient (best iterate, F values) | (G+M)²R²/ε² + (L₀+L₁G)R²/ε + L₁²R² | same, ×3 oracle types |
| This result | √((L₀+L₁G)R²/ε) + (1+L₁R)log(2+(1+L₁R)√(Δ/(L₀R²))) | + M²R²/ε² |

The gain over Lan is exponential in L₁R. The gain over Grimmer is ε⁻² → ε⁻¹ᐟ² in gradient calls. In total calls with Q = E, however, the result matches Grimmer in order unless ε(L₀+L₁G) ≫ M² or εL₁ ≫ M. At L₁ = 0 it is no better than Lan, and it drops Lan's Bregman, prox-term and stochastic extensions.

What can be claimed is the first gradient-sliding guarantee under (L₀,L₁)-smoothness, with polynomial constants and a new locality argument for inexact prox steps. Priority rests on a search that found no competitor, not on proof. The companion note's claim that subgradient methods are exponential is wrong.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
