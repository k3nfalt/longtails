# StochasticLocalHessianAccelerated: novelty assessment

[`result`](../../LongTails/Theorems/StochasticLocalHessianAccelerated.lean) proves the following for the [setup](../../LongTails/Setups/StochasticLocalHessianConvex.lean). Let `f` be a convex C² function on ℝᵈ whose Hessian varies locally, `‖∇²f(y)−∇²f(x)‖ ≤ (M₀+M₁‖∇f(x)‖)‖y−x‖` whenever `‖y−x‖ ≤ ρ`. Suppose there are IID unbiased stochastic gradients with variance ≤ σ² and a deterministic Hessian map `H` with `‖H−∇²f‖ ≤ δ`. Then the output of [NoisyDampedNewton](../../LongTails/Algorithms/NoisyDampedNewton.lean) satisfies `P(f(out)−f* > ε) ≤ β`. The updates use every parameter (M₀, M₁, ρ, δ, σ, R, Δ, ε, β).

**Proved complexity.** R bounds ‖x₀−x*‖, Δ bounds f(x₀)−f*, and β is the failure probability. Let `ℓ = log(2 + Δ/ε + δR²/ε + M₀R³/ε + M₁R² + R²/ρ² + 1/β + σ²R²/ε²)`. Then

```
gradient calls: O([1 + (M₁R²)^{1/3} + (R/ρ)^{2/3} + (M₀R³/ε)^{2/7} + (δR²/ε)^{1/2} + σ²R²/ε²] · ℓ³)
Hessian calls:  the same, without the σ²R²/ε² term outside ℓ.
```

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Agafonov, Ashabokov, Kamzolov, D'yakonov, Gasnikov, Takáč, [arXiv:2610.11693](https://arxiv.org/abs/2610.11693) (v1 8 Oct 2026, v2 13 Oct; preprint), Thm 5.1/C.7. **Prior. Covers only the M₁ = 0 subclass**, via a reduction: X = ball(x₀,R) (D = 2R, contains x*), Hessian replaced by (H+Hᵀ)/2+δI (PSD, error ≤ 2δ), gradients batched in groups of b, then Markov at βε | Gradients `O(1 + σ²R²/(β²ε²) + (δR²/(βε))^{1/2} + (M₀R³/(βε))^{2/7})`, Hessians the same without the σ term → the bounds above (ρ := R is admissible when M₁ = 0) | Confidence only: polynomial `β^{-2}, β^{-1/2}, β^{-2/7}` → `ℓ³`. A strict gain when, e.g., `β^{-2} ≫ ℓ³` and σ²R²/ε² dominates. **Worse** by ℓ³ at constant β | Bounded domain is not a real restriction (the ball reduction works with known R). Global Hessian Lipschitz → local, gradient-dependent (M₁ > 0) | Markov-converted expectation → a direct high-probability bound with logarithmic confidence cost. The baseline also gives expected accuracy; this result does not | Deterministic `H` (the baseline allows random, biased Hessians). Needs Δ and β. Pays ℓ³ and a 2⁸⁰ constant |
| Agafonov et al., [arXiv:2609.32977](https://arxiv.org/abs/2609.32977) (v1 26 Sep 2026; preprint), Thm 4.1. **Prior. Covers only the σ = 0 special case** (exact gradients) | Hessians `O((1+(M₁R²)^{1/3}+(R/ρ)^{2/3})(1+log₊(τ̄₀R²/ε)) + (M₀R³/ε)^{2/7} + (δR²/ε)^{1/2})`, gradients of the same order up to logs → the bound at σ = 0 | **Worse**: same polynomial terms, extra ℓ³ | Exact gradients → unbiased finite-variance gradients | **Worse**: that method is parameter-free; here all parameters are needed | That method needs symmetric `H`; asymmetry is free to fix |
| Agafonov et al., [arXiv:2309.01570v3](https://arxiv.org/abs/2309.01570) (ICLR 2024), Thm 3.2. Prior. **Global Lipschitz Hessian only (M₁ = 0)**; this is the note's main baseline | Batched + Markov: `O(1 + σ²R²/(β²ε²) + (δR²/(βε))^{1/2} + (M₀R³/(βε))^{1/3})` → the bound above | ε^{-1/3} → ε^{-2/7} curvature term, but the prior row 1 already achieves this | As in row 1 | As in row 1 | As in row 1 |

**Reduction check.** For M₁ = 0, the local condition chains to a global M₀-Lipschitz Hessian. Row 1's bound then follows by composing its theorem with the ball restriction, PSD shift, batching, and Markov's inequality. Its rate holds for every T, and batching divides σ² by b. For M₁ > 0 this reduction fails. On the ball, the Lipschitz constant becomes M₀ + M₁·sup‖∇f‖, and the setup's parameters do not bound that supremum: f = λx²/2 with x₀ = √(2Δ/λ) has gradient √(2Δλ) → ∞. A logarithmic-confidence bound cannot be had by repeating runs and keeping the best output, because without function values the outputs cannot be compared. The note's example f = Σcosh((Ax)ᵢ) checks out: M₀ = ‖A‖³e^{‖A‖ρ} and M₁ = M₀‖A^{-T}‖, and its Hessian is not globally Lipschitz.

**Proof ancestry.** The deterministic local-variation terms come from 2609.32977, and the stochastic Monteiro–Svaiter machinery from Carmon et al. (NeurIPS 2022). The new step is the clipped correction batch, which is accounted against the proposal and damped weights so that noise is paid once rather than per iteration. I did not check that proof by hand.

**Search coverage.** On 2026-11-04 (UTC) I read arXiv HTML for 2610.11693v2 (assumptions, Thm 5.1/C.7, limitations) and 2609.32977v1 (LH/IH, Thm 4.1). I also ran extended web searches for stochastic, high-probability, or generalized-smoothness accelerated second-order methods. For 2309.01570 and 2607.24520 I relied on the companion note and the repository's earlier review, not my own reading. **Mismatch:** the companion note omits 2610.11693, which predates the result's commit (d4f62392, 2026-11-04) by 27 days. That paper already gives the 2/7 exponent with an additive σ²R²/ε² gradient cost on the M₁ = 0 overlap, so the note's ε^{-2/7}-vs-ε^{-1/3} gain is not new. Repository overlap: [HessianAdaptiveCubic](HessianAdaptiveCubic.md) covers the constrained, expected-gap version with stochastic Hessians.

## Conclusion

**At constant confidence the rate is not better; the gains are a broader Hessian class and logarithmic confidence cost.**

The strongest baseline is Agafonov et al., arXiv:2610.11693 (Thm 5.1). Restricted to a ball of radius R, it applies whenever M₁ = 0. On that overlap, with suppressed polynomial terms abbreviated:

| | gradient calls for P(gap > ε) ≤ β |
|---|---|
| 2610.11693 + Markov | `1 + σ²R²/(β²ε²) + (δR²/(βε))^{1/2} + (M₀R³/(βε))^{2/7}` |
| this result | `[1 + σ²R²/ε² + (δR²/ε)^{1/2} + (M₀R³/ε)^{2/7}] · log³(…/β…)` |

So the selected result is ℓ³ worse at constant β and better only when 1/β is large enough to beat ℓ³. It also covers M₁ > 0 functions, whose Hessians may vary faster where gradients are large, such as the cosh example. Those functions are outside every checked stochastic baseline, because the reduction would need a gradient bound that the parameters do not supply.

The gain is modest for concrete reasons. The polynomial budget is exactly the term-by-term union of the deterministic local-variation bound (2609.32977) and the stochastic bound (2610.11693). The M₁ > 0 extension adds only (M₁R²)^{1/3} + (R/ρ)^{2/3}. Against those papers, the result loses parameter-freeness, expected-gap accuracy, and random Hessians, and pays ℓ³.

I found no prior high-probability or generalized-Hessian-smooth stochastic result of this kind, but the search was targeted and the literature is weeks old. What can be claimed: the first checked high-probability, finite-variance guarantee at the 2/7 order under gradient-dependent local Hessian variation.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
