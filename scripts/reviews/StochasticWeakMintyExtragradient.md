# Novelty assessment: StochasticWeakMintyExtragradient

[`result`](../../LongTails/Theorems/StochasticWeakMintyExtragradient.lean) proves that minibatch extragradient ([algorithm](../../LongTails/Algorithms/MinibatchExtragradient.lean)) uses step γ = 1/(2L), a constant batch b = ⌈2048σ²/ε²⌉+1, K = ⌈128L²R²/ε²⌉, and outputs the extrapolation point at an index drawn uniformly from {0,…,K}. On the [setup](../../LongTails/Setups/StochasticWeakMinty.lean) it achieves E‖F(x̂)‖ ≤ ε. The setup covers L-Lipschitz F on a separable real Hilbert space with a zero x⋆ satisfying ‖x⋆−x₀‖ ≤ R and ⟨F(x),x−x⋆⟩ ≥ −ρ‖F(x)‖², for 0 ≤ ρ ≤ 1/(20L). The oracle is IID, jointly measurable, unbiased, with variance ≤ σ².

**Complexity.** Let L be the Lipschitz constant, R the distance from x₀ to x⋆, σ² the oracle variance and ε the expected-residual target. The proved budget ⌈2¹⁹(1+L²R²/ε²)(1+σ²/ε²)⌉ gives

  N = O((1 + L²R²/ε²)(1 + σ²/ε²)) stochastic operator calls (no logarithms; the algorithm uses L, σ, R, ε but not ρ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Diakonikolas–Daskalakis–Jordan, *Efficient methods for structured nonconvex-nonconcave min-max optimization*, AISTATS 2021 ([arXiv:2011.00364v2](https://arxiv.org/abs/2011.00364), Thm 4.5(i)). Stochastic EG+ with a constant per-iteration batch n = O(σ²/ε²) and a uniformly random output ūᵢ. | O((1+L²R²/ε²)(1+σ²/ε²)) → O((1+L²R²/ε²)(1+σ²/ε²)) | None: same order | ℝᵈ → separable Hilbert space. This is routine: the proof uses only inner-product identities. | None. DDJ certify E‖F̃(ū)‖² ≤ ε² for the n-sample estimate. This already implies E‖F(ū)‖ ≤ ε, because the fresh batch has conditional mean F(ū), so E‖F̃‖² ≥ E‖F‖², and then Jensen applies. | Narrower ρ range. DDJ write the condition as ρ_DDJ/2 and allow ρ_DDJ < 1/(4√2L), which is ρ < 1/(8√2L) ≈ 0.088/L here, versus ρ ≤ 0.05/L. Uses EG (β=1) instead of EG+ (β=1/2). |
| Choudhury–Gorbunov–Loizou, NeurIPS 2023 ([arXiv:2302.14043](https://arxiv.org/abs/2302.14043), Thm 4.5). Mini-batched SPEG, single-call. *Special case:* finite-sum/arbitrary-sampling noise under "expected residual". | O(1/K) min-iterate E‖F‖² with batch τ = O(K) (scaling with σ⋆², the variance at x⋆), so order ε⁻⁴ in total. The exact L, R dependence was not re-derived from the extracted formula. → O((1+L²R²/ε²)(1+σ²/ε²)) | Not comparable: different noise model (ER, variance measured at x⋆) and min-over-iterates criterion | Their class requires the ER condition. Bounded variance alone does not imply it, so the classes are incomparable. | Their criterion is the best iterate, which is not computable without exact F. This result outputs a randomly stopped iterate. | They allow ρ < 1/(2L), which is wider, and need one oracle call per iteration. |
| Alacaoglu–Kim ([arXiv:2602.05531v1](https://arxiv.org/abs/2602.05531), Feb 2026, prior to this result; listed as ICML 2026 by the note, venue unverified), Thms 2.1/3.1 | Õ(ε⁻⁴) in expected residual; L, R dependence not checked → O((1+L²R²/ε²)(1+σ²/ε²)) | At most the removal of logarithmic factors in ε. The L, R constants were not compared. | None. Theirs is broader: constraints, and variance ≤ B²‖z−z₀‖²+σ². | None | Their Thm 2.1 uses increasing batches bₖ = Θ(k log k) and ρ < 1/(12L). Their Thm 3.1 allows ρ < 1/L but bounds only the *expected* number of calls (MLMC). |

**Reduction and mechanism.** The result is DDJ Thm 4.5(i) re-proved with β = 1, explicit constants, a Hilbert space, and a narrower ρ range. Their proof already has the same structure: a one-step EG potential, a cross term that vanishes by batch freshness, telescoping, and a uniform random index. No new mechanism or missing step was identified. The Lean proof's lower-Lebesgue-integral treatment avoids a priori integrability of the iterates. That is a formalization device, not a mathematical gain.

**Search coverage.** On 2026-11-19 I read the DDJ (arXiv v2) and Choudhury et al. theorem statements and DDJ's proof. I also checked Böhm (TMLR 2023, [arXiv:2201.12247](https://arxiv.org/abs/2201.12247), Thm 3.3: OGDA+, min-iterate, O(ε⁻¹) batches), Pethick et al. (ICLR 2023, [arXiv:2302.09029](https://arxiv.org/abs/2302.09029), Thm 6.1: requires Lipschitz-in-mean oracles; complexity not re-derived), and Alacaoglu–Kim's main theorems. I did not do an exhaustive proceedings search. Git history shows the result was introduced in commit 1cb8f879 (2026-11-19).

The companion note has one discrepancy. It says DDJ use "increasing batches", and it lists constant batches and a uniform random index as differences. In fact DDJ Thm 4.5(i) uses a constant batch n per iteration (tuned to ε, as here) and a uniformly random output. Pethick et al.'s phrase "increasing batch" refers to n growing as ε shrinks, and that is equally true of b = ⌈2048σ²/ε²⌉+1 here. The note does correctly say that the upper bound itself is not claimed as new.

**Conclusion**

**No: this is a re-proof of a known bound, with no improvement in complexity, scope or output.**

The strongest baseline is Diakonikolas–Daskalakis–Jordan (AISTATS 2021), Theorem 4.5(i). It uses the same oracle model (unbiased, variance σ²), the same algorithm design (constant ε-tuned minibatch, uniformly random iterate), and a criterion that implies E‖F(x̂)‖ ≤ ε:

| | Complexity | ρ range (this repository's convention) |
|---|---|---|
| DDJ'21 Thm 4.5(i) | O((1+L²R²/ε²)(1+σ²/ε²)) | ρ < 1/(8√2 L) ≈ 0.088/L |
| This result | O((1+L²R²/ε²)(1+σ²/ε²)) | ρ ≤ 0.05/L |

The orders are identical, and the selected result covers a strictly smaller nonmonotonicity range. Extending from ℝᵈ to a Hilbert space and stating explicit constants are routine. Later or broader methods (Choudhury et al., Alacaoglu–Kim) reach the same ε⁻⁴ order with wider ρ ranges or weaker noise assumptions.

What remains is a self-contained, formally checked proof of a known upper bound. Its value is as the matching half for the companion lower bound, which is a separate result and not assessed here. The companion note's claim that DDJ needed increasing batches, while this proof uses a constant batch and a random index, is inaccurate.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
