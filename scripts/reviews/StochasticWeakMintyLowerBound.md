# Novelty assessment: StochasticWeakMintyLowerBound

The [theorem](../../LongTails/Theorems/StochasticWeakMintyLowerBound.lean) is a lower bound on the [high-dimensional setup](../../LongTails/Setups/HighDimensionalStochasticWeakMinty.lean), a restriction of the [general setup](../../LongTails/Setups/StochasticWeakMinty.lean). It concerns a randomized adaptive method that queries an oracle g(x,ξₖ), where the samples ξₖ are IID, g is jointly measurable, unbiased for F, and has variance at most σ². The method has no `allowedAlgorithm` restriction, may run for any number of calls N ≤ budget (N = 0 included), and may output any point. For each such method there is an L-Lipschitz F on ℝᵈ, chosen depending on the method and N but not on its seed, that has a zero x⋆ with ‖x⋆ − x₀‖ ≤ R and satisfies the Minty inequality (already at ρ = 0), on which E‖F(x̂)‖ > ε. The hard instance is in [StochasticMintyOracle](../../LongTails/Proofs/StochasticMintyOracle.lean) and [StochasticMintyLowerBound](../../LongTails/Proofs/StochasticMintyLowerBound.lean). The setup has no algorithm module, because the theorem quantifies over all methods.

**Necessary calls.** L is the Lipschitz constant, R bounds the distance from x₀ to x⋆, σ² is the variance bound, ε is the expected-residual target, and d is the dimension. The bound is

  N ≥ ⌊L²R²(ε² + σ²)/(2¹⁹ε⁴)⌋ = Ω( (L²R²/ε²)(1 + σ²/ε²) ).

It holds whenever 0 ≤ ρ ≤ 1/(20L), 2¹⁰ε ≤ LR and d ≥ (LR/ε)⁶(1 + σ²/ε²). The bound is vacuous unless LR/ε ≥ 2¹⁰.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Yoon–Ryu, ICML 2021](https://proceedings.mlr.press/v139/yoon21d.html), Thm. 3 (monotone, which implies Minty with ρ = 0), plus the folklore Ω(σ²/ε²) mean-estimation bound for F(x) = L(x − c) | Ω(LR/ε + σ²/ε²) → Ω((L²R²/ε²)(1 + σ²/ε²)) | Larger by a factor of at least LR/(2ε) always, and at least L²R²/(2ε²) when σ² ≥ εLR. | Monotone hard instances → non-monotone Minty instances | Deterministic span methods → arbitrary randomized methods and outputs | Needs d ≥ (LR/ε)⁶(1 + σ²/ε²); Yoon–Ryu needs only d of order N |
| Repository [EuclideanWeakMintyLowerBound](../../LongTails/Theorems/EuclideanWeakMintyLowerBound.lean) (commit 98684e93, 2026-11-17, unpublished), deterministic (σ = 0), combined with mean estimation | Ω(L²R²/ε² + σ²/ε²) → Ω((L²R²/ε²)(1 + σ²/ε²)) | The noise term changes from additive to multiplicative, a gain of at least ½·min{L²R²/ε², 1 + σ²/ε²}. The full factor L²R²/(2ε²) is reached when σ ≥ LR. | Exact oracle → bounded-variance stochastic oracle | None | Larger dimension: (LR/ε)⁶ becomes (LR/ε)⁶(1 + σ²/ε²) |
| Upper bound: [Diakonikolas–Daskalakis–Jordan, AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), Thm. 4.5(i) (EG+, ρ < 1/(4√2L), constant batch O(σ²/ε²)); repository [StochasticWeakMintyExtragradient](../../LongTails/Theorems/StochasticWeakMintyExtragradient.lean) | Upper O((L²R²/ε²)(1 + σ²/ε²)) vs lower Ω(same) | Not an improvement of an upper bound. It certifies optimality up to a universal constant of about 2³⁸–2³⁹ in the stated regime. | None | DDJ bounds E‖F‖² at a random iterate, which implies the same E‖F‖ criterion by Jensen | The hard oracle is discontinuous in x, so the bound does not cover Lipschitz-in-mean oracles ([Pethick et al., ICLR 2023](https://arxiv.org/abs/2302.09029), Assumption III). |

**Reduction check.** [Arjevani et al.](https://arxiv.org/abs/1912.02365) prove an ε⁻⁴ bound, but its gradients of nonconvex functions are not Minty, so it does not transfer; and Minty gradient fields are star-convex, which admits fast methods. Composing the deterministic Minty bound with mean estimation gives only the additive Ω(L²R²/ε² + σ²/ε²). The multiplicative term requires the new step: masking with probability q, applied only to the frontier link of the repository's dead-zone chain, with the revealed prefix indexed by a coin count independent of π. The proof ancestry is the Arjevani et al. masking, which supplies the probabilistic hiding idea, and the repository's chain and prefix-counting lemma, which supply the Minty geometry and the randomized hiding.

**Search coverage.** I searched on 2026-11-19 for lower bounds on stochastic, weak-Minty, star-monotone and non-monotone VIs, and read DDJ Thm 4.5 in full. I also checked [Alacaoglu–Kim–Wright, arXiv:2402.05071](https://arxiv.org/abs/2402.05071), which gives Õ(ε⁻²) deterministic and Õ(ε⁻⁴) stochastic weak-MVI upper bounds and no lower bound; [Alacaoglu–Kim, ICML 2026](https://proceedings.mlr.press/v306/alacaoglu26a.html), Õ(ε⁻⁴); [Arefizadeh–Nedić, arXiv:2408.16918](https://arxiv.org/abs/2408.16918), which has no complexity bounds; and [arXiv:2601.23034](https://arxiv.org/abs/2601.23034), an O(ε⁻³) claim that assumes mean-squared smoothness and was withdrawn on 2026-10-17. Reading for Böhm, CGL and Alacaoglu–Kim was partial, so their exact L,R dependence is unverified. Git history dates the result to commit 1cb8f879 (2026-11-19).

Two points in the companion note need correction. DDJ Thm 4.5(i) uses a constant ε-dependent batch, not growing batches. Its Θ claim holds only under the dimension condition and the condition LR ≥ 2¹⁰ε. I did not build the proofs or run the axiom audit; a text search found no `sorry`.

## Conclusion

**Yes: this is a new lower bound showing that the ε⁻⁴ noise cost of stochastic Minty problems cannot be improved under bounded variance in high dimension.**

The strongest previous lower bound for this oracle class came from combining a deterministic bound with mean estimation. The strongest upper bound is DDJ's minibatch EG+ (Thm 4.5(i)):

| | Calls for E‖F(x̂)‖ ≤ ε |
|---|---|
| Previous lower (deterministic Minty + mean estimation) | Ω(L²R²/ε² + σ²/ε²) |
| This result (any randomized method) | Ω((L²R²/ε²)(1 + σ²/ε²)) |
| Upper (DDJ EG+; repository minibatch EG) | O((L²R²/ε²)(1 + σ²/ε²)) |

When σ ≥ ε, the necessary noise cost grows by the factor (LR/ε)². This separates Minty problems from monotone and cohypomonotone ones, where the noise cost is additive, σ²/ε². The deterministic Minty chain it builds on is itself a repository result from two days earlier, so the contribution beyond the repository is adapting the Arjevani-style masking to that chain.

The limitations are the required dimension d ≥ (LR/ε)⁶(1 + σ²/ε²), large constants, and the exclusion of Lipschitz-in-mean oracles. With such oracles, variance reduction might still reach ε⁻³. My search found no prior stochastic lower bound for this class, but that does not establish priority. What can be claimed is a matching Θ((L²R²/ε²)(1 + σ²/ε²)) characterization for bounded-variance Minty VIs in high dimension.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
