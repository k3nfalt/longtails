# HessianAdaptiveCubic: novelty assessment

[`result`](../../LongTails/Theorems/HessianAdaptiveCubic.lean) proves that an accelerated stochastic cubic method ([algorithm](../../LongTails/Algorithms/HessianAdaptiveCubic.lean)) run for `N = ⌈10¹⁸ Q J²⌉` rounds (3 oracle calls each) returns its weighted-average point `w_N ∈ C` with `∫ f(w_N) − f(x*) dP ≤ ε`. This holds for any convex `f` with a ρ-Lipschitz Hessian on a compact convex set `C` of diameter ≤ D, as specified in the [setup](../../LongTails/Setups/HessianAdaptiveStochasticConvex.lean). The gradient oracle is IID, unbiased, with variance ≤ σg². The Hessian oracle returns pointwise-PSD samples, possibly biased, with mean-square operator error ≤ σh². The updates use `C, x₀, D, ρ, σg`, but not σh or ε.

**Proved complexity** (D: diameter bound; ρ: Hessian-Lipschitz bound; σg, σh: gradient/Hessian RMS errors; ε: expected accuracy):

```
O( [1 + σg²D²/ε² + (σh D²/ε)^{1/2} + (ρD³/ε)^{2/7}]
   · [1 + log((1 + σh/(ρD))(1 + σg²D²/ε² + (σh D²/ε)^{1/2} + (ρD³/ε)^{2/7}))]² )
```

This is read directly off the Lean budget `3⌈10¹⁸ Q J²⌉` (`Proofs/HessianAdaptiveCubicRate.lean`, `accuracy_at_shape_budget`). The budget itself depends on σh, so the algorithm cannot use it as a stopping rule when σh is unknown.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Agafonov, Ashabokov, Kamzolov, D'yakonov, Gasnikov, Takáč, [arXiv:2610.11693](https://arxiv.org/abs/2610.11693) (v1 8 Oct 2026, v2 13 Oct 2026; preprint), Thm 5.1 / Alg. 2, with M = ρ. **Prior, direct competitor**, same model: bounded closed convex domain, biased a.s.-PSD Hessians, 2 gradients + 1 Hessian per iteration | `O(1 + σg²D²/ε² + (σhD²/ε)^{1/2} + (ρD³/ε)^{2/7})` → the bound above | **Worse** by the `[1+log(...)]²` factor; same polynomial order | None. Pointwise PSD (here) is formally slightly stronger than a.s. PSD | Known σh in λ_t = σg t³/D² + σh t^{3/2}/D + 2M → σh unknown in updates. σh is still needed for the stopping budget. Same averaged output and expected-gap criterion | Pays the log² factor and a 10¹⁸ constant. Still needs ρ and σg. Separate samples for g and H (the source allows shared ones) |
| Antonakopoulos, Kavis, Cevher, *Extra-Newton*, [NeurIPS 2022, arXiv:2211.01832](https://arxiv.org/abs/2211.01832), Thm 3.2 (γ = D). Prior; applies only to the **unbiased-Hessian subclass** | `O(σg²D²/ε² + (σhD²/ε)^{2/3} + (ρD³/ε)^{1/3} + β₀-initialization term)` → the bound above | Hessian term: ε^{-2/3} → ε^{-1/2}. Curvature term: ε^{-1/3} → ε^{-2/7}, up to log². This holds when `(σhD²/ε)^{1/2}` or `(ρD³/ε)^{2/7}` dominates σg²D²/ε², and only on their common subclass | Unbiased Hessians → biased PSD Hessians (biased PSD samples are not covered there) | **Worse**: Extra-Newton needs neither ρ nor σg (nor σh); here ρ and σg must be supplied | Needs known ρ and σg. PSD samples required (Extra-Newton does not need them) |
| Agafonov et al., [arXiv:2609.32977](https://arxiv.org/abs/2609.32977) (v1 26 Sep 2026; preprint), Thm 4.1. Prior; **special case only**: exact gradients (σg = 0), deterministic ‖H − ∇²f‖ ≤ δ, unconstrained | `O(1 + log₊(τ̄₀/(ρR+δ)) + (ρR³/ε)^{2/7} + (δR²/ε)^{1/2})` Hessians, same order in gradients, R = ‖x₀ − x*‖ ≤ D → this bound at σg = 0 | None: same order (here with extra log²) | Incomparable classes. Here: stochastic gradients, RMS (not uniform) Hessian error, constraints. There: unconstrained, generalized smoothness | None: that method is already adaptive to δ and ρ | That method needs exact gradients |

**Reduction check.** The algorithm is 2610.11693's Alg. 2 (α_t = 4/(t+3), β_t = λ_t D/t^{3/2}). The only change is that the σh t^{3/2}/D + 2M part of λ_t is replaced by an AdaGrad-type residual accumulator (initialized at 2ρ, floored at σg t³/D²), the same idea as in Extra-Newton.

There is no plug-in reduction to known-σh tuning:
- An underestimate of σh voids Thm 5.1.
- Guess grids cannot be pruned, because the oracle returns no function values.

The real technical step is controlling the bias from normalizing by a scale that depends on the fresh gradient. The proof does this with harmonic and log self-bounds, which is why it needs ≈3.9k Lean lines. I did not verify that proof by hand. Proof ancestry: Extra-Newton (adaptive scale) and Agafonov et al. (optimal-order tuned scheme).

**Search coverage.** On 2026-10-26 (UTC) I checked:
- arXiv abstracts and HTML for 2610.11693v2 (Assumptions 3.1, 3.3–3.5; Thm 5.1; Limitations, which lists adaptive variants as future work), 2309.01570v3 (ICLR 2024; Thm 3.2 gives an ε^{-1/3} curvature term and is unconstrained, so it is dominated by row 1) and 2609.32977v1 (Thm 4.1);
- the Extra-Newton PDF text (Thm 3.2; oracle assumption (2) requires unbiased Hessians);
- web searches for adaptive or parameter-free stochastic cubic or MS acceleration.

I could not find "Chen et al. (2026)", whom 2610.11693 cites for optimal inexact-Hessian acceleration with exact gradients. Proceedings were searched by keyword only.

The result was committed on 2026-10-26 (d289dbf), 18 days after 2610.11693 v1. I found no work, earlier or later, giving σh-agnostic updates at this order. The companion note's citations and claims match what I checked. I did not run builds or axiom audits.

## Conclusion

**No complexity improvement. What is new is that the updates no longer need the Hessian-noise level σh, at the cost of a squared logarithm.**

The strongest baseline is Agafonov et al. (arXiv:2610.11693, Thm 5.1), which works in the same constrained, biased-PSD-Hessian model with the same three calls per iteration:

| | oracle calls | needs σh |
|---|---|---|
| 2610.11693 Thm 5.1 | `1 + σg²D²/ε² + (σhD²/ε)^{1/2} + (ρD³/ε)^{2/7}` | updates and budget |
| this result | same × `[1 + log((1+σh/(ρD))·same)]²` | budget only |

The result is therefore never better in total complexity. Against fully adaptive Extra-Newton, the exponents are better: ε^{-1/2} vs ε^{-2/3} for Hessian noise, and ε^{-2/7} vs ε^{-1/3} for curvature. But that gain comes from the tuned scheme, and it needs ρ and σg, which Extra-Newton does not.

The gain is modest for concrete reasons:
- Only one of three constants becomes unknown, and only in the updates; the stopping budget still needs σh.
- The mechanism inserts Extra-Newton's AdaGrad-type scale into the 2610.11693 scheme.

The stochastic normalization-bias argument does look non-routine, and I found no prior σh-agnostic method at this order. Priority is supported only by a targeted search, in a two-week-old literature.

The contribution that can be claimed: up to log², the first optimal-order stochastic cubic guarantee whose updates do not need the Hessian-noise level.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
