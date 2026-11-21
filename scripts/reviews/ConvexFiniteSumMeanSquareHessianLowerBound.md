# Novelty review: ConvexFiniteSumMeanSquareHessianLowerBound

[`result`](../../LongTails/Theorems/ConvexFiniteSumMeanSquareHessianLowerBound.lean) proves the following. Take any randomized algorithm that adaptively picks a pair (component index, point) and gets back the exact value, gradient and full Hessian of that component. Then for every fixed per-run cap `b ≤ ⌊n(1+(HR³/(√n ε))^{2/7})/2¹⁶⌋`, some admissible instance has expected objective gap `> ε` ([setup](../../LongTails/Setups/ConvexFiniteSumMeanSquareHessian.lean)). The setup's `allowedAlgorithm` is the default `True`, so the result covers every algorithm, and the instance is fixed before the algorithm draws its seed.

**Necessary budget.** The bound is

  Ω( n + n^{6/7} (HR³/ε)^{2/7} ) component second-order calls,

and it is valid for `n ≥ 1`, `H ≥ 0`, `R, ε > 0` and `d ≥ 2¹⁷⁰ n³ (1+⌈(HR³/(√n ε))^{2/7}⌉)¹²`. The parameters are:
- `F = (1/n)Σfᵢ` is convex and each `fᵢ` is C².
- `(1/n)Σ‖∇²fᵢ(x)−∇²fᵢ(y)‖² ≤ H²‖x−y‖²` (mean-square Hessian Lipschitz).
- Some minimizer has norm at most `R`.
- `ε` is the target expected objective gap.

The two terms come from `n(1+s)`, with `s = (HR³/(√n ε))^{2/7}`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tsedenov–Kovalev, [arXiv:2610.10495 v1](https://arxiv.org/abs/2610.10495) (7 Oct 2026, preprint), Thm 2. Same (A1) class and same expected-gap criterion. | Ω(n + n^{6/7}(HR³/ε)^{2/7}) expected iterations → Ω(n + n^{6/7}(HR³/ε)^{2/7}) fixed-cap calls | None: same order | Algorithm class: linear-span iterates with i.i.d. uniform indices → all randomized algorithms, with adaptive indices, arbitrary query points, and arbitrary use of the full Hessians | None | Dimension grows from `d = 2K`, with `K ≈ (HR³/(√n ε))^{2/7}`, to `≥ 2¹⁷⁰n³(1+K)¹²`. The bound covers fixed caps, not expected work. |
| Zhang et al., [arXiv:2610.42040 v1](https://arxiv.org/abs/2610.42040) (30 Oct 2026, preprint), Thm 4.1. Restriction: individually convex components with individually H-Lipschitz Hessians. These instances also satisfy (A1). | Ω(n + n^{5/7}(HR³/ε)^{2/7}) on (A1) → Ω(n + n^{6/7}(HR³/ε)^{2/7}) | Larger by a factor n^{1/7} whenever HR³/ε ≥ √n | Zero-respecting, periodic, uniformly sampled algorithms → all algorithms | None | Their bound holds with probability 13/16 and applies to the narrower individual class, which this result does not certify. |

**Gap to upper bounds.** Tsedenov–Kovalev's Corollary 1 needs `O(n log(n+1) + n^{6/7}(H‖x*‖³/ε)^{2/7})` calls in *expected* work. Their step size (13) uses `‖x*‖`. The companion note pads the problem to a minimizer of norm exactly `R` and converts the method to a fixed cap with an extra `log(2+HR³/ε)` on the `n log n` term. I checked that argument only for plausibility. The remaining gap is logarithmic: the orders match when `HR³/ε ≥ √n (log 2n)^{7/2}`.

**Reduction check.** Plugging a single-function second-order lower bound into a finite sum does not give this result:
- Setting `fᵢ = f` gives only `(HR³/ε)^{2/7}`.
- Putting `f` in one component gives only `(HR³/(√n ε))^{2/7}`.

Getting the `n^{6/7}` factor needs a Woodworth–Srebro-style hidden ownership of the chain links across components. That has to work together with:
- dense or far-away probes, handled here by a ball cutoff plus a shared quadratic;
- links the algorithm has not visited, whose full Hessian jets must stay invisible;
- a mean-square accounting that permits the `√n` scaling.

Tsedenov–Kovalev §3.2 says the span condition "can probably be removed completely by extending the arguments of Arjevani et al. (2019)". Zhang et al. likewise "believe" a randomized version holds via robust zero-chains and leave it to future work. So the statement was conjectured, but no proof was available. Proof ancestry: Woodworth–Srebro (NeurIPS 2016) supplies component hiding for first-order oracles, and Carmon et al. and Arjevani–Shamir–Shiff supply randomized (nonconvex) and deterministic span-free chain arguments for a single function. Neither supplies the combined second-order finite-sum argument.

**Search coverage.** I searched arXiv and the web on 2026-11-21 for second-order finite-sum lower bounds that are randomized or free of span assumptions, in the convex case and under mean-square or individual smoothness. I found none that predates this result, which was introduced in commit `d07e227c` on 2026-11-21. The two preprints above were read in their main text, but parts of the appendices only as summaries. I checked Emmenegger et al. ([arXiv:2103.05138](https://arxiv.org/abs/2103.05138); nonconvex stationarity, a different criterion) only via the abstract and snippets, and I did not verify the note's "Wu et al." citation. Two discrepancies with the note: the note's label "(A2)" does not appear in Tsedenov–Kovalev, and the note's claim that the hard components are individually convex is not part of the Lean statement. I did not run the build or the axiom audit.

## Conclusion

**The rate is unchanged; what is new is that the known lower bound now holds for every algorithm, not only for span-restricted methods.**

The strongest baseline is Tsedenov–Kovalev's Theorem 2. It has the same mean-square class, the same expected-gap criterion and the same order:

  Ω(n + n^{6/7}(HR³/ε)^{2/7}),

but it applies only to linear-span iterates with i.i.d. uniform indices. This result covers algorithms that choose indices adaptively, probe anywhere, and exploit the full Hessians. Combined with their `Õ(n + n^{6/7}(HR³/ε)^{2/7})` upper bound, this settles the problem-class complexity up to logarithms in high dimension.

The costs are an astronomically large required dimension (prior: `d ≈ 2K`) and fixed-cap rather than expected-work counting. The statement was explicitly conjectured by both prior papers. Still, no simple reduction from single-function bounds gives the `n^{6/7}` factor. The proof has to handle hidden component ownership, arbitrary probes, and mean-square scaling together.

On priority: my search found no earlier unrestricted proof. The relevant literature is only weeks old, though, so a parallel result could exist.

The claimable contribution is the first lower bound for all algorithms, of order `n + n^{6/7}(HR³/ε)^{2/7}`, for convex finite sums with mean-square-Lipschitz Hessians. This extends a known span-restricted bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
