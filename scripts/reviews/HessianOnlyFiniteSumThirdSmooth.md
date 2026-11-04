# Novelty assessment: HessianOnlyFiniteSumThirdSmooth

The [theorem](../../LongTails/Theorems/HessianOnlyFiniteSumThirdSmooth.lean) concerns f = (1/n)∑fᵢ on a finite-dimensional Hilbert space, where each fᵢ is convex and C³ with an L-Lipschitz third derivative ([setup](../../LongTails/Setups/FiniteSumThirdSmoothConvex.lean)). Using only exact component (∇fᵢ, ∇²fᵢ) queries, the [algorithm](../../LongTails/Algorithms/HessianOnlyFiniteSumThirdSmooth.lean) returns a point x̂ with Pr{f(x̂) − f(x⋆) ≤ ε} ≥ 2/3 within a deterministic call budget.

**Complexity.** Here R ≥ ‖x₀ − x⋆‖, ε is the target accuracy, and G ≥ ‖∇f(x₀)‖ and H ≥ ‖∇²f(x₀)‖ are bounds on the mean at x₀ only. The proved budget 2³⁸(n + ⌈(n⁴LR⁴/ε)^{1/5}⌉)(1 + ⌈log Q⌉)² gives

  O( (n + n^{4/5}(LR⁴/ε)^{1/5}) · log²(2 + n + GR/ε + HR²/ε + LR⁴/ε) )

component calls, with no dimension factor. The algorithm is given n, L, R, ε, G, H and x₀.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kamzolov–Gasnikov, [arXiv:2002.09050v3](https://arxiv.org/abs/2002.09050v3) (preprint, June 2020), Thm 2, run on the full mean (one full call = n component calls) | Õ(n(LR⁴/ε)^{1/5}) Hessians plus a log((G+H)/ε) factor for gradients → O((n + n^{4/5}(LR⁴/ε)^{1/5}) log²(…)) | The iterative term drops by a factor n^{1/5} when LR⁴/ε ≥ n. When 1 ≤ LR⁴/ε ≤ n the gain factor is (LR⁴/ε)^{1/5}. Both statements hold modulo Thm 2's unspecified log powers | G, H bound gradients and Hessians uniformly along the iterates → G, H bound them only at x₀ | Deterministic-accuracy method (Thm 2) → success probability only 2/3 | Requires every component to be convex, while Thm 2 needs only f convex. Pays the additive n·log² term |
| Zhang–Chen–Li–Zhang, [arXiv:2610.42040v1](https://arxiv.org/abs/2610.42040v1) (preprint, 30 Oct 2026, prior by 5 days), Thm 5.1. **Applies only to the overlap**: individually convex fᵢ with L₂-Lipschitz Hessians, V = L₂R³/ε | O((n + n^{5/7}V^{2/7}) log² n) expected calls (×3 under Markov truncation for success probability 2/3) → O((n + n^{4/5}(LR⁴/ε)^{1/5}) log²(…)) | On the overlap the selected bound wins when n³(LR⁴/ε)⁷ < (L₂R³/ε)¹⁰ and the iterative terms dominate. Example: L = L₂ = R = 1 and ε = n⁻² give n^{6/5} log² n vs n^{9/7} log² n. It loses when LR⁴/ε is large relative to V | The classes are incomparable. Global Hessian-Lipschitz is replaced by third-derivative-Lipschitz, which covers e.g. ∑(aᵢᵀx − bᵢ)⁴ | Expected cost with almost-sure accuracy → fixed budget with probability 2/3 | Requires C³ smoothness. Needs G and H, which enter only through the logarithm |
| Projected AGD on the ball B(x₀, R) (derived reduction). Convexity of f and the third-order Taylor bound give ‖∇²f‖ ≤ 2H + LR² on the ball | O(n(1 + √(HR²/ε + LR⁴/ε))) → O((n + n^{4/5}(LR⁴/ε)^{1/5}) log²(…)) | Polynomially better whenever HR²/ε or LR⁴/ε exceeds polylog(Q). Worse by log² Q when both are O(1) | None | None | Needs Hessian queries |

**Reduction check.** Neither full-batch hyperfast optimization nor a literal two-term application of sliding gives n^{4/5}; full-batch costs n per iteration. Kamzolov–Gasnikov remark after their Thm 3 that "one can generalize this result on sum of n functions sorted by L3,fi and applied consecutively", but they give no proof or cost accounting. The companion note's obstacles to that generalization are recursive constants and logarithms and the third-order contractions of cached cubic models. I did not verify those obstacles independently, but I found no paper that proves the bound. The genuinely new step is a self-bound that uses third-order smoothness: ‖∇fᵢ(w+s) − ∇fᵢ(w) − ∇²fᵢ(w)s‖² ≤ 2L‖s‖²D_{fᵢ}(w+s,w). It powers a variance-reduced quartic-proximal inner solver that works from a cache of quadratic models only. This is proof ancestry, not inherited complexity. The Jensen-gap/variance-reduction template comes from Zhang et al. (Lemma 5.1), and the outer adaptive Monteiro–Svaiter step comes from [Carmon et al., NeurIPS 2022](https://arxiv.org/abs/2205.15371). Nesterov's superfast and inexact high-order proximal-point second-order methods are further proof ancestry for the n = 1 case.

**Search coverage.** I searched arXiv and the web on 4 Nov 2026 UTC for finite-sum second-order and tensor methods, hyperfast and sliding methods, and variance-reduced cubic methods. I read Kamzolov–Gasnikov Thms 2–3 from the PDF. For Zhang et al. and for [Tsedenov–Kovalev, arXiv:2610.10495](https://arxiv.org/abs/2610.10495) I checked the HTML theorem statements (only partially for both). Tsedenov–Kovalev assume average smoothness and prove O(n log n + n^{6/7}V^{2/7}), which is weaker than Zhang et al. on the overlap. I did not read Nesterov's papers in full. The companion note's citations and its regime inequality match what I checked. One correction: Kamzolov–Gasnikov Thm 2 assumes G, H bound the iterates, not just x₀.

**Conclusion**

**Yes. For large n this is a polynomially better proved complexity for second-order finite-sum optimization under third-order smoothness.** The closest prior guarantees are full-batch hyperfast optimization and the 5-day-older Hessian-Lipschitz finite-sum method of Zhang et al.

| | iterative term |
|---|---|
| full-batch hyperfast | n(LR⁴/ε)^{1/5} |
| Zhang et al. (Hessian-Lipschitz) | n^{5/7}(L₂R³/ε)^{2/7} |
| this result | n^{4/5}(LR⁴/ε)^{1/5} |

Against full-batch hyperfast, the gain is a factor n^{1/5} whenever LR⁴/ε ≥ n, up to logarithms. Against Zhang et al., the classes are incomparable. On instances satisfying both assumptions, this result wins exactly when n³(LR⁴/ε)⁷ < (L₂R³/ε)¹⁰; with constant smoothness and ε = n⁻² this is n^{6/5} versus n^{9/7}. It requires third derivatives to exist and be Lipschitz, it loses when LR⁴/ε is large relative to L₂R³/ε, and it gives only 2/3 success probability.

The comparison establishes a gain. Priority is less certain: Kamzolov–Gasnikov anticipated the n^{4/5} exponent in a one-sentence, unproved remark, and this area produced closely related preprints in October 2026. Optimality is not established, since no finite-sum lower bound for this class was found.

What can be claimed is the first proved, dimension-free, Hessian-only bound of order n + n^{4/5}(LR⁴/ε)^{1/5} (up to log²) for individually convex finite sums with Lipschitz third derivatives, built on a new third-order self-bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
