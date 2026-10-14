# Fast Douglas–Rachford splitting for non-quadratic smooth f: novelty assessment

[`result`](../../LongTails/Theorems/AcceleratedDouglasRachfordConvex.lean) proves the following. Take f convex with L-Lipschitz gradient and g convex on a convex set C, with access only to exact `prox_{γf}` and `prox_{γg}` (over C) at one fixed γ. Then the fast DRS iteration of Patrinos–Stella–Bemporad ([algorithm](../../LongTails/Algorithms/AcceleratedDouglasRachford.lean): relaxation λ, momentum (i−2)/(i+1)) returns a last iterate y_N ∈ C with F(y_N) − F(x*) ≤ 2‖w₁ − w*‖²/(λγN²) whenever 0 < λ ≤ 1 and 4γL ≤ λ ([setup](../../LongTails/Setups/DouglasRachfordSmoothConvex.lean)). The guarantee is deterministic.

**Complexity.** The proved budget, counting both prox calls of each iteration, is `2⌈√(2R²/(λγε))⌉`, i.e.

  **O(1 + R/√(λγε)) prox calls**, on the domain 0 < λ ≤ 1, 0 < γ ≤ λ/(4L).

Here R ≥ ‖w₁ − x* − γ∇f(x*)‖ is the distance from the DR start to a DR fixed point, and ε is the objective accuracy. With λ = 1 and γ = 1/(4L), this is O(1 + √(LR²/ε)). The algorithm uses γ, λ and w₁, but not L, R or ε. However, choosing an admissible γ requires an upper bound on L. The result was introduced in commit 6fffe58 on 2026-10-03.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Patrinos–Stella–Bemporad, CDC 2014 ([arXiv:1407.6723v2](https://arxiv.org/abs/1407.6723), Thm 5, same iteration). **Special case: f quadratic.** | 2⌈√(2R²/(γλε))⌉ with γ < 1/L and λ = (1−γL)/(1+γL) → 2⌈√(2R²/(λγε))⌉ | None: same order on quadratics. Their best tuned constant, 11.66L·R²/(N+1)², beats 8L·R²/N² only for N ≤ 4. | Convex quadratic f → every convex L-smooth f. This covers, for example, logistic loss plus ℓ₁ norm plus a box constraint. | None. Both give a last-iterate objective gap. | The stepsize range shrinks from γ < 1/L (with their λ rule) to γ ≤ λ/(4L). Their optimal γ = (√2−1)/L is not covered. |
| Abbaszadehpeivasti–Zamani ([arXiv:2509.06676v2](https://arxiv.org/abs/2509.06676), Sep 2025, Conjecture 4, momentum k/(k+3)) | Conjectured only, with no proof: 2R²/(γ((N²+7N−8)λ+8)) for γ ≤ 1/L → proved O(R/√(λγε)) for γ ≤ λ/(4L) | Not comparable. The earlier statement is a conjecture, not a guarantee. | This work proves the conjectured O(1/N²) order on a quarter of the stepsize range, for the k−2/(k+1) momentum of PSB14. | None | The exact constant and the range γ ∈ (λ/(4L), 1/L] remain open. The k/(k+3) variant is not formalized. |
| Standard same-oracle reduction (sketched here): recover ∇f(z) by the fixed-point loop w ← z + (w − prox_{γf}(w)), which contracts with factor γL/(1+γL) ≤ 1/5. Then run inexact FISTA with step γ (Schmidt–Le Roux–Bach 2011, [arXiv:1109.2415](https://arxiv.org/abs/1109.2415), Prop. 2). Start from x₀ = prox_{γf}(w₁), so ‖x₀−x*‖ ≤ R. | ≈ O((1 + R/√(γε))·log(2 + (R + γ‖∇f(x*)‖)/√(γε))) → O(1 + R/√(λγε)) | On the overlap γ ≤ λ/(4L) with λ of constant order, this result removes one logarithmic factor and the dependence on ‖∇f(x*)‖ inside the log. | None | Neither method needs L in its updates. The reduction's inner stopping test ‖prox(w) − z‖ ≤ δ_i is computable. | The reduction also works for γ ∈ (λ/(4L), 1/L], where this theorem does not apply. One step of the reduction is not checked line by line: the boundedness of the inexact-FISTA iterates. |
| Varying-parameter accelerated two-prox methods: Chambolle–Pock 2011 Alg. 2; Chari–Jang–Ryu–Açıkmeşe FDR ([arXiv:2605.08593v2](https://arxiv.org/abs/2605.08593), May 2026, Thm 1); applied to the dual, where f* is (1/L)-strongly convex | O(1/N²) squared distance to the dual solution, not an objective gap → objective-gap bound above | Not comparable. The accuracy criterion differs, and these methods use a stronger oracle. | None | Distance to the solution → last-iterate primal objective gap | Those methods need prox at N-dependent varying parameters. This result needs only a single fixed γ. |

**Reduction check and mechanism.** I found no substitution or change of variables that yields this theorem. The PSB14 proof uses convexity of the DR envelope, which fails when f is not quadratic. The new step is the two-point envelope inequality `env_ineq`, which has an error term −(Lγ²/2)‖G_a+G_b‖². The proof absorbs that term with a potential that pre-subtracts the bonus from the previous residual, and this works only for 4γL ≤ λ. Proof ancestry: Nesterov/FISTA potentials, and cocoercivity interpolation as in PEP analyses. These tools supply the template; the inequality and the reserve term are the additional work. The same-oracle reduction above shows that the O(1/N²) order itself is reachable up to a logarithmic factor.

**Search coverage.** On 2026-10-07 I searched arXiv and the web for accelerated DRS, ADMM and envelope methods. I also scanned the Semantic Scholar citations of PSB14 up to 2026 and read PSB14 Thm 3/5, PZ25 Alg. 3/Conj. 4, FDR's abstract and Thm 1 setup, and Schmidt et al. Prop. 2. I found no prior proof for non-quadratic f. Goldstein et al. (2014), Ozaslan–Jovanović (2025) and Bredies–Sun (2016) were checked only at abstract or snippet level. The companion note matches the Lean statement. However, it compares only with oracles that are stronger (FISTA's gradient, varying parameters) and omits the same-oracle reduction above.

**Conclusion**

**It gives a new proof for a specific method, but no meaningful complexity gain for the problem.**

PSB14 proved O(1/N²) objective accuracy for this exact fast DRS iteration only when f is quadratic. Abbaszadehpeivasti–Zamani (Sep 2025) stated the general convex L-smooth case as an open conjecture. This result proves that order for every convex L-smooth f, for constant λ ∈ (0,1] and γ ≤ λ/(4L). As far as my search shows, no earlier proof exists. That is historical novelty for this algorithm, not a new problem class.

The decisive comparison is with the same two fixed-γ prox oracles:

| | prox calls for F(y) − F* ≤ ε |
|---|---|
| this result | O(1 + R/√(λγε)), needs γ ≤ λ/(4L) |
| gradient recovery + inexact FISTA (sketched) | O((1 + R/√(γε))·log(2 + (R + γ‖∇f(x*)‖)/√(γε))), needs γ ≤ 1/L |

So the gain is one logarithmic factor in the regime γ ≤ λ/(4L). The reduction also covers larger γ, where this theorem does not apply. If that reduction failed at its unchecked step (iterate boundedness), the case for a complexity advantage would strengthen. It would still be limited to the fixed-parameter oracle model. Methods that use a gradient oracle or varying prox parameters already reach O(1/N²).

What can be claimed is the first proof, to my knowledge, of O(1/N²) last-iterate objective accuracy for PSB fast DRS with non-quadratic smooth f. Its optimization advantage is only a logarithmic factor over a standard same-oracle construction.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
