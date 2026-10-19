# Novelty review: MixedRelativeSmoothNonconvex

[`result`](../../LongTails/Theorems/MixedRelativeSmoothNonconvex.lean) ([setup](../../LongTails/Setups/MixedRelativeSmoothNonconvex.lean), [algorithm](../../LongTails/Algorithms/MultiscaleRepresentatives.lean)): for an L-smooth f with gap Δ, an unbiased jointly measurable oracle whose error satisfies E‖e(x)‖² ≤ r‖∇f(x)‖² + σ² and E‖e(x)−e(y)‖² ≤ r(‖∇f(x)‖²+‖∇f(y)‖²) + M²‖x−y‖², and IID samples shared by consecutive call pairs, a nested variance-reduced method with known parameters returns a uniformly sampled pre-step iterate X with E‖∇f(X)‖ ≤ ε.

**Proved budget** (scalar gradient calls, universal constant 2²⁴ suppressed; zero calls if 2LΔ ≤ ε²):

  O( 1 + (1+r)LΔ/ε² + σ²/ε² + min{ MσΔ/ε³ , LΔσ²/ε⁴ } ).

Here L is the gradient-Lipschitz constant, Δ ≥ f(x₀) − inf f, r is the relative-noise coefficient, σ is the absolute noise level, M is the centered-increment smoothness and ε is the target accuracy. There are no logarithms.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SGD under ABC noise: Khaled–Richtárik, [arXiv:2002.03329v3](https://arxiv.org/abs/2002.03329) (Jul 2020), Cor. 1 with A=0, B=1+r, C=σ². Direct competitor on the full class. | O((1+r)LΔ/ε² + LΔσ²/ε⁴) → O(1+(1+r)LΔ/ε² + σ²/ε² + min{MσΔ/ε³, LΔσ²/ε⁴}) | Never worse up to constants, since σ²/ε² ≤ 2LΔσ²/ε⁴ whenever 2LΔ > ε². When σ² ≥ (1+r)ε² and Mε ≤ Lσ, the ε⁻⁴ term becomes σ²/ε² + MσΔ/ε³, a speedup of order min{LΔ/ε², Lσ/(Mε)}. | None: SGD needs no increment condition. | SGD: min_k E‖∇f(x_k)‖, which converts to a random iterate through its averaged proof. This result: random iterate. Effectively none. | Needs the mixed increment condition, shared-sample paired calls, known L, r, M, σ, Δ, O(Td) memory and a 2²⁴ constant. |
| STORM variant: Liu–Jagabathula–Zhou, [arXiv:2302.06032v2](https://arxiv.org/abs/2302.06032v2) (Oct 2023; venue not verified), Thm 3.3/Cor. 3.4 with L₁=0. Their Assumption 3B is **raw** mean-squared smoothness with constant L̄ ≥ L, plus affine noise 4B. Overlap only. | With K = max{64r, 1} and G₀ = ‖∇f(x₀)‖ ≤ √(2LΔ): O((1+r)L̄Δ/ε² + (σ+√r G₀)√(1+r)/ε + L̄σΔ/ε³ + (σ²+σ√r G₀)σ/(√(1+r) ε³)) → the bound above with M ≤ L̄ | Uniformly no worse on the overlap: L ≤ L̄, M ≤ L̄, and σ²/ε² is bounded by their terms plus r. Strict gains: L̄ is replaced by the centered M, and the σ³/ε³ start-up term disappears. Example: g = C(∇f + z) with a random linear sparsifier C and x-independent z. Then M = 0 and L̄ = √(1+ω)L, so the cost goes from at least √(1+ω)LσΔ/ε³ to O((1+ω)LΔ/ε² + (1+ω)σ_z²/ε²). | Raw MSS (finite L̄) → mixed centered condition. Oracles with rough, x-discontinuous relative gains (L̄ = ∞, M finite) become covered. | min_t E‖∇F(x_t)‖ → uniformly sampled iterate. Conversion of their bound not checked. | Their theorem covers (L₀,L₁)-smoothness, uses constant batches and needs no paired-call structure beyond STORM's. Their literal oracle is ∇f(x,ξ); extending it to vector oracles was not checked. |
| Bounded-variance variance reduction (r = 0): SPIDER (Fang et al., NeurIPS 2018) and PAGE ([Li et al., ICML 2021](https://arxiv.org/abs/2008.10898), online case). Theorem numbers not rechecked. Special case r = 0. | O(LΔ/ε² + σ²/ε² + L̄σΔ/ε³) → the same order with M ≤ L̄ | None: same order (at most centered-vs-raw). This matches the ε⁻³ order of the Arjevani et al. (Math. Prog. 2023) MSS lower bound. | None at r = 0. | None. | None beyond paired calls. |

**Reduction check.** The obvious reduction runs PAGE/SPIDER on consecutive differences under the mixed inequality. My sketch (not a theorem) has the relative increment term r‖∇f‖² accumulate over the refresh horizon, giving O((1+r)LΔ/ε² + σ²/ε² + (M + √r L)σΔ/ε³). The new bound removes the √r·LσΔ/ε³ term. That gain is unbounded at fixed r ≥ 1 when M ≪ √r L, √r σ/ε ≫ 1+r and σε ≪ √r LΔ. For example, with r = 1, M = 0 and L, Δ, σ fixed, the cost drops from ε⁻³ to ε⁻².

**New mechanism.** Each scale uses uniformly sampled representatives of the previous completed block, with start-up batches, so relative charges are averaged over a block instead of being paid per step. **Proof ancestry:** nested variance reduction comes from SNVRG (Zhou–Xu–Gu, JMLR 2020). That paper supplies the multi-level telescoping, not this charge allocation or this rate.

**Search coverage.** Searches on 2026-10-18 UTC covered arXiv, proceedings and the web for variance reduction under affine, relative, strong-growth, ABC and Blum–Gladyshev noise. I read the Khaled–Richtárik and Liu–Jagabathula–Zhou theorem statements. I checked Fradin et al. ([arXiv:2512.18713v2](https://arxiv.org/abs/2512.18713v2)) and Upadhyay et al. ([arXiv:2605.15314v1](https://arxiv.org/abs/2605.15314)) only at the abstract level; they cover heavy-tailed and distance-growing noise, not this condition. I did not re-read DASHA or MARINA. The companion note names arXiv:2302.06032 correctly, but its "Theorem 3.3" bound is a min-over-iterates guarantee, which the note does not mention. The result entered the repository in commit fe07b78 (2026-10-18 21:58 UTC). Repository PR #21 (affine variance plus full MSS) is a related artifact, not a prior publication.

**Conclusion**

**Yes: on the full mixed-noise class, the proved complexity beats every published guarantee I found, and on the raw-MSS overlap it is never worse.**

On the full class, the only applicable published guarantee is SGD under ABC noise:

  SGD: (1+r)LΔ/ε² + LΔσ²/ε⁴  →  here: (1+r)LΔ/ε² + σ²/ε² + min{MσΔ/ε³, LΔσ²/ε⁴}.

The new bound is never worse. When σ² ≥ (1+r)ε² and Mε ≤ Lσ, it is faster by a factor of order min{LΔ/ε², Lσ/(Mε)}.

The relevant variance-reduction baseline, Liu–Jagabathula–Zhou's STORM variant, needs raw mean-squared smoothness L̄. That fails for oracles whose relative noise varies roughly with x. Where L̄ is finite, the new bound is no worse, and it is strictly better for noisy compressed gradients: there it drops from about √(1+ω)LσΔ/ε³ to order ε⁻² at fixed parameters. A direct PAGE-type reduction appears to pay an extra √r·LσΔ/ε³ term, which this result avoids.

The literature search does not establish priority. A variance-reduction analysis under relative noise may exist that I did not find, and the PAGE comparison is my own sketch. The result also needs shared-sample paired calls, known parameters, O(Td) memory and a 2²⁴ constant. It is optimal only at the r = 0 endpoint. What can be claimed is a new expected-stationarity complexity for smooth nonconvex optimization under combined relative and smooth-increment noise, with ε⁻³ variance-reduction scaling attained only through the centered constant M.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
