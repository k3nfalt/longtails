# Accelerated stochastic optimization under near-affine hidden convexity

[`result`](../../LongTails/Theorems/HiddenConvexAcceleratedStochastic.lean) proves that a safeguarded similar-triangles (AC-SA-type) method ([algorithm](../../LongTails/Algorithms/SafeguardedSimilarTriangles.lean)) reaches `E[F(x_K)] − F(x*) ≤ ε` at its last iterate. The method makes one stochastic-gradient call per iteration. The objective `F` is globally `L`-smooth and has a global minimizer `x*` with `‖x₀−x*‖ ≤ R`. On `ball(x₀,3R)` it equals `H∘c`, where `H` is convex and differentiable on an open set `U`. On `closedBall(x₀,2R)`, the map `c` has a Jacobian `J` with `‖Jv‖ ≥ μ‖v‖` that is `L_J`-Lipschitz, and the regime satisfies `32 L_J R ≤ μ`. The oracle is IID, jointly measurable and unbiased, with variance at most `σ²` ([setup](../../LongTails/Setups/LocalHiddenConvexStochastic.lean)). The updates use only `L, R, σ, x₀`, while the budget also needs `ε`.

**Complexity.** Here `L` is the smoothness constant, `R` the initial-distance bound, `σ²` the variance and `ε` the target accuracy. The constants `μ` and `L_J` enter only through the regime condition. The proved budget gives

  N = O( (√(LR²/ε) + σ²R²/ε²) · log²(2 + LR²/ε + σ²R²/ε²) ) oracle calls,

for every `L, R, ε > 0` and `σ ≥ 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fatkhullin–He–Hu, [arXiv:2401.00108v2](https://arxiv.org/abs/2401.00108) (SIOPT 2025), Thm 5 (P-SGD) and Thm 8 (momentum, last iterate). Prior. **Restriction:** projected onto a compact convex `X` with convex image `U = c(X)` of diameter `D_U`, where `c⁻¹` is `1/μ_c`-Lipschitz. Overlap: our instances with such an `X ∋ x₀, x*`, so `D_U/μ_c ≥ ‖x₀−x*‖`; take the best case `D_U/μ_c ≍ R`. | Õ(LR²/ε + LR⁴σ²/ε³) → O((√(LR²/ε)+σ²R²/ε²)·log²(·)) | Speedup by a factor of at least `√(LR²/ε)/log²(·)`: the deterministic term goes from `ε⁻¹` to `ε⁻¹ᐟ²`, and the noise term from `LR⁴σ²/ε³` to `σ²R²/ε²`. The gain survives whenever `LR²/ε ≫ log²(2+LR²/ε+σ²R²/ε²)`. | Incomparable classes. This result removes the compact convex `X` with convex `c(X)`, which the residual-map family `c(x)=x+βWᵀφ(Wx)` need not have. It adds a C^{1,1} requirement on `c` and the regime. | Step sizes no longer depend on `ε`, `D_U` or `μ_c` (anytime updates); stopping still needs `ε`. Same output: last-iterate expected gap (as in Thm 8). | Requires `32L_JR ≤ μ` and a local C^{1,1} `c`, which FHH do not need. Unconstrained with a global minimizer. The guarantee is in expectation only. |
| Bhaskara–Cutkosky–Kumar–Purohit, [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/c40fc068ed2b4ad43bff4f3f3206691e-Abstract-Conference.html), Thm 5.4. Prior. **Restriction:** global `c` with ρ-Lipschitz `J` and `‖J‖ ≤ 1/α`, `H` Lipschitz, oracle bounded a.s. by `H`, known `D₁, D₂`. | O(D₂⁴H³ρ/((αβ)⁴ε³)) → as above. `α` and `D₂` have no counterpart here. | `ε⁻³ → ε⁻²` on the smooth overlap; the full constants are not comparable. | Classes are incomparable. This result relaxes almost-surely bounded gradients to bounded variance and global C^{1,1} to local C^{1,1}. | Same last-iterate expectation output. | Needs global `L`-smoothness, so nonsmooth `H` is lost, and the regime condition. BCKP's result is global. |
| Lan, AC-SA, Math. Program. 133 (2012), Cor. 1. **Special case `L_J = 0`:** `F` convex. | O(√(LR²/ε)+σ²R²/ε²) → same order plus log² | Worse: an extra `log²(2+LR²/ε+σ²R²/ε²)` factor | Convex `F` → near-affine hidden convex `F`, which can be nonconvex and not quasar-convex (example below) | None | log² loss |

**Reduction check and mechanism.** I found no standard reduction that gives this bound. Hidden convexity yields the support inequality `F* ≥ F(y)+⟨∇F(y),x*−y⟩+⟨∇F(y),q(y)⟩` with `‖q(y)‖ ≤ (L_J/μ)‖y−x*‖²`. Treating the last term as a (δ,L)-oracle error leaves a non-vanishing δ of order `LR²·L_JR/μ`. Weak gradient domination alone has an `ε⁻³` stochastic lower bound (Masiha–Kiyavash–Thiran, [arXiv:2606.28278](https://arxiv.org/abs/2606.28278), α=1). Gupta–Wojtowytsch ([arXiv:2410.08395v3](https://arxiv.org/abs/2410.08395)) accelerate only under strong aiming (μ>0). Quasar-convex acceleration fails on the curved-valley instance: for every minimizer there are ball points where `⟨∇F,x−x̄⟩ < 0 < F−F*`. As written, that instance is not globally `L`-smooth, but a cutoff outside `ball(x₀,3R)` restores admissibility. The new step is an Abel-summation corrector `−D_k⟨z_k−x*,q(y_k)⟩` in the energy, combined with a projection-margin argument. The proof ancestry is AC-SA/similar triangles (Lan 2012) and BCKP's averaging stability (§3); neither supplies the hidden-convex slack control.

**Search coverage (2026-10-14).** I searched arXiv, ICLR proceedings and SIOPT. I verified FHH Thms 5 and 8 and its §7 open questions ("whether Nesterov's acceleration is possible"), and BCKP Thm 5.4 and their conclusion. Lan 2012's corollary was not re-read. The `Õ(ε⁻²)` hidden-convex results of Chen et al. (they need access to `c` and a separable box) and of variance-reduced policy-gradient work (they need mean-squared smoothness and RL structure) use stronger oracles; I know them only through FHH's description. The constrained bundle-level work of [Fatkhullin–He–Lan–Wolf (2025)](https://arxiv.org/abs/2511.10626) is deterministic and `Õ(ε⁻¹)`. The result entered the repository today, so its chronology relative to unpublished work is uncertain. Companion-note discrepancies: the curved-valley smoothness issue above, and the stronger-oracle `ε⁻²` work, which the note omits.

## Conclusion

**Yes: inside the near-affine regime, the proved complexity is better than the best known hidden-convex guarantees.** The strongest baseline is Fatkhullin–He–Hu's projected SGD with momentum:

| | Calls for `E[F(x_K)]−F* ≤ ε` |
|---|---|
| FHH (best case `D_U/μ_c ≍ R`) | Õ(LR²/ε + LR⁴σ²/ε³) |
| This result | O((√(LR²/ε) + σ²R²/ε²)·log²) |

The gain is a factor of at least `√(LR²/ε)` up to log², and up to `LR²/ε` when noise dominates. It requires `32L_JR ≤ μ` and a C^{1,1} reparametrization. Outside that regime nothing improves. On convex instances (`L_J=0`) the result loses a log² factor to AC-SA, but it matches the convex lower bound up to logarithms.

The class is genuinely broader than convex or quasar-convex objectives. An admissible instance with a curved minimizer manifold is neither convex nor quasar-convex, so known acceleration theorems do not apply to it. FHH's ε⁻³ results and BCKP's result cover settings this theorem does not: compact convex images, nonsmooth `H`, and no regime restriction.

The comparison establishes the gain. Priority rests on a search that found no earlier accelerated or `ε⁻²` bounded-variance result under hidden convexity; that search is not proof of absence. The contribution that can be claimed is the first accelerated, `ε⁻²`-stochastic guarantee for unknown near-affine hidden-convex reparametrizations, which partially answers FHH's acceleration question in this regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
