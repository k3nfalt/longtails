# CovarianceSoftCutConvex: novelty assessment

[`result`](../../LongTails/Theorems/CovarianceSoftCutConvex.lean) proves the following. Take any convex, globally L-Lipschitz f on ℝᵈ with a minimizer satisfying ‖x⋆‖ ≤ R, and an IID, jointly measurable, unbiased stochastic subgradient oracle with covariance bounded by (σ²/d)·I in every direction, that is E⟨g−v,u⟩² ≤ σ²‖u‖²/d ([setup](../../LongTails/Setups/CovarianceBoundedConvex.lean)). Then the soft-cut centroid method with tournament selection ([algorithm](../../LongTails/Algorithms/CovarianceSoftCutMethod.lean)) outputs a point with P[f(x̂) − f⋆ > ε] ≤ 1/3.

**Complexity (stochastic subgradient calls):**

  N = O( (d + σ²R²/ε²) · [1 + log(d(1 + LR/ε))]⁵ )

Here d is the dimension, L the Lipschitz constant, R the bound on ‖x⋆‖, σ² the total covariance scale (trace ≤ σ², operator norm ≤ σ²/d), and ε the target accuracy. Success probability 2/3 is fixed. The algorithm knows d, L, R, σ and ε, uses no function values, and assumes exact centroid computation at no cost.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Marsden–O'Carroll–Sidford–Zhang, NeurIPS 2025 ([arXiv 2510.20745v1](https://arxiv.org/abs/2510.20745)), Cor. 3, ESGO. **Special-case baseline:** applies only to directional sub-exponential noise, with P[\|⟨g−∇f,u⟩\| ≥ t] ≤ 2e^{−t√d/σ}. | Õ(d + σ²R²/ε²) → O((d + σ²R²/ε²)·log⁵(d(1+LR/ε))) | None: same order up to polylogs; our explicit log⁵ may be worse than theirs. | Directional exponential tails → directional second moments only. ESGO(σ) is contained in this class with scale 2σ. The new class also covers asymmetric Pareto-type noise with no third moment. | None (both have probability 2/3 and known parameters). | Exact centroids; info-theoretic only. |
| Same paper, Cor. 4 (batched cutting plane after Sidford–Zhang). Applies to the trace bound E‖g−∇f‖² ≤ σ², which contains this class. | Õ(d·σ²R²/ε² + d) → O((d + σ²R²/ε²)·log⁵(⋯)) | Noise term smaller by a factor ≈ d/polylog, once σ²R²/ε² ≳ 1 and d ≫ log⁵(d(1+LR/ε)). | Not broader. This class is the isotropic-covariance subclass. | None | Needs operator norm ≤ σ²/d. For anisotropic noise, σ² must be set to d·‖Cov‖ₒₚ, which gives back the d·V order. |
| SGD, the standard bound (cited in MOSZ §1). Applies under E‖g‖² ≤ L² + σ²; here the expected gap plus Markov's inequality gives probability 2/3. | O((L² + σ²)R²/ε²) → O((d + σ²R²/ε²)·log⁵(⋯)) | Better when d·log⁵(d(1+LR/ε)) ≪ L²R²/ε². Worse when d ≳ L²R²/ε². | None (SGD covers trace-bounded noise) | SGD has simpler arithmetic and no centroid computation | Polylog overhead; dimension term d |

**Lower bound.** MOSZ Thm. 5 gives Ω̃(σ²R²/ε² + min{L²R²/ε², d}) for ESGO oracles. Those oracles lie in this class, so the bound applies here too. The selected result is therefore tight up to polylogs when d ≤ L²R²/ε². I took the theorem statement from the paper and did not re-derive the proof.

**Standard reductions.** I checked three routes, and none reaches the bound:
- **Chebyshev.** It converts this oracle into an ISGO only with a polynomial dependence on 1/δ. Theorem 1 then needs δ ≲ 1/(d(V+d)), where V = σ²R²/ε², so the cost becomes polynomially worse.
- **MOSZ Lemma 5 (MAGO).** It averages ISGO replies and applies Hoeffding's inequality, which needs the tail assumption.
- **Coordinatewise or norm-robust median-of-means.** These give only norm accuracy σ√(log/b). That accuracy is no better than d·V.

[Lugosi–Mendelson, JEMS 26 (2024)](https://arxiv.org/abs/2010.11921) controls error in every direction, but its error still includes a trace-scale term √(E‖X−EX‖²/N). It also needs a moment-equivalence assumption.

The new mechanism has three parts:
- shifted-hinge exponential weights on a log-concave density, whose centroid mass contracts deterministically by Grünbaum's inequality;
- an expected log-loss bound for the target ball, which needs only second moments in a fixed direction;
- scalar median-of-means tournament selection.

**Proof ancestry.** Grünbaum's inequality and Prékopa–Leindler supply the geometry. Continuous exponential weights with hinge losses appear in Foster–Krishnamurthy (NeurIPS 2018). Neither gives an optimization rate.

**Search coverage.** I searched on 2026-10-29: arXiv, NeurIPS proceedings and the web, for follow-ups to MOSZ and for work on directional-variance SCO, heavy-tailed cutting planes and direction-dependent mean estimation. Semantic Scholar's citation API was rate-limited, so the list of forward citations is incomplete. Git history dates the result to the same day (commit 5c7e3c5). I did not verify the companion note's counterexample to the literal ISGO Theorem 1. It is irrelevant here, because the baseline row uses Cor. 3. The note's other claims are consistent with the Lean statement.

**Conclusion**

**Yes: the rate is unchanged, but it now holds under much weaker noise assumptions.** The strongest relevant baseline is Marsden–O'Carroll–Sidford–Zhang (NeurIPS 2025). They obtained the dimension-additive rate only when the noise has exponential tails in every direction. This theorem gets the same rate when the noise only has bounded variance in every direction:

| noise model | best previous bound | this result |
|---|---|---|
| directional exponential tails | Õ(d + σ²R²/ε²) | same order |
| directional variance ≤ σ²/d | Õ(d·σ²R²/ε² + d) (batched cutting plane), or (L²+σ²)R²/ε² (SGD) | Õ(d + σ²R²/ε²) |

On the newly covered instances, for example finite-variance Pareto-tailed noise, the noise term improves by roughly a factor of d over the batched cutting plane. It beats SGD when d·polylog ≪ L²R²/ε². It loses to SGD when d ≳ L²R²/ε², and it gives no gain for strongly anisotropic noise. It also does not resolve MOSZ's open problem for noise bounded only in trace, and its guarantee is information-theoretic (exact centroids).

The comparison establishes that this is a genuine relaxation of the assumptions, not a renaming. The straightforward ways of reducing the problem to MOSZ lose polynomial factors. Priority is only moderately established: the result dates from today, and I could not fully enumerate the papers that cite MOSZ. What can be claimed is the first checked dimension-additive, near-optimal stochastic subgradient complexity for convex Lipschitz minimization under directional second moments alone.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
