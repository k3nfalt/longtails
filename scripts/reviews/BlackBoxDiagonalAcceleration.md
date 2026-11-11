# Black-box accelerated adaptivity to an unknown diagonal preconditioner

[`result`](../../LongTails/Theorems/BlackBoxDiagonalAcceleration.lean) proves the following. Let `f` on `ℝ^d` satisfy `(μ/2)‖y−x‖²_w ≤ f(y)−f(x)−⟨∇f(x),y−x⟩ ≤ ½‖y−x‖²_w` for hidden weights `w > 0` and a hidden `μ ∈ (0,1]`. The algorithm ([setup](../../LongTails/Setups/DiagonalSmoothStronglyConvexBlackBox.lean), [algorithm](../../LongTails/Algorithms/BlackBoxDiagonalAccelerated.lean)) receives only `d` and `x0`, plus exact `(f,∇f)` calls. After any `K ≥ budget` calls, its last certified base point satisfies `f(x̂)−f⋆ ≤ ε` deterministically.

**Complexity.** `μ` is the relative strong-convexity constant, so `κ⋆ = 1/μ`. `Δ ≥ f(x0)−f⋆` is the initial gap, and smoothness is normalized into `w`. The budget `d+1+⌈21√(2/μ)(log(1+Δ/(μ²ε)) + (d+1)(3+log₂(1/μ))⁴)⌉` gives

  `O( d + μ^{-1/2} log(1 + Δ/(μ²ε)) + d μ^{-1/2} (1+log(1/μ))⁴ )`.

At `μ = 1` this is `O(d + log(1+Δ/ε))`. Neither `μ`, `w`, `Δ`, `ε` nor `f⋆` enters the updates. They enter only the budget, which is an anytime bound, not a stopping certificate.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Multidimensional backtracking: Kunstner–Portella–Schmidt–Harvey, [NeurIPS 2023](https://arxiv.org/abs/2306.02527), Prop. 3.2 + Thm 5.3 (ellipsoid). The total is my composition; the paper states none. | `O(√d μ^{-1} log(Δ/ε) + d log(L/α₀))` → `O(d + μ^{-1/2}log(1+Δ/(μ²ε)) + dμ^{-1/2}log⁴(1/μ))` | Leading term improves by a factor `√(dκ⋆)` once `log(Δ/ε) ≳ √(d/κ⋆)·log⁴κ⋆`. | Restricted to twice-differentiable `f`; the selected setup needs only differentiability. | Known `α₀` with `P⋆ ∈ S₀` → no initial set (secant probes) | Warm-up `dμ^{-1/2}log⁴(1/μ)` versus `d log(L/α₀)`. `L/α₀` is not expressible in setup parameters. Extra `log κ⋆²` inside the main log. |
| OSGM-R: Gao–Chu–Ye–Udell, [Part I v2](https://arxiv.org/abs/2505.23081), Thm 6.2 (COLT 2025 version [2411.01803](https://arxiv.org/abs/2411.01803)) | `O(κ⋆L²‖P¹−P̂‖²_F + κ⋆ log(Δ/ε))`, with `f⋆` and `L` known; per §6.1, the `f⋆`-free outer loop gives `O(κ⋆ log²(1/ε))` → same as above | `√κ⋆` gain in the leading term once `log(Δ/ε) ≳ d log⁴κ⋆/√κ⋆`. The regret term is unbounded in the setup parameters. | None on the overlap, which is diagonal `𝒫`. OSGM also allows full-matrix `𝒫`, so its scope is wider. | Known `f⋆` and `L` → only `(f,∇f)` | OSGM has no `d`-dependent warm-up. |
| Centre of gravity on the secant ellipsoid `{‖x−x0‖_J ≤ ‖∇f(x0)‖_{J⁻¹}/μ}`: [Bubeck 2015](https://arxiv.org/abs/1405.4980), Thm 2.1. This is my reduction (`J ≤ w ≤ J/μ`). | `O(d log(1+Δ/(μ⁴ε)))`, best queried point, `μ` known → same as above | Better only if `d ≫ √κ⋆` **and** `log(Δ/ε) ≫ √κ⋆ log⁴κ⋆`. Worse whenever `d ≲ √κ⋆`. | None | Known `μ` (radius) → unknown. A parameter-free radius-doubling variant was not checked. | Cutting-plane steps need poly(d) or intractable arithmetic; oracle units are the same. |
| Repository [`OnlineMetricAccelerated`](../../LongTails/Theorems/OnlineMetricAccelerated.lean), 2026-10-15 | `O(d + log(Δ/ε)(√κ⋆+log d) + d³log²d·log κ⋆·√κ⋆)` → same as above | Warm-up `d³log²d·logκ⋆` → `d log⁴κ⋆` (times `√κ⋆`). This gains only if `d²log²d ≳ log³κ⋆`. | None | Known `f⋆` → not needed | Extra `log κ⋆²` in the main log; worse when `d` is tiny and `κ⋆` is huge. |

**Reduction check.** Secant probes give `J ≤ w ≤ J/μ`, so AGD in the `J`-metric sees a condition number of at most `κ⋆²`. With known `μ` this gives `O(d+κ⋆log(1+Δ/ε))`, which is no better than the rows above. Composing known theorems therefore does not yield `√κ⋆ log(1/ε)`. The new mechanism is twofold:
- an accelerated phase certificate that uses only queried points (no `x⋆` and no `f⋆`), whose violated inequalities are convex in the log-scale metric;
- perceptron-type cuts on both the smoothness and strong-convexity sides, combined with doubling of the `κ⋆` guess.

Nesterov's estimate sequence and Kunstner et al.'s cut-based search are proof ancestry, not the complexity source. Only the doubling/restart pattern is standard.

**Search coverage (2026-11-09).** I searched arXiv and NeurIPS/COLT proceedings for accelerated diagonal or online-scaling methods, read the theorems of Kunstner et al. and OSGM Parts I–II, and checked for 2024–2026 follow-ups. I did not run a full citation-graph traversal. OSGM Part II v2 ([2509.11007](https://arxiv.org/abs/2509.11007), §5.3, Question 3; 6 Oct 2025) poses `O(√κ⋆ log(1/ε))` as open even with `f⋆`, and says black-box access "remains unclear"; Part II itself gives no proof of a √κ⋆ guarantee. I found no work achieving this before the result was introduced (commit `a5230a06`, 2026-11-09), and no later work. **Mismatch with the companion note:** it says the bound "matches the Nesterov lower bound" when `d ≳ √κ⋆ log(1/ε)`. In that regime, however, the warm-up `d√κ⋆log⁴κ⋆ ≥ κ⋆log(1/ε)log⁴κ⋆` dominates, so only the ε-dependent term matches. I did not run the Lean build or the comparator.

## Conclusion

**Yes. In a high-accuracy, moderate-dimension regime, the proved total complexity beats every checked applicable method, using only `(f,∇f)` access.** The strongest baselines are cutting planes on the secant ellipsoid and secant-metric AGD (both with `μ` known), plus Kunstner et al.'s backtracking and OSGM (`f⋆` known).

| | calls (`L_ε = log(Δ/ε)`) |
|---|---|
| this result | `√κ⋆ L_ε + d√κ⋆ log⁴κ⋆` |
| best checked prior | `min(d L_ε, κ⋆ L_ε, √d κ⋆ L_ε)` |

The gain needs `√κ⋆ ≪ d ≪ √κ⋆ L_ε / log⁴κ⋆`. For example, `d = L_ε = κ⋆` gives a speedup of order `√κ⋆/log⁴κ⋆`. The result loses to cutting planes when `d ≲ √κ⋆` or the accuracy is modest, and loses to `J`-metric AGD when the warm-up dominates.

The comparison establishes this gain. Priority rests on a literature search that found the black-box question explicitly posed as open in OSGM Part II and no answer to it. That search cannot rule out unindexed work, and a parameter-free cutting-plane variant remains unchecked; it would only matter for `d ≲ √κ⋆`. The contribution that can be claimed is the first black-box first-order method whose ε-dependent cost is accelerated and dimension-free with respect to the unknown optimal diagonal preconditioner, at the price of a large `d√κ⋆ log⁴κ⋆` warm-up.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
