# ComparisonTrustAccelerated: novelty assessment

[`result`](../../LongTails/Theorems/ComparisonTrustAccelerated.lean) proves the following. Let `f` on a finite-dimensional real inner-product space `E` (`n = dim E`) be C², with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian and `f(x₀) − inf f ≤ Δ`. Using only the exact comparison bits `[f(x) ≤ f(y)]`, a deterministic algorithm outputs a list of *visited* points that contains, on every run, a point with `‖∇f‖ ≤ ε`. See the [setup](../../LongTails/Setups/ComparisonHessianLipschitz.lean) and the [algorithm](../../LongTails/Algorithms/ComparisonTrustRegion.lean). The setup's `allowedAlgorithm` only requires that outputs be visited points.

**Complexity.** This comes from the Lean `budget`, with constants dropped:

  `O( (1 + Δ√ρ ε^{-3/2}) · (n+1) · (1 + L^{1/2}(ρε)^{-1/4}) · log³(2 + n + L/√(ρε) + √(LΔ)/ε) )` comparisons.

Here `L` and `ρ` are the gradient and Hessian Lipschitz constants, `Δ` is the initial gap and `ε` is the target gradient norm. When `L ≥ √(ρε)`, the bound is `Õ(n Δ L^{1/2} ρ^{1/4} ε^{-7/4})`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Wang–Zhang–Tao–Zhang–Li, [arXiv:2606.27082](https://arxiv.org/abs/2606.27082) v1 (25 Jun 2026, ICML 2026), Thm 8 / Thm 1. **Prior** (the commit is from 2 Nov 2026). Same class, same comparison oracle. | `Õ(Δ√ρ n² ε^{-3/2})` → `Õ(Δ√ρ ε^{-3/2} · n · (1 + (L²/(ρε))^{1/4}))` | Saves a factor `n / (1 + (L²/(ρε))^{1/4})` up to logs. It gains when `n ≫ (1 + (L²/(ρε))^{1/4}) log³(·)` and is **worse** when `n ≲ (L²/(ρε))^{1/4}`. | None (identical class) | Success probability 2/3 → deterministic, every run. Both use the "visits" criterion. | The baseline visits an **ε-second-order** point (`λ_min ≥ −√(ρε)`). This result gives first order only. The baseline has `L` only inside logs; this result has a `L^{1/2}` factor. |
| Zhang–Li, [arXiv:2405.11454](https://arxiv.org/abs/2405.11454) v1 (May 2024; now Tao et al., ICML 2026). Nonconvex result as stated in the abstract (theorem not checked). Also STP (Bergou–Gorbunov–Richtárik), `O(nLΔ/ε²)`, in expectation. | `Õ(nLΔ ε^{-2})` → `Õ(nΔ L^{1/2}ρ^{1/4} ε^{-7/4})` | Factor `(L²/(ρε))^{1/4}`, for every `n`, when `ε ≪ L²/ρ`. Worse when `ε ≳ L²/ρ` (constants and log³). | Needs a Lipschitz Hessian (`ρ`), which these baselines do not require. | Expectation/probabilistic → deterministic (STP) | The extra assumption `ρ < ∞`. |
| Repository: `ComparisonSmoothConvex` | Not comparable: convex objective-gap problem | — | Convex → nonconvex with Lipschitz Hessian (incomparable classes) | — | — |

Against the best of the two prior bounds, `min(nLΔ/ε², n²Δ√ρ/ε^{3/2})`, the result wins exactly when both `ε ≪ L²/ρ` and `n ≫ (L²/(ρε))^{1/4}` hold, up to logs. Example: take `L = ρ = Δ = 1` and `n = ε^{-1/2}`. Both prior bounds are `ε^{-5/2}`, while this result gives `Õ(ε^{-9/4})`.

**Reduction check.** There is no direct composition. Comparisons give no function values, so finite-difference gradients are unavailable. They also reveal only the scaled quantities `∇f/‖∇f‖` and `H/‖∇f‖`. Combining the `O(n log)` normalized-gradient estimator with a Hessian-vector-product `ε^{-7/4}` method (CDHS's regularizer `γ‖s‖²`, capped CG) breaks, because those methods use absolute scales. The new mechanism has three parts:
- a scale-free Hessian-vector-product estimate, with a ternary search for the one non-identifiable radial curvature;
- a `log(√(LΔ)/ε)` grid of gradient-scale guesses, selected by a comparison tournament;
- a guarded inexact AGD with computable Rayleigh certificates.

Proof ancestry: Carmon–Duchi–Hinder–Sidford ("Convex until proven guilty", ICML 2017) supplies the regularized-model AGD with its negative-curvature certificate. Tao et al. supply the sign-test gradient-direction estimation. 2606.27082 supplies the normalized-Hessian and candidate-tournament template. The scale-guess adaptation is the step this result adds.

**Search coverage.** I searched on 2 Nov 2026 (UTC): arXiv and proceedings searches for comparison, order, ranking and dueling oracles in nonconvex settings, the theorem statements of 2606.27082 (read from the PDF), the 2405.11454 abstracts (v1 and v3), and Lobanov–Gasnikov–Krasnov (NeurIPS 2024). The last is an order-oracle paper whose acceleration is for strongly convex problems; I did not verify its nonconvex theorems. I found no comparison-oracle `ε^{-7/4}` result. I did not check the companion note's value-oracle `Õ(nε^{-7/4})` claim or its arXiv:2606.05438 optimality citation. **Mismatch with the note:** its table does not say that 2606.27082 Thm 8 guarantees an ε-*second-order* point with no polynomial `L` dependence. Its claim to have "answered negatively" the `n²` question holds only for first-order stationarity, and only when `n ≳ (L²/(ρε))^{1/4}`.

**Conclusion**

**Yes: in high dimension, it has better proved total complexity for finding an ε-stationary point from comparisons alone.** The strongest baseline is Wang et al. (2606.27082, Thm 8), on the identical class and oracle:

| | comparisons |
|---|---|
| Wang et al. 2026 | `Õ(Δ√ρ n² ε^{-3/2})`, probability 2/3 |
| This result | `Õ(Δ√ρ ε^{-3/2} n (1 + (L²/(ρε))^{1/4}))`, deterministic |

The gain is a factor of about `n/(L²/(ρε))^{1/4}`, so it requires `n ≫ (L²/(ρε))^{1/4}` beyond the log³ factor. Combined with the `nLΔ/ε²` normalized-descent bound, it is a polynomial improvement when `ε ≪ L²/ρ` and the dimension is large, for example `ε^{-9/4}` versus `ε^{-5/2}`. In low dimension the `n²` method remains better, and it also certifies second-order stationarity, which this result does not.

The comparison establishes the gain. The literature search found no earlier comparison-oracle `ε^{-7/4}` method, but this is a fast-moving 2026 area, and absence from my search does not prove priority. The technical step that makes the gain possible is turning absolute-scale acceleration into a scale-free method. It is not a routine composition.

What can be claimed: the first (as far as I found) deterministic comparison-only method with `n·ε^{-7/4}` first-order complexity under Lipschitz Hessians. It improves the best prior bounds in the high-dimensional, small-ε regime, at the cost of second-order guarantees.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
