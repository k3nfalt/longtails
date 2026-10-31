# Novelty assessment: MonotoneHessianSecondOrder

The [theorem](../../LongTails/Theorems/MonotoneHessianSecondOrder.lean) runs the [monotone Hessian-reuse algorithm](../../LongTails/Algorithms/MonotoneHessianReuse.lean) through `execute`. For every C² function on a finite-dimensional real Hilbert space with an H-Lipschitz Hessian and `f(x₀) − inf f ≤ Δ` ([setup](../../LongTails/Setups/HessianLipschitzSecondOrder.lean)), it uses exact `(f, ∇f)` and exact full-Hessian oracles. With probability at least `1 − ρ`, the returned point `y` satisfies **both** `‖∇f(y)‖ ≤ ε` and `∇²f(y) ≽ −√(Hε) I`.

**Complexity.** Here d is the dimension and m ≥ 1 is the cost of one Hessian in units of ordinary calls. The Lean spec counts the two channels separately, and m enters only through the budgets. The proved budgets are `G = O(m^{1/3}(1+Δ√H/ε^{3/2}) log²(2+(d+1)m(1+Δ√H/ε^{3/2})/ρ))` ordinary calls and `J = O(1 + Δ√H/(m^{2/3}ε^{3/2}))` Hessian calls. The weighted total is therefore

  G + mJ = O( m + m^{1/3}(1 + Δ√H ε^{−3/2}) · log²(2 + (d+1) m (1 + Δ√H ε^{−3/2}) / ρ) ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fresh cubic regularization, [Nesterov–Polyak 2006](https://link.springer.com/article/10.1007/s10107-006-0706-8), global rate for the same-point measure μ (Sec. 3, Thm 1; recalled, not re-read here). Direct competitor. | O((m+1)(1+Δ√Hε^{−3/2})) → O(m + m^{1/3}(1+Δ√Hε^{−3/2})·log²(…)) | Factor ≈ m^{2/3}/log² when Δ√Hε^{−3/2} ≥ 1 and m^{2/3} ≫ log²(2+(d+1)m(1+Δ√Hε^{−3/2})/ρ). Same order when Δ√H ≲ ε^{3/2}. | None (same class) | None (both give same-point SOSP) | Holds with probability 1−ρ, not deterministically; adds a log² factor depending on d and ρ. Worse by log² when m = O(1). |
| Lazy cubic Newton, [Doikov–Chayti–Jaggi, ICML 2023](https://proceedings.mlr.press/v202/doikov23a.html), Thm 3.1 / Cor. 3.7, eq. (15). Direct competitor with a weaker certificate. | Its headline O(m + √m·Δ√Hε^{−3/2}) bounds min‖∇f‖ and min ξ separately, with curvature only −O(√(mHε)). Forcing curvature to √(Hε) needs ≈ m²Δ√Hε^{−3/2} iterations, i.e. O(m²(1+Δ√Hε^{−3/2})) weighted → this result | Factor ≈ m^{5/3}/log² on the matched criterion (same regime as above) | None | Separately indexed minima with an m-inflated curvature bound → one point certifying both conditions | Probabilistic; extra log² |
| [Adil–Bullins–Sidford–Zhang, NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/3dc910c921507a5d51d3dac0202b2618-Abstract-Conference.html) ([arXiv 2510.20786v1](https://arxiv.org/abs/2510.20786)), Thm 3 / Cor. 2 (no L₁). **Weaker criterion only.** | With n_H = ⌈Δ√H/(m^{2/3}ε^{3/2})⌉ Hessians: Õ(m + m^{1/3}Δ√Hε^{−3/2}) with log¹⁸ factors, for first-order ε-critical points only → same powers for SOSP | None in powers (log² vs log¹⁸) | None | ε-critical point → same-point (ε, √(Hε))-SOSP | Its result is deterministic and requires S ≥ 1; this one is probabilistic |
| [Chen–Liu–Luo–Zhang, COLT 2026](https://proceedings.mlr.press/v336/chen26a.html) ([arXiv 2501.17488v3](https://arxiv.org/abs/2501.17488), Jul 13 2026), Thm 4.1 (NALEN). **Weaker criterion only.** | O(m + m^{1/3}Δ√Hε^{−3/2}), FOSP, best block-average point → O(m + m^{1/3}(…)log²(…)) SOSP | Worse by log² on the first-order criterion | None | FOSP → same-point SOSP | It is deterministic and log-free |

**Standard-reduction check and proof ancestry.** The obvious composition fails to give the result. One would run Adil/NALEN to an ε-critical point, buy a fresh Hessian to test curvature, and escape if the test fails. That can take Θ(Δ√Hε^{−3/2}) escapes, each costing at least m, so the total is O(m(1+Δ√Hε^{−3/2})): no gain over fresh cubic. Doikov et al.'s guarantee cannot be rescaled to the matched criterion cheaply either (row 2). The note's mechanism addresses this. Curvature is tested on the stale-Hessian metric B with a Chebyshev filter of degree about m^{1/3}, built from gradient finite differences, which needs no global L. A monotone correction step comes before the test, so both certificates apply to the returned point. Proof ancestry: Carmon et al.'s convex-until-proven-guilty and NEON2's Chebyshev detection provide ingredients, not this bound.

Two competitors remain outside the table. First, a gradient-only alternative: finite-difference Hessians cost d+1 calls and their error is controlled by H alone. With inexact-Hessian cubic regularization this suggests O((d+1)(1+Δ√Hε^{−3/2})). That is a reduction sketch whose source theorem I did not re-verify. If it holds, the gain needs m^{1/3}log² ≪ d as well. Second, on the extra L-smooth overlap, accelerated SOSP methods (Carmon et al. 2018, cited by the note) were not re-read.

**Search coverage.** I searched on 2026-10-25 UTC: arXiv, NeurIPS, PMLR (ICML/COLT), the lazy-Hessian line, and the Chayti–Jaggi asynchronous-curvature preprint (v4, Oct 2026; its abstract states first-order guarantees only). I read the theorem text of Adil et al., Chen et al., and Doikov et al. Nesterov–Polyak was not re-read (paywalled). The result entered the repository in commit 17654b9 (2026-10-25 22:08 UTC), so all baselines are prior. The note's citations and venues check out (NeurIPS 2025 and COLT 2026 confirmed). It also correctly concedes that the method loses to dimension-based simulation when m is large and d is small. I ran no build or axiom audit.

**Conclusion**

**Yes: for same-point second-order stationarity on the plain Hessian-Lipschitz class, the proved weighted cost beats fresh cubic regularization by about m^{2/3}.**

The strongest applicable full-class baseline is Nesterov–Polyak cubic regularization. With S = Δ√H/ε^{3/2}:

| | weighted oracle cost | guarantee |
|---|---|---|
| fresh cubic | O(m(1+S)) | deterministic SOSP |
| this result | O(m + m^{1/3}(1+S)·log²(2+(d+1)m(1+S)/ρ)) | SOSP w.p. 1−ρ |

The gain survives when S ≥ 1 and m^{2/3} exceeds the log² term. Example: d ≥ m, S = m, ρ = 1/m gives O(m^{4/3}log²m) versus O(m²). It loses by log² when m is small or S ≲ 1. It is only probabilistic. If the finite-difference reduction holds, it is beaten whenever d ≲ m^{1/3}log².

The m^{1/3} powers were already known for first-order points (Adil et al.; Chen et al., without logs). What is new is reaching them for the stronger, matched second-order criterion. The naive "first-order method plus fresh-Hessian escape" composition provably costs O(m(1+S)), so the result is not a routine corollary. Priority beyond the searched literature is not established, the inexact-Hessian alternative was not fully verified, and I did not check the Lean proof.

The claimable contribution: first-order lazy-Hessian query complexity extended to same-point (ε, √(Hε))-second-order stationarity, at an extra log² and failure-probability cost.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
