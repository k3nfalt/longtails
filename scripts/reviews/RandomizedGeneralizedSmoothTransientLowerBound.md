# Randomized initialization lower bound under (L₀,L₁)-smoothness

[`result`](../../LongTails/Theorems/RandomizedGeneralizedSmoothTransientLowerBound.lean) is a lower bound for the setup [`GeneralizedSmoothConvexTransient`](../../LongTails/Setups/GeneralizedSmoothConvexTransient.lean). It says that every randomized adaptive exact-gradient algorithm, with any number of queries `b ≤ ⌊L₁R/(4096 log(2+L₁R))⌋`, fails on some convex instance to reach `∫ f(output) − f(x*) ≤ ε`. The instance may depend on the algorithm and `b` but not on its seed, and `b = 0` is included. The instance satisfies `‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖` and `‖x⁰ − x*‖ ≤ R`. There is no bound on the initial gap or gradient, and no algorithm restriction.

**Necessary budget.** In the regime

`L₁R ≥ 2²⁰`, `L₀/L₁² ≤ ε ≤ L₀R²/16`, `d ≥ 2²⁰(1+L₁R)⁸e^{2√(L₁R)}`,

the bound is

`N_rand(ε) = Ω( L₁R / log(2 + L₁R) )` gradient calls.

Here L₀ and L₁ are the generalized-smoothness constants, R is the distance bound, ε is the expected accuracy and d is the dimension. The regime is nonempty: `valid_nonempty` gives an example, and the budget there is at least 18. The lower accuracy limit is equivalent to `√(L₀R²/ε) ≤ L₁R`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, [Descending Everest I](https://arxiv.org/abs/2610.21461), Thm 4.10 (arXiv v1 15 Oct 2026, v2 5 Nov 2026; prior, preprint) | Deterministic methods: `Ω(1 + √(L₀R²/ε) + L₁R/√log(2+L₁R))` → randomized methods: `Ω(L₁R/log(2+L₁R))` | Worse in the L₁R term, by a factor `√log(2+L₁R)`. There is no `√(L₀R²/ε)` term. | Deterministic algorithms → arbitrary randomized algorithms, judged by expected objective gap | None | Gradient-only oracle (Part I also allows function values). Dimension `e^{2√(L₁R)}` instead of about the budget size. Requires `ε ≥ L₀/L₁²` and `L₁R ≥ 2²⁰`. |
| Randomized smooth convex bound restricted to L₀-smooth functions (Woodworth–Srebro, [NeurIPS 2016](https://arxiv.org/abs/1605.08003), smooth case with n=1; repository [`SmoothConvexExpectedLowerBound`](../../LongTails/Theorems/SmoothConvexExpectedLowerBound.lean)). Special case only: L₁ = 0 functions. | `Ω(√(L₀R²/ε))` → `Ω(L₁R/log(2+L₁R))` | Larger exactly when `ε ≫ L₀log²(2+L₁R)/L₁²`. Example: at `ε = L₀R²/16`, O(1) → `Ω(L₁R/log(L₁R))` | Captures initialization hardness that is invisible to L₀-smooth instances | None | Restricted ε-interval and very large dimension. Close to `ε = L₀/L₁²` the baseline term can be larger. |
| Descending Everest II, [arXiv 2611.04171](https://arxiv.org/abs/2611.04171) v2 (5 Nov 2026), Thm 7.1 (prior, preprint). Restricted to finite sums with `n ≥ 2` and `L₁²R²δ/ε ≥ 3`. | Randomized component-oracle bound `≳ T₀/log²N₀` → not specialisable to n = 1 | Not comparable: n = 1 is excluded (δ = 0) | Finite sum → single exact-gradient objective | None | — |

**Gap to the upper bound.** The repository's [RadiusFreeSherpa bound](../../LongTails/Theorems/RadiusFreeGeneralizedAccelerated.lean) needs `O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R))` calls. It is deterministic, so it also holds for the expected criterion. In this regime it exceeds the lower bound by at most a factor `log²(2+L₁R)`. The deterministic gap in Part I is `log^{3/2}`.

**Standard-reduction check.** Neither Yao's principle applied to Part I's resisting oracle, nor a plain random rotation, reaches randomized algorithms directly. Unrestricted queries can locate hidden coordinates, so hiding the chain needs a convex radial "wall" whose gluing keeps the gradient-dependent curvature bound even though the peak gradients are exponentially large. That localization step ([`GeneralizedSmoothLocalization`](../../LongTails/Proofs/GeneralizedSmoothLocalization.lean)) is what this proof adds; I found no derivation of it elsewhere. Several parts are inherited proof ancestry rather than new:

- **Woodworth–Srebro and Carmon et al.:** the finite-family / random-embedding hiding argument for randomized lower bounds.
- **Part II:** the radial-localization architecture. Its localization estimate assumes a global Hessian bound and does not carry over here.
- **Chen et al., ICML 2023, Prop. 1:** the local gradient-growth estimate used for smoothing.

**Search coverage (13 Nov 2026).** I searched arXiv, NeurIPS, ICML and the general web for randomized and (L₀,L₁) lower bounds, and read the arXiv pages and partial HTML of Parts I and II. Theorem 4.10's preconditions and the full text of Part II §7 are known only through an extraction tool, not read verbatim. Liang–Luo ([2610.21692](https://arxiv.org/abs/2610.21692)) gives nonconvex stochastic stationarity bounds only. A NeurIPS 2026 listing by Shulgin–Sadiev appears to give deterministic nonconvex bounds; its page returned an error and I did not verify it. The theorem was introduced in commit `0ed1e4a6` on 13 Nov 2026, after both Everest preprints. The companion note's description of these comparisons matches what I could check.

**Conclusion**

**Yes: this is the first randomized lower bound I found for the initialization cost of exact-gradient convex (L₀,L₁)-smooth optimization, but its rate is slightly weaker than the deterministic one.**

The strongest prior lower bound is Descending Everest I, Theorem 4.10. It covers only deterministic methods, though it allows value and gradient queries:

| | algorithms | L₁R term |
|---|---|---|
| Everest I | deterministic | `L₁R/√log(2+L₁R)` |
| this result | randomized | `L₁R/log(2+L₁R)` |

The bound holds for `L₀/L₁² ≤ ε ≤ L₀R²/16`, `L₁R ≥ 2²⁰` and dimension at least `e^{2√(L₁R)}`. The previous randomized bound, `√(L₀R²/ε)`, can be O(1) in this regime. With the deterministic upper bound `O(√(L₀R²/ε) + L₁R·log(L₁R))`, the result shows that randomization cannot remove the nearly linear L₁R initialization cost, up to two logarithms.

The gain is in the algorithm class: deterministic → randomized. The losses are a `√log(L₁R)` factor, gradient-only queries, an exponential dimension requirement and a restricted accuracy interval. The key step, a convex localization that keeps the generalized curvature bound despite exponentially large gradients, is not a routine corollary as far as I checked. Priority rests on a one-month-old literature and two partly read preprints.

The contribution that can be claimed is randomized gradient-only hardness of order `L₁R/log(L₁R)` for this class, matching the known upper bound up to `log²(L₁R)`.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
