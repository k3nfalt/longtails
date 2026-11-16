# Gap-sensitive randomized lower bound for convex (L₀,L₁)-smooth optimization

This theorem is a lower bound. For every valid parameter tuple and every randomized algorithm that only has exact-gradient access, and at every query budget up to the stated one, the theorem constructs a seed-independent convex instance. That instance satisfies ‖D∇f‖ ≤ L₀ + L₁‖∇f‖, ‖x₀ − x⋆‖ ≤ R and f(x₀) − f⋆ ≤ Δ, and on it the output's expected gap 𝔼[f(x̂) − f⋆] is not at most ε (or the loss is not integrable). Sources: [theorem](../../LongTails/Theorems/GapGeneralizedSmoothConvexLowerBound.lean), [setup](../../LongTails/Setups/GapGeneralizedSmoothConvex.lean) (which reuses the admissibility predicate of [GeneralizedSmoothAndConvex](../../LongTails/Setups/GeneralizedSmoothAndConvex.lean)), and [template](../../LongTails/TemplateLowerBound.lean). No algorithm is constructed and `allowedAlgorithm` is unrestricted.

**Proved necessary budget.** In terms of the original parameters:

$$
N \ \ge\ 2^{-24}\Big[\sqrt{L_0R^2/\varepsilon}+\min\Big\{\tfrac{L_1R}{1+\log(2+L_1R)},\ \Big(\tfrac{L_1R\,\log(\Delta/(8\varepsilon))}{1+\log(2+L_1R)}\Big)^{2/3}\Big\}\Big]
$$

The bound is the floor of this expression. The parameters are:
- L₀ and L₁ are the smoothness constants.
- R bounds the initial distance to x⋆.
- Δ bounds the initial gap.
- ε is the target expected accuracy.

The theorem requires L₀, R, ε > 0, L₁ ≥ 0, ε ≤ L₀R²/16, Δ ≥ 16ε, and dimension d ≥ ⌈2⁸⁰(1 + L₁R + √(L₀R²/ε))¹⁰⌉. The case split (zero queries, a smooth chain, and a calibrated transient chain) is checked in `GapBudget.cases`. A nonempty instance with L₁ = 0 is checked in `GapBudget.valid_nonempty`.

Notation: s = √(L₀R²/ε), q = L₁R, w = 1 + log(2+q), h = log(Δ/(8ε)).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, [Descending Everest I](https://arxiv.org/abs/2610.21461), Thm B.3 (v1 Oct 15, v2 Nov 5 2026, preprint). Class f(0) − f⋆ ≤ 4ε, which is nested in every Δ ≥ 4ε class. | Ω(s + (q/log(2+q²/s²))^{2/3}) for every Δ ≥ 4ε → Ω(s + min{q/w, (qh/w)^{2/3}}) | The lower bound gains a factor h^{2/3}, up to powers of w, when (qh)^{2/3} ≫ s and polylog(q) ≪ h ≤ √(q/w). The gain is polynomial in q only when Δ/ε ≥ e^{q^β} with 0 < β < 1/2, for example Ω(q^{2/3}) → Ω(q^{2(1+β)/3}/w^{2/3}). When Δ/ε ≤ poly(q), the gain is only log^{2/3}(Δ/ε). None when s dominates. | Δ = 4ε only → every Δ ≥ 16ε (the open intermediate-gap regime) | Algorithm class: deterministic → randomized. Same expected-gap criterion. | Their oracle also returns f-values; this proof covers gradients only. Their dimension is 2n; this one needs ≈2⁸⁰(1+q+s)¹⁰. The constant 2⁻²⁴ is weaker than their 1/12. |
| Same paper, Thm 4.10, radius-only class, deterministic. | Ω(s + q/√log(2+q)), but only when Δ exceeds the hard instances' gap, roughly (L₀/L₁²)e^{Θ(q)} → Ω(s + q/w) there | Worse by a factor √w in that regime | None | Deterministic → randomized | Gradients only; large dimension |
| Prior randomized, gradient-only bounds: smooth Ω(s) ([Woodworth–Srebro](https://arxiv.org/abs/1709.03594); repo `SmoothConvexExpectedLowerBound`), and repo [FullGeneralizedSmoothConvexLowerBound](../../LongTails/Theorems/FullGeneralizedSmoothConvexLowerBound.lean), Ω(s + q/log(2+q)) for the radius-only class (huge Δ only) | For moderate Δ only Ω(s) was known → Ω(s + min{q/w, (qh/w)^{2/3}}) | Gains an additive (qh/w)^{2/3} term whenever it exceeds s, including at constant gap | Bounded-gap classes are now covered for randomized methods | None | Same oracle; a larger dimension exponent (10 vs 5) |

**Upper-bound gap.** The prior upper bound for this class is Everest I, Thm B.7(b). From its Table 1, it is O(log(2+s²+q)·[1 + s + q^{2/3}log^{2/3}(2Δ/ε)]); I did not read the theorem itself. The repository's existing gap-sensitive and radius-only accelerated methods give O(s + min{(qh)^{2/3} + h, (1+q)w}). Checking the regimes h ≤ √q and h ≥ √q separately (for q ≥ 1) shows that the upper/lower ratio is O(w²), uniformly in Δ. So the Δ-dependence is now determined up to log²(2+L₁R) factors for gradient-only methods. For deterministic methods with value queries and intermediate gaps it remains open.

**Reduction check and proof ancestry.** The bound does not follow from known results by any of these routes:
- Restricting to a subclass recovers only the endpoints.
- Rescaling a constant-gap chain keeps Δ/ε fixed.
- Restarting or composing chains in stages gives only about q^{2/3}h^{1/3}.

The hard instance is Everest's mechanism (conjugates of strongly convex functions on a polytope, arranged in chains) with a tuned geometric spacing t = min{m^{-1/2}, h/(2m)} and a common shift. Randomized hiding comes from the Carmon et al. / Woodworth–Srebro style embedding already in this repository. The new step is calibrating the gap, radius and curvature constraints at the same time (16384·m·w ≤ q and 32768·m^{3/2}·w ≤ qh). I did not find this calibration in either Everest paper.

**Search coverage (2026-11-14 UTC).**
- **What I checked.** I read Everest Part I v2: §5 verbatim, the Thm B.3 formula verbatim, and B.7(b) only through Table 1. I also read Part II ([2611.04171](https://arxiv.org/abs/2611.04171), v2 Nov 5 2026). Its randomized finite-sum lower bound is Δ-independent and lists the optimal Δ-dependence as an open question. I searched arXiv and the web for later lower bounds or a Part III and found none.
- **What Everest says.** Part I §5 states: "A matching lower bound in terms of the dependence on Δ is unknown." It also says its lower bounds are deterministic only.
- **Chronology.** The result was committed on 2026-11-14, after both preprints.
- **Companion note.** Its citations and claims match what I checked.
- **Not checked.** The full text of Thm B.7 and the TeX source were inaccessible to me.

**Conclusion**

**Yes: it proves a lower bound for bounded-gap classes that the strongest prior work explicitly left open.** The strongest baseline is Everest I. Its deterministic bounds cover only the constant-gap endpoint, Δ = 4ε, and the radius-only endpoint, which requires an exponentially large gap.

| Regime | Previous lower bound | This result | Upper bound |
|---|---|---|---|
| Δ ≥ 16ε | Ω(s + (q/log)^{2/3}) (deterministic) | Ω(s + min{q/w, (qh/w)^{2/3}}) (randomized) | O(s + min{(qh)^{2/3} + h, qw}) |

Here s = √(L₀R²/ε), q = L₁R, h = log(Δ/(8ε)) and w = 1 + log(2+L₁R). The new bound matches the upper bound up to a factor of order log²(2+L₁R), uniformly in Δ. As a side effect, it also gives the first randomized version of the (L₁R)^{2/3} constant-gap bound.

The gain over the prior lower bound is a factor log^{2/3}(Δ/ε), up to log(L₁R) factors, and it matters only when that term exceeds s. It becomes polynomial in L₁R only for very large gaps, for example Δ/ε ≈ e^{(L₁R)^β} with β < 1/2. When Δ/ε is polynomial in L₁R, the result pins down a logarithmic dependence rather than an exponent. Compared with Everest, it gives up value queries, a small dimension, and good constants. Where Thm 4.10 applies, it is weaker by √log.

The comparison establishes that the bound is stronger than every prior bound I checked. My literature search found no earlier gap-dependent lower bound, but that search covers only a few weeks of very recent preprints. What can be claimed is a near-tight characterization of how the initial gap affects the complexity, for randomized gradient-only methods, built by adapting Everest's chain construction.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
