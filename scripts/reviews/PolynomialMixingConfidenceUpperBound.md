# Novelty assessment: PolynomialMixingConfidenceUpperBound

The [theorem](../../LongTails/Theorems/PolynomialMixingConfidenceUpperBound.lean) shows the following. Take a convex `f` on the ball `‖x‖ ≤ R` in `ℝ^d`. Each call returns one reply `g(x, Z_t)` from a single stationary real stream whose past–future β-mixing (absolute-regularity) coefficient at lag `t` is at most `(1+t/τ)^{-β}`. At each point, the stationary mean of the reply is a supporting subgradient and `E‖g‖^p ≤ G^p`. Under these assumptions the [selection algorithm](../../LongTails/Algorithms/PolynomialMixingSelection.lean) returns a point with `f(x̂) − min f ≤ ε` with probability at least `1−δ` ([setup](../../LongTails/Setups/PolynomialMixingSubgradient.lean)).

**Proved budget.** Here `a = p/(p−1)` and `L = log(8/δ)`. The bound holds for `1<p≤2`, `β>0`, `τ≥1`, `0<ε≤GR/8`, `0<δ≤1/32` and any `d≥1`:

$$N=O\Big(\tau L^2\Big[(2^{24}GR/\varepsilon)^{a(1+1/\beta)}+(L^2/\delta)^{1/\beta}\Big]\Big).$$

The constant `2^{24a(1+1/β)}` depends on `p` and `β` and is very large. The method must know `G, R, p, β, τ, ε, δ`. The output is the selected candidate. It is not the last iterate.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Standard reduction, same class: Berbee blocking + i.i.d. clipped SGD ([Liu–Zhou, arXiv 2303.12277 v3, Thm 3](https://arxiv.org/abs/2303.12277)). Raw moment gives centred moment ≤ 2G. Use `N₀=O((GRL/ε)^a)` samples with spacing `τ(2N₀/δ)^{1/β}`, so the coupling error is ≤ δ/2. | `τ(GRL/ε)^{a(1+1/β)}δ^{-1/β}` → `τL²[(2^{24}GR/ε)^{a(1+1/β)}+(L²/δ)^{1/β}]` | The product of the two time scales becomes a sum. The speedup is about `min{δ^{-1/β}L^{a(1+1/β)−2}, (GRL/ε)^{a(1+1/β)}L^{-2-2/β}}`, up to p,β-dependent constants. It is never worse by more than such constants. Example (`p=2, β=1`): `τ(GR/ε)^4L^4/δ` → `τL²[(GR/ε)^4+L²/δ]`. | None: same class | None | Both need all parameters. The certified constant `2^{24a(1+1/β)}` means the gain only shows up for very small δ unless the reduction's hidden constants are also large. |
| [Agarwal–Duchi, IEEE TIT 2013 / arXiv 1110.2529 v2, Thm 3](https://arxiv.org/abs/1110.2529) (β-mixing, online-to-batch with OGD). **Special case only:** per-sample convex losses with a.s. `‖g‖≤G`. | With `2β(k)GR/δ≤ε`: `τ(GR/ε)^{2+1/β}δ^{-1/β}·log(τGR/(εδ))` → (p=2) `τL²[(2^{24}GR/ε)^{2+2/β}+(L²/δ)^{1/β}]` | Better when `1/δ ≫ (GR/ε)L^{2β}`. **Worse** by up to `(GR/ε)^{1/β}` when `1/δ ≲ GR/ε`. | a.s. bounded, per-sample-Lipschitz replies → raw p-th moment only (heavy tails, unbounded features) | None (both are averaged-type outputs with high-probability accuracy) | Needs past–future β-mixing, which is stronger than A–D's single-slice weak β-mixing. Has a worse ε-exponent on the overlap. |
| [Duchi–Agarwal–Johansson–Jordan, arXiv 1105.4681 v3, Thm 2](https://arxiv.org/abs/1105.4681). **Special case only:** uniform conditional mixing (Assumption C) and a.s. Lipschitz samples (Assumption B). | `τ(GR/ε)^{2+1/β}log(τ(GR/ε)^{1/β}/δ)` → as above | **Worse** throughout that overlap, by at least `(GR/ε)^{1/β}L` | Uniform (φ-type) mixing → β-mixing, plus heavy tails | None | On their class the confidence cost is only logarithmic. |

**Reduction check and mechanism.** The direct reduction (Berbee coupling of every sample + an i.i.d. heavy-tailed method) gives only the product bound in row 1. Removing the product takes a two-scale design:

- short spacing gives constant-probability blocks;
- long spacing separates only `O(L²)` blocks;
- a gradient-only chord-quadrature score selects among candidates.

The scalar version of this two-scale idea is already in [Lerasle–Oliveira, arXiv 1112.3914 v1, Prop. 16](https://arxiv.org/abs/1112.3914). There, median-of-means is used with a `2Vβ_q` coupling penalty, under 4th moments and summable mixing. That is proof ancestry. Carrying it over to adaptive, nonsmooth, gradient-only optimization with raw p-th moments is the added step. Confidence boosting by candidate selection is also standard in the i.i.d. setting.

**Search coverage.** The search was run on 2026-11-18 UTC. It covered arXiv and the web for heavy-tailed, high-probability, Markov/mixing stochastic convex optimization. I read the theorem statements of Duchi et al., Agarwal–Duchi, Liu–Zhou and Lerasle–Oliveira. I did not read in detail Sarkar et al. ([arXiv 2606.26316](https://arxiv.org/abs/2606.26316); its setting is smooth PL objectives with geometric mixing) or Lovas–Tukora (arXiv 2610.15974, cited by the note for scalar median-of-means). The result entered local history in commit `673c14bb`.

The companion note's formula matches the Lean budget. Its comparison omits Agarwal–Duchi, which beats this bound on the bounded-gradient overlap when δ is moderate.

The repository's [AcceleratedHeavyTailedMarkovConvex](../../LongTails/Theorems/AcceleratedHeavyTailedMarkovConvex.lean) is not comparable. It covers expected gap for smooth unconstrained Markov problems. Converting it with Markov's inequality would cost `δ^{-a(1+1/β)}`.

**Conclusion**

**Yes, for heavy-tailed, polynomially β-mixing streams the proved high-confidence complexity beats the standard reduction by a polynomial factor.** The strongest applicable baseline I could build couples every sample to an i.i.d. copy and runs clipped SGD:

| | calls (constants depending on p, β suppressed) |
|---|---|
| reduction | `τ (GR log(1/δ)/ε)^{a(1+1/β)} · δ^{-1/β}` |
| this result | `τ log²(1/δ) [ (GR/ε)^{a(1+1/β)} + (log²(1/δ)/δ)^{1/β} ]` |

The accuracy and confidence costs now add instead of multiplying. The companion lower bound shows that both terms are necessary.

The gain is real but has limits. On the narrower class of a.s. bounded gradients, Agarwal–Duchi's β-mixing bound is better whenever `1/δ ≲ GR/ε`. Under uniform mixing, Duchi et al. are better everywhere. The certified constants are also enormous. Median-of-means blocking with an additive coupling penalty already exists for scalar estimation (Lerasle–Oliveira). What is new is carrying it over to adaptive, gradient-only, nonsmooth optimization.

My search found no earlier optimization result for this class. Two recent preprints were not checked in detail, so priority is not fully settled.

The contribution that can be claimed: the first checked high-confidence guarantee for this model in which the accuracy and confidence time scales add rather than multiply. It improves the standard reduction polynomially when both `GR/ε` and `1/δ` are large.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
