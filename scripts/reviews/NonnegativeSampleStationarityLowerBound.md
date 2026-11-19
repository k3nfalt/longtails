# NonnegativeSampleStationarityLowerBound: what is actually new?

[`result`](../../LongTails/Theorems/NonnegativeSampleStationarityLowerBound.lean) proves the following in the [Euclidean setup](../../LongTails/Setups/NonnegativeSmoothSampleLossEuclidean.lean), which specializes the [general setup](../../LongTails/Setups/NonnegativeSmoothSampleLoss.lean). Assume `L, Δ, ε > 0` and `2³²ε ≤ √(LΔ)`. Let `A` be any randomized adaptive algorithm; there is no `allowedAlgorithm` restriction. Each call queries two points and returns gradients only, from one fresh uniform sample. Then for every budget `b ≤ ⌊√(LΔ)/(2³²ε)⌋³` there is a hard instance on which `A` fails. Each sample loss is nonnegative with an `L`-Lipschitz gradient, the risk satisfies `F(0) ≤ Δ`, and failure means `E‖∇F(x̂)‖ > ε`. The instance depends on `A` and `b` but not on the realized seed ([construction](../../LongTails/Proofs/SampleLossLowerBound.lean)).

**Necessary budget.** Write `L` for the per-sample smoothness constant, `Δ` for the initial *risk* `F(x₀)` (not the gap), and `ε` for the target expected gradient norm. For `LΔ/ε² ≥ 2⁶⁴`:

  `N ≥ ⌊√(LΔ)/(2³²ε)⌋³ + 1 = Ω((LΔ)^{3/2}/ε³)`, with constant about `2⁻⁹⁶`.

The construction uses `m = (512(n+1))²` samples and dimension `Θ(n¹¹)`, where `n = ⌊√(LΔ)/(2³²ε)⌋`. The [companion upper bound](../../LongTails/Theorems/NonnegativeSampleStationarity.lean) is `⌈8192(1+LΔ/ε²)^{3/2}⌉` pair calls (normalized STORM). The two bounds match up to a universal factor of about `2¹⁰⁹`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani et al., [arXiv 1912.02365](https://arxiv.org/abs/1912.02365) v2 (Feb 2022; Math. Program. 2023), Thm. 3, eq. (24). *Its hard oracle is only mean-squared smooth (Lemma 8) with bounded variance. It is not in the target class.* | `Ω(ΔL̄σ/ε³ + σ²/ε²)`; substituting `σ² ≍ LΔ` formally gives `Ω((LΔ)^{3/2}/ε³)` → `Ω((LΔ)^{3/2}/ε³)` | None: same order. Their bound does not apply to the target class. | MSS oracle with bounded variance and gap `Δ` → individually `L`-smooth, nonnegative sample losses with risk `F(0) ≤ Δ`. The new hard class is a much smaller class. Arjevani et al., §6, call extending to per-sample smoothness "non-trivial." | None (both use expected gradient norm) | Here the oracle returns only gradients, not values, so it is weaker than theirs. Requires `LΔ/ε² ≥ 2⁶⁴` and dimension `n¹¹`. |
| Peng–Tang–Jia, [arXiv 2609.00045](https://arxiv.org/abs/2609.00045) v1–v3 (30 Aug–10 Oct 2026, preprint, **prior**), Thm. 3.1. *Finite sums with individual `L_max` smoothness and gap `F(0)−inf F ≤ Δ`. Its components are not shown to be nonnegative with average value `≤ Δ`.* | `Ω(n + √n LΔ/ε²)` IFO calls; with `n ≍ LΔ/ε²` and a uniform-sampling simulation (two IFO calls per pair call), `Ω((LΔ)^{3/2}/ε³)` → `Ω((LΔ)^{3/2}/ε³)` | None: same order | Gap `≤ Δ` with arbitrary component offsets → nonnegative samples with risk `≤ Δ` (a subclass, since `F(0) − inf F ≤ F(0)`). This is a strict gain only if shifting their components to nonnegativity costs more than `O(Δ)` in initial risk. I did not verify that. | None (convertible: constant failure probability gives expected norm `≥ cε`) | Their bound holds for every `n` and against component-selecting oracles that also return values. Here the sample count is tied to `n` stages. |
| Repository [AbcNoiseLowerBound](../../LongTails/Theorems/AbcNoiseLowerBound.lean) (2026-11-17). *Single-query oracle, gap-based ABC noise.* | `Ω(LAΔ²/ε⁴ + …)` per single gradient → not comparable | Not comparable: different oracle (K=1 vs. same-sample pair) | None | None | That theorem's oracles are not gradients of nonnegative smooth samples |

**Reduction check and ancestry.** The shortest route is "Peng et al. with `n ≍ R`, shifted per component." It needs the average `F(0) − mean_i inf f_i` to be `O(Δ)`. The companion note argues that the raw-row chains of Peng et al. and Wu et al. ([2609.28202](https://arxiv.org/abs/2609.28202) v2, Thm. 3.2 covers only `p ≥ 2`) cost order `n√m`, or `n/ρ`, in that shift. I did not verify this against their appendices. If the claim holds, the new step is the recursive perturbation `s ← (1−a)s + ab`. It cancels hidden rows exactly while keeping every sample's shift `O(n+√m)` and its smoothness `O(1+√m)`. This is a real technical modification within the known machinery: Carmon et al.'s chains, Arjevani et al.'s probabilistic reveal, and Peng et al.'s dense row hiding.

**Search coverage (2026-11-18).** I searched arXiv and the web for lower bounds under individual smoothness, finite sums, variance reduction, nonnegative or self-bounded losses, and bounded noise. I read the statements of Arjevani Thm. 3 and §6, Peng Thm. 3.1 (partly through a summary), Wu Thm. 3.2, and Jin [2608.09004](https://arxiv.org/abs/2608.09004) Thm. 4.1. Jin's result is K=1 only and not comparable. I could not read Peng's Appendix C/F, where the component infima and the `n`-range would be. I found no prior lower bound for nonnegative samples parameterized by risk. The result was introduced in commit `6af6a91` (2026-11-19 +0300). The note's citations match what I checked. Its Proposition C.1(ii) claim is unverified.

**Conclusion**

**The rate is not new; what is new is showing that the hardness survives nonnegative, risk-bounded sample losses.**

The strongest baseline is Peng–Tang–Jia (Aug 2026, preprint). Their individually smooth finite-sum bound with `n ≍ LΔ/ε²` already forces the same order, but for instances bounded only in the *gap*:

| | necessary pair calls | class |
|---|---|---|
| Peng et al., `n ≍ LΔ/ε²` | `Ω((LΔ)^{3/2}/ε³)` | individually smooth, `F(0) − inf F ≤ Δ` |
| this result | `Ω((LΔ)^{3/2}/ε³)`, for `LΔ/ε² ≥ 2⁶⁴` | the same plus `ℓ_ξ ≥ 0`, `F(0) ≤ Δ` |

Nonnegativity is what drives the companion STORM upper bound through `‖∇ℓ‖² ≤ 2Lℓ`. So the pair establishes `Θ((LΔ)^{3/2}/ε³)` for this natural model: self-bounded noise gives no advantage beyond `ε⁻³`. The gain is modest, though: same exponent, a subclass of a hard family published three months earlier, astronomical constants, and dimension `n¹¹`.

What remains open is whether Peng et al.'s components already shift to nonnegativity at `O(Δ)` cost. If they do, this theorem is a corollary. If they do not, the recursive perturbation is the real contribution. The claimable result is a tight, seed-independent lower bound for nonnegative smooth sample losses, obtained by adapting dense row hiding.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
