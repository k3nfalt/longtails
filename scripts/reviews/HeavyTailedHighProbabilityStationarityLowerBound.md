# Novelty assessment: HeavyTailedHighProbabilityStationarityLowerBound

[`result`](../../LongTails/Theorems/HeavyTailedHighProbabilityStationarityLowerBound.lean) proves the following ([setup](../../LongTails/Setups/HighDimensionalHeavyTailedHighProbabilityStationarity.lean), [hard instances](../../LongTails/Proofs/HeavyTailedHighProbabilityLower.lean)). Take any randomized algorithm on `ℝ^d` that uses at most the stated number of IID stochastic-gradient calls, where the noise is unbiased and has central `p`-th moment at most `σ^p`. Then some `L`-smooth `f` with `f(x₀) − inf f ≤ Δ` makes it fail to have `P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ`. The hard instance may depend on the algorithm but not on its seed.

**Necessary budget** (Lean: `⌊(…)/2^55⌋`). Here `L` is smoothness, `Δ` the initial gap, `σ^p` the central `p`-moment bound with `p ∈ (1,2]`, `ε` the gradient-norm accuracy and `δ` the failure probability:

```
N ≥ 2^-55 [ (1 + (σ/(2^12 ε))^{p/(p−1)}) LΔ/ε² + (σ/(2^12 ε))^{p/(p−1)} log(1/(4δ)) ]
```

The theorem requires `0 < δ ≤ 1/4`, `LΔ ≥ 2^54 ε²` and `d ≥ 2^130 (1 + LΔ(1+(σ/ε)^{p/(p−1)})/ε²)^4`. The factor `2^{12p/(p−1)}` inside the noise term is not a universal constant: it blows up as `p → 1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fradin–Sadiev–Condat–Richtárik, [arXiv:2512.18713](https://arxiv.org/abs/2512.18713) v1 21 Dec 2025, v2 31 Mar 2026 (prior), Thm 3.2 (first branch of the min, letting the similarity constant grow); Lemma C.1 / Thm 3.1 term `(σ/ε)^{p/(p−1)}` | `Ω((1+(σ/ε)^{p/(p−1)})LΔ/ε²)` → the bound above | Adds `(σ/ε)^{p/(p−1)} log(1/δ)`. This exceeds the prior bound by more than a constant only when `log(1/δ) ≫ LΔ/ε²` (≥ 2^54 here) | Zero-respecting algorithms → all randomized algorithms | Expectation-type criterion → probability `1−δ` for every `δ ≤ 1/4` | Needs dimension polynomial (fourth power) in `LΔ(1+(σ/ε)^{p/(p−1)})/ε²`. Constants are worse, and the noise-term constant depends on `p` |
| Zhang et al., NeurIPS 2020, [arXiv:1912.03194](https://arxiv.org/abs/1912.03194) Thm 6 (App. G) | `E‖∇f(x_k)‖ ≥ Ω(k^{−(α−1)/(3α−2)})`, i.e. order `ε^{−(3p−2)/(p−1)}` with other parameters fixed → the bound above | Explicit dependence on `L, Δ, σ` and `δ` | Raw moment `E‖g‖^α ≤ G^α` with `G ≥ 4√(LΔ)` → central moment, any `σ ≥ 0` | Expected norm → probability `1−δ` | None beyond the dimension requirement |
| 1-D reduction from heavy-tailed mean estimation (Devroye–Lerasle–Lugosi–Oliveira, [Ann. Statist. 2016](https://arxiv.org/abs/1509.05845), Thm 3.1) | `Ω((σ/ε)^{p/(p−1)} log(1/δ))` by the reduction below → same term | None: same order (confidence term) | None | None | Devroye et al. state it for `δ > 2e^{−n/4}`; the repository's two-point argument has no such restriction |
| Repository [`HighProbabilityStationarityLowerBound`](../../LongTails/Theorems/HighProbabilityStationarityLowerBound.lean) (`p = 2`) | `Ω((LΔ(1+σ²/ε²) + σ² log(1/δ))/ε²)` → same form | None at `p = 2` (worse constants) | Variance → central `p`-moment, `p ∈ (1,2]` | None | None |

**Reduction check.** Take `f_θ(x) = (L/2)x² + θx` with a query-independent noise sample `Y`. Every call then reveals only an IID sample of mean `θ`, and an ε-stationary output gives `|−Lx̂ − θ| ≤ ε`. So the confidence term follows from two-point heavy-tailed testing, and the repository's "rare-reveal" coin is the scaled-Bernoulli law used by Bubeck–Cesa-Bianchi–Lugosi ([arXiv:1209.1727](https://arxiv.org/abs/1209.1727)). The main term reuses the probability-θ zero chain of Arjevani et al. (Math. Program. 2023), with its randomized-algorithm extension and Bernoulli noise; its only new ingredient is the elementary bound `E|coin−1|^p ≤ 2t^{p−1}`, which is Fradin et al.'s Lemma C.1-type computation. A sum of two lower bounds is at most twice their maximum, so combining them is free. I found no proof obstacle that needs a new idea. I did not verify that Fradin's appendix proof yields constant-probability failure, though zero-chain proofs usually do.

**Search coverage.** I searched on 2026-11-25 (UTC) using web searches covering nonconvex heavy-tailed lower bounds, high-probability lower bounds, and mean-estimation lower bounds. I read the theorem statements of Fradin et al. (v2), Zhang et al. Thm 6 with App. G, and Devroye et al. Thm 3.1. I did not read Liu–Zhou's p-BCM lower bound ([arXiv:2412.19529](https://arxiv.org/abs/2412.19529)) or Fradin's appendix proofs, and Fradin's publication venue (the note says AISTATS 2026) is unverified. The theorem entered the repository in commit `3f8d16ff` on 2026-11-25. The companion note is right that the main-term and rare-reveal mechanisms are standard. Its claim of a "first high-probability characterization" overstates the result: against the paired upper bound, the low-noise `log(1/δ)·polylog` term and the `√(LΔ)log(1/δ)/ε` corner term are not captured, the polylog factor remains, and `σ/ε` is rescaled by a factor of `2^{57}` inside the power `p/(p−1)`.

## Conclusion

**This adds no new complexity term: it combines two known lower bounds and extends them to all randomized algorithms at confidence 1−δ.** The closest baseline is Fradin et al. (Dec 2025), Thm 3.2, which proves the main term for zero-respecting algorithms under the same central-moment noise.

```
Fradin et al.:  Ω( (1 + (σ/ε)^{p/(p−1)}) · LΔ/ε² )            zero-respecting, expectation
This result:    Ω( (1 + s′) · LΔ/ε²  +  s′ · log(1/δ) )       all randomized, probability 1−δ
                where s′ = (σ/(2^12 ε))^{p/(p−1)}
```

The extra `s′·log(1/δ)` term increases the necessary budget only when `log(1/δ) ≫ LΔ/ε²`, that is, at exponentially small failure probabilities. That term also follows from the classical heavy-tailed mean-estimation lower bound through a one-dimensional quadratic. The extension to randomized algorithms follows Arjevani et al.'s standard randomization of the zero chain.

What is established is a correct-looking statement, with explicit constants, that covers all randomized algorithms, all `p ∈ (1,2]` and all `δ ≤ 1/4`; I did not run the build or the axiom audit. What remains open is whether this exact combined, randomized-algorithm, high-probability statement already appears in print; I found it nowhere. Even so, every ingredient is a known mechanism, and the gaps to the paired upper bound remain. The claimable contribution is a unified high-probability lower bound against randomized algorithms for heavy-tailed nonconvex stationarity, an incremental strengthening of Fradin et al. and Zhang et al.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
