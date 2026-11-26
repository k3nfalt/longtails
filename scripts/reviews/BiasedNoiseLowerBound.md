# BiasedNoiseLowerBound: novelty assessment

[`result`](../../LongTails/Theorems/BiasedNoiseLowerBound.lean) is a lower bound on the [setup](../../LongTails/Setups/HighDimensionalBiasedNoiseNonconvex.lean), the ℝ^{d+1} restriction of [the Ajalloeian–Stich class](../../LongTails/Setups/BiasedNoiseNonconvex.lean). For every valid parameter vector, every randomized gradient-only algorithm and every call count `b ≤ budget`, there is an `L`-smooth `f` with `f(x₀) − inf f ≤ Δ` and an IID oracle satisfying both conditions below on which `E‖∇f(x̂)‖ > ε`. The algorithm class is fully adaptive, with arbitrary internal randomness and output rule. The conditions are:

- `(m,ζ²)`-bias: `‖Eg − ∇f‖² ≤ m‖∇f‖² + ζ²`;
- `(M,σ²)`-noise: `Var g ≤ M‖Eg‖² + σ²`.

The hard instance is in [Proofs/BiasedLowerOracle.lean](../../LongTails/Proofs/BiasedLowerOracle.lean).

**Necessary oracle calls.** The proved budget is `⌊LΔ(1+M+σ²/r)/(2⁶⁰r)⌋` with `r = (1−m)ε²`:

  Ω( LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴) ).

Here `L` is the smoothness constant, `Δ` the initial gap, `m∈[0,1)` the relative bias, `M` the relative variance, `σ²` the absolute variance and `ε` the target for `E‖∇f‖`. The bound requires `16ζ² ≤ (1−m)ε²`, `2²⁸ε² ≤ LΔ` and `d ≥ 2⁴⁰(1 + LΔ(1+M+σ²/r)/r)⁴`. It does not depend on ζ. The companion [upper bound](../../LongTails/Theorems/BiasedNoiseSgdUpperBound.lean) uses `⌈16LΔ(1+M+σ²/r)/r⌉+1` SGD calls on the general class. The two bounds therefore match up to universal constants, with no logarithms.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani et al., [Math. Program. 2023](https://arxiv.org/abs/1912.02365), Thm 1 (unbiased, randomized). Special case `m=M=0`; such instances lie in the class. | Ω(LΔ/ε² + LΔσ²/ε⁴) → Ω(LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴)) | Larger necessary budget by factors `(1+M)/(1−m)` (deterministic term) and `1/(1−m)²` (noise term). The gain is polynomial when `1−m ≪ 1` or `M ≫ 1`. | Unbiased oracle → relative-bias oracle with `m>0` | None: both are randomized, expectation-type bounds | Polynomial dimension `d ≳ (LΔ(1+M+σ²/r)/r)⁴`; constant `2⁶⁰` |
| Repository [AbcNoiseLowerBound](../../LongTails/Theorems/AbcNoiseLowerBound.lean). Unbiased ABC model, covers `m=0`. | Ω(LΔ(1+M+σ²/ε²)/ε²) at `m=0` → adds `1/(1−m)` in every term | Factor `1/(1−m)` and `1/(1−m)²` | `m=0` → `m∈[0,1)` | None | The base chain is reused white-box |
| Shyam–Bullins, [arXiv:2606.19553](https://arxiv.org/abs/2606.19553) v1 (17 Jun 2026, prior), Thm 1. Absolute bias `‖b‖≤B`, i.e. `m=M=0, ζ=B` (their Remark 1). | Ω(LΔ/(ε²+B²) + LΔσ²/(ε⁴+B⁴)) (`ε` = norm accuracy) → as above | Under the floor `ζ² ≲ (1−m)ε²`, their bound reduces to row 1. The gain is the same `m`- and `M`-factors. | Absolute bias only → relative bias | Zero-respecting algorithms, constant probability → all randomized algorithms, expectation | Does not quantify the ζ-floor regime; their bound does |
| Huang et al., [NeurIPS 2022](https://arxiv.org/abs/2206.03665), Thm 2 (δ-contractive compression). Different model: `n≥2` workers, communication rounds, zero-respecting, σ>0. | Ω(LΔσ²/(nε⁴) + LΔ/(δε²)). With their rand-s compressor, `m=(1−δ)²` and `M=(1−δ)/δ`, so `1−m∈[δ,2δ]`. Selected bound for that pair: Ω(LΔ/(δ²ε²) + LΔσ²/(δ²ε⁴)) | Not directly comparable (different oracle and cost model). On the induced `(m,M)` pair, the selected necessary budget is larger by a factor `1/δ` (deterministic term) and `n/δ²` (noise term). | Coupled `(m,M)` from one compressor → independent `m`, `M`, including `M=0` | — | Single oracle; does not cover distributed rounds |

**Reduction check.** Simple reductions do not give the bound. The scaled oracle `(1−√m)∇f` is admissible but reveals the gradient, so it loses nothing. Absolute-bias and unbiased chains contain no `m`. The new mechanism (verified in the Lean files) is a sign-randomized "decoy" slope `κθ·p(s z − c)` with `κ² = m/(1−m)`. The oracle suppresses that slope exactly while `θ|p′| ≤ ‖∇F‖`. This is precisely the relative-bias budget, so the effective accuracy shrinks from `ε²` to `(1−m)ε²` in every term. The randomized chain, coin masking and counting argument are proof ancestry from Arjevani et al. and the repository's ABC lower bound. The hard bias is adversarial and deterministic, orthogonal to `∇F`, and admissible in the class.

**Search coverage.** I searched on 2026-11-26 (arXiv, NeurIPS/Math. Program. proceedings). I read the theorem statements of:

- Ajalloeian–Stich ([arXiv:2008.00051](https://arxiv.org/abs/2008.00051) v2, ICML 2020 workshop): Thm 4 is an upper bound, and Remark 5 is only a floor example;
- Demidovich et al. ([NeurIPS 2023](https://arxiv.org/abs/2305.16296)): it claims rates are "also optimal in the biased case" but gives no biased lower-bound theorem;
- Shyam–Bullins;
- Huang et al.;
- Vasin et al. [arXiv:2503.06628](https://arxiv.org/abs/2503.06628) and Vasin–Gasnikov [arXiv:2603.12376](https://arxiv.org/abs/2603.12376): relative-error lower bounds that are convex/strongly convex only or method-specific.

Some appendices were read only through summaries. I did not verify the note's Polyak (1987) citation, Vernimmen–Glineur's PEP bound, or the ICLR 2027 submissions. I found no mismatch between the companion note and the Lean statement.

## Conclusion

**Yes: this is a new lower bound that pins down how relative gradient bias affects nonconvex complexity.** The strongest prior lower bounds are Arjevani et al. for unbiased noise and Shyam–Bullins (2026) for absolute bias. Both are blind to the relative-bias parameter `m`, so the Ajalloeian–Stich SGD upper bound was not known to be tight in `m`.

| | necessary calls |
|---|---|
| prior (`m`-free) | Ω(LΔ/ε² + LΔσ²/ε⁴) |
| this result | Ω(LΔ(1+M)/((1−m)ε²) + LΔσ²/((1−m)²ε⁴)) |
| SGD upper bound (Ajalloeian–Stich / companion theorem) | O(same) |

This closes the class complexity up to universal constants, uniformly in `m∈[0,1)`, for every randomized gradient-only method. It shows that relative bias costs `1/(1−m)` without noise and `1/(1−m)²` with noise, and that momentum, adaptivity or output selection cannot avoid either factor. The gain over the prior lower bounds is polynomial only when `1−m ≪ 1` or `M ≫ 1`. For `m` bounded away from 1 it is a constant factor.

The theorem needs a polynomially large dimension and uses an adversarial, deterministic hard bias. It says nothing about oracles that also return function values, or about convex classes. My search found no prior proof of this statement; Demidovich et al.'s optimality claim is unsupported for `m>0`. Some sources were not fully checked, so priority is likely but not certain.

What can be claimed is the first verified lower bound showing that the `m`-dependence of biased SGD is optimal for nonconvex stationarity, together with a new decoy construction.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
