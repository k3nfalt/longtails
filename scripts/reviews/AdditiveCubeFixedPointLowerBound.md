# Novelty assessment: AdditiveCubeFixedPointLowerBound

[Theorem](../../LongTails/Theorems/AdditiveCubeFixedPointLowerBound.lean) · [Setup](../../LongTails/Setups/GaussianAdditiveCubeFixedPoint.lean) (extends [AdditiveCubeFixedPoint](../../LongTails/Setups/AdditiveCubeFixedPoint.lean)) · hard instance: [AdditiveFixedPointFamily](../../LongTails/Proofs/AdditiveFixedPointFamily.lean), [noise variance](../../LongTails/Proofs/AdditiveFixedPointLowerBudget.lean)

**Guarantee.** Suppose `R ≥ 128ε` and `d ≥ ⌈R/ε⌉`. Take any measurable, adaptive, randomized algorithm and any budget `b` up to the stated bound. Then some map `T : [-R,R]^d → [-R,R]^d` that is 1-Lipschitz in the sup norm defeats it. The map may depend on the algorithm and `b`, but not on the seed. Each call returns `T(x)+Z` with fresh noise `Z ~ N(0, vI)`, where `v = σ²/(4(2+log d))`, so `E‖Z‖∞² ≤ σ²`. Under this oracle the output fails `E‖T(x̂)−x̂‖∞ ≤ ε`.

Here R is the cube radius, σ bounds the second moment of the noise in the sup norm, ε is the accuracy and d is the dimension. The proved necessary budget (Lean constant `2⁻²⁶`) is

  N_lower = Ω( (1 + σ²/(ε²(2+log d))) · R / (ε(1+log(2+(R+σ)/ε))) ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Diakonikolas–Guzmán–Martínez-Rubio (DGM), [arXiv:2609.09524v1](https://arxiv.org/pdf/2609.09524v1) (8 Sep 2026, preprint), Thm 11: exact oracle, ℓ∞ box, `d ≥ ⌊1/(8ε)⌋` after rescaling. It applies here: v = 0 is an admissible Gaussian. | Ω(R/ε) → the bound above | Larger by a factor of about σ²/(ε² log d · log((R+σ)/ε)) when σ² ≳ ε² log d · log(2+(R+σ)/ε). Worse by a factor 1+log(2+(R+σ)/ε) when σ² ≲ ε² log d. | None (same class) | None. DGM's constant-probability failure transfers to expected residual by Markov's inequality. | Needs d ≥ R/ε, compared with d ≳ R/(8ε) for DGM. |
| DGM Thm 13 + Remark 14: lazy Bernoulli oracle `x + (B/p)(T(x)−x)`, ℓ∞ variance σ², constant-probability success. | Ω(R/ε + Rσ²/ε³) on the Bernoulli class → the bound above on the additive Gaussian class | Not comparable: different oracle classes. On its own class DGM is larger by a factor of about log d · log((R+σ)/ε). | Hardness moves from a query-dependent, information-masking noise law to a fixed additive isotropic Gaussian law. This is a narrower and more benign oracle class, so the hardness statement is stronger. | None | Loses factors of log d and log((R+σ)/ε). Requires the isotropic normalization v ∝ σ²/log d. |

**Upper-bound gap.** Lee, [arXiv:2610.26484v1](https://arxiv.org/abs/2610.26484) (19 Oct 2026), Thm 3, case p = ∞, and the repository's [AdditiveCubeFixedPoint](../../LongTails/Theorems/AdditiveCubeFixedPoint.lean) give O(R/ε + Rσ² log(2d)/ε³). The gap to this lower bound is log²d · log((R+σ)/ε). The companion note says Gaussian averaging gives O(R/ε + Rσ²/ε³) on this subclass, which would leave a gap of log d · log((R+σ)/ε). I did not check that claim. Bravo–Contreras ([arXiv:2403.12338v4](https://arxiv.org/abs/2403.12338), Thm 3.7) give Ω(σ²ε⁻³), but only in ℓ₁, for span-restricted algorithms, with a Bernoulli oracle. It does not apply here.

**Reduction check and proof ancestry.** DGM's lower bound does not reduce to the additive model. Its oracle sets the noise to `(B/p−1)(T(x)−x)`, which depends on the query and is exactly 0 on uninformative calls. Additive Gaussian replies leak information about every coordinate on every call. The new step is a phase-wise change of measure: a Gaussian χ²/Cauchy–Schwarz transfer of rare-hit events under adaptive querying, combined with a coupled sign-chain map adapted from DGM eq. (8). DGM supplies the deterministic chain geometry. The additive-noise information argument is not in DGM.

**Search coverage (18 Nov 2026).** I searched arXiv and the web for stochastic nonexpansive and ℓ∞ fixed-point lower bounds. I read the DGM Thm 11, 13 and 16 statements and proofs from the PDF. Lee's Thm 3 and Bravo–Contreras Thm 3.7 were read through a fetch agent from their HTML versions, as were the relevant parts of Diakonikolas [arXiv:2607.09097](https://arxiv.org/abs/2607.09097) and Shehu [arXiv:2610.00295](https://arxiv.org/abs/2610.00295). None of these states an additive-noise lower bound for this problem. Diakonikolas 2607.09097 lists nonexpansive lower bounds as open. All of these are recent preprints, and very recent arXiv postings may be missed. The companion note's description of DGM Thm 11 and 13 matches the paper. The result was introduced in commit `8d8a7ab6` on 18 Nov 2026 UTC, after DGM and Lee.

## Conclusion

**Yes, in a sense: it shows the cubic cost for noisy sup-norm fixed points is not an artifact of query-dependent noise.** The strongest baseline is DGM's Ω(R/ε + Rσ²/ε³) (Thm 13). That bound uses a lazy Bernoulli oracle, whose noise masks the map on most calls, so it says nothing about plain additive noise `T(x)+Z`.

| Oracle class | Necessary calls |
|---|---|
| Bernoulli, query-dependent (DGM) | Ω(R/ε + Rσ²/ε³) |
| Additive isotropic Gaussian (this result) | Ω((1 + σ²/(ε² log d)) · R/(ε log((R+σ)/ε))) |
| Additive, upper bound (Lee Thm 3) | O(R/ε + Rσ² log d/ε³) |

On the same additive class, the result beats the only applicable prior bound, DGM's noiseless Ω(R/ε). The gain appears once σ²/ε² ≫ log d · log((R+σ)/ε), and it is polynomial: Ω̃(ε⁻³) instead of Ω(ε⁻¹). For smaller noise it is weaker by a logarithm. It also requires d ≥ R/ε and loses log d · log((R+σ)/ε) relative to DGM's bound on the Bernoulli class.

The comparison establishes this gain. Priority rests on a search of very recent preprints that found no additive-noise lower bound. The contribution that can be claimed is a near-cubic lower bound against arbitrary adaptive randomized algorithms, under fresh additive Gaussian noise, with a new change-of-measure argument. Logarithmic gaps to the upper bounds remain.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
