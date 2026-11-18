# Novelty assessment: MarkovSmoothNonconvexLowerBound

[The theorem](../../LongTails/Theorems/MarkovSmoothNonconvexLowerBound.lean) covers the high-dimensional regime of [the setup](../../LongTails/Setups/HighDimensionalMarkovSmoothNonconvex.lean). There, for every randomized adaptive algorithm and every budget `N ≤ ⌊τLΔσ² log(σ/ε)/(2⁶⁵ε⁴)⌋`, it constructs an `L`-smooth objective and an admissible stationary Markov oracle on which `∫‖∇f(output)‖ > ε` ([base oracle class](../../LongTails/Setups/MarkovSmoothNonconvex.lean), [hard construction](../../LongTails/Proofs/MarkovFrontierLower.lean)). The oracle is a jointly measurable unbiased vector estimator with stationary variance at most σ². Its chain is real-valued, starts in stationarity, and has β-mixing coefficient `∫‖Pᵗ(z,·)−π‖_TV dπ(z) ≤ 2e^{−t/τ}`.

**Necessary calls.** The parameters are: `L` (gradient Lipschitz constant), `Δ` (initial gap), `σ²` (stationary variance), `τ ≥ 1` (β-mixing scale), `ε` (target expected gradient norm) and `d` (dimension). The theorem shows

  N = Ω( τ · LΔσ²/ε⁴ · log(σ/ε) ),

valid when `LΔ ≥ 2²⁶ε²`, `σ ≥ 2¹⁶ε` and `d ≥ 2⁴⁰(1+LΔ/ε²)⁴(1+τσ²ε⁻² log(σ/ε))`. The hard instance depends on the algorithm and on `N`, but not on either seed. The repository's [upper bound](../../LongTails/Theorems/MarkovSmoothNonconvex.lean) uses `O((1+LΔ/ε²)(1+σ²/ε²)τ log(2+σ²/ε²))` calls. On this regime the two bounds match up to universal constants.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Sun–Wei, NeurIPS 2025, [Thm 3.1 (smooth)](https://proceedings.neurips.cc/paper_files/paper/2025/file/1cdbce34681a3aaa0154b300706743d8-Paper-Conference.pdf). *Zero-respecting algorithms only*; finite stationary chains with hitting time ≤ c₀τ; component-gradient oracle. Embedding into this class needs their chain's β-mixing scale to be O(τ) (not checked) | Ω(τLΔ/ε² + τσ²·min(σ², LΔ)/ε⁴) → Ω(τLΔσ² log(σ/ε)/ε⁴) | Larger by a factor `log(σ/ε)·max(1, LΔ/σ²)`. Example: σ=√ε gives τε⁻² → τε⁻³log(1/ε) | Zero-respecting algorithms → all randomized algorithms | None. Both use expected gradient norm at the output | Requires polynomial dimension and the thresholds above. The log factor comes from the β-mixing envelope; their hitting-time class is a different parameterization. The hard estimator is not a component gradient |
| Sun–Wei, ICML 2025, [Thm 3.1](https://proceedings.mlr.press/v267/sun25u.html). Countable stationary chains, hitting time ≤ τ, zero-respecting | Ω(τσ²/ε² + τσ²min(σ²,LΔ)/ε⁴) → same as above | Same factor as the row above | Same as the row above | None | Same as the row above |
| Arjevani et al., [Math. Program. 2023 / arXiv:1912.02365](https://arxiv.org/abs/1912.02365), Thm 1 and its randomized high-dimensional extension. IID oracle, which is admissible here for every τ ≥ 1 | Ω(LΔ/ε² + LΔσ²/ε⁴) → Ω(τLΔσ² log(σ/ε)/ε⁴) | Larger by a factor `τ log(σ/ε)` | IID → stationary β-mixing Markov | None | Regime thresholds; IID covers every σ ≥ 0 |

**Reduction check and proof ancestry.** I found no standard reduction that gives the result. If Arjevani's probabilistic zero-chain is driven by a sticky chain that holds each sample for about τ steps, an open gate can reveal about τ coordinates in one visit, so the factor τ is lost. Sun–Wei's construction limits the chain length to σ²/ε², which is the source of their `min(σ², LΔ)`.

The mechanisms that look new are masking only the "frontier" gradient component, and countdown halves of alternating parity that limit progress to one coordinate per excursion ([oracle](../../LongTails/Proofs/MarkovFrontierOracle.lean), [occupancy](../../LongTails/Proofs/MarkovFrontierOccupancy.lean)). The rare-excursion source of `log(σ/ε)` is inherited from the repository's convex countdown bound ([review](StretchedExponentialMarkovConvexLowerBound.md), commit `89bcdaf8`, 2026-11-13). The randomized-algorithm extension follows the random-embedding counting approach of Arjevani et al.

**Search coverage (2026-11-18 UTC).** I searched the web for Markov, β-mixing and nonconvex lower bounds, and read the full Theorem 3.1 statements and proof sketches of both Sun–Wei papers. Other sources were checked only partly:
- Beznosikov et al. (arXiv:2305.15938): abstract only. It states lower bounds only in the strongly convex case.
- The AAAI 2026 Markovian-stochasticity paper: inaccessible.
- Jin (arXiv:2608.09004): abstract only. It concerns IID noise.

The result was introduced in commit `8d1d2181` (2026-11-19 +0300). The companion note's citations and its description of Sun–Wei are accurate. However, the note omits that the ICML Theorem 3.1 has the same `min(σ², LΔ)` structure.

**Conclusion**

**Yes: this is a larger necessary budget than any checked prior bound, and it holds for all randomized algorithms.**

The strongest prior lower bound is Sun–Wei's (NeurIPS 2025). It is restricted to zero-respecting algorithms and uses hitting-time-bounded finite chains:

| | Necessary oracle calls |
|---|---|
| Sun–Wei Thm 3.1 | Ω(τσ²·min(σ², LΔ)/ε⁴) |
| This theorem | Ω(τLΔσ² log(σ/ε)/ε⁴) |
| Repository upper bound | O(τLΔσ² log(σ/ε)/ε⁴) on this regime |

There are three gains. First, the bound holds for all randomized algorithms, not only zero-respecting ones. Second, it is larger by a polynomial factor `LΔ/σ²` when σ² ≪ LΔ, for example ε⁻³ log(1/ε) instead of ε⁻² at σ = √ε. Third, it carries a `log(σ/ε)` factor, which shows that the upper bound's logarithm is necessary under β-mixing.

Several qualifications apply. The theorem needs polynomially large dimension and the stated thresholds. The log factor is specific to averaged (β-)mixing, not to uniform or hitting-time mixing. Embedding Sun–Wei's chain into this class was not checked, so the comparison of their class with this one is not fully verified, but their bound is weaker in every case. Priority is supported only by a search that found no competing result; it is not proven, and the AAAI paper was inaccessible.

What can be claimed is a tight minimax lower bound, `τLΔσ² log(σ/ε)/ε⁴`, for smooth nonconvex stationarity with β-mixing Markov gradient oracles, holding for all algorithms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
