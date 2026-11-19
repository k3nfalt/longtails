# Novelty assessment: AverageMixingMarkovSmoothNonconvexLowerBound

[The theorem](../../LongTails/Theorems/AverageMixingMarkovSmoothNonconvexLowerBound.lean) is stated in [the setup](../../LongTails/Setups/HighDimensionalAverageMixingMarkovSmoothNonconvex.lean), which restricts the parameters of [the base setup](../../LongTails/Setups/AverageMixingMarkovSmoothNonconvex.lean); the hard instance is in [MarkovFrontierOracle](../../LongTails/Proofs/MarkovFrontierOracle.lean) and [MarkovFrontierLower](../../LongTails/Proofs/MarkovFrontierLower.lean). The theorem says: for every randomized adaptive algorithm and every budget `b ≤ ⌊τLΔσ² log(σ/ε)/(2⁶⁵ε⁴)⌋`, some admissible instance makes `E‖∇f(x̂)‖ > ε`. The instance may depend on the algorithm and on `b`, but not on the seeds. Each call returns `g(x,Z_t)` from one stationary chain on ℝ. The chain only has to satisfy a stationary-averaged mixing bound, `∫‖Pᵗ(z,·)−π‖_TV dπ(z) ≤ 2e^{−t/τ}`; for a stationary chain this quantity is exactly the β-mixing coefficient. Under π the oracle is unbiased with variance at most `σ²`.

**Necessary calls:** Ω(τ·LΔσ²·log(σ/ε)/ε⁴).
- Parameters: `L` is the gradient-Lipschitz constant, `Δ = f(x₀) − inf f`, `σ²` the stationary variance, `τ ≥ 1` the averaged-mixing scale, `ε` the target accuracy and `d` the dimension.
- Valid range: `L,ε > 0`, `LΔ ≥ 2²⁶ε²`, `σ ≥ 2¹⁶ε`, and `d ≥ 2⁴⁰(1+LΔ/ε²)⁴(1+τσ²log(σ/ε)/ε²)`.
- In this range `σ²/ε² ≥ 2³²`, so the term `τLΔ/ε²` is absorbed.
- The [companion upper bound](../../LongTails/Theorems/AverageMixingMarkovSmoothNonconvex.lean) is `(⌊2048LΔ/ε²⌋+1)(⌊256σ²/ε²⌋+1)(⌊τ log(32+8192σ²/ε²)⌋+1) = O(τLΔσ² log(σ/ε)/ε⁴)` here. It is the same model and was added in the same commit, so the complexity is Θ in this regime, up to very large universal constants.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani et al., *Math. Program.* 2023 ([arXiv:1912.02365](https://arxiv.org/abs/1912.02365)), Thm 3; Jin ([arXiv:2608.09004](https://arxiv.org/abs/2608.09004), Aug 2026, Thm 4.1) gives the same order. Applies only to IID data; IID chains are in the class for every τ ≥ 1. | Ω(LΔ/ε² + LΔσ²/ε⁴) → Ω(τLΔσ² log(σ/ε)/ε⁴) | Larger by a factor τ·log(σ/ε), for every τ ≥ 1 and σ ≥ 2¹⁶ε | IID samples → one stationary β-mixing chain | None. Both cover all randomized algorithms and use `E‖∇f‖`. | Dimension polynomial in `LΔ/ε²` and in `τσ²/ε²`; requires σ ≥ 2¹⁶ε; constant 2⁻⁶⁵ |
| Sun & Wei, NeurIPS 2025 ([paper](https://proceedings.neurips.cc/paper_files/paper/2025/file/1cdbce34681a3aaa0154b300706743d8-Paper-Conference.pdf)), Thm 3.1 (ICML 2025 Thm 3.1 is analogous). Uses a hitting-time class and covers only zero-respecting algorithms. | Ω(τ_h σ² min{σ²,LΔ}/ε⁴). Their hard chains mix in about τ_h² steps, so with τ ≍ τ_h² this is Ω(√τ·LΔσ²/ε⁴) when σ² ≥ LΔ → Ω(τLΔσ² log(σ/ε)/ε⁴) | In mixing units: a factor √τ·log(σ/ε) when σ² ≥ LΔ; when σ² < LΔ, √τσ⁴ → τLΔσ² log(σ/ε) | Hitting-time parameter → averaged-mixing parameter (incomparable classes) | Zero-respecting methods → all randomized adaptive methods, with arbitrary outputs | Theirs needs no huge dimension. The √τ conversion is taken from the [prior repository review](MarkovNonconvexStationarityLowerBound.md) and was not re-derived here. |
| Repository: [MarkovNonconvexStationarityLowerBound](../../LongTails/Theorems/MarkovNonconvexStationarityLowerBound.lean), commit c8bf1984, 2026-11-19 (about 11 h earlier; unpublished). Uses uniform mixing, which is nested in the averaged class. | Ω(τLΔσ²/ε⁴) → Ω(τLΔσ² log(σ/ε)/ε⁴) | A factor log(σ/ε) | Dimension requirement (1+τLΔσ²/ε⁴)⁴ → (1+LΔ/ε²)⁴(1+τσ²log(σ/ε)/ε²) | None | Hardness holds only in the larger averaged class: the hard chain does not mix uniformly at scale τ. Requires σ ≥ 2¹⁶ε instead of 4096ε. Whether the log is needed under uniform mixing remains open. |

**Reduction check.** The repository's uniform-mixing bound already transfers to this class, but only as Ω(τLΔσ²/ε⁴). Sticky refresh chains cannot add the logarithm. A refresh rate λ with colour mass q gives averaged TV ≈ 2q·e^{−λt}, so the envelope forces λτ ≳ 1. The log(σ/ε) requires deterministic rare excursions of length about τ log(σ²/ε²). The new mechanism splits each excursion into two halves, with the parity of the frontier deciding which half can reveal it. This keeps an excursion from revealing more than one zero-chain link.

**Proof ancestry.** The pieces are inherited as follows:
- the zero-chain and coordinate hiding come from Arjevani et al. and Carmon et al.;
- the alternating parity comes from Sun–Wei and the repository's uniform-mixing proof;
- the calibrated countdown chain comes from the repository's convex [StretchedExponentialMarkovConvexLowerBound](StretchedExponentialMarkovConvexLowerBound.md), whose `CountdownMarkov` module this proof imports.

Combining D barriers with the excursion logarithm is the additional step, and the companion note correctly says the precedents do not imply it.

**Search coverage (2026-11-19 UTC).** I searched the web for lower bounds under Markov, β-mixing and hitting-time sampling for nonconvex stationarity. The search covered Beznosikov et al. ([arXiv:2305.15938v2](https://arxiv.org/abs/2305.15938)), whose lower bounds treat only strongly convex problems under uniform mixing, and Prokhorov et al. ([arXiv:2601.01160](https://arxiv.org/abs/2601.01160)), which treats zero-order, strongly convex problems. It also covered [arXiv:2607.25785](https://arxiv.org/abs/2607.25785), with an Ω(τε⁻³) hitting-time bound under mean-squared smoothness, [arXiv:2606.26316](https://arxiv.org/abs/2606.26316), on PL problems, and Nagaraj et al. (NeurIPS 2020), on least squares. None gives a nonconvex mixing-time bound for all algorithms.

Caveats:
- The Beznosikov and Prokhorov statements were read through extracted summaries.
- The Sun–Wei mixing conversion is taken from the earlier review.
- The theorem's own text was not re-read for Arjevani et al. or Even (ICML 2023).

The companion note's claims agree with the Lean statement.

**Conclusion**

**Yes: under exponentially β-mixing Markov oracles, this is a new tight lower bound, and it shows the log(σ/ε) factor in the upper bound is necessary.** Against published work, the strongest baseline for all algorithms is the IID bound of Arjevani et al.; Sun–Wei's Markov bound covers only zero-respecting methods.

| | Necessary calls (high-dim., σ ≥ 2¹⁶ε, LΔ ≥ 2²⁶ε²) |
|---|---|
| Arjevani et al. (IID) | Ω(LΔσ²/ε⁴) |
| Repository, uniform mixing (one day earlier) | Ω(τLΔσ²/ε⁴) |
| This theorem | Ω(τLΔσ²log(σ/ε)/ε⁴), matched by the companion upper bound |

The published comparison proves a gain of τ·log(σ/ε). I found no earlier bound that rivals it, but that does not prove priority.

Two limitations matter. Relative to the repository's own predecessor, the new content is only the logarithm and a milder dimension condition, and it holds only because averaged mixing permits long rare excursions. The hard oracle also needs huge dimension and statewise errors far above σ, so bounded-noise models are untouched.

What can be claimed is the first matching Θ(τLΔσ²log(σ/ε)/ε⁴) characterization of nonconvex expected stationarity for all randomized algorithms under stationary β-mixing oracles.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
