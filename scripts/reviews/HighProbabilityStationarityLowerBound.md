# Novelty review: HighProbabilityStationarityLowerBound

[`result`](../../LongTails/Theorems/HighProbabilityStationarityLowerBound.lean) proves the following on the setup [`HighDimensionalHighProbabilityStationarity`](../../LongTails/Setups/HighDimensionalHighProbabilityStationarity.lean). Take any valid parameters, any randomized adaptive algorithm (no `allowedAlgorithm` restriction), and any budget `b` up to `budget`. Then some instance has the following properties: `f : ℝ^d → ℝ` has an `L`-Lipschitz gradient, `f(x₀) − inf f ≤ Δ`, and the oracle is an IID unbiased stochastic gradient with variance at most `σ²`. On that instance, the algorithm fails `P(‖∇f(x̂)‖ ≤ ε) ≥ 1 − δ`. The hard instances are in [`HighProbabilityLowerAssembly`](../../LongTails/Proofs/HighProbabilityLowerAssembly.lean) and do not depend on the seed.

**Necessary budget.** The parameters are: `L` is the smoothness constant, `Δ` the initial gap, `σ²` the noise variance, `ε` the target gradient norm, and `δ` the allowed failure probability.

```
⌊(LΔ(1+σ²/ε²) + σ² log(1/(4δ))) / (2⁵⁴ ε²)⌋  =  Ω( LΔ/ε² + LΔσ²/ε⁴ + σ² log(1/(4δ))/ε² )
```

This holds when `0 < δ ≤ 1/4`, `2⁵⁴ε² ≤ LΔ`, and `d ≥ 2⁴⁰(1 + LΔ(1+σ²/ε²)/ε²)⁴`. The regime is nonempty.

**Proof structure (checked in Lean source).**
- *Chain term.* The repository's ABC masked-chain construction with `A=B=0`, `C=σ²` gives `P(‖∇f(x̂)‖ ≤ ε) < 3/4` below the chain budget, so success at level `1−δ ≥ 3/4` is impossible.
- *Confidence term.* There are two 1-D quadratics, `f_± = (L/2)⟨e,x−x₀⟩² ± 2ε⟨e,x−x₀⟩`. Their gradients differ by `4ε` everywhere, so no point is ε-stationary for both signs. The oracle adds a rare "reveal" noise with variance exactly `σ²`. With `N ≤ σ² log(1/(4δ))/(8ε²)` calls, the sign stays hidden with probability `> 2δ`, so one of the two signs fails with probability `> δ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani–Carmon–Duchi–Foster–Srebro–Woodworth, *Math. Program.* 2023 ([arXiv 1912.02365v2](https://arxiv.org/abs/1912.02365)), Thm 3, Eq. (23): `Ω(LΔσ²/ε⁴)` for all randomized algorithms. The `Ω(LΔ/ε²)` term is from Carmon et al., *Lower bounds for finding stationary points I*, Math. Program. 2020 (randomized-algorithm theorem; statement recalled, not re-read). | `Ω(LΔ/ε² + LΔσ²/ε⁴)` → `Ω(LΔ/ε² + LΔσ²/ε⁴ + σ² log(1/δ)/ε²)` | The added term `σ² log(1/δ)/ε²`. It raises the bound by more than a factor of 2 only when `log(1/(4δ)) > LΔ/ε² + LΔ/σ²`. For example, `σ = ε` gives `δ < ¼·e^{−2LΔ/ε²}`. In every other regime the two bounds have the same order. | None: same class and oracle model. ACDFSW measure success by `E‖∇F‖ ≤ ε`, but their proof gives `‖∇F‖ > 2ε` with probability ≥ 1/2. This already rules out success at `1−δ` for any `δ < 1/2`, so the chain part transfers directly. | Expected-norm criterion → explicit `1−δ` probability criterion. The conversion is immediate from the probability-1/2 failure event in the proof. | Needs `δ ≤ 1/4`. The dimension requirement `d ≳ (LΔσ²/ε⁴)⁴` is much larger than ACDFSW's `Õ(Δ²L²σ²ε⁻⁶)`. Constants are loose (`2⁻⁵⁴`). |
| Repository [`AbcNoiseLowerBound`](../../LongTails/Theorems/AbcNoiseLowerBound.lean) with `A=B=0`, `C=σ²` | `⌊LΔ(1+σ²/ε²)/(2⁵³ε²)⌋` for `E‖∇f‖ ≤ ε` → the bound above | The added `σ² log(1/δ)/ε²` term, in the same regime as the previous row. | None | Expectation criterion → `1−δ` criterion. This reuses that file's internal `3/4`-probability lemma. | Same chain construction and dimension requirement. |
| Companion [`HighProbabilityStationarityUpperBound`](../../LongTails/Theorems/HighProbabilityStationarityUpperBound.lean), from the same commit and not prior work. Here `ℓ = log(16/δ)`. | Upper `O((1+σ²/ε²)(LΔ/ε² + ℓ log³(2+ℓ)) + √(LΔ)ℓ/ε)` vs lower `Ω(LΔ(1+σ²/ε²)/ε² + σ²ℓ/ε²)` | Matching order when `ℓ log³(2+ℓ) ≲ LΔ/ε²` and `ℓ ≲ (√(LΔ)/ε)(1+σ²/ε²)`. For `σ ≳ ε` the confidence term is tight up to `log³(2+ℓ)`, apart from the `√(LΔ)ℓ/ε` term. | Not applicable: this row pairs bounds, it is not a baseline. | Same `1−δ` criterion. | When `σ ≲ ε`, the δ-gap is unbounded. The lower bound uses a high-dimensional Euclidean subclass. |

**Reduction check.** The confidence term follows from a standard reduction. The two quadratics turn ε-stationarity into testing the sign of a mean `±2ε` from variance-`σ²` samples with confidence `1−δ`. The classical Le Cam / Bretagnolle–Huber two-point bound for this test (for example, Gaussian noise) gives `Ω(σ² log(1/δ)/ε²)`, and taking the maximum with the chain bound is trivial. The rare-reveal oracle is a clean exact-coupling variant of this argument, not a new mechanism. The note itself calls this term folklore and the chain extension routine. Carmon–Hinder ([arXiv 2402.10898](https://arxiv.org/abs/2402.10898), COLT 2024) state analogous known-parameter high-probability lower bounds for convex optimization. I checked this only at the abstract level, so it serves as proof ancestry, not as a table baseline.

**Search coverage (2026-11-20).** I read ACDFSW v2 (HTML, Thm 1/Thm 3 and the proof of Thm 1). I also checked two recent papers:
- Liang–Luo, [arXiv 2610.21692v2](https://arxiv.org/abs/2610.21692) (Oct/Nov 2026). Its Thm 4.5 at `L₁=0`, `p=2` reduces to `Ω(LΔ/ε²(1+σ²/ε²))` in expectation, with no `δ` term.
- Fradin–Sadiev–Condat–Richtárik, [arXiv 2512.18713v2](https://arxiv.org/abs/2512.18713). Its lower bounds are for zero-respecting algorithms, again with no `δ` term.

Both papers were read only in part. I found no prior paper that states the combined `δ`-dependent nonconvex stationarity lower bound explicitly. That absence is not evidence of mathematical novelty, given the reduction above. The theorem was introduced in commit `0da5e0ce` (2026-11-20). The companion note's claims agree with the Lean statement.

## Conclusion

**No new complexity insight: this is a careful formal combination of a known lower bound with a textbook confidence term.**

The strongest baseline is Arjevani et al. (2023), together with Carmon et al. (2020) for the `LΔ/ε²` term. Their proof already gives failure probability at least 1/2. So the only added content is

```
Ω(LΔ/ε² + LΔσ²/ε⁴)   →   Ω(LΔ/ε² + LΔσ²/ε⁴ + σ² log(1/δ)/ε²),
```

and the new term changes the order only when `log(1/δ) ≳ LΔ/ε² + LΔ/σ²`. That means the failure probability must be exponentially small in `LΔ/ε²`, which the setup forces to be at least `2⁵⁴`.

That extra term comes from the standard two-point sign-testing bound: two 1-D quadratics whose ε-stationary sets are disjoint. The chain part transfers directly. The setup is a subclass of the standard one, with a larger dimension requirement.

The useful contribution is a fully formalized lower bound under the exact `1−δ` criterion, all algorithms quantified. When `σ ≳ ε` it shows the companion upper bound's confidence term is necessary up to `log³ log(1/δ)` factors and a `√(LΔ) log(1/δ)/ε` term. It does not establish a new lower-bound phenomenon.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**
