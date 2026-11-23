# DistributedLocallySmoothGrowth: novelty assessment

[`result`](../../LongTails/Theorems/DistributedLocallySmoothGrowth.lean) is an elapsed-time bound for a finite-bit star network, given in the [setup](../../LongTails/Setups/DistributedLocallySmoothGrowth.lean) and the [algorithm](../../LongTails/Algorithms/LocallySmoothGrowthSgd.lean). The algorithm is the earlier [gradient-diversity schedule](../../LongTails/Algorithms/GradientDiversitySgd.lean) with a new `scale`. The assumptions are:
- convex `fᵢ` with public per-worker gradient-Lipschitz bounds `Lᵢ`;
- the average `F` has `μ`-quadratic growth;
- mean-squared strong growth `Σᵢ‖∇fᵢ‖² ≤ nρ‖∇F‖²`;
- unbiased worker oracles with variance at most `σ²`, IID within each worker and independent across workers.

Under these assumptions the last stored iterate satisfies `E dist(X, X*)² ≤ ε`.

**Bound.** The parameters are:
- `hᵢ`, worker `i`'s time per gradient, with `H = maxᵢhᵢ` and `S = Σᵢ1/hᵢ`;
- `ℓ`, the latency, and `b`, the cost per bit;
- `d`, the dimension, and `R`, the distance from `x₀` to a minimizer;
- `L̄ = max(μ, maxᵢLᵢ)`, the derived aggregate smoothness.

The profile `u` minimizes `Σuᵢ²/hᵢ` subject to `Σuᵢ = n` and `Σuᵢ² ≤ nρ`. It has no closed form, and the budget computes it with a scalar threshold. Write `I₀ = Σuᵢ²/hᵢ`, `m = maxᵢuᵢ·max(μuᵢ, Lᵢ)` and `A = 2Sm/(μI₀)`. Reading this off the Lean budget, with constants suppressed:

`T = O( σ²/(μ²I₀ε) + A·log(2+R²/ε)·[H + ℓ + b(1 + d·log(4+d+A+(R² + σ²(maxᵢuᵢ)²/m²)/ε))] )`.

At equal speeds `u ≡ 1`, so `A = 2L̄/μ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Malenia SGD, [Tyurin–Richtárik, NeurIPS 2023](https://arxiv.org/abs/2305.12387); PL version in [Tyurin, arXiv 2609.17483v1](https://arxiv.org/abs/2609.17483) (15 Sep 2026, only version), Thm F.2. Needs convex `fᵢ` and `F` that is `L̄`-smooth and PL; QG plus convexity implies PL up to a constant. Free communication. | `[H·L̄/μ + (Σhᵢ)σ²/(n²μ²ε)]·log(R²/ε)` → `T` | **Equal speeds:** both are `h·L̄/μ·log + hσ²/(nμ²ε)·(log)`, so the order is the same; only the log on the statistical term is removed. **Many-speed family from the note:** `n=2m`, ε = m^(−γ) with `5/4<γ<7/4`. Here the bound improves from `Θ(m^γ log m)` to `Θ(m^γ/log m)`, a `log² m` gain. | None. Malenia's class contains this one. | None. Both need known parameters and give `E dist²` for the returned point. | Needs strong growth, known `ρ`, and known `Lᵢ`. Each round waits for the slowest worker `H`. For `γ<5/4` in that family, the new bound is worse (`m^{5/4}` vs `m^γ log m`). This result pays for communication; Malenia does not model it. |
| Repository [DistributedGradientDiversity](../../LongTails/Theorems/DistributedGradientDiversity.lean) (`a378bdce`, 2026-11-23, same day). Its setup has aggregate `L` only. | Same statistical term; round factor `L·max(βU₀S, nW₀)/(μI₀)`, with `β = min(n, 1+√(n(ρ−1)))` → `A` | The round factor shrinks by up to `β`. At equal speeds and `Lᵢ = L̄` it goes `2βL̄/μ → 2L̄/μ`, i.e. `Θ(√n)` fewer rounds at `ρ=2`. | None. The class here is smaller. | None | Requires per-worker `Lᵢ`. Convexity only gives `Lᵢ ≤ nL`, and with loose `Lᵢ` this bound is worse. The noise radius in the bit length can grow. |
| Repository [DistributedStrongGrowthTime](../../LongTails/Theorems/DistributedStrongGrowthTime.lean) (`efd75c78`, 2026-11-21) | Same statistical term; round factor `nL·U₀S/(μI₀)` → `A` | Up to a factor `n` in rounds | None | None | Same as the row above |

**Reduction check.** The proof inherits the support inequality, the surrogate growth and the finite-bit execution unchanged. It adds three elementary bounds in [LocallySmoothGrowth](../../LongTails/Proofs/LocallySmoothGrowth.lean):
- `∇fᵢ(z) = 0` at minimizers together with `Lᵢ`-smoothness gives `‖∇fᵢ(x)‖ ≤ Lᵢ‖x−z‖`;
- the triangle inequality bounds the smoothness of the surrogate by `Σaᵢ Lᵢ/hᵢ ≤ Sm`;
- `aᵢ² ≤ m`.

So this is a retuning of an existing schedule under an added assumption. There is no new mechanism.

A standard subset reduction is also available: the alignment lemma in [DistributedGrowthComparison](../../LongTails/Proofs/DistributedGrowthComparison.lean) followed by Malenia on the fast workers. It applies when the fast fraction exceeds `(ρ−1)/ρ`, and it beats this result in the note's first family (`O(√n log n)` vs `Θ(n log n)`). For two-speed families, the condition for a statistical gain, `ρ < nΣhᵢ²/(Σhᵢ)²`, is asymptotically the same as the condition for this reduction. I did not find a family where the result beats the best of all-worker Malenia, subset Malenia and the repository bounds polynomially.

Rennala SGD, [Tyurin, Thm 3.8](https://arxiv.org/html/2609.17483v1), does not apply because it requires local PL and strong interpolation.

**Search coverage (2026-11-23).** I read Tyurin 2609.17483v1 directly: Thms F.2 and 3.8 and Remark 2.4. That paper models no communication costs. I searched for Ringmaster/Ringleader ASGD (2501.16168, 2509.22860), "Do We Need Asynchronous SGD?" (2602.03802), Birch SGD (2505.09218) and work on strong growth with heterogeneous times. None treats per-worker smoothness under strong growth with communication costs.

The companion note's family calculations are consistent with my checks, and it acknowledges the subset reduction. Its "√n" gain is relative to the repository's own schedule, not to Malenia. I did not run the build or the audit.

**Conclusion**

**No polynomial improvement over the best applicable method is established; this mostly retunes the repository's own schedule using extra per-worker smoothness bounds.** The strongest external baseline is Malenia SGD (Tyurin, Thm F.2). Its class contains this one, and it ignores communication costs.

| equal speeds `h`, `Lᵢ ≤ L̄` | round/noiseless term | statistical term |
|---|---|---|
| Malenia | `h·L̄/μ·log(R²/ε)` | `hσ²/(nμ²ε)·log(R²/ε)` |
| GradientDiversity (repo) | `≈ 2β·h·L̄/μ·log` | `hσ²/(nμ²ε)` |
| This result | `≈ 2·h·L̄/μ·log` | `hσ²/(nμ²ε)` |

The `√n` round reduction only recovers what Malenia already achieves. It comes from the added assumption that each worker's gradient is `Lᵢ`-Lipschitz, through elementary bounds. With heterogeneous speeds, the checked gain over Malenia is `log² m`, in an accuracy window `m^(−7/4) < ε < m^(−5/4)` of the note's many-speed family. That statistical gain comes from the earlier strong-growth result. In two-speed families a fast-subset reduction beats this schedule.

The gain is real but modest and routine. It is not ruled out that some speed profile gives a polynomial advantage over every baseline, but none was found. What can be claimed is a sharper repository bound: up to `β` times fewer rounds than the earlier gradient-diversity theorem when tight `Lᵢ` are known.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
