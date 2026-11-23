# DistributedStrongGrowthTime: novelty assessment

[`result`](../../LongTails/Theorems/DistributedStrongGrowthTime.lean) gives an elapsed-time bound for the star-network [setup](../../LongTails/Setups/DistributedMeanStrongGrowth.lean). The local functions `fᵢ` are convex, the average `F` is `L`-smooth with `μ`-quadratic growth, and the mean-squared strong-growth condition `Σᵢ‖∇fᵢ‖² ≤ nρ‖∇F‖²` holds. Each worker's oracle is unbiased with variance at most `σ²`. Under these assumptions the [weighted two-phase SGD](../../LongTails/Algorithms/DistributedGrowthSgd.lean) returns `X` with `E dist(X,S)² ≤ ε`.

**Bound.** Here `hᵢ` is worker `i`'s time per sample, `ℓ` the link latency, `b` the per-bit time, `d` the dimension, and `R` the distance from `x₀` to a minimizer. Define

`I = min{Σᵢ aᵢ²/hᵢ : Σᵢ aᵢ = n, Σᵢ aᵢ² ≤ nρ}`,

with minimizer `u` and `u_max = maxᵢ uᵢ`. The `least_energy` lemma and its feasibility proof show that the Lean scalar construction attains this minimum. With `A = nL·u_max·(Σᵢ1/hᵢ)/(μI)`, the proved deadline is

`T = O( σ²/(μ²εI) + A·log(2+R²/ε)·[maxᵢhᵢ + ℓ + b(1 + d·log(3+d+A+(R²+σ²/(n²L²))/ε))] )`.

These quantities satisfy `n²/Σhᵢ ≤ I ≤ Σ1/hᵢ`, `u_max ≥ 1`, and hence `A ≥ nL/μ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Malenia SGD, [Tyurin–Richtárik, NeurIPS 2023](https://arxiv.org/abs/2305.12387), as restated in [Tyurin, arXiv 2609.17483v1 (15 Sep 2026)](https://arxiv.org/abs/2609.17483v1), Thm F.2. Its class (convex `fᵢ`, `L`-smooth PL `F`) contains this class up to constants, since convexity plus quadratic growth gives PL. Communication is free. | `[maxᵢhᵢ·L/μ + (Σhᵢ)σ²/(n²μ²ε)]·log(R²/ε)` → `T` at `ℓ=b=0` | The statistical term improves by the factor `I·Σhᵢ/n²` times a log. This factor is `>1` exactly when speeds differ and `ρ < nΣhᵢ²/(Σhᵢ)²`. Example: `n` fixed, `n−1` workers with `h=1`, one with `h=H`, `ρ=2`, `ε=H⁻²`. Then `I ≥ (n−√(2n))²/(n−1)`, and the bound improves from `Θ(H³log H)` to `O(H²)`. | Gives a positive upper bound for the pointwise class `maxᵢ‖∇fᵢ‖² ≤ 2‖∇F‖²`, which Tyurin's Remark 2.4 leaves as an open question. | None. Both use known parameters, and both give `E dist²` for the returned iterate. | The noiseless term is worse by at least a factor `n` (`n·u_max·Σ(1/hᵢ)/I ≥ n`). This loss decides the comparison when `ε ≳ σ²/(nμL·u_max·maxᵢhᵢ·Σ1/hᵢ)`. For `ρ ≥ nΣhᵢ²/(Σhᵢ)²` there is no statistical gain beyond a log. |
| Rennala SGD under strong interpolation plus local PL, Tyurin 2609.17483v1, Thm 3.8 (prior). Applies only on the overlap. | `min_m(m⁻¹Σ_{i≤m}1/hᵢ)⁻¹(L_max/μ_loc + σ²/(mεμ_loc²))·log(R²/ε)` → `T` | Not comparable: neither class contains the other. On `fᵢ = aᵢx²/2`, Thm 3.8 uses `μ_loc = minᵢaᵢ`, while this result uses `μ = mean(aᵢ)` and pays through `ρ`. | Removes per-worker PL, per-worker smoothness, and the requirement that minimizer sets coincide. Covered example: a fraction `p ≤ 1/8` of workers holds `μ[(vᵀx)²/2 − log cosh(vᵀx)]`, which has a hyperplane of minimizers and quartic transverse growth, so local PL fails. The rest hold `(F−pg)/(1−p)` with `F = μ‖x‖²/2 + c[log cosh(vᵀx) + log cosh(wᵀx)]`. I checked convexity and pointwise `ρ ≤ ((1+p)/(1−p))² < 2`. | None | Requires `ρ` and pays for a bounded `ρ`. The noiseless term is `≥ n` times Rennala's when `ρ=1` (identical functions). |
| Repository: [DistributedWeightedInterpolation](../../LongTails/Theorems/DistributedWeightedInterpolation.lean) | Arithmetic-type statistical term when only aggregate smoothness is known (per the companion note; not rederived) → `T` | Statistical term improves in the regime above | Per-worker absolute smoothness → mean-square strong growth | None | Same protocol and cost structure |

**Reduction check and ancestry.** The result is not a substitution into Thm 3.8 or Malenia. Thm 3.8 needs local PL, which fails in the example above, and Malenia's unbiased aggregation pays an arithmetic-mean cost. The new step is the support inequality for signed, ellipsoid-constrained worker projections (`support` and `weighted_gap`). It shows that `G = Σ(uᵢ/hᵢ)fᵢ` keeps the minimizer set `S` and grows at rate `I`. The repository's finite-bit two-phase protocol and slope-comparison arguments ([Daniilidis–Drusvyatskiy](https://arxiv.org/abs/2303.16277)) supply only the remaining analysis. The lower bound `Ω(σ²/(μ²εI))` in the note is prose only and not formalized. It adapts Tyurin's Gaussian two-point construction, and its KL calculation looks correct to me.

**Search coverage (2026-11-21).** I read arXiv 2609.17483v1 in full text: Thms 2.3, 3.2, 3.6–3.8, F.2, and Remark 2.4. I also searched Ringleader/Ringmaster ASGD, Rescaled ASGD (NeurIPS 2026), "First Provably Optimal ASGD" (2601.02523), and work on strong growth and interpolation; none treats strong growth with heterogeneous worker times. I could not access the November OpenReview revision of Tyurin's paper, so it may address Remark 2.4. The companion note's citations match the sources I checked.

**Conclusion**

**Yes: for heterogeneous worker speeds and small ε, this is a better time bound on a class that Tyurin left open.** The strongest applicable baseline is Malenia SGD, which pays the arithmetic mean of worker times. Tyurin's lower bounds show this cost is unavoidable under similarity, weak interpolation, or strong interpolation alone. His Remark 2.4 explicitly asks whether the pointwise strong-growth class allows a better rate.

| | statistical term | noiseless term |
|---|---|---|
| Malenia | `σ²Σhᵢ/(n²μ²ε)·log(R²/ε)` | `maxhᵢ·(L/μ)·log` |
| This result | `σ²/(μ²εI)`, with `I ≥ n²/Σhᵢ` | `≥ n·maxhᵢ·(L/μ)·log` |

The gain can be polynomial: with one worker `H` times slower, the bound improves from `H³log H` to `H²` at `ε = H⁻²`. The covered example satisfies every remaining assumption but has neither local PL nor shared local minimizer sets, so Tyurin's Theorem 3.8 does not apply to it. The result loses when the noiseless term dominates, where it is at least a factor `n` worse. When `ρ` is large it reduces to Malenia's rate. Nothing is gained for identical speeds.

The comparison establishes the gain. Priority is supported by Tyurin's paper, which appeared two months earlier and states this question as open, but the November revision of that paper is unchecked. The matching statistical lower bound is plausible but not formalized. What can be claimed is a new elapsed-time upper bound for convex workers under mean-squared strong growth, with a speed-and-ρ-dependent information quantity `I`, partially answering Tyurin's Remark 2.4.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
