# DistributedGradientDiversity: novelty assessment

[`result`](../../LongTails/Theorems/DistributedGradientDiversity.lean) gives an elapsed-time bound on the same [star-network setup](../../LongTails/Setups/DistributedMeanStrongGrowth.lean) as [DistributedStrongGrowthTime](../../LongTails/Theorems/DistributedStrongGrowthTime.lean). The setup has convex `fᵢ`, an `L`-smooth average `F` with `μ`-quadratic growth, mean-squared strong growth `Σᵢ‖∇fᵢ‖² ≤ nρ‖∇F‖²`, and unbiased worker oracles with variance at most `σ²`. Under these assumptions the [re-tuned weighted two-phase SGD](../../LongTails/Algorithms/GradientDiversitySgd.lean) returns `X` with `E dist(X,S)² ≤ ε`.

**Bound.** The parameters are as follows: `hᵢ` is worker `i`'s time per sample, `H = maxᵢhᵢ`, `S = Σᵢ1/hᵢ`, `ℓ` is the link latency, `b` the per-bit time, `d` the dimension, and `R` the distance from `x₀` to a minimizer. Let `u` minimize `Σuᵢ²/hᵢ` subject to `Σuᵢ = n` and `Σuᵢ² ≤ nρ`. This profile is defined implicitly and has no closed form. Write `I₀ = Σuᵢ²/hᵢ`, `U₀ = maxᵢuᵢ`, `W₀ = maxᵢuᵢ/hᵢ`, and `β = min(n, 1+√(n(ρ−1)))`. Then the Lean budget gives (using `σU/M ≤ σ/(Lβ)` inside the bit-length logarithm)

`T = O( σ²/(μ²I₀ε) + (L·max(βU₀S, nW₀)/(μI₀))·log(2+R²/ε)·[H + ℓ + b(1 + d·log(2+d+L·max(βU₀S,nW₀)/(μI₀)+(R²+σ²/(L²β²))/ε))] )`.

The round factor satisfies `2L/μ ≤ A ≤ 2nL·U₀S/(μI₀)`, using `I₀ ≤ nW₀` and `nW₀ ≤ nU₀S`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository [DistributedStrongGrowthTime](../../LongTails/Theorems/DistributedStrongGrowthTime.lean). Prior, but only by days: both come from the 2026-11 history, and this theorem was added in commit `a378bdce` on 2026-11-23. Identical setup. | `σ²/(μ²I₀ε) + (6nLU₀S/(μI₀))·log(1+R²/ε)·[H+ℓ+b(64+d·log(3+d+A_old+(R²+σ²/(9n²L²))/ε))]` → `T` | The round factor drops by `3n/max(β, nW₀/(U₀S))`. For equal speeds and `ρ = 2`, this is `n → √n`, so `Θ(n log n) → Θ(√n log n)` at fixed other parameters. There is no gain when `nW₀/(U₀S) ≈ n`, for example at `ρ = 1` with one very fast worker. | None (same class) | None | The statistical term is unchanged. The bit-length log can grow because the noise radius goes from `σ/(3nL)` to `σ/(Lβ)`. |
| Malenia SGD, [Tyurin, arXiv 2609.17483v1](https://arxiv.org/abs/2609.17483) (15 Sep 2026, only version), Thm F.2. Its class (convex `fᵢ`, smooth PL `F`) contains this class up to constants. Communication is free. | `[H·L/μ + (Σhᵢ)σ²/(n²μ²ε)]·log(R²/ε)` → `T` at `ℓ=b=0` | Statistical term: as in the earlier theorem's review, it gains a factor `I₀Σhᵢ/n²` and a log under heterogeneous speeds. Noiseless term: still worse, `≥ 2HL/μ` and `= 2βHL/μ·log` at equal speeds. The gap shrinks from a factor of at least `n` to `β`. | None: this class is a subclass of Malenia's; it is the same class as the earlier repository theorem | None | Requires known `ρ` and speeds. The noiseless term is worse by a factor of up to `β` (`= 1` only at `ρ = 1`). |

**Mechanism and reduction check.** The new ingredients, in [GradientDiversityGeometry](../../LongTails/Proofs/GradientDiversityGeometry.lean), are elementary sharper constants fed into the existing scheduler:
- Centering plus Cauchy–Schwarz gives `‖∇fᵢ(x)‖ ≤ Lβ‖x−z‖`.
- The weighted Bregman sum gives smoothness `nLμW₀` for the surrogate.

The growth certificate, finite-bit protocol and two-phase analysis are inherited unchanged from the earlier repository proof. I checked the scaling family from the earlier note: `n = 2m`, `m` unit-time workers and times `1,…,m`, `ρ = 2`, taking the note's `I₀ = Θ(log m)` and `U₀ ≤ 8` as given. With `ε = m^(−11/4)` and fixed other parameters:

| | bound |
|---|---|
| New | `Θ(m^(11/4)/log m)` |
| Earlier theorem | `Θ(m³)` |
| Malenia | `Θ(m^(11/4) log m)` |

Against the better of the two baselines this is only a `log² m` gain. I did not verify a polynomial gain over `min(Malenia, earlier theorem)`.

**Search coverage (2026-11-23).** I read Tyurin 2609.17483v1 (Thm F.2, Thm 3.8, Remark 2.4). I also searched for Ringmaster/Ringleader ASGD, "Do We Need Asynchronous SGD?" (2602.03802), and gradient-diversity work (Yin et al., 1706.05699), and found no time bound under strong growth with heterogeneous speeds. The OpenReview revision of Tyurin's paper was not checked. The companion note's claims (`A/A_old = D/(3n)`, the `√n` example) match my derivation. I did not run the build or audit.

**Conclusion**

**The improvement is real but small: it cuts the round/communication term of the repository's own result from order `n` to `√n`.** The statistical term is unchanged, and on the noiseless term the method remains slower than Malenia SGD's.

| equal speeds `h`, `ρ = 2` | noiseless/round term |
|---|---|
| Malenia (free communication) | `h(L/μ) log(R²/ε)` |
| Earlier repository theorem | `≈ 6n·h(L/μ) log` |
| This result | `≈ 2√n·h(L/μ) log` |

The gain matters only at moderate accuracy, where the round term dominates the shared statistical term `σ²/(μ²I₀ε)`. At small `ε` with `σ > 0`, the two repository bounds coincide. In the heterogeneous family I checked, the advantage over the better of Malenia and the earlier theorem is only a `log² m` factor.

Historically, this sharpens a bound posted days earlier in the same repository. The class-level novelty (strong growth with heterogeneous speeds) belongs to that earlier result. The new step uses two elementary estimates, a centered gradient bound and a weighted Bregman bound, so the contribution is modest and routine.

What can be claimed is a tighter constant-in-`n` calibration of the clipping and step size: the earlier theorem's round count improves by a factor of up to `n/β`, but no new class and no advantage over full-batch/Malenia rounds is established.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
