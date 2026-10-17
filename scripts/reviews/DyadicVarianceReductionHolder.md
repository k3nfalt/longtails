# Novelty assessment: DyadicVarianceReductionHolder

[`result`](../../LongTails/Theorems/DyadicVarianceReductionHolder.lean) proves the following. Take an `L`-smooth nonconvex `f` on a Hilbert space with gap `f(x₀) − inf f ≤ Δ`. Its unbiased IID two-point same-sample oracle has variance `≤ σ²` and satisfies the mean-squared Hölder condition `E‖g(x,ξ) − g(y,ξ)‖² ≤ M‖x−y‖^{2ν}` with `ν ∈ [1/2, 1]` ([setup](../../LongTails/Setups/MeanSquaredHolderNonconvex.lean)). Under these assumptions the normalized dyadic (Fenwick-tree) difference estimator method ([algorithm](../../LongTails/Algorithms/DyadicVarianceReduction.lean)) returns a uniformly random iterate with `E‖∇f(x_out)‖ ≤ ε`.

**Complexity (pair calls, from the proved budget):**

  `O( log²(2 + LΔ/ε²) · [1 + (LΔ + σ²)/ε² + Δ M^{1/(2ν)} σ^{2−1/ν}/ε³] )`

- `L`: smoothness of `f`.
- `M, ν`: mean-squared Hölder constant and exponent.
- `σ²`: variance bound.
- `Δ`: initial gap.
- `ε`: target `E‖∇f‖`.

The tuning uses `L, M, ν, σ, Δ, ε`. At `ν = 1/2, σ = 0` the formula retains `ΔM/ε³`, because Lean evaluates `0⁰ = 1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SGD, [Ghadimi–Lan 2013](https://arxiv.org/abs/1309.5549) Cor. 2.2; tight over the bounded-variance class by [Arjevani et al.](https://arxiv.org/abs/1912.02365) v2 Thms 1, 3 (Math. Prog. 2023). Covers the full target class. | `O(1 + LΔ/ε² + LΔσ²/ε⁴)` → `O(log²(2+LΔ/ε²)[1 + (LΔ+σ²)/ε² + ΔM^{1/(2ν)}σ^{2−1/ν}/ε³])` | Leading term gains a factor `Lσ^{1/ν}/(M^{1/(2ν)}ε)`. Better when `Lσ^{1/ν}/(M^{1/(2ν)}ε) ≫ log²(2+LΔ/ε²)` and `LΔσ²/ε⁴` dominates SGD's bound. Ramp loss example: about `R/ε` when `σ ≍ R`. | None (same class) | None (same random-iterate output; SGD's `E‖∇f‖² ≤ ε²` implies `E‖∇f‖ ≤ ε`) | Needs MSH_ν, two-point oracle, and known `M, ν, σ`. Worse when `M^{1/(2ν)}ε ≳ Lσ^{1/ν}`: the proved formula then exceeds SGD's by a factor of up to `log²` times its ratio to SGD's bound. |
| SPIDER/SNVRG/STORM under MSS ([Fang et al. 2018](https://arxiv.org/abs/1807.01695), [Zhou et al. 2018](https://arxiv.org/abs/1806.07811), [Cutkosky–Orabona 2019](https://arxiv.org/abs/1905.10018); upper bounds matching Arjevani Thm 2). **Special case ν = 1 only.** | `O(σ²/ε² + LΔ/ε² + ΔL̄σ/ε³)` → at `ν=1, M=L̄²`: `log²(2+LΔ/ε²)` × same | Worse: extra `log²(2+LΔ/ε²)` at ν = 1 | MSS (ν=1) → MSH_ν, ν ∈ [1/2,1). Adds instances with kinked sample losses, e.g. ramp loss with a bounded conditional density. | None | Extra log². STORM needs no anchor batches and no knowledge of σ. |
| SPIDER recursion re-analysed under MSH_ν (my reduction check; no published source found) | `O(σ²/ε² + LΔ/ε² + Δσ√M L^{1−ν} ε^{−(4−ν)})` → this | Gains a factor `(Lσ^{1/ν}/(M^{1/(2ν)}ε))^{1−ν}`, up to log². For example, `ε^{−3.5} → ε^{−3}` at ν = ½. | None | None | Same oracle; log² loss |
| NSGD-MVR under q-WAS, [Fradin–Sadiev–Condat–Richtárik](https://arxiv.org/abs/2512.18713) v2 (31 Mar 2026) Thm 4.1 at p = 2. **Overlap only: instances that are also 1-WAS**, e.g. ramp, where `E‖Δg‖ ≤ L̄‖Δx‖`. | `O(σ²/ε² + L̄Δ/ε² + L̄Δσ²/ε⁴)` with `L̄ ≥ L` → this | On ramp (`L̄ = 2κR²`, `M = 2κR³`): `κR²Δσ²/ε⁴ → log²·κR³Δ/ε³` | Incomparable classes. MSH_ν does not imply q-WAS for ν < 1, and 1-WAS does not imply a finite MSH_{1/2} constant. | None | Their Thm 3.1 lower bound makes ε⁻⁴ tight over 1-WAS. I did not verify the note's claim that the hard instance has an ε-dependent `M`. |

**Reduction check.** Batching, SPIDER/STORM telescoping, and SCSG-style anchors give at best `ε^{−(4−ν)}` (derived above). Smoothing the sample gradient does not restore MSS without an intractable inner expectation. The new mechanism is the observation that under ν ≥ 1/2, per-level costs `J(n/2^j)M(2^jη)^{2ν}/ε²` grow geometrically, with the epoch length tied to `M(nη)^{2ν} ≈ σ²`. This mirrors Giles' MLMC case β = γ.

**Proof ancestry, not baselines:**
- tree aggregation ([Dwork et al. 2010](https://dl.acm.org/doi/10.1145/1806689.1806787); Chan–Shi–Song 2011);
- its DP use in [Arora et al. ICML 2023](https://arxiv.org/abs/2206.00846), for smooth losses;
- the nested reference points of SNVRG, which have the same multi-level structure but were analysed only under MSS;
- the normalized-step descent of [Cutkosky–Mehta 2020](https://arxiv.org/abs/2002.03305).

None of these supplies the Hölder cost calculation.

**Search coverage (2026-10-17).**
- **Searched:** arXiv, NeurIPS/ICML proceedings, and general web for Hölder or mean-squared-Hölder variance reduction, discontinuous sample gradients, MLMC for stochastic optimization, and SNVRG/STORM extensions.
- **Read:** Arjevani et al. v2 (theorem statements) and Fradin et al. v2 (Assumption 2.6, Thms 3.1, 4.1–4.4).
- **Not read in full:** SNVRG and Arora et al.; MLMC-SA papers only via abstracts or snippets.
- **Result:** no prior ε⁻³ result under MSH_ν was found.
- **Chronology:** the result was introduced in commit 91a260f on 2026-10-17, so no later work exists.
- **Companion note:** its citations check out. Its lower bound is an unformalized hand sketch that I did not verify, so I make no optimality claim.

## Conclusion

**Yes. Under mean-squared Hölder sample regularity the proved complexity is polynomially better than every applicable baseline I could find.**

The strongest applicable baseline on this class is SGD; the ε⁻³ variance-reduction methods need MSS (ν = 1), which fails for kinked losses. A direct re-analysis of SPIDER-type recursion under the Hölder condition is the next-best option:

| Method | Pair/sample calls (leading term) |
|---|---|
| SGD | `LΔσ²/ε⁴` |
| SPIDER under MSH_ν | `Δσ√M L^{1−ν} ε^{−(4−ν)}` |
| This result | `log²(2+LΔ/ε²) · ΔM^{1/(2ν)}σ^{2−1/ν}/ε³` |

The gain over SGD is the factor `Lσ^{1/ν}/(M^{1/(2ν)}ε)` minus a log² loss, which is about `R/ε` for the ramp loss. The ramp loss example shows that the class contains natural nonconvex instances with bounded data density where MSS fails. The result loses log² against STORM at ν = 1 and loses against SGD when `M^{1/(2ν)}ε ≳ Lσ^{1/ν}`. It also needs the two-point oracle and known `M, ν, σ`.

What is established is the comparison. Priority rests on a search that found no prior Hölder variance-reduction analysis; that is not proof. The estimator itself is known from tree aggregation and SNVRG, and the claimed matching lower bound is unverified. The claimable contribution is a new oracle-complexity bound, ε⁻³ up to log², for unbiased two-point oracles under mean-squared Hölder smoothness with ν ∈ [1/2, 1]. It comes from analysing a known multilevel estimator.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
