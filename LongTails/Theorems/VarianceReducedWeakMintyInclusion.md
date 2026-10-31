# Variance reduction over the full weak-Minty range

The [Lean result](VarianceReducedWeakMintyInclusion.lean) constructs the [explicit algorithm](../Algorithms/VarianceReducedWeakMinty.lean) for the [finite-sum inclusion specification](../Setups/FiniteSumWeakMintyInclusion.lean). It proves an expected squared **graph-certificate residual** bound, counting component evaluations and exact resolvent calls. The contribution is an amortized finite-sum guarantee for general nonlinear weak-Minty inclusions throughout the range `ρL < 1`. It is not a new deterministic corrected-proximal method, an optimality result, or a claim of improvement in every parameter regime.

## Problem and oracle

Let `F = (1/n) Σᵢ Fᵢ`, with `n ≥ 1`, on a real Hilbert space. All finite-dimensional Euclidean spaces are covered. Assume

- `‖F(x) − F(y)‖ ≤ L‖x − y‖`, with `L > 0`;
- `(1/n) Σᵢ ‖Fᵢ(x) − Fᵢ(y)‖² ≤ Λ²‖x − y‖²`, with `Λ ≥ L`;
- `A` is monotone and the oracle supplies its exact resolvent for every positive step size;
- there exists `x⋆` with `−F(x⋆) ∈ A(x⋆)`, `‖x₀ − x⋆‖ ≤ R`, and, for **every** `v ∈ A(y)`,
  `⟨F(y)+v, y−x⋆⟩ ≥ −ρ‖F(y)+v‖²`, where `0 ≤ ρL < 1`.

The resolvent is specified by graph membership and monotonicity, which establish nonexpansiveness and uniqueness. Availability at every positive step is the usual maximal-monotone resolvent access. Component maps need not be monotone, interpolate the root, or have uniformly bounded values. No bounded domain, bounded stochastic variance, pairwise cohypomonotonicity, or extra differentiability is assumed. The average Lipschitz constant `L` is distinguished from the component mean-square constant `Λ`: the admissible weak-Minty range uses the former.

The public input consists of `n,L,Λ,ρ,R,ε,x₀` and the ambient space; `ε > 0`. The root, component maps, and graph are not public input. Each query either evaluates one specified `Fᵢ(x)` or requests one resolvent evaluation. Both count as one oracle call. This is a deterministic finite-sum oracle; all randomness is internal to the algorithm. The algorithm law is an explicit finite uniform product, including separate coordinates for each batch, each snapshot selection, and final output selection. It places no finite-sample-space restriction on the objective class.

These are established assumptions, separately and together in finite-sum weak-Minty research. The graph weak-Minty condition and full range are those of Pethick–Mavrothalassitis–Cevher's [accepted ICLR 2025 paper, Theorems 5.3, 5.5 and 6.1](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), after changing their sign convention. Finite-sum mean-square component regularity appears in [Tran-Dinh–Nguyen-Trung, arXiv:2603.15576v2](https://arxiv.org/html/2603.15576v2). The new theorem does not assume their small weak-Minty range. Knowing valid parameter bounds permits explicit tuning; parameter-free adaptation is not claimed.

## Algorithm, output, and proved cost

Write `δ = 1−ρL ∈ (0,1]`, `r = Λ/L`, and `H = L²R²/ε²`. Define

`Wexact = n(1 + H/δ²)`,

`Wbatch = [n + r² + (√n r + r²)H/δ²]/δ³`.

Use exact evaluations when `Wexact ≤ Wbatch`; otherwise use batched differences. Set

- `η = (2−δ)/(2L)`, `s = δ/(2−δ)`;
- `q = 2` for the exact branch, otherwise `q = max{2,⌈√n/r⌉}`;
- `b = 1` for the exact branch, otherwise `b = ⌈524288 q r²/δ³⌉`;
- `J = 1 + ⌈(32/δ) log(65536/δ²)⌉`;
- `M = max{1,⌈128H/(δ²q)⌉}` and `p = 1/q`.

Initially `x=w=x₀`. Each epoch computes `F(w)` using `n` component calls and holds `w` fixed for `q` steps. At each step, set `z=(1−p)x+pw` and `y₀=z`. In the batch branch, each independent estimator is

`g(y)=F(w)+(1/b)Σℓ[Fᵢℓ(y)−Fᵢℓ(w)]`.

The exact branch uses `g(y)=F(y)`. Perform `J` updates

`yⱼ₊₁ = (I+ηA)⁻¹(z−ηgⱼ(yⱼ))`.

Keep the last graph certificate `v=(z−yⱼ₊₁)/η−gⱼ(yⱼ)`. With a **fresh independent** estimator at the final `y`, update `x=z−sη(gfresh(y)+v)`. Store `(y,v)`. After the epoch, keep the final `x` and replace `w` by an independent uniform selection among that epoch's `q` updated `x` values. After `M` epochs, return an independent uniform selection `(Y,V)` among all `qM` stored graph certificates.

The theorem proves measurability, integrability, `V ∈ A(Y)` almost surely, and

`∫ ‖F(Y(ω))+V(ω)‖² dP(ω) ≤ ε²`.

The exact plan uses

`M [n + q(c + (1+c)J)]`

oracle calls, where `c=n` in the exact branch and `c=2b` in the batch branch. This includes all snapshot evaluations, both sides of every component difference, every Picard resolvent, and the final independent correction. Selection needs no oracle calls. The repository framework executes with the following single explicit budget; any calls after the plan is complete leave the output unchanged and are included in that budget:

`⌈2⁴² [log(2/δ)/δ] min{Wexact,Wbatch}⌉`.

The public Lean budget expands every abbreviation in the setup parameters. The large universal constant is conservative and explicit; neither a practical speedup nor favorable finite constants are claimed. In asymptotic notation the new branch costs

`O(log(2/δ)[(n+r²)δ⁻⁴ + (√n r+r²)Hδ⁻⁶])`.

The fallback costs `O(n log(2/δ)[δ⁻¹+Hδ⁻³])`. The `max{1,…}` epoch count and startup terms remain present when `R=0` or the requested accuracy is coarse.

## New mechanism and proof

The deterministic corrected-proximal energy inequality is already present in the ICLR 2025 analysis. The new part couples a noisy inner Picard solve with persistent finite-sum snapshots and an outer snapshot-energy telescope.

For `h=1−η²L²`, the batch variance coefficient is `ν=Λ²/b` (zero for exact evaluations). The inner proof bounds the scaled certificate error by

`E‖η(F(y)+v)−(z−y)‖² ≤ (s²/32)E‖z−y‖² + (256η²ν/h)‖z−w‖²`.

The second term cannot be discarded or assumed uniformly small. Negative momentum `z=(1−p)x+pw` generates a matching `p(1−p)‖x−w‖²` energy decrease. The stated batch size lets this decrease absorb the snapshot-relative inner error and fresh-correction variance. Independence of the correction sample eliminates the problematic bias-distance cross term. This yields the actual-step inequality

`E‖x⁺−x⋆‖² + (s²η²/16)E‖F(y)+v‖² ≤ (1−p)‖x−x⋆‖²+p‖w−x⋆‖²`.

Uniform snapshot refresh with `qp=1` makes the potential `(1−p)‖x−x⋆‖²+‖w−x⋆‖²` telescope across epochs. Its initial value is at most `2R²`, giving the output residual bound `32R²/(s²η²qM)=128L²R²/(δ²qM)`. Banach's contraction theorem supplies the exact proximal fixed point only inside the proof; the algorithm never queries that point or the root.

Ordinary batching of a bounded-variance full-range stochastic guarantee does not produce this amortization: this setup has no uniform variance bound, and a generic stochastic `ε⁻⁴` guarantee remains insufficient. Running a separate variance-reduced proximal solver with a new full snapshot for every outer step pays `n` at each such step. The negative-momentum finite-sum analysis of [Alacaoglu–Malitsky, accepted COLT 2022](https://proceedings.mlr.press/v178/alacaoglu22a.html) requires monotonicity and a step linked to the refresh probability. It cannot simply be substituted for weak Minty, which controls the graph only relative to a root. The coupled snapshot-relative error bound and epoch potential are what avoid these two costs. No new restriction is added to make those inequalities assumptions of the setup; they are proved from the algorithm and the stated regularity.

The formal proof can be traced through [Sampling](../Proofs/VarianceReducedWeakMintySampling.lean) (`estimator_error_sum_zero`, `estimator_error_variance`), [Inner](../Proofs/VarianceReducedWeakMintyInner.lean) (`picard_relative_error`), [Outer](../Proofs/VarianceReducedWeakMintyOuter.lean) (`stepPlan_descent`), and [Epoch](../Proofs/VarianceReducedWeakMintyEpoch.lean) (`outputPlan_residual_bound`). [Tuning](../Proofs/VarianceReducedWeakMintyTuning.lean) discharges their numerical hypotheses, [Budget](../Proofs/VarianceReducedWeakMintyBudget.lean) proves `total_cost`, [Execution](../Proofs/VarianceReducedWeakMintyExecution.lean) connects the query plan to `execute` and graph membership, and [Convergence](../Proofs/VarianceReducedWeakMintyConvergence.lean) proves `algorithm_success` with the explicit probability measure. These are supporting lemmas for the single public convergence theorem.

## Closest guarantees and improvement regimes

1. **Full-range deterministic baseline.** The accepted [ICLR 2025 paper](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), Theorems 5.3/5.5, 6.1, Corollary 6.3 and Appendix D, gives a corrected proximal algorithm for `ρL<1`. Specializing its tolerance to `s/2` gives `K=⌈16L²R²/(δ²ε²)⌉` outer iterations and `j=⌈(2/δ)log(8/δ)⌉` Picard iterations, at cost `K[n(j+1)+j]`. Its energy sum also supports the same uniformly sampled certificate criterion, without extra full evaluations. Its printed accuracy parameter is squared residual accuracy, so it must be replaced by our `ε²`. The fallback matches its parameter orders, not its constants. For fixed `δ` and bounded `r`, the new accuracy-dependent component cost scales as `√n` rather than `n`.

2. **Restricted-range finite sums.** [Tran-Dinh–Nguyen-Trung, arXiv:2603.15576v2, revised September 9, 2026](https://arxiv.org/html/2603.15576v2), gives variance-reduced weak-Minty guarantees with a substantially smaller admissible product (`ρL<1/(24√2)` in the compared analysis), with `n^(2/3)ε⁻²` unbiased-estimator and `n^(3/4)ε⁻²` biased-estimator orders. It is a preprint in this comparison. Our full-range theorem covers nonlinear instances excluded by that restriction. Different margin factors must be retained when comparing costs.

3. **Full-range stochastic access.** [Alacaoglu–Kim, accepted ICML 2026](https://proceedings.mlr.press/v306/alacaoglu26a.html), [arXiv:2602.05531v1](https://arxiv.org/abs/2602.05531v1), reaches the full range using multilevel Monte Carlo under its stochastic bounded-growth model, with `ε⁻⁴` dependence. This is not an interchangeable finite-sum `√n ε⁻²` result. [Pethick et al., ICLR 2023 preprint version arXiv:2302.09029](https://arxiv.org/abs/2302.09029) uses paired mean-square regularity but a half-range condition and stochastic `ε⁻⁴` cost. Pairwise cohypomonotone accelerated results impose a stronger condition than the one-point graph inequality here.

4. **A disputed restricted-range comparison.** [Alizadeh–Yazdandoost Hamedani–Jalilzadeh, arXiv:2405.10735v3](https://arxiv.org/abs/2405.10735v3), claims a particularly favorable weak-Minty finite-sum rate. In the accessible version, the estimator-bias cancellation between Lemma 7 equations (32) and (30), and a quadratic-root bound in Lemma 8, do not justify the stated estimate; initialization is also ambiguous. A final journal article exists at [DOI 10.1080/10556788.2025.2612351](https://doi.org/10.1080/10556788.2025.2612351), *Optimization Methods and Software* 41(1), 226–255 (2026), but its full text was inaccessible during both investigations. We cannot assert that its final proof retains those problems. Consequently this note does **not** claim a settled best-known rate in every restricted weak-Minty regime. The full-range contribution is distinguished from the accessible paper's restricted range. This remains an explicit literature-access limitation.

Relative to the deterministic baseline's accuracy term, the new bound has ratio, up to universal constants and comparable logarithms,

`(1+r²/n)/(Hδ) + r/(√n δ³) + r²/(nδ³)`.

Thus sufficient asymptotic improvement conditions are `n ≫ r²δ⁻⁶` and `H ≫ δ⁻¹(1+r²/n)`. These conditions describe where the guarantee improves; they are **not assumptions in the setup**. Small margins, large component heterogeneity, or coarse accuracy can favor the exact branch. No uniform superiority as `δ→0`, sharp margin dependence, or lower bound is proved. Monotone special cases can have substantially faster known residual guarantees; this result is for the larger weak-Minty class.

## A nonlinear family genuinely outside the half-range

The motivation is not limited to scalar or quadratic operators. The published **GlobalForsaken** constrained game in [Pethick et al., accepted ICLR 2022, Example 4 and Appendix C.3](https://openreview.net/pdf?id=2_vhkAMARk), also accessible as [arXiv:2302.09831v1](https://arxiv.org/html/2302.09831v1), provides a concrete source. The following scaling and bounds are our own calculations, not constants attributed to that paper.

Let `C=[−4/3,4/3]²`, `ψ(t)=2t⁶/21−t⁴/3+t²/3`, and

`φ(x,y)=xy+(4/3)ψ(x)−(4/3)ψ(y)`.

On `C`, use its saddle operator `F(x,y)=((4/3)ψ′(x)+y,(4/3)ψ′(y)−x)` and `A=N_C`. Extend the oracle globally by `F(P_C z)`; this agrees with the saddle operator on the feasible set, but is not claimed to be a saddle gradient outside it. The graph of `N_C` is empty outside `C`.

The origin is a Nash equilibrium because `ψ(t)≥0`. On the box, write `F(z)=(J+D)z`, with the unit skew matrix `J` and diagonal entries of `D` in `[−4/27,8/9]`. With `ρ=36/211`, the matrix `D+ρ(J+D)ᵀ(J+D)` is positive semidefinite: its determinant factors as

`[c₁+ρ(1+c₁c₂)][c₂+ρ(1+c₁c₂)]`,

and both factors are nonnegative since `c₁c₂≥−32/243`. At an active box coordinate, the outward component of `z+2ρF(z)` is positive, so adding **any** normal-cone vector preserves the graph weak-Minty inequality. The derivative interval `ψ″∈[−11/15,1466/567]` gives the global Lipschitz upper bound `L=35/9`, including the projection extension. Hence `ρL=140/211<1`.

This is genuinely beyond the half-range even after retuning constants: the diagonal point `x=y=√(7/6)` forces every weak-Minty constant to be at least `108/745`, while an interior limiting Jacobian column forces every Lipschitz constant to exceed `7/2`. Their product is therefore at least `378/745>1/2`. It also has no finite pairwise cohypomonotonicity constant: an interior Jacobian with one diagonal entry `−44/45` and the other approaching `45/44` from above has a negative eigenvalue tending to zero. The pairwise inequality would require an unbounded constant.

For heterogeneous finite sums, replace coefficients `4/3,1` by `aᵢ,bᵢ` with those averages and add constant vectors `dᵢ` of average zero. Each component has Lipschitz constant at most `(1466/567)|aᵢ|+|bᵢ|`; their root-mean-square supplies `Λ`. The offsets permit noninterpolation. Independent blocks give arbitrarily large even dimensions with interacting coordinates within each block and no additional dimension factor in the theorem. These calculations illustrate covered scope; the Lean theorem does not assume this example or restrict instances to such blocks. The example certification in this note is mathematical exposition, not an additional formalized theorem.

## Research coverage and limits

Both agents independently surveyed current primary results before selecting this direction, using UTC October 22–23, 2026. Coverage included official ICML 2026/2025, ICLR 2026/2025, and publicly available NeurIPS 2026/2025 material (also 2024 where relevant), targeted arXiv submissions and revisions over roughly two years, and foundational citations. This was a targeted literature investigation, not exhaustive enumeration. Conference status was checked against official proceedings or OpenReview; preprints are identified above. The inaccessible final journal version is recorded explicitly. The proof and specification do not certify novelty or conference acceptance: those require the independent review alongside the exact Lean contents.
