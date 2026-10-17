# ε⁻³ variance reduction under mean-squared Hölder smoothness (dyadic difference estimator)

## Summary

Variance reduction (SPIDER, STORM, PAGE) reaches an ε-stationary point of a smooth nonconvex
expectation `F(x) = E_ξ f(x, ξ)` with `O(ε⁻³)` stochastic gradients instead of SGD's `Θ(ε⁻⁴)`. The
improvement relies on **mean-squared smoothness** (MSS) of the sample gradients:
`E‖g(x,ξ) − g(y,ξ)‖² ≤ L̄²‖x − y‖²`. MSS fails for one of the most common situations in practice:
sample losses with kinks, such as ramp, truncated-ℓ₁, quantile and hinge losses, and ReLU
features. There the population objective `F` is smooth, because the data have a bounded density,
but the sample gradients jump.

For such losses the natural regularity is a **mean-squared Hölder** condition of order ν:

  `E‖g(x,ξ) − g(y,ξ)‖² ≤ M ‖x − y‖^{2ν}`,  with ν = 1/2 for kinks under a bounded density.

ν = 1 is exactly MSS.

**Main result.** For every ν ∈ [1/2, 1], a normalized method driven by a dyadic (Fenwick-tree)
difference estimator returns `x_out` with `E‖∇F(x_out)‖ ≤ ε` after

  `⌈800 (1 + log₂(2 + 16LΔ/ε²))² (1 + (LΔ + σ²)/ε² + Δ M^{1/(2ν)} σ^{2−1/ν}/ε³)⌉`

two-point oracle calls, i.e. `Õ(LΔ/ε² + σ²/ε² + Δ M^{1/(2ν)} σ^{2−1/ν} ε⁻³)`.
- At ν = 1 this is the optimal STORM/SPIDER rate `ΔL̄σε⁻³`, up to the log² factor.
- At ν = 1/2 it is `Õ(ΔM ε⁻³)`, which does not depend on σ.

The ε⁻³ exponent holds for every ν ≥ 1/2. Every previously available method gets ε⁻⁴ or ε⁻³·⁵ on
these instances; see the comparison below. The ε⁻³ exponent is the optimal one: a re-scaled
Arjevani et al. construction gives a matching lower bound, sketched below.

## Setup

[`LongTails/Setups/MeanSquaredHolderNonconvex.lean`](../Setups/MeanSquaredHolderNonconvex.lean)
(`LongTails.Setups.MeanSquaredHolderNonconvex.spec`).

- **Space.** `E` is a real, complete inner-product space with Borel σ-algebra and second-countable
  topology. This covers ℝ^d of arbitrary dimension.
- **Objective.** `f : E → ℝ` is differentiable, with an `L`-Lipschitz gradient, and
  `f(x₀) − f(x) ≤ Δ` for all `x`.
- **Oracle.** IID samples `ξ_k ∼ p`, using the repository's `IID` structure. One call with query
  `(x, y)` returns `(g(x, ξ_k), g(y, ξ_k))`, i.e. two stochastic gradients on the same sample. This
  is the standard STORM/SPIDER two-point model. `g` is jointly measurable and integrable.
- **Assumptions (all `x, y`):**
  - unbiasedness: `∫ g(x,ω) dp = ∇f(x)`;
  - bounded variance: `∫ ‖g(x,ω) − ∇f(x)‖² dp ≤ σ²`;
  - **MSH_ν:** `∫ ‖g(x,ω) − g(y,ω)‖² dp ≤ M ‖x − y‖^{2ν}`, with `1/2 ≤ ν ≤ 1` and `M ≥ 0`.
- **Accuracy criterion.** `E‖∇f(x_out)‖ ≤ ε`. The expectation is over the algorithm's seed, which
  selects a uniformly random iterate, and all oracle samples.
- **Cost.** Number of oracle calls. Each call is one sample and two gradient evaluations.

Bounded variance, unbiasedness and L-smoothness are the standard assumptions of the SGD and STORM
literature (Ghadimi–Lan 2013; Arjevani et al. 2019, eqs. (2)–(4)). The single new assumption is
MSH_ν, which replaces MSS.

### Where MSH_ν comes from

**Provenance.** L²(P)-Hölder conditions on increments of sample (sub)gradients, of order ½ for
indicator-type discontinuities under a bounded density, are classical in M-estimation and nonsmooth
stochastic approximation. Examples are the L²-continuity conditions in van der Vaart–Wellner
(*Weak Convergence and Empirical Processes*, 1996, §3.2) and Kim–Pollard (1990, *Ann. Statist.*), and
the Hölder-type increment conditions of multilevel Monte Carlo for discontinuous payoffs (Giles,
*Acta Numerica* 2015, β = 1/2). To our search, MSH_ν has not been used as an oracle-complexity
assumption for nonconvex variance reduction. It is new in that role, not as a regularity
condition.

**Example (nonconvex, coordinates coupled, dimension-free constants).** Robust regression or
classification with the ramp (truncated-hinge) loss, `ψ(r) = min(1, max(0, r))` (Collobert et al.,
ICML 2006):

  `f(x) = E ψ(b − ⟨a, x⟩)`,  with `‖a‖ ≤ R` a.s. and the conditional density of `b` given `a` at
  most `κ`.

Here `g(x,ξ) = −ψ′(b − ⟨a,x⟩) a`, with `ψ′ ∈ {0, 1}`.
- **MSH_{1/2}.** `g(x,ξ) ≠ g(y,ξ)` only if a kink (`r = 0` or `r = 1`) lies between `b − ⟨a,x⟩`
  and `b − ⟨a,y⟩`. Given `a`, that happens on a set of `b` of length at most `2|⟨a, x − y⟩|`, hence
  with probability at most `2κR‖x − y‖`. Since `‖g(x) − g(y)‖² ≤ R²`, we get
  `E‖g(x) − g(y)‖² ≤ 2κR³ ‖x − y‖`: MSH_{1/2} with `M = 2κR³`.
- **Smoothness and variance.** `∇f(x) = −E[a·P(0 < b − ⟨a,x⟩ < 1 | a)]` is `2κR²`-Lipschitz, and
  `σ² ≤ R²`.
- **Failure of MSS.** If the conditional density is bounded below by `κ₀ > 0` near the kinks, then
  `E‖g(x) − g(y)‖² ≥ c‖x − y‖` for small `x − y` along directions with `E|⟨a, x−y⟩| > 0`. MSS then
  fails for every `L̄`.
- **More examples.** The same argument covers truncated-ℓ₁/Tukey-type piecewise-linear residual
  losses, quantile (pinball) losses and two-sided ramps. Losses `|r|^q` with `q ∈ (1, 3/2)` give
  ν = q − 1/2. A ReLU feature layer `max(0, ⟨w, z⟩)` on data with bounded density also has kinks,
  but needs a bounded parameter domain or a margin for global constants. We do not use it as a
  headline example.

**Explicit exclusions.**
- **Finite sums and empirical distributions** violate MSH_ν for every ν > 0: a finite sample has
  no density. The result is about streaming / population-risk optimization, or data with continuous
  noise, e.g. Gaussian label or feature augmentation, which restores a bounded density. It does not
  cover the finite-sum training regime that variance reduction is often used for.
- **Unbounded densities near kinks** are excluded.

## Algorithm

[`LongTails/Algorithms/DyadicVarianceReduction.lean`](../Algorithms/DyadicVarianceReduction.lean)
(`OracleTemplate.DyadicHolder.dyadicVR`).

Iterations `k = 0, …, K` take normalized steps `x_{k+1} = x_k − η d_k/‖d_k‖`. Let `n = 2^J` be the
epoch length and `t = k mod n` the position within the epoch.
- **Anchor (`t = 0`).** `d_k` is the mean of `b_A` fresh samples of `g(x_k, ·)`.
- **Otherwise.** Let `j = v₂(t)` (the 2-adic valuation) and `p = k − 2^j`, the Fenwick
  predecessor. Then
  `d_k = d_p + (1/b_j) Σ_{i ≤ b_j} [g(x_k, ξ_i) − g(x_p, ξ_i)]`,
  using fresh samples and pair queries.

The output is `x_τ`, with `τ` uniform on `{0, …, K}`.

Tuning, as in [`DyadicHolderTuning.lean`](../Proofs/DyadicHolderTuning.lean):
- `η = ε/(4L)` and `K = ⌈16LΔ/ε²⌉`;
- `J` is the largest `j ≤ log₂(K+1)` with `M(2^j η)^{2ν} ≤ σ²`, or 0 if there is none;
- `b_A = ⌈32σ²/ε²⌉ + 1` and `b_j = ⌈32(J+1) M (2^j η)^{2ν}/ε²⌉ + 1`.

The algorithm uses `L, M, ν, σ, Δ, ε`. It is not parameter-free.

**Prior estimator.** The estimator is the tree-aggregation (prefix-sum) estimator of Dwork et al.
(STOC 2010) and Chan–Shi–Song (2011). It is used in differentially private nonconvex optimization by
Arora, Bassily, González, Guzmán, Menart, Ullah,
[*Faster rates of convergence to stationary points in differentially private optimization*](https://arxiv.org/abs/2206.00846)
(ICML 2023), under smooth losses. It is related to the nested reference points of SNVRG (Zhou, Xu,
Gu, NeurIPS 2018). **We do not claim the estimator as new.** What is new is its use to exploit
Hölder sample regularity, the resulting rate, and its tightness.

## Theorem

[`LongTails/Theorems/DyadicVarianceReductionHolder.lean`](DyadicVarianceReductionHolder.lean):
`OracleTemplate.DyadicHolder.result : Convergence spec budget`, where `budget` is the one-line
formula in the Summary. Every oracle call is counted: anchor batches, all level batches with their
ceilings, and the iterations up to `K`. The proof is in
[`DyadicHolderConvergence.lean`](../Proofs/DyadicHolderConvergence.lean), with supporting modules
`DyadicHolder{Process,Trajectory,Moments,Descent,Count,Tuning}.lean`. It uses only `propext`,
`Classical.choice` and `Quot.sound`.

## Proof idea (the new mechanism)

1. **Sub-additivity under ν < 1.** Normalized steps give `‖x_t − x_s‖ ≤ |t − s|η`. Under MSH_ν, one
   difference spanning `m` steps has second moment `≤ M(mη)^{2ν} = s² m^{2ν}`, with `s² = Mη^{2ν}`.
   Telescoping `m` one-step differences, as STORM and SPIDER do, costs `m s²`. The long difference
   is cheaper by `m^{1−2ν}` for ν < 1, but it cannot be reused by the recursive estimators.
2. **Fenwick chains.** Each iterate's estimator is the anchor plus at most `J` level differences,
   one per binary digit of `t`. Each level batch is fresh given the past, so second moments add
   along the chain ([`Hyp.err_moment`](../Proofs/DyadicHolderMoments.lean)):
   `E‖d_k − ∇F(x_k)‖² ≤ σ²/b_A + Σ_{digits j} M(2^jη)^{2ν}/b_j ≤ ε²/16`.
   Level `j` is recomputed only every `2^{j+1}` steps.
3. **Cost.** Per epoch, level `j` costs `(n/2^{j+1}) b_j ≈ J (n/2^j) M(2^jη)^{2ν}/ε²`.
   - For ν ≥ 1/2 this increases geometrically in `j`, so the total is `≲ J² M(nη)^{2ν}/ε²`.
     Lean: `level_count` and `pow_rpow_split`.
   - The epoch length is chosen so that the top-level difference is no noisier than one fresh
     sample, `M(nη)^{2ν} ≈ σ²`. The epoch length is then `n ≈ (σ²/M)^{1/(2ν)}/η`. Each epoch costs
     `Õ(σ²/ε²)`, and there are `Kη · M^{1/(2ν)}/σ^{1/ν}` epochs.
   - The total is `Õ(Δ M^{1/(2ν)} σ^{2−1/ν}/ε³)`.
4. **Descent.** `F(x_{k+1}) ≤ F(x_k) − η‖∇F(x_k)‖ + 2η‖e_k‖ + Lη²/2`. Averaging gives
   `E‖∇F(x_out)‖ ≤ ε/4 + ε/2 + ε/8`.

For ν < 1/2 the geometric sum reverses and the method loses its advantage. This is why the theorem
is stated for ν ∈ [1/2, 1]. The threshold mirrors Giles' MLMC complexity theorem, case β = γ.

## Lower bound (hand proof; not formalized)

**Claim.** For ν ∈ [1/2, 1] and `ε ≤ ε₀(L, M, σ, Δ, ν)`, every randomized algorithm in the two-point
model needs `Ω(Δ M^{1/(2ν)} σ^{2−1/ν} ε⁻³)` calls.

**Construction.** Take Arjevani et al. 2019 ([arXiv 1912.02365](https://arxiv.org/abs/1912.02365)),
the MSS lower bound (their Thm 3) with its probability-p zero chain and smoothed progress gate:
- the objective is `F(x) = (L′λ²/ℓ₁) F_T(x/λ)`;
- the oracle is `g(x,ξ) = ∇F(x) + (ξ/p − 1) h(x)`, with `h = ∇F ⊙ Θ` and `ξ ∼ Bernoulli(p)`.

**Bounds.**
1. Because `E(ξ/p − 1) = 0`,
   `E‖g(x)−g(y)‖² = ‖∇F(x)−∇F(y)‖² + ((1−p)/p)‖h(x)−h(y)‖²`.
2. Their variance and MSS lemmas give `‖h‖² ≲ (L′λ)²`, `‖h(x)−h(y)‖² ≲ L′²‖x−y‖²`,
   `‖∇F‖² ≲ T(L′λ)²` and that `∇F` is `L′`-Lipschitz.
3. Since `min(a r², b) ≤ a^ν b^{1−ν} r^{2ν}`, and with `λ ≍ ε/L′`:
   - MSH_ν holds with `M ≳ L′^{2ν} ε^{2−2ν}(p⁻¹ + T^{1−ν})`;
   - variance `≲ ε²/p`.

**Parameters.** Choose:
- `p ≍ ε²/σ²`;
- `T ≍ ΔL′/ε²`;
- `L′ = L* ≍ M^{1/(2ν)} ε/σ^{1/ν}`, so that the noise part is admissible. Then
  `λ ≍ (σ²/M)^{1/(2ν)}` does not depend on ε.

The deterministic part is admissible once `L*^{1+ν}Δ^{1−ν} ≲ M`, i.e. for
`ε^{1+ν} ≲ M^{(ν−1)/(2ν)} σ^{(1+ν)/ν} Δ^{ν−1}`. We also need `L* ≤ L`, i.e.
`ε ≲ Lσ^{1/ν}/M^{1/(2ν)}`, and `ε ≤ σ`.

**Conclusion.** Arjevani et al.'s argument gives `≳ T/p = ΔL*σ²/ε⁴ = Δ M^{1/(2ν)} σ^{2−1/ν}/ε³`
queries. Their argument applies to algorithms making several queries per seed, and to randomized
algorithms via random rotation. Hence the proved upper bound is optimal in its ε-, M- and
σ-dependence up to the log² factor, in the small-ε regime. Together with `Ω(σ²/ε²)` and Carmon et
al.'s deterministic `Ω(LΔ/ε²)`, the full bound is tight up to log² for small ε.

**Relation to Fradin et al. (q-WAS).** Their q = 1 hard oracle has `E‖Δg‖² ≤ min(ℓ̄²‖Δx‖²/θ, Cσ²)`
with `θ ≍ ε²/σ²`. Its best MSH_{1/2} constant is `M ≍ sup_r min(ℓ̄² r/θ, Cσ²/r) ≍ ℓ̄σ²/ε`, which is
unbounded as ε → 0. Their Ω(ε⁻⁴) for 1-WAS therefore does not contradict ε⁻³ under MSH_{1/2}: the
two conditions are incomparable.

## Comparison with the closest results

Parameters are fixed, and the instance class is MSH_ν with ν ∈ [1/2, 1), plus the standard
assumptions. The ramp loss above is in this class.

| Method / source | Assumption used | Oracle | Rate on MSH_ν instances | Relation to this result |
|---|---|---|---|---|
| SGD; lower bound [Arjevani et al. 2019](https://arxiv.org/abs/1912.02365) Thm 1 | bounded variance | one point | `Θ(LΔσ²ε⁻⁴)` | ours `ε⁻³`; gain `≍ Lσ^{1/ν}/(M^{1/(2ν)}ε)` up to log² |
| STORM / SPIDER ([Cutkosky–Orabona 2019](https://arxiv.org/abs/1905.10018), [Fang et al. 2018](https://arxiv.org/abs/1807.01695)) | MSS | two points | not applicable (MSS fails) | at ν = 1 ours matches up to log² |
| STORM recursion re-analysed under MSH_ν (our reduction check) | MSH_ν | two points | `Δσ√M L^{1−ν} ε^{−(4−ν)}` (ε⁻³·⁵ at ν = ½) | ours removes `(L/L*)^{1−ν}`, a factor `ε^{−(1−ν)}` |
| SCSG-type anchored epochs | MSH_ν | two points | `ε^{−4+2ν/(1+2ν)}` (ε⁻³·⁵ at ν = ½) | ours better |
| [Fradin–Sadiev–Condat–Richtárik 2512.18713](https://arxiv.org/abs/2512.18713) v2, Thm 3.1/4.1 (q-WAS) | E‖Δg‖^q ≤ L̄^q‖Δx‖^q | two points | ramp-type instances are only 1-WAS, so their tight rate is ε⁻⁴ | incomparable classes; ours uses the second-moment structure |
| NSGD-M with extrapolation ([Cutkosky–Mehta ICML 2020](https://arxiv.org/abs/2002.03305)); tight for one point ([Arjevani et al. COLT 2020](https://arxiv.org/abs/2006.13476)) | Lipschitz ∇²F (needs Lipschitz data density) | one point | `O(ε⁻³·⁵)` if ∇²F is Lipschitz, else `ε⁻⁴` | ours needs only a bounded density, and better ε-exponent |
| [He–Lu 2412.14488](https://arxiv.org/abs/2412.14488) | Lipschitz p-th derivative of F | one point | `Õ(ε^{−(3+1/p)})` | needs smooth densities; ours better exponent |
| HVP-based ε⁻³ methods (Arjevani 2020; Tran–Cutkosky 2022) | stochastic Hessian-vector products | HVP | n/a: sample Hessians vanish a.e. for kinks | ours first-order |
| Online-to-nonconvex conversion ([Cutkosky–Mehta–Orabona ICML 2023](https://arxiv.org/abs/2302.03775)) | Lipschitz F, bounded variance | one point | `δ⁻¹ε⁻³` Goldstein; with δ ≍ ε/L, about `Lε⁻⁴` for ‖∇F‖ | ours better for smooth F |
| Tree aggregation in DP ([Arora et al. ICML 2023](https://arxiv.org/abs/2206.00846)) | smooth samples | — | privacy-driven rates | same estimator; different purpose and assumption |

**Improvement regime.** The fixed-parameter gain over SGD is `Lσ^{1/ν}/(M^{1/(2ν)}ε)` up to log².
It is substantial whenever `ε ≪ Lσ^{1/ν}/M^{1/(2ν)}`. For the ramp loss at ν = ½ the ratio is
`≍ σ²/(Rε)`.

**Tradeoffs.**
- **Logarithmic factor.** The budget carries `(1 + log₂(2 + 16LΔ/ε²))²`. At ν = 1 it is therefore
  worse than STORM by this log² factor. A level-dependent error allocation would remove it for
  ν > 1/2 (geometric costs), but not at ν = 1/2. This proof does not do that.
- **Two-point oracle.** The method needs the same-sample two-point oracle, like STORM.
- **Parameters.** The tuning uses `M, ν, σ, L, Δ`.

## Limitations

- **ν ≥ 1/2 only.** For ν < 1/2 the dyadic estimator's advantage disappears, and the right rate is
  open.
- **Expectation guarantee.** The guarantee is in expectation. High-probability bounds are not
  addressed.
- **Lower bound not formalized.** The lower bound is a hand proof that re-scales Arjevani et al.'s
  construction. It is valid in the stated small-ε regime.
- **No finite sums.** Finite sums are excluded, as discussed above.

## Literature search (2026-10-17)

- **Searched:** arXiv, NeurIPS/ICML/ICLR proceedings and OpenReview, for:
  - Hölder or mean-square-Hölder variance reduction;
  - discontinuous sample gradients with ε⁻³ rates;
  - tree aggregation outside differential privacy;
  - multilevel Monte Carlo for stochastic approximation and optimization: Dereich–Müller-Gronbach
    ([1506.05482](https://arxiv.org/abs/1506.05482)), Frikha 2016, Hu–Chen–He NeurIPS 2021,
    Asi et al. NeurIPS 2021, Hu–Wang–Chen–He [2408.11084](https://arxiv.org/abs/2408.11084). These
    address biased oracles and bias–variance–cost tradeoffs, not Hölder sample regularity under
    unbiased oracles;
  - quantile and CVaR variance reduction.
- **Read:** Fradin et al. v2 (definitions, Thms 3.1, 4.1–4.3, App. B/C hard oracle) and
  Arjevani et al. 2019/2020.
- **Abstracts only:** Arora et al. and the MLMC papers.
- **Not read:** Lowy et al. 2024 (DP nonconvex).
- **Result:** no prior ε⁻³ result for sample gradients that are Hölder in mean square was found.
  This is evidence, not proof, of priority.
