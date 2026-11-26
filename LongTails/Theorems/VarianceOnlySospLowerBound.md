# Dimension-linear lower bound for second-order stationary points under variance-only noise

**Theorem.** `LongTails.Theorems.VarianceOnlySospLowerBound.result` in
[`VarianceOnlySospLowerBound.lean`](VarianceOnlySospLowerBound.lean) proves
`NonConvergence LongTails.Setups.HighDimensionalVarianceOnlySecondOrder.spec budget`, where, with
`D = √ρ·Δ/ε^{3/2}`,

`budget = ⌊ d·(σ/ε)²·D / 2^703 ⌋`.

In words, the theorem covers every measurable randomized algorithm, every componentwise budget `b ≤ budget`, and
every parameter choice in the regime of `valid`, where:
- `δ ≤ 1/2`;
- `L ≥ 2^130 √(ρε)`;
- `σ ≥ 2^200 ε`;
- `D ≥ 2^390`;
- `D²·log(dσD/ε) ≤ 2^480·d`.

For all of these, there is an instance on which the algorithm fails to return an `(ε, √(ρε))`-second-order
stationary point with probability at least `1 − δ`. So `Ω(dσ²√ρΔ/ε^{7/2})` stochastic gradients are necessary
in that regime.

**Comparison with PR #170.** That upper bound is theorem `GatedPerturbedEscapeSosp.result` (see below). It has the
same leading term `dσ²√ρΔ/ε^{7/2}` with constant `2^{94}` and polylogarithmic factors `K⁸ℓ²`. The leading term
dominates when, in addition, `d ≳ L/√(ρε)`. In that regime the two bounds determine the oracle complexity of
certified SOSPs under variance-only noise up to:
- the polylogarithmic factors `K⁸ℓ²`;
- the universal constant ratio `2^{94}/2^{-703}`.

## Setup

[`LongTails/Setups/HighDimensionalVarianceOnlySecondOrder.lean`](../Setups/HighDimensionalVarianceOnlySecondOrder.lean).

The setup is the problem class of
[`VarianceOnlySecondOrder.lean`](../Setups/VarianceOnlySecondOrder.lean) (the setup of PR #170), passed through
`toGeneral`. The `admissible` and `successful` predicates are taken verbatim:
- `f` is `C²` on `ℝ^d`;
- `∇f` is `L`-Lipschitz and `∇²f` is `ρ`-Lipschitz in operator norm;
- `f(x0) − f(x) ≤ Δ`;
- the oracle is `g(x, ξ_k)` with i.i.d. seeds, jointly measurable, unbiased, with
  `∫ ‖g(x,ξ) − ∇f(x)‖² ≤ σ²`;
- success means the output is measurable and is an `(ε, √(ρε))`-SOSP with probability at least `1 − δ`.

Relative to that setup, the lower bound fixes or restricts the following.
- **Space.** The space is `E = EuclideanSpace ℝ (Fin d)`. Every inner-product space of dimension `d` is
  isometric to it, so the hardness transfers to any such `E`. This transfer is a remark, not a formal claim.
- **Seeds.** The seed space is `Ω = ℝ`. A noise sample is one real number, which is enough to encode any standard
  Borel noise. With a trivial seed space no stochastic lower bound is possible.
- **Start point.** `x0 = 0`, which loses no generality by translation.
- **Measurable algorithms only.** `allowedAlgorithm := measurablePolicy`: the algorithm's state space carries a
  measurable structure for which `initial`, `query`, the uncurried `update` and `output` are measurable. This is
  verbatim the restriction used by the existing lower bound
  [`AdditiveCubeFixedPoint.lean`](../Setups/AdditiveCubeFixedPoint.lean). It holds for every algorithm built from
  Borel-measurable operations (arithmetic, comparisons, sampling). This includes PR #170's algorithm, although that
  is not formalized. The proof needs it because it integrates events of the form "the oracle coin falls in an interval
  that depends on the query". Without measurability of the query map, Fubini fails and mathlib's integral is only
  a lower integral.
- **Parameter regime (`valid`).** Besides the base conditions (`L, ρ, ε, δ > 0`, `δ < 1`, `ρε ≤ L²`, `d ≥ 1`;
  the third is implied by the next list), `valid` requires:
  - `δ ≤ 1/2`;
  - `L ≥ 2^130 √(ρε)`;
  - `σ ≥ 2^200 ε`;
  - `D ≥ 2^390`;
  - `D²·log(dσD/ε) ≤ 2^480·d`.

  These constants are universal but enormous and unoptimized. They come from one fixed normalized profile
  (link strength `2^24`, escape thresholds of order `2^{-6}`, and Lipschitz constants `2^126` of the normalized
  instance). Shrinking them is possible but was not attempted.

## Hard instances

The proof modules are `LongTails/Proofs/EscapeChain*.lean`. In normalized units:
- the instance is `f(x) = δ0·F(x/r0)` with `r0 = 2^133√(ε/ρ)/10` and `δ0 = 2^133 ε r0`;
- the chain length is `K = ⌊10D/2^388⌋`.

The normalized objective [`objective`](../Proofs/EscapeChainFunction.lean) is

`F(x) = χ_R(x)·Σ_{l<K} [ −2^24·Λ(c_l)·Ψ(a_{l−1})·Φ(a_l) + Γ(a_{l−1})·S(c_l)·W_l(x) ] + ‖x‖²/2`.

Here:
- `a_l = ⟨u_l, x⟩` and `c_l = ⟨v_l, x⟩`, for hidden orthonormal *progress* directions `u_l` and *escape*
  directions `v_l`;
- `Φ = π/2 + arctan`;
- `Ψ, Γ, Λ` are `C³` spline gates with exact dead zones:
  - `Ψ = 0` for `a ≤ 1/2` and `Ψ = 1` for `a ≥ 1`;
  - `Γ = 0` for `a ≤ 3/5` and `Γ = 1` for `a ≥ 4/5`;
  - `Λ(c) = 0` for `c² ≤ 2^{-12}` and `Λ(c) = 1` for `c² ≥ 2^{-11}`;
- `S(c) = −2c²` near `0`, with compact support, is a saddle;
- `W_l = χ((‖x‖² − Σ_{m<l}(a_m² + c_m²))/4)` localizes saddle `l` to the region where the coordinates of all
  later stages are small;
- `χ_R` is a cutoff at radius `R = 2^130√(K+1)`.

The roles of the pieces are:
- **Links give depth.** The links are not localized, so each completed stage lowers the value by about `2^24`.
  The whole chain has depth `Θ(K)`, and `f(0) − inf f ≤ Δ`.
- **Saddles give curvature.** At the frontier stage the link is closed (`Λ = 0`), so the gradient vanishes there.
  The only certificate of non-stationarity is the saddle's negative curvature `−4`.

**Geometric lemma (no spurious SOSP).** [`certificate`](../Proofs/EscapeChainCertificate.lean) and
[`no_calm`](../Proofs/EscapeChainGeometry.lean): if all stages from some index `k < K` on are *clean*
(`|a_l|, |c_l| ≤ 1/128`), then `x` is not a normalized SOSP. The proof is a backward induction:
- **Frontier step** (`step_one`): the frontier saddle is localized and gives curvature at most `1.39 − 4Γ`.
- **Collapse step** (`step_two`): a stage whose saddle gate is not open is dead or yields a certificate.
- **Partial configurations** are excluded by the onset convexity of the spline gates.
- **Outside the ball**, the radial derivative gives the certificate.

**Smoothness.** The bounds are uniform in `K` and `d`: `‖∇²F‖, ‖∇³F‖ ≤ 2^126`
([`EscapeChainRegularity.lean`](../Proofs/EscapeChainRegularity.lean)). Links are summed with an "energy"
Cauchy–Schwarz bound, and at most 45 localized saddles are active at any point.

## Oracle

[`answerN`](../Proofs/EscapeChainOracle.lean) is a masked reveal oracle with one uniform coin `U` per query.
- **Exact terms.** The links and the regularizer are returned exactly.
- **Masked saddles.** Each saddle `l` is returned as `∇s̃_l/p_l·1{U ∈ I_l}`. The intervals `I_l` are disjoint
  subintervals of `[0,1]` of length `p_l = ‖∇s̃_l‖²/A`, with `A = σ̂²/45²` and `σ̂ = 2^{-133}σ/ε`.
- **Properties.** The oracle is jointly measurable and unbiased, and its variance is at most `σ²`
  (`answer_mean`, `answer_variance`).

## Hiding and counting

**Hidden directions.** The hidden directions are block-sign vectors. A uniformly random permutation of
`⌊d/b⌋` disjoint coordinate blocks of size `b` is drawn, together with independent uniform signs
([`EscapeChainFamily.lean`](../Proofs/EscapeChainFamily.lean)). The instance depends on the algorithm but not on
its seed: the theorem averages over this finite family and picks a bad member.

**Simulators.** For each `j`, the stage-`j` simulator `S_j` knows only the stages `< j`
([`EscapeChainSimulator.lean`](../Proofs/EscapeChainSimulator.lean)). As long as the unknown stages stay clean,
it answers exactly like the true oracle until saddle `j`'s coin hits. Cleanliness of all simulator queries holds
except on an event of small probability. This is proved by a cosh-MGF Hoeffding bound over the signs
([`EscapeChainBadCount.lean`](../Proofs/EscapeChainBadCount.lean)).

**Reveal rate.** A coin hit for the frontier saddle has conditional probability `p_j(x_t) ≤ 2^26 c_j²/A`. Here
`c_j = ⟨v_j, P_j x_t⟩` and `‖P_j x_t‖ ≤ 4` on the support of the localization. Averaging `v_j` over the unused
blocks and signs gives `E p_j ≤ 2^30/(A·b·(n − 2K − 1)) ≈ 2^43/(σ̂² d)`
([`reveal_average`](../Proofs/EscapeChainAverage.lean)).

**Counting.** Stage durations are counted inside each simulator's own run, which avoids conditioning on
informative non-reveals ([`many_fast`](../Proofs/EscapeChainCounting.lean) and
[`EscapeChainProbability.lean`](../Proofs/EscapeChainProbability.lean)).
- **Fast stages.** If the output is an SOSP and nothing bad happened, then at least `K/2` stages must be
  revealed within `m = ⌊2N/K⌋` queries of the previous reveal.
- **Freeze lemma.** Each such fast reveal has probability at most `(m+1)·E p_j` after a freeze argument over the
  coin of the revealing query ([`freeze`](../Proofs/EscapeChainFreeze.lean)).
- **Conclusion.** Markov's inequality gives `P(success) ≤ 1/8 + 1/8 < 1 − δ` whenever `N ≤ budget`.

## What is new, and comparison

**Upper bound (PR #170).**
[`GatedPerturbedEscapeSosp.lean`](GatedPerturbedEscapeSosp.lean) proves, for the same problem class,
`budget = N·b` with:
- `N = ⌈2^40 ℓ² K⁴ κ (1 + D)⌉`;
- `b = ⌈2^54 K⁴ (1 + dσ²√ρ/(L ε^{3/2}) + σ²/ε²)⌉ + 1`;
- `κ = L/√(ρε)`, `K = log(20480 d)` and `ℓ = log(4096·K·κ·(1+D)/δ)`.

Up to the factor `2^{94}K⁸ℓ²`, this is
`κ(1+D)(1+σ²/ε²) + d(σ/ε)²(1+D)`.

Under `valid`, `D ≥ 2^390` and `σ ≥ 2^200 ε`, so `1 + D ≈ D` and `1 + σ²/ε² ≈ σ²/ε²`. If moreover `d ≥ κ`, the
term `d(σ/ε)²D` dominates. This is exactly the shape of the lower-bound budget `d(σ/ε)²D/2^703`.

The upper-bound theorem is stated for `VarianceOnlySecondOrder`, which has an arbitrary seed type and allows all
algorithms. The two formal statements differ only in:
- the fixed `E`, `Ω` and `x0`;
- the restricted `valid`;
- `measurablePolicy`.

**Where the question comes from.** Jin, Netrapalli, Ge, Kakade, Jordan (JACM 2021, `arXiv:1902.04811v2`),
Theorem 16, analyse perturbed SGD without per-sample smoothness.
- Their bound is `Õ(d·LΔσ²/ε⁴)` stochastic gradients, with a factor linear in the ambient dimension.
- Whether some dimension factor is necessary without per-sample smoothness was not settled. It is not posed there as an explicit open problem; the gap is inferred from the scope of the known bounds.
- PR #170 reduced the dimension-dependent part to `dσ²√ρΔ/ε^{7/2}`. This theorem shows that this part cannot be
  improved beyond polylogarithmic factors.

**Prior lower bounds.**
- **Carmon–Duchi–Hinder–Sidford**, *Lower bounds for finding stationary points I and II* (Math. Program. 2020,
  `arXiv:1710.11606` and `arXiv:1711.00841`).
  - They give noiseless chain constructions for `ε`-stationary points (first-order), including under Hessian
    Lipschitzness.
  - Randomized algorithms are handled by a random rotation in dimension `poly(1/ε)`.
  - The rates have no ambient-dimension factor.
- **Arjevani, Carmon, Duchi, Foster, Sekhari, Sridharan** (COLT 2020, `arXiv:2006.13476v1`), Theorem 6 and
  eq. (14), give a chained-saddle lower bound for `γ`-weakly-convex points (the curvature part of an SOSP).
  - It holds for zero-respecting algorithms with stochastic Hessian-vector-product noise.
  - It is dimension-free.
  - For gradient-only oracles (no HVP noise) its curvature term vanishes.

  Chaining saddles is therefore not new. What is new here is the dimension factor.
- **Per-saddle statistical analogue.** Detecting one hidden negative direction from noisy gradients is a
  spiked-covariance/noisy-eigenvector problem, which needs about `d/θ²` samples.
  - PR #170's note contains a single-saddle bound of order `dσ²/ε²`, proved on paper and not formalized. That
    bound has no `D` factor.
  - In the noiseless model, eigenvector computation needs only `Ω(log d)` matrix-vector products (Simchowitz et
    al.). The linear-`d` factor here is a noise effect.
- **Dimension-free rates under more structure.** Dimension-free rates are possible under additional per-sample
  smoothness. Examples are SPIDER-type rates and the `ε^{-3}` rates of `arXiv:2610.16832`.

**New result.** To our knowledge, this is the first lower bound for finding `(ε, √(ρε))`-SOSPs with
variance-only stochastic gradients that is linear in the ambient dimension and multiplies it by the chain length:
`Ω(d σ² √ρ Δ / ε^{7/2})`. It holds against every measurable randomized algorithm, not only zero-respecting ones.

**Technical mechanism.** The new ingredients are:
- **Localized masked saddles.** The localization `W_l` prevents the "leak proportional to level" of
  non-localized saddles, so each stage's reveal rate is `O(1/(dσ̂²))` regardless of how far the chain has
  progressed.
- **Unmasked links with exact dead zones.** These keep the chain deep while carrying no information about the
  frontier.
- **Block-sign hiding.** Hoeffding concentration over the signs lets an unbounded number of queries go
  undetected, with a dimension requirement only of order `D²log`.
- **Stage-wise simulators.** The reveal events are counted inside each simulator's own run.

## Scope

- **Almost-tight pair in Template terms.**
  - The upper bound is the existing `Convergence` theorem `GatedPerturbedEscapeSosp.result` (PR #170).
  - The lower bound is this new `NonConvergence` theorem.
  - They match up to polylogarithmic factors and universal constants in the regime above, as explained there,
    including the setup differences.
- **Practical setup.** The task is finding SOSPs of smooth nonconvex objectives from unbiased stochastic
  gradients with bounded variance. This is the standard Ghadimi–Lan noise model, with no per-sample smoothness and
  no Hessian oracle.
- **Newness.** No previous lower bound for this problem has a linear factor in the ambient dimension (see above).
- **Overlap.** A check of local `main` and the open PRs found no overlapping result. In particular, the open PRs as
  of 2026-11-26 (#4, #215, #257, #273–#275) and the recently merged PRs #249–#272 study other classes.

## Limitations

- **Constants.** They are astronomically large in both `valid` and the budget, as stated above. The bound is an
  asymptotic statement.
- **Regime.** The bound needs:
  - `σ ≥ 2^200 ε`;
  - long chains, `D ≥ 2^390`;
  - high dimension, `d ≥ 2^{-480}D²log(dσD/ε)`.

  Together with `D ≥ 2^390`, the dimension condition forces `d ≳ 2^{300}`. The theorem is therefore a statement
  about the asymptotic shape `d(σ/ε)²D` and not a numerically meaningful bound. Reducing the constants (gate
  slopes, link strength `2^24`, the uniform Lipschitz constants `2^126`) would shrink these thresholds but was not
  attempted. Tightness against PR #170 additionally needs `d ≳ L/√(ρε)`. For `d ≪ L/√(ρε)`, the upper
  bound's `LΔσ²/ε⁴` term dominates. Whether `dσ²√ρΔ/ε^{7/2}` is then also necessary is open.
- **Polylog gap.** The upper and lower bounds differ by the upper bound's `log⁸ d·log²(·)` factors.
- **Measurable algorithms only.** The formal statement covers measurable algorithms only. Lean does not
  formalize the measurability of PR #170's algorithm.
- **Guarantee type.** The lower bound is for constant success probability `1 − δ` with `δ ≤ 1/2`. The upper
  bound gives tunable confidence. A lower bound with an explicit `log(1/δ)` dependence is not attempted.
