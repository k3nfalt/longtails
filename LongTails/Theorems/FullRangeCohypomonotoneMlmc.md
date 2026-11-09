# Stochastic composite cohypomonotone inclusions over the full range ρL < 1: Õ(LR/(τ³ε) + σ²/(τ²ε²)) with τ = 1 − ρL

This note explains the contribution formalized in
[FullRangeCohypomonotoneMlmc.lean](FullRangeCohypomonotoneMlmc.lean).

**Lean files.**
- Main theorem: `LongTails.Theorems.FullRangeCohypomonotoneMlmc.result`, with the budget `LongTails.Theorems.FullRangeCohypomonotoneMlmc.budget`.
- Setup: [`../Setups/FullRangeCohypomonotoneInclusion.lean`](../Setups/FullRangeCohypomonotoneInclusion.lean).
- Algorithm:
  - [`../Algorithms/FullRangeMlmc.lean`](../Algorithms/FullRangeMlmc.lean): the inner solver and the MLMC estimator;
  - [`../Algorithms/FullRangeProgram.lean`](../Algorithms/FullRangeProgram.lean): the query program;
  - [`../Algorithms/FullRangeTuned.lean`](../Algorithms/FullRangeTuned.lean): constants and `algorithm`.
- Proof chain, all in `../Proofs/`:
  - `FullRangeResolvent`: the fixed-point map;
  - `FullRangeClip`: ball clipping and the terminal bound;
  - `BiasedAnchoring`: anchoring with a biased oracle;
  - `FullRangeInner` and `FullRangeEstimator`: the inner solver and the estimator;
  - `FullRangeOperator`: the biased operator and measurability;
  - `FullRangeExecution` and `FullRangeLaw`: program evaluation and laws;
  - `FullRangeCertificate`: the certificate;
  - `FullRangeSeed`: the seed-cost tail;
  - `FullRangeAccuracy`: assembly;
  - `FullRangeTuning` and `FullRangeBudget`: constants and the budget;
  - `FullRangeMain`: the final bound.
- `#print axioms result`: `propext`, `Classical.choice`, `Quot.sound`.

## Problem

Find a zero of F + G on a finite-dimensional real inner-product space E, where:
- F is L-Lipschitz and need not be monotone;
- G is maximal monotone, accessed through its exact resolvent J_γ = (Id + γG)⁻¹ for every γ > 0;
- F + G is ρ-cohypomonotone:

  ⟨(Fx + a) − (Fy + b), x − y⟩ ≥ −ρ‖(Fx + a) − (Fy + b)‖²  for all a ∈ Gx, b ∈ Gy.

F is seen only through an unbiased stochastic oracle with variance σ². The output is a pair (x̄, u) with u ∈ G(x̄) for every seed, and E‖F(x̄) + u‖ ≤ ε. Every F-sample and every resolvent call is counted.

## Contribution

For every **ρL < 1**, the algorithm uses at most

  budget = ⌈ 2⁷⁹ · (1 + LR/(τε) + σ²/ε²) / τ² · Λ⁷ ⌉,
  τ = 1 − ρL,  Λ = 1 + log(2 + LR/ε + σ²/ε²) + log(2/τ),

oracle calls. That is Õ(LR/(τ³ε) + σ²/(τ²ε²) + 1/τ²), a **deterministic** budget that holds for every seed.

How this compares with known results on the range ρL ∈ [1/2, 1). The range includes composite (G ≠ 0) problems.

| Source | Range | Stochastic complexity on that range |
|---|---|---|
| Alacaoglu–Kim–Wright, [arXiv 2402.05071](https://arxiv.org/abs/2402.05071), Cor. 4.1 (ICML 2024; v3 Sep 2026) | ρ < 1/L, constrained | Õ(ε⁻⁴) |
| Pethick et al. 2023b (cited in AKW Remark 4.2) | ρ < 1/(2L) | Õ(ε⁻¹⁶) |
| Chen–Luo, [arXiv 2208.05925](https://arxiv.org/abs/2208.05925) | ρ ≤ 1/(2L), **unconstrained** | Õ(σ²/ε² + LD/ε), expected cost |
| Library [`RegularizedProxExtragradientCohypomonotone`](RegularizedProxExtragradientCohypomonotone.lean) | 2ρL < 1, composite | Õ((1 − 2ρL)⁻⁸ (LR/ε + σ²/ε²)) |
| Tran-Dinh, [arXiv 2504.13046](https://arxiv.org/abs/2504.13046) v3 (Aug 2025), §4.5 Cor. 24 (Hybrid-SGD; Cors. 22–23 for L-SVRG/L-SARAH) | **different class:** T ρ-cohypomonotone, F co-coercive in mean square, ρL < 1 | O(ε⁻³) for E‖G_λx^K‖² ≤ ε² |
| **This result** | ρL < 1, composite | Õ(LR/(τ³ε) + σ²/(τ²ε²)) |

Tran-Dinh's row is related prior work, not a direct competitor. There the set-valued part T carries the nonmonotonicity, and F must be co-coercive in mean square, which makes F monotone and restricts the oracle beyond bounded variance. Here F is only Lipschitz and possibly nonmonotone, G is maximal monotone, and only the sum F + G is cohypomonotone. Neither class contains the other. If their F is identified with our F and their T with our G, the common instances have F + G monotone, and monotone methods already give ε⁻² there. Some problems fit both classes under a different split, for example T = T_s + N_C with T_s Lipschitz and nonmonotone. In their model those problems need an exact resolvent of the nonmonotone part, which our model does not assume. The two results therefore use different oracle models and are not directly comparable. The output criteria also differ: the expected squared forward-backward residual there, and the expected norm of F(x̄) + u with u ∈ G(x̄) here.

The motivating open question comes from AKW Remark 4.2, which is unchanged in v3. After stating Chen–Luo's unconstrained Õ(ε⁻²), AKW list as open "a similar complexity improvement in our constrained setup with a wider range for ρ". This theorem gives that improvement, with explicit dependence on τ.

Inside the library, the setup and the earlier theorem required 2ρL < 1. On that range their bound blows up as (1 − 2ρL)⁻⁸. The new range is ρL ∈ [1/2, 1), and on the old range the τ powers improve. These are the only gains relative to the library.

### What is *not* claimed

- **Mechanism.** The ingredients are all known:
  - a debiased resolvent by multilevel Monte Carlo (MLMC);
  - recursive anchoring on the resolvent fixed-point map;
  - a stochastic forward-backward inner solver.

  Chen–Luo already use MLMC with a biased oracle on a saddle envelope. The new work is the assembly for the composite case at ρ ∈ [1/(2L), 1/L), with a fixed budget.
- **Unconstrained case.** When G = 0, Chen–Luo's method with a different envelope parameter (τ_CL > L, ρ < 1/τ_CL) plausibly covers the full range. We do not claim novelty there. The same parameter change, with the envelope parameter in (L, 1/ρ) and an inner prox step for G, plausibly also covers the composite case. We have not checked this. If it holds, our result is a variant of RAIN++.
- **Optimality.** We claim no lower bound. The τ⁻³ and τ⁻² powers are what the proof gives; they are not shown to be tight.
- **Constants.** 2⁷⁹ and Λ⁷ are loose. They come from a proof-friendly tuning and are not meant to be competitive.

## Setup

[`FullRangeCohypomonotoneInclusion`](../Setups/FullRangeCohypomonotoneInclusion.lean) reuses the parameters, oracle, `admissible` and `successful` of the library's [`StochasticCohypomonotoneInclusion`](../Setups/StochasticCohypomonotoneInclusion.lean) by delegation. Only `valid` changes:

  0 < L,  0 ≤ ρ,  **ρL < 1** (was 2ρL < 1),  0 ≤ R,  0 ≤ σ,  0 < ε.

| Condition | Statement | Provenance |
|---|---|---|
| resolvent | γ⁻¹(z − J_γ z) ∈ G(J_γ z) for all γ > 0 | AKW setting (exact prox of G) |
| monotone G | ⟨a − b, x − y⟩ ≥ 0 | AKW setting |
| Lipschitz F | ‖Fx − Fy‖ ≤ L‖x − y‖ | AKW setting |
| cohypomonotone F + G | as above | AKW setting, ρ < 1/L (Bauschke–Moursi–Wang 2021) |
| solution | ∃x*, −F x* ∈ G x*, ‖x0 − x*‖ ≤ R | standard |
| oracle | IID stream; E g(x, ξ) = F x, E‖g − F x‖² ≤ σ² | AKW stochastic setting (unbiased, bounded variance) |

**Queries.** `inl z` returns g(z, ξ_k). `inr (γ, z)` returns J_γ z. Each costs one call.

## Algorithm

The constants are τ = 1 − ρL, η = (ρ + 1/L)/2 (so that η − ρ = τ/(2L) and 1 − ηL = τ/2), the averaging weight a = τ, and the inner step γ₀ = τ/8.

1. **Fixed-point map.** Define T = (1 − τ)Id + τJ_{η(F+G)}. Because ρ < η < 1/L, T is nonexpansive, and its fixed points are the zeros of F + G. The resolvent J_{η(F+G)} is not available, so it is estimated.
2. **Clipping.** Run on T' = T ∘ P, where P projects onto the ball B(x0, r) with r = 2R + 2ε_T. T' is nonexpansive and has x* as a fixed point. Its estimation error is therefore uniform. A linear terminal bound transfers accuracy back to T: ‖Ty − y‖ ≤ 4‖T'z − z‖ for y = Pz.
3. **Inner solver.** Stochastic forward-backward on the strongly monotone subproblem that defines J_{η(F+G)}(x): z ← J_{γη}(z − γ(z − x + η g(z, ξ))). The step halves at dyadic epochs.
4. **MLMC estimator.** Draw a level ℓ ∈ {0, …, top} with probability 2^{-ℓ} for ℓ ≥ 1 and 2^{-top} for ℓ = 0. Return the base output plus the reweighted dyadic difference. The bias is at most θ-small, and the second moment is O(top · η²σ²).
5. **Outer loop.** Anchoring with a biased oracle, implemented by the library's SmoothBanach pipeline, on T'. The bias tolerance is β ≤ ε_T/(80S), with S = clog₂(⌈16R/ε_T⌉ + 1) + 1 anchoring stages.
6. **Fixed budget.** All MLMC levels are drawn up front, from the algorithm's seed. If their total cost exceeds a Chernoff-type limit, the algorithm skips the loop and certifies at x0. This happens with probability at most d = ετη/(8(ετη + 3r)). Its contribution to the expectation is at most ε/8.
7. **Certificate.** At y = P(z_final):
   - run one inner path;
   - average a batch of ⌈576σ²/ε²⌉ + 1 samples;
   - take one prox step p = y − η F̂, and output x̄ = J_η p, u = η⁻¹(p − x̄).

   Then u ∈ G(x̄) for every seed, and ‖F x̄ + u‖ ≤ 3·(error) + ‖y − J y‖/η.

The cost is dominated by n0 · calls · top, where:
- n0 = O(Λ/τ²) is the base inner length;
- calls = S · innerSteps = Õ(1 + LR/(τε) + σ²/ε²);
- the other two factors are logarithmic.

## A nontrivial instance with ρL ∈ [1/2, 1) (pen-and-paper)

Take z = (x, y) ∈ ℝ^d × ℝ^d, a box Y = [−b, b]^d, and

  f(x, y) = φ(x) + s⟨x, y⟩ + (ℓ/2)‖y‖²,  min over x ∈ ℝ^d, max over y ∈ Y.

Here φ(x) = Σᵢ c·h_δ(xᵢ), with h_δ the Huber function. φ is convex and β-smooth with β = c/δ, and its gradient is bounded by c. For fixed x, the y-player maximizes a **convex** function, so f is nonconcave in y. The problem is nevertheless *hidden-concave*; see the caveat after the proof. Set F(x, y) = (∇φ(x) + s y, −s x − ℓ y) and G = {0} × N_Y. G's resolvent is (x, y) ↦ (x, proj_Y y).

**Claim.** If s² > βℓ, then F + G is ρ-cohypomonotone with ρ = ℓ/(s² − βℓ), and F is L-Lipschitz with L = ‖M‖ + β, where M = [[0, s], [−s, −ℓ]] and ‖M‖ = (ℓ + √(ℓ² + 4s²))/2.

**Proof.** Take two points. Write dφ = ∇φ(x) − ∇φ(x'), and du for the difference of elements of (F + G) at the two points.
- The normal-cone parts satisfy ⟨dn, dy⟩ ≥ 0.
- The bilinear terms cancel.
- ∇φ is (1/β)-cocoercive.

So ⟨du, dz⟩ ≥ ‖dφ‖²/β − ℓ‖dy‖².

Also ‖du‖² ≥ ‖dφ + s dy‖². For any vectors a and w, minimizing over a gives ‖a‖²/β + ρ‖a + w‖² ≥ ρ/(1 + ρβ) · ‖w‖². Apply this with a = dφ and w = s dy. Then

  ⟨du, dz⟩ + ρ‖du‖² ≥ (ρs²/(1 + ρβ) − ℓ)‖dy‖² = 0  for ρ = ℓ/(s² − βℓ).

The Lipschitz bound follows from the triangle inequality. ∎

**Lower bounds, so the instance is really outside the old range.** Take two points where every |xᵢ| > δ with the same signs, so dφ = 0, and y in the interior of Y.
- Choosing dx = −(ℓ/s) dy gives ⟨du, dz⟩ = −ℓ‖dy‖² and ‖du‖² = s²‖dy‖². So every valid ρ is at least ℓ/s².
- F is affine with matrix M on this open region. So every valid L is at least ‖M‖.

**Numbers.** s = 1, ℓ = 0.5, β = 0.05:
- ρ = 0.5128 and L = 1.3308, so ρL = 0.682 < 1, which the theorem allows.
- **Every** valid pair has ρL ≥ 0.5 · 1.2808 = 0.640 > 1/2. So no library setup with 2ρL < 1 admits this instance.

A sampling check gives a largest observed ratio of 0.5119 against the bound 0.5128, so the bound is tight up to sampling. Taking a large Huber threshold δ with c = βδ makes the region of relevant y as large as wanted. Adding linear terms ⟨a, x⟩ − ⟨e, y⟩ moves the solution away from the origin without changing ρ or L.

**Where the structure breaks.**
- **Constraining x.** If x is constrained, take both points at the same boundary x and choose the normal-cone difference to cancel s dy. Then du = (0, −ℓ dy), which forces ρ ≥ 1/ℓ = 2, so ρL > 2.
- **Rotation-type F.** Rotation-type F with facet constraints can also push ρL past the range.

**Caveat: hidden concavity.** Minimizing over x first gives the dual function

  d(y) = min_x f(x, y) = −φ*(−s y) + (ℓ/2)‖y‖².

φ is β-smooth, so φ* is (1/β)-strongly convex. Hence d is (s²/β − ℓ)-strongly concave on Y, and the hypothesis s² > βℓ is exactly this condition. A method that works on the dual could therefore also solve these instances. It would maximize the strongly concave d over Y and recover x from ∇φ*. This needs solving x-subproblems from stochastic samples, which our oracle does not provide directly, and we do not analyze it. So this family is a valid instance of the theorem outside the old range, not evidence that the theorem is needed for it. We do not have a composite instance at ρL ≥ 1/2 that is provably out of reach of such reductions.

So the composite instances at ρL ≥ 1/2 form a one-sided structured family: constraints or regularizers sit on the nonconcave side, and the coupled partner is free.

## Limitations

- **Criterion.** The criterion is the expected residual E‖F x̄ + u‖ ≤ ε, not a high-probability bound.
- **Oracle model.** Exact resolvents of G are assumed. Only F is stochastic.
- **Instances.** The instance family above is narrow, as the previous section explains.
- **Mechanism.** As stated earlier, the mechanism is known. The value is the full-range composite guarantee, with explicit τ dependence and a deterministic budget, formalized end to end.
