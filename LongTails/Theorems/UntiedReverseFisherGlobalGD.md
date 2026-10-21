# Global reverse-Fisher GD for two untied components without separation

[Lean theorem](UntiedReverseFisherGlobalGD.lean) · [Setup](../Setups/UntiedGaussianReverseFisher.lean) · [Algorithm and output](../Algorithms/UntiedReverseFisherGD.lean)

This result proves global exact recovery for constant-step gradient descent (GD) on the population reverse Fisher divergence, in Tyurin's Gaussian-mixture score-matching setup. It covers two untied student means fitted to a two-component teacher whose means are not separated. The separation may be anywhere in `[0, 1]`, including coincident means. The cost is `O(log(d(1+B)/(δε)) / max(Δ², ε))` exact-gradient calls, so the dimension `d` and the teacher-centre bound `B` enter only logarithmically.

The contribution is about the dynamics of GD on this score-training objective. It does not improve the oracle complexity of learning two-component Gaussian mixtures over all algorithms.

## Model, oracle, algorithm, and guarantee

This is the setup of [Tyurin, arXiv:2606.19876v1](https://arxiv.org/abs/2606.19876), eqs. (1)–(3), with `n = m = 2`.

- **Teacher.** `p̄ = ½N(µ̄₀, I) + ½N(µ̄₁, I)` in `ℝ^d` for any `d ≥ 1`. Write `Δ = ‖µ̄₀ − µ̄₁‖` and `ū = (µ̄₀ + µ̄₁)/2`.
- **Student.** `p_µ = ½N(µ₀, I) + ½N(µ₁, I)`. The means `µ = (µ₀, µ₁)` are untied and live in the Euclidean (ℓ²) product space `(ℝ^d)²`, formalized as `PiLp 2`.
- **Score.** The score is the exact mixture score `∇log p_µ(x) = Σᵢ wᵢ(x) µᵢ − x`, with softmax weights `wᵢ(x) ∝ exp(−‖x − µᵢ‖²/2)`.
- **Loss.** The setup defines Tyurin's eq. (1):

  `L(µ) = E_{x∼p_µ} ‖∇log p_µ(x) − ∇log p̄(x)‖² = ½ Σᵢ E_{z∼N(0,I)} ‖s_µ(µᵢ+z) − s̄(µᵢ+z)‖²`.

- **Oracle.** It returns the exact gradient `∇L(µ)` in this geometry, including the dependence of the sampling distribution on `µ`.
- **Public information.** The algorithm receives only `d`, `B`, `s`, `ε` and `δ`. The admissible instances satisfy `s ≤ Δ ≤ 1` and `‖ū‖ ≤ B`, with `0 ≤ s ≤ 1`. The value `s = 0` is allowed. The algorithm sees neither the teacher means, nor the teacher centre or axis, nor `Δ`.

**Algorithm** (`LongTails.Algorithms.UntiedReverseFisherGD`):

1. **Mirrored random start.** Draw `z ∼ Unif[−1,1]^d`, set `w = z/‖z‖` (or `e₁` if `z = 0`), and set `µ⁰ = (w, −w)`. The start depends only on the algorithm's own randomness. It is a mirrored initialization, not Tyurin's independent large-sphere initialization, and independent per-component starts are not covered.
2. **Updates.** Run `µ^{k+1} = µ^k − γ ∇L(µ^k)` with the single constant step `γ = 1/32`.
3. **Budget.** Make exactly `K` oracle calls, where

   `K = ⌈10¹⁶ / max(s², ε) · log(10²⁰ d (1+B) / (δ ε))⌉`.

4. **Output.** Return the last iterate.

The setup's `allowedAlgorithm` (`constantStepGD`) enforces the following, while the step value is left to the algorithm:

- one gradient query per step, at the current point;
- the update `point ← point − γ·reply` with one step `γ > 0` that is the same in every state;
- last-point output.

**Guarantee** (`LongTails.Theorems.UntiedReverseFisherGlobalGD.result : Convergence spec budget`):

`P[ min_{π ∈ S₂} Σᵢ ‖µᵢ^K − µ̄_{π(i)}‖² ≤ ε ] ≥ 1 − δ`.

The probability is taken over the product of the algorithm's cube law and the oracle seed law. Measurability of the output is proved. The proof shows more than the stated success event: every seed with `|⟨w, e⟩| ≥ δ/d` succeeds, where `e` is the teacher axis. When `Δ² ≤ 4ε/10⁵`, every seed succeeds.

**Rate.** The budget is `O(log(d(1+B)/(δε)) / max(s², ε))`.

- With `s = Δ`, this is `O(log(·)/Δ²)` for `ε ≤ Δ²`, which gives geometric (logarithmic) dependence on the accuracy.
- At `Δ → 0` it is `O(log(·)/ε)`, matching the shape of Tyurin's Thm 2.1 / Cor 2.5 for a single teacher (`Õ(1/ε)` with `n = 2`).
- The constants `10¹⁶` and `10²⁰` are proof constants, not practical recommendations.
- No lower bound or optimality claim is made.

## What is new, and how it compares with the closest results

| Primary result | Hypotheses and criterion | Relation to this theorem |
|---|---|---|
| [Tyurin v1](https://arxiv.org/abs/2606.19876), Thm 3.2 / E.1 | General `n, m`, independent large-sphere init. Requires `δ_min ≥ Ω(√(log(n³max{n,m}R0⁴/ε²)·log(2d/ρ)))`, which depends on ε. Criterion: each student is ε-close to its initially closest teacher, with probability `1−4ρ`. §3.1 lists "near-zero separation" as future work. | We cover the complementary regime `0 ≤ Δ ≤ 1` for `n = m = 2`, where E.1 does not apply. The criterion is exact recovery up to label permutation. E.1's closest-teacher criterion cannot hold in this regime when `n ≠ m`, because limit points become compromise points. |
| Tyurin v1, Thm 2.1 / Cor 2.5 | Single teacher (`Δ = 0`), any `n`, deterministic arbitrary init. | Our theorem contains the `Δ = 0`, `n = 2` endpoint with the same `1/ε` shape. It needs random mirrored init and pays a `log(1/δ)` factor. |
| Repository [`SymmetricReverseFisherGlobalGD`](SymmetricReverseFisherGlobalGD.md) | Tied student `±θ`, teacher centre at the origin and known to the model, symmetric teacher, all separations. Its setup allowed state-dependent steps. Its review notes a 2-call exact solution inside that family. | That result is the invariant slice `w = 0, µ₁ = −µ₀` of ours, and this work builds on it: its scalar functions and tied-step lemmas are reused. New here: untied students, an unknown teacher centre with `‖ū‖ ≤ B` and arbitrary offset, and a family restricted to a single constant step. |
| [Xu–Hsu–Maleki, NeurIPS 2016](https://arxiv.org/abs/1608.07630), Model 2 | Population EM for the balanced two-component mixture with two unknown untied means. Converges for any `θ* ≠ 0` from non-degenerate starts, with qualitative rates. | The EM analogue. We analyse GD on a score-matching objective with explicit oracle cost. Neither result implies the other. |
| [Shah–Chen–Klivans, NeurIPS 2023](https://arxiv.org/abs/2307.01178), Thm 13 | DDPM/forward objective at a chosen high noise level, projected GD plus a norm estimate, sample access, symmetric two-component, small separation. | Different objective, oracle and algorithm. We do not improve its sample complexity. |
| Gradient-EM / forward-Fisher works: [Xu–Fazel–Du, NeurIPS 2024](https://arxiv.org/abs/2407.00490), [Zhou–Xu–Fazel–Du, NeurIPS 2025](https://arxiv.org/abs/2506.06584), [Zhang et al., ICLR 2026](https://arxiv.org/abs/2511.22069) | Single-Gaussian truth or well-separated (`≳ √log`) mixtures. | None covers non-separated multi-component teachers for reverse-Fisher GD. |
| [Chen–Kontonis–Shah, COLT 2025](https://arxiv.org/abs/2404.18893), [Gatmiry–Kelner–Lee (preprint)](https://arxiv.org/abs/2404.18869) | Learning general GMMs without separation from samples. | The problem class is learnable without separation. We make no problem-class improvement. |

**Why no stronger oracle-complexity claim is made.** Exact population gradients carry a great deal of information. If state-dependent steps were allowed, a few calls could already recover the parameters. This is why the setup fixes a single constant step, and why the contribution is stated only as a GD-dynamics guarantee, which is the subject of Tyurin's paper.

## New mechanism

1. **Exact decoupling of the untied loss.** Let `w = (µ₀+µ₁)/2 − ū`, `v = (µ₀−µ₁)/2`, `b = (µ̄₀−µ̄₁)/2`, `a = ‖b‖`, and `cᵢ = ⟨µᵢ − ū, b⟩`. Then `L(µ) = ‖w‖² + K(‖v‖) + ½S_a(c₀) + ½S_a(c₁)`, with `K = radialSelf` and `S_a = scalarPotential`, both from the repository's tied analysis (`loss_decomposition`).
   - The proof uses the softmax-to-tanh closed form and a two-sided Gaussian posterior identity `E_{N(m,1)}[tanh(mx)h] + E_{N(−m,1)}[tanh(mx)h] = E_{N(m,1)}h − E_{N(−m,1)}h`. This identity is lifted to `ℝ^d` through orthogonal projections.
   - Background (not formalized): for general `n, m`, `L(µ) = (1/n)Σᵢ U(µᵢ) + d − E_{p_µ} tr C_µ`. Here `U` is a single-particle teacher potential and `C_µ` is the student posterior covariance of the means. The two-component case is the formalized instance.
2. **Gradient and step.** The gradient is `∇_{µ₀}L = w + ½A(‖v‖)v − ½R(c₀)b` and `∇_{µ₁}L = w − ½A(‖v‖)v − ½R(c₁)b`, with `A = alpha` and `R = ridgeForce` (`hasGradientAt_loss`). GD therefore acts on `(w, v)` as the exact map `pairStep`:
   - `w⁺ = (1−γ)w + (γ/4)(R(c₀)+R(c₁)) b`;
   - `v⁺ = (1 − γA/2) v + (γ/4)(R(c₀)−R(c₁)) b`.
3. **Centre contraction.** The prior file gives `R′ = 2T′ + 2W′ − a²T‴`. The integrand of `W′` is pointwise at most that of `T′`, because `y tanh y ≥ 0`. This gives `a²R′/2 ≤ 2a² + a⁴ ≤ 9/16` for `a ≤ ½`, together with a matching lower bound. Hence `‖w⁺‖ ≤ (1 − 7γ/16)‖w‖` holds uniformly in `v` (`centre_norm_step`). The component of `w` orthogonal to the teacher axis contracts by `(1−γ)` exactly.
4. **Perturbed tied dynamics.** The transverse part of `v` follows the tied update exactly. The axis coordinate `u = ⟨v, e⟩` gets the tied multiplier plus a defect `|R(σ+κ) − R(σ−κ) − 2R(κ)| ≤ 64|κ||σ|`, where `σ = ⟨w,b⟩` and `κ = ⟨v,b⟩`. This bound uses `|R″| ≤ 32`, proved in `UntiedReverseFisherRidge`. The defect is multiplicative in `κ`, so the invariant set `κ = 0` is respected and the random alignment is not destroyed. The phases are:
   - **Warm-up.** For `O(log(1 + 10⁷B))` steps, until `‖w‖ ≤ 10⁻⁷`, crude bounds cost only a polynomial factor in `1+B` for the alignment and angle ratio.
   - **Tied-like phases.** The repository's phases then run with half the signal strength: angle-ratio contraction, a floor, capped escape to `√m/8`, and aligned contraction with additive geometric errors (`post_branch`).
   - **Small signal.** When `Δ² ≤ 4ε/10⁵`, a separate capped-decay estimate covers the case, including coincident means.
5. **Budget.** A single explicit budget dominates every phase. This is proved in `UntiedReverseFisherBudget` and counts every gradient call.

## Thresholds, scope, and limitations

- **Three separation thresholds.**
  - Proved: `Δ ≤ 1`.
  - Numerical limit of the centre-contraction mechanism (not part of the formal result): `Δ ≈ 1.954`, where the computed `sup_c a²R′(c)/2` reaches 1. This is where the teacher potential stops being strongly convex along the axis, and numerically it coincides with the bifurcation of the single-student fit. The proof uses only the proved bound `a²R′/2 ≤ 2a² + a⁴ ≤ 9/16`, valid for `Δ ≤ 1`.
  - Spurious stable minima were observed in one-dimensional numerical experiments (not part of the formal result) from about `Δ ≈ 2.85`. Some upper bound on `Δ` is therefore intrinsic in kind.
  - The window `1 < Δ ≲ √log(1/ε)` between this theorem and Tyurin's E.1 remains open.
- **Two components only.** Only `n = m = 2` with equal fixed weights and identity covariances is covered. Over-parameterized students (`n > m`) and `m ≥ 3` are not.
- **Initialization.** The start is mirrored, `(w, −w)`. Independent component starts are not covered. The invariant bad sets (`µ₀ = µ₁`, and orthogonal alignment) make random initialization necessary.
- **Constants and optimality.** Constants are large and unoptimized. There is no lower bound and no claim of oracle-complexity improvement for the problem class.
- **Dimension.** Iterates stay in a low-dimensional span, so "arbitrary `d`" is not itself a contribution. `d` enters the budget only through `log(d/δ)` from the initialization.

## How the scope requirement is met

The requirement is to generalize Tyurin's result to non-separated means in the same setup.

- The same objective (eq. 1), the same student and teacher families (uniform weights, identity covariance, untied student means), the same exact-gradient constant-step GD, and the same parameter-recovery accuracy are kept.
- Tyurin's separation assumption `δ_min ≥ Ω̃(1)` is replaced by `Δ ≤ 1`, which includes `Δ = 0`.
- The specialization `n = m = 2`, and the mirrored start in place of the large-sphere start, are disclosed above.

## Verification

The public theorem imports its setup directly and states `Convergence LongTails.Setups.UntiedGaussianReverseFisher.spec budget`. The budget is one explicit line in the public parameters. The checks are `./build.sh`, `./lint.sh`, and `python3 run_comparator.py UntiedReverseFisherGlobalGD.lean`. The comparator allows only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The literature comparison was checked on 2026-10-20 UTC by both agents, covering web, arXiv and Semantic Scholar. Tyurin is arXiv v1 only, has no venue found, and is treated here as a preprint. OpenReview pages and the full ICML/NeurIPS 2026 accepted lists were not crawled directly.
