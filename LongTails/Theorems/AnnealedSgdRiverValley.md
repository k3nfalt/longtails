# Annealed SGD on river valleys with hill-concentrated noise

Lean: [`AnnealedSgdRiverValley.lean`](AnnealedSgdRiverValley.lean) (`OracleTemplate.RiverValley.result`),
setup [`LongTails/Setups/RiverValleyHillNoise.lean`](../Setups/RiverValleyHillNoise.lean),
algorithm [`LongTails/Algorithms/StepDecaySgd.lean`](../Algorithms/StepDecaySgd.lean),
proofs `LongTails/Proofs/RiverValley*.lean`. The budget reduction is `budget_ge` and the main
assembly is `convergence_of_le`, both in `RiverValleyConvergence.lean`.

## Summary

Single-step-size SGD with an annealing phase finds an ε-stationary point (`E‖∇f(x_out)‖ ≤ ε`) of a
nonconvex *curved* river-valley function. Its ε⁻⁴ oracle-complexity term does not depend on the hill
curvature `Lv`. The hill noise `σv²` enters that term only through river-side constants
(`Γ²Lh`, `ΓLJG`, `Lm'²/μ`, `c'σu/Lv`), and `Lv σv²` is paid only at order ε⁻² in the final small-step
phase. SGD does not know the split, the river or the hills.

The result explains *annealing in general*: any schedule that ends with a long enough small-step phase
gets this behaviour, and the formal algorithm is one such schedule. It does not claim that WSD beats
cosine or any other annealed schedule. Constant-step SGD on the same class pays `Lv Δ σv²/ε⁴`
(paper argument below).

## Motivation

Loss landscapes of LLM pre-training are often described as a *river valley*. Sharp "hill" directions
carry most of the curvature and most of the gradient noise. A flat, slowly turning "river" carries the
actual loss decrease. This picture is used to explain why warmup–stable–decay (WSD) and step-decay
schedules beat constant step sizes: see Wen et al., *Understanding Warmup-Stable-Decay Learning Rates:
A River Valley Loss Landscape Perspective* (ICLR 2025, [arXiv 2410.05192](https://arxiv.org/abs/2410.05192)).

The existing theory for this picture has two kinds of results:
- model-specific tracking and approximation statements (Wen et al., Thms 3.4–3.5: straight river,
  isotropic hill noise);
- deterministic analyses ([arXiv 2609.30957](https://arxiv.org/abs/2609.30957)).

To our knowledge it contains no oracle-complexity guarantee for SGD on a class of nonconvex functions
with a *curved* river. This gap is inferred from the scopes of the theorems in these papers; it is not
an open question stated in the literature.

The structural premise, that a few sharp outlier Hessian directions sit above a flat bulk, is documented
at scale by:
- Sagun et al., *Empirical Analysis of the Hessian of Over-Parametrized Neural Networks*
  ([arXiv 1706.04454](https://arxiv.org/abs/1706.04454));
- Ghorbani, Krishnan and Xiao, *An Investigation into Neural Net Optimization via Hessian Eigenvalue
  Density* (ICML 2019);
- Papyan, *Traces of Class/Cross-Class Structure Pervade Deep Learning Spectra* (JMLR 2020).

That gradient noise concentrates in the sharp directions is documented by:
- Zhu et al., *The Anisotropic Noise in Stochastic Gradient Descent* (ICML 2019);
- Jastrzębski et al. 2018.

### Small-scale numerical check

Setting: a character-level transformer with 128k parameters, trained with plain SGD. The scripts are
outside the repository.

- **Noise concentration.** The gradient-noise variance along the top-20 Hessian eigendirections is about
  10³ times larger per direction than along random directions. The top-20 block carries about 7% of the
  total noise energy.
- **Schedule comparison, unclipped.** The comparison is best against best over the shared learning-rate
  grid {1.0, 3.0}; lr 3.0 diverged for both schedules. Final loss:
  - seed 0: WSD-style step decay 1.545, constant 1.644;
  - seed 1: WSD-style step decay 1.467, constant 1.573.
- **Schedule comparison, with gradient clipping.** Best over the same grid:
  - seed 0: WSD 1.257, constant 1.391;
  - seed 1: WSD 1.273, constant 1.527.

Limitation of the check: at this scale the bulk curvature (≈1.65) is not well separated from the
smallest top-20 eigenvalue (≈1.59). So the strong valley separation assumed below is *not* demonstrated
here. For that structure at scale we rely on the Hessian-spectrum literature cited above.

## Setup (`RiverValleyHillNoise.spec`)

### Objective

The ambient space is a finite-dimensional real inner-product space `E`. It splits as `E = K ⊕ Kᗮ`,
where `K` holds the hill coordinates and `Kᗮ` the river coordinates. `P` and `Q` are the orthogonal
projections onto `K` and `Kᗮ`. The split is existential in `admissible` and is not given to the
algorithm. The objective is

  f(x) = h(Qx) + ½ ⟨A(Px − φ(Qx)), Px − φ(Qx)⟩.

### Assumptions

All quantifiers are global.

- **River loss `h`.** `h` is nonconvex, with gradient `gh`.
  - `gh` is `Lh`-Lipschitz.
  - The Hessian `Hh` is `ρh`-Lipschitz.
  - The river gradient is bounded: `‖gh‖ ≤ G`. This is a limitation; see below.
- **River curve `φ : E → K`.** `φ` is `C^{2,1}`, with Jacobian `Jφ` and second derivative `DJ`.
  - `Jφ` is `LJ`-Lipschitz.
  - `DJ` is `ρJ`-Lipschitz.
- **Turning rate.** `‖A Jφ(y) Q z‖ ≤ Γ μ ‖Q z‖`, so the cross-curvature is `Γμ`. This implies
  `‖Jφ Q‖ ≤ Γ`.
- **Hills.** `A` is a symmetric operator that maps `K` into `K`, with `μ‖k‖² ≤ ⟨Ak,k⟩` and
  `‖Ak‖ ≤ Lv‖k‖` on `K`. `A` may be arbitrarily anisotropic on `K`.
- **Initial gap.** `f(x0) − f(x) ≤ Δ` for all `x`.
- **Oracle.** IID stochastic gradients `g(x, ξ)`, jointly measurable and unbiased, using the repository's
  `IID` structure. Only *block* second moments are assumed:
  - `E‖Q(g − ∇f)‖² ≤ σu²` (river noise);
  - `E‖P(g − ∇f)‖² ≤ σv²` (hill noise).

### Regime conditions (`valid`)

Here `Lm' = ΓLh + 2LJG` and `c' = 2GρJ + 2LJLh + Γρh + G LJ²`.

1. `16Γ ≤ 1`: the river turns slowly.
2. `64 Lm' ≤ μ`: hill curvature dominates the river's curvature couplings.
3. `64 c' σu ≤ μ Lv`: a noise–curvature condition, discussed below.
4. `32 Lh log R ≤ μ`: the valley condition for the cooldown. `R` is the explicit quantity in `valid`:

     R = 3 + Lv²/μ² + 4Lv² Mc/(μ³(Lv ε² + 8N̂)),

   with `N̂` and `Mc` as in the Result section.
   - If `N̂ > 0` then `R ≤ 3 + Lv²/μ² + Lv² Mc/(2μ³N̂)` for every ε, so the condition does not depend
     on ε.
   - If `N̂ = 0`, for example when `Γ = LJ = σu = 0` and `σv > 0`, then `R` grows like ε⁻². The
     condition then requires `Lh ≲ μ / log(1/ε)`.

All four conditions are free of ε apart from this caveat.

**About condition 3.** It was added while completing the proof. Its only use is to show `λ ≤ μ/8` for
the stable-phase weight
`λ = 256Lm'²/μ + 32ΓLm' + 2c'σu/Lv` (`descent_real`, `RiverValleyMaster`).
- **Why the term is there.** The summand `2c'σu/Lv` of `λ` absorbs a third-order noise term,
  of size `c'·η²σu²·(…)`, from the second-order expansions of the correction `m` and of `φ`. It
  multiplies river noise by the third-order river constants `GρJ, LJLh, Γρh, GLJ²`.
- **How to read it.** It says that river noise times third-order river curvature is at most
  `(hill curvature)²/64`. Indeed `μLv ≥ μ²`, so the condition is implied by `64c'σu ≤ μ²`.
- **When it is vacuous.** It holds automatically when `φ` is affine (`LJ = ρJ = 0`) and `h` is
  quadratic (`ρh = 0`), and also when `σu = 0`.
- **Can it be removed?** We did not manage to. Using Young's inequality to push this term to order
  `η³` puts a factor `1/(ημ)` on the remaining `‖w‖²` term, and that factor is not uniformly bounded
  in the stable phase.

### Examples (nonlinear, interacting coordinates)

Take `E = ℝ^{du} × ℝ^{dv}`, so `K = {0} × ℝ^{dv}`. Let `A` be any symmetric matrix on `ℝ^{dv}` with
spectrum in `[μ, Lv]`, and let `e_j ∈ ℝ^{dv}` be orthonormal eigenvectors of `A` with eigenvalue `μ`. Set

- `h(u) = α log(1 + ‖u‖²)`. It is nonconvex and bounded below. Its constants are `G = α`, `Lh = 2α` and
  `ρh = O(α)`.
- `φ(u) = Σ_j a_j sin(⟨b_j, u⟩/ℓ) e_j`, with unit vectors `b_j`. Write `a := max_j a_j` and assume the
  `b_j` are orthonormal. Then:
  - the turning rate is `Γ = a/ℓ`;
  - `LJ = a/ℓ²` and `ρJ = a/ℓ³`.

  If the `e_j` are arbitrary orthonormal vectors instead of `μ`-eigenvectors, then `Γ = Lv a/(μℓ)`.

The conditions hold when:
- `a/ℓ ≤ 1/16`;
- `α(a/ℓ + a/ℓ²) ≲ μ`;
- the noise and log conditions hold.

This is a lower-bounded, slowly turning, small-amplitude version of Wen et al.'s toy
`(x₂ − sin x₁)² − αx₁`. The toy itself is *not* in the class: it is unbounded below and has `Γ ≈ 1`.
The function `f` is not separable in any orthogonal frame, and the hill offset depends nonlinearly on
all river coordinates.

### Accuracy criterion

`E‖∇f(x_out)‖ ≤ ε`, with `x_out` measurable and `‖∇f(x_out)‖` integrable.

## Algorithm (`StepDecaySgd.method`)

The algorithm is plain single-step-size SGD; `allowedAlgorithm` enforces exactly this family.
1. Draw `τ` uniformly from `{0,…,T}`, using the algorithm's own randomness.
2. Run `τ` stable steps with step `ηs`.
3. Run `K` cooldown steps with step `ηc`.
4. Output the last iterate.

The algorithm uses neither the split, nor `φ`, nor `A`. The parameters `ηs, ηc, T, K` depend only on
the public constants:
- `ηs = 1/(8Lv + 64N̂/ε²)`;
- `ηc = 1/(8Lv + 256 log R · Mc/(με²))`;
- `T = ⌈256Δ/(ηs ε²)⌉`;
- `K = ⌈2 log R/(μηc)⌉`.

## Result

The theorem is `result : Convergence spec budget`. The budget is the single explicit line

  budget = ⌈256Δ(8Lv + 64N/ε²)/ε² + log²(3 + Lv²/μ² + 4Lv²M/(μ³(Lvε² + 8N)))·(16Lv/μ + 512M/(μ²ε²)) + 1⌉

where:
- `N = 2Lhσu² + Lm'·((1792Lm'/μ + 224Γ)(σu² + σv²) + σuσv) + c'σu·(14(σu² + σv²)/Lv + σu²/μ + ΓGσu/Lv)
  + 2LJ²σu⁴/Lv`. This is algebraically equal to the tuning quantity
  `N̂ = 2Lhσu² + 7λ(σv² + σu²) + Lm'σuσv + c'σu³/μ + c'ΓGσu²/Lv + 2LJ²σu⁴/Lv`.
- `M = 2Gρhσu² + μ²σu² + 4Lv²σv² + 8LvLJ²σu⁴/μ`. This is an upper bound on the cooldown noise constant
  `Mc = (2Gρh + Lh²)σu² + 4Lv²σv² + 20Γ²μ²σu² + 8LvLJ²σu⁴/μ + ΓμGLJσu²/4` under `valid`.

`budget_ge` proves `T + K ≤ budget`. Extra budget queries leave the output unchanged. The simplification
costs only absolute constants. All parameter rates are preserved, including the ε-free `R` in the log.

In words, with `S = σu² + σv²`:

  O( Lv Δ/ε² + Δ·[Lh σu² + (Γ²Lh + ΓLJG + Lm'²/μ + c'σu/Lv)·S + Lm'σuσv + …]/ε⁴
     + log²R · (Lv/μ + (Lv²σv² + μ²σu² + Gρhσu² + …)/(μ²ε²)) ).

The coefficient of `σv²` in the ε⁻⁴ term is

  1792 Lm'²/μ + 224 Γ Lm' + 14 c'σu/Lv
    = O(Γ²Lh + ΓLJG + (ΓLh + LJG)²/μ + c'σu/Lv).

When `Lh ≤ μ/256` this reduces to `O(Γ²Lh + LJG + c'σu/Lv)`. Here `2048 LJ²G²/μ ≤ 16 LJG` follows from
condition 2. There is also a cross term `Lm'σuσv`.

The **hill noise therefore enters the leading ε⁻⁴ term only through river-side quantities, not through
the hill curvature `Lv` or the hill condition number `Lv/μ`**. The term `Lv²σv²` appears only in the
cooldown, at order ε⁻²·log²R.

## Comparison and novelty

### Generic nonconvex SGD

This compares against Ghadimi–Lan, SIAM J. Optim. 2013, Thm 2.1/Cor 2.2. On the subclass with an affine
river (`LJ = ρJ = 0`), `f` is globally `L`-smooth with `Lv ≤ L ≤ Lh + (1+Γ)²Lv`, so generic SGD needs
`O(LΔ(σu² + σv²)/ε⁴)`. Its rule "min over iterates of `E‖∇f‖² ≤ ε²`" implies our criterion for a
uniformly sampled iterate.

The result above replaces the hill-noise coefficient `L ≥ Lv` by
`O(Γ²Lh + ΓLJG + Lm'²/μ + c'σu/Lv)`. In the river-valley regime `Lv ≫ Lh` this is smaller by a factor of
order `Lv/(Γ²Lh + …)`.

For a curved river (`LJ > 0`), `f` is **not** globally smooth: `∇²f` contains `⟨DJ(·,·), Aw⟩`, which
grows with `‖w‖`. Ghadimi–Lan therefore does not apply directly. Any local smoothness constant of `f` is
still at least `Lv`.

### Constant-step SGD cannot achieve this

This is a paper argument, *not formalized*.

**Instance.** `E = ℝ²` with `Γ = LJ = ρJ = 0` and `A = Lv` on the hill line (so `μ = Lv`). The objective
is `f(u,v) = h(u) + (Lv/2)v²`, where:
- `h` is a bounded-below `C^{2,1}` function with `h' = −2ε` on `[0, D]`, `D = Δ/(4ε)`;
- `h` saturates smoothly over a length large enough that `Lh` and `ρh` are as small as the valley
  condition needs.

The noise is `ξu = 0` and `ξv ~ N(0, σv²)`, with `σv ≥ ε`. The start point is `x0 = (0, 0)`. Then:
- `G = 2ε`;
- the gap is at most `Δ`;
- `c' = 0`;
- `N̂ = 0`.

So the instance is in the class, with the ε-dependent `R` caveat above.

**Algorithms covered.** Every constant step `η` with output either the last iterate or an iterate at a
time chosen independently of the noise. The argument is:

1. **`η ≥ 2/Lv`.** Then `|1 − ηLv| ≥ 1`, so `Var v_t ≥ η²σv²` for every `t ≥ 1`. Hence
   `E‖∇f‖ ≥ Lv E|v_t| ≥ 2√(2/π)σv > ε`. At `t = 0`, `|h'(0)| = 2ε`. Either way the method fails.
2. **`η < 2/Lv`.** The river coordinate moves deterministically, `u_t = 2εηt`. While `u_t < D`,
   `‖∇f(x_t)‖ ≥ 2ε`. Reaching `u_t ≥ D` needs `t ≥ D/(2εη) ≥ 1/(ηLv)` once `ΔLv ≥ 8ε²`. By then the hill
   coordinate has mixed:

     Var v_t = η²σv²(1 − (1−ηLv)^{2t})/(1 − (1−ηLv)²) ≥ (1 − e⁻²) ησv²/(2Lv).

   So `E‖∇f(x_t)‖ ≥ c√(ηLv)σv`.
3. **Conclusion.** `E‖∇f(x_out)‖ ≤ ε` forces both `η ≤ ε²/(c²Lvσv²)` and `T ≥ D/(2εη)`, that is
   `T = Ω(LvΔσv²/ε⁴)`.

**Comparison.** On the same instance the annealed method uses `O(LvΔ/ε² + log²R·Lv²σv²/(μ²ε²))` calls.
Annealing is therefore necessary for the improvement.

### Γ = 0 is easy

With a straight, axis-aligned river the problem separates into two parts:
- nonconvex SGD on `h`;
- strongly convex last-iterate SGD with step decay (Ge, Kakade, Kidambi and Netrapalli, NeurIPS 2019;
  Pan et al., *Eigencurve*, ICLR 2022).

The content of the result is the curved, turning river (`Γ > 0`, nonlinear `φ`). Through the coupling,
SGD's single learning rate transmits hill noise into the river direction. The proof shows that:
- this costs only `Γ²·(river curvature)·σv²`, not the `Γ²μσv²` that a direct two-timescale potential
  gives;
- the ε⁻⁴ term is free of `Lv/μ`.

Numerically, the transmitted noise divided by `Γ²σv²` is about 0.1–1.3, independent of `A`
(A = 10…1000) and of `κv = Lv/μ ∈ {1, 10, 100}`.

### Two-timescale and bilevel stochastic approximation

This covers:
- Borkar; Konda–Tsitsiklis;
- Doan;
- Zeng, Doan and Romberg ([arXiv 2109.14756](https://arxiv.org/abs/2109.14756));
- Kaledin et al., COLT 2020;
- TTSA (Hong et al.);
- ALSET (Chen, Sun and Yin, NeurIPS 2021).

These methods use *separate* step sizes on known blocks, or inner solves, so they need the split. SGD on
an LLM does not have it. Our algorithm does not use the split: SGD is rotation-equivariant.

### SDE and implicit-bias analyses near manifolds of minima

Blanc et al.; Damian et al.; Li, Wang and Arora; Gu et al. These describe asymptotic drift along a valley
of *minimizers*. Here the river has nonzero slope `∇h`, and we give a finite-time oracle-complexity
guarantee for stationarity.

### Schedule theory

Schaipp et al. (ICML 2025) observe that convex schedule theory predicts how schedules behave in LLM
training, but they leave the nonconvex mechanism open. The result above is one rigorous nonconvex
mechanism, in a stylized class.

## Technical mechanism

1. **Poisson-corrected potential.** The potential is `V = h(Qx) + ⟨m, w⟩ + λ‖w‖²`, where:
   - `w = Px − φ(Qx)`;
   - `m = (I + JJᵀ)⁻¹ J a`, with `J = Jφ∘Q` and `a = Q∇h`.

   The correction cancels the cross term `η⟨Ja, Aw⟩`. A Woodbury bound then gives river descent
   `(η/2)‖a‖²`.
2. **Second-order expansions at two base points.** `m` and `φ` are expanded to second order (C^{1,1})
   at the deterministic river step and at the noisy one. This removes the `O(η)` bias that Lipschitz
   control of `m` alone would leave. It is why `h, φ ∈ C^{2,1}` are assumed, and the source of `c'`.
3. **A κ-free cooldown.** Three coupled recursions:
   - the plain hill energy `‖w‖²`, which controls the kick to `‖a‖` with constant `Γμ` and not `ΓLv`;
   - the A-weighted hill energy `‖Aw‖²`, which gives the final bound `‖∇f‖ ≤ ‖a‖ + (1+Γ)‖Aw‖`;
   - the river gradient `‖a‖²`, controlled through a Hessian-Lipschitz expansion so that river noise
     does not accumulate over the cooldown.

   A Gronwall argument on `‖a‖² + θ‖w‖²` combines them.

## Limitations and open points

- **Quadratic hills.** The hills are quadratic with a constant operator `A`. This is a stylization, as
  in the river-valley literature. The general class, with only a Lipschitz third derivative of `f`, is
  not covered.
- **Bounded river gradient** `‖∇h‖ ≤ G`. This excludes rivers with quadratic growth.
- **Regime conditions.** `Γ ≤ 1/16`, the valley conditions, and the noise–curvature condition
  `64c'σu ≤ μLv` (discussed above). When `N̂ = 0` the log condition depends on ε.
- **Constants.** The constants are large (256, 1792, …), and the cooldown carries a `log² R` factor.
- **Lower bounds.**
  - The constant-step lower bound is a paper argument and is not formalized.
  - A *class* lower bound showing that the `Γ²·L_river·σv²` term is necessary for methods that do not
    know the split is **open**.
  - The `σu²` term matches Arjevani et al. (2019) on the river block.
- **Fixed split.** The split `K` is fixed. This stylizes sharp subspaces that rotate slowly.
- **Numerical validation.** It is small-scale and does not show a clean valley separation (see above).
