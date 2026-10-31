# Dimension-linear heavy-tailed zeroth-order optimization with clipped SPSA

[The Lean theorem](ClippedSpsaHeavyTailed.lean) (`OracleTemplate.ClippedSpsaHeavyTailed.result`) gives an in-expectation oracle-complexity bound for finding an approximately stationary point of a smooth nonconvex function. The algorithm sees only paired noisy function values whose sample gradients have just a bounded central `p`-th moment, `1 < p ≤ 2`. With `q = p/(p-1)`, the horizon is

\[
H \;=\;\Big\lceil 2^{20}\,132^{\,q}\,\frac{L\,d\,\Delta}{\varepsilon^2}\Big(1+\big(\tfrac{\sigma}{\varepsilon}\big)^{q}\Big)\Big\rceil,
\qquad H+1\;=\;O_p\!\Big(\frac{dL\Delta}{\varepsilon^2}+\frac{dL\Delta\,\sigma^{p/(p-1)}}{\varepsilon^{(3p-2)/(p-1)}}\Big),
\]

two-point calls, that is, `2(H+1)` function evaluations. All published heavy-tailed two-point zeroth-order analyses we found carry a dimension factor `d^{p/(2(p-1))}` on the heavy-tailed term. Our bound reduces it to `d`, a gain of `d^{(2-p)/(2(p-1))}` (for example `√d` at `p = 3/2`). It also separates the deterministic term `dLΔ/ε²` from the heavy-tail term. The mechanism is a directional clipping-bias bound: the two-point estimator automatically has a dimension-free directional moment, so no extra noise assumption is needed.

## Problem, oracle and output

The [setup](../Setups/HeavyTailedTwoPointZerothOrder.lean) (`LongTails.Setups.HeavyTailedTwoPointZerothOrder.spec`) has public parameters `d ≥ 1`, `L > 0`, `Δ ≥ 0`, `σ ≥ 0`, `1 < p ≤ 2`, `ε > 0`, an initial point `x0 ∈ ℝ^d`, and an abstract sample space `Ω`. An instance is an objective `f : ℝ^d → ℝ` with:

- **objective:** `f` is differentiable and has a lower bound `lower` with `f(x0) − lower ≤ Δ`;
- **sample functions:** for every sample `ξ`, `F(·;ξ)` is differentiable with gradient `G(·,ξ)`, and `‖G(x,ξ) − G(y,ξ)‖ ≤ L‖x − y‖` for all `x, y` (uniform sample smoothness);
- **unbiasedness:** `∫ G(x,ξ) dν(ξ) = ∇f(x)` for every `x`;
- **heavy-tailed noise:** `∫ ‖G(x,ξ) − ∇f(x)‖^p dν(ξ) ≤ σ^p` for every `x`, with integrability stated explicitly. No variance or directional-moment assumption is made, so for `p < 2` the variance may be infinite;
- **measurability:** `F` and `G` are jointly measurable;
- **sampling:** samples are IID under an abstract law `P` with marginal `ν`, through the repository's `IID` structure; the product form is derived internally.

`f` is linked to the oracle only through `E G = ∇f`. This contains the usual case `f = E F` and its additive shifts. The `L`-smoothness of `f` is derived from sample smoothness, not assumed.

**Oracle.** One call takes a pair of points `(y₁, y₂)`. It returns `(F(y₁;ξ), F(y₂;ξ))` for a single fresh sample `ξ`; this is the standard two-point zeroth-order model with shared randomness (Duchi et al. 2015; El Bakkali et al. 2026). The algorithm never sees gradients, `∇f`, `G`, the sample `ξ`, or a third evaluation with the same sample. With three or more evaluations per sample, coordinate differences would reveal the whole sample gradient; this oracle excludes that.

**Accuracy criterion.** The returned point `X` satisfies `E‖∇f(X)‖ ≤ ε`, with the expectation over both the algorithm's randomness and the samples.

## Algorithm

The [algorithm](../Algorithms/ClippedSpsa.lean) (`OracleTemplate.ClippedSpsa.method`) is SPSA, the simultaneous-perturbation method with Rademacher directions, with clipping and a uniformly random stopping index. At step `t` it:

- draws `u_t ∈ {−1, 1}^d` uniformly from its own seed;
- queries `(x_t + μu_t, x_t − μu_t)`;
- forms `Y_t = (F(x_t + μu_t; ξ_t) − F(x_t − μu_t; ξ_t))/(2μ)`;
- updates `x_{t+1} = x_t − η · clip_c(Y_t) · u_t`.

Because `‖u_t‖ = √d`, scalar clipping at `c` is the same as norm clipping of `Y_t u_t` at `c√d`. The output is `x_τ`, where `τ` is uniform on `{0, …, H}` and drawn from the seed; the run freezes once `t = τ`. The explicit tuning in [SpsaTuning](../Proofs/SpsaTuning.lean) is:

- `μ = ε/(28Ld)`;
- `S = 2(σ + ε/56)`;
- `c = 256S + 64ε + 2S(33S/ε)^{1/(p−1)}`;
- `η = min{1/(8192Ld), ε²/(96Ld·c^{2−p}S^p)}`.

The algorithm uses the public parameters `L, Δ, σ, p, ε, d`. It is not parameter-free.

## Proof idea and new mechanism

Write `a = ∇f(x)`, `A = ⟨a,u⟩`, and `V = Y − A`. Two-sided Taylor bounds from sample smoothness give `V = ⟨ζ,u⟩ + r`, with `ζ = G(x,ξ) − a` and `|r| ≤ Lμd/2`.

1. **Directional moments come for free.** For Rademacher `u`, `E_u⟨x,u⟩²⟨y,u⟩² ≤ 3‖x‖²‖y‖²` (proved by induction on `d` in [RademacherDirections](../Proofs/RademacherDirections.lean)). By the power-mean inequality this gives `E|⟨ζ,u⟩⟨a,u⟩|^p ≤ 3^{p/2}‖ζ‖^p‖a‖^p`, independent of `d`. The norm of the same noise vector `⟨ζ,u⟩u` has `p`-th moment of order `d^{p/2}σ^p`. In the language of Liu (ICLR 2026), the estimator's generalized effective dimension is about `d` without any assumption. See `SampleHyp.moment_hyp` in [SpsaStep](../Proofs/SpsaStep.lean).
2. **Directional clipping bias.** The first-order effect of clipping is `E[(1 − w)VA]`. By Hölder and Markov, the part on `{|V| > c/2}` is bounded by `√3 S‖a‖(2S/c)^{p−1}`, which has no `√d` factor. A norm-based bias bound, as in Lemma B.5 of El Bakkali et al., pays an extra `√d` here, and this is the source of their `d^{p/(2(p−1))}`. See `MomentHyp.tail_cross_le` in [ClippedScalarDescent](../Proofs/ClippedScalarDescent.lean).
3. **Large gradients without localization.** For `‖a‖ > c/16`, the pointwise bound `min(|A|,c)|A| ≥ t(A² − A⁴/(4‖a‖²))` with `t = min(1, c/(2‖a‖))`, together with `E A⁴ ≤ 3‖a‖⁴`, gives descent of order `c‖a‖`. Together with the small-gradient case: `E⟨a, clip(Y)u⟩ ≥ φ(‖a‖) − ‖a‖B`, where `φ(t) = min(t²/2, ct/128)`. See `MomentHyp.clipped_inner_lower`.
4. **Descent and averaging.** The one-step bound `E f(x⁺) ≤ f(x) − (η/4)φ(‖∇f(x)‖) + 2ηB² + Lη²d·c^{2−p}S^p` (`SampleHyp.expected_descent`) is telescoped along the trajectory (`RunHyp.window_sum` in [SpsaProcess](../Proofs/SpsaProcess.lean)). The trajectory uses two independent fresh streams, directions and samples (`fresh_pair`). The pointwise inequality `t ≤ (2/ε + 128/c)φ(t) + ε/4` then converts the averaged `φ` bound into `E‖∇f(x_τ)‖ ≤ ε` (`LongTails.Proofs.SpsaConvergence.convergence`). [SpsaTuning](../Proofs/SpsaTuning.lean) proves that the one-line public budget dominates `96Δ/(ηε²)`.

The proof keeps the light random-direction part `⟨a,u⟩u − a`; this part is the classical source of the factor `d`. It also keeps the smoothing remainder, initialization, and every call of the execution. Clipped steps keep the iterates in a ball of radius `H·η·c·√d`, which gives all integrability.

## Comparison with prior work

| Work | Setting and guarantee | Dimension and parameter factor |
| --- | --- | --- |
| El Bakkali, Chayti, Zhang, Rahali, Saadi, [arXiv 2605.17394v1](https://arxiv.org/abs/2605.17394), NeurIPS 2026 poster, Thm 2.3 and Remark 2.4 | Same smooth nonconvex two-point model under a weak-`L_p` tail condition (which contains our `p`-moment class); RSC-ZO with scalar clipping and spherical directions; high-probability bound on the trajectory average `(1/T)Σ‖∇f(x_t)‖² ≤ ε²` | `Õ(LΔ(√(LΔ)+σ)^{q} d^{q/2} ε^{−(3p−2)/(p−1)})`. Its clipping-bias Lemma B.5 is norm-based. |
| Liu and Luo, [arXiv 2605.24513v1](https://arxiv.org/abs/2605.24513) | Lipschitz nonsmooth nonconvex, `(δ,ε)`-Goldstein stationarity, clipped two-point estimator | `d^{p/(2(p−1))}`, stated to match the best known convex nonsmooth zeroth-order results |
| Kornilov et al., NeurIPS 2023 ([arXiv 2310.18763](https://arxiv.org/abs/2310.18763)); Kornilov et al., Computational Management Science 2023 ([arXiv 2304.02442](https://arxiv.org/abs/2304.02442)) | Nonsmooth convex, heavy-tailed, (accelerated) clipped zeroth-order methods. The NeurIPS paper (Sec. 1.1) poses the optimal dimension dependence as an open question for that nonsmooth convex setting. | `(√d)^{p/(p−1)}` |
| Kornilov et al., median clipping ([arXiv 2402.02461](https://arxiv.org/abs/2402.02461)) | Zeroth-order methods for *symmetric* heavy-tailed value noise | Assumes symmetry, so it lies outside this asymmetric `p`-moment class |
| Ghadimi and Lan, SIOPT 2013 | Smooth nonconvex, finite variance (`p = 2`), two-point Gaussian smoothing | `O(dLΔ/ε² + dLΔσ²/ε⁴)`. Our bound has this order at `p = 2`. |
| Liu, [arXiv 2512.23178v3](https://arxiv.org/abs/2512.23178) (ICLR 2026); Liu, arXiv 2610.21026 (NeurIPS 2026) | First-order clipped SGD under an *assumed* fine-grained model (directional moment `σ_s`, norm moment `σ_l`), for nonsmooth or smooth convex objectives | Not zeroth-order and not nonconvex. Our directional-bias step uses the same idea, but the structure is derived from the estimator rather than assumed. |

**Improvement claimed.** On the common class (uniform sample smoothness and bounded `p`-th central moment), comparing oracle complexities:

- the heavy-tailed term improves from `LΔ(√(LΔ)+σ)^{q} d^{q/2} ε^{−(3p−2)/(p−1)}` to `LΔσ^{q} d ε^{−(3p−2)/(p−1)}`;
- the deterministic term `dLΔ/ε²` is kept separate. The baseline has no `σ`-free term: at `σ = 0` its bound is still of order `d^{q/2}(LΔ)^{q/2+1}ε^{−(3p−2)/(p−1)}`.

For `p < 2` the dimension gain is `d^{(2−p)/(2(p−1))}`, which grows without bound as `p ↓ 1`. At `p = 2` there is no dimension gain; the rate is the classical one.

**What is not claimed.**

- **Criterion.** Our guarantee is in expectation, on one uniformly sampled iterate; the baseline is a high-probability statement on the trajectory average. We do not claim to dominate it as a high-probability result. The dimension gap comes from their clipping-bias bound (Lemma B.5), which is norm-based and does not depend on the accuracy criterion.
- **Directions.** We use Rademacher (SPSA) directions; the baselines use the sphere.
- **Class.** Our class is the `p`-moment subclass of the baseline's weak-`L_p` class.
- **Other settings.** Nonsmooth, convex, Goldstein and high-probability analogues are not proved here. In particular, Kornilov et al.'s open question for nonsmooth convex problems is not resolved; this theorem is the smooth nonconvex analogue.

**Optimality.** At `p = 2` the order is that of Ghadimi and Lan. We do not prove a lower bound. Whether `d·LΔσ^{q}ε^{−(3p−2)/(p−1)}` is jointly optimal in `d` and `p` for two-point oracles remains open.

## Nontrivial instances

- **Quasi-likelihood regression with heavy-tailed responses.** Take features `a ∈ ℝ^d` with `‖a‖ ≤ 1`, responses `b` with `E|b|^p < ∞` and `E[b | a] ∈ [0,1]`, and
  `F(x;(a,b)) = softplus(⟨a,x⟩) − b⟨a,x⟩ + κ Σ_i x_i²/(1 + x_i²)`.
  - Each `F(·;ξ)` is `(1/4 + 2κ)`-smooth.
  - The noise `(sigmoid(⟨a,x⟩)a − E[·]) − (ba − E[ba])` has a uniform `p`-th moment bound with `σ ≤ 2 + 2(E|b|^p)^{1/p}`, and infinite variance when `E b² = ∞`.
  - `f ≥ 0`, because `softplus(t) ≥ βt` for `β ∈ [0,1]`.
  - The penalty makes `f` nonconvex, and dense features couple the coordinates.
- **Heavy-tailed linear perturbations.** `F(x;ξ) = h(x) + ⟨ζ(ξ), x⟩`, for any smooth nonconvex lower-bounded `h` and zero-mean `ζ` with only a `p`-th moment (for example a centred multivariate Student-t with `p < ν ≤ 2` degrees of freedom). This is the additive heavy-tailed gradient-noise model, observed through function values.

## Limitations

- The constants (`2^{20}`, `132^{q}`) are loose, and `132^{q}` blows up as `p ↓ 1`; this is not uniform in `p`.
- The algorithm needs `L, Δ, σ, p, ε, d`.
- The guarantee is in expectation and uses a random stopping index.
- Uniform sample smoothness (for every `ξ`) is required, as in the baseline. Random-design models whose noise grows with `‖x‖` are excluded by the global moment bound.
- Literature coverage: the screening of NeurIPS 2026 accepted papers was partial (title lists were incomplete).
- Unchecked source: the Optimization Methods and Software paper "Zeroth-order methods for non-smooth stochastic problems under heavy-tailed noise" (doi 10.1080/10556788.2026.2617623) could not be accessed. It concerns nonsmooth problems.
