# SCENT for compositional entropic risk minimization: explicit moment-ratio complexity with anchor batching

Lean: [`ScentCompositionalEntropicRisk.lean`](ScentCompositionalEntropicRisk.lean)
(`OracleTemplate.Scent.ScentCompositionalEntropicRisk.result`),
setup [`LongTails/Setups/CompositionalEntropicRisk.lean`](../Setups/CompositionalEntropicRisk.lean),
algorithm [`LongTails/Algorithms/Scent.lean`](../Algorithms/Scent.lean),
proofs `LongTails/Proofs/Scent*.lean`. The final assembly is `expected_gap`, the parameter
algebra is `tuning`, and the public-budget reduction is `horizon_bound`, all in
`ScentConvergence.lean`.

## Summary

The target paper is Wei, Zhou, Wang, Lin and Yang, *A Geometry-Aware Efficient Algorithm for
Compositional Entropic Risk Minimization* ([arXiv 2602.02877v2](https://arxiv.org/abs/2602.02877),
ICML 2026). Its algorithm SCENT solves

  min_{w ∈ W} F_CERM(w) = (1/n) Σ_{i=1}^n log E_{ζ∼P_i} exp(s_i(w; ζ))

through the jointly convex min-min form F(w, ν) = (1/n) Σ_i E[exp(s_i(w;ζ) − ν_i) + ν_i], with a
stochastic proximal mirror-descent (SPMD) step on the sampled dual coordinates and a projected
stochastic gradient step on w. Its convergence bound (Theorem 3.6) is stated in terms of
*trajectory* variance quantities `σ_t²`, `δ_t²`; Section 4 of the paper asks whether these hide
exponentially large constants and answers it only for `n = 1` or for a fixed `w`.

This result gives, under exactly the paper's assumptions, an explicit a-priori oracle complexity
for SCENT (with a sequential anchor batch of size `B ≥ 1`) in which the exponential scale `e^Δ`,
`Δ = c₁ − c₀`, is replaced where possible by the paper's own moment ratio `κ` and gradient proxy
`σ′`, and in which anchor batching provably reduces the iteration complexity down to a
`κ G² R² / ε²` floor. The guarantee is `E[F_CERM(w̄) − F_CERM(w⋆)] ≤ ε` for the average iterate,
after

  T = ⌈( 64 κ G² R² (1 + e^Δ ε) + 32 V R² (1 + ε) / B + 8 n e^Δ (1 + 64 (1 + Δ)(κ − 1)) (1 + ε) / B ) / ε² ⌉

iterations, `V = min(2 e^Δ σ′², e^{2Δ} G²)`, i.e. `(B + 1) T` oracle calls and `2 B T` samples.

The contribution is an explicit complexity statement and batch speedup for the *same* algorithm
family under the *same* assumptions, not a new rate: the `ε⁻²` order and the additive `n/ε²`
anchor term are unchanged. The improvement is in parameter dependence and is stated below with
its regimes.

## Setup (`CompositionalEntropicRisk.spec`)

Parameters `q`: a real inner-product space `E` (complete, Borel, second countable), a sample space
`Ξ`, the number of anchors `n ≥ 1`, the anchor batch size `B`, score bounds `c₀ ≤ c₁`, the gradient
second-moment bound `G`, the moment ratio `κ`, the weighted gradient bound `σ` (the paper's `σ′`),
the radius `R`, the accuracy `ε`, and the initial point `w₀`. `valid` is
`0 < B ∧ c₀ ≤ c₁ ∧ 0 < G ∧ 1 ≤ κ ∧ 0 ≤ σ ∧ 0 ≤ R ∧ 0 < ε`.

Instance: scores `score i w ζ`, subgradients `grad i w ζ`, per-anchor laws `law i`, a domain.
`objective I w = (1/n) Σ_i log ∫ exp(score i w ζ) d(law i)` is `F_CERM`.

Admissibility (every condition is from the paper; the paragraph after the list gives the mapping):
- the domain is closed and convex, `w₀` lies in it, and the projection oracle is a measurable
  Euclidean projection (`∀ x, ∀ u ∈ W, ⟪x − Π x, u − Π x⟫ ≤ 0`);
- `score i` and `grad i` are jointly measurable, and the subgradient inequality
  `score i x ζ + ⟪grad i x ζ, y − x⟫ ≤ score i y ζ` holds for all `x, y ∈ W` and all `ζ`;
- `c₀ ≤ score i x ζ ≤ c₁` for all `x ∈ W`, `ζ`;
- `∫ ‖grad i x ζ‖² d(law i) ≤ G²` for all `x ∈ W` (integrability included);
- `∫ exp(2 score i x ζ) ≤ κ (∫ exp(score i x ζ))²` for all `x ∈ W`;
- `∫ exp(2 score i x ζ) ‖grad i x ζ‖² ≤ σ² (∫ exp(score i x ζ))²` for all `x ∈ W`;
- a minimizer `w⋆ ∈ W` of `objective I` exists with `‖w₀ − w⋆‖ ≤ R`;
- the oracle is `sampleOracle I projection P`: the seeds of the oracle calls are IID with law
  `uniform(Fin n) ⊗ (⊗_i law i) ⊗ (⊗_i law i)` (reusing the repository's `IID` structure);
  a `sample w` query returns the drawn anchor `i` together with `(score i w ζ, grad i w ζ)` and
  `(score i w ζ′, grad i w ζ′)` for two independent samples `ζ, ζ′ ∼ law i`; a `projection x`
  query returns `Π x`. The anchor index is drawn by the oracle (uniformly, as in Algorithm 1 of
  the paper); the algorithm cannot choose which anchor it visits.

Provenance. The first three bullets are Assumption 3.2 (i) and (ii) of the paper (convexity of
`s_i(·; ζ)` is used there only through the subgradient inequality; we do not need
differentiability). The fourth is Assumption 3.2 (iii), stated for all `w ∈ W` rather than only
along the trajectory; the paper's proof of Lemma 3.4 uses it at the iterates, and the bias
inequality below needs it at the iterates as well, so the quantifier change is a faithful
clarification, not an added restriction. The fifth and sixth are Assumption 4.1 (i) and (ii)
of the paper (there stated for `n = 1` and, for (ii), along the trajectory), taken as a supremum
over anchors and over `w ∈ W`. Both are implied by Assumption 3.2 with `κ = e^Δ` and
`σ = e^Δ G` (`e^{s − μ} ≤ e^Δ` on `[c₀, c₁]`), so the theorem has a corollary under Assumption 3.2
alone with these substitutions. The existence of a minimizer within distance `R` is the paper's
`‖w₁ − w⋆‖` term. Sampling two fresh independent samples per visited anchor is Algorithm 1 of the
paper (`ζ_{i,t}` for the dual step, `ζ′_{i,t}` for the primal step). `0 < G` is harmless: any
instance with `G = 0` also satisfies the bound with any positive `G`.

Success: the output is measurable, lies in `W`, and
`∫ (objective I (output ω) − objective I w⋆) dP ≤ ε` for the product law of the algorithm seed and
the oracle seeds.

## Algorithm (`scent q η α T`)

The state carries the iteration counter, the sub-step counter `j`, the current point `w`, the dual
vector `ν ∈ ℝⁿ` (initialised to `c₁·1`), the accumulated primal estimator, the running sum of
iterates, and a pending projection proposal. One iteration consists of `B` sequential
`sample w` calls followed by one `projection` call:

- on reply `(i, (s, g), (s′, g′))`: `ν_i ← ν_i + log(1 + α e^{s}) − log(1 + α e^{ν_i})`, which is
  the paper's SPMD closed form `e^{ν_i^{new}} = e^{ν_i}(1 + α e^{s}) / (1 + α e^{ν_i})`
  (Lemma 3.1), and `acc ← acc + exp(s′ − ν_i^{new}) g′`;
- after the `B`-th sub-step the proposal `w − (η/B) acc` is sent to the projection oracle, and
  the reply becomes the next iterate; the dual vector is kept.

The output is the average `(1/T) Σ_{t<T} w_t` of the first `T` iterates (the paper's `w̄_T`).
The parameters are constants:

  η = 1 / (8 L₁/ε + 4 L₂),  L₁ = V/B + 2 κ G²,  L₂ = V/B + 4 e^Δ κ G²,
  α = 1 / (e^{c₁} + 8 C K/ε + 4 C K),  C = 2 (1 + Δ),  K = 4 (κ − 1) e^{c₁},

so `α e^{c₁} ≤ 1` (the paper's `α_t ≤ ρ min_i e^{−ν_{i,t−1}}` with `ρ = 1`, since
`ν ∈ [c₀, c₁]ⁿ`) and `η ∝ α` up to the burn-in terms (the paper's single time scale
`η_t = η α_t`). The algorithm uses only `c₀, c₁, G, κ, σ, R, n, B, ε`, all public parameters; the
paper's tuning likewise uses `c₁, Δ, G, R, n, B, T`.

Batch variant. The paper's Algorithm 1 draws a uniform subset of `B` anchors per iteration; here
the `B` anchors are drawn sequentially with replacement, and the dual update of sub-step `b` is
visible to the primal estimator of sub-step `b` and to later sub-steps. For `B = 1` the two
coincide exactly.

## Main theorem

`result : Convergence CompositionalEntropicRisk.spec budget` with

  budget q = (B + 1) ⌈( 64 κ G² R² (1 + e^Δ ε) + 32 min(2 e^Δ σ², e^{2Δ} G²) R² (1 + ε) / B
             + 8 n e^Δ (1 + 64 (1 + Δ)(κ − 1)) (1 + ε) / B ) / ε² ⌉.

Each iteration uses `B` sample calls (two samples each) and one projection call, and
`horizon_bound` plus `execute_scent` connect this count to the actual execution. The inequality
behind it (`expected_gap`, with `ρ = 1`) is, for any `η, α > 0` with `α e^{c₁} ≤ 1` and
`η L₂ + C α K ≤ 1/2`,

  E[F_CERM(w̄) − F_CERM(w⋆)] ≤ ‖w₀ − w⋆‖² / (η T) + 2 η L₁ + 2 C α K + 2 n e^{−c₀} / (α T B).

Reading the budget as a complexity:

- iteration complexity
  `T = O( κ G² R²/ε² + e^Δ κ G² R²/ε + [ e^Δ min(σ′², e^Δ G²) R² + n e^Δ (1 + (1+Δ)(κ−1)) ] (1/ε² + 1/ε) / B )`;
- sample complexity `2 B T`, minimised at `B = 1`:
  `O( [ κ G² R² + e^Δ min(σ′², e^Δ G²) R² + n e^Δ (1 + (1+Δ)(κ−1)) ] / ε² )` plus the
  `1/ε` burn-in terms.

The `1/ε` terms are a burn-in: they are dominated by the `1/ε²` terms once
`ε ≤ min(e^{−Δ}, 1)`.

## What is new relative to the paper

Closest statement: Theorem 3.6 of the paper, instantiated under Assumption 3.2 with
`ν₀ = c₁·1`. Using `σ_t² ≤ e^{2Δ} G²`, `δ_t² ≤ e^{2c₁ − c₀}/4`, `D_φ(ν⋆, ν₀) ≤ n e^{−c₀}`, and
optimising `η, α`, that theorem yields

  E[F_CERM(w̄_T) − F⋆] ≤ e^Δ ( R G + √(2 n (1 + Δ)/B) ) / √T,

i.e. iterations `e^{2Δ} (R² G² + n (1 + Δ)/B) / ε²` and samples `e^{2Δ} (B R² G² + n (1 + Δ)) / ε²`
(this instantiation is ours; the paper leaves `V` as a trajectory quantity). Lemma 4.2 of the
paper bounds `σ_t², δ_t²` by `(κ, σ′)` times powers of the *actual-sequence* gap
`F(w_t, ν_t) − F⋆` (quadratically for `σ_t²`), which is not closable for `n ≥ 2` because the
stale dual coordinates are not controlled by the regret bound; the paper closes the recursion
only for fixed `w` (Theorems 4.3, 4.5, E.10) and states a `(κ − 1)/T` lower bound for that
fixed-`w` dual problem (Theorem E.4).

Improvements in explicit regimes (same assumptions, same oracle, same criterion, same cost
accounting), at `B = 1`:

- the primal term `e^{2Δ} G² R²` becomes `κ G² R² + e^Δ min(σ′², e^Δ G²) R²`; since
  `κ ≤ e^Δ` this is never worse than `2 e^{2Δ} G² R²`, and it is smaller by the factor
  `≈ e^Δ G² / σ′²` whenever `σ′² ≪ e^Δ G²`;
- the anchor term `n (1 + Δ) e^{2Δ}` becomes `n e^Δ (1 + (1 + Δ)(κ − 1))`; since
  `κ − 1 ≤ e^Δ/4` this is never worse than `≈ n (1 + Δ) e^{2Δ}`, and it is smaller by the factor
  `≈ e^Δ / (κ − 1)` when `κ − 1 ≥ 1/(1 + Δ)`, and by `≈ (1 + Δ) e^Δ` when `κ − 1 ≪ 1/(1 + Δ)`.

With batching, the paper's primal term `e^{2Δ} G² R²` does not decrease in `B` (Lemma 3.4 uses
the full second moment `σ_t²`), while here the iteration complexity is
`κ G² R²/ε² + O(1/B)`: the `e^{2Δ}` in the paper's primal term is a variance effect that anchor
batching removes down to the Lipschitz floor of `F_CERM` (`‖∇F_CERM‖ ≤ √κ G`). The floor is
not proved optimal for the joint problem; Theorem E.4 of the paper shows only that `κ − 1`
is necessary for the fixed-`w` dual.

Worst case: under Assumption 3.2 alone (`κ = e^Δ`, `σ′ = e^Δ G`) the `B = 1` bound reduces to
the paper's instantiation up to absolute constants and the burn-in terms, so nothing is lost.

For `n = 1` the dual variable is a scalar scale and plain projected SGD with a fixed `ν` already
gives `e^{2Δ} G² R²/ε²`; the anchor-term gains above concern `n ≥ 2`, where the dual variables
reweight anchors against each other.

## Technical mechanism (new relative to the paper's proofs)

With `m_i(w) = E e^{s_i(w;ζ)}`, `μ_i = log m_i`, `u_i = μ_i(w) − ν_i`, `ψ(u) = e^u − 1 − u`,
the per-anchor dual gap is `F_i(w, ν_i) − min_ν F_i(w, ·) = ψ(u_i)`.

1. **Bias-to-gap inequality** (`AnchorHyp.bias_bound`, `gradW_sub_center_sq`):
   `‖∇_w F(w, ν) − ∇F_CERM(w)‖² ≤ 2 e^Δ κ G² · (1/n) Σ_i ψ(u_i)`, from `‖∇μ_i‖ ≤ √κ G`
   (Cauchy–Schwarz with Assumption 4.1 (i) and 3.2 (iii)) and the scalar inequality
   `(e^u − 1)² ≤ 2 e^{max(u,0)} ψ(u)` (`sq_exp_sub_one_le`). It lets the mean of the primal
   estimator be split from its noise, which is what makes the batch average effective.
2. **Linear self-bounding on the virtual sequence** (`exp_le_two_mul_one_add_psi`,
   `virtual_variance_bound`, `second_moment_gap`): `e^u ≤ 2 (1 + ψ(u))` applied to the
   *virtual* dual coordinates `ν̄_{i}` (the value anchor `i` would receive if drawn) gives
   `E‖piece‖² ≤ 2 e^Δ σ′² (1 + gap)` and `δ² ≤ 2 (1 + ρ)(κ − 1) e^{c₁} (1 + gap)` with the
   joint gap `F(w, ν̄) − F⋆` averaged over anchors; the paper's Lemma 4.2 is quadratic and uses
   the actual sequence. Linearity is what closes the recursion for `n ≥ 2`.
3. **Pre-update to post-update comparison** (`exp_neg_le_of_spmd`):
   `e^{−ν_{t−1}} ≤ (1 + ρ) e^{−ν̄_t}` under `α e^{c₁} ≤ ρ`, which replaces the paper's
   trajectory-dependent step constraint by the public one `α e^{c₁} ≤ 1`.
4. **Sequential batch with martingale orthogonality** (`inner_S_dZ_expect`, `Accsq_expect`):
   with-replacement sub-steps make each sub-step's conditional mean equal to
   `∇_w F(w_t, ν̄^{(b)})`, so `E‖acc‖² ≤ 2 Σ_b E‖piece_b‖² + 2 B Σ_b E‖mean_b‖²`, giving the
   `1/B` factor on the variance part only.
5. **Closing the self-bounding recursion** (`total_bound`): primal regret (`primal_total`),
   the paper's dual regret lemma reproved per sub-step with the virtual sequence
   (`anchor_regret`, `dual_telescope`), and the gap bounds above give
   `Σ gap ≤ X + q Σ gap` with `q = η L₂ + C α K ≤ 1/2`.
6. **Averaging through the supporting hyperplane of the joint objective** (`average_bound`):
   `1 + F_CERM(w̄) ≤ (1/(TB)) Σ_{t,b} virtualObj(w_t, ν̄_{t,b})` pointwise, by joint convexity of
   `(w, ν) ↦ m(w) e^{−ν} + ν` at the averaged point, so the expected gap is bounded by the
   average virtual gap without separately using convexity of `F_CERM`.

The randomness is handled on the product space of IID oracle seeds (`PP I = ⊗_ℕ sampleLaw I`),
with prefix-measurable states and the workhorse `substep_integral` for conditional expectations
of one sub-step.

## Example family

Entropic risk of a convex loss with bounded features, the paper's motivating application:
`s_i(w; ζ) = β ℓ(⟨w, φ(ζ)⟩, y(ζ))` for a convex Lipschitz loss `ℓ` (logistic, hinge, …) with
`‖φ‖ ≤ 1`, `W = {‖w‖ ≤ r}`, and anchors `i` indexing `n` groups or distributions `P_i`. Then
`c₀ = β ℓ_min`, `c₁ = β ℓ_max`, `Δ = β (ℓ_max − ℓ_min)` (e.g. `ℓ_max ≈ log(1 + e^r)` for the
logistic loss), `G ≤ β L_ℓ`, and the objective is the KL-DRO / entropic-risk objective, a
genuinely nonlinear function of `w` with interacting coordinates (its Hessian is the
exponentially tilted covariance of `β ℓ′ φ`). The moment ratio is
`κ_i(w) = E e^{2β ℓ} / (E e^{β ℓ})² = exp(K_i(2β) − 2 K_i(β))` for the cumulant generating
function `K_i` of the loss at `w`; for losses that are sub-Gaussian with variance proxy `τ²`
this is at most `e^{2 β² τ²}`, while `e^Δ = e^{β (ℓ_max − ℓ_min)}`. So for a large risk-aversion
parameter `β` with concentrated losses (`β τ² ≪ ℓ_max − ℓ_min`) the ratio `e^Δ/(κ − 1)` is
exponentially large, and the anchor term of the bound improves accordingly. Dimension enters
only through `G` (bounded features) and `τ`.

## Comparison with other methods

- Hu, Chen and He, *On the Bias-Variance-Cost Tradeoff of Stochastic Optimization*
  (NeurIPS 2021; journal version [arXiv 2408.11084](https://arxiv.org/abs/2408.11084), Theorem 6,
  Table 8): RT-MLMC gives an `n`-free `Õ(ε⁻²)` sample complexity for convex conditional
  stochastic optimization, but needs `s_i` almost surely Lipschitz and smooth (Assumption 4
  there), pays `log²(1/ε)` and constants of order `e^{4Δ}` for the log outer function. It is
  the better baseline when `n e^Δ (1 + (1+Δ)(κ−1)) ≫ e^{4Δ} G² R² log²(1/ε)`; it does not
  apply under Assumption 3.2 (iii) alone (second moment, no smoothness).
- Goda and Kitade, MCS 2023 ([arXiv 2206.01991](https://arxiv.org/abs/2206.01991)): unbiased
  antithetic MLMC gradients with finite variance give `n`-free `O(ε⁻²)` without logs, under
  higher moment conditions on `∇s` and `C²`-type smoothness of the outer function; not under
  Assumption 3.2.
- Wang and Yang, ALEXR (ICML 2025, [arXiv 2312.02277](https://arxiv.org/abs/2312.02277)):
  `O(n/ε²)` for convex finite-sum coupled compositional problems with convex monotone outer
  functions; the concave `log` is not covered, and its `Ω(n/ε²)` lower bound (Theorem 4) is for
  nonsmooth outer functions only, so it does not show that the `n/ε²` term here is optimal.
- Jiang et al., MSVR ([arXiv 2609.15723](https://arxiv.org/abs/2609.15723), unpublished 2026
  revision): `O(n/ε²)` for convex FCCO with smooth inner and outer functions; same `n`-order as
  SCENT under stronger assumptions.
- Gladin et al. (ICML 2026, [arXiv 2509.24894](https://arxiv.org/abs/2509.24894), Theorem 2.9)
  and Iashchinskaia and Gladin ([arXiv 2609.40120](https://arxiv.org/abs/2609.40120)): softplus
  surrogates with `ε⁻⁴` or `K²/ε²` complexities; worse in `ε` or in the number of normalizers.

None of these analyses SCENT or implies a `(κ, σ′)`-explicit bound for it.

## Limitations

- Same `ε⁻²` rate and same additive `n/ε²` anchor structure as the paper; improving the `n`-term
  to `n/ε` (or removing it without smoothness) is open and is not attempted here.
- The batch variant draws anchors with replacement and applies the sub-steps sequentially; the
  paper's uniform-subset batch is not formalised. The sample complexity is minimised at `B = 1`;
  the batch statement is an iteration/parallel-complexity statement.
- The burn-in terms (the `1/ε` part of the budget and the factor `(1 + e^Δ ε)`) are an artefact
  of the constant step sizes; they are lower order for `ε ≤ min(e^{−Δ}, 1)`.
- The tuning uses `κ` and `σ′` (or their Assumption 3.2 proxies `e^Δ`, `e^Δ G`), `R`, `G`, `n`,
  `B` and `ε`; no adaptivity is claimed.
- The absolute constants (`64`, `32`, `8·64`) were simplified for a one-line budget and are not
  optimised.
- The `κ G² R²/ε²` floor is an upper bound; no matching lower bound for the joint problem is
  known.

## Verification

`./build.sh`, `./lint.sh`, and `python3 run_comparator.py ScentCompositionalEntropicRisk.lean`
were run on the final integrated files by the independent Reviewer in a clean worktree on the
recorded base; all three pass, and the theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
