# Stochastic nonconvex composite optimization at the ε^{-7/2} rate under second-order smoothness

The [main theorem](CompositeImplicitTransport.lean) (`OracleTemplate.CompositeTransport.result`) constructs the
[prox-transport algorithm](../Algorithms/CompositeTransport.lean) for the
[stochastic composite Lipschitz-Hessian specification](../Setups/StochasticCompositeHessianLipschitz.lean) and bounds the total
number of oracle calls (stochastic gradients **and** prox evaluations) needed to reach expected composite stationarity
with one stochastic gradient per step and no mean-squared smoothness.

## Problem, information and criterion

Minimize F = f + ψ over a finite-dimensional real inner-product space E.

- f : E → ℝ has gradient `grad` everywhere, `grad` is L-Lipschitz, and `grad` has Fréchet derivative `hess` with
  ‖hess x − hess y‖ ≤ ρ‖x − y‖ (operator norm) **on all of E**; f may be nonconvex.
- ψ is convex on a convex set Q (ψ = +∞ outside Q is the intended reading; only values on Q matter). Q may be unbounded;
  ψ may be nonsmooth (ℓ1, group norms, nuclear norm, indicators of projection-friendly closed convex sets, …).
- x₀ ∈ Q and F(x₀) − F(x) ≤ Δ for every x ∈ Q.
- Oracle (one channel, two query kinds, each answer counts as one call):
  `gradient x` returns g(x, ξ_k) with IID samples ξ_k (repository `IID` structure), jointly measurable, unbiased
  (∫ g(x,ω) dμ = ∇f(x)) and with ∫ ‖g(x,ω) − ∇f(x)‖² dμ ≤ σ²;
  `prox a z v` (a > 0) returns the exact minimizer over Q of ‖u − z‖²/(2a) + ⟨v, u − z⟩ + ψ(u), assumed to exist, with a
  measurable prox map. No function values, Hessians, Hessian–vector products, or minimizer information are given.
- Public parameters: L, ρ, σ, Δ, ε, x₀ (all used for tuning, as in Cutkosky–Mehta).
- Criterion: the output X ∈ Q a.s. and **E‖G(X)‖ ≤ ε**, where G(x) = L(x − prox_{1/L}(x, ∇f(x))) is the standard
  (unscaled) gradient mapping built from the true gradient and the exact prox.

## Algorithm and output

`transport` (Algorithm file) with tuned constants from `tunedConfig` ([tuning](../Proofs/CompositeTransportTuning.lean)),
ε' = ε/3, α = ε'²/(ε'² + 120σ²), γ = 1/(L + 7√(ρε')/α), n₀ = ⌈120σ²/ε'²⌉ + 1, T = ⌈Δ/(γε'²)⌉:

1. m₀ = average of n₀ stochastic gradients at x₀.
2. For t = 0, 1, …: p_t = prox_γ(x_t, m_t); **capped step** x_{t+1} = x_t + min(1, 2γε'/‖p_t − x_t‖)(p_t − x_t)
   (a convex combination, so x_{t+1} ∈ Q); **implicit gradient transport**: query the gradient at
   w_t = x_{t+1} + ((1−α)/α)(x_{t+1} − x_t) and set m_{t+1} = (1−α)m_t + α g(w_t, ξ).
3. The algorithm draws τ uniformly from {0,…,T} with its own seed (independent of the samples), stops after τ
   iterations and returns x_τ. Remaining budgeted calls are padding and are counted.

## Guarantee

The public budget is the single line

⌈10⁶ (LΔ/ε² + (1 + σ²/ε²) Δ√(ρε)/ε² + σ²/ε² + 1)⌉,

i.e. O(LΔε⁻² + Δ√ρ ε^{-3/2} + **σ²√ρ Δ ε^{-7/2}** + σ²ε⁻²) total oracle calls (n₀ + 2T, gradients and proxes together).
The Δ√ρ ε^{-3/2} term is dominated by LΔε⁻² whenever ε ≤ L²/ρ. The proof establishes (`expected_bound`)
∫ ‖G(x_τ)‖ ≤ 3ε' = ε over the product of the uniform index law and the IID stream, together with measurability,
integrability and x_τ ∈ Q.

## Proof mechanism (where the composite structure enters)

- **Error split.** With e_t = m_t − ∇f(x_t): e_t = N_t + β_t exactly, where N_{t+1} = (1−α)N_t + α(g(w_t,ξ) − ∇f(w_t))
  is martingale noise and β_{t+1} = (1−α)β_t + b_t is transport bias. The choice of w_t cancels the first-order term,
  so ‖b_t‖ ≤ (ρ/α)‖x_{t+1} − x_t‖² ([step lemmas](../Proofs/CompositeTransportStep.lean), `transport_bias`), and the
  cap gives ‖x_{t+1} − x_t‖ ≤ 2γε' **pathwise**, hence ‖β_t‖ ≤ ρ(2γε')²/α² ≤ 4ε'/49 for all t.
- **Noise.** E‖N_t‖² ≤ σ²/n₀ + ασ² for all t ([moments](../Proofs/CompositeTransportMoments.lean)), by a lintegral recursion
  using freshness of the sample at the transported query.
- **Capped composite descent** (replaces normalization, which has no composite analogue): from prox optimality and
  convexity of ψ along the segment, ε'‖p_t − x_t‖ ≤ F(x_t) − F(x_{t+1}) + γ(9‖e_t‖² + 9ε'²/8) in both the capped and
  uncapped branch (`capped_progress`). The uncapped branch is quadratic in the step, the capped branch linear; the
  common bound is what turns the potential into a bound on E‖G‖ (not only on a truncated square).
- **From the noisy step to the true gradient mapping.** Prox nonexpansiveness bounds ‖prox_γ(x,m) − prox_γ(x,∇f(x))‖ by
  γ‖e‖, and the monotonicity ‖G_{1/L}(x)‖ ≤ ‖G_γ(x)‖ for γ ≤ 1/L (`mapping_antitone`, proved from the prox optimality
  condition only; cf. Beck, *First-Order Methods in Optimization*, SIAM 2017, Thm. 10.9) gives the stated criterion.
- Telescoping over t ≤ T and averaging over the uniform τ ([assembly](../Proofs/CompositeTransportMain.lean)).

## Comparison with prior work

| Work | Setting / oracle | Criterion | Rate (single sample, bounded variance) |
|---|---|---|---|
| [Arjevani et al., COLT 2020, arXiv 2006.13476](https://arxiv.org/abs/2006.13476), eq. (10) | ψ = 0, gradient-only, single-point queries, L, ρ | ‖∇f‖ ≤ ε | **lower bound** Ω(Δ√ρσ²ε^{-7/2}) |
| [Cutkosky–Mehta, ICML 2020](https://arxiv.org/abs/2002.03305); [Kovalev, arXiv 2503.12645](https://arxiv.org/abs/2503.12645) | ψ = 0 (unconstrained), normalized / trust-region momentum with extrapolation | E‖∇f‖ ≤ ε | O(ε^{-7/2}) |
| [Gao–Rodomanov–Stich, ICML 2024, arXiv 2403.02967](https://arxiv.org/abs/2403.02967) | composite prox, Polyak momentum, no second-order smoothness used | E‖G‖ ≤ ε | O(LΔσ²ε⁻⁴) |
| He–Deng, *Stochastic interior-point methods for smooth conic optimization*, JMLR 26 (2025) | Ax = b, x ∈ K (cone), interior-point with extrapolated momentum, locally Lipschitz Hessian | barrier-scaled residual | Õ(ε^{-7/2}) |
| [Jang–Lee, arXiv 2605.05577](https://arxiv.org/abs/2605.05577) (preprint) | LMO over compact centrally symmetric sets / unconstrained | Frank–Wolfe gap (RSF) | O(ε^{-7/2}) for the gap |
| Composite STORM / ProxSARAH | requires mean-squared smoothness (stronger, different assumption) | E‖G‖ ≤ ε | O(ε⁻³) (not comparable) |
| **This theorem** | general prox-friendly convex ψ (incl. unbounded sets, ℓ1), global L, ρ | **E‖G_{1/L}‖ ≤ ε (unscaled)** | **O(LΔε⁻² + σ²√ρΔε^{-7/2} + σ²ε⁻²)** |

What is new. To our knowledge (web search over 2024–2026 composite/constrained stochastic methods with second-order
smoothness, proximal implicit gradient transport, and constrained IGT; the arXiv API was unavailable, so a missed
preprint is possible), this is the first single-sample, gradient-only guarantee at the ε^{-7/2} order for **general**
prox-friendly composite problems with the standard unscaled gradient-mapping criterion. Its noise term σ²√ρΔε^{-7/2}
matches the Arjevani et al. single-point lower bound for ψ = 0 (so it is optimal in that term); relative to the best
composite single-sample baseline (Gao et al.) the noise term improves by a factor ≈ L/√(ρε) when ε ≪ L²/ρ.

Relation to the closest results.
- *He–Deng* already combine extrapolated momentum with movement-confined (Dikin-ellipsoid) steps under conic
  constraints, so "transport + bounded movement under constraints" is not new as a mechanism. Their criterion is
  barrier-scaled and strictly weaker near the boundary (for K = ℝⁿ₊, x_i = √ε, ∇_i f = √ε gives scaled residual ε but
  |G_i| ≈ √ε), it carries polylog factors and an interior-point method, and it covers cones/affine constraints only,
  not nonsmooth regularizers.
- *Jang–Lee* use an LMO oracle on compact sets and the Frank–Wolfe gap. On a compact P with diameter D_P one has
  gap(x) ≥ ⟨∇f(x), x − p⟩ ≥ ‖G(x)‖²/L (projection inequality, p = Π_P(x − ∇f(x)/L)) and gap(x) ≤ ‖G(x)‖(D_P + ‖∇f(x)‖/L);
  so their result yields ‖G‖ ≤ ε only through gap ≤ ε²/L, i.e. at O(ε^{-7}), while ours implies a gap bound at the same
  ε^{-7/2} order on compact sets. The oracles differ (LMO vs prox), so no dominance is claimed.
- *Cutkosky–Mehta* normalize the momentum; normalization has no meaning for the prox-gradient mapping. Here the
  movement cap (a convex combination with the current point) plays its role.

Limitations and honest scope.
- At σ = 0 the LΔε⁻² term is **not** optimal: for ψ = 0, Carmon–Duchi–Hinder–Sidford (ICML 2017) and Li–Lin (2022)
  obtain ε^{-7/4} under the same smoothness; whether a composite ε^{-7/4} first-order method exists is open (we do not
  address it). Optimality is claimed only for the noise term.
- The Hessian must be Lipschitz on all of E (not only on Q), because the transported queries w_t may leave Q; their
  distance from x_{t+1} is at most (1−α)2γε'/α = O(√(ε/ρ)).
- Parameters L, ρ, σ, Δ, ε are assumed known; the method is not adaptive. The output is a uniformly random iterate
  (expected-accuracy criterion, no high-probability statement). Constants are conservative (10⁶).
- Technical depth is modest: the contribution is a composite-scope extension of the optimal second-order-smooth
  stochastic rate, in the spirit of extending a guarantee to the composite setting.

Example family. Robust regression with the Cauchy loss, f(x) = (1/n)Σ_i φ(a_iᵀx − b_i), φ(t) = log(1 + t²), with
ψ = λ‖x‖₁ or the indicator of a box: |φ''| ≤ 2 and |φ'''| ≤ 3 give L ≤ 2 max_i‖a_i‖² and ρ ≤ 3 max_i‖a_i‖³ globally;
sampling a row uniformly gives an unbiased oracle with |φ'| ≤ 1, so σ ≤ max_i‖a_i‖. The objective is nonconvex with
interacting coordinates, and the bound is dimension-free.
