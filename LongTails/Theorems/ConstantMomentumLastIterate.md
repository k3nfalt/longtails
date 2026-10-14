# Constant-momentum SGD with an affine step-size decay: an optimal, log-free last-iterate rate

This note explains the contribution formalized in
[ConstantMomentumLastIterate.lean](ConstantMomentumLastIterate.lean), with
[setup](../Setups/MomentumLipschitzConvex.lean),
[algorithm](../Algorithms/ConstantMomentumSgd.lean) and proof modules
[Weights](../Proofs/MomentumLastIterateWeights.lean),
[Recursion](../Proofs/MomentumLastIterateRecursion.lean),
[Sample](../Proofs/MomentumLastIterateSample.lean),
[Trajectory](../Proofs/MomentumLastIterateTrajectory.lean),
[Expectation](../Proofs/MomentumLastIterateExpectation.lean),
[Gap](../Proofs/MomentumLastIterateGap.lean),
[Descent](../Proofs/MomentumLastIterateDescent.lean),
[Convergence](../Proofs/MomentumLastIterateConvergence.lean).

**Summary.** SGD with momentum in the exponential-moving-average form
m_t = β m_{t−1} + (1−β) g_t, x_{t+1} = x_t − η_t m_t with a *constant* momentum β is the form used in
practice. For convex Lipschitz objectives, Li, Liu and Orabona (ALT 2022) proved that with polynomial
step sizes η_t = c·t^{−α} its last iterate is Ω(ln T/√T) for every constant β, and proposed changing the
algorithm (increasing momentum). We prove that the same constant-β method, run for a known horizon N
with the affine schedule η_t = γ(N + 1 − t + κ), κ = β/(1−β), has

  E f(x_N) − f* ≤ (4·G·R/√(N+2)) · [1 + κ/√(N+2) + κ²·log(N+2)/(N+2)]  for every N ≥ 1 and β ∈ [0, 1),

so the last iterate attains the minimax rate G·R/√N without a logarithm, with a leading constant that
does not depend on β, once N ≳ κ²·log(1/(1−β)). The oracle complexity is
⌈100·G²R²/ε²⌉ + ⌈4κ²(1 + log(1/(1−β)))⌉ stochastic subgradient calls. The rate itself is the known optimal
rate for the problem class; what is new is that a constant-momentum method attains it at the last
iterate, and the weight construction that proves it.

## Setup and proved guarantee

- **Space.** E is a real separable Hilbert space of any dimension (complete, second countable, Borel).
- **Objective.** f : E → ℝ convex with a minimizer x*, ‖x₀ − x*‖ ≤ R. No smoothness, no strong convexity,
  no bounded domain.
- **Oracle.** A stochastic subgradient oracle G(ξ, x), jointly measurable, with i.i.d. samples ξ₀, ξ₁, …
  from an arbitrary law. For every x: E‖G(ξ, x)‖² ≤ G² and the mean E G(ξ, x) is a subgradient of f at x,
  i.e. f(y) ≥ f(x) + ⟨E G(ξ, x), y − x⟩ for all y. Deterministic subgradients with norm at most G are the
  special case of a point-mass law. Each query costs one call.
- **Validity.** G > 0, R ≥ 0, 0 ≤ β < 1, ε > 0.
- **Information.** The algorithm is built from (G, R, β, ε, x₀). It needs the horizon.
- **Admissible algorithms.** `allowedAlgorithm` admits only the state machine below with the public β,
  started at x₀ with zero momentum, for some scale γ and horizon N. The theorem is a statement about
  this method.
- **Success.** E f(x_out) − f(x*) ≤ ε, expectation over the oracle samples.

**Algorithm** (eq. (1) of Li–Liu–Orabona with constant β). m_{−1} = 0 and, for t = 0, …, N − 1,

  g_t = G(ξ_t, x_t),  m_t = β m_{t−1} + (1−β) g_t,  x_{t+1} = x_t − η_t m_t,
  η_t = γ·(N + 1 − t + κ),  κ = β/(1−β),  γ = R/(G·(N+2)^{3/2}).

The output is the last iterate x_N. Exactly N oracle calls are made. The schedule is affine in t; it is
the linear-decay-to-zero schedule for horizon N + 1 + κ stopped κ + 1 steps early, so its final value is
γ(κ + 2) rather than 0. The offset depends on β.

**Guarantee** (`theorem result : Convergence spec budget`). With

  budget = ⌈100·G²·R²/ε²⌉ + ⌈4·(β/(1−β))²·(1 + log(1/(1−β)))⌉

calls the last iterate satisfies E f(x_N) − f* ≤ ε. The proof modules contain the bound for every horizon:
`Hyp.expected_gap` gives, for all N and γ > 0,

  2u₁·(E f(x_N) − f*) ≤ W(N+2)·‖x₀−x*‖² + 2ν·(f(x₀) − f*) + (2γ(N+1) + 4κ²γ·log(N+2))·G²,

with u₁ = (3+κ)/(6(1+κ)) + 2κ/(2+3κ) ≥ 1/2, W(N+2) ≤ 2/(γ(N+2)²), ν ≤ 2κ/(N+2), and `final_bound` turns
it into the displayed inequality of the summary for the stated γ.

## Mechanism

Write T = N + 1 and τ = T − t.

1. **Exact virtual iterate.** z_t = x_t − κγτ·m_{t−1} satisfies z_{t+1} = z_t − γτ·g_t (`zed_succ`). This
   is where the offset κ in the schedule is used: it makes the virtual steps exactly linear in τ. The
   step at t = N exists only in the analysis; it uses a subgradient at x_N that the algorithm never
   requests.
2. **Momentum telescoping** (classical; Ghadimi–Feyzmahdavian–Johansson 2015). Because
   x_t − x_{t−1} = −η_{t−1} m_{t−1}, convexity gives, for every w,
   ⟨E g_t, z_t − w⟩ ≥ (1+κ_t)(f(x_t)−f*) − κ_t(f(x_{t−1})−f*) − (f(w)−f*), κ_t = κτ/(τ+1+κ)
   (`Hyp.one_sample`, `traj_prev`). For averaged iterates this already gives constants independent of β.
3. **Last-iterate references** (Zamani–Glineur 2023, Liu–Zhou 2024). w_t is a convex combination of x*
   and x₀, …, x_t with weights ω_t: w_t = (ω_{t−1}/ω_t)·w_{t−1} + (1 − ω_{t−1}/ω_t)·x_t.
4. **New: the weights.** Combining 2 and 3, the coefficient of the intermediate gap E f(x_t) − f* in the
   summed inequality is u_t − u_{t+1} with u_t = ω_{t−1}Γ_{t−1} + κ_tγ_tω_t, Γ_{t−1} = Σ_{r≥t} γ_r. With the
   Zamani–Glineur choice ω = 1/Γ these coefficients are negative as soon as β > 0, and nothing bounds the
   intermediate gaps. We take

     ω_t = W(τ) = 2(τ+1+κ)/(γ·τ²·(τ+1+3κ)),

   for which u(τ) = τ(τ+2+κ)/((τ+1)(τ+2+3κ)) + 2κ/(τ+1+3κ) is nondecreasing in τ (`uu_mono`: the numerator
   of u(τ) − u(τ−1) is a polynomial in τ − 2 and κ with nonnegative coefficients), so all intermediate
   coefficients are nonnegative, and the coefficient of the last gap is u(1) ≥ 1/2 (`uu_one`). The
   potential is

     Φ_t = ω_{t−1}·E‖z_t − w_{t−1}‖² + 2Γ_{t−1}ω_{t−1}·E(f(w_{t−1})−f*) + 2κ_tγ_tω_t·E(f(x_{t−1})−f*),

   and `core_step` shows Φ_{t+1} ≤ Φ_t + e_t − 2(u_t − u_{t+1})·E(f(x_t) − f*).
5. **Cost of momentum.** The references are combinations of the x_s, not of the z_s (otherwise the
   error is of leading order). Jensen then costs (ω_t − ω_{t−1})·‖z_t − x_t‖² = (ω_t − ω_{t−1})(κγτ)²‖m_{t−1}‖²,
   at most 4κ²γG²/(τ+1) in expectation (`jensen_le`, `Hyp.moment`); summed, this is the κ²·log term. The
   first step contributes 2κ_0γ_0ω_0·(f(x₀) − f*) ≤ 4κGR/(N+2), the κ/√N term.

An LP over all weight sequences admissible for this argument (not part of the repository) indicates
that the best leading constant of the technique is 2 for every κ, with a correction of order κ/√N; our
closed-form weights give 4.

## What is known, and what is new

| source | method | step sizes | guarantee for convex G-Lipschitz f |
|---|---|---|---|
| Li, Liu, Orabona, ALT 2022, [arXiv:2102.07002](https://arxiv.org/abs/2102.07002), Thm 1 | SGDM eq. (1), any constant β | polynomial c·t^{−α}, α ∈ [0, 1/2] | lower bound: last iterate ≥ L²(1−β)²c·ln T/(4T^α); with c ∝ 1/√T or α = 1/2 this is Ω(ln T/√T) |
| same paper, Thms 2–3 | FTRL-based momentum, **increasing** momentum | horizon-free | last iterate O(1/√T) |
| Jain, Nagaraj, Netrapalli, COLT 2019 | SGD (β = 0) | horizon-dependent, piecewise | last iterate O(1/√T) |
| Zamani, Glineur, SIOPT 2025, [arXiv:2307.11134](https://arxiv.org/abs/2307.11134) | subgradient method (β = 0) | linear decay | last iterate exactly G·R/√(T+1), minimax optimal; momentum appears only in a conjecture |
| Liu, Zhou, ICLR 2024, [arXiv:2312.08531](https://arxiv.org/abs/2312.08531) (v4) | SGD, composite, general domains | general | last iterate O(1/√T) without log; explicitly without momentum or averaging |
| Tao et al., ICLR 2021; Sebbouh, Gower, Defazio, COLT 2021, [arXiv:2006.07867](https://arxiv.org/abs/2006.07867) | heavy ball | **time-varying** momentum β_t → 1 | last iterate O(1/√T) |
| Hudiani, [arXiv:2507.07281](https://arxiv.org/abs/2507.07281) (v4) | stochastic heavy ball, constant β; a different class (convex with Hölder/Lipschitz gradient) | polynomial t^{−p}, p ∈ (1/2, 1) | last iterate O(t^{max(p−1, 1−2p)}·log²(t/δ)) with probability 1 − δ; slower than 1/√t and with logarithms |
| Ghadimi, Feyzmahdavian, Johansson, ECC 2015, [arXiv:1412.7457](https://arxiv.org/abs/1412.7457) | heavy ball, constant β | constant | Cesàro averages; source of the telescoping in step 2 |
| Kornowski, Shamir, [arXiv:2604.13870](https://arxiv.org/abs/2604.13870) | SGD/GD, any horizon-free schedule | — | lower bound: an extra polylog factor is unavoidable for anytime last iterates |
| this repository, [LinearDecaySgdLastIterate](LinearDecaySgdLastIterate.lean) | SGD (β = 0), smooth convex | linear decay | last iterate without log; same Zamani–Glineur mechanism, no momentum |
| **this theorem** | SGDM eq. (1), any constant β ∈ [0,1) | affine decay γ(N+1−t+κ) | E f(x_N) − f* ≤ (4GR/√(N+2))(1 + κ/√(N+2) + κ²log(N+2)/(N+2)) |

**New.** To our knowledge this is the first log-free O(G·R/√N) last-iterate bound for SGD with a
constant momentum parameter on convex Lipschitz objectives, and the leading constant is independent of
β. It shows that the ln T factor in the Li–Liu–Orabona lower bound comes from the polynomial step sizes
(as at β = 0, where it is the Harvey et al. construction) and not from constant momentum. The technical
contribution is step 4: the weight sequence that keeps every intermediate coefficient nonnegative when
the momentum telescoping is combined with last-iterate references.

**What a standard reduction gives.** Steps 1–3 with references built from the z_s, or treating g_t as an
ε-subgradient at z_t, give O(G·R·√((1+β)/(1−β))/√N) for f(z_N). The β-independence of the leading constant
is expected from step 2 (it is classical for averages); the new part is making it compatible with the
last-iterate weights. The result is not an improvement of the oracle complexity of the problem class.

**Novelty status.** Based on searches of arXiv and the cited papers (October 2026); we did not find the
statement, but we cannot exclude an overlooked reference.

## Numerical check (not part of the proof)

Exact worst cases from the performance-estimation SDP for the algorithm above with G = R = 1 and the
theorem's γ, reported as √(N+2) × (worst-case f(x_N) − f*):

| β | N = 4 | N = 8 | N = 16 | N = 32 | N = 64 | N = 96 |
|---|---|---|---|---|---|---|
| 0 | 1.11 | 1.07 | 1.04 | 1.02 | 1.01 | – |
| 0.5 | 1.10 | 1.06 | 1.03 | 1.02 | 1.01 | – |
| 0.9 | 1.35 | 1.54 | 1.52 | 1.29 | 1.15 | – |
| 0.99 | 1.41 | 1.85 | 2.87 | 4.55 | 5.09 | 5.01 |

For β = 0.99 the normalized worst case exceeds 4 for N between 32 and 96 (it peaks near N = 64 and
then decreases; larger N did not fit in memory), so for this schedule a term that grows with κ at
moderate N cannot be avoided; it is not an artifact of the proof. The proved bound is very loose in that
regime (at β = 0.99, N = 32 it is about 4·10³ against 4.55). For β ≤ 0.9 the true constant is close to 1,
against the proved 4.

## Limitations

- **Schedule.** The schedule is affine with a β-dependent offset. Plain linear decay to zero in the EMA
  form is not covered: its virtual steps are γ₀(τ − κ(1 − β^τ)) and we have no closed-form weights for it.
- **Heavy-ball form.** For x_{t+1} = x_t − η_t g_t + β(x_t − x_{t−1}) with η_t = (1−β)γ(N+1−t) the same
  argument works on paper with constant κ_t = κ and W(τ) = 2/(γτ(τ+2κ+1)), with a larger lower-order term
  (κ³/N^{3/2}). It is not formalized and not claimed.
- **No general step-size theorem.** The sign condition in step 4 depends on the schedule.
- **Unconstrained.** A projection breaks the virtual-iterate identity. Zamani–Glineur and Liu–Zhou
  handle constraints at β = 0.
- **Constants.** Leading constant 4, against the exact 1 of Zamani–Glineur at β = 0. The burn-in
  4κ²(1 + log(1/(1−β))) is about 1.8·10⁵ calls at β = 0.99.
- **Horizon.** N must be known. At β = 0 this is unavoidable for log-free rates (Kornowski–Shamir).
- **Mode of convergence.** In expectation only; i.i.d. samples.

## Lean layout

- `Weights`: W, u and the rational inequalities (`wt_anti`, `uu_mono`, `uu_one`, `noise_le`, `jensen_le`).
- `Recursion`: `core_step`, `potential_bound` (the abstract recursion on real sequences), the harmonic
  sum, `final_bound`, `budget_bound`.
- `Sample`: consequences of the oracle assumptions for one sample (`norm_mean_le`, `lip`, `one_sample`,
  `moment_sample`).
- `Trajectory`: the trajectory, references and virtual iterate as functions of the sample sequence;
  `zed_succ`, `traj_prev`; measurability and dependence on a prefix.
- `Expectation`, `Gap`, `Descent`: square-integrability, E‖m_t‖² ≤ G², the three expected one-step
  inequalities and `Hyp.expected_gap`.
- `Convergence`: the execution of the state machine equals the analysed trajectory with N calls, and
  the budget suffices.
