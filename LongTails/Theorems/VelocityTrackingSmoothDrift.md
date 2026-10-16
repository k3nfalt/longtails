# Velocity-tracking stochastic gradient for smoothly drifting strongly convex objectives

The [main theorem](VelocityTrackingSmoothDrift.lean) is a finite-time mean-square tracking guarantee for nonstationary stochastic optimization. The objective is a sequence of μ-strongly convex, L-smooth functions f₀, f₁, … on a Hilbert space. Each oracle call t returns one unbiased stochastic gradient of the current function f_t, with variance at most σ². The minimizers θ*_t move along a path whose second differences have norm at most Γ. Nothing bounds their speed after the first step.

A velocity-tracking method uses one stochastic gradient per time step. It attains squared tracking error ε for every ε satisfying

  9792 Γ² (2L/μ + 99σ²/(μ²ε))⁴ ≤ ε.

Up to constants this condition says ε ≳ (σ²/μ²)^{4/5} Γ^{2/5} + κ⁴Γ², with κ = L/μ. The number of calls needed is O((κ + σ²/(μ²ε)) · log(1 + (R² + V²(κ + σ²/(μ²ε))²)/ε)), and the bound then holds at every later time. The first floor term is minimax-optimal up to a constant (§4). SGD, which the focus paper shows beats momentum methods under drift, cannot go below (Δσ²/μ²)^{2/3} on a constant-velocity path with speed Δ (§4). So when Γ ≪ Δ, a different kind of "momentum", one that estimates the drift velocity instead of averaging gradients, provably beats SGD.

## 1. Setup, algorithm, and proved guarantee

**Setup** ([SmoothDriftStronglyConvex](../Setups/SmoothDriftStronglyConvex.lean)).

- **Space.** E is a real Hilbert space (complete, Borel, second countable), of any dimension. The instance is a sequence f : ℕ → E → ℝ.
- **Regularity, uniform in t.** Each f_t has a gradient everywhere. It satisfies the first-order μ-strong-convexity inequality f_t(x) + ⟨∇f_t(x), y − x⟩ + (μ/2)‖y − x‖² ≤ f_t(y), and ∇f_t is L-Lipschitz. The shape of f_t may change arbitrarily over time.
- **Oracle.**
  - Call number k is answered by `oracle k x ξ_k`.
  - The seeds ξ_k are i.i.d. with law `Measure.infinitePi` of a probability measure P.
  - Each map (x, ξ) ↦ oracle k x ξ is jointly measurable and satisfies the repository's `IsStochasticGradient` for f_k: ∫ oracle k x ξ dP = ∇f_k(x) and ∫ ‖oracle k x ξ − ∇f_k(x)‖² dP ≤ σ² for all x.
  - Time-dependent maps of i.i.d. seeds represent any sequence of independent, drifting data distributions.
- **Drift.** There are minimizers θ*_k of f_k satisfying three conditions:
  - ‖x₀ − θ*₀‖ ≤ R;
  - ‖θ*₁ − θ*₀‖ ≤ V;
  - ‖(θ*_{k+2} − θ*_{k+1}) − (θ*_{k+1} − θ*_k)‖ ≤ Γ for all k.

  The path is deterministic, so the environment is oblivious.
- **Public data.** The algorithm receives E, the seed space, μ, L, σ, ε and x₀. It does not receive Γ, R, V or the horizon slack H.
- **Validity.** 0 < μ ≤ L, σ, Γ, R, V ≥ 0, ε > 0, and the floor condition 9792 Γ² (2L/μ + 99σ²/(μ²ε))⁴ ≤ ε, stated explicitly in `valid`.
- **Output and accuracy.** The output is a pair (point, clock). `allowedAlgorithm` only asks the algorithm to carry an honest call counter:
  - there is a map clock : State → ℕ with clock(initial) = 0 and clock(update s r) = clock(s) + 1;
  - the output's second component equals clock.

  The predicate does not restrict the update rule. Success means ∫ ‖x_out − θ*_{clock−1}‖² ≤ ε, with the required integrability. So the output is judged against the minimizer of the last queried function, at the moment execution stops.

**Algorithm** ([VelocityTrackingSgd](../Algorithms/VelocityTrackingSgd.lean)).

- **State.** The state is (count, x, v), starting from v₀ = 0.
- **Step.** At call t the algorithm queries y_t = x_t + v_t, the position predicted with the current velocity estimate. It receives g_t = oracle t y_t ξ_t and updates
  - x_{t+1} = y_t − γ g_t,
  - v_{t+1} = v_t − β g_t.
- **Tuning.** γ = με/(99σ² + 2Lμε) and β = γ²μ/4, so 1/(γμ) = Q := 2L/μ + 99σ²/(μ²ε). Both γ and β depend only on public data.
- **As a momentum method.** Eliminating v gives x_{t+1} = x_t + (x_t − x_{t−1}) − (γ + β) g_t + γ g_{t−1}. This is heavy-ball momentum with parameter exactly 1 plus a gradient correction: a discrete double integrator, or α–β filter.

**Budget** (one line in the theorem file):

  ⌈16 (2L/μ + 99σ²/(μ²ε)) · log(1 + (15R² + 45V²(2L/μ + 99σ²/(μ²ε))²)/ε)⌉₊ + H + 1,

where H ∈ ℕ is a free slack parameter. Every call is counted: each time step costs exactly one stochastic gradient. Because H is arbitrary, the theorem certifies accuracy ε at every time after the burn-in.

**Proved bound before tuning** ([VelocityTrackingRun](../Proofs/VelocityTrackingRun.lean), `expected_error`). Let s = γμ. For every γ with γL ≤ 1/2 and every K,

  E‖x_{K+1} − θ*_K‖² ≤ 2(1 − s/16)^K (5R²/2 + 15V²/(2s²)) + 3264 Γ²/s⁴ + 32γσ²/μ + γ²σ².

[VelocityTrackingConvergence](../Proofs/VelocityTrackingConvergence.lean) checks that the budget and the tuning make the right-hand side at most ε.

## 2. Mechanism

Write p_t = y_t − θ*_t for the prediction error and u_t for the previous velocity: u_t = θ*_t − θ*_{t−1} for t ≥ 1 and u₀ = θ*₁ − θ*₀. Define:

- ŵ_t = (v_t − u_t)/s, the scaled velocity error;
- G_t = γ∇f_t(y_t), the scaled gradient;
- n_t = γ(g_t − ∇f_t(y_t)), the scaled noise;
- d_t = u_t − u_{t+1}, so that ‖d_t‖ ≤ Γ and d₀ = 0.

The algorithm gives exactly

  p_{t+1} = p_t + s ŵ_t − (1 + s/4)(G_t + n_t) + d_t,  ŵ_{t+1} = ŵ_t − (G_t + n_t)/4 + d_t/s.

1. **Sector facts.** These hold for each f_t relative to its own minimizer, whatever its shape ([VelocityTrackingStep](../Proofs/VelocityTrackingStep.lean), `sector`):
   - strong monotonicity, ⟨G, p⟩ ≥ s‖p‖²;
   - co-coercivity, ⟨G, p⟩ ≥ ‖G‖²/(γL) ≥ 2‖G‖².

   Convexity is derived from the first-order inequality, and co-coercivity comes from the repository lemma `SampledConvex.cocoercive`.
2. **One quadratic Lyapunov function for all sector-bounded maps** (`lyap_contract`).
   - Let 𝒱(p, ŵ) = ‖p‖² − 3⟨p, ŵ⟩ + 6‖ŵ‖².
   - For every 0 < s ≤ 1/2 and all p, ŵ, G satisfying the two sector facts, the noise-free, drift-free update satisfies 𝒱⁺ ≤ (1 − s/8)𝒱.
   - The certificate is an exact identity in the six Gram scalars:

     𝒱⁺ − (1 − s/8)𝒱 = −λ₁(⟨G,p⟩ − s‖p‖²) − λ₂(⟨G,p⟩ − 2‖G‖²) − s[(1 − 2s)q₀ + 2s q_{1/2}],

     with λ₁ = 15/16 + s/4 and λ₂ = 5/16 + s/4.
   - q₀ and q_{1/2} are fixed positive semidefinite forms, written as explicit sums of squares in Lean.
   - κ enters only through s ≤ 1/2 and the co-coercivity constant. The contraction rate 1 − s/8 is therefore uniform over arbitrarily ill-conditioned, non-commuting, time-varying "Hessians".
   - This is the step not visible in scalar or fixed-quadratic analyses. The velocity integrator is undamped (momentum parameter 1). The focus paper's momentum analysis requires γ ≤ μ(1 − β)²/(4L²), which is vacuous at β = 1.
3. **Noise and drift** (`energy_step`).
   - The noise term has conditional mean zero. Its 𝒱-weight is (1 + s/4)² − 3(1 + s/4)/4 + 3/8 ≤ 1, contributing γ²σ² per step.
   - The drift enters only through d_t, with 𝒱(d, d/s) ≤ 6Γ²/s².
   - Young's inequality with parameter s/16 gives E𝒱_{t+1} ≤ (1 − s/16)E𝒱_t + 102Γ²/s³ + γ²σ².
   - Iterating gives a steady state of order Γ²/(γμ)⁴ + γσ²/μ. The first-order speed u_t never appears.
4. **Output.** x_{t+1} − θ*_t = (p_t − G_t) − n_t, and ‖p − G‖² ≤ ‖p‖² ≤ 2𝒱. Hence E‖x_{t+1} − θ*_t‖² ≤ 2E𝒱_t + γ²σ² (`exit_step`).
5. **Balancing.** Choosing γ ≍ (Γ²/(μ³σ²))^{1/5} makes the two floor terms equal and gives (σ²/μ²)^{4/5}Γ^{2/5}. The budget's γ is the largest step allowed by the noise target, γ ≍ με/σ². The validity condition is exactly the statement that this γ also controls the drift term.

## 3. Relation to prior work

| Work | Model / oracle | Guarantee | Relation |
| --- | --- | --- | --- |
| Sahu–Hogan–Wells, [arXiv:2601.12238](https://arxiv.org/abs/2601.12238) v5 (ICML 2026). Thm 3.1 (SGD), Thm 3.3 / 3.5 (SGDM), Thm 3.9 (lower bound for SGDM(β)). | Predictable random drift with E‖θ*_t − θ*_{t+1}‖² ≤ Δ²; martingale noise; one gradient per step. | SGD: (1 − γμ/2)^t‖θ₀ − θ*₀‖² + 4Δ²/(γ²μ²) + σ²γ/μ for γ ≤ min(μ/L², 1/L). Heavy ball and Nesterov carry (1 − β)^{−1}, (1 − β)^{−2} penalties. | Focus paper. Its momentum results cover gradient-averaging momentum with β < 1 and step γ ≤ μ(1 − β)²/(4L²). The present method is a β = 1 velocity estimator, outside that family. We add bounded second differences, which the focus paper does not assume. Our drift model is stronger: deterministic with a sup bound. Our variance is uniform in x rather than along iterates. |
| Cutler–Drusvyatskiy–Harchaoui, JMLR 24(147), 2023 ([arXiv:2108.07356](https://arxiv.org/abs/2108.07356)), Thm 3 and the asymptotic tracking error after it. | As in Sahu, with η ≤ 1/(2L). | Floor min_{η ≤ 1/(2L)} ησ²/μ + (Δ/(μη))²: (Δσ²/μ²)^{2/3} at low drift, σ²/(μL) + 4κ²Δ² at high drift. | Strongest SGD baseline. |
| Sarkar–Mandal–Wells, [arXiv:2610.16923](https://arxiv.org/abs/2610.16923) (preprint, Oct 2026). | Causal procedures, one stochastic gradient per step, squared path-variation budget. | Minimax average error ≍ σ^{4/3} D_T^{1/3}/(μ^{4/3} T^{1/3}), which is (Δσ²/μ²)^{2/3} for uniform drift. | Under first-order drift alone SGD is already minimax. Beating it needs extra structure, as here. |
| Kamijima–Marumo–Takeda, [arXiv:2512.15205](https://arxiv.org/abs/2512.15205) v1 (preprint), Thm 4.4 and Thm 5.5. | Every sample loss ℓ(·; y) is μ-strongly convex and L-smooth (Assm 2.1). The correction must contract to the sample minimizer with factor γ_c, γ_c‖α‖₁ < 1 (Assm 4.1a). | lim sup E‖x̂_k − x*_k‖ = O(Δ₁ + γ_c Δ₂ + (Δ₂ + 1)h^{q/(2q+1)}), first moment. | Same exponent family, so we do not claim the rate h^{2/5} as new by itself. Their bound reaches it only when the sample minimizers are unbiased (Δ₁ = 0, essentially least squares) and γ_c = O(h^{q/(2q+1)}). That requires repeated inner iterations on the same sample function. Our theorem needs neither condition: it uses a single unbiased stochastic gradient per time step for general nonlinear objectives, a setting their result does not cover. |
| Maity–Mukherjee–Banerjee–Sun, ICLR 2023 ([arXiv:2205.13575](https://arxiv.org/abs/2205.13575)), Thm 3.3. | Bound stated in terms of the error σ_ζ of an estimate of (∇²R)^{−1}∇_{θt}R. | Asymptotic tracking error with an O(h²/η)-type bias term plus ησ_ξ + hσ_ζ. | Concrete estimators are only given for specific applications, such as least squares with known design. There is no generic single-gradient estimator for general nonlinear objectives. |
| Wu–Petersen–Ugrinovskii–Shames, [arXiv:2411.01826](https://arxiv.org/abs/2411.01826) (ACC 2025), and [arXiv:2508.21335](https://arxiv.org/abs/2508.21335). | Deterministic. Exactly linear drift with time-invariant shape f(x, t) = f̃(x − x*(0) − at). Sector-bounded gradients. | Asymptotic zero-error tracking via the circle criterion. Optimal rates for quadratics with polynomial drift. | Same double-integrator structure. There is no noise, no approximate drift, no tracking floor and no finite-time stochastic bound. |
| Bastianello–Carli–Zampieri, internal-model online optimization ([arXiv:2205.13932](https://arxiv.org/abs/2205.13932), IEEE TAC 2024); Bianchin et al. ([arXiv:2407.08037](https://arxiv.org/abs/2407.08037)). | Quadratic or deterministic, with a known model of the variation. | Exact tracking and an internal-model principle. | They give the structural reason integrators are needed. They do not treat noise. |
| Benveniste, "Design of adaptive algorithms for the tracking of time-varying systems", Int. J. Adaptive Control Signal Process. 1(1):3–29, 1987 ([doi](https://doi.org/10.1002/acs.4480010103)); Benveniste–Métivier–Priouret 1990; α–β trackers (Kalata, IEEE TAES 1984). | Adaptive algorithms (stochastic approximation) in the small-gain asymptotic regime with stochastic drift models; linear-Gaussian filtering. | Multistep (velocity) algorithms improve tracking of trending parameters. Kalman and α–β filters are optimal for integrated random-walk drift. | The qualitative mechanism is classical, and the 1-D Gaussian quadratic case of our method is a steady-state α–β filter. We could not access the full texts (paywalled) to check whether a non-asymptotic, global bound for general nonlinear strongly convex objectives with changing shape appears there. To our knowledge from the accessible abstracts and later citations, it does not. This is an unresolved literature check. |

**What is new.** We claim no new algorithmic idea. The contribution is the following finite-time theorem:

- it is global and dimension-free;
- it covers general μ-strongly convex, L-smooth objectives whose shape varies arbitrarily over time;
- it uses a single unbiased stochastic gradient per time step;
- it allows a deterministic minimizer path with bounded second differences;
- it gives the minimax-order mean-square floor (σ²/μ²)^{4/5}Γ^{2/5}, κ-free in the low-drift regime;
- it needs no knowledge of Γ, R or V.

The technical ingredient is the κ-uniform common quadratic Lyapunov certificate of §2 for the undamped double integrator under sector-bounded, time-varying gradient maps.

## 4. Lower bounds and comparison regimes

These statements are proved here on paper. They are not formalized.

**(a) Minimax floor for the class.**
- *Model.* Take E = ℝ, f_t(x) = (μ/2)(x − θ_t)², and the oracle μ(x − θ_t) + σξ_t with ξ_t ~ N(0, 1) i.i.d. Every query reveals Z_t = θ_t − σξ_t/μ and nothing else. So any (randomized, adaptive) causal algorithm is an estimator built from Z₀, …, Z_{T−1} and an independent seed.
- *Two hypotheses.* Let a = T − 1 − w. Compare θ ≡ 0 with θ_t = (Γ/2)((t − a)₊)².
  - Both paths have second differences at most Γ and satisfy R = V = 0 when a ≥ 1.
  - Their values at T − 1 are 0 and H = Γw²/2.
- *Information.* The Kullback–Leibler divergence between the two observation laws is Σ_{j≤w} (Γj²/2)²·μ²/(2σ²) ≤ Γ²μ²w⁵/(8σ²).
- *Le Cam step.* Since |x|² + |x − H|² ≥ H²/2 and by Pinsker's inequality, max_i E_i|x̂ − θ^{(i)}_{T−1}|² ≥ (H²/4)(1 − √(KL/2)).
- *Choice of w.* Take w = ⌊(4σ²/(μ²Γ²))^{1/5}⌋. This needs Γ ≤ 2σ/μ (so that w ≥ 1) and T ≥ w + 2. Then KL ≤ 1/2, and every algorithm has worst-case error at least (4^{4/5}/512)(σ²/μ²)^{4/5}Γ^{2/5} ≥ (1/200)(σ²/μ²)^{4/5}Γ^{2/5}.
- *Conclusion.* The floor in the theorem is optimal up to a universal constant in that regime. The constants in the theorem (9792 and 99) are not optimized.

**(b) SGD cannot exploit smooth drift.**
- *Model.* Take the same 1-D model with θ_t = Δt, so Γ = 0 and V = Δ.
- *Recursion.* Constant-step SGD's error e_t = x_{t+1} − θ_t satisfies e_t = (1 − γμ)e_{t−1} − (1 − γμ)Δ − γσξ_t.
- *Limit.* For 0 < γμ < 2 the mean-square error converges to (1 − γμ)²Δ²/(γμ)² + γσ²/(μ(2 − γμ)), and for γμ ≥ 2 it diverges.
- *Minimizing over γ.*
  - If γμ ≤ 1/2, the limit is at least Δ²/(4γ²μ²) + γσ²/(2μ) ≥ (3/4)(Δσ²/μ²)^{2/3}.
  - If γμ > 1/2, it is at least σ²/(4μ²).
- *Conclusion.* When Δ ≤ σ/μ, every constant step has limiting error at least (1/4)(Δσ²/μ²)^{2/3}. On the same instance (Γ = 0) the velocity-tracking theorem reaches any ε > 0 in O((κ + σ²/(μ²ε)) log(1 + (V²(κ + σ²/(μ²ε))²)/ε)) calls.

**(c) Regimes.**
- *Both models apply.* Suppose the drift has both a speed bound Δ and a second-difference bound Γ. The velocity-tracking floor (σ²/μ²)^{4/5}Γ^{2/5} improves on the SGD floor (Δσ²/μ²)^{2/3} exactly when Γ ≲ Δ^{5/3}(μ/σ)^{2/3}. This covers near-constant-velocity drift, smooth trends, and slowly accelerating targets.
- *Only first-order drift.* If only first-order drift is known (Γ ≤ 2Δ is then all one can say), the velocity method is worse than SGD by a factor (σ/(μΔ))^{4/15} in the low-drift regime. This is unavoidable by (a) and the Sarkar et al. lower bound.
- *High drift.* When the cap γ ≤ 1/(2L) binds, the guarantee needs ε ≳ κ⁴Γ². This is worse in κ than SGD's high-drift floor κ²Δ² + σ²/(μL) when Γ ≈ Δ. We do not claim an improvement in that regime.

## 5. Limitations

- **Deterministic path.** The drift is a deterministic, oblivious path with a sup bound on second differences. This is stronger than the predictable random drift with an expectation bound used by Sahu et al. and Cutler et al.
- **Variance and criterion.**
  - The variance bound is uniform in x, which is stronger than the along-iterate bounds of the focus paper.
  - The criterion is in expectation (mean square). We give no high-probability result.
- **Time indexing.**
  - Time advances by one per oracle call.
  - The theorem certifies accuracy at the stopping time, for every horizon after the burn-in (through the free slack H). It does not give a pathwise uniform-in-time statement.
- **Constants and scope.**
  - The constants are large and unoptimized.
  - Higher-order smoothness (bounded q-th differences with a q-fold integrator, expected floor (σ²/μ²)^{2q/(2q+1)}Γ_q^{2/(2q+1)}) is not covered. Whether a common quadratic Lyapunov function exists for q ≥ 3 under sector-bounded maps was not settled.
- **Literature check.** The classical literature check is incomplete (§3).

## 6. Lean layout

- [SmoothDriftStronglyConvex](../Setups/SmoothDriftStronglyConvex.lean): setup.
- [VelocityTrackingSgd](../Algorithms/VelocityTrackingSgd.lean): algorithm.
- [VelocityTrackingStep](../Proofs/VelocityTrackingStep.lean): the Lyapunov certificate `lyap_contract`, the quadratic-form algebra, and the sector facts.
- [VelocityTrackingRun](../Proofs/VelocityTrackingRun.lean): one-step energy and exit bounds in expectation, measurability, the induction over i.i.d. seeds, the execution identity `execute_vt`, and `expected_error`.
- [VelocityTrackingConvergence](../Proofs/VelocityTrackingConvergence.lean): tuning algebra and the setup-level success statement.
- [VelocityTrackingSmoothDrift](VelocityTrackingSmoothDrift.lean): budget and `result : Convergence spec budget`.
