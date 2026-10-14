# Stochastic nonconvex–strongly-concave minimax with Lipschitz Hessians: an ε^{-3.5} gradient-only guarantee

Lean files:
- main theorem: [`HessianNcscImplicitTransport.lean`](HessianNcscImplicitTransport.lean) (`OracleTemplate.HessianNcsc.result`, budget `OracleTemplate.HessianNcsc.budget`);
- setup: [`../Setups/StochasticHessianNcsc.lean`](../Setups/StochasticHessianNcsc.lean);
- algorithm: [`../Algorithms/HessianNcscIgt.lean`](../Algorithms/HessianNcscIgt.lean) (`igtSgda`);
- parameter formulas: [`../Proofs/HessianNcscTuning.lean`](../Proofs/HessianNcscTuning.lean) (`tCfg`, `tEs`, `tγ`, `tα`, `tη`).

## Problem and assumptions

We consider min_x max_y f(x, y). Here x ∈ E and y ∈ F, where E and F are arbitrary finite-dimensional real inner-product spaces. Norms on E × F are Euclidean: ‖(u, v)‖² = ‖u‖² + ‖v‖².

The setup's `admissible` predicate requires:

- **(A1) Joint smoothness.** f has partial gradients g_x and g_y, and ∇f = (g_x, g_y) is L-Lipschitz on E × F.
- **(A2) Strong concavity.** f(x, ·) is μ-strongly concave for every x, with 0 < μ ≤ L. We write κ = L/μ.
- **(A3) Lipschitz Hessian.** g_x and g_y are Fréchet differentiable. Their derivative (the joint Hessian) is ρ-Lipschitz in the Euclidean operator norm.
- **(A4) Initial gap and dual residual.**
  - Φ(x0) − Φ(x) ≤ Δ for all x, where Φ(x) = max_y f(x, y). In the setup this is written without iSup as ∀ x y, ∃ y′, f(x0, y) − f(x, y′) ≤ Δ.
  - ‖∇_y f(x0, y0)‖ ≤ G.
- **(A5) Stochastic oracle.**
  - Each call at a point z = (x, y) returns (o_x(z, ω), o_y(z, ω)), where ω is a fresh IID sample.
  - The oracle is jointly measurable and unbiased.
  - The variance is jointly bounded: E‖o_x − g_x‖² + E‖o_y − g_y‖² ≤ σ².
  - The samples ξ_k are an `IID` stream under an abstract probability measure P.

(A1), (A2), (A4) and (A5) are the setting of Wu et al. (arXiv [2610.00229](https://arxiv.org/abs/2610.00229)) and SAPD+ (Zhang–Aybat–Gürbüzbalaban, NeurIPS 2022, [arXiv 2205.15084](https://arxiv.org/abs/2205.15084)).

(A3) is the only addition, and it is the standard second-order smoothness assumption:
- Cutkosky–Mehta, *Momentum improves normalized SGD*, ICML 2020, [arXiv 2002.03305](https://arxiv.org/abs/2002.03305), for single-level problems;
- Luo–Li–Chen, NeurIPS 2022, [arXiv 2110.04814](https://arxiv.org/abs/2110.04814), and Chen–Ma–Zhang, [arXiv 2405.00914](https://arxiv.org/abs/2405.00914), for minimax and bilevel problems.

Positivity of ρ and σ is required in `valid`. This is harmless, because both are upper bounds: any instance with ρ = 0 or σ = 0 also satisfies the hypotheses with any positive value. No separate deterministic or quadratic theorem is claimed.

**Example.** A concrete nonlinear instance in arbitrary dimension with interacting coordinates:

f(x, y) = ℓ(x) + Σ_{j=1}^m s(⟨b_j, x⟩ + ⟨c_j, y⟩) − (μ₀/2)‖y‖².

The ingredients are:
- ℓ is a nonconvex loss with Lipschitz gradient and Hessian;
- s is softplus, s(t) = log(1 + e^t), whose second and third derivatives are bounded by 1/4 and 1/(6√3);
- μ₀ > (1/4)Σ_j‖c_j‖².

This f satisfies the following:
- (A1) and (A3) hold globally with explicit L and ρ.
- (A2) holds with μ = μ₀ − (1/4)Σ‖c_j‖².
- The coupling blocks ∇²_xy f and ∇²_yy f vary with x and y, so the varying-matrix part of the analysis is used.
- Any additive gradient noise with variance at most σ² gives (A5).

Distributionally robust or adversarially regularized losses of this form (a nonconvex primal loss with a smooth strongly concave dual) are the standard motivation for the class.

**Accuracy criterion.** The criterion is the expected norm of the true gradient of the primal function:

E‖∇Φ(x̂)‖ ≤ ε, where Φ(x) = f(x, y*(x)).

In Lean, `successful` states the following. The output is measurable, and a maximizer map exists. For every maximizer map ys, the function ω ↦ ‖gradient (fun x => f x (ys x)) (x̂(ω))‖ is integrable and its integral is at most ε.

The maximizer y* is not assumed. Its existence (via a Banach fixed point), uniqueness and Lipschitz continuity are proved. Danskin's identity ∇Φ = ∇_x f(·, y*(·)) is also proved (`Hyp.Phi_hasGradient`).

## Algorithm (`igtSgda`)

The algorithm is a single-loop stochastic gradient descent–ascent. It uses implicit gradient transport (IGT) momentum on x and a smooth normalized step:

φ(m) = −η m / √(‖m‖² + λ²).

Every oracle call uses one fresh joint stochastic gradient. The algorithm runs in four phases; all calls are counted in the budget.

- **Phase A** (N_A calls): stochastic gradient ascent on y at x0, with step γ.
- **Phase B** (N_B calls): the momentum is initialized as the average of N_B stochastic x-gradients at (x0, y_A).
  - Set w_1 = x0 + φ(m_0).
- **Phase C** (N_C calls): stochastic gradient ascent on y at the transported point x̃_1 = w_1 + ((1−α)/α)φ(m_0).
- **Main loop** (T calls): one query at (x̃_t, y_t), giving (g_t, h_t). Then:
  - m_t = (1−α)m_{t−1} + α g_t;
  - w_{t+1} = w_t + φ(m_t);
  - x̃_{t+1} = w_{t+1} + ((1−α)/α)φ(m_t);
  - y_{t+1} = y_t + γ h_t.
- **Output:** w_τ, with τ uniform on {0, …, T}. τ is drawn from the algorithm's own seed and costs no oracle call.

**Parameters.** All parameters are explicit functions of L, μ, ρ, σ, ε and G. Write K = 1 + κ, and set:

| Quantity | Formula |
|---|---|
| Q | 40ρK/ε + L²/(ε² + 20σ²) |
| E* | 1/Q |
| γ | 1/(L²/μ + 20σ²Q/μ) |
| α | 1/(4000 K²(1 + σ²/ε²)(1 + ρεK/L²)) |
| η | α√E*/(20K) |
| λ | ε/4 |
| N_A | ⌈log(1 + G²Q/μ²)/(γμ)⌉ |
| N_B | ⌈1/α⌉ |
| N_C | ⌈4/(γμ)⌉ |
| T | budget − N_A − N_B − N_C |

## Theorem

`result : Convergence spec budget`. For every valid parameter set and every admissible instance and oracle, the following hold:

- `igtSgda` makes exactly `budget` oracle calls;
- its output satisfies the accuracy criterion above;
- with K = 1 + L/μ and Q as above, the budget is

budget = ⌈10⁶ K²(1 + σ²/ε²)(1 + ρεK/L²) · ( KΔ√Q/ε + 1 + σ/ε + log(1 + G²Q/μ²) )⌉.

**Leading term.** As ε → 0 with the other parameters fixed, √Q ≈ √(40ρK/ε), so

budget = O( Δ K^{3.5} √ρ σ² / ε^{3.5} ) + O( K³ L Δ σ / ε³ + K³ L Δ / ε² + K² σ³/ε³ + K² (σ²/ε²) log(1 + G²ρK/(μ²ε)) ) + lower-order terms.

The ε⁻³-type terms are lower order than the ε^{-3.5} term. The dual residual G enters only logarithmically. Constants are explicit but not optimized.

## Closest prior results and the contribution

- **First-order smoothness: Wu et al.** arXiv [2610.00229v1](https://arxiv.org/abs/2610.00229) (Sep 2026, preprint, not yet peer reviewed). Their main theorem (Thm 3.4) proves the sharp bound

  Θ̃(√κLΔ/ε² + κLΔσ²/ε⁴ + κ²σ²/ε² + √κ log₊(G/(ε√κ)))

  for fresh-gradient algorithms under (A1), (A2), (A4) and (A5). The lower bound uses instances whose Hessian-Lipschitz constant scales like L²/ε. It therefore does not apply when ρ is fixed.
- **SAPD+** (NeurIPS 2022) gives O(κLG₀σ²ε⁻⁴).
- **SGDA** (Lin–Jin–Jordan, ICML 2020, [arXiv 1906.00331](https://arxiv.org/abs/1906.00331)) gives O(κ³ε⁻⁴).
- **Lower bounds for stochastic NC–SC** under bounded variance are Ω(κσ²ε⁻⁴): Wu et al. above, and Zhang–Wu–Yang, arXiv 2609.35206 (preprint). Both use hard instances that are only first-order smooth. The deterministic lower bounds of Zhang et al. (UAI 2021) and Li et al. (NeurIPS 2021) concern a different oracle.
- **Other oracles.** Cai–Alghunaim–Sayed ([arXiv 2406.13041](https://arxiv.org/abs/2406.13041)) and Ma–Xiao–Zhang ([arXiv 2606.07003](https://arxiv.org/abs/2606.07003), single-loop regularized Newton) reach ε⁻³-type rates. Both use stochastic Hessian–vector products, which our oracle does not provide.
- **Mean-squared smoothness.** Variance-reduced methods under mean-squared smoothness (same-sample gradient pairs) reach O(ε⁻³). Our oracle (A5) does not provide such pairs.
- **Single-level analogue.** For min_x F(x) with Lipschitz Hessian and bounded-variance stochastic gradients:
  - Cutkosky–Mehta (ICML 2020, Thm 3, NIGT) give O(ε^{-3.5}).
  - Arjevani et al. ([arXiv 2006.13476](https://arxiv.org/abs/2006.13476), COLT 2020) give the Ω(ε⁻³) lower bound.
  - Even single-level, the gap between ε^{-3.5} and ε⁻³ is open.

**Contribution.** To our knowledge, this is the first guarantee for stochastic NC–SC minimax with an ε-exponent below 4 that uses only stochastic gradients: one fresh joint sample per call, bounded variance, and no Hessian–vector products or mean-squared smoothness. It requires the single standard addition (A3) and gives ε^{-3.5}. Under (A3) alone, Wu et al.'s ε⁻⁴ is therefore not the right complexity for this oracle.

The ε^{-3.5} term equals Cutkosky–Mehta's single-level rate Δ σ_Φ² √ρ_Φ/ε^{3.5} for Φ, with σ_Φ = Kσ (the noise of the implicit gradient) and ρ_Φ = ρK³ (the Hessian-Lipschitz constant of Φ). That single-level rate would require an exact implicit-gradient oracle, which is not available here.

**Improvement regime.** Our leading term is smaller than Wu et al.'s κLΔσ²/ε⁴ (and SAPD+'s ε⁻⁴ term) only when ε ≤ c·L²/(ρκ⁵) for an absolute constant c. The constant c is small because our constants are not optimized. The comparison is asymptotic in ε. For moderate accuracy, or for large κ, the ε⁻⁴ methods are better.

**κ dependence.** The κ-dependence (κ^{3.5} versus Wu et al.'s linear κ) is worse. It comes from σ_Φ² = K²σ² and √ρ_Φ = K^{1.5}√ρ. We do not know whether this loss is necessary.

**Not claimed.** We make no optimality claim in ε or κ.

## Technical mechanism (why this is not a black-box composition)

The natural reductions fail:

1. **NIGT on Φ with an inner y-solver.** Running NIGT on Φ while solving y*(x̃_t) to accuracy ε at each step costs ε^{-5.5}. With warm starts it still costs ε⁻⁴.
2. **Treating y-tracking error as gradient bias.** The tracking error y_t − y*(x̃_t) has size √(γσ²/μ) ≍ √ε, which is far larger than ε. A biased-gradient analysis of NIGT therefore gives nothing.
3. **Extrapolating y as well.** This amplifies the y-noise by a factor 1/α.
4. **STORM/SPIDER-type variance reduction.** These methods need same-sample gradient pairs, which (A5) does not provide.

The proof instead analyzes the corrected momentum error

χ_t = (m_t − ∇Φ(w_t)) − (α/γ) M(w_t)(y_{t+1} − Z_t), with M(w) = ∇²_xy f · (∇²_yy f)⁻¹ evaluated at (w, y*(w)).

Here Z_t is an exponential average of y*(x̃_s). The slowly varying matrix M converts the √ε-sized y-error into the martingale term α(ξ − Mζ), which is the implicit-gradient noise, plus remainders of order ε.

The proof steps are:

- **IGT cancellation without ∇²Φ.** The IGT cancellation is proved as a convexity-defect bound for the map x ↦ ∇_x f(x, y*(x)) (`Hyp.Gs_defect`). This uses only (A3); it requires neither the Hessian of Φ nor the implicit-function theorem.
- **Tracking error.** The tracking error is controlled in L² through a one-step recursion (`track_moment`). The recursion uses the smooth normalization's second-order expansion (`nphi_taylor`) for the conditional mean of the y*-drift.
- **Momentum error.** A crude L² bound on the momentum error (`eh_moment`) closes a two-sequence invariant (`moments_all`).
- **Sharp L¹ bound.** The sharp L¹ bound on χ (`Rq_bound`, `rbar_l1`, `ehM_l1`) feeds the normalized-descent inequality (`descent_step`, `grad_sum`).
- **Noise moments.** Only second moments of the noise are used.

## Formalization notes and limitations

- **Supporting proofs.** The supporting proofs are in `LongTails/Proofs/HessianNcsc*.lean`: Local, Normalization, Phi, Path, Trajectory, Process, Track, Moments, Noise, R, Phases, Main, Assembly, Output and Tuning.
  - The probability layer uses `Measure.infinitePi`. This is derived from the IID assumption (`IID.stream_law`); the theorem does not prescribe a product measure.
  - It also uses a fresh-sample Tonelli identity (`fresh_lintegral`).
- **Oracle-call accounting.** The theorem counts exactly N_A + N_B + N_C + T = budget oracle calls (`igt_execute`). The budget's domination of the required N_A + N_B + N_C + T is proved in `budget_ok`.
- **Scope.**
  - The guarantee is in expectation for the uniformly random iterate w_τ. No high-probability version is given.
  - The parameters require knowledge of L, μ, ρ, σ, ε and G, as in the baselines.
