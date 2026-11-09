# Accelerated diagonal-scale adaptivity from a black-box first-order oracle

Lean: theorem [`result`](BlackBoxDiagonalAcceleration.lean), setup
[`DiagonalSmoothStronglyConvexBlackBox`](../Setups/DiagonalSmoothStronglyConvexBlackBox.lean), algorithm
[`BlackBoxDiagonalAccelerated`](../Algorithms/BlackBoxDiagonalAccelerated.lean). Supporting proofs are in
`LongTails/Proofs/`: `PhaseCertificate`, `LogScaleCut`, `BlackBoxValidity`, `BlackBoxRun`, `BlackBoxPhase`,
`BlackBoxProbe`, `BlackBoxMacro`, `BlackBoxLevels`, `BlackBoxInvariant` and `BlackBoxFinal`.

## Problem class, information and oracle

Let `f : ℝ^d → ℝ` be differentiable. Suppose there are **unknown** weights `w ∈ ℝ^d_{>0}` and an
**unknown** `μ ∈ (0, 1]` such that, writing `‖v‖²_w = Σ_i w_i v_i²`, for all `x, y`

    (μ/2)‖y − x‖²_w  ≤  f(y) − f(x) − ⟨∇f(x), y − x⟩  ≤  ½‖y − x‖²_w .

Equivalently, `f` is 1-smooth and `μ`-strongly convex in the norm of the diagonal preconditioner
`P⋆ = Diag(1/w)`, i.e. `(1/κ⋆)P⋆⁻¹ ⪯ ∇²f ⪯ P⋆⁻¹` with `κ⋆ := 1/μ`. Minimising `κ⋆` over `w` gives the
optimal-diagonal condition number of
Kunstner, Portella, Schmidt and Harvey ([NeurIPS 2023, arXiv:2306.02527](https://arxiv.org/abs/2306.02527), §2).
The Euclidean condition number can be arbitrarily larger than `κ⋆`, for example after a bad coordinate
scaling `f(x) = g(Sx)` of a well-conditioned `g` (`S` an unknown positive diagonal). A concrete nonlinear
family with interacting coordinates is

    f(x) = Σ_{i ≤ n} log(1 + exp(a_iᵀ S x − b_i)) + (λ/2)‖S x‖²,

with dense `a_i`. It satisfies the class with `w = (λ + ‖A‖²/4)·S²` and `μ = λ/(λ + ‖A‖²/4)`. This is
logistic-type regression on badly scaled features.

**Information.** The algorithm receives only `d` and `x0`, and each call returns the exact pair `(f(x), ∇f(x))`.
It does **not** receive `w`, `μ`, `κ⋆`, any smoothness constant, `f⋆ = min f`, a minimiser,
`Δ ≥ f(x0) − f⋆` or `ε`. These parameters enter only the validity conditions, the admissibility conditions
and the budget. The setup states exactly these hypotheses; it is the existing
[`DiagonalSmoothStronglyConvex`](../Setups/DiagonalSmoothStronglyConvex.lean) setup with `f⋆` removed from
the public information. It imposes no `allowedAlgorithm` restriction. The accuracy criterion is the
deterministic objective gap `f(x̂) − f(x⋆) ≤ ε` of the returned point. In the framework this is stated
almost surely over a trivial seed.

## Main theorem

For every admissible instance, after

    d + 1 + ⌈21 √(2/μ) · ( log(1 + Δ/(μ²ε)) + (d + 1)(3 + log₂(1/μ))⁴ )⌉

oracle calls (the public `budget`), the output satisfies `f(x̂) − f⋆ ≤ ε`. With `κ⋆ = 1/μ` this is

    O( √κ⋆ · log(1 + κ⋆²Δ/ε)  +  d √κ⋆ log⁴ κ⋆  +  d ).

The budget counts every call:
- the `d + 1` coordinate probes;
- two calls per accelerated step (the extrapolated point and the new iterate);
- the test point of each phase;
- every failed phase, at every guessed condition number;
- calls inside an incomplete final phase, since the run is anytime.

The leading `ε`-dependent term `√κ⋆ log(1/ε)` has no dimension factor. In high dimension
(`d ≳ √κ⋆ log(1/ε)`) it matches the order of the Nesterov lower bound `Ω(√κ⋆ log(1/ε))`, which holds even
when `P⋆` is known. In low dimension that lower bound does not apply: cutting-plane methods reach
`O(d log(·))` without knowing the preconditioner (see the comparison below). The main logarithm is
`log(1 + κ⋆²Δ/ε)` rather than the `log(Δ/ε)` of the repository result below. The extra `log κ⋆²` comes from
converting between the probed metric `J` and the true weights.

## Algorithm

1. **Probes** (`d + 1` calls). The secants `J_k = ∂_k f(x0 + e_k) − ∂_k f(x0)` lie in `[μ w_k, w_k]`.
   The proof reuses the repository lemma `secant_bounds`.
2. **Phases.** A phase at level `j` uses the guess `κ̂ = 2^j`, `μ̂ = 1/(4·2^j)`, `α = √μ̂`,
   `N = ⌈2√(2^j) ln(512·8^j)⌉` and a diagonal metric `m = e^θ`. It runs `N` steps of Nesterov's
   constant-momentum method in the metric `m`:
   `y_k = (αv_k + x_k)/(1+α)`, `x_{k+1} = y_k − m⁻¹∇f(y_k)`, `v_{k+1} = (1−α)v_k + αy_k − (α/μ̂)m⁻¹∇f(y_k)`.
   It then queries the test point `z = x_N − m⁻¹∇f(x_N)`.
3. **Certificate check.** The algorithm checks `2N + 4` inequalities among the queried points only:
   - cocoercive descent for every pair `(y_k, x_{k+1})` and for `(x_N, z)`;
   - the strong-convexity lower model of `z` from every `y_k`;
   - strong convexity for the pair `(x0, x_N)`;
   - strong monotonicity for `(x0, z)`;
   - cocoercivity for `(x_N, z)`.

   Each check has the form `Σ_k a_k e^{−θ_k} + Σ_k b_k e^{θ_k} ≤ c` with `a, b ≥ 0`.
4. **Success.** If every check holds, the new base point is `x_N`.
5. **Failure.** Otherwise the first violated inequality is a convex function `h(θ)`. The algorithm
   takes `θ ← clamp(θ − ln 2 · ∇h/‖∇h‖)` into the box `[ln J, ln J + ln 4 + j ln 2]`. After
   `⌊d j²/4⌋ + 1` failures at level `j` it moves to level `j + 1` and resets `θ` to the box centre
   `ln J + ln 2 + (j/2) ln 2`.
6. **Output.** The output is the current base point, i.e. the last certified one.

## Proof structure and new mechanisms

* **An accelerated phase certificate with no x⋆ and no f⋆** (`phase_certificate`). Nesterov's estimate
  sequence `φ_k(u) = φ_k* + (μ̂/2)‖u − v_k‖²_m` gives `φ_k* ≥ f(x_k)`. This uses only the descent checks and
  the convexity inequality `f(x_k) ≥ f(y_k) + ⟨∇f(y_k), x_k − y_k⟩`. Evaluating the estimate sequence at the
  test point `z` and using the lower-model checks gives

      ‖∇f(x_N)‖²_{m⁻¹} ≤ 8(1−α)^N/μ̂ · ‖∇f(x0)‖²_{m⁻¹} ≤ ‖∇f(x0)‖²_{m⁻¹}/(16·4^j).

  The remaining checks control `f(x0) − f(x_N)` and `‖z − x0‖_m`. Every inequality used is between queried
  points. This removes the obstacle named in OSGM Part II §5.3, that AGD potentials require `x⋆`.
* **Two-sided learning in log-scale coordinates** (`LogScaleCut`, `BlackBoxValidity`).
  - In the metric `e^θ`, cocoercivity-type checks involve `Σ a_k e^{−θ_k}` and strong-convexity-type checks
    involve `Σ b_k e^{θ_k}`. Both are convex in `θ`.
  - Every check holds for all metrics in `[w, 4w]` once `2^j ≥ κ⋆`. That region contains the ball of radius
    `ln 2` around `ln w + ln 2`.
  - A violated check therefore gives a perceptron-type step that reduces `‖θ − (ln w + ln 2)‖²` by at least
    `ln²2` (`cut_progress`). The initial distance is at most `d (j ln 2)²/4`, so a level with `2^j ≥ κ⋆`
    fails fewer than `d j²/4` times and is never left.
  - The cuts of Kunstner et al. are half-spaces in the preconditioner, and they certify only the smoothness
    side. That suffices for gradient descent but not for momentum, which needs both sides.
* **Removing κ⋆ by doubling** (`BlackBoxInvariant`).
  - A certified success is valid algebraically at any level; this is where the measure `‖∇f‖²_{J⁻¹}` comes in.
    Because `J ≤ m ≤ 4·2^j J`, each success shrinks `‖∇f‖²_{J⁻¹}` by `4·2^j`.
  - Levels stop below `j⋆ = ⌈log₂ κ⋆⌉`.
  - An exponential potential charges each success's cost against its log-reduction. Each failure is charged
    to a per-level failure budget.
* **Accuracy.** `f(x) − f⋆ ≤ ‖∇f(x)‖²_{J⁻¹}/(2μ)` because `J ≤ w`, and initially `‖∇f(x0)‖²_{J⁻¹} ≤ 2Δ/μ`.

## Comparison (same class; deterministic accuracy `f(x̂) − f⋆ ≤ ε`)

| method | needs | oracle calls |
|---|---|---|
| AGD in the Euclidean metric | `L, μ_E` or backtracking | `O(√κ_E log(1/ε))`, where `κ_E` can be ≫ `κ⋆` |
| Multidimensional backtracking (Kunstner et al., NeurIPS 2023, Thm 5.3; ellipsoid version) | f, ∇f | `O(√(2d) κ⋆ log(1/ε) + d log(L/α₀))` |
| OSGM-R (Gao, Chu, Ye, Udell, COLT 2025, [arXiv:2411.01803](https://arxiv.org/abs/2411.01803); Part I [arXiv:2505.23081](https://arxiv.org/abs/2505.23081), eq. (5)) | f, ∇f, **f⋆** | `O(κ⋆ log(1/ε))` plus a regret overhead; `κ⋆` is trajectory-dependent |
| Secant-Jacobi metric + AGD (standard reduction; the metric `κ⋆J` is `κ⋆²`-conditioned) | f, ∇f, κ⋆ | `O(d + κ⋆ log(1/ε))` |
| Repository result [`OnlineMetricAccelerated`](OnlineMetricAccelerated.md) | f, ∇f, **f⋆** | `O(√κ⋆ log(Δ/ε) + log d · log(Δ/ε) + d³ log²d · log κ⋆ · √κ⋆)` |
| Cutting planes (centre of gravity / Vaidya) in the secant ellipsoid | f, ∇f, κ⋆ (for the initial radius; a radius-doubling variant costs an extra log factor) | `O(d log(κ⋆Δ/ε))`, with poly(d) arithmetic per step |
| **This theorem** | f, ∇f only | `O(√κ⋆ log(1 + κ⋆²Δ/ε) + d √κ⋆ log⁴ κ⋆ + d)` |

**What is new.**
- To our knowledge, for this global diagonal class, this is the first black-box first-order method whose
  leading term is accelerated and dimension-free, `√κ⋆ log(1/ε)`, for the optimal *unknown* diagonal
  preconditioner. It uses only
  `(f, ∇f)` and needs no `f⋆` and no condition number.
- This answers, for global diagonal candidate sets, the black-box version of the question in OSGM Part II
  ([arXiv:2509.11007v2](https://arxiv.org/abs/2509.11007), §5.3). There the authors ask for
  `O(√κ⋆ log(1/ε))` with knowledge of `f⋆`, and state that with only black-box access the question
  "remains unclear".
- Relative to the repository's own `OnlineMetricAccelerated`, which already answers the version with
  `f⋆`:
  - the requirement `f⋆` is removed;
  - the dimension dependence of the warm-up improves from `d³ log²d · log κ⋆ · √κ⋆` to `d log⁴κ⋆ · √κ⋆`,
    at the cost of three extra `log κ⋆` factors. This is an improvement only when `d² log²d ≳ log³κ⋆`;
    it is not uniform;
  - the `log d · log(1/ε)` term disappears.

  The mechanisms differ. The present one uses x⋆-free gradient-norm certificates and log-scale cuts. The
  repository result uses hindsight comparators with `f⋆`-halving.
- We checked one composition: the reduction "guess `f⋆` and restart" (Hazan–Kakade style) applied to
  `OnlineMetricAccelerated`. A wrong guess either stalls the `f⋆`-halving epochs or invalidates their
  hindsight comparator. Running `O(log(1/ε))` guesses, each with its own warm-up, gives the upper estimate
  `√κ⋆ log²(1/ε)` plus a warm-up per guess. This is only an estimate for this one composition, not a proved
  impossibility for reductions in general.

## Regimes and limitations

* **The improvement is asymptotic in ε.**
  - Against secant-Jacobi + AGD and OSGM-R (`κ⋆ log(1/ε)`), the leading term improves by `√κ⋆`. The warm-up
    `d √κ⋆ log⁴κ⋆` is repaid once `log(1/ε) ≳ d log⁴κ⋆ / √κ⋆`.
  - Against Kunstner et al., it is repaid once `log(1/ε) ≳ √(d/κ⋆) log⁴κ⋆`.
* **Cutting planes dominate in many regimes.**
  - In pure oracle complexity, centre-of-gravity or Vaidya methods need only `O(d log(κ⋆Δ/ε))` calls. They
    are better whenever `d ≤ √κ⋆`.
  - For `d > √κ⋆`, this theorem is better only once `log(1/ε) ≳ √κ⋆ log⁴κ⋆`, which is very high accuracy.
  - The warm-up `d√κ⋆` arises because a failure may be certified only at the end of a phase. We did not
    find a way to remove the `√κ⋆` factor from it.
  - The contribution is therefore the first dimension-free accelerated leading term with black-box access.
    It has the same profile as non-asymptotic superlinear quasi-Newton results: an `ε`-independent warm-up
    followed by a better asymptotic rate.
* **Diagonal candidate sets only.** The class assumes a global sandwich `μw ⪯ ∇²f ⪯ w`, as in Kunstner
  et al. OSGM's `κ⋆` is trajectory-dependent and may use full matrices; full-matrix candidate sets remain open.
* **Constants.** The constants (21, the fourth power of the logarithm) are conservative. A geometric sum
  over levels would give `log³κ⋆`. Optimality of the warm-up and lower bounds for learning diagonal
  preconditioners are open.
* **Phases are restarts.** They are intrinsic to the certificate and to the metric updates.
* **Literature search.** No 2024–2026 paper with accelerated adaptivity to an unknown diagonal preconditioner
  was found. The search covered OSGM follow-ups, quasi-Newton/A-HPE papers including
  [arXiv:2306.02212](https://arxiv.org/abs/2306.02212) and [arXiv:2610.40608](https://arxiv.org/abs/2610.40608),
  and accelerated AdaGrad variants such as Ene–Nguyen–Vladu,
  [arXiv:2007.08840](https://arxiv.org/abs/2007.08840). The citation graph of Kunstner et al. could not be
  accessed, so novelty relative to unindexed work is not certain.
