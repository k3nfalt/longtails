# Accelerated online scaling: O(√κ⋆ log(1/ε)) with the optimal diagonal preconditioner

Lean: theorem [`result`](OnlineMetricAccelerated.lean), setup
[`DiagonalSmoothStronglyConvex`](../Setups/DiagonalSmoothStronglyConvex.lean), algorithm
[`OnlineMetricAccelerated`](../Algorithms/OnlineMetricAccelerated.lean); supporting proofs in
`LongTails/Proofs/` (`DiagonalCut`, `MetricAcceleratedStep`, `LogBandLearner`, `EpochLoss`,
`OnlineMetric*`).

## Problem class and oracle

Let `f : ℝ^d → ℝ` be differentiable and suppose there are unknown weights `w ∈ ℝ^d_{>0}` and
`μ ∈ (0,1]` such that for all `x, y`, writing `‖v‖²_w = Σ_i w_i v_i²`,

    (μ/2)‖y − x‖²_w ≤ f(y) − f(x) − ⟨∇f(x), y − x⟩ ≤ ½‖y − x‖²_w .

Equivalently, `f` is 1-smooth and `μ`-strongly convex in the norm induced by the diagonal
preconditioner `P⋆ = Diag(1/w)`. The quantity `κ⋆ := 1/μ` is the condition number after
diagonal preconditioning. Minimising it over `w` gives the optimal diagonal condition number used by
Kunstner et al. (eq. (1)–(2)) and by Gao et al.'s OSGM (Part I, Def. 3.1, diagonal candidate set).
The theorem holds for every admissible pair `(w, μ)`, in particular for the optimal one. The
Euclidean condition number `κ = L/μ_E` can be arbitrarily larger than `κ⋆`, for example after a bad
coordinate scaling of a well-conditioned function.

The algorithm knows `d`, `x0`, and the optimal value `f⋆ = min f` (the information model of
OSGM-R and of the question below). It does **not** know `w`, `μ`, `κ⋆`, `L`, `Δ` or `ε`. Each oracle
call returns `(f(x), ∇f(x))` and is counted. The Lean setup states exactly these hypotheses: both
inequalities in the `w`-norm, `f⋆` attained, `f(x0) − f⋆ ≤ Δ`. Accuracy is the deterministic
objective gap `f(x̂) − f⋆ ≤ ε` of the returned point `x̂`, which is the start of the current epoch.

## Algorithm (OnlineMetricAccelerated)

1. **Secant box** (2d calls). The exact coordinate secants
   `s_i = ∂_i f(x0 + e_i) − ∂_i f(x0) ∈ [μ w_i, w_i]` give a box `b = 1/s` with `P⋆ ≤ b ≤ κ⋆ P⋆`.
2. **Epochs with f⋆-halving.** Epoch `s` runs an accelerated method from `x_s` and stops as soon as
   `f − f⋆ ≤ (f(x_s) − f⋆)/2`. Within an epoch, AGD keeps a fixed *distance metric*
   `P_s = b ⊙ e^{φ_s}`, with the shape `φ_s` restricted to the log-band `[−ln 4d, −ln 2]^d`, so that
   `b/(4d) ≤ P_s ≤ b/2`. The gradient steps use `θ P_s` with scalar backtracking on `θ ∈ {1, ½, …}`
   (Armijo test), using FISTA-type weights `a = θ(k+1)/2`.
3. **Certified cuts.** A failed Armijo test at `q = θP_s` produces the hypergradient half-space
   `⟨a⁺, p⟩ ≤ c` of Kunstner et al. (Props 4.2–4.3, re-derived from first-order inequalities). It
   contains `P⋆`, and `⟨a⁺, q⟩ > c`. If the cut is deep with respect to the box
   (`⟨a⁺, b⟩ > 2dc`), one coordinate of `b` is halved, both learners reset, and the attempt
   restarts. Otherwise the cut is recorded and `θ` is halved.
4. **Online learning of the distance metric across epochs (new).** When epoch `s+1` ends, the point
   `x_{s+2}` is known and has gap `≤ Δ_s/4`. The algorithm forms the hindsight surrogate
   `L_s(φ) = √(8 ℓ_s(φ) V_s(φ))`, where
   `ℓ_s(φ) = Σ_i (x_s − x_{s+2})_i² /(Δ_s b_i e^{φ_i})` and
   `V_s(φ) = max{1, max over recorded cuts of 2⟨a⁺, b ⊙ e^φ⟩/c}`.
   This loss is convex in `φ`, since both factors are log-sum-exp/max-type. The algorithm takes one
   projected AdaGrad-norm step on it. Two interleaved learners, one per epoch parity, avoid delayed
   feedback.

## Main theorem

For every admissible instance, after at most

    2 · ( d + 1 + ⌈log₂(Δ/ε)⌉·⌈24√κ⋆ + log₂ d + 2⌉ + (d⌈log₂ κ⋆⌉ + 1)·⌈110 d² (1 + ln 2d)² √κ⋆⌉ )

oracle calls, the output satisfies `f(x̂) − f⋆ ≤ ε` (theorem `result`; the public `budget`).
Thus the complexity is

    O( √κ⋆ · log(Δ/ε)  +  log d · log(Δ/ε)  +  d³ log² d · log κ⋆ · √κ⋆ ).

The leading `ε`-dependent term `√κ⋆ log(1/ε)` has **no dimension factor**. All dependence on `d`
appears in an `ε`-independent warm-up term, apart from the additive `log d` per epoch caused by
backtracking.

## Mechanism and proof structure

* *Hindsight comparator, avoiding x⋆-dependent potentials.* The AGD potential with a fixed distance
  metric holds for **every** comparator `u`. Taking `u = x_{s+2}` (gap `≤ Δ_s/4`) bounds the epoch
  length by `1 + L_s(φ_s)` (`Inv.record_bound`). The bound is computable after the fact, which
  addresses the obstacle named in OSGM Part II §5.3: AGD potentials require `x⋆`.
* *Certified validity.* `1/θ_min ≤ V_s(P_s)`, because every halving of `θ` comes from a cut with
  `⟨a⁺, θP_s⟩ > c`. So `V_s` measures, convexly in `log P`, how far the learned metric overshoots
  the valid region, using only trajectory data.
* *d-free comparator.* For `P' = max(P⋆/2, b/(4d))`, which lies in the band:
  `ℓ_s(P') ≤ 2‖x_s − x_{s+2}‖²_w/Δ_s ≤ 9κ⋆` by strong convexity, and `V_s(P') ≤ 2`, because cuts
  satisfy `⟨a⁺, P⋆⟩ ≤ c` and recorded cuts satisfy `⟨a⁺, b⟩ ≤ 2dc`. Hence `L_s(P') ≤ 12√κ⋆`
  (`lossL_comparator`). Both bounds use only the realised trajectory.
* *Regret with self-bounding.* `‖∇L_s‖₂ ≤ L_s`, and on the band `L_s ≤ 17 d √κ⋆`. AdaGrad-norm
  regret `≤ 1.5 D √(Σ‖∇‖²)` with `D = √d ln(2d)` therefore gives
  `Σ L_s(φ_s) ≤ 2 Σ L_s(P') + (9/4) D² F` per learner and box segment
  (`learner_step_bound`, `self_bounding`).
* *Accounting.* There are at most `d⌈log₂ κ⋆⌉` box halvings, because `P⋆ ≤ b ≤ κ⋆P⋆` initially.
  Each abandoned attempt or dropped loss costs at most `8d√κ⋆ + O(log d)` steps. The ledger
  invariant (`Inv`, `Ledger`) is preserved by every macro step (`inv_macro`), and `count_bound`
  turns it into the budget.

## Comparison with prior results (same smoothness/strong-convexity class)

| method (reference) | oracle info | iterations to ε |
|---|---|---|
| AGD, backtracking (Nesterov) | f, ∇f | O(√κ log(1/ε)) |
| Multidimensional backtracking, ellipsoid (Kunstner–Portella–Schmidt–Harvey, NeurIPS 2023, [arXiv:2306.02527](https://arxiv.org/abs/2306.02527), Thm 5.3) | f, ∇f | O(√(2d) κ⋆ log(1/ε) + d log(L/α₀)) |
| OSGM-R (Gao–Chu–Ye–Udell, COLT 2025, [arXiv:2411.01803](https://arxiv.org/abs/2411.01803); Part I preprint [arXiv:2505.23081v2](https://arxiv.org/abs/2505.23081), §6.1, eq. (5)) | f, ∇f, f⋆ | O(κ⋆ L²‖P₁−P⋆‖²_F + κ⋆ log(1/ε)), never worse than O(κ log(1/ε)) |
| Secant-Jacobi + AGD (standard reduction; our check) | f, ∇f | O(d + κ⋆ log(1/ε)) (secant metric has condition ≤ κ⋆²) |
| Fixed-box MB + restarted AGD (our intermediate result; same d-barrier as Jacobi/van der Sluis) | f, ∇f, f⋆ | O(√(dκ⋆)[log(1/ε) + Σ log(B w_i)]) |
| HDM-AGD (Chu et al., ICML 2025, [arXiv:2502.11229](https://arxiv.org/abs/2502.11229), Thm 4.2) | f, ∇f | Euclidean AGD rate with trajectory-dependent constant-factor gains |
| **This result** | f, ∇f, f⋆ | **O(√κ⋆ log(1/ε) + log d log(1/ε) + poly(d) √κ⋆ log κ⋆)** |

Accelerated diagonal-adaptive AdaGrad methods (Ene–Nguyen–Vladu, AAAI 2021,
[arXiv:2007.08840](https://arxiv.org/abs/2007.08840); Kovalev,
[arXiv:2506.23803](https://arxiv.org/abs/2506.23803)) need ℓ∞-bounded iterates or domains and pay
`R∞²‖w‖₁`. After restarting, they lose the coordinate-scale spread that preconditioning is meant to
remove.

**Open question addressed.** OSGM Part II ([arXiv:2509.11007v2](https://arxiv.org/abs/2509.11007),
§5.3, Question 3) asks whether, with knowledge of `f⋆`, an `O(√κ⋆ log(1/ε))` complexity is
achievable asymptotically with a first-order oracle. Stochastic OSGM
([arXiv:2609.11751v2](https://arxiv.org/abs/2609.11751)) states that Nesterov guarantees are
unknown in OSGM. For diagonal candidate sets this theorem answers the question affirmatively, with
an explicit, `ε`-independent polynomial warm-up.

## Regimes and limitations (stated honestly)

* The improvement is asymptotic in `ε`. Against the `√(dκ⋆)` box/Jacobi barrier, the warm-up
  `≈ d³ log²d log κ⋆ √κ⋆` is repaid only once `log(1/ε) ≳ d^{2.5}` (up to logarithms). Against
  `κ⋆`-type bounds (OSGM-R, secant-Jacobi), the leading term improves once `κ⋆` is large (with the stated constants, roughly `κ⋆ ≳ 10³`) and `ε` is
  small enough. Against Euclidean AGD, it improves when `κ ≫ κ⋆` and `ε` is small. No uniform
  dominance is claimed.
* Constants are large (leading term ≈ 48√κ⋆ log₂(Δ/ε) calls). Small-dimensional numerical tests
  (d ≤ 100) show no practical gain over the box/Jacobi baselines. The contribution is a worst-case
  guarantee.
* The method needs `f⋆`, like OSGM-R and the question it answers. AGD, multidimensional
  backtracking and Jacobi do not.
* Strong convexity in the `w`-norm is used, not only quadratic growth. The hindsight comparator
  needs `‖x_s − x_{s+2}‖_w` to be controlled through a unique minimiser.
* The epochs are restarts. They are intrinsic here: `f⋆`-halving supplies linear convergence without
  knowing `μ`, the epochs are the rounds of the online-learning problem, and the metric changes
  between them. This departs from the repository's default preference for restart-free accelerated
  methods.
* Full-matrix candidate sets and a lower bound for learning diagonal preconditioners remain open.
  The polynomial warm-up is not claimed to be optimal.
