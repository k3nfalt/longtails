# Momentum-free acceleration: gradient descent with a fractal Chebyshev stepsize schedule on Hessian-Lipschitz nonconvex functions

## Setup

Lean setup: [`LongTails/Setups/HessianLipschitzGradientStationarity.lean`](../Setups/HessianLipschitzGradientStationarity.lean).

- **Objective class.** Let `E` be a finite-dimensional real inner-product space of any dimension. The objective `f : E → ℝ` is `C²` and has
  - an `L`-Lipschitz gradient: `‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖`;
  - a `ρ`-Lipschitz Hessian in operator norm: `‖∇²f(x) − ∇²f(y)‖ ≤ ρ‖x − y‖`;
  - an initial gap `f(x₀) − f(x) ≤ Δ` for all `x`.

  This is the standard class for accelerated nonconvex first-order methods (Carmon–Duchi–Hinder–Sidford 2017; Jin–Netrapalli–Jordan 2018; Li–Lin 2022). The class is not restricted further: there is no convexity, no strict-saddle assumption, no bounded domain, and no spectral model.
- **Oracle.** An exact gradient oracle: a query at `x` returns `∇f(x)`. No function values, no Hessian–vector products, and no randomness.
- **Accuracy.** The returned point `x̂` satisfies `‖∇f(x̂)‖ ≤ ε`, deterministically (`∀ ω`).
- **Cost.** The number of gradient queries is the `execute` budget. Every query is counted, including those after the method has stopped.
- **Admissible algorithms (`allowedAlgorithm`).** The method must be gradient descent and nothing else: every update is `x ← x − h·∇f(x)`, with no momentum, extrapolation, or auxiliary sequence. The stepsize `h` is either `1/L` or the current entry of a finite list `steps` of positive stepsizes, selected by a counter.
  - The counter advances along `steps` during a "block" and restarts (Li–Lin-style distance restart) once the iterate leaves a ball of radius `R` around the block's starting point, or once the list is exhausted.
  - When the counter is at `0` and `‖∇f(x)‖ > G1`, the method takes a plain `1/L` step instead.
  - The method stops, keeping its point, at the first queried `x` with `‖∇f(x)‖ ≤ ε`.

  The tuning parameters `G1`, `R` and `steps` are left existential. The setup therefore pins down the update family (memoryless GD steps), the restart rule and the output rule, and nothing else.

## Algorithm

Lean: [`LongTails/Algorithms/RestartedChebyshevGd.lean`](../Algorithms/RestartedChebyshevGd.lean) and [`LongTails/Algorithms/FractalChebyshevSteps.lean`](../Algorithms/FractalChebyshevSteps.lean).

1. **Block length.** Let `k = ⌊log₂⌊L²/(2²² ρ ε)⌋⌋ / 9` (integer division) and `n = 2^k`, so that `n⁹ ≲ L²/(ρε)`.
2. **Small regime (`k < 2`).** The method is plain GD with step `1/L` (`G1 = 0`, no list).
3. **Main regime (`k ≥ 2`).**
   - **Parameters.** Put `τ = 2(k+2)/n` and `μ = L·(cosh τ − 1)/(cosh τ + 1)`, which gives `L/μ ≈ n²/(k+2)²`.
   - **Stepsizes.** The `n` stepsizes are the reciprocals of the Chebyshev roots on `[μ, L]`, `1/((L+μ)/2 + (L−μ)/2·cos θ_j)`.
   - **Order.** The angles `θ_j` come in the recursive "small-step-first" fractal order: `Θ₀ = [π/2]`, and `Θ_{i+1}` replaces each angle `ψ` of `Θ_i` by the pair `π/2 − ψ/2, π/2 + ψ/2`.
   - **Thresholds.** `G1 = nε` and `R = 8·S·G1`, where `S = Σ_j h_j` is the total block stepsize.
   - **Output.** The returned point is the stopped iterate.

## Main theorem

Lean: [`LongTails/Theorems/FractalChebyshevGdStationarity.lean`](FractalChebyshevGdStationarity.lean), `result : Convergence spec budget`.

For all valid parameters (`L, ρ, ε > 0`, `Δ ≥ 0`), all admissible `f`, and all exact gradient oracles, the output satisfies `‖∇f(x̂)‖ ≤ ε` after

```
N = ⌈1000 · log₂(2 + L²/(ρε)) · (ρε/L²)^{1/9} · LΔ/ε² + (L²/(ρε))^{1/9} + 2⌉
```

gradient queries. That is,

```
N = O( Δ L^{7/9} ρ^{1/9} ε^{-17/9} · log(L²/(ρε)) + (L²/(ρε))^{1/9} ).
```

The ε-exponent is `17/9 ≈ 1.889`, strictly below the exponent `2` of gradient descent. The bound holds for every ε. When `L²/(ρε) < 2⁴⁰`, the method is plain GD, and the same formula dominates `2LΔ/ε² + 1`.

**The gain is asymptotic.** With the proved constants, the leading term `1000·log₂(L²/(ρε))·(ρε/L²)^{1/9}·LΔ/ε²` drops below GD's `2LΔ/ε²` only when `(L²/(ρε))^{1/9} > 500·log₂(L²/(ρε))`, that is, `L²/(ρε) ≳ 2¹⁴⁵ ≈ 10⁴³·⁷`. For `2⁴⁰ ≤ L²/(ρε)` below that threshold, the method runs Chebyshev blocks with a proved bound worse than GD's. The constants have not been optimised. The contribution is the exponent, not a practical speed-up at moderate accuracy.

## What is new

### Known results

- **GD with steps `h/L`, `h ∈ (0, 2)`, needs `Θ(LΔ/ε²)` queries, even on C^∞ functions.** If the stepsizes are bounded by `2/L`, a smoothly flattened linear ramp (zero Hessian on most of its length) forces order `LΔ/ε²` steps. This per-ε worst case, `Θ(LΔ/ε²)` for bounded steps, is folklore. Cartis–Gould–Toint (SIAM J. Optim. 2010, steepest descent complexity) ask a different and harder question: whether a *single* function with Lipschitz continuous second derivatives forces order `ε^{-2}` evaluations for every ε. The ramp does not answer their question, and neither does this work. Gratton–Sim–Toint (arXiv 2408.09124) show that, for each fixed function, steepest descent with standard stepsizes (Armijo, Goldstein, exact line search) needs only `o(ε^{-2})` iterations as `ε → 0`. This is a per-function asymptotic statement. As they note, it does not contradict the `ε`-dependent lower-bound constructions. The quantity improved here is the uniform worst case over the class, which remains `Θ(LΔ/ε²)` for GD with bounded steps.
- **Methods with momentum reach `Õ(Δ L^{1/2} ρ^{1/4} ε^{-7/4})`.** These are Carmon–Duchi–Hinder–Sidford, *Convex until proven guilty*, ICML 2017 (arXiv 1705.02766); Jin–Netrapalli–Jordan, COLT 2018 (arXiv 1711.10456); and Li–Lin, *Restarted nonconvex accelerated gradient descent*, ICML 2022 (arXiv 2201.11411), which removes the logarithm. Every first-order method needs `Ω(ε^{-12/7})` (Carmon et al., *Lower bounds for finding stationary points II*, Math. Program. 2021, arXiv 1711.00841). Two recent unreviewed preprints claim a matching `Ω(ε^{-7/4})`. Zhou, *Sharp first-order lower bounds for higher-order smooth nonconvex optimization*, arXiv 2606.05438, covers deterministic methods. Zhang et al., *Matching lower bounds for randomized first-order methods in Hessian-Lipschitz nonconvex optimization*, arXiv 2610.00245, covers randomized methods.
- **Long-step schedules are known to accelerate GD only on convex problems.**
  - Silver stepsizes (Altschuler–Parrilo 2023, arXiv 2309.07879 and 2309.16530).
  - Long steps for the objective gap and the gradient norm (Grimmer–Shu–Wang, arXiv 2403.14045).
  - Fractal Chebyshev schedules on quadratics (Agarwal–Goel–Zhang, *Acceleration via fractal learning rate schedules*, ICML 2021, arXiv 2103.01338). That paper explicitly leaves the nonconvex case outside its theory.
  - Chebyshev-type methods under Hessian drift (Pasechnyuk-Vilensky–Takáč, *Chebyshev-exact acceleration under Hessian variation, I: Sine-Jacobi method*, arXiv 2606.16671). This work treats only the strongly convex case, with the drift entering through the interval `[μ, L]`. It also shows that momentum is needed to reach the optimal first-order drift sensitivity. It gives no guarantee for nonconvex stationarity.
- **Predetermined stepsizes cannot fully accelerate GD even on convex problems.** On smooth convex functions, no predetermined schedule reaches the optimal `n^{-2}` rate. Ma–Chen (arXiv 2608.10418) prove `Ω(n^{-1.9319})`, and Ye–Liu (arXiv 2609.02855) improve this to `Ω(n^{-1.6342})`, also allowing negative steps. Both are unreviewed preprints. They are the main contrast for this work. Stepsize-only acceleration is provably weaker than momentum in the convex case, yet here stepsizes alone still break the `ε^{-2}` barrier for nonconvex stationarity. Our method is not purely predetermined, since it uses a restart rule, so these lower bounds do not apply directly. Whether stepsize-based methods must lose to `ε^{-7/4}` in the nonconvex case is open.
- **Window inequality.** The window/fringe inequality used below goes back to Lebedev–Finogenov (1971). It appears as Thms. 8–9 and Lemma 23 of Agarwal–Goel–Zhang. It is re-proved here for this order and is not part of the novelty claim.

### The new result

**This is the first guarantee below `ε^{-2}` for momentum-free gradient descent on general Hessian-Lipschitz nonconvex functions.** The improvement over GD is the factor `(ρε/L²)^{1/9}·log(L²/(ρε))`. It becomes an actual improvement over GD's proved bound only when `L²/(ρε)` is astronomically large (see the asymptotic remark above). The contribution is the exponent. Compared with momentum methods, the result shows that stepsizes alone, with a distance restart, already beat the GD barrier. The `ε^{-7/4}` rate of AGD-type methods is not matched.

### Technical mechanism

1. **Localized quadratic model.** On a ball of radius `R` around a block's start `y`, the gradient is `∇f(y) + H(x − y) + e(x)` with `‖e‖ ≤ ρR²`.
2. **Per-direction recursions.** In the eigenbasis of `H = ∇²f(y)`, each coordinate follows the scalar recursion of GD on a quadratic, perturbed by `e`.
   - **Positive curvature.** The schedule's polynomial has prefix products bounded by `1` and window products bounded by `L/μ`, and it satisfies the accelerated relation `1 − P² ≥ 2λSP²`. Together these give the accelerated decrease `(S/4)·‖Π₊ model gradient‖²` with `S ≈ n²/(L log n)`, where GD would give `n/L`.
   - **Negative curvature.** Directions grow monotonically. A good/bad case split on each direction shows that they never increase the model, except through error terms.
3. **Exits.** A block that exits the ball decreases `f` by `≳ S·G1²`.
4. **Debts and the potential.** A completed block whose end gradient lies mostly in negative-curvature directions of `H` is not paid by itself. Its successor block pays instead. The successor is analysed in the *predecessor's* frame and eigenbasis, so no Davis–Kahan argument is needed: its start-based negative-curvature decrease is `(S/2)·‖Π₋ γ‖²`. The two frame bounds are combined through `max ≥ average`. A potential `f + P`, with `P ∈ {Q, (S/8)·‖Π₊γ‖²}`, decreases by `≥ Q/(2n)` per gradient query, where `Q = Sε²/16`.
5. **Balancing.** The block length `n` is chosen to balance the accumulated Taylor errors, using the condition `ρ S² n³ ε (L/μ + n) ≲ 10⁻⁷`. This gives `n⁹ ≈ L²/(ρε)` and the rate `ε^{-2}·ε^{1/9}`.

### Obstruction not visible in quadratics

On quadratics, the fractal Chebyshev schedule is known to be accelerated. Two things are new in the nonlinear case:

- The Hessian changes during a block by `ρR`, which is comparable to the smallest Chebyshev root `μ` in the balancing regime.
- Long steps amplify errors through window products of size `L/μ`.

The proof controls both, and the per-direction negative-curvature analysis handles exits. These are the steps that fail in a quadratic-only argument.

## Limitations and open points

- **Rate gap.** The exponent `17/9` is a limitation of this proof (window and Taylor-error accounting), not a lower bound. Abel summation of the gradient errors would plausibly give `15/8`; this is not formalized. Matching `7/4` without momentum remains open.
- **Large constant.** The constant `1000`, and the `2⁻²²` inside the choice of `n`, come from crude bounds. As a result the proved bound beats GD's only when `L²/(ρε) ≳ 2¹⁴⁵`. The method does not fall back to GD in the intermediate regime `2⁴⁰ ≤ L²/(ρε) < 2¹⁴⁵`.
- **Parameter knowledge.** The method needs `L`, `ρ` and `ε`. It does not need `Δ`.
- **Not purely predetermined.** The schedule has a restart rule based on distance and a gradient threshold, which use oracle replies. The step *values* come from a fixed finite menu.
- **Priority.** No earlier sub-`ε^{-2}` bound for momentum-free GD on this class was found in the literature survey (ICML/ICLR/NeurIPS 2024–2026, arXiv 2024–2026). Stepsize research is very active, so priority should be re-checked before publication.

## Proof modules

| Module | Contents |
| --- | --- |
| `Proofs/FractalChebyshevTree` | Fractal order, pair identity, prefix bound ≤ 1. |
| `Proofs/FractalChebyshevExchange`, `FractalChebyshevCollapse`, `FractalChebyshevWindows`, `FractalChebyshevChain` | Lebedev–Finogenov exchange inequality, fringe chains, and window bound ≤ `L/μ`. |
| `Proofs/FractalChebyshevSchedule`, `FractalChebyshevParams` | Stepsize bridge, final relation, and the closed form `S = n·tanh(nτ)/(L·tanh(τ/2))` with its bounds. |
| `Proofs/ScheduleBlockScalar`, `ScheduleBlockGeneric`, `ScheduleCoordinateBounds`, `ScheduleCoordinateBoundsExtra`, `ScheduleCoordinateCases` | Scalar per-direction estimates. |
| `Proofs/ScheduleBlockVector`, `ScheduleBlockEstimates` | Eigenbasis reduction, Cauchy–Schwarz error sums, cubic Taylor bound, and the three block lemmas (completed, predecessor frame, exit). |
| `Proofs/RestartedChebyshevRun`, `RestartedChebyshevCount`, `RestartedChebyshevNumeric`, `RestartedChebyshevConvergence` | Execution of the state machine, potential argument, numeric constants, and budget. |
