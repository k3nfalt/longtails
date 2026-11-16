# Projection complexity of stochastic convex optimization over many convex sets

This note explains the result formalized in
[PenaltyKatyushaManyConstraint.lean](PenaltyKatyushaManyConstraint.lean). The other pieces are:

- the [setup](../Setups/ManyConstraintStochasticConvex.lean);
- the [algorithm](../Algorithms/ManyConstraintMethod.lean), which is built from
  [the query plan](../Algorithms/ManyConstraintVR.lean) and the
  [two-oracle plan type](../Algorithms/ManyConstraintPlan.lean);
- the proof modules: [convergence and execution](../Proofs/ManyConstraintConvergence.lean),
  [final expectations](../Proofs/ManyConstraintFinal.lean), [budget algebra](../Proofs/ManyConstraintBudget.lean) and
  [multi-epoch energy](../Proofs/ManyConstraintMulti.lean).

**Summary.** The problem is to minimize a stochastic convex objective over the intersection of m closed convex sets,
using two separately counted oracles: stochastic gradients, and the exact projection onto one chosen set. We give
and formalize a single method with the following costs.

- **Projections:** N_p = Õ(m + √(mκ)·(σR/ε + R√(L/ε)) + κ log(R/δ)).
- **Gradient samples:** N_g = Õ(σ²R²/ε² + LR²/ε + m + √(mκ)·(σR/ε + R√(L/ε))).
- **Output guarantee:** E(f(out) − f*)₊ ≤ ε and E dist(out, C)² ≤ δ².
- **Parameters:** κ is the average-form linear-regularity constant of the sets, σ² is the second moment of the
  stochastic gradient at a solution, L is the componentwise smoothness constant, and R ≥ ‖x₀ − x*‖.

In the note (on paper, not in Lean) we prove a matching lower bound, N_p = Ω(m + √(mκ)·GR/ε), for the stated regime.
It holds whenever κ ≥ 2m + 2, √κ ≲ √m·GR/ε, ε ≲ G√κR/√m and δ ≲ ε/(G√κ), with G = ‖∇f(x*)‖ ≤ σ. It is proved by
reduction from Woodworth–Srebro's finite-sum lower bound, for randomized algorithms whose projection queries lie in a
ball B(x₀, ρ) with ρ ≥ 3R. Within that algorithm class, and when in addition σ ≍ G, L ≲ σ²/ε (so the R√(L/ε)
term is lower order) and κ log(R/δ) ≲ √(mκ)·σR/ε, the projection complexity is therefore Θ̃(m + √(mκ)·σR/ε),
while the noise σ² is paid only in gradient samples.

This is a characterization obtained by **reduction plus composition**:

- the lower bound is an epigraph lifting of a known construction;
- the method combines a quadratic penalty, Katyusha-type variance reduction over the penalty components, minibatched
  stochastic gradients, a regularization, and a Fejér clean-up.

Each ingredient is standard. The new elements are the precise two-oracle statement, the parameter mapping that makes
the lifted lower bound match, and a complete machine-checked upper bound under the weak noise assumption. Our gradient
count is not optimal: a heavier composition with gradient sliding (B8″ below) has better N_g. Nothing is claimed for
m > κ.

## Setup (Lean: `LongTails.Setups.ManyConstraintStochasticConvex`)

- **Space and sets.** E is a real Hilbert space (any dimension). C₁, …, C_m ⊆ E are closed and convex, with
  intersection C ≠ ∅.
- **Objective.** f(x) = E_ξ f_ξ(x), where each f_ξ is convex and differentiable with an L-Lipschitz gradient ∇f_ξ.
  The map (ξ, x) ↦ ∇f_ξ(x) is jointly measurable, and f_ξ(x) is integrable for every x.
- **Solution and noise.** There is a minimizer x* of f over C with ‖x₀ − x*‖ ≤ R and E‖∇f_ξ(x*)‖² ≤ σ². This is an
  uncentered second moment at x* only; no uniform variance bound is assumed. It implies G := ‖∇f(x*)‖ ≤ σ.
- **Regularity.** Average-form linear regularity holds for every x:

  dist(x, C)² ≤ κ · (1/m) Σ_j dist(x, C_j)².
- **Oracles** (`numOracles = 2`). The two oracles are counted separately; each call consumes one IID sample ξ.
  - Oracle 0 is a stochastic gradient: query (x, ·) returns ∇f_ξ(x).
  - Oracle 1 is a projection: query (x, some j) returns the exact projection Π_{C_j}(x), characterized variationally
    (Π_j x ∈ C_j and ⟨x − Π_j x, w − Π_j x⟩ ≤ 0 for all w ∈ C_j). Query (x, none) returns x.
  - The sample stream is IID with law `M.law` in the abstract sense of the library's `IID` structure. The proof
    derives the product representation internally.
- **Public information.** The algorithm receives m, L, R, σ, κ, ε, δ and x₀. It is not told the sets, the law, x* or
  G.
- **Success criterion.** The output must be measurable and satisfy

  ∫ (f(out) − f(x*))₊ dP ≤ ε and ∫ dist(out, C)² dP ≤ δ²,

  where P is the product of the algorithm's seed law and the oracle stream law.
  - The positive part is natural here, because an infeasible point can have f(out) < f*.
  - The two accuracies are independent: δ is not tied to ε.
- **Validity.** 0 < m, 0 < L, 0 ≤ R, 0 ≤ σ, 1 ≤ κ, 0 < ε, 0 < δ.

## Algorithm and output (Lean: `LongTails.Algorithms.ManyConstraintMethod.method`)

If R = 0, the method returns x₀ (= x*) with no queries. Otherwise the parameters are:

- μ = ε/(384R²), β = 384κ(σ²/ε + L) and L_t = L + β;
- t = max(1, ⌈√(L_t/(2mμ))⌉), τ = 1/(2t), α = 1/(24 m t μ) and θ = 1 + αμ (the library's Katyusha tuning for
  m components, smoothness L_t and modulus μ);
- an inner-loop length M = 2m and a minibatch size b = max(1, ⌈t(768σ²/ε + 2L)/L_t⌉);
- S = ⌈(12t + 1)·log(64(2σR + 2L_tR² + 3ε)/ε)⌉ epochs, and Q = ⌈κ log(4R²/δ²)⌉ clean-up projections.

The method runs strongly convex Katyusha with a ball constraint on the regularized penalty

  Φ(x) = f(x) + (1/m) Σ_j (β/2) dist(x, C_j)² + (μ/2)‖x − x₀‖²  over the ball B(x₀, R).

Each penalty component (β/2)dist(x, C_j)² is β-smooth with gradient β(x − Π_j x), so evaluating it costs one
projection. Each epoch, starting from a snapshot s, does the following.

- **Snapshot pass.** Compute the full penalty gradient at s with m projections.
- **Inner steps.** Repeat M times with a uniformly random j. Form x = τz + s/2 + (1/2 − τ)y. Query b fresh stochastic
  gradients at x, the projection Π_j x and the projection Π_j s. Build the estimator

  v = (1/b)Σ ∇f_{ξ_i}(x) + β(x − Π_j x) − β(s − Π_j s) + ∇h_β(s).
- **Updates.** y⁺ = prox over the ball with step 1/(3L_t) at x, and z⁺ = prox over the ball with step α at z. Both
  are closed-form ball-constrained proxes of the regularizer (shrink towards x₀, then project onto B(x₀, R)).
- **New snapshot.** The θ-weighted average of the y iterates.

After S epochs the method applies Q uniformly random projections to the last snapshot (a Fejér clean-up) and
returns the result. The random indices form the algorithm's seed; they are drawn uniformly from the finite set
(Fin S → Fin M → Fin m) × (Fin Q → Fin m). The execution is a fixed query plan (`fullPlan`) and its output is
`cleanup(run(...).s)` (Lean `evalS_fullPlan`, `out`).

**Query locations.** These matter for the lower-bound class.

- All gradient and projection queries of the Katyusha phase are taken at convex combinations of points of B(x₀, R),
  so they lie in B(x₀, R).
- The clean-up queries p_n satisfy ‖p_n − x*‖ ≤ ‖s − x*‖ ≤ 2R (Fejér monotonicity, `cleanup_fejer`), so they lie in
  B(x₀, 3R).

## Proved guarantee (Lean: `OracleTemplate.PenaltyKatyushaManyConstraint.result`)

`result : Convergence spec budget`. For every valid parameter and every admissible instance, the output satisfies
both accuracy requirements within the following call budgets, writing Γ = σR/ε + R√(L/ε) and
Λ = log(50000 κ (1 + σR/ε + LR²/ε)²):

- gradient oracle: 2m · ⌈(13 + 3264 √(κ/m) Γ) Λ⌉ · ⌈3 + 544 Γ/√(mκ)⌉;
- projection oracle: ⌈κ log(4R²/δ²)⌉ + 5m · ⌈(13 + 3264 √(κ/m) Γ) Λ⌉.

In order notation this is

  N_p = O((m + √(mκ) Γ) Λ + κ log(R/δ)),  N_g = O((m + √(mκ) Γ + Γ²) Λ),  with Γ² ≍ σ²R²/ε² + LR²/ε.

So N_g = Õ(T_g + N_p), where T_g = σ²R²/ε² + LR²/ε is the gradient count of plain SGD on the unconstrained problem.

The guarantee is for the clean-up of the final snapshot, i.e. a last-iterate type output, not an average over
iterations.

### Proof outline (all steps in Lean)

1. **Expected one-step inequality** (`ManyConstraintExpected`).
   - The f-noise is state dependent: E‖∇f_ξ(x) − ∇f(x)‖² ≤ 4L·D_f(x, x*) + 2σ², by componentwise co-coercivity.
   - With the batch condition L ≤ τ L_t b, this term is absorbed by the co-coercivity gain of the Katyusha
     coupling. This is the step the Reviewer flagged as needing verification "in the actual energy"; it is proved
     here.
   - The remaining exogenous error per step is σ²/(2L_t b).
2. **Shifted gap.** Dgap(x) = Φ(x) − Φ(x*) + c₀ with c₀ = κσ²/(2β) + μR²/2 is nonnegative on the ball
   (`ManyConstraintLower`). The proof uses first-order optimality of x* on C, G ≤ σ, and linear regularity, which
   give Φ(x) − Φ(x*) ≥ −σd + (β/2κ)d² − μR²/2 with d = dist(x, C).
3. **Epoch and multi-epoch energy** (`ManyConstraintInner`, `ManyConstraintEpochEnergy`, `ManyConstraintMulti`):
   (θ^M)^S · E Pot_S ≤ Pot₀ + Σ_{i<S}(θ^M)^i · (weight sum) · err. With the library tuning this gives
   E Dgap(s_S) ≤ ε/16 (`ED_bound`).
4. **From gap to objective and distance** (`ManyConstraintSuccess`).
   - (f(s) − f*)₊ ≤ Dgap(s) + μR²/2.
   - dist(s, C)² ≤ 4κ Dgap/β + 4κ²σ²/β².
   - The clean-up damage is (f(p) − f*)₊ ≤ 2(f(s) − f*)₊ + 3σd + 4Ld², which gives (f(p) − f*)₊ ≤ (11/5)·Dgap(s) + ε/7
     pathwise. Hence E(f(out) − f*)₊ ≤ (11/5)(ε/16) + ε/7 < ε.
5. **Feasibility.** Each random projection contracts E dist² by (1 − 1/κ) (`cleanup_feasibility`, from linear
   regularity in average form). So E dist(out, C)² ≤ (1 − 1/κ)^Q (2R)² ≤ δ².
6. **Execution and budget.**
   - The algorithm is a fixed two-oracle query plan, executed exactly by the template's `execute` (`execute_plan`).
   - The counts are S·M·b gradients and Q + S(2M + m) = Q + 5mS projections.
   - These are bounded by the one-line public budget (`ManyConstraintBudget`) using t ≤ 1 + 272√(κ/m)Γ,
     b ≤ ⌈3 + 544Γ/√(mκ)⌉, and log of the start gap ≤ Λ.

## Lower bound (paper proof; not formalized)

The Setup cannot express lower bounds, so this part is a paper proof only.

**Theorem LB.** Let the following hold:

- m ≥ 2, κ ≥ 2m + 2, G > 0, R > 0, L > 0 and ρ ≥ 3R;
- 0 < ε < G√κ·R/(60√m) and √κ ≤ √m·GR/(30ε);
- 0 < δ ≤ ε/(2G√κ).

Then there are a finite dimension d (polynomial in m, κ, GR/ε and ρ/R) and a random family of instances with the
following properties:

- every instance satisfies all Setup assumptions with parameters (m, L, R, σ = G, κ, ε, δ) in E = ℝ^{d+m};
- every (randomized) algorithm whose projection queries all lie in B(x₀, ρ) and whose projection budget is below
  c·(m + √(mκ)·GR/ε) fails the Setup's success criterion on some instance of the family. Here c > 0 is an absolute
  constant, and the gradient budget is arbitrary.

Gradient queries are unrestricted and free in this construction.

**Source.** Woodworth & Srebro, *Tight Complexity Bounds for Optimizing Composite Objectives*, NeurIPS 2016,
[arXiv:1605.08003v3](https://arxiv.org/abs/1605.08003) (WS16).

- Theorem 5, with the proof in App. C/C.1: for L′, B > 0, m ≥ 2, ε′ < L′B/(10√m) and a randomized algorithm with
  access to h_F(x, i, β) = (f_i(x), ∂f_i(x), prox_{f_i}(x, β)), F = (1/m)Σf_i over X = {‖x‖ ≤ B}, reaching
  E[F(x̂) − F*] < ε′ needs Ω(m + √m·L′B/ε′) queries.
- Their hard family consists of m/2 pairs f_{i,1}, f_{i,2}, built from orthonormal random vectors v_{i,0..k} and
  ψ_c(z) = max(0, |z| − c), with k = ⌊L′B/(10ε′√m)⌋ and b = B√(2/(m(k+1))).
- The proof combines Property 1 (an oracle answer at a point with small inner products against the unknown v's
  reveals at most the next vector) and Lemma 8 (if all queries have norm ≤ B_q and d ≥ 2N + (2/α²) log(2mkN) with
  α ∝ c/(B_q(1 + c√(2N))), then with probability ≥ 3/4 the premise of Property 1 holds for all N queries).
- WS16 state explicitly that Lemma 8 needs bounded query norms (App. C, before Lemma 6, and the Remark after C.1).

**Construction.** Write φ_i for the WS16 functions with Lipschitz constant L′ = G_φ and radius B. Set

  a = G√m, G_φ = G√(κ − m − 1), B = R/√2, z = (x, t) ∈ ℝ^d × ℝ^m,
  C_i = {(x, t) : ‖x‖ ≤ B, a·t_i ≥ φ_i(x)}, f(z) = (a/m) Σ_i t_i (deterministic, so σ = ‖∇f‖ = a/√m = G),
  x₀-public start z₀ = (0, t⁰) with t⁰_i = φ_i(0)/a.

The start is instance-independent: φ_i(0) = G_φ b/√2 for the f_{·,1} components and 0 for the f_{·,2} components,
whatever the random vectors are. The Setup conditions are checked as follows.

1. **Convexity and closedness** hold. f is linear, so its gradient is 0-Lipschitz and any L > 0 is admissible. Exact
   projections onto C_i exist. Take Ξ a one-point space, so the IID stream is trivial.
2. **Value.** For z ∈ C we have f(z) ≥ (1/m)Σφ_i(x) = F(x), with equality at t_i = φ_i(x)/a. Hence min_C f = F* and
   z* = (x*, φ(x*)/a) is a minimizer, where x* = b Σ_{i,r} v_{i,r} is the WS16 minimizer with ‖x*‖ = B. Also
   E‖∇f_ξ(z*)‖² = G² = σ².
3. **Linear regularity with constant κ.** Let z = (x, t) and x′ = Π_{‖·‖≤B} x.
   - Since every C_i ⊆ {‖x‖ ≤ B} × ℝ^m, we have ‖x − x′‖ ≤ d_i := dist(z, C_i) for each i.
   - Let (y, s) = Π_{C_i} z. Then φ_i(x′)/a − t_i ≤ (s_i − t_i) + (G_φ/a)‖x′ − y‖ ≤ (s_i − t_i) + (G_φ/a)‖x − y‖,
     using that y is in the ball and the ball projection is nonexpansive. By Cauchy–Schwarz,
     (φ_i(x′)/a − t_i)₊² ≤ (1 + G_φ²/a²)·d_i².
   - The point (x′, max(t, φ(x′)/a)) lies in C, so
     dist(z, C)² ≤ ‖x − x′‖² + Σ_i (φ_i(x′)/a − t_i)₊² ≤ (1 + m(1 + G_φ²/a²))·(1/m)Σ_i d_i².
   - Since 1 + m + mG_φ²/a² = 1 + m + (κ − m − 1) = κ, the constant is exactly κ.
4. **Radius.**
   - We have f_{i,1}(x*) = f_{i,2}(x*) = 0, so ‖z₀ − z*‖² = B² + (m/2)·G_φ²b²/(2a²) = B²(1 + G_φ²/(2a²(k+1))).
   - Since G_φ²/a² ≤ κ/m, this is at most 2B² = R² as soon as k + 1 ≥ κ/(2m).
   - Set ε′ = 3ε. Since κ ≥ 2m + 2 we have G_φ ≥ G√(κ/2), so G_φB ≥ G√κR/2 and
     k + 1 ≥ G_φB/(10ε′√m) ≥ G√κR/(60ε√m).
   - So k + 1 ≥ κ/(2m) holds whenever √κ ≤ √m·GR/(30ε), which is the hypothesis.
5. **WS16 accuracy range.** ε′ = 3ε < G_φB/(10√m) holds because ε < G√κR/(60√m) and G_φB ≥ G√κR/2.

**Oracle answers reveal no more than WS16's oracle** (Property 1 holds for the projection oracle).

- The gradient oracle returns the constant vector ∇f and reveals nothing.
- A projection query (z̄ = (x̄, t̄), j) returns (y, s), with s_l = t̄_l for l ≠ j. The pair (y, s_j) is the
  projection of (x̄, t̄_j) onto K_j = {(u, τ) : ‖u‖ ≤ B, aτ ≥ φ_j(u)}, i.e. onto the epigraph of
  g = φ_j/a + ι_{‖·‖≤B}.
  - If (x̄, t̄_j) ∈ K_j, the answer is the query itself.
  - Otherwise, by the KKT conditions, y = argmin_{‖u‖≤B} φ_j(u) + (β*/2)‖u − x̄‖² = prox_{φ_j}(x̄, β*), the WS16
    prox over X, and s_j = φ_j(y)/a. Here β* ∈ (0, ∞] is the unique root of the monotone equation
    β = a / (φ_j(prox_{φ_j}(x̄, β))/a − t̄_j), where β = ∞ means y = Π_ball x̄.
- **Ball-constrained prox.** WS16's Property 1 proof concerns the unconstrained prox
  prox^unc_φ(x, β) = argmin_u φ(u) + (β/2)‖u − x‖², through the free u^⊥ block. With the ball inside C_j we reduce
  to it. Let λ ≥ 0 be the multiplier of ‖u‖ ≤ B. Then
  argmin_{‖u‖≤B} φ(u) + (β/2)‖u − x̄‖² = prox^unc_φ(γx̄, β + λ) with γ = β/(β + λ) ∈ (0, 1].
  - This is the KKT condition 0 ∈ ∂φ(u) + β(u − x̄) + λu, rewritten as 0 ∈ ∂φ(u) + (β + λ)(u − γx̄).
  - λ = 0 if ‖prox^unc_φ(x̄, β)‖ ≤ B. Otherwise λ is the smallest root of ‖prox^unc_φ(γ(λ)x̄, β + λ)‖ = B.
  - The minimizer is unique by strong convexity, so any root gives the same point.
  - The premise of Property 1 is preserved at γx̄, since |⟨γx̄, v⟩| ≤ |⟨x̄, v⟩| ≤ c/2.
  - So, by the argument below applied to the unconstrained prox, the norm map λ ↦ ‖prox^unc‖ is a deterministic
    function of the same known information. Hence so are λ and the constrained prox, which lies in
    span{x̄, known v's, v_{j,t}}.
  - Below, "prox_{φ_j}(x̄, β)" denotes this ball-constrained prox.
- Fix a query whose x-part x̄ satisfies the premise of Property 1 (|⟨x̄, v⟩| ≤ c/2 for all unknown v of pair j).
  The WS16 proof of Property 1 (App. C.1, "We now prove the properties about the proxs") shows that for **every**
  β > 0, for the unconstrained prox at any point γx̄ with γ ∈ (0, 1] (hence, by the reduction above, also for the
  ball-constrained one):
  - prox_{φ_j}(x̄, β) = x̄^⊥ + x̄⁺ + (a minimizer over the known block x̄⁻), which lies in span{x̄, known v's, v_{j,t}};
  - this minimizer is a deterministic function of x̄ and the known vectors;
  - the value φ_j at that point equals φ_j of its known block, because ψ_c is flat on the unknown block (the "x⁺"
    part).
- Hence the map β ↦ (prox_{φ_j}(x̄, β), φ_j(prox)) is a deterministic function of x̄ and the known vectors (plus at
  most v_{j,t}). So are its root β* and the answer (y, s), and the answer lies in span{x̄, known vectors, v_{j,t}}
  in the x-block.
- The same holds in the limit case β* = ∞ (ball projection) and in the feasible case. Membership is decided by
  φ_j(x̄), which is also determined by the same information.
- This is exactly the conclusion of Property 1 (and Corollary 1) for our oracle, so it is used in place of h_F.
  There is no inexact simulation and no log-factor loss.

**High dimension and bounded queries.**

- A projection query lies in B(z₀, ρ), and z₀ has x-part 0, so its x-part satisfies ‖x̄‖ ≤ ρ.
- Lemma 8 then applies with query bound B_q = ρ, and a dimension d ≥ 2N + O((ρ/B)²(1 + c√(2N))²c⁻² log(mkN)) that
  is polynomial in m, κ, GR/ε and ρ/R.
- With probability ≥ 3/4 over the random vectors, the event E of WS16 holds for the first N projection queries.
  On E, by Property 1, query n reveals at most one new vector of the queried pair.

**Output transfer.** Let z_out = (x̂, t̂) be the algorithm's output and let w = Π_C(z_out) = (x_w, t_w), so that
D := ‖z_out − w‖ = dist(z_out, C).

- Since f is linear, F(x_w) ≤ f(w) ≤ f(z_out) + G·D.
- The point x̂′ = Π_ball(x̂) satisfies ‖x̂′ − x_w‖ ≤ D, and F is G_φ-Lipschitz.
- Hence F(x̂′) − F* ≤ (f(z_out) − f*)₊ + (G + G_φ)·D.
- Taking expectations and using Jensen, E[F(x̂′) − F*] ≤ ε + 2G√κ·δ ≤ 2ε < ε′.
- x̂′ is a deterministic function of the output with ‖x̂′‖ ≤ B. We count it as one extra query point (as WS16 do for
  the final iterate), so it is covered by E.
- Run WS16's proof of Theorem 5 (App. C.1) with our oracle in place of h_F. On E, after N queries at most N vectors
  v_{i,r} are revealed. If v_{i,k} is unrevealed for at least m/4 pairs, the App. C.1 bound gives
  F(x) − F* ≥ ε′ for every x in the span of the revealed information. So any algorithm reaching
  E[F(x̂′) − F*] < ε′ needs Ω(m(k+1)) projection queries. Yao's principle extends this to randomized algorithms.
- **Fixed budgets.** Suppose an algorithm in the class, with projection budget N < c·(m + √(mκ)GR/ε), met the
  success criterion on every instance of the family. Then it would also meet it in expectation over the random
  draw of the vectors v_{i,r}.
  - The output transfer then gives E[F(x̂′) − F*] < ε′, with the expectation over both the family and the
    algorithm's randomness.
  - The simulated algorithm makes N + 1 bounded queries, which contradicts WS16's bound for c small enough.
  - Hence some instance of the family defeats the algorithm.
- Hence N_p = Ω(m(k+1)) − 1 = Ω(m + √m·G_φB/ε) = Ω(m + √(mκ)·GR/ε).

**Limitations of the lower bound.**

- **Bounded queries.** Algorithms that query projections at arbitrarily far points are not covered. This comes from
  the random high-dimensional proof technique (Lemma 8 needs bounded query norms), not from the problem. WS16 sketch
  a Lipschitz extension outside the ball that removes the restriction for gradient/prox oracles (Remark after C.1);
  we have not verified that an analogous extension works for epigraph projections, so we leave it open.
- **Query radius.** The upper-bound method lies inside the class with ρ = 3R, which makes the matching meaningful.
  Restricting query locations is standard for explicit randomized lower bounds (WS16, App. C).
- **Feasibility part.** The lower bound concerns the √(mκ)·GR/ε part only. The κ log(R/δ) clean-up term of the upper
  bound and the Õ(·) logs are not matched.
- **Regime.** It is tight only for κ ≥ 2m + 2 (up to constants, m ≲ κ). For m > κ the sets become individually
  redundant (a sampled subfamily already approximates C), and neither the lower bound nor optimality of the m-term
  is claimed there.

## What is known and what is new

| Method | N_g | N_p | Status |
|---|---|---|---|
| Anchor: Vaidyan–Friedlander–Alacaoglu, [arXiv:2602.05489](https://arxiv.org/abs/2602.05489) (PMLR v306), Thm 4.1 | — | — | Covers proxes of Lipschitz g_j, or the full projection Π_C. They list random projections onto C_j (g_j = ι_{C_j}) as open. |
| Inner-loop random projections + projected SGD (e.g. Chakraborty–Nedić, [arXiv:2601.20076](https://arxiv.org/abs/2601.20076), ICML 2026; Wang et al. [arXiv:1511.03760](https://arxiv.org/abs/1511.03760)) | Õ(T_g) | ≈ N_g·κ log(1/η) | Assumptions are stronger (bounded subgradients, or deterministic gradients). |
| Mishchenko–Richtárik, Stochastic Decoupling Method, [arXiv:1905.11535](https://arxiv.org/abs/1905.11535), NeurIPS 2019 | one stochastic gradient per step | one prox of a single ι_{C_j} per step (m stored dual variables) | Covers f + Σ_j ι_{C_j} with σ* only at the solution and existence of multipliers. Criterion: Bregman/Lagrangian gap D_f(x̄, x*) of the averaged iterate, O(1/√t) with SGD; constants involve multiplier norms and m. No (f − f*)₊ or feasibility guarantee. |
| Patrascu–Necoara, [arXiv:1706.06297](https://arxiv.org/abs/1706.06297), JMLR 2018 | joint prox of f(·; S) + ι_{X_S} | same | Same average-form linear regularity. Convex case needs bounded subgradients, with rate O(E[L²]R²/ε²) up to κ factors (Cor. 8). The σ*-at-solution version needs strong convexity (Thm 17). |
| Kundu–Bach–Bhattacharyya, [arXiv:1710.06465](https://arxiv.org/abs/1710.06465), AISTATS 2018 | deterministic | all m projections per iteration | Exact penalty under max-form linear regularity. Deterministic f; smooth case O(1/ε) iterations, so N_p = O(m/ε). |
| m-free plain: one random projection per SGD step plus clean-up (composition) | Õ(T_g) | Õ(T_g + κσ²R²/ε² + κ log(R/δ)) | Its N_p is smaller when m ≳ κσ²R²/ε². |
| B8″ composition: penalty + Ivanova et al. separation ([arXiv:2002.02706](https://arxiv.org/abs/2002.02706), JOTA 2022, Cor. 4.3) / sliding + minibatch SA under state-dependent noise + clean-up | O(√(LR²/ε) + σ²R²/ε²) | Õ(m + √(mκ)Γ + κ log(R/δ)) | Paper-level composition. It has not been written down as a theorem in this form as far as we found, and it is not formalized. |
| **This result (Lean)** | Õ(T_g + m + √(mκ)Γ) | Õ(m + √(mκ)Γ + κ log(R/δ)) | Single-loop method, fully formalized. |
| **Lower bound (this note)** | any | Ω(m + √(mκ)GR/ε) | Projection queries in B(x₀, ρ); κ ≥ 2m + 2; δ ≲ ε/(G√κ). |

Here Γ = σR/ε + R√(L/ε) and T_g = σ²R²/ε² + LR²/ε.

**What is new.**

1. **A two-oracle characterization of the projection complexity.** In the regime above it is
   N_p = Θ̃(m + √(mκ)·σR/ε) when σ ≍ G and the L-term is lower order. We found no prior statement of this
   characterization for many-constraint stochastic convex optimization.
   - The matching depends on a non-obvious parameter mapping: a = G√m, G_φ = G√(κ − m − 1), and the radius
     computation R² = B²(1 + G_φ²/(2a²(k+1))).
   - The mapping identifies √(mκ)·G as the price of projections. The noise σ² enters only the gradient count.
2. **A complete, machine-checked upper bound under weak assumptions.** The assumptions are a second moment at x*
   only, the (·)₊ criterion together with expected squared infeasibility, independent ε and δ, and arbitrary Hilbert
   space. The state-dependent gradient noise is absorbed inside the Katyusha energy with a constant minibatch. This step
   is proved, not assumed.
3. **A different answer to the anchor's open case g_j = ι_{C_j}.** That case already has a variance-reduced
   answer with one projection per step: Mishchenko–Richtárik's SDM, with σ* at the solution. SDM, however, uses a
   weaker criterion (Bregman gap of an averaged iterate, multiplier-dependent constants). Our contribution there is
   a different accelerated method and accounting:
   - separate counts of the two oracles;
   - the (·)₊ objective criterion together with E dist² ≤ δ², with public-parameter constants;
   - the matching lower bound on projections.

   Neither our method nor SDM uses the anchor's own template (last iterate of prox-SGD).

**What is not new.** Every algorithmic ingredient is standard: quadratic penalty, Katyusha
([Allen-Zhu, JMLR 2018](https://arxiv.org/abs/1603.05953)), minibatching under state-dependent noise, random
projections under linear regularity (Necoara–Richtárik–Patrascu, [arXiv:1801.04873](https://arxiv.org/abs/1801.04873)),
and the Fejér clean-up. The lower bound is a direct epigraph reduction from WS16. We therefore assess the result as a
careful tight characterization by reduction plus composition, of incremental significance, and not as a new
algorithmic mechanism.

**Limitations of the upper bound.**

- **Gradient count.** N_g carries the extra terms m + √(mκ)Γ (one minibatch per projection) and LR²/ε instead of
  √(LR²/ε); B8″ avoids both by sliding. This trade is the price of a single-loop method that we could formalize.
- **Log factors.** The log factors in N_p and N_g are not optimized.
- **Parameter knowledge.** The method needs κ, σ, L and R; it is not adaptive.
- **The L-term.** The √(mκ)·R√(L/ε) term in N_p is not matched by the lower bound, which uses a linear f.

## Lean files

- Setup: [ManyConstraintStochasticConvex.lean](../Setups/ManyConstraintStochasticConvex.lean).
- Algorithm: [ManyConstraintMethod.lean](../Algorithms/ManyConstraintMethod.lean),
  [ManyConstraintVR.lean](../Algorithms/ManyConstraintVR.lean) and
  [ManyConstraintPlan.lean](../Algorithms/ManyConstraintPlan.lean).
- Proofs: `LongTails/Proofs/ManyConstraint*.lean`, covering geometry, penalty, coupling, stochastic model, ball
  prox, finite-sum estimator, noise, one-step expectation, run, stream, energy, inner/epoch/multi-epoch energy,
  lower gap bound, clean-up, tuning, accuracy, success, final expectations, budget and convergence.
- Audit: `./build.sh` and `./lint.sh` pass. `python3 run_comparator.py PenaltyKatyushaManyConstraint.lean` reports
  only the axioms propext, Classical.choice and Quot.sound.
