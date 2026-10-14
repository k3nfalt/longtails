# Accelerated composite optimization under (L0, L1)-smoothness without knowing ∇f(x*)

This note explains the contribution formalized in
[CompositeGeneralizedAccelerated.lean](CompositeGeneralizedAccelerated.lean), with the
[setup](../Setups/CompositeGeneralizedSmooth.lean) and the
[algorithm](../Algorithms/CompositeGeneralizedAccelerated.lean).

The theorem is an accelerated oracle-complexity bound for composite or constrained convex problems
min_{x∈Q} f(x) + ψ(x) in which f is (L0, L1)-smooth rather than globally smooth. A single
gradient-and-prox method, which does not know ∇f(x*) or any bound on it, reaches F(x_K) − F* ≤ ε after

  O( √((L0 + L1‖∇f(x*)‖) R²/ε) + (1 + L1 R) · log(2 + (1 + L1 R) √(Δ/(L0 R²))) )

gradient and prox calls. In the composite setting ∇f(x*) ≠ 0 in general, so every known accelerated
analysis for (L0, L1)-smooth functions, all of which are unconstrained and use ∇f(x*) = 0, fails. With
constraints, the only available guarantees are unaccelerated, need ‖∇f(x*)‖ in the step size, or
depend on sup‖∇f‖ along the trajectory or on the feasible set. That supremum can be exponentially larger
than ‖∇f(x*)‖.

## Setup and proved guarantee

The [setup](../Setups/CompositeGeneralizedSmooth.lean) works in a real Hilbert space E of any dimension.

- **Smooth part.** f : E → ℝ is convex and has a continuous gradient on all of E. The gradient
  satisfies the symmetric (L0, L1) condition of Chen, Zhou, Liang and Lu
  ([ICML 2023](https://proceedings.mlr.press/v202/chen23ar.html), symmetric generalized smoothness),

    ‖∇f(x) − ∇f(y)‖ ≤ (L0 + L1 · max_{θ∈[0,1]} ‖∇f(x + θ(y − x))‖) · ‖x − y‖.

  The Lean statement uses the equivalent form without a maximum: if ‖∇f‖ ≤ M on the segment then the
  difference is at most (L0 + L1 M)‖x − y‖. This first-order form is implied by the Hessian form
  ‖∇²f(x)‖ ≤ L0 + L1‖∇f(x)‖ of Zhang, He, Sra and Jadbabaie
  ([ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS)), which is used in the closest
  unconstrained works. It does not require second derivatives. Continuity of ∇f is automatic for
  differentiable convex functions in finite dimension and is stated explicitly here. The condition is
  imposed on all of E, which excludes barrier-type f that blow up at the boundary of Q.
- **Nonsmooth part.** Q ⊆ E is convex and ψ : E → ℝ is convex on Q. Constraints are ψ ≡ 0;
  regularizers are Q = E. The setup does not require Q to be closed or ψ to be lower semicontinuous.
  Instead it requires the prox oracle below to return an exact minimizer, which is what those
  conditions are normally used to guarantee.
- **Oracles.** A gradient query x returns ∇f(x). A prox query (a, z, v) with a > 0 returns a point of Q
  minimizing ‖u − z‖²/(2a) + ⟨v, u − z⟩ + ψ(u) over u ∈ Q, as in Nesterov
  ([Math. Program. 140, 2013](https://doi.org/10.1007/s10107-012-0629-5), composite gradient mapping).
  Both replies are exact. Each query counts as one oracle call.
- **Solution data.** There is a minimizer x* ∈ Q of F = f + ψ on Q with ‖x0 − x*‖ ≤ R,
  F(x0) − F(x*) ≤ Δ and ‖∇f(x*)‖ ≤ G, all for the same x*; x0 ∈ Q. The parameters satisfy
  L0, R, Δ, ε > 0 and L1, G ≥ 0.
- **Information.** The algorithm is built from (E, L0, L1, R, Δ, x0) only. G and ε are fields of the
  parameters but not of the public input, so the Lean types guarantee that the method never uses
  them. ∇f is constant on the solution set of a convex composite problem, so G can be taken equal
  to ‖∇f(x*)‖.
- **Success.** The returned point lies in Q and satisfies F(x) − F(x*) ≤ ε.

**Algorithm.** The [method](../Algorithms/CompositeGeneralizedAccelerated.lean) is the similar-triangles
form of Nesterov's accelerated method with an observable step rule and a growth cap. It keeps
(A_k, x_k, z_k), starting from A_0 = R²/(2Δ) and x_0 = z_0 = x0. Iteration k makes three calls:

  M_k = L0 + L1‖∇f(x_k)‖                                   (gradient call 1)
  a_k = min{ (1 + √(1 + 16 M_k A_k))/(8 M_k), A_k/(1 + 32 L1 R) }
  y_k = (A_k x_k + a_k z_k)/(A_k + a_k)
  z_{k+1} = prox(a_k, z_k, ∇f(y_k))                          (gradient call 2, prox call 3)
  x_{k+1} = (A_k x_k + a_k z_{k+1})/(A_k + a_k),  A_{k+1} = A_k + a_k.

The first entry of the minimum is the root of 4 M_k a² = A_k + a. The output is x_k. There is no line
search, no function value, no restart and no phase switch.

**Guarantee.** With

  K = ⌈10 √((L0 + L1 G) R²/ε) + (6 + 128 L1 R) · log(2 + (3 + 96 L1 R) √(Δ/(L0 R²)))⌉,

the point x_K, returned after the public budget of 3K calls, lies in Q and satisfies
F(x_K) − F(x*) ≤ ε. The logarithm involves only public quantities. Its argument is the ratio between
the scale at which a gradient step is trusted, 1/L1, and the initial accuracy scale. G enters only the
leading term.

**Lean layout.**
- [CompositeGeneralizedLocal](../Proofs/CompositeGeneralizedLocal.lean): local Lipschitz and descent
  bounds on balls of radius 1/(2L1), the shifted cocoercivity inequality, first-order optimality on Q,
  and the prox three-point and distance inequalities.
- [CompositeGeneralizedStep](../Proofs/CompositeGeneralizedStep.lean): the step-weight facts, the
  one-step potential inequality, and the invariant step with the locality argument.
- [CompositeGeneralizedRun](../Proofs/CompositeGeneralizedRun.lean): the curvature bound, the growth of
  √A_k, the counting potential, the accuracy theorem, and the identification of the algorithm's
  execution with the analysed recursion (three calls per iteration).

## Mechanism

Write g* = ∇f(x*), M(x) = L0 + L1‖∇f(x)‖, and Φ_k = A_k(F(x_k) − F*) + ‖z_k − x*‖²/2.

1. **Shifted function.** h(x) = f(x) − f(x*) − ⟨g*, x − x*⟩ is convex, nonnegative, minimized on all of
   E at x*, and satisfies h ≤ F − F* on Q by first-order optimality. h has the same second-order
   behaviour as f, so it is (L0 + L1‖g*‖, L1)-smooth. This shift is known (see below). It is used only in
   the analysis, because the algorithm cannot form ∇h = ∇f − g*.
2. **Cocoercivity with the observed constant.** For every x,
   ‖∇f(x) − g*‖² ≤ 8 (M(x) + L1‖∇f(x) − g*‖) h(x).
   The constant is the observable M(x), not L0 + L1‖g*‖. This matters when ‖∇f(x_k)‖ is much smaller
   than ‖g*‖, where an estimate based on g* would allow steps that are too long.
3. **Locality without circularity.** The point z_{k+1} is controlled before the descent inequality of
   step k is used: the prox three-point inequality and item 1 give
   ‖z_{k+1} − x*‖ ≤ ‖z_k − x*‖ + 2a_k‖∇f(y_k) − g*‖. Item 2 with h(x_k) ≤ R²/A_k, the root condition
   4M_k a_k² ≤ A_{k+1} and the cap a_k ≤ A_k/(1 + 32 L1 R) bound the right-hand side by about 10R. Hence
   y_k and x_{k+1} stay within 1/(2L1) of x_k, where ∇f is 2M_k-Lipschitz. The one-step inequality of the
   similar-triangles method then gives Φ_{k+1} ≤ Φ_k ≤ R².
4. **Curvature along the run.** Item 2 also gives M_k ≤ 2(L0 + L1G) + 24 L1²R²/A_k. Consequently √A_k
   grows by 1/(4√(3(L0 + L1G))) per step once A_k ≥ 24 L1²R²/(L0 + L1G), and geometrically, by the
   factor 1 + 1/(3 + 96 L1 R), before that. The potential √A/δ + c·log min(√A, δ/ρ) increases by at
   least 3/4 per iteration, which yields K. Then F(x_K) − F* ≤ R²/A_K ≤ ε.

The cap in item 3 is what replaces a priori gradient bounds. It limits the relative step a_k/A_{k+1} to
1/(32 L1 R) so that every query stays in the trust region of an observed gradient. A larger initial gap
or a larger ‖g*‖ only lengthens the geometric phase logarithmically or enters the leading term.

## Relation to prior results

- **Unconstrained (L0, L1) acceleration.** Tyurin ([arXiv:2508.06884 v2](https://arxiv.org/abs/2508.06884),
  ICML 2026), Theorem 4.3, gives O(√L0 R/√ε + L1 R log(min{L1²R²Γ0/L0, Γ0R²/ε}) + log(Γ0/L0)) for
  unconstrained problems, with Γ0 ≥ 2(f(x0) − f*)/‖x0 − x*‖², the same information as Δ here. Vankov,
  Rodomanov, Nedich, Sankar and Stich ([ICLR 2025](https://arxiv.org/abs/2410.10800)) and Gorbunov et al.
  ([ICLR 2025](https://arxiv.org/abs/2409.14989)) are also unconstrained. Borodich and Kovalev
  ([arXiv:2507.09823](https://arxiv.org/abs/2507.09823), ICLR 2026), Corollary 3, give an adaptive
  gradient-only method with O(√(L0D²/ε) + (L1D)³ + …) for problem (1), min over ℝ^d. All of these
  analyses use ∇f(x*) = 0.
  **When ψ ≡ 0 and Q = E the present theorem is no improvement over Tyurin's**; it has the same
  leading term and an additive term of the same order.
- **Constrained (L0, L1) problems.**
  - Richtárik, Gruntkowska and Li ([arXiv:2605.08850 v2](https://arxiv.org/abs/2605.08850)), Prop. E.2
    and Thm D.12, analyse projected and broximal gradient descent with the constant
    c* = L0 + L1‖∇f(x*)‖. Their step size uses ‖∇f(x*)‖, their criterion is
    min_k ‖∇f(x_k) − ∇f(x*)‖, and the methods are unaccelerated. The constant L0 + L1‖∇f(x*)‖ is
    therefore not new.
  - Vyguzov and Stonyakin ([arXiv:2510.16468 v2](https://arxiv.org/abs/2510.16468)), Theorem 5.1:
    Frank–Wolfe on compact Q with rate 2eD²(L0 + L1 max_k‖∇f(x_k)‖)/(k + 3), unaccelerated and
    dependent on the largest gradient along the trajectory.
  - Vyguzov and Stonyakin ([arXiv:2609.00261](https://arxiv.org/abs/2609.00261)), Proposition 1, state
    the shift lemma of item 1. They then handle Q-constrained augmented-Lagrangian subproblems with a
    public bound on the gradient shift over Q.
  - Pethick et al. ([arXiv:2506.01913 v3](https://arxiv.org/abs/2506.01913)) give a constrained clipped
    conditional-gradient variant for nonconvex stationarity. Kovalev and Stonyakin
    ([arXiv:2607.26969 v2](https://arxiv.org/abs/2607.26969)) treat the unconstrained problem.
- **What a routine argument already gives.** (i) On the ball of radius R around x*, (L0, L1)-smoothness
  only gives a Lipschitz constant of order (L0 + L1‖g*‖)e^{L1 R}, so standard accelerated proximal
  methods (Nesterov 2013; Beck–Teboulle FISTA) pay e^{L1 R/2} in the leading term. (ii) With a public
  bound B ≥ ‖g*‖, applying an accelerated method to the shifted function of item 1 with constant
  L0 + L1 B is routine. From public data alone, however, B can only be bounded by
  (‖∇f(x0)‖ + L0/L1)e^{L1 R}. On compact Q one can use B = sup_Q‖∇f‖, which is exponential in L1 D on
  the family below. (iii) Backtracking with function values is outside this oracle model. Its known
  analyses bound the trial smoothness at y_k, which mixes in z_k at distance about R from x*, and so
  have no polynomial bound in this class.
- **Lower bound for the leading term.** Take Q = {x : x_1 ≥ 0} and f(x) = G x_1 + q(x_2, …, x_d), with q
  Nesterov's worst-case quadratic of curvature L0 + L1 G. Since ∂_1 f ≡ G, ‖∇f‖ ≥ G everywhere, so f is
  (L0, L1)-smooth and ‖∇f(x*)‖ = G. Projection acts only on x_1, so the standard span argument gives
  Ω(√((L0 + L1G)R²/ε)) calls in high dimension (d growing with the number of calls). The leading term is
  therefore optimal up to its constant. The example also shows that no bound in terms of
  (L0, L1, R, Δ, ε) alone holds for the composite class. It says nothing about the additive L1 R log
  term. This remark is not formalized.

**What is new.** The first accelerated objective-gap guarantee for composite or constrained
(L0, L1)-smooth convex problems whose algorithm uses neither ∇f(x*) nor a bound on it, with leading
term √((L0 + L1‖∇f(x*)‖)R²/ε). The new ingredients are the observed-constant cocoercivity inequality
(item 2), the non-circular locality argument (item 3) and the cap-based counting (item 4). The
similar-triangles template, the shift lemma and the constant L0 + L1‖∇f(x*)‖ are known.

## Example: ℓ1- or ball-constrained exponential-loss boosting

Let f(x) = Σ_i w_i exp(⟨a_i, x⟩) with w_i > 0, and assume a unit vector u and c ∈ (0, 1] with
⟨a_i, u⟩ ≥ c‖a_i‖ for all i. This is the exponential loss of a separable dataset (a_i = −y_i ξ_i) with
normalized margin c along −u. With α = max_i‖a_i‖,

  ‖∇²f(x)‖ ≤ Σ w_i e^{⟨a_i,x⟩}‖a_i‖² ≤ α Σ w_i e^{⟨a_i,x⟩}‖a_i‖ ≤ (α/c)⟨∇f(x), u⟩ ≤ (α/c)‖∇f(x)‖,

so f is (L0, α/c)-smooth for every L0 > 0 (Hessian form, hence the first-order form). The coordinates
interact through the a_i. The unconstrained infimum is not attained, so a constraint or regularizer is
essential and ∇f(x*) ≠ 0. Take Q the Euclidean ball of radius τ around x0 = 0, so D = 2τ, and suppose
‖a_i‖ ∈ [α/κ, α]. Then sup_Q‖∇f‖ ≥ ⟨∇f(τu), u⟩ ≥ (cα/κ)e^{cατ/κ}Σw_i, while
‖∇f(x*)‖ ≤ α f(x*) ≤ α f(−τu) ≤ α e^{−cατ/κ}Σw_i. Hence

  sup_Q‖∇f‖ / ‖∇f(x*)‖ ≥ (c/κ) e^{c² L1 D/κ},  L1 = α/c.

On this family the leading term here uses L0 + L1‖∇f(x*)‖, whereas the sup-gradient reduction uses
L0 + L1 sup_Q‖∇f‖, larger by a factor exponential in L1 D for fixed margin. An ℓ1 ball, the setting of
ℓ1-regularized boosting paths (Rosset, Zhu and Hastie, JMLR 2004), behaves the same way along u.

## Scope and limitations

- **Improvement regime.** The gain is for composite or constrained problems with L1 > 0, where ‖∇f(x*)‖
  is unknown or much smaller than the available a priori bounds. Nothing is gained when ψ ≡ 0 and
  Q = E.
- **Additive term.** (1 + L1 R)·log(…) matches the order of Tyurin's unconstrained additive term. Whether
  an L1 R-type term is necessary at all is open, as it is in the unconstrained case, where Tyurin's
  conclusion names it as an open question. A sharper non-dominant term is known only in other
  formulations, for example the (L1 R)^{2/3} terms of ball-oracle-type methods.
- **Public Δ.** Δ ≥ F(x0) − F* sets A_0 and appears only inside the logarithm. It is the same
  information as Tyurin's Γ0. For pure constraints, Δ = ‖∇f(x0)‖R is computable by convexity. For a
  general ψ, a start without Δ would need a bound on ‖∇f(x0) − ∇f(x*)‖, which this class only provides
  with an exponential factor.
- **Known L0, L1, R.** The step uses L0, L1 and R; G and ε are not used.
- **Exact oracles, deterministic.** No inexact prox, no stochastic gradients.
- **Constants.** They are not optimized. With L1 = 0 the leading constant is about 10, against roughly 2
  for the textbook similar-triangles bound, and each iteration spends one extra gradient call at x_k.
- **Witness properties.** The theorem is an oracle-complexity statement for the class. That the
  witness is a single run returning its last point describes the proof, not a separately claimed
  property.
- **Literature search.** Searches on arXiv, OpenReview and the proceedings of ICML 2025–2026,
  ICLR 2025–2026 and NeurIPS 2024–2025 (dated 2026-10-03) found no accelerated composite or constrained
  (L0, L1) guarantee free of exponential factors, sup-gradient bounds or knowledge of ∇f(x*). Full texts
  of ICML 2026 papers were not all available.
- **Computer assistance.** The potential and locality inequalities were checked numerically before
  formalization. Every step is proved in Lean without `sorry` or extra axioms.
