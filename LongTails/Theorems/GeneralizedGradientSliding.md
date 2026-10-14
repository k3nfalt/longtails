# Gradient sliding under (L0, L1)-smoothness

This note explains the contribution formalized in
[GeneralizedGradientSliding.lean](GeneralizedGradientSliding.lean), with the
[setup](../Setups/SlidingGeneralizedSmooth.lean) and the
[algorithm](../Algorithms/GeneralizedGradientSliding.lean).

The theorem extends Lan's gradient sliding to composite problems min_{x∈Q} f(x) + h(x) in which the
smooth part f is only (L0, L1)-smooth and the nonsmooth part h is accessible only through
subgradients. Gradients of f and subgradients of h are counted separately. The method needs

  O( √((L0 + L1‖∇f(x*)‖) R²/ε) + (1 + L1 R) · log(2 + (1 + L1 R) √(Δ/(L0 R²))) )   gradients of f,
  O( M²R²/ε² + the same term )                                                     subgradients of h and projections onto Q (active phase),

to reach F(x) − F* ≤ ε, where M bounds the subgradients of h. Every constant is polynomial in L1R.
With L1 = 0 these are the orders of Lan's gradient sliding for an L0-smooth f. The gain is not a
better rate for globally smooth problems; it is that the guarantee holds, with polynomial constants,
for a class on which every previously available sliding-type bound is either inapplicable or
exponential in L1R in the worst case (see the comparison below).

## Setup and proved guarantee

The [setup](../Setups/SlidingGeneralizedSmooth.lean) works in a real Hilbert space E of any dimension.

- **Smooth part.** f : E → ℝ is convex with a continuous gradient on all of E satisfying the symmetric
  (L0, L1) condition of Chen, Zhou, Liang and Lu
  ([ICML 2023](https://proceedings.mlr.press/v202/chen23ar.html)): if ‖∇f‖ ≤ B on the segment [x, y]
  then ‖∇f(x) − ∇f(y)‖ ≤ (L0 + L1 B)‖x − y‖. It is implied by the Hessian condition
  ‖∇²f(x)‖ ≤ L0 + L1‖∇f(x)‖ of Zhang, He, Sra and Jadbabaie
  ([ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS)). This is the same first-order form as in
  the repository setup [CompositeGeneralizedSmooth](../Setups/CompositeGeneralizedSmooth.lean).
- **Nonsmooth part.** h : E → ℝ is accessed only through a subgradient oracle: for every query
  u ∈ Q and every call, the reply s satisfies ‖s‖ ≤ M and h(v) ≥ h(u) + ⟨s, v − u⟩ for all v ∈ Q.
  The selection is adversarial and may change from call to call. This makes h convex and
  M-Lipschitz on Q, as in Lan's setting. No proximal operator of h is available.
- **Constraint.** Q ⊆ E is convex and accessed through an exact projection oracle (a nearest point of
  Q). Q is part of the unknown instance, so projections are oracle calls and are counted.
- **Solution data.** There is a minimizer x* ∈ Q of F = f + h on Q with ‖x0 − x*‖ ≤ R,
  F(x0) − F(x*) ≤ Δ and ‖∇f(x*)‖ ≤ G; x0 ∈ Q; L0, R, Δ, ε > 0 and L1, M, G ≥ 0.
- **Information.** The public input is (E, L0, L1, M, R, Δ, G, ε, x0). The updates use L0, L1, M,
  R, Δ, ε and x0. G is used only to stop issuing gradient queries after the certified number
  2K; on admissible instances the method reaches its target before that point, so G never changes
  the computed iterate. ε is used, as N is in Lan's method, to size the inner loops.
- **Cost model.** Oracle numbers 0, 1 and 2 select the gradient of f, a subgradient of h and
  projection onto Q, respectively. The public budget is the tuple (2K, N, N), represented in
  Lean by `Fin 3 → ℕ`, where K is defined below and N = 8K + ⌈768 M²R²/ε²⌉.
  `Convergence` checks each bound against the corresponding count returned by execution.
- **Success.** The returned point lies in Q and satisfies F(x) − F(x*) ≤ ε.

**Algorithm.** The [method](../Algorithms/GeneralizedGradientSliding.lean) keeps (A_k, x_k, z_k),
starting from A_0 = R²/(4Δ) and x_0 = z_0 = x0. While A_k < R²/ε (and fewer than K outer steps were
made), an outer step does:

  M_k = L0 + L1‖∇f(x_k)‖                                        (gradient call 1)
  a_k = min{ (1 + √(1 + 64 M_k A_k))/(32 M_k), A_k/(1 + 80 L1 R) }
  y_k = (A_k x_k + a_k z_k)/(A_k + a_k),  g_k = ∇f(y_k)           (gradient call 2)
  T_k = ⌈192 M² a_k/ε⌉ + 2,  W = T_k(T_k + 3)/2,  β = W/(a_k(W + 1)),  u_0 = ũ_0 = z_k,
  for t = 0, …, T_k − 1 (prox-sliding, two calls each):
      s_t = h′(u_t)                                                   (subgradient call)
      u_{t+1} = Π_Q( (z_k + ((t+1)/2) u_t − (g_k + s_t)/β) / (1 + (t+1)/2) )   (projection call)
      ũ_{t+1} = (W_t ũ_t + (t + 2) u_{t+1}) / W_{t+1},   W_t = t(t + 3)/2
  x_{k+1} = (A_k x_k + a_k ũ_{T_k})/(A_k + a_k),  z_{k+1} = u_{T_k},  A_{k+1} = A_k + a_k.

The first entry of the minimum is the root of 16 M_k a² = A_k + a. The inner loop is Lan's PS
procedure with p_t = t/2 and weights proportional to t + 1. Once A_k ≥ R²/ε the method idles and
returns x_k.

**Guarantee.** With

  K = ⌈20 √((L0 + L1 G) R²/ε) + (6 + 320 L1 R) · log(2 + (3 + 240 L1 R) √(Δ/(L0 R²)))⌉,

the theorem certifies the budget tuple (2K, N, N), where N = 8K + ⌈768 M²R²/ε²⌉:
at most 2K gradient calls, N subgradient calls and N projection calls.
The proof chooses an execution of N total calls whose output lies in Q and satisfies
F(x) − F(x*) ≤ ε. The component bounds are upper limits, not numbers of calls that must all be used.
The proof also shows (in the cost invariant of
[SlidingConvergence](../Proofs/SlidingConvergence.lean)) that the active phase, before the method
reaches A_k ≥ R²/ε, makes at most 3K + 384 M²R²/ε² subgradient calls and as many projection calls;
the remaining calls of this N-call execution are idle padding queries (projections of the current point),
which do not change the output.

**Lean layout.**
- [SlidingInner](../Proofs/SlidingInner.lean): projection variational inequality, one inner step,
  the weighted telescoping of the inner loop, and the inexact three-point inequality
  a(⟨g, ũ − u⟩ + h(ũ) − h(u)) + ‖ũ − z‖²/3 + ‖u_T − u‖²/2 ≤ ‖z − u‖²/2 + 24 M² a²/(T + 3).
- [SlidingStep](../Proofs/SlidingStep.lean): the step-weight facts, the similar-triangles step with an
  inexact prox point, and the locality argument.
- [SlidingRun](../Proofs/SlidingRun.lean): the curvature bound, the growth of √A_k and the
  iteration count.
- [SlidingExecution](../Proofs/SlidingExecution.lean): the state machine against the analysed
  recursion, including adversarial per-call replies, and the gradient-call certificate.
- [SlidingConvergence](../Proofs/SlidingConvergence.lean): the outer invariant, the cost bound and
  the final statement.

## Mechanism

Write g* = ∇f(x*), F* = F(x*) and Φ_k = A_k(F(x_k) − F*) + ‖z_k − x*‖²/2.

1. **Inexact three-point inequality.** The inner loop solves the prox-linear subproblem
   min_u a⟨g, u⟩ + a h(u) + ‖u − z‖²/2 only approximately, using T subgradients. Its averaged point ũ
   and last point u_T satisfy the inequality above. The coefficient of ‖u_T − u‖² on the left equals
   that of ‖z − u‖² on the right, so the error enters the outer potential additively.
2. **Locality of the approximate prox point.** For (L0, L1) functions the descent inequality is only
   valid inside a ball of radius about 1/L1 around the observed point. With u = x* and the
   optimality condition −g* ∈ ∂h(x*) + N_Q(x*), the inexact inequality gives
   ‖ũ − z‖² ≤ 3(‖z − x*‖²/2 + error) + 3a‖∇f(y) − g*‖‖ũ − x*‖. The repository's shifted-cocoercivity
   bound ‖∇f(x) − g*‖² ≤ 8(L0 + L1‖∇f(x)‖ + L1‖∇f(x) − g*‖)(f(x) − f(x*) − ⟨g*, x − x*⟩) and the root
   rule bound a‖∇f(y) − g*‖ by 5R. Hence ‖ũ − x*‖ ≤ 19R, the iterates satisfy ‖x_k − x*‖ ≤ 20R, and
   the cap a_k ≤ A_k/(1 + 80 L1 R) keeps y_k and x_{k+1} within 1/(2L1) of x_k. The stronger root
   rule 16 M a² ≤ A + a (instead of 4 M a²) is what makes this distance bound close: it limits
   a‖∇f(y) − ∇f(x)‖ to ‖z − x‖/8.
3. **Error budget with adaptive weights.** Because a_k is chosen from observed gradients, the number
   of outer steps is not known in advance. Choosing T_k ≥ 192 M² a_k/ε makes the inner error at
   most a_k ε/8, so the errors sum to at most (A_k − A_0)ε/8 ≤ R²/4 while A_k < 2R²/ε. This keeps
   Φ_k ≤ R² throughout, and the total number of inner steps is at most 3K + 384 M² R²/ε².
4. **Growth.** As in the exact composite case, the curvature estimate satisfies
   M_k ≤ 2(L0 + L1G) + 24 L1²R²/A_k, so √A_k grows by 1/(8√(3(L0 + L1G))) per step after a
   geometric phase of length O((1 + L1R) log(…)). After K steps A_K ≥ R²/ε, and then
   F(x_K) − F* ≤ Φ_K/A_K ≤ ε.

## Relation to prior results

- **Gradient sliding with a globally smooth f.** Lan,
  [*Gradient sliding for composite optimization*](https://arxiv.org/abs/1406.0919), Math. Program.
  159 (2016), Corollaries 1–2: O(√(L V(x0, x*)/ε)) gradients and O(M² V(x0, x*)/ε² + √(L V/ε))
  subgradients, for f with a globally L-Lipschitz gradient. The analysis uses L in the step sizes and
  in every descent inequality. For an (L0, L1)-smooth f, such as cosh(L1⟨c, x⟩)/L1², there is no
  global L. Restricting to the ball B(x0, 2R) gives L ≤ (L0 + L1‖∇f(x0)‖)·exp(O(L1R)), which is tight
  for cosh, and costs √(e^{L1R} R²/ε) gradients (and a projection onto Q ∩ ball).
- **Parameter-free and adaptive sliding.** Wu, Ouyang, Zhang and Luo,
  [arXiv:2603.23492 v2](https://arxiv.org/abs/2603.23492) (PFUGS), handle unknown constants by
  backtracking, but assume a globally L-Lipschitz gradient for the smooth part (their condition (1.3)
  in the PDF of v2, displayed as (3) in the HTML rendering, stated "for all x, y"). Takahashi, [arXiv:2601.20443 v2](https://arxiv.org/abs/2601.20443) (adaptive
  conditional gradient sliding), needs only local smoothness on a compact set, but its bound uses the
  largest local Lipschitz estimate along the iterates; its only a-priori bound is the smoothness
  constant on the iterate set, which for (L0, L1) functions can be exponential in L1 times the
  diameter. It also uses a linear minimization oracle, not a subgradient oracle for a nonsmooth h.
- **(L0, L1) acceleration.** Tyurin ([arXiv:2508.06884 v2](https://arxiv.org/abs/2508.06884),
  Theorem 4.3), Vankov et al. ([ICLR 2025](https://arxiv.org/abs/2410.10800)), Gorbunov et al.
  ([ICLR 2025](https://arxiv.org/abs/2409.14989)) and Borodich–Kovalev
  ([arXiv:2507.09823](https://arxiv.org/abs/2507.09823)) treat unconstrained smooth problems. The
  repository result [CompositeGeneralizedAccelerated](CompositeGeneralizedAccelerated.md) treats
  f + ψ with an exact proximal oracle of ψ. None of these applies when h is only available through
  subgradients.
- **Subgradient methods on F = f + h.** They need a bound on ‖∇f‖ along the trajectory (again
  exponential in L1R in the worst case) and use O(ε^{-2}) gradients of f.
- **Sublevel-set reduction.** On {F − F* ≤ cΔ} the local smoothness constant of f is polynomial,
  about L0 + L1G + L1²Δ + L1√((L0 + L1G)Δ). This does not give the present result: the query points
  of gradient sliding mix in the prox sequence, which is controlled only in distance, not in function
  value; on the cosh family these points leave every polynomial sublevel set. Even if the reduction
  applied, it would put L1²ΔR²/ε inside the leading square root, whereas here Δ appears only inside
  a logarithm.

**What is new.** To our knowledge this is the first gradient-sliding guarantee under generalized
smoothness: separate O(√((L0 + L1G)R²/ε)) gradient and O(M²R²/ε²) subgradient counts with constants
polynomial in L1R, and the method never uses ‖∇f(x*)‖ in its iterates. The technical point is that
the locality argument required by (L0, L1)-smoothness must be carried out for an approximate prox
point whose error is controlled only in the aggregate, with outer weights chosen online.

**Example.** E = ℝ^d, f(x) = cosh(L1⟨c, x⟩)/L1² + (μ/2)‖x‖² with ‖c‖ = 1 is convex and symmetric
(1 + μ, L1)-smooth (‖∇²f‖ ≤ cosh(L1⟨c, x⟩) + μ and ‖∇f(x)‖ ≥ |sinh(L1⟨c, x⟩)|/L1), but not globally
smooth. With h(x) = λ‖Dx‖₁ for a graph incidence matrix D (graph total variation, whose prox has no
closed form on general graphs) and Q = ℝ^d, M = λ max‖Dᵀv‖ over ‖v‖_∞ ≤ 1 and ‖∇f(x*)‖ ≤ M, while
sup over B(x*, R) of ‖∇f‖ is at least sinh(L1R)/L1.

## Limitations

- The improvement is worst case over the class: polynomial instead of exponential dependence on
  L1R. For globally smooth f there is no rate improvement over Lan's method, and the constants here
  are larger.
- The method needs ε (to size the inner loops, as Lan's needs N) and the problem constants L0, L1, M,
  R, Δ; it is not parameter-free. G is public only for the gradient-call certificate.
- Subgradients of h are exact. Stochastic subgradients (Lan's stochastic gradient sliding) are not
  covered: the outer step-size rule uses pathwise potential bounds that would require a
  high-probability analysis.
- The leading constants (20 and 768) are not optimized. No lower bound is proved for the class.
- The literature search covered 2024–2026 venues and arXiv up to October 2026 for sliding under
  generalized or local smoothness; no prior result was found, but very recent preprints are poorly
  indexed.
