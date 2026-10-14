# Accelerated convex minimization under relative gradient error, without logarithms

This note explains the contribution formalized in
[AcceleratedRelativeErrorConvex.lean](AcceleratedRelativeErrorConvex.lean), with
[setup](../Setups/RelativeErrorSmoothConvex.lean),
[algorithm](../Algorithms/DampedAccelerated.lean) and
[proofs](../Proofs/DampedAccelerated.lean).

**Summary.** For a convex L-smooth objective and a gradient oracle whose error is at most α‖∇f(x)‖, 0 ≤ α < 1,
a single run of a Nesterov-type method with a damped mirror step satisfies

  f(x_N) − f* ≤ (2e·LR²/(1−α)) · (8/N² + 2α²/N),  R ≥ ‖x₀ − x*‖,

so accuracy ε is reached in N = ⌈7√(LR²/((1−α)ε)) + 11α²LR²/((1−α)ε)⌉ oracle calls. Published bounds for this
class and oracle are of order max{√(LR²/ε), α·LR²/ε}·log(LR²/ε) for α ≤ 1/3, or (LR²/ε)·log(LR²/ε) for
α < 1/2, or stop at the plateau α²LR². The new bound has no logarithm, holds for every α < 1, keeps the
accelerated rate up to α ≈ (ε/LR²)^{1/4}, and has α² in place of α beyond that. In particular, for LR²/ε ≤ α⁻⁴ the
budget is O(√(LR²/((1−α)ε))), which matches the lower bound for exact gradients up to the constant and the
factor (1−α)^{−1/2}; the previously published range for this was α ≲ (ε/LR²)^{1/2}. On explicit instances the
method attains the rate α²LR²/N numerically; no lower bound for the method is proved. The term α²LR²/ε is not
a barrier for the problem class: a two-level scheme has α⁴ in its place, at the price of a logarithm and
large constants; see "Tightness".

## Setup and proved guarantee

- **Space.** E is a real Hilbert space of any dimension; nothing depends on the dimension.
- **Objective.** f : E → ℝ is differentiable and, for all x, y,

    0 ≤ f(y) − f(x) − ⟨∇f(x), y − x⟩ ≤ (L/2)‖y − x‖².

  This is the class of convex functions with L-Lipschitz gradient. A minimizer x* with ‖x₀ − x*‖ ≤ R exists.
  No strong convexity, growth condition or bounded level set is assumed.
- **Oracle.** The k-th call at a point x returns any vector g with ‖g − ∇f(x)‖ ≤ α‖∇f(x)‖. The reply may
  depend on the call index and on an oracle seed in an arbitrary way; it need not be a function of x and
  need not be a gradient field. Since the method is deterministic, an adversary that adapts to the past is
  covered. This is the relative-error model of Polyak (1987): condition (10) of [VG26], Assumption 4 of
  [KAG+25], condition (1) of [HL24].
- **Cost and success.** Cost is the number of oracle calls. Success means f(x_N) − f(x*) ≤ ε for every
  oracle seed.
- **Information.** The algorithm receives L, α, x₀, R and ε. It uses R and ε only through the horizon N.
- **Validity.** L > 0, 0 ≤ α < 1, R ≥ 0, ε > 0.

**Algorithm.** Put N = ⌈7√(LR²/((1−α)ε)) + 11α²LR²/((1−α)ε)⌉ and q = (1−α)/(8 + 2α²N). With x₀ = z₀, for
k = 0, …, N−1:

  y_k = (k·x_k + 2·z_k)/(k+2),  g_k = oracle(y_k),
  x_{k+1} = y_k − g_k/L,  z_{k+1} = z_k − (q(k+1)/(2L))·g_k.

The output is x_N. There is one oracle call per iteration, no restart, no regularization and no line
search. For q = 1 this is the usual linear-coupling form of Nesterov's method; the only change is the
factor q in the step of the z-sequence. Damping this step is not a new idea ([KAG+25, Alg. 1] divides it by
a parameter a ≥ 1); the contribution is the analysis, the resulting choice of q, and the rate.

**Guarantee.** With A_k = qk(k+1)/(4L) and Φ_k = A_k(f(x_k) − f*) + ½‖z_k − x*‖², every admissible reply gives

  Φ_{k+1} ≤ (1 + 2qα²/(1−α))·Φ_k   whenever 0 < q ≤ (1−α)/8,

hence Φ_N ≤ e·R²/2 for the q above, which is the displayed bound. The Lean theorem `result` states that the
budget N gives f(x_N) − f(x*) ≤ ε for every oracle seed, using exactly N calls. The rate statement for a
general horizon is the lemma `advance_potential` together with `damping_bounds`.

## Relation to prior results

All rows concern the same class, oracle and criterion.

| Source | Bound | Restrictions |
|---|---|---|
| [KAG+25, Thm 3.1] (ISTM, p = 2) | f(y_N) − f* = O(LR²·max{1/N², √α/N^{3/2}, α/N, α²}) | plateau α²LR²: accuracy ε needs α ≲ (ε/LR²)^{1/2}; parameter depends on N |
| [VG26, Thm 7.1] (regularized GD) | N ≤ 12(1+α)²(1−α)⁻⁶ (LR²/ε) ln(2LR²/ε) + 1 | α < 1/2; uses R and ε |
| [VG26, Thm 7.2, 9.3] (regularized RE-AGM) | N = O((LR²/ε)^{1−β} ln(LR²/ε)) for α ≤ (1/3)(ε/12LR²)^β, β ≤ 1/2, i.e. max{√(LR²/ε), α·LR²/ε}·log | α ≤ 1/3; uses R and ε |
| descent lemma for GD | O(L·R̃²/((1−α)N)), R̃ = radius of the initial sublevel set | R̃/R is unbounded: f = (L/2)x₁² + (μ/2)x₂², x₀ = e₁ gives R̃/R = √(L/μ) |
| regularization + [AcceleratedInexactStronglyConvex](AcceleratedInexactStronglyConvex.md) (this repository; not carried out) | (√κ + α²κ/(1−α))·log(LR²/ε), κ ≈ LR²/ε | needs a bound ‖y_k − x₀‖ ≤ cR, which is not available; α below about 1/(12c); uses R and ε |
| **this note** | ⌈7√(LR²/((1−α)ε)) + 11α²LR²/((1−α)ε)⌉ | every α < 1; uses R and ε through N |

- **[KAG+25]** Kornilov, Alkousa, Gorbunov, Stonyakin, Dvurechensky, Gasnikov, *Intermediate gradient
  methods with relative inexactness*, [arXiv:2310.00506](https://arxiv.org/abs/2310.00506) v1 (read in
  full); published in J. Optim. Theory Appl. 207 (2025), whose text neither the author nor the reviewer of this
  note could access. Their method is the
  similar-triangles scheme with the z-step divided by a = O(max{1, N^{1/2}√α, Nα, N²α²}). It has no gradient
  step, so there is no descent term to absorb the error; the error term is bounded by induction on
  ‖z_k − x*‖ ≤ √2·R, which produces the terms √α/N^{3/2}, α/N and the plateau.
- **[VG26]** Vasin, Gasnikov, [arXiv:2603.12376](https://arxiv.org/abs/2603.12376) v1 (preprint, read in
  full). Their convex results are obtained by regularization from the strongly convex case, which is the
  source of the logarithm; Remark 10.2 notes that the upper bound for α < 1/2 "differs by the log factor"
  from their lower-bound statement. Earlier strongly convex results: Vasin et al.
  [arXiv:2503.06628](https://arxiv.org/abs/2503.06628) (complexity of order ακ) and
  [arXiv:2102.02921](https://arxiv.org/abs/2102.02921) (Section 5, α = O(μ/L)).
- **The repository's strongly convex theorem.** Its rate √κ + α²κ already shows the α² dependence. For a
  convex f it cannot simply be applied to f + (μ/2)‖x − x₀‖²: the error is relative to ∇f, not to the
  gradient of the regularized function, so it turns into an additional absolute error αμ‖y_k − x₀‖ that
  depends on the trajectory. If a bound ‖y_k − x₀‖ ≤ cR were proved, the validity condition of that theorem
  would restrict α to a small constant and the result would carry the factor log(LR²/ε). So, relative to
  that theorem, what is new here is: no logarithm, every α < 1, no trajectory bound, and a single run on f
  itself. Relative to the published literature the α² dependence in the convex case is new as well.
- **[HL24]** Hallak, Levy, *A study of first-order methods with a deterministic relative-error gradient
  oracle*, [ICML 2024](https://proceedings.mlr.press/v235/hallak24a.html): projected and conditional
  gradient methods for constrained problems, unaccelerated; the conclusion lists acceleration with this
  oracle as a direction for future work. The present theorem is unconstrained, so it does not address their
  constrained setting.
- **Exact worst-case analyses of inexact gradient descent** (de Klerk, Glineur, Taylor; Vernimmen, Glineur,
  [arXiv:2506.17145](https://arxiv.org/abs/2506.17145)) treat gradient descent, with strong convexity or
  with the gradient-norm criterion measured from f(x₀) − f*; they do not give a bound on f(x_N) − f* in terms
  of ‖x₀ − x*‖ for convex f.

We found no bound for this class and oracle that is free of logarithms and stated in R, and no bound with
α² dependence (searches of 2026-10-03; OpenReview and the NeurIPS 2026 list were not accessible).

## Mechanism

Let G = ‖∇f(y_k)‖, e = g_k − ∇f(y_k), D = ‖z_k − x*‖, a = q(k+1)/(2L), A' = A_{k+1}.

1. With step 1/L the gradient step gives f(x_{k+1}) ≤ f(y_k) − (G² − ‖e‖²)/(2L); the cross term ⟨∇f, e⟩
   cancels exactly.
2. Convexity at y_k (towards x_k and towards x*) and A'·y_k = A_k·x_k + a·z_k give
   A'(f(y_k) − f*) − A_k(f(x_k) − f*) ≤ a⟨∇f(y_k), z_k − x*⟩.
3. The z-step gives ½‖z_{k+1} − x*‖² = ½D² − a⟨g_k, z_k − x*⟩ + (a²/2)‖g_k‖², and ‖g_k‖² ≤ 2G² + 2‖e‖².
4. Adding these, using a²L ≤ qA' and q ≤ (1−α)/8:  Φ_{k+1} − Φ_k ≤ aαGD − A'(1−α)G²/(4L).
5. The remaining term is linear in the error and involves the distance to the solution. It is split
   against the descent slack: aαGD ≤ A'(1−α)G²/(4L) + (qα²/(1−α))·D², and D² ≤ 2Φ_k.

There is no strong convexity to pay for the term in step 5 (the mechanism of the repository's strongly
convex theorem), and the iterates are not Fejér monotone: ‖z_k − x*‖ can grow. The analysis lets the
potential grow by the factor 1 + 2qα²/(1−α) per step and chooses q so that the total growth over the
horizon is at most e. This fixes q ≈ 1/(α²N) when α²N ≫ 1, and then A_N ≈ N/(α²L).

The same computation explains two facts.

- *Horizon dependence.* For step-dependent damping q_k the analysis needs Σ q_k ≲ 1/α², while A_N grows
  like (Σ √q_k)²/L. A constant q ≈ 1/(α²N) is the best choice; a horizon-free schedule loses at least a
  logarithm in this analysis. Gradient descent corresponds to q_k ≈ 1/k and loses a factor N^{cα²}.
- *Why damping.* In the oscillator picture of Nesterov's method the mode of curvature λ is damped at rate
  about 1/k + λ/L per step, while an error of relative size α can pump it at rate about α√(λ/L). The modes
  with λ ≈ α²L are therefore amplified once k ≫ 1/α², unless the momentum is reduced.

## Tightness

**What is established.** The following are numerical observations on explicit instances, not theorems.
Take f(x) = (λ/2)‖x‖² on ℝ² and the admissible linear oracle g(y) = λ(I + αJ)y, J the rotation by 90°, and
maximize f(x_N) over λ ∈ [10⁻¹⁰L, L].

| | N = 10² | 10³ | 10⁴ | 10⁵ |
|---|---|---|---|---|
| undamped (q = 1), α = 0.1: f(x_N)·N²/(LR²) | 0.67 | 0.68 | 4.7·10⁷ | 1.8·10¹⁰⁴ |
| undamped (q = 1), α = 0.3 | 0.67 | 1.0·10⁷ | 1.4·10⁹³ | overflow |
| damped, α = 0.1: f(x_N)·N/(α²LR²) | 6.1 | 2.0 | 1.5 | 1.4 |
| damped, α = 0.3 | 1.6 | 1.3 | 1.3 | 1.3 |
| damped, α = 0.6 | 0.68 | 0.68 | 0.68 | 0.68 |

So Nesterov's method without damping is not merely slowed down: it diverges on admissible instances once
N ≫ 1/α². The damped method attains about 1.3·α²LR²/N on these instances, against the proved bound of about
11·α²LR²/((1−α)N). This is numerical evidence that the analysis of the method cannot be improved in order; a
lower bound for the method is not proved.

**The term α²LR²/ε is not a barrier for the problem class.** The following statement is proved here on
paper; it is not formalized and is not part of the Lean theorem. Write T = LR²/ε.

*Proposition (two-level scheme).* Let 0 < α ≤ 1/27 and T ≥ 1. There is a deterministic method, using only the
oracle above and the parameters L, α, R and ε, that reaches f(x) − f* ≤ ε with
O((1/α² + √T + α⁴T)·log(2 + T/α²)) calls. (For T ≤ 1/2 the starting point already satisfies the target.) The
proof below is a hand proof, checked by hand by the independent reviewer of this note; it is not
machine-checked.

*Method.* Fix η > 0, integers K, m ≥ 1 and q = 1/(6 + 3σ²K) with σ² = 170α². Outer loop, for k < K, with
x₀ = z₀:

  y_k = (k·x_k + 2·z_k)/(k+2),  x_{k+1} = Inner(y_k),  z_{k+1} = z_k − (q(k+1)/2)·(y_k − x_{k+1}).

Inner(y) runs m steps of the method of [AcceleratedInexactStronglyConvex](AcceleratedInexactStronglyConvex.md)
on h(x) = f(x) + ‖x − y‖²/(2η), started at y, with constants L_h = L + 1/η, μ_h = 1/η, relative parameter 2α,
feeding it the vector oracle(x) + (x − y)/η, and returns its primal iterate. The cost is K·m calls.

*Proof.* Let p be the minimizer of h, so that ∇f(p) = (y − p)/η =: G.

1. *Inner oracle.* The error of oracle(x) + (x − y)/η as a gradient of h is at most α‖∇f(x)‖, and
   ‖∇f(x)‖ ≤ ‖∇h(x)‖ + ‖x − y‖/η ≤ 2‖∇h(x)‖ + ‖p − y‖/η, because ‖x − p‖ ≤ η‖∇h(x)‖. So the inner oracle has
   relative error 2α and absolute error δ = α‖p − y‖/η, a constant of the subproblem.
2. *Inner accuracy.* The potential inequality of that theorem (Lean lemmas `advance_potential` and `floor_le`
   in `Proofs/InexactAcceleratedConvergence.lean`, the latter with the fifth conjunct of `momentum_bounds`)
   gives, with θ its momentum parameter,
   h(x⁺) − h(p) ≤ (1 − θ/2)^m·(L_h/2 + 1/(4η))‖y − p‖² + 68δ²η/(1 − 2α)².
   For m ≥ (2/θ)·ln((ηL + 3/2)/(10α²)) this is at most (σ²/(2η))‖p − y‖² with σ² = 170α² ≤ 1/4.
3. *Outer step.* Put v = (y − x⁺)/η. Strong convexity of h gives ‖x⁺ − p‖² ≤ σ²‖p − y‖², hence
   ‖v − G‖ ≤ σ‖G‖, and f(x⁺) ≤ h(x⁺) ≤ f(p) + (1 + σ²)η‖G‖²/2. With A_k = qηk(k+1)/4, a = qη(k+1)/2 and
   Φ_k = A_k(f(x_k) − f*) + ½‖z_k − x*‖², convexity at p and A_{k+1}y_k = A_k x_k + a z_k give
   A_{k+1}(f(p) − f*) − A_k(f(x_k) − f*) ≤ −A_{k+1}η‖G‖² + a⟨G, z_k − x*⟩, and therefore
   Φ_{k+1} − Φ_k ≤ −A_{k+1}η‖G‖²·((1 − σ²)/2 − q(1 + σ)²/2) + aσ‖G‖·‖z_k − x*‖ ≤ (8/3)qσ²·Φ_k,
   by the same split as in step 5 of the mechanism (the bracket is at least 3/16 for σ ≤ 1/2, q ≤ 1/6).
4. *Count.* Φ_K ≤ e·R²/2, so f(x_K) − f* ≤ 2e(6 + 3σ²K)R²/(ηK²). Take K = ⌈1/(170α²)⌉, so σ²K ≤ 2, and
   η = 24eR²/(εK²); then ηL ≤ 24e·170²·α⁴T and K·√(ηL) ≤ √(24eT). The inner theorem has
   2/θ = 8√((ηL+1)/(1−2α)) + 128α²(ηL+1)/(1−2α), so K·m = O((1/α² + √T + α⁴T)·log(2 + T/α²)). ∎

Consequences and caveats.

- For T^{−1/4} ≪ α ≪ T^{−1/8} the proposition gives Õ(√T) calls, whereas [VG26, Thm 10.2, part 1] asserts,
  as we read it, that no first-order method can need fewer than about α²T calls in that range, and
  [VG26, Remark 10.2] treats the regularized bound as optimal up to the logarithm. The proposition
  contradicts that statement. The proof given in [VG26] applies the lower bound of Devolder, Glineur and
  Nesterov for the (δ, L, μ)-oracle class to the smaller class of smooth functions with gradient error,
  which is not a valid transfer.
- The constants are very large (the α⁴T term carries a factor of order 10⁶), so the proposition improves
  on the theorem only for α below about 10⁻³ and T above about α⁻⁴. For T ≤ α⁻⁴ the single-loop bound of
  the theorem is the better one, and it has no logarithm.
- The α² term is thus a property of this method, as far as the numerics show, and not of the class. We
  expect, but have not shown, that further nesting reduces the power of α again. The complexity of the
  class is open: between √T and the minimum of the two bounds above.
- Numerically, on the rotation instances with α = 0.05, a tuned two-level scheme keeps f(x_N)·N²/(LR²)
  between 250 and 670 for N from 10⁵ to 1.6·10⁶ (far beyond 1/α² = 400), 4 to 8 times below the single-loop
  method with the same number of calls.
- For a time-invariant linear error on a quadratic, polynomial methods designed for a sector of half-angle
  arcsin α are expected to reach a rate close to N^{−2+(2/π)·arcsin α}; such methods carry no guarantee against
  errors that change with time.

## Instances

A typical instance with interacting coordinates and no strong convexity is unregularized logistic or
log-cosh regression, f(x) = Σᵢ log cosh(⟨aᵢ, x⟩ − bᵢ) with L = ‖A‖², where the dimension enters only through
L and R. Sources of relative error are the same as in the strongly convex case: reduced-precision
gradients (α = 2^{−p} for p mantissa bits), inexact inner solves stopped at a relative accuracy (bilevel and
PDE-constrained problems), and contractive compression
(α² = 1 − k/d, where the bound has the order of gradient descent). A one-dimensional example does not show
the difficulty, because there the error only rescales the gradient; the harmful errors are orthogonal to
the gradient and aligned with z_k − x*.

For ε/(LR²) = 10⁻⁶ the earlier accelerated bounds apply for α ≲ 10⁻³. The present budget is about 7·10³
for α ≤ 10⁻², about 1.7·10⁴ at α = 0.03 and about 1.3·10⁵ at α = 0.1, where [VG26, Thm 7.1] gives about 4·10⁸.

## Scope and limitations

- **Horizon.** The damping uses N, hence R and ε (in fact only LR²/ε). The published baselines use the
  same information. No anytime or parameter-free statement is made, and restarting with a doubled horizon
  is not covered by the proof.
- **Relative error only.** An additional absolute error δ is not treated; the expected floor is of order δR.
- **Unconstrained, deterministic, Euclidean.** No constraints, proximal terms or stochastic oracles.
- **Optimality.** Not claimed. For very small α and very small ε the two-level scheme of "Tightness" has a
  better order. The power of 1 − α is not claimed to be sharp.
- **Constants.** They are not optimized.
- **Numerical checks.** The inequalities were tested numerically on quadratic and log-cosh instances with
  adversarial, orthogonal and random errors before formalization. Every step of the theorem is proved in
  Lean without `sorry` or additional axioms.
