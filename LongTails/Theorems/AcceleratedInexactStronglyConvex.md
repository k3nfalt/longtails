# Accelerated gradient descent under relative and absolute gradient error

This note explains the contribution formalized in
[AcceleratedInexactStronglyConvex.lean](AcceleratedInexactStronglyConvex.lean), with
[setup](../Setups/InexactGradientStronglyConvex.lean),
[algorithm](../Algorithms/InexactAccelerated.lean),
[one-step potential inequality](../Proofs/InexactAcceleratedStep.lean) and
[convergence, tuning and execution](../Proofs/InexactAcceleratedConvergence.lean).

**Summary.** For an L-smooth, μ-strongly convex objective and a gradient oracle whose error is bounded by
α‖∇f(x)‖ + δ, a constant-parameter Nesterov-type method reaches accuracy ε in

  N = ⌈ (8 √(κ/(1−α)) + 32 α² κ/(1−α)) · log(1 + 2LR²/ε) ⌉,  κ = L/μ,

oracle calls, for every α ∈ [0,1) and every ε above an error floor of order δ²/μ. The dependence on the relative
error is α²κ, where the best bound we found in the literature is ακ; the accelerated √κ rate is kept up to
α ≈ κ^(−1/4), where the previous threshold was κ^(−1/2). The closest baselines ([VKK+25], [VG26], [GDH26]) are
recent arXiv preprints, not peer-reviewed publications as far as we could verify. The absolute error contributes a floor of order δ²/μ with no √κ inflation, at
the accelerated rate. We do **not** claim that α²κ is optimal for the problem class; see "Tightness".

## Setup and proved guarantee

- **Space.** E is a real Hilbert space of any dimension. Nothing depends on the dimension.
- **Objective.** f: E → ℝ is differentiable and, for all x, y,

    (μ/2)‖y − x‖² ≤ f(y) − f(x) − ⟨∇f(x), y − x⟩ ≤ (L/2)‖y − x‖²,  0 < μ ≤ L.

  This is Assumption 1 of [VKK+25] and (3)–(4) of [VG26]. For convex f the upper inequality is equivalent to an
  L-Lipschitz gradient, so this is the standard class of L-smooth μ-strongly convex functions. A minimizer x*
  with ‖x₀ − x*‖ ≤ R is assumed; in this class it exists and is unique, so the only content is the bound R.
- **Oracle.** The k-th call at a point x returns any vector g with

    ‖g − ∇f(x)‖ ≤ α‖∇f(x)‖ + δ,  0 ≤ α < 1, δ ≥ 0.

  The reply may depend on the call index and on an oracle seed in an arbitrary way, so the error can be
  time-varying and adversarial; it need not be a function of x, and g need not be a gradient field. Since
  the method is deterministic, an adversary that adapts to the past is covered as well. With δ = 0
  this is the relative-error model of Polyak (1987) used in [VGDS23, KGD+23, VKK+25]; with α = 0 it is bounded
  additive error; in general it is the composite model (8) of [VG26]. The squared form
  ‖g − ∇f‖² ≤ ζ² + a‖∇f‖² of Ajalloeian–Stich and [GDH26, Def. 2.6] implies it with α = √a, δ = ζ.
- **Information.** The algorithm receives E, L, μ, α and x₀. It does not use δ, R or ε. The horizon is the
  budget; the method itself is anytime.
- **Validity.** 136 δ² ≤ μ(1−α)² ε. Some condition of this type is unavoidable: with additive error δ no
  method can guarantee accuracy below δ²/(2μ), because the oracle g(x) = μx is admissible for both
  f±(x) = (μ/2)‖x ∓ (δ/μ)u‖², ‖u‖ = 1 (the standard example, cf. [VGDS23, eq. (5)–(6)]).

**Algorithm.** With

  θ = 1 / (4 √(L/(μ(1−α))) + 16 α² L/(μ(1−α))),

and x₀ = z₀, each iteration makes one oracle call:

  y_k = (x_k + θ z_k)/(1 + θ),  g_k = oracle(y_k),
  x_{k+1} = y_k − g_k/L,  z_{k+1} = (1−θ) z_k + θ y_k − (2θ/μ) g_k.

The output is the last primal iterate x_N. There are no restarts, no line search and no extra queries. The
template is the two-sequence scheme used by RE-AGM ([VKK+25, Alg. 1], [VG26, Alg. 2]); the contribution is the
parameter choice and the analysis, not a new algorithm family.

**Guarantee.** With Φ_k = f(x_k) − f(x*) + (μ/4)‖z_k − x*‖², every admissible reply gives

  Φ_{k+1} ≤ (1 − θ/2) Φ_k + (2/(1−α)) (3/(4L) + 2θ/μ) δ²,

hence, for all N,

  f(x_N) − f(x*) ≤ (1 − θ/2)^N · L R² + 68 δ² / (μ(1−α)²).

The Lean theorem `result` states that the budget N above gives f(x_N) − f(x*) ≤ ε for every oracle seed, using
exactly N calls. Here 2/θ = 8√(κ/(1−α)) + 32α²κ/(1−α) is the budget prefactor.

## What is new, and in which regimes

Write κ = L/μ. All comparisons are for the same class, the same oracle and the same criterion.

1. **Rate under relative error.** The best accelerated bound we found is [VG26, Thm 6.1] (equivalently
   [VKK+25, Thm 5] for δ = 0), valid for α ≤ 1/3:
   contraction 1 − (1/300)(μ/L)^(1−γ), γ = min{log_{μ/2L}(3α), 1/2}, that is, complexity of order
   max(√κ, ακ) with constant about 300 (respectively 900ακ). Ours is 8√(κ/(1−α)) + 32α²κ/(1−α).
   - For α ≤ κ^(−1/2) both are accelerated; ours has the smaller constant.
   - For κ^(−1/2) ≪ α ≤ κ^(−1/4) ours is still of order √κ; theirs is ακ. The gain is α√κ, up to κ^(1/4).
   - For κ^(−1/4) ≪ α ≤ 1/3 ours is α²κ; theirs is ακ. The gain is 1/α.
   Earlier thresholds for keeping the √κ rate were α ≲ μ/L [VGDS23, Thm 5.1], (μ/L)^(3/4) (via the
   (δ,L,μ)-oracle of Devolder–Glineur–Nesterov; Gannot 2022), and (μ/L)^(1/2) ([KGD+23, Thm 3.2] with restarts,
   [VKK+25, Thm 4] single loop, described there as the "maximal possible relative error").
2. **Comparison with gradient descent.** GD with step 1/L has complexity about κ/(1−α²) · log for every
   α < 1. Our prefactor is smaller than κ/(1−α²) iff 8(1+α)√((1−α)/κ) + 32α²(1+α) < 1; for large κ this means
   α < 0.164. For larger α our bound has GD's order Θ(κ/(1−α)) but a worse constant (about 64 times as
   α → 1). "Every α ∈ [0,1)" is a validity range, not an improvement range.
3. **Error floor.** The floor 68δ²/(μ(1−α)²) holds at every rate, including the accelerated one, and it does
   not depend on the trajectory. Earlier accelerated bounds are of two kinds. Some have a floor inflated by
   √κ: (1+√κ)·3ζ²/(2μ) in [GDH26, Thm 3.3] (α = 0, via Devolder–Glineur–Nesterov), and (2κ^γ + 5)δ²/μ in
   [VG26, Thm 6.1], which is √κ δ²/μ in the accelerated regime. The other kind is [VGDS23, Thm 4.7] (see also
   their eq. (14)): for α = 0 the floor is (1+√κ)δ²/(2L) + 3R̃_N δ, which is not √κ-inflated in δ² but involves
   the radius R̃_N of the generated trajectory. R̃_N is not bounded in that theorem; with the bound
   R̃ ≃ R + δ/μ mentioned in their introduction the floor is of order Rδ + δ²/μ, which is linear in δ and
   exceeds δ²/μ whenever R ≫ δ/μ. So the new statement for α = 0 is: a single-loop method without
   restarts, the accelerated rate, and a trajectory-independent floor of order δ²/μ.
   [GDH26] explicitly leave open whether the trade-off between acceleration and asymptotic error is
   unavoidable for inexact gradient oracles on smooth losses ("Tradeoff" paragraph after Cor. 3.4, and
   Section 6). For this oracle and class the answer is no: rate √κ and floor O(δ²/μ) hold together. The
   power (1−α)^(−2) in our floor (GD has (1−α²)^(−1)) is an artifact of the proof.
4. **Range.** [VKK+25, VG26] require α ≤ 1/3; here α < 1.
5. **Consequence for Byzantine-robust aggregation (not formalized).** By [GDH26, Lemma 2.5], robust
   aggregation under (G,B)-heterogeneity yields ‖g − ∇f‖² ≤ νG² + νB²‖∇f‖². With α = √ν·B < 1 and δ = √ν·G the
   theorem gives an accelerated rate for B ≠ 0 (their accelerated result needs B = 0) with floor of order
   νG²/μ.

## Instances and where the improvement applies

A typical nonlinear instance with interacting coordinates is ℓ₂-regularized logistic regression,
f(x) = (1/n)Σᵢ log(1 + exp(−bᵢ⟨aᵢ, x⟩)) + (μ/2)‖x‖², with L = ‖A‖²/(4n) + μ. The dimension enters only through L
and μ. The size of α depends on how the gradient is produced.

- *Reduced-precision gradients.* Truncating each coordinate to p mantissa bits gives α = 2^(−p)
  (see [arXiv:2506.09730](https://arxiv.org/abs/2506.09730)). For κ = 10⁶ the old threshold α ≲ √(μ/L)/3
  allows about 3·10⁻⁴; an 8-bit mantissa (α ≈ 0.004) is outside it but well inside the new one (α²κ = 16 ≪ √κ), so
  the fully accelerated rate is now guaranteed. With 4 bits (α ≈ 0.06) the budget prefactor is about 1.4·10⁵,
  against about 10⁶ for gradient descent.
- *Inexact inner solves* (bilevel problems, implicit or PDE-constrained objectives). The inner solver is
  stopped at a relative accuracy, so α is a design parameter, and values of 10⁻²–10⁻¹ are the cheap ones.
- *Robust aggregation.* α = √ν·B with ν of order f/(n−2f); a few percent of Byzantine workers with B ≈ 1 give
  α ≈ 0.1–0.2, at the edge of the improvement window.
- *Outside the window.* Contractive compressors such as top-k or scaled sign have α² = 1 − k/d close to one,
  where the bound has gradient descent's order and a worse constant. Double-precision round-off (α ≈ 10⁻¹⁶)
  is already covered by the old threshold unless κ exceeds about 10³⁰.

## Mechanism

Let G = ‖∇f(y_k)‖, e = g_k − ∇f(y_k) and w = (1−θ)(z_k − x*) + θ(y_k − x*). The standard estimate gives, exactly,

  Φ_{k+1} ≤ (1−θ)(f(x_k) − f*) + (μ/4)(1−θ)‖z_k − x*‖² − (θμ/4)‖y_k − x*‖²
      − (G² − ‖e‖²)/(2L) + (θ²/μ)‖g_k‖² − θ⟨e, w⟩.

Two observations make the bias harmless.

- With the step 1/L the descent term is exactly (G² − ‖e‖²)/(2L): the cross term ⟨∇f, e⟩ cancels.
- Taking θ a constant factor below its exact-oracle value leaves a slack of order G²/L. The dangerous term
  θ⟨e, w⟩ is linear in the error and involves the distance to the solution. Young's inequality splits it as
  (2θ/μ)‖e‖² + (θμ/8)‖w‖². The second part is paid by the contraction of ‖z_k − x*‖² and by strong convexity at
  y_k. The first part costs (2θα²/μ)G² and is absorbed by the slack iff θ ≲ μ/(α²L), and it adds only
  (2θ/μ)δ² per step, which gives the floor δ²/μ after dividing by the contraction θ/2.

Previous analyses bound the bias term linearly in α (the parameter equation of RE-AGM has a term 4α·a), or
pass through the (δ,L,μ)-oracle, whose error accumulates with √κ. Using the descent slack to absorb *unbiased*
multiplicative noise is known (Vaswani–Bach–Schmidt 2019; Gupta–Siegel–Wojtowytsch 2024); the step that is
specific to deterministic bias is the Young split of θ⟨e, w⟩ against the two strong-convexity terms.

The inequality is state-wise and holds for each call separately, so δ may change from call to call; summing it
gives Σ_k (f(x_k) − f*) ≤ (2/θ)Φ₀ + O(1/μ)·Σ_k δ_k² for α = 0, an ℓ₂-gain bound of the optimal order 1/μ at the
accelerated rate with step 1/L (not stated in Lean).

A one-dimensional example does not show the difficulty: there a relative error only rescales the gradient by a
factor in [1−α, 1+α]. The harmful errors are orthogonal to the gradient and aligned with z_k − x*, which needs
dimension at least two and, for a general f, an error that is not a gradient field.

## Tightness

**For this scheme the trade-off θ ≍ μ/(α²L) cannot be improved by more than a constant.** The following
statement is proved here on paper and checked numerically; it is not formalized.

*Proposition.* Let 0 < α < 1, 0 < μ ≤ L and 12μ/(α²L) < θ ≤ α²/24. Run the scheme above with this θ (steps 1/L and
2θ/μ) on f(x) = (λ/2)‖x‖², x ∈ ℝ², λ = 2θL/(1 + 2θ²L/μ) ∈ [μ, L], with the admissible linear oracle
g(y) = λ(I + αJ)y, where J is the rotation by 90°. Then the iteration matrix has an eigenvalue of modulus
greater than one, so no bound Φ_{k+1} ≤ qΦ_k with q < 1 can hold.

*Proof.* Identify ℝ² with ℂ; then g(y) = c·y with c = λ(1 + iα), and ‖g − ∇f‖ = α‖∇f‖. Put ρ = λ/L,
m = 1 + 2θ²L/μ, q = m − 1 + θ. The map (x, z) ↦ (x⁺, z⁺) is ℂ-linear with characteristic polynomial
(1+θ)r² − (2 − ρm(1+iα))r + (1−θ)(1 − ρ(1+iα)). Substituting r = 1 − ε gives
ε² − Sε + P = 0 with S = (2θ + ρm(1+iα))/(1+θ) and P = ρq(1+iα)/(1+θ). For a quadratic with roots
ε₁ = a₁ + ib₁, ε₂ = a₂ + ib₂ one has the identity
Re S · Re(S P̄) − (Im P)² = a₁a₂[(a₁+a₂)² + (b₁−b₂)²]. Since Re S > 0, a root with negative real part exists iff
the left side is negative, that is, iff

  (2θ + ρm)(2θ + ρm(1+α²)) < (1+θ) α² ρ q.

With ρ = 2θ/m this reads 4(2+α²)m < (1+θ)α²(1+ν), ν = 2θL/μ, m = 1 + θν. Under the hypotheses θν ≤ α²ν/24, so
4(2+α²)m ≤ 12 + α²ν/2 < α²ν, because α²ν > 24. A root with Re ε < 0 gives |r| = |1 − ε| > 1. Finally
ρ ≤ 2θ ≤ 1, and ρ ≥ μ/L is equivalent to ν(1−θ) ≥ 1, which holds because ν > 24 and θ ≤ 1/24; so
λ = ρL ∈ [μ, L]. ∎

Two elementary facts about the exact oracle complete the picture. First, on f(x) = (L/2)‖x‖² the iteration
gives x_k = 0 for k ≥ 1 and z_{k+1} = z_k(1 − 2θ²L/μ)/(1+θ), which diverges when θ²L/μ > 3/2. Second, on
f(x) = (μ/2)‖x‖² the iteration matrix has determinant (1−θ)(1−μ/L)/(1+θ), so its spectral radius is at least
the square root of this number: the linear rate of the scheme is at most about θ + μ/(2L). Hence, if
α⁴ ≥ 864μ/L (so that α²/24 ≥ √(3μ/(2L))), every θ > 12μ/(α²L) is unstable on some admissible instance, every
stable θ is at most 12μ/(α²L), and the scheme cannot contract faster than about 13μ/(α²L) per step. The
theorem uses θ ≥ (1−α)μ/(32α²L) in that regime. So within this two-sequence family the rate μ/(α²L) is sharp
up to a constant factor depending only on 1−α, and, for this one-parameter family only, κ^(−1/4) is the true
order of the largest relative error at which the √κ rate survives. Other algorithms are not covered by this
statement.

**No lower bound for the problem class is claimed.** [VG26, Thm 10.1] states the lower bound
max(√κ, α²κ) (in exponent form), which our upper bound matches. However, its proof (Appendix G there) turns
additive gradient noise on a smooth function into a (2δ²/μ, 2L, μ/2)-oracle and then applies the
rate/floor trade-off of Devolder–Glineur–Nesterov, which is a lower bound over the whole (δ,L,μ)-oracle class
(its hard instances are nonsmooth) and does not transfer to that subclass. Our theorem with α = 0 (rate √κ
with floor O(δ²/μ)) is incompatible with that transfer. So the statement of [VG26, Thm 10.1] is, to our
knowledge, unproved, and the optimal dependence on α is open. The instance in the proposition cannot settle
it: for a time-invariant linear error on a quadratic the oracle is a fixed linear map with spectrum in the
cone |arg z| ≤ arctan α, and polynomial (Krylov-type) methods are expected to need only about κ^(1/2+O(α))
iterations there (a heuristic, not proved here). A general Ω(α²κ) bound, if true, must use nonlinear or
time-varying errors.

## Relation to prior work

- [VKK+25] Vasin, Krivchenko, Kovalev, Stonyakin, Tupitsa, Dvurechensky, Alkousa, Kornilov, Gasnikov,
  [arXiv:2503.06628v3](https://arxiv.org/abs/2503.06628v3). Thm 4: √κ rate for α ≲ √(μ/L); Thm 5: rate
  (μ/L)^(1/2+τ) for α = (1/3)(μ/L)^(1/2−τ), i.e. ακ. Same algorithm template. Preprint.
- [VG26] [arXiv:2603.12376](https://arxiv.org/abs/2603.12376), "Lower and upper bounds of the convergence rate
  of gradient methods with composite noise in gradient". Thm 5.2 (GD), Thm 6.1 (RE-AGM under composite noise),
  Remark 10.2 (their own upper/lower gap), Thm 10.1 and Appendix G (see above). Preprint.
- [KGD+23] Kornilov, Gorbunov, Alkousa, Stonyakin, Dvurechensky, Gasnikov,
  [arXiv:2310.00506](https://arxiv.org/abs/2310.00506). Thm 3.2: √κ for α ≲ √(μ/L) with restarts.
- [VGDS23] Vasin, Gasnikov, Dvurechensky, Spokoiny, [arXiv:2102.02921](https://arxiv.org/abs/2102.02921)
  (Optim. Methods Softw. 2023). Thm 5.1: α = O(μ/L).
- [GDH26] Gaucher, Dieuleveut, Hendrikx, [arXiv:2602.03329](https://arxiv.org/abs/2602.03329). Def. 2.6,
  Thm 3.3, Cor. 3.4 and the open question quoted above. Preprint.
- Devolder, Glineur, Nesterov, "First-order methods of smooth convex optimization with inexact oracle"
  (Math. Program. 2014) and the strongly convex companion (CORE DP 2013/16): (δ,L,μ)-oracle, floor √κ·δ for
  fast methods and the matching trade-off for that oracle class. Not read in the original; used as quoted in
  [VG26], [GDH26], [VGDS23].
- Gürbüzbalaban, [arXiv:2309.11481](https://arxiv.org/abs/2309.11481). ℓ₂ gain of momentum methods under
  square-summable additive errors: exact for quadratics (1/√(2μ) for Nesterov), and Prop. 5.3 for general
  strongly convex f, which is of the optimal order only for small steps and contains a term of order L/μ² at
  step 1/L. Multiplicative errors are treated there for quadratics through stability radii.
- Lessard, Recht, Packard, [arXiv:1408.3595](https://arxiv.org/abs/1408.3595), Section 5.2, and Cyrus, Hu,
  Van Scoy, Lessard, [arXiv:1710.04753](https://arxiv.org/abs/1710.04753): the same relative-error model,
  with numerical (IQC/LMI) evidence that Nesterov's method with standard tuning loses stability as κ grows and
  that slower tunings are more robust; no closed-form rate in α and κ. Gannot,
  [arXiv:1912.13494](https://arxiv.org/abs/1912.13494): explicit rate for the inexact Triple Momentum Method
  with standard tuning.
- Ajalloeian and Stich, [arXiv:2008.00051](https://arxiv.org/abs/2008.00051): biased SGD, non-accelerated.
- Vaswani, Bach, Schmidt, [arXiv:1810.07288](https://arxiv.org/abs/1810.07288); Gupta, Siegel, Wojtowytsch,
  [arXiv:2302.05515](https://arxiv.org/abs/2302.05515): acceleration under *unbiased* multiplicative noise.

Skimmed only: Michalowsky–Scherer–Ebenbauer, [arXiv:1905.00279](https://arxiv.org/abs/1905.00279) (IQC-based
synthesis, numerical) and Stonyakin et al., [arXiv:2001.09013](https://arxiv.org/abs/2001.09013) (inexact models of
(δ,L)-type). Not read: Devolder's thesis and the CORE discussion paper.
We found no earlier proof of the √κ + α²κ rate, of the κ^(−1/4) threshold, or of an accelerated rate with an
O(δ²/μ) floor for general smooth strongly convex objectives, but the control-theoretic literature is large and
this search cannot be exhaustive.

## Limitations

- The method needs L, μ and (an upper bound on) α.
- No lower bound is proved; optimality of α²κ over all methods is open (see "Tightness").
- For α ≳ 0.16 the bound does not improve on gradient descent.
- Only the strongly convex case is formalized. The same mechanism with a horizon-dependent slack
  s = min(1, 1/(α²N)) in the linear-coupling potential A_k(f(x_k) − f*) + ½‖z_k − x*‖² gives, for merely convex
  f and δ = 0, f(x_N) − f* ≲ LR²(1/N² + α²/N)/(1−α²), removing the α²LR² plateau of [KGD+23, Thm 3.1] and the
  logarithm of [VG26, Thm 7.1]. This remark is a derivation sketch and is **not** part of the formal result.
- The result is deterministic and worst-case. Unbiased stochastic noise is not treated.

## Lean layout

- [InexactAcceleratedStep](../Proofs/InexactAcceleratedStep.lean): `step_potential`, the one-step inequality
  for an arbitrary state and an arbitrary admissible reply.
- [InexactAcceleratedConvergence](../Proofs/InexactAcceleratedConvergence.lean): `momentum_bounds` (the
  parameter θ satisfies the two step conditions and 2/θ equals the budget prefactor), `advance_potential`
  (iteration along the actual execution with time-varying replies), `floor_le`, and `execute_accuracy`.
- [AcceleratedInexactStronglyConvex](AcceleratedInexactStronglyConvex.lean): the one-line `budget` and the
  theorem `result : Convergence spec budget`.
