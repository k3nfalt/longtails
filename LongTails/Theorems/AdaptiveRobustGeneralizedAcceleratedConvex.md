# Light-tail complexity under finite variance for accelerated (L₀,L₁)-smooth convex optimization

This note explains the theorem `OracleTemplate.RobustGeneralized.AdaptiveRobustGeneralizedAcceleratedConvex.result` in
[AdaptiveRobustGeneralizedAcceleratedConvex.lean](AdaptiveRobustGeneralizedAcceleratedConvex.lean).
It is a second convergence theorem for the same setup namespace as the baseline
[FiniteVarianceGeneralizedAcceleratedConvex.lean](FiniteVarianceGeneralizedAcceleratedConvex.lean).
Its algorithm and proofs live in the namespace `OracleTemplate.AdaptiveRobustGeneralized`.

**Same setup.** The theorem keeps the setup, oracle, accuracy criterion and public information of the baseline
[`RobustGeneralized.result`](FiniteVarianceGeneralizedAcceleratedConvex.lean). Its oracle
complexity is never worse in order and is better in every noise-dominated regime.

**Headline.** Under only finite variance, the high-probability complexity matches the
sub-Gaussian complexity W + Vℓ, up to constants, whenever δ ≥ (e+W)^{−c} for a fixed c > 0,
where W is the deterministic complexity.

**L₁ = 0 subclass.** The bound √A + Vℓ holds simultaneously for all δ ≥ (e+A)^{−c}, and it is
optimal up to constants (Corollary 2). At constant δ this matches what earlier finite-variance
bounds already give, for example NEN's (√A+V)ℓ. The difference appears for polynomially small
δ ≤ A^{−c′}. There, every previous finite-variance accelerated high-probability bound we know
multiplies √A by a confidence logarithm, so this result gains a factor min{ℓ, log A} on √A.

## Setup (reused unchanged)

[`RobustGeneralized.spec`](../Setups/FiniteVarianceGeneralizedSmoothAndConvex.lean):

- **Objective:** a convex f on a separable real Hilbert space. The gradient is differentiable,
  with ‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖. This is the Hessian form of (L₀,L₁)-smoothness from
  [Zhang, He, Sra, Jadbabaie, ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS).
- **Solution data:** a minimizer x* with ‖x₀−x*‖ ≤ R and f(x₀)−f(x*) ≤ Δ.
- **Oracle:** IID samples from an abstract probability law. The stochastic gradient is jointly
  measurable and vector unbiased, with E‖g(x,ξ)−∇f(x)‖² ≤ σ². No higher moments are assumed.
- **Public information:** L₀, L₁, R, Δ, σ, ε and δ.
- **Success:** the returned point x̂ satisfies Pr[f(x̂) − f(x*) > ε] ≤ δ.

**Notation.**

- A = L₀R²/ε, q = L₁R, V = σ²R²/ε², Λ = log(4+4Δ/ε), ℓ = log(e/δ).
- W = 1 + √A + Λ + (qΛ)^{2/3}.
- A′ = A + ℓ²V, S′ = √(1+A′), W′ = 1 + √A′ + Λ + (qΛ)^{2/3} (so W ≤ W′ ≤ W + ℓ√V).
- H = log(e(1+A′+q+Λ)/δ).

## Algorithm and returned point

The [algorithm](../Algorithms/AdaptiveRobustGeneralizedAccelerated.lean) is the baseline's
non-restarted damped accelerated method with pilot-centred clipped gradient estimates. Each step
makes two gradient queries, each answered from a fresh block of samples. The method returns its
final iterate x̂. The three changes below use only public parameters and the step's nominal
weight a. That weight is determined before any of the step's samples are drawn.

1. **Noise-dependent curvature floor** (`inflate`).
   - The method runs with L₀′ = L₀ + ℓ²σ²/ε. Since L₀′ ≥ L₀, f is also (L₀′,L₁)-smooth.
   - The invariant guess ≥ L₀′ caps every active nominal weight: a·√(1+A′) ≤ 725R²/ε.
   - This costs at most ℓ√V extra iterations. In return, the pilot cost, which is quadratic in
     a, becomes O(Vℓ²/√(1+A′)) instead of O(Vℓ²).
2. **Adaptive number of pilot groups** (`ratio`, `pilotGroups`).
   - The clipping radius is B = R/(64aℓ), and the per-sample noise-to-radius ratio is
     x = 576σ²/B².
   - Let y = min{1, max{x, e^{−28H}}}. The majority-vote pilot centre uses
     k = max{1, ⌈28H/log(4/y)⌉} groups of max{1,⌈x⌉} samples.
   - It fails with probability at most (2√(y/16))^k ≤ e^{−14H}, which suffices for a union
     bound over the deterministic iteration limit.
   - The baseline always uses ⌈64H⌉ groups. Here k = 1 whenever the per-step noise is
     exponentially below the radius.
3. **Correction with linear confidence** (`correctionSize`).
   - The clipped correction batch has max{1,⌈2³⁰σ²aℓ/ε⌉} samples; the baseline uses ℓ².
   - The exponential-moment compensator now totals ℓ instead of O(1). With the unchanged energy
     threshold 2R², the noise event has probability at most e^{ℓ−2ℓ} = δ/e.

## Guarantee

The public budget below is one explicit line in the parameters. Within it, at most K calls are
made, counting all pilot, correction and padding calls, and Pr[f(x̂)−f(x*) > ε] ≤ δ.

K = ⌈2²¹W′ + 2⁴⁰Vℓ + 2⁴⁸·H·Vℓ²/S′ + 2²¹·H·W′ / log(e + W′S′/(2²⁶Vℓ² + W′S′e^{−28H}))⌉.

Up to constants, the four terms are:

- **Iterations:** W′.
- **Statistical:** Vℓ.
- **Pilot samples:** H·Vℓ²/S′ ≤ Hℓ√V.
- **Confidence price of the optimization term:** H·W′/log(·).

## Consequences

**Corollary 1 (light-tail parity).** For every c > 0 there is C_c such that δ ≥ (e+W)^{−c}
implies K ≤ C_c(W + Vℓ). This is the complexity that
[`StochasticGeneralizedAcceleratedConvex`](StochasticGeneralizedAcceleratedConvex.lean) proves
under norm-sub-Gaussian noise. Here only finite variance is assumed.

*Proof sketch.*

- **Pilot term:** if √V ≥ H then Hℓ√V ≤ Vℓ. Otherwise V < H², and
  H ≤ ℓ + log(e(1+A+q+Λ)) + log(1+ℓ²H²) = O_c(log(e+W)), because ℓ = O_c(log(e+W)) and
  1+A+q+Λ ≤ 7(e+W)^3. Hence Hℓ√V ≤ H²ℓ = O_c(log³(e+W)) = O_c(W).
- **Last term, case Vℓ² ≤ √(W′S′):** the logarithm is at least ½ min{log(W′S′), 28H}. Also
  H ≤ ℓ + C log(e+W′S′), using A′ ≤ S′², q ≤ C W′^{3/2} and Λ ≤ W′. So the last term is
  ≤ C W′(1 + ℓ/log(e+W′)) = O_c(W′).
- **Last term, otherwise:** ℓ√V > W′^{1/3}, because S′ ≥ ℓ√V. There are two sub-cases.
  - If ℓ√V ≤ W′^{3/4}, the logarithm is at least ¼ log W′.
  - If ℓ√V > W′^{3/4}, put Y = ℓ²V. Then W′ < Y^{2/3}, and also
    H ≤ ℓ + C log(e+Y), because 1+A′+q+Λ ≤ C(Y+W′)². Under the hypothesis,
    ℓ ≤ c·log(e+W) + 1 ≤ C_c log(e+Y). Hence H·W′ ≤ C_c log(e+Y)·Y^{2/3}. Moreover
    log²(e+Y)·Y^{2/3} ≤ C'·Y when Y exceeds an absolute constant, so
    H·W′ ≤ C_c''·Y/log(e+Y) ≤ C_c'''·Y/ℓ = C_c'''·Vℓ. For Y below that constant, every term is
    O_c(1) ≤ O_c(W).
- **Iterations:** finally, W′ ≤ W + ℓ√V ≤ W + Vℓ + ℓ, and ℓ = O_c(log(e+W)).

A numerical evaluation of the exact formula, with constants dropped, gave
max K/(W+Vℓ) = 8.1, 12.5 and 21.6 for c = 1, 2, 4. The scan covered A ≤ 10¹², q ≤ 10⁹ and
V ≤ 10¹².

**Corollary 2 (optimal on the ordinary-smooth subclass).** Take L₁ = 0 and Δ ≤ L₀R²/2, which
holds for the true gap. Then Λ ≤ log(4+2A) and W ≍ 1+√A. For δ ≥ (e+A)^{−c}:

K ≤ C_c(1 + √A + Vℓ).

This is optimal up to constants:

- **Deterministic lower bound:** Ω(√A) for first-order methods on L₀-smooth convex functions in
  high dimension (Nesterov, *Introductory Lectures*, Thm 2.1.7). It applies with σ = 0.
- **Statistical lower bound:** Ω(Vℓ), by a standard two-point argument. It needs δ < 1/4, A ≥ 4
  and 2ε ≤ Δ ≤ L₀R²/2.
  - Let f_θ(x) = θcx + (L/2)x² on ℝ, with θ ∈ {±1}, L = 4ε/R² ≤ L₀ and c = 4ε/R, and start at
    x₀ = 0.
  - Then x* = −θR, f_θ(x₀) − f* = c²/(2L) = 2ε ≤ Δ, and f_θ(x) − f* = (L/2)(x+θR)². So the
    ε-sublevel sets {|x+θR| ≤ R/√2} of the two instances are disjoint, and an ε-optimal point
    reveals θ.
  - The oracle returns ∇f_θ(x) + N(0,σ²). The two instances' replies differ in mean by 2c, so
    the KL divergence per call is (2c)²/(2σ²) = 32ε²/(σ²R²).
  - By Bretagnolle–Huber, success probability at least 1−δ for both θ requires
    n ≥ (σ²R²/(32ε²))·log(1/(4δ)).

  Gaussian noise has finite variance (it is even sub-Gaussian), so this bound applies to the
  present class. These lower bounds are classical and are not formalized here.

By comparison:

- **[Nguyen, Ene, Nguyen, NeurIPS 2023, Thm 4.1](https://arxiv.org/abs/2304.01119):** O((√A+V)ℓ).
  This equals ours up to constants at constant δ, and loses a factor min{ℓ, log A} on √A
  when δ ≤ A^{−c′}.
- **[Sadiev et al., ICML 2023](https://proceedings.mlr.press/v202/sadiev23a.html):** about
  √A·log(A/δ) + V·log(V/δ).
- **[Gorbunov, Danilova, Gasnikov, NeurIPS 2020](https://proceedings.neurips.cc/paper_files/paper/2020/file/abd1c782880cc59759f4112fda0b8f98-Paper.pdf)
  (clipped-SSTM; Thm F.1 and eq. (30) of the full version, [arXiv 2005.10785](https://arxiv.org/abs/2005.10785)):**
  O(max{√A, V}·log(A/δ)).

Sadiev et al. and clipped-SSTM carry log(A/δ) on √A even at constant δ. NEN loses on √A only
when δ ≤ A^{−c′}.

**Under (L₀,L₁).** Optimality is claimed only where √A dominates the curvature and logarithmic
terms. The optimal dependence on q is open even deterministically; see Gorbunov et al. (ICLR
2025) and the ARC-SG discussion.

**Comparison with the baseline K₀ = Θ((W+Vℓ²)·H₀), where H₀ = log(e(1+A+q+Λ)/δ):**

- **Never worse in order.**
  - Terms without H: W′ ≤ W + ℓ√V, with ℓ√V ≤ (1+ℓ²V)/2. So W′ and Vℓ are O(K₀).
  - Terms with H: H ≤ H₀ + log(1+ℓ²V). If log(1+ℓ²V) ≤ 4H₀, H is absorbed into H₀. Otherwise
    ℓ²V ≥ e^{4H₀} − 1 ≥ (W/7)². In that case log(1+ℓ²V)·(W + ℓ√V) = O(ℓ²V) = O(K₀), using
    W ≤ 7(1+A+q+Λ)² ≤ 7e^{2H₀}.
- **Variance term:** Vℓ²H₀ becomes Vℓ + Hℓ√V, which is Vℓ when V ≥ H²: a gain of a factor ℓH₀.
- **Optimization term:** W·H₀ becomes W(1 + H/log(e + W′S′/(Vℓ²+W′S′e^{−28H}))), giving O(W)
  under Corollary 1.

The formula also evaluates to O(W) at σ = 0, but this is only a sanity property, since with an
exact oracle it is trivial.

## Related work and why the mechanism is needed

**Robust mean estimation.** Median-of-means and geometric-median selection give sub-Gaussian
deviation at a prescribed confidence from finite-variance samples:

- [Minsker, Bernoulli 2015](https://arxiv.org/abs/1308.1334);
- [Hsu and Sabato, JMLR 2016](https://jmlr.org/papers/v17/14-273.html).

Plugging such estimators into each step of a gradient method is the approach of
[Prasad, Suggala, Balakrishnan, Ravikumar, JRSS-B 2020](https://doi.org/10.1111/rssb.12364).

**Per-step union bound.** When a robust estimate is needed at each of T steps, the union bound
asks for confidence δ/T per step, so every step pays log(T/δ) samples at least. This puts the
factor log(T/δ) on the optimization term. That is the source of the H factor in the baseline,
and of the log(A/δ) in clipped-SSTM and Sadiev et al. NEN avoid the union bound with a
whole-run supermartingale, but their clipping radius forces step sizes smaller by a factor
γ = log(1/δ), which costs √A·ℓ iterations.

**Confidence boosting.** proxBoost
([Davis, Drusvyatskiy, Xiao, Zhang, JMLR 2021](https://jmlr.org/papers/v22/20-821.html)) and
truncated mirror descent
([Juditsky, Nazin, Nemirovsky, Tsybakov, Autom. Remote Control 2019](https://arxiv.org/abs/1907.02707))
do not give an additive confidence cost for accelerated non-strongly-convex problems. proxBoost
needs strong convexity or regularization, which adds logarithms on both terms. RSMD is
non-accelerated with a bounded domain.

**What is added here.** The required confidence per step is log(T/δ), but the number of samples
it costs is log(T/δ)/log(1/x), where x is the step's noise-to-radius ratio. Two ingredients turn
this into an additive cost:

- an exponent floor that keeps the count at one group when the step is essentially noiseless;
- a concavity charging inequality, 1/log(4/y) ≤ (1+y/τ)/log(4/τ).

The charging sums the per-step confidence costs against the total pilot noise mass, which the
curvature floor keeps at O(Vℓ²/√(1+A′)). The result is
W·H/log(e + W′S′/(Vℓ²+…)) instead of W·H. Under (L₀,L₁) this must hold uniformly over damped
attempts. That is ensured by the pathwise nominal-weight bound and the guess ≥ L₀′ invariant.

## Comparison with the closest (L₀,L₁) results

| Result | Model | Complexity | Relation |
|---|---|---|---|
| [Lobanov, Dvinskikh, Gasnikov, arXiv 2609.33415v1, Thm 9](https://arxiv.org/abs/2609.33415) (preprint, 27 Sep 2026) | (H₀,H₁), p-th moment, single sample, restarts | O((S+√A+qJ+V)·log(S/δ)), S=⌈log₂(Δ/ε)⌉, J=min{S,⌈log₂⁺(cL₁²Δ/L₀)⌉} | For Δ > ε, W ≤ C(1+S+√A+qJ) by an elementary computation, so the deterministic part is never worse. Their confidence factor log(S/δ) multiplies everything. Ours is 1 + ℓ/log(·) on W′ and ℓ on V. Their model is broader: first-order local smoothness, p∈(1,2], gradient- and gap-dependent noise. |
| [Chezhegov et al., arXiv 2505.20817 v3, Thm 2](https://arxiv.org/abs/2505.20817) | convex (L₀,L₁), heavy tails, non-accelerated | O(A + V·max{q,ℓ} + ℓ² + q·log(·/δ)) | Ours is accelerated and has no q multiplier on V. |
| Repository baseline | same setup | Θ((W+Vℓ²)H₀) | Never worse in order; better as above. |

**Exceptions.** These are the regimes where this theorem is not better:

- **Against LDG:**
  - (i) the corner where A and V are polylogarithmic and δ is tiny. There our Hℓ√V ≈ ℓ²
    exceeds their (S+V)log(S/δ); a numerical scan found up to a factor of about 20 at ℓ=100.
  - (ii) the moderate-noise band Vℓ² ≈ W′S′, where our factor on W′ reverts to H against their
    log(S/δ).
- **Against Chezhegov v3:** the corner where A, q and V are O(1) and δ is small.
- **Against NEN:** no gain at constant δ.

## Limitations

- **Obstruction (not a lower bound).** In schemes that recentre the clipping at every step, the
  residual factor 1 + ℓ/log(·) is necessary for this proof technique:
  - gradients at consecutive accelerated query points can differ by their own magnitude, while
    the admissible clip radius is smaller by a factor ℓ;
  - a per-step centre must therefore be accurate at relative level 1/ℓ, which costs about
    log(N/δ)/log(1/x) samples at failure probability δ/N;
  - tolerating failures instead lets each one consume a Θ(R²) share of the energy budget.

  This is a statement about that algorithm class only. We know of no lower bound that separates
  finite-variance from sub-Gaussian high-probability complexity.
- **NEN comparison:** it is made against their theorem. We do not prove that their algorithm
  needs √A·ℓ iterations.
- **Constants:** they are large (2²¹ to 2⁴⁸). The deterministic shape keeps the baseline's
  (qΛ)^{2/3} and Λ.
- **Twice differentiability:** it is inherited from the setup's Hessian condition.

## Lean layout

- **Algorithm:** [`AdaptiveRobustGeneralizedAccelerated`](../Algorithms/AdaptiveRobustGeneralizedAccelerated.lean)
  defines `ratio`, `pilotGroups`, `correctionSize`, `inflate` and `algorithm`.
- **Generic majority bound:** [`AdaptivePilotConfidence`](../Proofs/AdaptivePilotConfidence.lean)
  proves Pr[majority bad] ≤ (2√θ)^k for an arbitrary per-group failure probability θ.
- **Analysis modules:** `AdaptiveRobustGeneralized{Tuning,Measurability,Oracle,Process,Concentration,StoppedEnergy,Trace,Terminal,Failures,Cost,Budget,Execution,Coupling,Convergence,Output}`
  follow the baseline's layout. The new content is in:
  - Tuning, Concentration and Terminal: the O(ℓ) exponent budget and the δ/e tail.
  - Failures: the adaptive pilot failure bound e^{−14H} and the union bound.
  - Cost: the charging inequality and the per-step estimator cost.
  - Budget: the guess ≥ L₀ invariant, the weight cap, and the summed call bound `callBound`.
- **Public reduction:** [`AdaptiveRobustGeneralizedPublic`](../Proofs/AdaptiveRobustGeneralizedPublic.lean)
  reduces `callBound (inflate p)` to the one-line public budget.
