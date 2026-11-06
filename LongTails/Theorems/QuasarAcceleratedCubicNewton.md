# Accelerated cubic Newton for quasar-convex functions with Lipschitz Hessians

**Lean files:**
- Theorem: [`QuasarAcceleratedCubicNewton.lean`](QuasarAcceleratedCubicNewton.lean) (`LongTails.Theorems.QuasarAcceleratedCubicNewton.result`).
- Setup: [`QuasarConvexHessianLipschitz.lean`](../Setups/QuasarConvexHessianLipschitz.lean).
- Algorithm: [`QuasarCubicNewton.lean`](../Algorithms/QuasarCubicNewton.lean).
- Proofs: [`QuasarCubicStep`](../Proofs/QuasarCubicStep.lean) (cubic step and envelope bracket), [`QuasarCubicPotential`](../Proofs/QuasarCubicPotential.lean) and [`QuasarCubicStepBound`](../Proofs/QuasarCubicStepBound.lean) (estimate sequence), [`QuasarCubicTuning`](../Proofs/QuasarCubicTuning.lean) (parameters), [`QuasarCubicExecution`](../Proofs/QuasarCubicExecution.lean) and [`QuasarCubicConvergence`](../Proofs/QuasarCubicConvergence.lean).

## Summary

To our knowledge, this is the first second-order (Hessian-oracle) method for γ-quasar-convex functions with only a Lipschitz Hessian that beats the ε^{-1/2} complexity of cubic regularization. The algorithm uses no gradient-Lipschitz constant, no convexity, and no bounded sublevel set. It returns, deterministically, a last iterate x̂ with

f(x̂) − f(x⋆) ≤ ε

after O(γ^{-3/2} (HR³/ε)^{3/8} log(·)) oracle calls. Each call returns (f, ∇f, ∇²f) at one point. Cubic Newton needs γ^{-3/2}(HD³/ε)^{1/2} under the same assumptions plus a sublevel-set diameter D.

The contribution is partial acceleration, ε^{-1/2} → ε^{-3/8}, for this nonconvex class. It is not the convex rate ε^{-1/3} or the optimal convex rate ε^{-2/7}; see "Limitations".

## Problem class, oracle, and accuracy

The [setup](../Setups/QuasarConvexHessianLipschitz.lean) fixes a finite-dimensional real inner-product space E of arbitrary dimension and a function f : E → ℝ such that:

- f is C² and its Hessian is globally H-Lipschitz in operator norm: ‖∇²f(x) − ∇²f(y)‖ ≤ H‖x − y‖. This is the Nesterov–Polyak cubic-regularization assumption.
- f is γ-quasar-convex with respect to a global minimizer x⋆, for some 0 < γ ≤ 1:
  γ(f(x) − f(x⋆)) ≤ ⟨∇f(x), x − x⋆⟩ for all x.
  This is Definition 1 of Hinder–Sidford–Sohoni, stated here without their smoothness assumption. Star-convexity with differentiable f is the case γ = 1.
- The algorithm knows the public bounds ‖x₀ − x⋆‖ ≤ R and ‖∇²f(x₀)‖ ≤ L₀ (the latter enters only a logarithm), together with H, γ and ε.

There is no gradient-Lipschitz assumption, no convexity, and no bound on sublevel sets. ∇f(x₀) and f(x₀) − f(x⋆) are not used.

One oracle call at a query point x returns the triple (f(x), ∇f(x), ∇²f(x)). The algorithm never sees x⋆, f(x⋆), or third derivatives. The theorem counts every call, including all line-search probes.

The guarantee is deterministic. The output is the last iterate of the outer loop, and the accuracy criterion is f(x̂) − f(x⋆) ≤ ε (stated as an almost-sure statement under the trivial seed law).

## Algorithm

Quasar accelerated cubic Newton (QACN) maintains an estimate function. Write a_{k+1} = (k+1)(k+2)/2 and A_k = k(k+1)(k+2)/6. Then

ψ_k(u) = Σ_{i<k} a_{i+1}[f(z_i) + γ^{-1}⟨∇f(z_i), u − z_i⟩] + (N/6)‖u − x₀‖³,

whose minimizer v_k has a closed form. With the cubic model m_y(h) = ⟨∇f(y),h⟩ + ½⟨∇²f(y)h,h⟩ + (M/6)‖h‖³ and its exact global minimizer h⋆(y), the method uses the **model envelope**

ẽ(y) = f(y) + min_h m_y(h).

ẽ(y) is computable from one oracle call at y.

Iteration k, with d = v_k − x_k:

1. Query v_k. If ẽ(v_k) ≤ f(x_k), set y = v_k.
2. Otherwise, bisect on τ ∈ [0,1] for n steps. Keep ẽ(x_k + τ_lo d) ≤ f(x_k) < ẽ(x_k + τ_hi d), starting from τ_lo = 0, which is valid because ẽ(x_k) ≤ f(x_k). Set y = x_k + τ_lo d.
3. Take the cubic step z = y + h⋆(y), query z, and set x_{k+1} = z. Add the quasar lower model at z to ψ.

The horizon is K = ⌈(2²³ HR³/(γ⁴ε))^{3/8}⌉. The regularization is M = 270 H K^{1/3}/γ, which is fixed-horizon, and N = 7776 M/γ³. The bisection depth n is logarithmic. The [algorithm file](../Algorithms/QuasarCubicNewton.lean) gives the exact formulas.

## Guarantee and oracle cost

The public budget is

⌈(2²³ HR³/(γ⁴ε))^{3/8}⌉ · (⌊log₂⌈27(2²³HR³/(γ⁴ε)+1)²(L₀/(HR)+32768)/γ²⌉⌋ + 3) + 1

oracle calls, that is O(γ^{-3/2}(HR³/ε)^{3/8} · log(HR³/(γε) + L₀/(HR))). The theorem proves that this many calls suffice for the actual `execute` run: each iteration uses at most depth + 2 calls, plus one initial call.

## The new mechanism

Accelerated second-order methods for convex f (Nesterov 2008; Monteiro–Svaiter 2013; Carmon et al. 2022) need, in the coupling step,

f(x_k) ≥ f(z) + ⟨∇f(z), x_k − z⟩

at the new point z, which convexity provides. For quasar-convex functions, Hinder–Sidford–Sohoni replace this with a line search on f along [x_k, v_k]. The search certifies ⟨∇f(y), v_k − y⟩ ≥ 0 at the *searched* point y. A second-order step, however, makes progress measured by the gradient at the *stepped* point z = y + h⋆(y), and the two gradients are not comparable.

With the anisotropic cubic preconditioner, ⟨∇f(z), v_k − y⟩ can be ≈ −‖∇f(z)‖‖v_k − y‖ at the line minimizer of f, already for convex quadratics in dimension 2. So the first-order search does not transfer.

QACN searches on the model envelope ẽ instead. Its key bracket lemma ([`envelope_increment`](../Proofs/QuasarCubicStep.lean)) reuses the *same step vector* h⋆(y) at the shifted point y + w. Because ẽ is a minimum over steps,

ẽ(y + w) − ẽ(y) ≤ ⟨∇f(z), w⟩ + H‖h‖²‖w‖ + O(‖w‖²).

The cubic regularizer cancels exactly, and the only error is the change of the Taylor remainder, bounded via the Lipschitz Hessian. This needs neither third derivatives nor continuity or uniqueness of the (possibly non-unique) cubic step map. The bisection bracket therefore certifies

⟨∇f(z), v_k − x_k⟩ ≥ −H r²‖v_k − x_k‖ − O(2^{-n}),  where r = ‖h⋆(y)‖.

This approximate quasar coupling holds at the gradient that drives second-order progress.

The coupling error (a/γ)H r² D is paid by AM–GM out of the A_{k+1}-weighted cubic descent margin (M/12)A_{k+1} r³. Summed over K steps, the leftover forces M ≍ H K^{1/3}/γ, and this gives

f(x_K) − f(x⋆) ≤ C · H R³/(γ⁴ K^{8/3}).

The distance D = O(R/γ) between v_k and x_k is proved inside the induction from the potential, using Σ A_{k+1} r_k³ = O(R³/γ³) and a Hölder/Young bound on Σ r_k. So no sublevel-set bound or ‖∇f(x₀)‖ is needed. The first step has d = 0, so no coupling error arises there.

## Comparison with prior work

All rows count oracle calls returning (f, ∇f, ∇²f) unless stated otherwise.

| method | extra assumptions | complexity to f − f⋆ ≤ ε |
|---|---|---|
| Cubic Newton ([Nesterov–Polyak 2006](https://link.springer.com/article/10.1007/s10107-006-0706-8), Section 4.1, star-convex case γ = 1). The γ-explicit version is our reconstruction: the same proof with ⟨∇f(z), z − x⋆⟩ ≥ γ(f(z) − f⋆) | bounded sublevel set, diameter D | O(γ^{-3/2}(HD³/ε)^{1/2}) (our reconstruction for γ < 1) |
| [Hinder–Sidford–Sohoni, COLT 2020](https://arxiv.org/abs/1906.11985) (first-order) | globally L-smooth | O(γ^{-1}(LR²/ε)^{1/2} log) gradients. Not directly applicable under only a Lipschitz Hessian, because no global L exists |
| [Ahookhosh et al. 2026](https://arxiv.org/abs/2604.26735) (HiPPA) | exact high-order prox oracle; growth or strong quasar for rates | prox-step counts, not accelerated |
| Accelerated cubic, MS/A-NPE, and Lipschitz-third-derivative "superfast" methods | **convexity** (γ = 1, convex) | (HR³/ε)^{1/3}; optimal (HR³/ε)^{2/7}; under L₃, ε^{-1/4} and the optimal (L₃/ε)^{1/5} ([2607.24520](https://arxiv.org/abs/2607.24520)). None applies to γ < 1 or to nonconvex star-convex f |
| **This result** | none beyond the setup | **O(γ^{-3/2}(HR³/ε)^{3/8} log)** |

**Improvement regimes:**
- Versus cubic Newton: the ε-exponent improves from 1/2 to 3/8 at the same γ^{-3/2}, and D is replaced by R. Note that D ≥ R and D can be unbounded for quasar-convex functions.
- Versus HSS, heuristically: suppose one plugs a local smoothness bound L ≈ L₀ + HR/γ into HSS. Then it would cost γ^{-1}((L₀ + HR/γ)R²/ε)^{1/2} gradient calls, about γ^{-3/2}(HR³/ε)^{1/2} when L₀ ≲ HR/γ. QACN improves this by (HR³/ε)^{1/8}, up to logarithms. This is **not** a known guarantee: nobody has shown that HSS iterates stay in a ball where that bound holds. The comparison is also in Hessian-oracle calls versus gradient calls.
- **Crossover (the gain is asymptotic).** With the proved constants, QACN uses about γ^{-3/2}·2^{69/8}(HR³/ε)^{3/8}·log calls, while cubic Newton uses about γ^{-3/2}(HD³/ε)^{1/2}. So for D ≈ R, the proved bound is smaller only once (HR³/ε)^{1/8} ≳ 2^{69/8}·log(·), that is HR³/ε ≳ 10^{30} or more. When D ≫ R (in particular when sublevel sets are unbounded, and cubic Newton then has no guarantee), the comparison favors QACN much earlier. The constants were not optimized, and the crossover reflects the proof, not measured performance.

## Instances

A realizable generalized linear model gives a nonconvex instance with interacting coordinates:

f(w) = (1/2n) Σ_i (σ(⟨w, x_i⟩) − σ(⟨w⋆, x_i⟩))².

Take the activation σ(t) = t + a·tanh(t) with a > 0, so that σ' ∈ [1, 1 + a].

- **Quasar-convexity.** Since (σ(u) − σ(u⋆))(u − u⋆) ≥ (σ(u) − σ(u⋆))²/C and σ'(u) ≥ c,
  ⟨∇f(w), w − w⋆⟩ = (1/n)Σ (σ(u_i) − σ(u⋆_i)) σ'(u_i)(u_i − u⋆_i) ≥ (2c/C) f(w).
  So f is γ-quasar-convex with γ = min(1, 2c/C) = 2/(1+a) for a ≥ 1.
- **Lipschitz Hessian.** With φ(u) = ½(σ(u) − y)², we have φ''' = 3σ'σ'' + (σ − y)σ'''. The function σ''' decays like e^{-2|u|}, while |σ − y| grows at most linearly, so φ''' is bounded. Hence H ≤ ‖φ'''‖_∞ max_i ‖x_i‖³.
- **Nonconvexity.** φ'' = σ'² + (σ − y)σ'' takes negative values. For example, a = 10, u = 0.66 and u⋆ = −3 give σ(u) ≈ 6.44, y = σ(−3) ≈ −12.95, σ'(u) ≈ 7.66 and σ''(u) ≈ −7.70. So φ''(u) ≈ 58.7 − 19.39·7.70 ≈ −90 < 0. With data in general position, f is therefore nonconvex.
- **When the rate matters.** If the empirical covariance Σ = (1/n)Σ x_i x_iᵀ is positive definite, the GLM is in fact strongly quasar-convex (quadratic growth with respect to w⋆), and first-order methods converge linearly. The sublinear ε^{-3/8} guarantee is relevant when Σ is singular or badly conditioned, for example n < d or nearly collinear features. The minimizer set is then an affine subspace, and only R = dist(x₀, minimizers) is controlled.

Quasar-convexity also arises in learning linear dynamical systems ([Hardt–Ma–Recht 2018](https://jmlr.org/papers/v19/16-465.html)). For this specific GLM, special-purpose methods such as GLMtron exist. Our result is a class-level oracle guarantee, and the GLM only illustrates that the class is nontrivial.

## Literature coverage

The search was done on 2026-11-04 by both agents independently. It covered:
- ICML 2025–2026, ICLR 2025–2026 and NeurIPS 2024–2025 proceedings and OpenReview;
- arXiv through 2611.04, with queries on quasar-convex, star-convex, weakly quasi-convex, accelerated cubic/tensor/Newton, Hessian oracle, and benign nonconvexity.

The closest work found is:
- **First-order.** [HSS](https://arxiv.org/abs/1906.11985) and follow-ups on quasar-convex acceleration and its stochastic, proximal and continuized variants, including 2410.08395, 2607.19965, 2610.10927 and 2611.04597.
- **Non-accelerated high-order proximal.** [HiPPA, 2604.26735](https://arxiv.org/abs/2604.26735).
- **Convex accelerated second-order and tensor methods.** Nesterov 2008, Monteiro–Svaiter 2013, Carmon et al. 2022, and [2607.24520](https://arxiv.org/abs/2607.24520).

We found no accelerated Hessian-oracle guarantee for quasar- or star-convex functions. This is a gap inferred from theorem scopes, not an explicitly posed open problem.

## Limitations and open questions

- **The exponent 3/8 is not the convex 1/3 or 2/7.** The bracket certifies the coupling only up to a relative error H/M. We believe this error is intrinsic to the bracket certificate: the envelope compares two cubic models whose Hessians differ by up to H‖w‖, and nothing in the class controls the sign of that change along v_k − x_k. Removing it would need control of the Taylor remainder's derivative along v_k − x_k, which a C² function with Lipschitz Hessian does not provide. Whether ε^{-1/3} is achievable under H-Lipschitz Hessians alone is **open**. The obstruction is specific to this mechanism and is not a lower bound for the problem class.
- **The γ-dependence is not improved.** We have γ^{-3/2} versus the first-order γ^{-1} of HSS, and no matching lower bound is known for second-order methods.
- The method is fixed-horizon (M depends on K) and needs H, γ, R and a bound L₀ (logarithmically).
- The constants are large (2²³ inside the (·)^{3/8}). No attempt was made to optimize them.
- Lean represents the exact cubic subproblem minimizer as a choice function. Computing it is internal computation in this framework and costs no oracle calls.

## How the result meets the scope requirement

The requirement is "second-order optimization". The method is a cubic-regularized Newton method that queries Hessians at every step. The class is a standard second-order smoothness class (Lipschitz Hessian), and the contribution is a new Hessian-oracle complexity bound.
