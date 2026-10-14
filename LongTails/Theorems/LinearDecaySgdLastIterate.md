# Log-free last-iterate SGD under variance at the optimum

This note explains the contribution formalized in
[LinearDecaySgdLastIterate.lean](LinearDecaySgdLastIterate.lean).

The theorem is a last-iterate guarantee for plain SGD with a known-horizon linear-decay stepsize. It assumes only per-sample convexity and smoothness plus a bound on the gradient variance at a minimizer, with no uniform variance bound. The resulting rate O(LR²/T + σR/√T) contains no logarithmic factor.

Averaged SGD already attains this order. The claim concerns the last iterate only.

## Setup and proved guarantee

The [setup](../Setups/SampledSmoothConvex.lean) has three ingredients.

- **Space.** E is a real Hilbert space (complete, Borel, second countable).
- **Samples.** Each sample ξ from a probability space (Ξ, p) carries a loss F_ξ: E → ℝ. Each F_ξ is convex, has a gradient ∇F_ξ(x) at every point, and that gradient is L-Lipschitz.
- **Measurability and objective.** (ξ, x) ↦ ∇F_ξ(x) is jointly measurable, and every F_·(x) is integrable. The objective is f(x) = ∫ F_ξ(x) dp(ξ).

The setup assumes a minimizer x* of f with

  ‖x₀ − x*‖ ≤ R   and   σ*² := ∫ ‖∇F_ξ(x*)‖² dp ≤ σ².

Both bounds refer to the same x*. Nothing else is assumed: no uniform variance bound, bounded domain, bounded gradients or strong convexity.

The variance at the optimum does not depend on which minimizer is chosen. Co-coercivity forces ∇F_ξ to agree p-almost surely across minimizers.

**Oracle.** The oracle draws i.i.d. samples, with law `Measure.infinitePi` of p, and the k-th call at x returns ∇F_{ξ_k}(x). The public data are L, R, σ, ε and x₀.

**Algorithm.** The [algorithm](../Algorithms/LinearDecaySgd.lean) runs plain SGD, x_{k+1} = x_k − η_k ∇F_{ξ_k}(x_k), with one oracle call per iteration. The schedule is

  η_k = η (T − k)/T,   η = R / (8LR + σ√T),   k = 0, …, T − 1.

The output is the last iterate x_T. The public budget is the one-line formula

  T = ⌈48 L R²/ε + 324 σ² R²/ε²⌉,

and the theorem proves E f(x_T) − f(x*) ≤ ε. Before tuning, the proof gives

  E f(x_T) − f* ≤ 3‖x₀ − x*‖²/(ηT) + 6 η σ*²   whenever Lη ≤ 1/8.

With the stated η this becomes 24LR²/T + 9σR/√T.

**Interpolation.** When σ = 0, this is a log-free O(LR²/T) last-iterate bound.

**Pinning the algorithm.** The success condition requires that the output's law equal the law of the last iterate of this linear-decay SGD for some horizon T (the witness runs T = budget), together with measurability and E f(output) − f(x*) ≤ ε. Without the law condition, `Convergence` would be satisfied by averaged SGD or by variance-reduced methods. The template's success predicate does not see the oracle seeds, so the pinning is distributional rather than pathwise.

**Lean layout.** The Lean proof is split into the following modules.
- [LinearDecaySgdWeights](../Proofs/LinearDecaySgdWeights.lean): deterministic weight algebra and the tuning bound.
- [LinearDecaySgdStep](../Proofs/LinearDecaySgdStep.lean): the one-sample inequality.
- [LinearDecaySgdExpectation](../Proofs/LinearDecaySgdExpectation.lean): independence of the past and the current sample, and the assembly of the bound.
- [LinearDecaySgdExecution](../Proofs/LinearDecaySgdExecution.lean): the algorithm's execution equals the SGD path.
- [LinearDecaySgdConvergence](../Proofs/LinearDecaySgdConvergence.lean): the final convergence statement.

## Mechanism

Write a_k = E f(x_k) − f*, S_k = Σ_{j≥k} η_j, and c_k = 2Lη_k²(1+Lη_k).

1. **One step.** For any point y determined by the past, one SGD step satisfies

   E f(x_{k+1}) − E f(y) ≤ (E‖x_k − y‖² − E‖x_{k+1} − y‖²)/(2η_k) + (c_k/η_k) a_k + η_k(1+Lη_k)σ*².

   The gap term comes from the per-sample transfer E‖∇F_ξ(x)‖² ≤ 4L(f(x) − f*) + 2σ*², which uses co-coercivity of each convex smooth F_ξ.
2. **Reference points.** Following Zamani–Glineur, take y = z_k, a convex combination of x* and the past iterates. The weights are modified so that they also absorb the gap term: v_0 = 1 and v_{k+1}(S_{k+1} + c_{k+1}) = v_k S_k. The potential
   v_k S_k (f(z_k) − f*) + v_k c_k (f(x_k) − f*) + (v_k/2)‖x_k − z_k‖²
   then grows only by the noise term at each step.
3. **The price.** Absorbing the gap costs the factor Γ = Π_s (1 + c_s/S_s).
   - With constant steps, c_s/S_s ≈ 2Lη/(T − s), so Γ ≈ T^{2Lη}. This is the polynomial or logarithmic loss in the existing σ*-only analyses.
   - Under linear decay, η_s²/S_s ≤ 2η/T uniformly. Hence Σ_s c_s/S_s ≤ 4Lη(1+Lη) ≤ 9/16, and Γ ≤ 16/7 is a horizon-free constant.

Absorbing the gap into the weights is not new. Garrigos et al. and Vaidyan–Friedlander–Alacaoglu use it with constant steps. The new observation is that linear decay keeps the absorbed product bounded, and this is what removes the logarithm.

## Relation to prior results

- **Garrigos, Cortild, Ketels, Peypouquet ([arXiv:2507.14122](https://arxiv.org/abs/2507.14122)).** Under exactly these assumptions they obtain a last iterate of O(ln T/√T). Their Remark 3.6 conjectures that the ln T can be removed with a non-standard stepsize. This theorem confirms that conjecture for a known-horizon schedule.
- **Attia, Schliserman, Sherman, Koren (NeurIPS 2025, [arXiv:2507.11274](https://arxiv.org/abs/2507.11274)).**
  - They obtain Õ(1/T + σ*/√T) for a tuned constant step, and O(1/√T) for the greedy step 1/β when σ* = 0.
  - They leave "eliminating this remaining gap" as an open problem; this theorem closes it for linear decay.
  - Their question about the greedy constant step is not addressed here.
- **Vaidyan, Friedlander, Alacaoglu ([arXiv:2602.05489](https://arxiv.org/abs/2602.05489), Feb 2026).** Proximal SGD with constant steps achieves O(ln T/√T) under componentwise convexity and smoothness. They state that removing the log was "only known with bounded variance".
- **Liu and Zhou ([arXiv:2312.08531](https://arxiv.org/abs/2312.08531), v4).** They give log-free last-iterate rates with linear decay, but under a uniform finite-variance assumption. That global noise level can be arbitrarily larger than σ*, and in the interpolation regime it does not reduce to O(1/T).
- **Other last-iterate work.**
  - Jain, Nagaraj, Netrapalli (2019) and Zamani–Glineur cover Lipschitz or deterministic settings.
  - Defazio, Cutkosky, Mehta, Mishchenko (2023) bound gradients uniformly.
  - Kornowski–Shamir ([arXiv:2604.13870](https://arxiv.org/abs/2604.13870)) show that anytime last-iterate guarantees must lose polylogarithmic factors in the Lipschitz case.

  None of these covers σ*-only smooth problems without a log.
- **Averaged iterates.** Averaged SGD already achieves O(LR²/T + σR/√T) under these assumptions. The contribution is the last-iterate guarantee.
- **Rate comparison.**
  - The deterministic term LR²/T is the gradient-descent rate. Accelerated methods improve it to LR²/T².
  - The noise term σR/√T is unimprovable for stochastic first-order methods.

  The claim concerns plain SGD; it is not an optimal rate for the class.

## Scope and limitations

- **Known horizon and known bounds.** The schedule needs the horizon T and the public bounds R and σ. Log-free last-iterate rates for constant steps, for anytime schedules, and for the greedy step remain open. In the Lipschitz case, Kornowski–Shamir show that anytime schedules cannot avoid polylogarithmic factors.
- **Constants.** The constants 48 and 324 are not optimized.
- **Pinning.** The success predicate pins the output distribution, not the sample path, and `Convergence` remains an existential statement about the specified SGD. It therefore does not formally tie the horizon T to the call count; the direct bound for every T > 0 is `Hyp.expected_gap`.
- **Computer assistance.** The proof was found with computer assistance. Small cases of the deterministic weight identities were checked in exact rational arithmetic before formalization. Every step, including the independence and integrability arguments, is proved in Lean without `sorry` or extra axioms.
