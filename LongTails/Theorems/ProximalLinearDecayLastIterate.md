# Log-free last iterate of proximal SGD with linear decay under variance only at a minimizer

The [main theorem](ProximalLinearDecayLastIterate.lean) is a last-iterate guarantee for proximal stochastic gradient descent with the horizon-dependent linear-decay schedule on composite convex objectives. It assumes only per-sample convexity and smoothness of the sampled losses, a proper convex lower semicontinuous regularizer accessed through an exact proximal oracle, and a bound on the variance of the sampled gradient at one minimizer. The resulting rate O(LR²/T + σR/√T + Δ/T) has no logarithmic factor.

Averaged proximal SGD already attains this order. The claim concerns the last iterate of this specific method only; it is not an improvement of the oracle complexity of the problem class.

**Basis for this contribution.** The log removal rests on the mechanism of the repository's unconstrained theorem [LinearDecaySgdLastIterate](LinearDecaySgdLastIterate.lean) (unpublished internal prior): the Zamani–Glineur reference-point weights absorb the per-step gap term, and the linear-decay schedule keeps the absorbed product bounded. The present theorem is the composite extension of that mechanism. The user instructed the agents to proceed with it on the basis that it is a new theoretical rate that resolves a gap stated in the literature, overriding the Reviewer's objection that the extension is routine and lies outside the session's orthogonality steer.

## Setup and proved guarantee

The [setup](../Setups/SampledCompositeSmoothConvex.lean) has the following ingredients.

- **Space.** E is a real Hilbert space (complete, Borel, second countable).
- **Samples.** Each sample ξ from a probability space (Ξ, p) carries a loss F_ξ : E → ℝ. Each F_ξ is convex, has a gradient ∇F_ξ(x) at every point, and that gradient is L-Lipschitz. (ξ, x) ↦ ∇F_ξ(x) is jointly measurable, and every F_·(x) is integrable. The smooth part is f(x) = ∫ F_ξ(x) dp(ξ).
- **Regularizer.** A convex closed set Q ⊆ E and a real-valued lower semicontinuous ψ : E → ℝ that is convex on Q. The pair represents the proper convex lsc regularizer h = ψ + ι_Q of Vaidyan–Friedlander–Alacaoglu; indicator-type constraints enter through Q. The composite objective is Φ = f + ψ on Q.
- **Prox oracle.** For a > 0 and z, g ∈ E, prox(a, z, g) ∈ Q minimizes u ↦ ‖u − z‖²/(2a) + ⟨g, u − z⟩ + ψ(u) over Q, i.e. prox(a, z, g) = prox_{a h}(z − a g). This is the modeling of [CompositeGeneralizedSmooth](../Setups/CompositeGeneralizedSmooth.lean). Nonexpansiveness of the prox is derived from this characterization, not assumed.
- **Minimizer and public bounds.** x₀ ∈ Q, and there is x* ∈ Q minimizing Φ over Q with

  ‖x₀ − x*‖ ≤ R,  Φ(x₀) − Φ(x*) ≤ Δ,  ∫ ‖∇F_ξ(x*) − ∇f(x*)‖² dp ≤ σ².

  The last bound is the variance of the sampled gradient at x*; it is implied by the second-moment bound ∫‖∇F_ξ(x*)‖² dp ≤ σ² used by Vaidyan–Friedlander–Alacaoglu, and it is strictly weaker in the composite case because ∇f(x*) need not vanish. Nothing else is assumed: no uniform variance bound, no bounded domain, no Lipschitz regularizer, no bounded gradients, no strong convexity.

**Oracle.** The oracle answers two kinds of queries, and the query type alone determines the reply: a gradient query at a point x is answered by ∇F_{ξ_k}(x), where k is the call index and the ξ_k are i.i.d. with law `Measure.infinitePi` of p; a prox query (a, z, g) is answered by the exact prox(a, z, g). Both kinds are counted. Since the algorithm alternates the two kinds, its gradient calls are the even-indexed calls and the samples it uses, ξ₀, ξ₂, …, are i.i.d.; this interleaving is a property of the execution, proved in the execution module, not a restriction on the oracle. The public data are L, R, Δ, σ, ε and x₀.

**Algorithm.** The [algorithm](../Algorithms/ProximalLinearDecaySgd.lean) runs proximal SGD, x_{k+1} = prox(η_k, x_k, ∇F_{ξ_k}(x_k)), with one gradient call and one prox call per iteration. The schedule is

  η_k = η (T − k)/T,  η = R / (8LR + σ√T),  k = 0, …, T − 1.

The output is the last iterate x_T. The public budget is the one-line formula

  budget = 2 · ⌈72 L R²/ε + 900 σ² R²/ε² + 6 Δ/ε⌉

oracle calls (T iterations, two calls each), and the theorem proves E Φ(x_T) − Φ(x*) ≤ ε. Before tuning, the proof gives

  E Φ(x_T) − Φ(x*) ≤ 3‖x₀ − x*‖²/(ηT) + 7ησ² + 2Δ/T   whenever Lη ≤ 1/8.

With the stated η this becomes 24LR²/T + 10σR/√T + 2Δ/T.

**Interpolation.** When σ = 0, this is a log-free O(LR²/T + Δ/T) last-iterate bound.

**Pinning the algorithm.** `allowedAlgorithm` requires the algorithm to be `proximalLinearDecaySgd η T x₀` for some η ≥ 0 and horizon T, so the statement is about the last iterate of this method, with the explicit schedule and the explicit η above.

**Lean layout.**
- [ProximalLinearDecayStep](../Proofs/ProximalLinearDecayStep.lean): prox three-point inequality on Q, nonexpansiveness, the minimizer inequality and gap transfer on Q, the second-moment transfer, and the one-sample inequality.
- [ProximalLinearDecayWeights](../Proofs/ProximalLinearDecayWeights.lean): deterministic weight algebra, the potential recursion and bound, and the tuning bound.
- [ProximalLinearDecayExpectation](../Proofs/ProximalLinearDecayExpectation.lean): measurability and integrability along the trajectory, independence of the fresh sample, the step, Jensen and anchor bounds, and the expected-gap theorem.
- [ProximalLinearDecayExecution](../Proofs/ProximalLinearDecayExecution.lean): the algorithm's execution equals the explicit path, with 2T calls.
- [ProximalLinearDecayConvergence](../Proofs/ProximalLinearDecayConvergence.lean): the final convergence statement.

## Mechanism

Write Φ for the composite objective, a_k = E Φ(x_k) − Φ*, S_k = Σ_{j≥k} η_j, and c_k = 2Lη_k²(1 + 2Lη_k).

1. **Three-point inequality.** For v = prox(a, z, g) and any u ∈ Q, ψ(v) + ⟨g, v − u⟩ ≤ ψ(u) + (‖u − z‖² − ‖u − v‖² − ‖v − z‖²)/(2a), from the strong convexity of the prox objective and its minimality on the convex set Q.
2. **Gap transfer on Q.** From the optimality of x* on Q, ψ(y) − ψ(x*) + ⟨∇f(x*), y − x*⟩ ≥ 0 for y ∈ Q, so the Bregman distance D_f(x, x*) is at most Φ(x) − Φ(x*). Co-coercivity of each F_ξ then gives ∫‖∇F_ξ(x) − ∇f(x)‖² dp ≤ 4L(Φ(x) − Φ*) + 2σ² on Q.
3. **One step.** Combining smoothness and convexity of f with the three-point inequality, for any past-measurable y ∈ Q,

   Φ(x_{k+1}) ≤ Φ(y) + (‖x_k − y‖² − ‖x_{k+1} − y‖²)/(2η_k) + ⟨∇f(x_k) − g_k, x_k − y⟩ + (η_k/(2(1 − Lη_k)))‖∇f(x_k) − g_k‖².

   The cross term through the prox is handled by splitting ⟨∇f(x_k) − g_k, x_{k+1} − y⟩ into a mean-zero part and ⟨∇f(x_k) − g_k, x_{k+1} − x_k⟩, which Young's inequality with parameter η_k/(1 − Lη_k) absorbs exactly against the −(1/(2η_k) − L/2)‖x_{k+1} − x_k‖² term. Taking expectations and using step 2,

   E Φ(x_{k+1}) − E Φ(y) ≤ (E‖x_k − y‖² − E‖x_{k+1} − y‖²)/(2η_k) + (c_k/η_k) a_k + η_k(1 + 2Lη_k)σ².
4. **Reference points.** Following Zamani–Glineur, take y = z_k, a convex combination of x* and the past iterates, with weights v_0 = 1 and v_{k+1}(S_{k+1} + c_{k+1}) = v_k S_k that also absorb the gap term. The potential v_k S_k (E Φ(z_k) − Φ*) + v_k c_k a_k + (v_k/2)E‖x_k − z_k‖² grows only by the noise term at each step.
5. **The price.** Absorbing the gap costs Γ = Π_s(1 + c_s/S_s). Under linear decay η_s²/S_s ≤ 2η/T uniformly, so Σ_s c_s/S_s ≤ 5Lη ≤ 5/8 and Γ ≤ 8/3 is a horizon-free constant. With constant steps the same product grows like a power of T, which is the logarithmic or polynomial loss in the constant-step analyses.
6. **Initial gap.** Unlike the unconstrained case, Φ(x₀) − Φ(x*) is not bounded by LR²/2 (the regularizer contributes), so the public bound Δ enters through the lower-order term 2Δ/T and the budget, exactly as the term (h(x₀) − h*)/T in Vaidyan–Friedlander–Alacaoglu's bound.

The constants were re-derived independently by the Reviewer. Every step is proved in Lean without `sorry` or extra axioms.

## Comparison with prior results

| Result | Method | Noise assumption | Last-iterate bound |
|---|---|---|---|
| Vaidyan, Friedlander, Alacaoglu, [arXiv:2602.05489](https://arxiv.org/abs/2602.05489) (Feb 2026), Thm 3.1 | proximal SGD, constant τ = 1/(3L√T) | second moment at a minimizer σ*² | (9/√T)[L D*² + (h(x₀) − h*)/√T + (σ*²/L)(1/T + 4 ln(T+1))] |
| Liu and Zhou, [arXiv:2312.08531](https://arxiv.org/abs/2312.08531) (v4) | composite SGD, linear decay | uniform variance σ² | O(1/T + σ/√T), log-free |
| Garrigos, Cortild, Ketels, Peypouquet, [arXiv:2507.14122](https://arxiv.org/abs/2507.14122) | unconstrained SGD | variance at a minimizer | O(ln T/√T) |
| Attia, Schliserman, Sherman, Koren, [arXiv:2507.11274](https://arxiv.org/abs/2507.11274), Thm 2 | unconstrained SGD | variance at a minimizer | logarithmic factors |
| [LinearDecaySgdLastIterate](LinearDecaySgdLastIterate.lean) (this repository, unpublished) | unconstrained SGD, linear decay | variance at a minimizer | 24LR²/T + 9σR/√T |
| **this theorem** | proximal SGD, linear decay | variance at a minimizer | 24LR²/T + 10σR/√T + 2Δ/T |
| averaged proximal SGD (standard) | proximal SGD, averaged output | variance at a minimizer | same order; not a last-iterate result |

The stated gap. Vaidyan, Friedlander and Alacaoglu write in their Conclusions that their rate "is ln(T+1) away from the optimal rate that is only known with bounded variance." This theorem removes exactly that ln(T+1) under exactly their assumptions on the smooth part and the regularizer, for the same quantity (the composite gap at the last iterate), with the variance at a minimizer in place of the second moment. Their proximal extension is stated by them not to follow directly from the unconstrained analyses; here the composite step is handled by the three-point inequality and the gap transfer on Q.

## Scope and limitations

- **Known horizon and known bounds.** The schedule needs the horizon T and the public bounds L, R, σ and Δ, as do the constant step of Vaidyan–Friedlander–Alacaoglu and the internal unconstrained theorem. Log-free last-iterate rates for constant steps and for anytime schedules remain open.
- **Positive radius.** The setup requires R > 0. This costs nothing: R is only an upper bound on ‖x₀ − x*‖, so every instance, including x₀ = x*, is admissible with any R > 0. The value R = 0 is excluded only because it would make the step zero, and the prox oracle is specified only for positive parameters.
- **Constants.** The constants 72, 900 and 6 are not optimized.
- **Real-valued ψ on Q.** Extended-valued regularizers are represented by the pair (ψ, Q); ψ is required to be lower semicontinuous (as h is proper, convex and lsc in the source) so that Φ(x_k) is measurable.
- **Pinning.** The success predicate pins the output distribution, not the sample path, and `Convergence` remains an existential statement about the specified method. The direct bound for every T > 0 is `expected_gap`.
- **Not a class-complexity claim.** Averaged proximal SGD attains the same order; the contribution is the last-iterate guarantee for this method.
