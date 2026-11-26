# Novelty assessment: restarted accelerated dual averaging with quadratic weights under total-gap curvature

[`CompositeGapQuadraticWeights.result`](../../LongTails/Theorems/CompositeGapQuadraticWeights.lean) ([setup](../../LongTails/Setups/CompositeGapSmooth.lean), [algorithm](../../LongTails/Algorithms/CompositeGapQuadraticWeights.lean)) works on a Hilbert space. Here f is globally convex and differentiable, ψ is convex on a convex set Q, and the model f(y) ≤ f(x) + ⟨∇f(x), y−x⟩ + (H₀ + H₁(F(x)−F⋆))‖y−x‖² holds for x ∈ Q and ambient y with √H₁‖y−x‖ ≤ 1. Under these conditions, the method deterministically returns a final point x̂ ∈ Q with F(x̂) − F⋆ ≤ ε, using exact gradient and exact Q-constrained prox calls.

**Proved budget** (total gradient plus prox calls; Lean constants 32(2+√2) and 85):

  O( R√(H₀/ε) + (1 + R√H₁) · log(2 + Δ/ε) ),

where R ≥ ‖x₀ − x⋆‖, Δ ≥ F(x₀) − F⋆, H₀, H₁ ≥ 0, and R, Δ, ε > 0. All five parameters are known and used both in the updates and in the phase lengths. The budget has no dimension factor and uses no function values. For Δ ≤ ε it is O(1), and the output is x₀.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lobanov–Dvinskikh–Gasnikov, [arXiv:2609.33415v1](https://arxiv.org/abs/2609.33415) (27 Sep 2026, preprint, prior), Thm 9 at zero noise. **Only for ψ ≡ 0, Q = ℝᵈ**; Q there is an auxiliary projection set of diameter D, so choosing the ball B(x₀, R) gives D = 2R | O(log(Δ/ε) + R√(H₀/ε) + R√H₁·min{log(Δ/ε), log⁺(H₁Δ/H₀)}), times a hidden log(1/ρ) → O(R√(H₀/ε) + (1+R√H₁)log(2+Δ/ε)) | None: same order. The extra R√H₁ log terms where H₁ ≤ H₀/d_k are dominated by the geometric √(H₀/d_k) sum, and the confidence log disappears in the deterministic case | Smooth unconstrained f → composite f + ψ over convex Q (ψ nonsmooth, ∇f(x⋆) ≠ 0 allowed) | None (both final iterate) | Exact oracles only. Thm 9 also handles heavy-tailed stochastic gradients |
| Lobanov, [arXiv:2608.04884v1](https://arxiv.org/abs/2608.04884) (5 Aug 2026, preprint, prior), Thm 5. **Only for ψ ≡ 0, Q = ℝᵈ** | O(R̃√(H₀/ε) + R̃√H₁ log(F₀/ε)), with R̃ the radius of the initial sublevel set (≥ R) → this result | None in general. Better on the overlap only when R̃ ≫ R | Same scope gain as above | None | Lobanov also needs F₀ known, plus an exact segment search per iteration; this result does not |
| Repository [CompositeGapAccelerated](../../LongTails/Theorems/CompositeGapAccelerated.lean) (commit 0dc2692, 2026-10-26; same spec; not literature) | O((1+R√(H₀/ε+H₁))·log(4+R²(H₀/ε+H₁))·log(2+Δ/ε)) → this result | Removes log(4+R²H₀/ε)·log(Δ/ε) from the accuracy term and log(4+R²H₁) from the H₁ term. For fixed H₀, R, Δ and ε→0, this is ε^{−1/2}log²(1/ε) → ε^{−1/2}. The new bound is never larger (companion-note argument, checked) | None (identical spec) | None | None found |

**Reductions and mechanism.** No standard reduction gives the composite bound. The smooth-only theorems above need differentiable F, and with Q = E. There is no global Lipschitz constant for ∇f: in the example below the Hessian is unbounded. As a result, ordinary FISTA or restarted FISTA with fixed L_k = H₀ + H₁d_k needs to show that its extrapolation points stay inside the local model's region. That is exactly what the proof establishes, as follows.

- With quadratic weights a_i = i/(128M), center distances grow at most linearly in n.
- The gap of the composite at extrapolation points is controlled through the cumulative prox model, J(z) ≤ d + K_nG, yielding F(y) − F⋆ ≤ 10d.
- The step ‖x′ − y‖ ≤ ρ is bounded before the model at y is invoked. Summing the phases geometrically then removes both logarithms.

Proof ancestry: Xiao's accelerated regularized dual averaging ([JMLR 2010](https://jmlr.org/papers/v11/xiao10a.html), §7, quadratic weights) supplies the energy algebra under global smoothness. Geometric gap-halving restarts with a √(H₀/d_k) sum follow Lobanov's Thm 5 and LDG's eq. (44). The new work is the localization step that allows nonsmooth ψ, together with a single fixed initial distance R. I did not audit the Lean proofs or run the build or comparator.

**Example (composite instance not covered by the smooth-only rows).** Take f = 2e^{δy}cosh x, ψ = |x| + 2δ|y|, x₀ = (0, 1/δ), with small δ. The minimizer is x⋆ = (0, 0), since 0 ∈ ∇f(0) + ∂ψ(0). For δ ≤ 0.3, ‖∇²f‖ ≤ 2f, and log f is √(1+δ²)-Lipschitz. Within radius e^{−1/2}, therefore, curvature is at most 2e·f(x) ≤ 2e(F(x)−F⋆+2), so H₀ = 2e and H₁ = e. With R = 1/δ and Δ = 2e, the budget is O(δ⁻¹ε^{−1/2} + δ⁻¹log(1/ε)). F is nonsmooth, ∇f(x⋆) ≠ 0, and ∇²f is unbounded on the R-ball around x⋆ (it grows like cosh(1/δ)), so neither the smooth-only gap results nor a global-L FISTA analysis applies.

**Search coverage.** On 2026-11-26 UTC I checked the setting and complexity sections of 2609.33415v1 and 2608.04884v1. Their Thm 9 and Thm 5 statements came through a fetched extraction and were not read verbatim from the PDFs. I also ran arXiv and web searches for composite, proximal, or constrained acceleration under gap-dependent (H₀,H₁)-smoothness. These found nothing beyond 2609.06555 (gradient-dependent smoothness) and unrelated Hölder or Wasserstein prox methods. I did not re-read Lu–Mei's local-Lipschitz APG (arXiv:2206.01209) or the full 2026 proceedings. The result was introduced in commit 9e4d973 on 2026-11-26, after both preprints. The companion note's descriptions of these sources match what I read. Its "strictly smaller for every valid parameter" claim is relative only to the repository sibling.

## Conclusion

**This result is not faster than the literature on smooth problems; what is new is that the smooth-only gap-curvature rate now holds for composite and constrained problems.**

The strongest prior guarantees, Lobanov's Thm 5 and Lobanov–Dvinskikh–Gasnikov's Thm 9, cover only unconstrained smooth f. On that overlap, all three bounds have the same order:

| | gradient + prox calls |
|---|---|
| 2609.33415 / 2608.04884 (ψ = 0, Q = ℝᵈ) | O(R√(H₀/ε) + R√H₁ log(Δ/ε)) (up to log(Δ/ε), log(1/ρ) or R̃ vs R) |
| repository sibling (same composite spec) | O((1+R√(H₀/ε+H₁)) log(4+R²(H₀/ε+H₁)) log(Δ/ε)) |
| this result (any convex ψ, Q) | O(R√(H₀/ε) + (1+R√H₁) log(2+Δ/ε)) |

The repository sibling already extended gap-curvature acceleration to composite problems, but it lost about a log²(1/ε) factor. This theorem removes that loss, so the composite extension carries no rate penalty. The checked exponential-plus-ℓ₁ example shows nonsmooth composite instances with bounded gap constants, where the smooth-only theorems do not apply.

The comparisons establish the scope gain and the log removal. Priority is plausible but uncertain: no composite gap-curvature work turned up, the field is moving quickly, and part of the scope credit belongs to the unpublished sibling. What can be claimed is the first checked accelerated composite or constrained guarantee under total-gap curvature that matches the best smooth-only rate, using only gradient and prox calls.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
