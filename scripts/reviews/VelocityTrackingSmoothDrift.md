# Velocity-tracking SGD under smooth minimizer drift: novelty assessment

[`result`](../../LongTails/Theorems/VelocityTrackingSmoothDrift.lean) proves the following. Let `f_k` be μ-strongly convex, L-smooth functions on a Hilbert space whose shape may change arbitrarily with k. Each step makes one unbiased stochastic-gradient call to the current `f_k`, with variance at most σ² uniformly in x. The deterministic minimizers satisfy `‖x₀−x*₀‖ ≤ R`, `‖x*₁−x*₀‖ ≤ V` and second differences at most Γ. Under these conditions, the [velocity-tracking method](../../LongTails/Algorithms/VelocityTrackingSgd.lean) (`y=x+v`, `x⁺=y−γg`, `v⁺=v−βg`) satisfies `E‖x_N − x*_{N−1}‖² ≤ ε` at every N past the budget ([setup](../../LongTails/Setups/SmoothDriftStronglyConvex.lean)).

**Complexity.** Write κ = L/μ, ε for the target mean-square error, and H ≥ 0 for free slack. The budget is

  N = O( (κ + σ²/(μ²ε)) · log(2 + (R² + V²(κ + σ²/(μ²ε))²)/ε) ) + H.

It holds whenever 9792 Γ² (2κ + 99σ²/(μ²ε))⁴ ≤ ε, that is, ε ≳ (Γ²σ⁸/μ⁸)^{1/5} + κ⁴Γ². Updates use only μ, L, σ and ε, not Γ, R or V. Every N above the budget succeeds. Γ = 0 (constant velocity) allows every ε > 0.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Cutler–Drusvyatskiy–Harchaoui, [JMLR 24(147), 2023](https://arxiv.org/abs/2108.07356) v4, Thm 3 (constant step) and Thm 4/Thm 28 (step decay). SGD with `E‖x*_t−x*_{t+1}‖² ≤ Δ²`. Overlap: paths with speed ≤ Δ, hence V ≤ Δ and Γ ≤ 2Δ. | `O(κ log(R²/ε) + σ²/(μ²ε))`, valid only for ε ≳ (Δσ²/μ²)^{2/3} + κ²Δ² + σ²/(μL) → `O((κ+σ²/(μ²ε)) log(2+(R²+Δ²(κ+σ²/(μ²ε))²)/ε))`, valid for ε ≳ (Γ²σ⁸/μ⁸)^{1/5} + κ⁴Γ² | **Worse** where both apply: the bounds agree up to a log factor on the σ²/(μ²ε) term, which step decay avoids. **Gain** in reachable accuracy when (Γ²σ⁸/μ⁸)^{1/5} + κ⁴Γ² ≪ ε ≪ (Δσ²/μ²)^{2/3}. In that range the SGD bound is vacuous, and constant-step SGD provably stalls: on 1-D x*_t = Δt, its limiting error is ≥ ¼(Δσ²/μ²)^{2/3} when Δ ≤ σ/μ (I checked the note's recursion). | The classes are incomparable. This result covers paths with unbounded speed (V + kΓ), which no speed-bounded SGD bound handles. It loses random drift with second-moment bounds. | None; both need μ, L, σ and ε, and both certify the current iterate. | Variance must be uniform in x (CDH uses noise along iterates). The path must be deterministic. If Γ ≈ Δ, the domain shrinks: it needs ε ≳ κ⁴Δ² rather than κ²Δ². |
| Moulines–Priouret–Roueff, [Ann. Statist. 33(6), 2005](https://arxiv.org/abs/math/0603047), Thm 8 / Cor. 9. Romberg combination of two NLMS chains; time-varying AR (linear regression), θ(·) ∈ C^β with 1 < β ≤ 2. **Special case (quadratic losses only).** | Gives the minimax rate n^{−2β/(1+2β)} = n^{−4/5} at β = 2 (in-fill asymptotics, unspecified constant M, after a burn-in of a fixed fraction of n). Our floor (σ²/μ²)^{4/5}Γ^{2/5} with Γ ∝ n⁻² has the **same exponent**. | Not comparable: MPR gives no explicit call bound. On the common scaling the floor exponents match. | Quadratic loss with smoothly varying Σ(t) → general strongly convex f_k with arbitrarily changing Hessians. | Asymptotic, non-explicit constants → explicit finite-time bound | MPR allows multiplicative (random-design) noise, which is outside the uniform-variance oracle here. MPR needs two gradient chains per sample. |
| Kamijima–Marumo–Takeda, [arXiv:2512.15205](https://arxiv.org/abs/2512.15205) v1 (Dec 2025, preprint), Thm 4.4 / 5.5. Polynomial-extrapolation prediction plus correction. | `lim sup E‖x̂_k−x*_k‖` (first moment) needs every sample loss to be strongly convex and an inner solver contracting toward each **sample** minimizer (Assm 4.1a). The h^{q/(2q+1)} rate needs unbiased sample minimizers. | Not comparable: it uses a stronger sample-function oracle with many inner gradients and has no call count. | Removes per-sample strong convexity, the sample-minimizer bias condition and repeated inner solves. | lim sup of the first moment → finite-time mean square | KMT bounds gradient variance only at x*_k, not uniformly in x. KMT allows a convex regularizer ψ; this result does not. |

**Reduction check.** The floor exponent for second-order-smooth drift is not new: MPR's Richardson extrapolation and classical α–β/Kalman trackers achieve it for linear models. I found no verified reduction to the Lean class, because the Romberg cancellation needs a lag term `(μn)⁻¹Σ⁻¹θ̇` with slowly varying Σ, and here the Hessians change arbitrarily between steps. The new mechanism is the κ-uniform quadratic Lyapunov certificate `lyap_contract` for the undamped integrator under time-varying sector-bounded gradients. The proof ancestry is SGD tracking (CDH) plus co-coercivity.

**Search coverage (2026-10-16).** I searched arXiv and journal sources and read CDH Thm 3/4, MPR Thm 7–8/Cor 9 and KMT Assm 2.1/4.1/Thm 4.4. Sahu–Hogan–Wells ([arXiv:2601.12238](https://arxiv.org/abs/2601.12238) v5, ICML 2026) and Sarkar–Mandal–Wells ([arXiv:2610.16923](https://arxiv.org/abs/2610.16923), 12 Oct 2026, four days before commit 5ae97cd) treat only first-order drift. I could not access full texts for Delyon–Juditsky (SICON 1995, asymptotically optimal tracking for linear regression), Benveniste (1987), Popkov (2005) or Kosaty et al. (ACC 2019, Nesterov-type stochastic tracking). The companion note omits MPR, which is the closest prior rate-matching result. The note's minimax floor is a paper proof and is not formalized.

**Conclusion**

**It covers meaningful new instances, but where SGD applies it is no faster.** The strongest baseline is SGD tracking (Cutler–Drusvyatskiy–Harchaoui 2023), whose guarantee requires bounded minimizer speed Δ:

| | reachable ε | calls |
|---|---|---|
| SGD (CDH) | ≳ (Δσ²/μ²)^{2/3} + κ²Δ² | κ log(R²/ε) + σ²/(μ²ε) |
| This result | ≳ (Γ²σ⁸/μ⁸)^{1/5} + κ⁴Γ² | (κ + σ²/(μ²ε))·log(2 + (R² + V²(κ+σ²/(μ²ε))²)/ε) |

The gain is reachable accuracy. When the minimizer's acceleration Γ is much smaller than its speed Δ, accuracies below SGD's floor become attainable, and with Γ = 0 every accuracy is attainable. Paths with growing speed also become trackable. The cost is one stochastic gradient per step and a log factor; constant-step SGD provably cannot reach these accuracies. When Γ ≈ Δ, or when both methods' domains already contain ε, SGD is as good or better by a log factor.

The h^{4/5}-type floor itself is classical for linear models (Moulines–Priouret–Roueff 2005), so the exponent is not new. What appears new is a finite-time, explicit guarantee for general strongly convex objectives with arbitrarily changing shape, using one unbiased gradient per step. It assumes variance uniform in x, which excludes random-design least squares. Inaccessible classical tracking texts leave priority somewhat uncertain.

The contribution that can be claimed is a non-asymptotic extension of velocity-based tracking to nonlinear, shape-varying strongly convex objectives, giving sub-SGD-floor accuracy on smooth drift.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
