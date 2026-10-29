# Novelty assessment: gradient-only quasar acceleration with logarithmic confidence

The [theorem](../../LongTails/Theorems/GradientOnlyQuasarHighProbability.lean) works in any finite-dimensional Euclidean space. For a γ-quasar-convex function (relative to one attained minimizer x⋆) with continuous gradient that satisfies the symmetric (L₀,L₁) condition, the [randomized continuized method](../../LongTails/Algorithms/GradientOnlyQuasar.lean) uses only exact gradients and a fixed number of calls, and its last primal point satisfies P{f(y_K) − f(x⋆) > ε} ≤ δ ([setup](../../LongTails/Setups/GradientOnlyGeneralizedQuasar.lean)).

**Proved budget**, simplified from the Lean `budget` (`clog₂⌈4/δ⌉ ≍ log(1/δ)` since δ<1, and `clog₂⌈8Δ/ε⌉ ≤ 1 + log₂(1+8Δ/ε)`):

$$K = O\!\Big(\tfrac{1+\log(1/\delta)}{\gamma}\Big[1+\sqrt{L_0R^2/\varepsilon}+L_1R\big(1+\log(1+\Delta/\varepsilon)\big)\Big]\Big).$$

Here L₀ and L₁ are the generalized-smoothness constants, R ≥ ‖x₀−x⋆‖, Δ ≥ f(x₀)−f(x⋆), γ∈(0,1] is the quasar parameter, ε is the accuracy, and δ∈(0,1) is the failure probability. The algorithm must know L₀, L₁, R, Δ, γ, ε and δ. Write T = L₀R²/ε; when L₁=0 and T<1/2, the point x₀ is already ε-optimal.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Wang–Wibisono, [ICLR 2023](https://openreview.net/forum?id=yYbhKqdi7Hz), [arXiv:2302.07851v1](https://arxiv.org/abs/2302.07851) Thm 1 + Cor 1 (Markov + Chebyshev). *Applies only when L₁=0*; gradient-only | Choosing c₀=2/δ, c=1/2 gives O(γ⁻¹√(T/δ) + 1/δ) → O(γ⁻¹(1+log(1/δ))(1+√T)) | For T ≥ 1, a speedup of order δ^{-1/2}/(1+log(1/δ)), and never worse up to constants. This compares proved upper bounds, not a lower bound for their method | L-smooth → symmetric (L₀,L₁)-smooth | None: same information (Δ = L₀R²/2 is free when L₁=0) and the same high-probability last-iterate output | Uses Δ; very large constant (65536) |
| Hinder–Sidford–Sohoni, [COLT 2020](https://proceedings.mlr.press/v125/hinder20a.html), [arXiv:1906.11985v3](https://arxiv.org/abs/1906.11985) Thm 2. *Applies only when L₁=0*; uses **function values** + gradients | O(γ⁻¹√T·log₊(γ⁻¹√T)) deterministic → O(γ⁻¹(1+log(1/δ))(1+√T)) | Not comparable in oracle terms. In call counts, better iff 1+log(1/δ) ≪ log(√T/γ); worse for smaller δ | L-smooth → (L₀,L₁) | Worse output: a deterministic guarantee becomes failure probability δ | Advantage of this result: no function values or line search |
| Jin, [arXiv:2010.04937v3](https://arxiv.org/abs/2010.04937) eq. (12), σ=0, step 1/(2L), with monotone descent. *Applies only when L₁=0*; gradient-only GD | O(T/γ) deterministic → O(γ⁻¹(1+log(1/δ))(1+√T)) | Faster by order √T/(1+log(1/δ)) when log(1/δ) ≪ √T; worse when δ ≤ e^{−c√T} | L-smooth → (L₀,L₁) | Worse output: deterministic → probability δ | Randomized algorithm; needs known parameters |
| Kovalev, [arXiv:2605.15522v2](https://arxiv.org/abs/2605.15522) (May 2026 preprint) App. C, Thm 11/Cor 6. *Broader class* (stochastic, nonsmooth); applies here when L₁R ≳ 1, via ‖∇f‖ ≲ L₀/L₁ + L₁(f−f⋆) | Expected Õ(γ⁻⁶(L₁R)⁴ + γ⁻²(L₀R/(L₁ε))²); after Markov, Õ(γ⁻⁶(L₁R)⁴ + γ⁻²(L₀R/(L₁εδ))²) → this result | By AM–GM their bound is ≳ γ⁻⁴L₁R·T/δ, which dominates this result's bound up to log(1+Δ/ε) | None: their class is broader | Expected → high probability with log(1/δ) | Narrower class: exact gradients, smooth |
| Repository [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean). *Applies only when γ=1, f is convex, and the gradient is differentiable*; gradient-only | O(1+√T+(L₁R)^{2/3}log(1+Δ/ε)) almost surely → O((1+log(1/δ))(1+√T+L₁R log(1+Δ/ε))) | Worse on the convex overlap: extra factor 1+log(1/δ), and L₁R instead of (L₁R)^{2/3} | Convex → γ-quasar (nonconvex) | Worse: almost-sure → probability δ | — |

**Reduction check.** I looked for a standard reduction and found none that reproduces the bound. Independent repetition needs a selection rule. Without function values, comparing two candidates by integrating gradients along a segment costs Θ(L₀D²/ε) calls, which is the order of GD. Certifying through f−f⋆ ≤ ‖∇f‖R/γ needs a gradient-norm accuracy that costs more than √T. The new mechanism is the bounded p-th-power energy barrier with p ≍ log(1/δ), combined with a Chernoff bound on the clock. Proof ancestry: the continuized framework of Even et al. and Wang–Wibisono. Hermant et al. ([arXiv:2512.16533v2](https://arxiv.org/abs/2512.16533), Cor. 15) sharpen only the clock tail and keep a Markov 1/c₀ energy term.

**Search coverage.** Searches were run on 2026-10-28 and covered arXiv 2019–2026, COLT/ICLR/ALT/AISTATS proceedings, and forward citations of HSS and Wang–Wibisono. The deterministic quasar acceleration papers I found all rely on line or plane searches: Martínez-Rubio ([arXiv:2510.01943v3](https://arxiv.org/abs/2510.01943)), whose oracle I verified returns function values, plus Guminov–Gasnikov–Kuruzov and Lezane–Langer–Koolen (ALT 2026), whose oracle I did not check. Gbaguidi–Hermant ([arXiv:2607.19965](https://arxiv.org/abs/2607.19965)) is value-only, and I read only its abstract. Gorbunov et al. ([ICLR 2025](https://arxiv.org/abs/2409.14989)) Thm 3.3 covers only convex (L₀,L₁) problems. I did not read Ablaev et al. (2025), ProxBoost, or Bonnerjee–Ramdas; I relied on the note's description of them. The note's claim that HSS plus restarts already gives (L₀,L₁) acceleration with value access is unverified. The result was introduced in commit `1dbf4ea` (2026-10-28), so every source above predates it.

**Conclusion**

**Yes: with exact gradients only, the confidence cost drops from polynomial to logarithmic, and the guarantee extends to (L₀,L₁)-smooth quasar-convex objectives.** The strongest gradient-only baseline is Wang–Wibisono's Corollary 1, which covers only the case L₁=0:

| Gradient-only, L₁=0 | Calls |
|---|---|
| Wang–Wibisono | γ⁻¹√(L₀R²/(δε)) + 1/δ |
| This result | γ⁻¹(1+log(1/δ))(1+√(L₀R²/ε)) |

For L₀R²/ε ≥ 1 the new bound is never worse up to constants and is faster by a factor of about δ^{-1/2}/log(1/δ). It also beats deterministic GD, O(L₀R²/(γε)), when log(1/δ) ≪ √(L₀R²/ε). For L₁>0, the only applicable gradient-only bound I found (Kovalev's, after Markov) is polynomially worse.

The gain has limits. Hinder–Sidford–Sohoni's deterministic method, which uses function values, is cheaper once log(1/δ) exceeds log(√(L₀R²/ε)/γ). On convex instances, the repository's deterministic method improves L₁R to (L₁R)^{2/3} and has no confidence factor. The δ^{-1/2} comparison is against Wang–Wibisono's proved Markov-based bound, not a lower bound on their method.

I found no prior gradient-only accelerated quasar guarantee with log(1/δ) confidence, and no accelerated quasar guarantee under (L₀,L₁) smoothness. That absence does not prove priority. The claimable contribution is accelerated last-iterate high-probability convergence with exact gradients, logarithmic confidence overhead, and (L₀,L₁) curvature.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
