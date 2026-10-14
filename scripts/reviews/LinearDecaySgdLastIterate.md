# Linear-decay SGD under variance at the optimum: novelty assessment

The [theorem](../../LongTails/Theorems/LinearDecaySgdLastIterate.lean) proves the following. Take plain SGD ([algorithm](../../LongTails/Algorithms/LinearDecaySgd.lean)) with steps η_k = η(T−k)/T, where η = R/(8LR + σ√T). Run it for T = ⌈48LR²/ε + 324σ²R²/ε²⌉ i.i.d. sample-gradient calls. Its **last iterate** then satisfies E f(x_T) − f(x\*) ≤ ε whenever f = E F_ξ on a real Hilbert space, every F_ξ is convex with an L-Lipschitz gradient, ‖x₀ − x\*‖ ≤ R, and E‖∇F_ξ(x\*)‖² ≤ σ² ([setup](../../LongTails/Setups/SampledSmoothConvex.lean)). No uniform variance bound is assumed.

**Proved complexity.** L is the per-sample smoothness constant, R the initial distance, σ² a bound on the gradient variance at x\*, and ε the expected objective gap:

  T = O(LR²/ε + σ²R²/ε²) calls, with no logarithm (T = 0 when R = 0).

The steps need L, R, σ and T. The underlying bound, `Hyp.expected_gap`, is 3‖x₀−x\*‖²/(ηT) + 6ησ² for Lη ≤ 1/8. At σ = 0 it gives O(LR²/ε).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Sebbouh–Gower–Defazio, [arXiv:2006.07867](https://arxiv.org/abs/2006.07867) v2 (COLT 2021), Thm G.1 / Cor. G.2, stochastic heavy ball (SHB-IMA). Same assumptions in ℝᵈ (Assumption 1.1, σ² from Def. 1.2) | Constant η_k = min(1/(4L), R/(σ√(T+1))) gives 4LR²/(T+1) + 3σR/√(T+1), i.e. O(LR²/ε + σ²R²/ε²) → O(LR²/ε + σ²R²/ε²) | None: same order | ℝᵈ → separable Hilbert space. This is minor, since neither proof uses the dimension | None: both bound the last query point of their method, and both need L, R, σ, T | Plain SGD instead of heavy ball with varying momentum. SHB's x_T is an online average of its z-iterates |
| Attia–Schliserman–Sherman–Koren, [arXiv:2507.11274](https://arxiv.org/abs/2507.11274) v2 (NeurIPS 2025), Thm 2. Plain SGD with a tuned constant step, same class in ℝᵈ | At least O(LR²/ε·log(2+LR²/ε) + σ²R²/ε²·log(2+σR/ε)) → O(LR²/ε + σ²R²/ε²) | Θ(log) fewer calls whenever LR²/ε or σR/ε is large. At σ = 0 the gain is a log factor over their Thm 1(ii) | ℝᵈ → Hilbert (minor) | None: both use known L, R, σ*, T and bound the last iterate | Linear-decay schedule instead of a constant step |
| Garrigos–Cortild–Ketels–Peypouquet, [arXiv:2507.14122](https://arxiv.org/abs/2507.14122) v1, Thm 3.1 + Remark 3.8 tuning. Plain SGD, same class | Same order as Attia et al., with a log in each term → O(LR²/ε + σ²R²/ε²) | Θ(log) fewer calls, same regime as above | None: same Hilbert-space class | None | Their Cor. 3.4 step 1/(CL√T) needs no σ, but its rate is not optimal under interpolation |
| Liu–Zhou, [arXiv:2312.08531](https://arxiv.org/abs/2312.08531) v4 (ICLR 2024), Thm 3.4. Linear-decay SGD under a **uniform** variance bound σ_u² ≥ sup_x E‖g−∇f(x)‖² | O(LR²/ε + σ_u²R²/ε²) → O(LR²/ε + σ²R²/ε²) | None at equal noise. Since σ\* ≤ σ_u, σ_u²/σ² fewer calls on the overlap | Uniform variance → variance only at x\*. This covers, e.g., least squares with random design, where σ_u = ∞. The classes are incomparable | None | Requires per-sample convexity and smoothness, which Liu–Zhou do not. No composite term, constraints, or high-probability bound |

**Reduction check.** Liu–Zhou's Thm 3.4 cannot simply be substituted, because the transfer E‖∇F_ξ(x)‖² ≤ 4L(f(x)−f\*) + 2σ\*² puts a gap term at the current iterate. Absorbing that term into Zamani–Glineur-type weights costs a factor ∏(1 + c_s/S_s). This factor is T^{O(Lη)} for constant steps (Garrigos Thm 3.1; Attia Thm 2), and the selected proof shows it stays below 16/7 under linear decay, because η_s²/S_s ≤ 2η/T. That short observation is the only new mechanism. Proof ancestry: Zamani–Glineur reference points, the linear-decay schedule as used by Liu–Zhou, and the variance transfer from Garrigos et al. and Attia et al. Averaged SGD reaches the same order, but only for an averaged output (Attia App. B).

**Search coverage.** I searched on 2026-10-07: arXiv, NeurIPS/COLT pages, and forward citations of Attia, Garrigos, and Liu–Zhou. I also checked Vaidyan et al. ([arXiv:2602.05489](https://arxiv.org/abs/2602.05489), Thm 3.1: proximal SGD, ln T rate) and Kornowski–Shamir ([arXiv:2604.13870](https://arxiv.org/abs/2604.13870); Lipschitz setting, anytime lower bounds). I read the theorem statements for all table rows. Attia's tuned display extracted poorly from the PDF, so I give only a lower bound for its log power. Schedule-Free SGD and other momentum variants were not checked under σ\*. The result entered the repository in commit d5e463c on 2026-10-01, and all table rows predate it. The companion note cites its sources accurately. However, it omits Sebbouh et al. Its claim that averaged SGD is the only log-free alternative under σ\* is therefore wrong: SHB already gives a log-free last iterate.

## Conclusion

**The total complexity does not improve: a log-free last-iterate rate for this problem class was already known, and the new result proves it for plain SGD.**

The strongest baseline is Sebbouh–Gower–Defazio's stochastic heavy ball (COLT 2021, Thm G.1). It uses the same per-sample convex, L-smooth, variance-at-optimum assumptions, one sample gradient per step, and a known horizon. Its last iterate already reaches the same order:

| method | last-iterate calls |
|---|---|
| SHB, constant tuned η (Sebbouh et al.) | O(LR²/ε + σ²R²/ε²) |
| plain SGD, constant step (Attia et al.; Garrigos et al.) | O(LR²/ε·log + σ²R²/ε²·log) |
| plain SGD, linear decay (this theorem) | O(LR²/ε + σ²R²/ε²) |

The theorem therefore removes the logarithm for plain SGD and answers the question raised in Garrigos et al.'s Remark 3.6 and Attia et al.'s open problems for a tuned, known-horizon schedule. Against the best applicable method, it changes neither the rate, the information required, nor the problem class; the Hilbert-space generality is cosmetic. I found no earlier log-free plain-SGD bound under σ\* alone, but that search does not establish priority.

What can be claimed is a short, likely new analysis showing that linear decay lets plain SGD's last iterate match the best known σ\*-only complexity, not a faster method for this problem class.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
