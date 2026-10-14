# Novelty assessment: gradient-only ε^{-3.5} for stochastic NC–SC minimax with Lipschitz Hessians

[`HessianNcsc.result`](../../LongTails/Theorems/HessianNcscImplicitTransport.lean) proves the following for the setup in [`StochasticHessianNcsc.lean`](../../LongTails/Setups/StochasticHessianNcsc.lean) on arbitrary finite-dimensional spaces E×F. Assume f is jointly L-smooth, μ-strongly concave in y, and has a ρ-Lipschitz joint Hessian. Each oracle call returns one fresh, unbiased joint stochastic gradient with variance ≤ σ². Then single-loop IGT-momentum normalized SGDA ([`igtSgda`](../../LongTails/Algorithms/HessianNcscIgt.lean)) uses exactly `budget` calls and returns a uniformly random iterate w_τ with E‖∇Φ(w_τ)‖ ≤ ε, where Φ(x) = max_y f(x,y).

**Proved complexity.** Write K = 1+L/μ. Here Δ bounds Φ(x₀) − inf Φ, and G bounds ‖∇_y f(x₀,y₀)‖. The formula below comes directly from `budget`, using √Q ≍ √(ρK/ε) + L/(ε+σ):

  N = O( K²(1+σ²/ε²)(1+ρεK/L²)·[ KΔ(√(ρK/ε) + L/(ε+σ))/ε + 1 + σ/ε + log(1 + G²ρK/(μ²ε) + G²L²/(μ²(ε+σ)²)) ] ).

For σ ≥ ε and ρεK ≤ L², this becomes O(K^{3.5}√ρΔσ²/ε^{3.5} + K³LΔσ/ε³ + K²σ³/ε³ + K²(σ²/ε²)·log(…)).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Wu et al., [arXiv 2610.00229v1](https://arxiv.org/abs/2610.00229), Thm 3.4 (preprint, 22 Sep 2026; prior). Same fresh-gradient oracle, but no Hessian assumption. | Õ(√κLΔ/ε² + κLΔσ²/ε⁴ + κ²σ²/ε² + √κ log₊(G/(ε√κ))), where κ = L/μ → N above | Noise term improves from ε^{-4} to ε^{-3.5}, a speedup of ≈ min{L/(κ^{2.5}√(ρε)), σ/(κ²ε), LΔ/(κσε)}. This holds when σ ≥ ε and ε ≲ min{L²/(ρκ⁵), σ/κ², LΔ/(κσ)}, up to universal constants (ours are ~10⁷) and Wu's logarithms. | None (ours covers a nested subclass) | Ours bounds E‖∇Φ‖. Wu bounds P(‖∇Φ‖ ≤ ε) ≥ 2/3. Markov at ε/3 converts ours to Wu's criterion at the same order, but not conversely. | Adds a ρ-Lipschitz Hessian, and ρ must be known. Worse in κ (κ^{3.5} vs κ). Deterministic part K³LΔ/ε² vs √κLΔ/ε² is worse by κ^{2.5}. Worse for moderate ε. |
| Cai–Alghunaim–Sayed, [arXiv 2406.13041v3](https://arxiv.org/abs/2406.13041), Thm 1 (HCMM-1; preprint) | O(ε^{-3}) for E‖∇P‖ (κ, σ, ρ dependence not tracked here) → N | Not comparable: it uses a stronger oracle | Removes their bounded-gradient assumption (Asm 5) | None | Their method also needs unbiased bounded-variance **stochastic Hessians**, which our oracle lacks. Ours has the worse exponent, 3.5 vs 3. |
| Cutkosky–Mehta, ICML 2020, [arXiv 2002.03305](https://arxiv.org/abs/2002.03305), Thm 3 (NIGT). Applies only to the special case f(x,y) = F(x) − (μ/2)‖y‖². | O(Δσ²√ρ/ε^{3.5} + LΔ/ε² + lower order) → N with K = 2 (take μ = L) | None on the overlap: same order | Single-level → coupled NC–SC minimax | None (both bound the average/random-iterate E‖∇‖) | Ours adds K³LΔσ/ε³-type terms |

**Reduction check.** I checked three natural reductions, and none gives this rate:
- Running NIGT on Φ with an inner SGA solver needs ‖y − y*‖ ≲ ε/L at every step, which costs ≈ κ²σ²/ε² samples per outer step, or ε^{-5.5} in total.
- Treating the √ε-sized y-tracking error as bias breaks NIGT's ε-bias tolerance.
- STORM/finite-difference HVP surrogates need same-sample gradient pairs, which this oracle does not provide.

The new mechanism is a corrected momentum error χ_t = (m_t − ∇Φ(w_t)) − (α/γ)M(w_t)(y_{t+1} − Z_t). Here M = ∇²_{xy}f(∇²_{yy}f)^{-1}, and the correction turns the linear tracking error into martingale implicit-gradient noise. I inspected the theorem, setup, algorithm and tuning, but not every proof module. I did not run the build or the axiom audit. The proof ancestry is NIGT, which supplies the transported-momentum cancellation, plus standard SGA tracking. Neither gives the minimax bound without this correction.

**Search coverage (2026-10-08).** I searched arXiv, NeurIPS, ICML and JMLR sources for gradient-only NC–SC and bilevel methods under second-order smoothness, and read the theorem statements of the rows above.
- The fully first-order bilevel results I found give ε^{-6}, or ε^{-4} under mean-squared smoothness: Kwon et al., [2402.07101](https://arxiv.org/abs/2402.07101), Thms 3.1–3.2.
- Yang et al., NeurIPS 2024, report O(ε^{-7/2}), but for a squared-gradient criterion.
- Neither of these beats ε^{-4} in norm.
- I did not recheck SAPD+ or Lin–Jin–Jordan; both are reported at ε^{-4}, and Wu et al. dominates them.
- I did not verify the companion note's claim that Wu's hard instances have ρ ∼ L²/ε. Zhang–Wu–Yang ([2609.35206](https://arxiv.org/abs/2609.35206)) prove Ω(κLΔσ²ε^{-4}), and its abstract states no Hessian assumption.
- **Note discrepancies:** [arXiv 2405.00914](https://arxiv.org/abs/2405.00914) is a *withdrawn* paper by C. J. Li, not "Chen–Ma–Zhang". The note also omits that Wu's guarantee holds with constant probability.

The theorem was introduced in commit c6400ca (2026-10-07). Wu et al. and Zhang–Wu–Yang predate it, and I found no later competing work.

## Conclusion

**Yes. Under the extra Lipschitz-Hessian assumption, the proved total complexity beats the best gradient-only NC–SC bound for small ε, but it loses badly in κ.**

The strongest applicable baseline is Wu et al.'s sharp fresh-gradient bound. It assumes no Hessian smoothness, so it also covers this subclass:

| | noise-dominated cost |
|---|---|
| Wu et al. (first-order smooth) | κLΔσ²/ε⁴ |
| This result (+ ρ-Lipschitz Hessian) | κ^{3.5}√ρΔσ²/ε^{3.5} + κ³LΔσ/ε³ |

The gain survives all shared terms only when σ ≥ ε and ε ≲ min{L²/(ρκ⁵), σ/κ², LΔ/(κσ)}. With L, μ, ρ, Δ, σ fixed and ε → 0, the speedup grows like ε^{-1/2}. For moderate ε, or for large κ, the ε^{-4} method wins; the deterministic term is also worse by κ^{2.5}. Methods that reach ε^{-3} need stochastic Hessian–vector products, which this oracle does not provide.

The comparison establishes this gain. The literature search separately found no earlier gradient-only NC–SC result below ε^{-4} under second-order smoothness. However, the area moved quickly in September 2026, so priority is supported but not certain. The method is the minimax analogue of Cutkosky–Mehta's single-level rate, and the momentum correction for y-tracking is the step not covered by known reductions.

What can be claimed: a first gradient-only, single-loop ε^{-3.5} guarantee for stochastic NC–SC minimax under Lipschitz Hessians, which improves ε-dependence at the cost of κ^{3.5}.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
