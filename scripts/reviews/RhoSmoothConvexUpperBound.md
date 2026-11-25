# Novelty assessment: RhoSmoothConvexUpperBound

The [theorem](../../LongTails/Theorems/RhoSmoothConvexUpperBound.lean) shows that a deterministic three-phase gradient method, [RhoSmoothThreePhase](../../LongTails/Algorithms/RhoSmoothThreePhase.lean), returns a last iterate with `f(x_N) − f* ≤ ε` for every seed. The class is the setup [RhoSmoothRadiusConvex](../../LongTails/Setups/RhoSmoothRadiusConvex.lean): convex `f` on a real Hilbert space, exact gradients, `‖D∇f(x)‖ ≤ L₀ + L₁‖∇f(x)‖^ρ`, `1 < ρ ≤ 2`, and `‖x₀ − x*‖ ≤ R`. There is no bound on the initial gap Δ or on the initial gradient. The method is given `L₀, L₁, ρ, R, ε`.

**Complexity.** The proved budget is `⌈9√(L₀R²/ε) + 262144(1 + Q)⌉` gradient calls, which is

  N = O( √(L₀R²/ε) + 1 + R² L₀^(2−2/ρ) L₁^(2/ρ) ),

where `Q = R² L₀^(2−2/ρ) L₁^(2/ρ) = (L₀R/G)²` and `G = (L₀/L₁)^(1/ρ)` is the gradient level at which `L₁‖∇f‖^ρ = L₀`. Here L₀ is the base curvature, L₁ the growth coefficient, ρ the growth exponent, R the initial distance, and ε the accuracy. The bound is valid for `L₀, L₁, R, ε > 0` and `ρ ∈ (1, 2]`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884) (21 May 2026, ICML 2026), Thm 3.3 / Cor 3.4 (Alg. 1, `ρ ≤ 2`), with GD from [Tyurin 2412.11773v2](https://arxiv.org/abs/2412.11773), Table 2 (`1<ρ<2`) | With δ ≍ min{G²/L₀, L₀R²}: `O(√(L₀R²/ε) + 1 + Q + Q·min{(Δ/(L₀R²))^(ρ/2), …})` → `O(√(L₀R²/ε) + 1 + Q)`. Cor 5.3 as stated also adds an `L₀R²/Δ` term. | Same order when `Δ ≤ L₀R²`. When `Δ > L₀R²` the Δ-term drops, a gain factor of up to `(Δ/(L₀R²))^(ρ/2)`, which is unbounded. | Known-Δ class → radius-only class. This covers instances whose Δ and `‖∇f(x₀)‖` are arbitrarily large for fixed R (e.g. doubly exponential growth along a line), on which the prior bound gives no guarantee. ρ = 2 is included. | Δ is no longer an input. Both results give a last-iterate guarantee. | None on the overlap. Constants are larger (262144). |
| Verified standard composition (not stated as a theorem anywhere): normalized steps (Nesterov, *Lectures*, Lemma 3.2.1, as used in [Vankov et al. 2410.10800v3](https://arxiv.org/abs/2410.10800), Thm 4.1), then GD ([Li et al., NeurIPS 2023](https://arxiv.org/abs/2306.01264), Thm 4.2), then Tyurin's Thm 3.2 AGD | `O(√(L₀R²/ε) + 1 + Q)` → `O(√(L₀R²/ε) + 1 + Q)` | None: same order | None | None | None |
| Rudomanov–Fomin–Gasnikov–Stonyakin, [arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461) (Oct/Nov 2026), Thm 3.7. **Applies only at ρ = 1** | `O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R))` on the ρ = 1 class | Not comparable: the classes are disjoint for ρ > 1. Embedding the ρ = 1 class into the ρ-class as ρ ↓ 1 gives `Q ≈ (L₁R)²`, which is worse. | ρ = 1 → ρ ∈ (1,2] | None | Uses no line search. |

**Reduction check.** The rate follows from published lemmas, with constants suppressed:

1. **Phase 1.** Suppose `‖∇f(x)‖ ≥ G`. Li et al.'s Lemma 3.5 gives `f(x) − f* ≥ ‖g‖²/(2ℓ(2‖g‖)) ≳ G²/L₀`; this uses ρ ≤ 2. Li et al.'s Lemma 3.3 at x* gives quadratic growth within radius about `G/L₀`. Nesterov's Lemma 3.2.1 then forces `⟨g/‖g‖, x−x*⟩ ≳ G/L₀`. So fixed normalized steps reduce `‖x−x*‖²` by about `(G/L₀)²`, and the gradient drops below G within `O(1+Q)` calls.
2. **Phase 2.** At that point `‖∇f‖ < G`, so `ℓ(2G) ≤ 5L₀`. Li et al.'s Theorem 4.2 then reaches gap `δ ≍ min{G²/L₀, L₀R²}` in `O(1+Q)` calls.
3. **Phase 3.** This δ meets Tyurin's condition `ℓ(8√(δL₀)) ≤ 2L₀`, so his Theorem 3.2 finishes in `5√(L₀R²/ε) + O(1)` calls.

The Lean algorithm is exactly this pipeline. Its local `deep_cut` lemma is a direct form of step 1. I found no new technical mechanism.

The proof ancestry is Tyurin's AGD analysis, which supplies the Lyapunov invariant and the region where the gradient stays small, plus Li et al.'s local-smoothness lemmas. The repository adds the bookkeeping that makes the three phases fit together, and the formal Hilbert-space version. The cited papers work in ℝ^d.

**Search coverage.** I searched arXiv and the web on 2026-11-25 for generalized-smooth, ℓ-smooth, and (ρ,L₀,L₁) convex optimization. Results found and checked:
- Tyurin 2025 and 2026, Li et al., Vankov et al., and Everest I: full texts, at the theorems cited above.
- Gorbunov et al. and Kovalev–Stonyakin: from abstracts and Everest I's survey table only. Both are ρ = 1.
- Lobanov's (H₀,H₁)-smoothness paper ([2608.04884](https://arxiv.org/abs/2608.04884)), El Bakkali–Gorbunov ([2610.23301](https://arxiv.org/abs/2610.23301)), Dvinskikh–Gasnikov–Lobanov ([2609.06555](https://arxiv.org/abs/2609.06555)), and Krivchenko ([2611.29211](https://arxiv.org/abs/2611.29211)): abstracts only. All are ρ = 1, gap-dependent, or stochastic.

No stated radius-only bound for ρ > 1 turned up, before or after the result. It was introduced in commit `b37d9c82` (2026-11-25). Proceedings versions were not separately checked.

The companion note is consistent with the Lean statement, and it already calls this upper bound's novelty "modest". However, its claim that dropping Δ and including ρ = 2 improves on Tyurin's bound overlooks that Li et al.'s GD, plus the standard normalized-step warm-up, already gives both.

## Conclusion

**The proved bound is new as a stated theorem, but it comes from routinely composing known results.** The closest published baseline, Tyurin's Theorem 3.3 / Corollary 5.3, needs a bound Δ on the initial gap and carries a Δ-dependent term. The selected theorem removes Δ entirely:

| | Calls |
|---|---|
| Tyurin (known Δ) | `√(L₀R²/ε) + 1 + Q + Q·min{(Δ/(L₀R²))^(ρ/2), …}` |
| This result (radius only) | `√(L₀R²/ε) + 1 + Q`, with `Q = R²L₀^(2−2/ρ)L₁^(2/ρ)` |

The two bounds have the same order when `Δ ≤ L₀R²`. The new one is strictly better when `Δ > L₀R²`, and it covers objectives whose initial gap and gradient are unbounded for a fixed radius R. On those, the earlier bound gives no guarantee.

The gain is modest because a short, verified chain of published lemmas reproduces the same `O(√(L₀R²/ε) + 1 + Q)` bound. The chain is a normalized-step warm-up (Nesterov's Lemma 3.2.1 with Li et al.'s local lemmas), then Li et al.'s GD, then Tyurin's AGD. My search found no paper that states this radius-only bound for ρ > 1. Priority therefore looks likely, but it is not proven.

What can be claimed is a correct, explicit, formally verified radius-only accelerated bound for convex (ρ,L₀,L₁)-smooth minimization. Its value lies mainly in pairing with the companion lower bound, which shows that the Q term is necessary up to a factor of (ρ−1)². It is not a new algorithm or proof technique.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
