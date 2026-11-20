# Novelty assessment: SharpLipschitzConvexLowerBound

[`result`](../../LongTails/Theorems/SharpLipschitzConvexLowerBound.lean) is stated for the setup [HighDimensionalSharpLipschitzConvex](../../LongTails/Setups/HighDimensionalSharpLipschitzConvex.lean), which reuses the instances, oracle and criterion of [SharpLipschitzConvex](../../LongTails/Setups/SharpLipschitzConvex.lean). The proof is [SharpChainLowerBound](../../LongTails/Proofs/SharpChainLowerBound.lean); no algorithm is restricted. The theorem says: for every valid parameter point, every randomized algorithm (arbitrary adaptive queries and output, any value-and-subgradient oracle use) and every budget b ≤ ⌊κ²(1+log(μD/ε))/4608⌋, there is an instance on which the expected gap 𝔼f(x̂)−f⋆ exceeds ε. The instance is convex, L-Lipschitz on ℝᵈ and globally μ-sharp, with a minimizer within D of x₀.

**Proved necessary budget.** Write κ = L/μ, where L is the Lipschitz constant, μ the sharpness modulus, D the initial distance and ε the target expected gap. Then

  N ≥ ⌊κ²(1 + log(μD/ε))/4608⌋ = Ω(κ²(1 + log(μD/ε))).

This holds for κ ≥ 96, 0 < ε ≤ μD and d ≥ 2¹⁰(1+κ²(1+log(μD/ε)))⁶(LD/ε)². It is vacuous when κ²(1+log(μD/ε)) < 4608.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Wang, [arXiv 2512.13863](https://arxiv.org/abs/2512.13863) v1 (15 Dec 2025, only version, unrefereed), Thm 2 and the Hölder corollary at θ=1. **Covers only subgradient-span methods.** | ≈ 2κ² log(μD/ε) iterations for f−f⋆ ≤ ε, span methods, d ≥ N+1 → Ω(κ²(1+log(μD/ε))) for all randomized methods | None in order. The gain is in algorithm class: span → arbitrary deterministic or randomized. Constant is worse (≈2 vs 1/4608). | Hard instances are globally sharp; Wang's class only needs the error bound within distance D of argmin. Global sharpness is a subclass, so this is a stronger statement. | Deterministic gap → expected gap, holding for every randomized algorithm | d must be polynomial in κ², log(μD/ε) and LD/ε (Wang needs only d ≥ N+1); κ ≥ 96; ε ≤ μD |
| Log-free Ω(κ²), attributed by the companion note to Juditsky–Nesterov, [arXiv 1401.1792](https://arxiv.org/abs/1401.1792) App. Thm 8 (deterministic). **Its applicability at ρ=1 is unverified.** | Ω(κ²) → Ω(κ²(1+log(μD/ε))) | Adds a factor 1+log(μD/ε), which is unbounded as μD/ε → ∞. | None | Deterministic → randomized | Same dimension and constant caveats as above |
| Upper bound, *not a competitor*: Polyak step (1969; Wang Thm 1), restarted subgradient ([Yang–Lin 2018](https://arxiv.org/abs/1512.03107)); repo [SharpLipschitzConvexRestartedSubgradient](../../LongTails/Theorems/SharpLipschitzConvexRestartedSubgradient.lean) | ⌈4κ²⌉(⌈log₂⌈μD/ε⌉⌉+1) = O(κ²(1+log(μD/ε))) | Matches up to a universal factor (≤ 1.4·10⁵) | Same class and oracle | — | The upper bound holds in every dimension. Below d ≈ κ², cutting-plane methods with O(d log(LD/ε)) calls are faster, so a high-dimensional condition is necessary. |

**Reduction check.** There is no direct route from known bounds. Rescaling the Nemirovski–Yudin Ω(L²R²/ε²) Lipschitz bound does not produce sharp instances, and the log factor needs a multiscale chain. Wang identifies enforcing a global error bound as the difficulty and leaves non-span algorithms untreated. The hiding step reuses familiar random-coordinate prefix simulation (Nemirovski–Yudin / Woodworth–Srebro style; also the repository's weak-Minty bound). What is new is a *robust* sharp chain: a half-weight radial piece, ordered offsets and a cone, built so that small unrevealed coordinates do not change the oracle answers. I did not check whether a low-dimensional resisting-oracle argument with d ≈ κ² could give the same result more easily.

**Search coverage.** Searches on 2026-11-20 covered arXiv, NeurIPS and related lower-bound work: Wang 2025, Roulet–d'Aspremont ([arXiv 1702.03828](https://arxiv.org/abs/1702.03828) v2, NeurIPS 2017), Grimmer ([arXiv 2104.10196](https://arxiv.org/abs/2104.10196)), Juditsky–Nesterov, and randomized lower bounds (Diakonikolas–Guzmán, [arXiv 1811.01903](https://arxiv.org/abs/1811.01903)). Nemirovski–Nesterov 1985 (*USSR Comput. Math. Math. Phys.* 25(2)) could not be accessed. Grimmer says its Hölder-growth lower bounds were "claimed … although no proof is given", and Roulet–d'Aspremont say it does not treat the nonsmooth case. Neither statement was checked against the paper itself. **Mismatch with the companion note:** Juditsky–Nesterov define uniform convexity with ρ ≥ 2, so the note's "ρ = 1" reading of their Theorem 8 needs justification. The theorem was introduced in commit c3a26ec9 on 2026-11-20; I found no later or concurrent work.

## Conclusion

**Yes: this extends the known κ²·log lower bound from span methods to all randomized algorithms; the rate itself is unchanged.**

The strongest prior lower bound is Wang's Theorem 2 (Dec 2025). It gives the same order but only for subgradient-span methods. For general deterministic or randomized methods, the only lower bound I could verify is log-free.

| | Algorithm class | Necessary calls |
|---|---|---|
| Wang 2025 | span methods, d ≥ N+1 | ≈ 2κ² log(μD/ε) |
| This result | all randomized, d ≥ poly(κ², log(μD/ε), LD/ε) | κ²(1+log(μD/ε))/4608 |

Together with restarted subgradient, this gives Θ(κ²(1+log(μD/ε))) for the class, up to a universal factor, in high dimension. That shows restarted subgradient and Polyak steps cannot be beaten by any method, including methods that know f⋆. The construction needs global sharpness to survive off the span, and Wang names that as the obstacle.

There are three limitations. The dimension requirement is far larger than Wang's d ≥ N+1. The constant is weak. The parameter range is restricted to κ ≥ 96 and ε ≤ μD. The comparison establishes a strictly broader algorithm class, but the literature search does not fully establish priority: Nemirovski–Nesterov 1985 could not be read, and it might claim a related bound, apparently without proof.

What can be claimed: the first verified lower bound of Ω(κ² log(μD/ε)) for general randomized first-order methods on globally sharp Lipschitz convex functions, matching the classical upper bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
