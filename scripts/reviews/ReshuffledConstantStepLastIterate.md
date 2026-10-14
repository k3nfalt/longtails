# Constant-step random reshuffling, raw last iterate (smooth convex finite sums)

[`result`](../../LongTails/Theorems/ReshuffledConstantStepLastIterate.lean) proves the following. Let F = (1/n)Σfᵢ, where each fᵢ is convex with an Lᵢ-Lipschitz gradient, Lᵢ ≤ L_max, and (1/n)ΣLᵢ ≤ L_avg. Run random reshuffling (RR): K epochs, each with a fresh uniform permutation and the constant step η = 1/(12(1+log n)(1+log(n+2+a))(536L_max+132σ²/ε)). Then the raw final iterate satisfies 𝔼[F(x_{nK})−F(x\*)] ≤ ε after exactly nK component-gradient calls. The construction is in the [setup](../../LongTails/Setups/ConstantStepReshuffledSmoothConvex.lean) and the [algorithm](../../LongTails/Algorithms/ConstantStepReshuffledGradient.lean), with the bound from `sum_gap` (`2D²/(ηT)+66ηH_nH_Tσ²` with step cap `ηL_maxH_nH_T ≤ 1/536`). The quantities are D ≥ ‖x₀−x\*‖ and σ² ≥ (1/n)Σ‖∇fᵢ(x\*)‖², the gradient variance at the minimizer. The setting is any real Hilbert space. With u = L_maxD²/ε and s = σ²D²/ε² (so a = u+s), the proved budget is

  **N = O( n + (L_maxD²/ε + σ²D²/ε²)·(1+log n)·log(n + 2 + L_maxD²/ε + σ²D²/ε²) ).**

The rounding cost is included: nK ≤ 2n + 32768(1+log n)(u+s)(1+log(n+2+u+s)). L_avg does not appear in the bound.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| **VRADA**, Song–Jiang–Ma, NeurIPS 2020, [arXiv 2006.10281v4](https://arxiv.org/abs/2006.10281) Thm 1/Table 2. Repo: [AcceleratedFiniteSumConvex](../../LongTails/Theorems/AcceleratedFiniteSumConvex.lean), 2026-09-30, budget 3n(⌈log₂⌈log₂n⌉⌉+⌈√(32L_maxD²/(nε))⌉) | O(n log log n + √(nL_maxD²/ε)) → N | **Worse** when L_maxD²/ε ≥ n: by a factor ≥ log n·log(n+u+s)/log log n, and polynomially (√(u/n), or s/(√(nu)+n)). At most an O(log log n) gain when (u+s)log²n ≲ n log log n | None. The selected class (Lᵢ ≤ L_max) is a subclass of VRADA's | None. VRADA outputs an epoch average | Needs σ (VRADA does not); has the σ²D²/ε² term; logarithmic step cap |
| **IID SGD, raw last iterate**: Attia–Schliserman–Sherman–Koren, [arXiv 2507.11274v2](https://arxiv.org/abs/2507.11274) (Jul 2025; NeurIPS 2025), Thm 2 with β = L_max and uniform component sampling | O(1 + u·log²(2+u+s) + s·log⁴(2+u+s)) → N | Only polylogarithmic: the noise term loses log⁴ in favor of log n·log(n+u+s) when n ≲ s. Worse when n ≫ (u+s)·polylog (full-epoch cost) | None: same assumptions (σ\* at a minimizer) | None: both are raw last iterates with the same required inputs (D, σ, ε, L_max) | Reshuffling instead of IID sampling; additive n |
| RR last iterate, small step: Liu–Zhou, ICML 2024, [arXiv 2403.07723v3](https://arxiv.org/abs/2403.07723) Thm 4.4 (the note cites App. Thm C.1); also Cai–Diakonikolas, ICLR 2025 (not separately checked) | Õ(n√(L_avgL_max)D²/ε + √(nL_avg)·σD²/ε^{3/2}) → N | Deterministic term improves by ≈ n√(L_avg/L_max)/log²; noise term improves iff ε ≳ σ²log²n·log²(n+u+s)/(nL_avg). Worse for smaller ε | None (the same RR class; L_avg-sensitivity is lost) | None (both raw last iterates) | Uses L_max only; loses the n^{-1/3}K^{-2/3} reshuffling noise branch |
| RR, same method, averaged output: Liu, COLT 2026, [arXiv 2606.32005v1](https://arxiv.org/abs/2606.32005) (30 Jun 2026) Thm 1/Cor 1, η ≤ 1/(6L_max) | O(n + u + min{s, √(nL_avg)·σD²/ε^{3/2}}) → N | **Worse**: extra log n·log(n+u+s), and worse in the noise term when ε < σ²/(nL_avg) | None | Weighted average of all inner iterates → raw last iterate (the main gain; Jensen cannot reverse it) | Smaller step (logarithmic cap) |

**Reduction check.** The result is not obtained by substitution. Attia et al.'s argument requires conditionally IID samples, and their one-pass Theorem 3 does not extend to fresh epochs. The multi-epoch, terminally weighted moving-anchor analysis therefore appears genuinely new for RR. Proof ancestry: Liu (2026) supplies the transposition and nonexpansive-coupling lemmas, and Liu–Zhou (2024) and Attia et al. supply the anchor/weighting style. None of these yields the selected bound without the new within-epoch history control.

**Search coverage.** On 2026-10-07 UTC I checked arXiv, ICML, ICLR, NeurIPS and COLT for 2019–2026 work on RR and SGD last iterates and on variance-reduced finite-sum methods. I read the cited theorem statements from the arXiv texts. The theorem was introduced in commit f294d32 (2026-10-05), and all baselines above predate it. The full text of Kim–Cha–Yun (2026) is inaccessible. The companion note omits the stronger baselines VRADA and Attia et al. Thm 2 (it cites Attia only for its one-pass result), so its regime comparison is RR-internal only.

## Conclusion

**No optimization advantage is established: other methods already reach this accuracy with the same or fewer calls.** What is new is a large-step, last-iterate analysis of RR specifically.

For this exact class, the strongest baseline is accelerated variance reduction (VRADA, also formalized in this repository):

| method | component-gradient calls |
|---|---|
| this theorem | n + (L_maxD²/ε + σ²D²/ε²)·log n·log(n+L_maxD²/ε+σ²D²/ε²) |
| VRADA | n log log n + √(nL_maxD²/ε) |
| IID SGD, last iterate | (L_maxD²/ε)·log² + (σ²D²/ε²)·log⁴ |

VRADA is never worse by more than an O(log log n) factor. It is polynomially better whenever L_maxD²/ε ≫ n or σ²D²/ε² ≫ n + √(nL_maxD²/ε). If a raw last iterate is the requirement, IID SGD (Attia et al. 2025) already gives the same rate up to logarithms, with no full-epoch cost.

Within RR, the theorem beats the earlier small-step last-iterate bound when n is large and ε ≳ σ²·polylog/(nL_avg). It also turns Liu's 2026 averaged guarantee into a last-iterate one, at the cost of two logarithms and the reshuffling noise branch. No paper I found proves this for RR, but that establishes only priority for a method-specific analysis, not a better guarantee.

The claimable contribution: the first multi-epoch raw-last-iterate guarantee for constant-step RR with step ≍ 1/(L_max·log n·log(nK)) on general smooth convex finite sums.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
