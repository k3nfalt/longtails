# BoundedScalarConvex: novelty assessment

The [theorem](../../LongTails/Theorems/BoundedScalarConvex.lean) ([setup](../../LongTails/Setups/BoundedScalarConvex.lean), [algorithm](../../LongTails/Algorithms/ScalarSgd.lean)) proves that, for a convex H-Lipschitz f on a bounded interval C, projected SGD with constant step η = ε/(25H²) has an expected last-iterate gap of at most ε after K = max{1, ⌈25H²R²/ε²⌉} calls. The oracle replies are bounded by H almost surely, and their conditional means, given the revealed-seed past, are relative subgradients.

**Complexity:** O(1 + H²R²/ε²) stochastic-subgradient calls. Here H > 0 bounds the Lipschitz constant and the replies, R ≥ 0 bounds |x₀ − x⋆|, and ε > 0 is the target expected gap. The method is one-dimensional and requires x₀ ∈ C. It needs H and ε for the step size, plus R for the stopping time. If R = 0, it still uses one call.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liu–Zhou, [Thm 3.4, §3.1.1](https://arxiv.org/html/2312.08531v4) (linear-decay projected SGD; v3 Dec 2025, v4 Mar 19 2026; prior) | O(1 + H²R²/ε²) → O(1 + H²R²/ε²) | None: same order | None: theirs is broader (any dimension, unbounded closed convex domain, finite variance) | None: both give last-iterate expected gap and need H, R, ε/T | Current: d = 1, compact interval, a.s.-bounded replies; only change is constant step instead of linear decay |
| Jain–Nagaraj–Netrapalli, [Thm 1](https://arxiv.org/pdf/1904.12443) (COLT 2019; prior) | O(1 + H²D²/ε²), D = diam C ≥ R → O(1 + H²R²/ε²) | Factor (D/R)² when D > R; already removed by Liu–Zhou | Independent noise → adapted replies (both bounded a.s.) | None: last iterate in both | Theirs: any dimension, step schedule tied to the horizon; current: scalar only |
| Beretta et al., [Thm 2, Eq. (2)](https://arxiv.org/html/2606.24879) (v1 June 23 2026; prior; same constant-step scalar method) | O(1 + H²R²/ε²) on the bounded-noise overlap (L = σ = H) → same | None: same order | Additive i.i.d. state-independent noise → adapted, state- and time-dependent bounded replies | None | Not nested: theirs allows unbounded noise and domains; current needs a.s. bounds and a compact interval |

**Reduction check.** Liu–Zhou applies after extending f outside C with slopes ±H. The bounded relative-support conditional means then become global subgradients of the extension, matching their Assumption 4, E[ĝₜ | ℱₜ₋₁] ∈ ∂f(xₜ). Take L = 0, M = 2H, σ ≤ H, and D_ψ = R²/2 for the Euclidean distance. Their bound O((M+σ)√D_ψ/√T) becomes O(HR/√T), so the same budget follows with no logarithm.

Defazio et al. ([Cor. 2](https://arxiv.org/pdf/2310.07831), Oct 2023) get DG/√T for unprojected linear decay. That result is not applied here because unprojected queries leave C, where the oracle contract is silent.

**What is technically new.** The new part is the method-specific analysis. It bounds terminal excursions of constant-step scalar SGD under bounded adapted replies, using finite hinge supersolutions and secant-weighted telescoping. The excursion-plus-regret skeleton is inherited from the scalar literature (Liu–Lu; Beretta et al.).

Beretta et al. show a (log n)/√n lower bound for time-inhomogeneous noise (Theorem 3). Their construction needs noise of order √n, and they state that the uniformly bounded case remains unsettled. The selected result therefore plausibly settles that algorithm-specific question. [Kornowski–Shamir](https://arxiv.org/abs/2604.13870) give anytime lower bounds in dimension T+1; these do not apply to this horizon-tuned scalar method.

**Search coverage.** On 2026-10-07 UTC I checked arXiv versions and COLT/ICLR sources for these papers and read the cited theorem statements, plus Beretta's lower-bound construction. Git dates the result to 2026-09-28 (`3c0299d`), after every source in the table.

**Mismatches with the companion note.** The note compares the result only with a generic constant-step bound that carries log T. It does not cite Liu–Zhou Thm 3.4, Jain et al., or Defazio et al. as direct log-free last-iterate competitors. Its "meaningful asymptotic improvement" is therefore a gain over constant-step analyses only, not over SGD. The [previous review](../reviews/BoundedScalarConvex.md) cited a log-factor gain over Liu–Zhou's weaker Thm 3.1, which [negative_examples.md](../negative_examples.md) explicitly corrects.

## Conclusion

**No: the call complexity is unchanged, and no new problem instances are covered.**

The strongest baseline is Liu–Zhou's Theorem 3.4: projected SGD with a linearly decaying step, available since December 2025. It already gives the same last-iterate accuracy and needs the same parameter knowledge, under broader assumptions: any dimension, unbounded domains, finite-variance martingale noise.

| | Calls for E[f(x_T)] − f⋆ ≤ ε |
|---|---|
| Liu–Zhou (linear decay) | O(1 + H²R²/ε²) |
| This result (constant step) | O(1 + H²R²/ε²) |

The only difference is the step-size schedule. A constant step on its own improves neither complexity, scope, information requirements, nor the output guarantee. The claimed removal of a log T factor holds only against other constant-step analyses, not against the best applicable SGD guarantees.

What is plausibly new is the proof itself. It appears to be the first log-free last-iterate analysis of unmodified constant-step scalar SGD under bounded, history-dependent replies. Beretta et al. (June 2026) list this case as open. The search supports, but does not prove, priority for that analysis.

The contribution that can be claimed is a new analysis of one particular algorithm, not a better optimization guarantee.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
