# Novelty assessment: PolylogPrecisionRelativeErrorConvex

[`result`](../../LongTails/Theorems/PolylogPrecisionRelativeErrorConvex.lean) concerns a convex, L-smooth `f` on a real Hilbert space with a minimizer `x*` satisfying `‖x₀−x*‖ ≤ R`. Every gradient reply may be adversarial, as long as `‖g−∇f(x)‖ ≤ α‖∇f(x)‖` with `α ≤ 1/(100(33(1+log(2+LR²/ε)))¹²)`. Under these conditions, the deterministic recursive Moreau-envelope method [`sharpEnvelopeOutput`](../../LongTails/Algorithms/SharpEnvelope.lean) returns a point with `f(x_out) − f(x*) ≤ ε` for every seed ([setup](../../LongTails/Setups/SharpRelativeErrorSmoothConvex.lean)). The method uses `L, R, ε, x₀` but not α.

**Complexity.** L is the smoothness constant, R the initial distance, ε the target objective gap and α the relative error. The exact public budget is `⌈8(33(1+log(2+LR²/ε)))²⁰(2+LR²/ε)^{5/8}⌉` physical gradient calls ([`oracle_cost`](../../LongTails/Proofs/SharpEnvelopeBudget.lean)). In O-form, with the constant `8·33²⁰ ≈ 2·10³¹` suppressed:

  N = O( (2+LR²/ε)^{5/8} · (1+log(2+LR²/ε))²⁰ ),  valid for `0 ≤ α ≤ (100(33(1+log(2+LR²/ε)))¹²)⁻¹`.

Below, T = LR²/ε and α* is the admissible threshold. Crossovers were computed at α = α*. For smaller α the baselines improve and the crossovers move later.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vasin–Gasnikov, [arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376v1) (Mar 2026 preprint, prior), Thm 9.3 with the largest admissible τ = log(1/(9α))/log(2T) | `72000·T^{1−τ}·ln(480T)`, which is `T^{1−o(1)}` at α = α* → `O(T^{5/8}log²⁰T)` | Exponent `1−o(1)` → `5/8`. The bound is actually smaller only when `ln T ≳ 837`. | None (the new class is the subclass with α ≤ α*) | None. Both give the last output's objective gap. Their method also needs α. | Requires `α ≤ α*` (`≈10⁻²⁵` at T≈1). Far worse whenever `ln T < 837`. |
| Repository [AcceleratedRelativeErrorConvex](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean) (Lean, prior; every α<1) | `⌈7√(T/(1−α)) + 11α²T/(1−α)⌉` → same | Better iff `11α²T ≳ 2·10³¹(log T)²⁰T^{5/8}`. At α = α* this needs `ln T ≳ 1273` (T ≈ 10⁵⁵³). The asymptotic ratio is about `(log T)⁴⁴/T^{3/8}`. | None | None. That method needs α in its damping; this one does not. | Worse roughly whenever `α ≲ 10^{16}T^{−3/16}(log T)^{10}` and for all practical T. |
| Repository [RecursiveRelativeErrorConvex](../../LongTails/Theorems/RecursiveRelativeErrorConvex.lean) (Lean, 2026-10-24, prior) | `4√(2+T)(32+log(2+T))^{32(1+√log(2+T))}`, but only for `α ≤ e^{−8(1+√log(2+T))}/100` → same | Precision regime enlarged: `α ≤ e^{−O(√log T)}` → `α ≤ Θ((log T)^{−12})`. On the overlap this result is smaller for `ln T ≲ 1.8·10⁷`. | Covers `e^{−8(1+√log)}/100 < α ≤ α*`, which that theorem excludes | None (same information and output) | Exponent 5/8 instead of `1/2+o(1)`, so it loses for `ln T ≳ 1.8·10⁷` |

**Reduction check.** Kornilov et al. ([arXiv:2310.00506](https://arxiv.org/abs/2310.00506), Thm 3.1) need `α ≲ T^{−1/2}`. The strongly convex accelerated methods ([arXiv:2503.06628v3](https://arxiv.org/abs/2503.06628v3), Thm 4: `α < 0.016√(μ/L)`) need `α ≲ T^{−1/2}` after regularization with `μ = ε/R²`, and they would also face mixed relative-plus-absolute error. At `α ≍ (log T)^{−12}` neither applies. Batching cannot reduce adversarial bias. Plain Catalyst ([JMLR 2018](https://jmlr.org/papers/v18/17-748.html)) needs decaying inner errors.

Proof ancestry: the result is the repository's own recursive envelope scheme, which itself rests on Catalyst-type outer proximal steps. The genuinely new step is a phase-2 inner solver whose output averages the iterates and keeps the gradient-dissipation term. Its error amplification per level is `1+2τ`, not 16, so `Θ(log T/log log T)` levels cost only a constant precision loss. I checked the energy and budget lemmas only at the statement level. I did not build the project or run the comparator. A grep found no `sorry`/`admit`/`axiom` in the SharpEnvelope modules.

**Lower-bound conflict.** The literal statement of Vasin–Gasnikov Thm 10.2(1) implies `N ≳ T^{1−o(1)}` when α = T^{−o(1)}, so this theorem contradicts it, as the recursive result already did. Both the companion note and the earlier review locate gaps in that claimed lower bound's proof (App. G). I did not re-verify those gaps independently.

**Search coverage** (2026-10-26): I searched arXiv and the web for relative and multiplicative gradient error, acceleration, quantized precision and nested proximal schemes. I read the theorem statements of 2603.12376v1 (§7, §9, §10) and 2503.06628v3 (Thm 4–5). For Hallak–Levy (ICML 2024), I checked only the abstract: projected and conditional gradient methods, unaccelerated. I did not access the JOTA text of Kornilov et al. or Burns–Liang 2602.17878 in full. I found no prior or later work achieving a polynomial exponent below 1 at inverse-polylogarithmic relative precision. The companion note's citations and its regime statements match what I checked. Its two-level comparison bound is a hand proof that I did not verify.

## Conclusion

**Asymptotically yes, but only at astronomically large `LR²/ε`: relative precision of order `1/polylog(LR²/ε)` now suffices for a polynomial speedup.** The strongest baselines are the repository's damped accelerated method (every α < 1) and Vasin–Gasnikov's regularized method (2026 preprint, Thm 9.3).

At `α ≍ (log T)^{−12}`:

| Method | Calls |
|---|---|
| Vasin–Gasnikov Thm 9.3 | `T^{1−o(1)}` |
| Damped acceleration (repo) | `T/(log T)²⁴` |
| This result | `T^{5/8}(log T)²⁰` |

The repository's recursive method reaches `T^{1/2+o(1)}`, but only for `α ≤ e^{−O(√log T)}`, which is far smaller than any inverse polylog. The gain over the damped method requires `ln T ≳ 1273` at the largest admissible α. The constant is about `10³¹`, and the threshold α* is `≈10⁻²⁵` even at T ≈ 1. So the theorem is a qualitative tradeoff between precision and exponent, not a usable speedup. It also contradicts a published but disputed lower-bound claim.

The comparison proves this asymptotic gain. The search found no prior result of this kind, which supports priority but cannot establish it. The mechanism is a sharper inner certificate inside the repository's own recursive scheme. What can be claimed is that, for smooth convex minimization, adversarial relative gradient error of size `Θ((log(LR²/ε))^{−12})` still allows `O((LR²/ε)^{5/8})` calls up to polylogarithmic factors. The concrete limitation is that the gain appears only beyond T ≈ 10⁵⁵³.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
