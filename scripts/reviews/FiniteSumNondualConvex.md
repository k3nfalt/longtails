# FiniteSumNondualConvex: what is actually new?

The [theorem](../../LongTails/Theorems/FiniteSumNondualConvex.lean) ([setup](../../LongTails/Setups/FiniteSumNondualSmoothConvex.lean), [algorithm](../../LongTails/Algorithms/FiniteSumNondual.lean)) works for `F = (1/n)Σᵢ fᵢ` with each `fᵢ : ℝᵈ → ℝ` convex and having an `L`-Lipschitz Euclidean gradient. With exact feasible component-gradient queries on the ℓ₁ ball `Q = R·B₁ᵈ`, a randomized method returns `x̂ ∈ Q` with `E[F(x̂)] − min_Q F ≤ ε`.

**Complexity (component-gradient calls).** Here `n` is the number of components, `d` the dimension, `L` the component smoothness constant, `R` the ℓ₁ radius, and `ε` the expected objective accuracy. There are no function values, gradient bounds, or initial-gap assumptions. The exact budget `2⁴⁰ n(1+⌈(LR²/(nε))^{1/3}⌉)(1+⌊log₂(2+d+n+⌈LR²/ε⌉)⌋)⁴` gives

`N = O( (n + n^{2/3}(LR²/ε)^{1/3}) · log⁴(2+d+n+LR²/ε) )`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Varag, Lan–Li–Zhou, [NeurIPS 2019, arXiv:1905.12412v3](https://arxiv.org/abs/1905.12412), Thm 1 (μ=0). It applies because `Q` lies in the Euclidean ball of radius `R`. With one initial projected full-gradient step (n calls, gap ≤ 2LR²), `D₀ ≤ 10LR²` | `O(n log n + √(nLR²/ε))` → `O((n + n^{2/3}(LR²/ε)^{1/3}) log⁴(2+d+n+LR²/ε))` | Gain factor `(LR²/(nε))^{1/6}/log⁴(·)`. Sufficient regime: `LR²/ε ≥ n·log²⁴(2+d+n+LR²/ε)` | None (same class) | None (both give expected objective gap) | **Worse** by up to `log⁴(d+n)/log n` when `LR²/ε ≲ n·polylog`. Varag is implementable; here selectors and cut-emptiness tests are free and exact, with no runtime claim |
| SP-Prox, Loginov et al., [arXiv:2609.32910v1](https://arxiv.org/abs/2609.32910) (26 Sep 2026, preprint), Prop. E.8. It is run on `F`, and each gradient costs `n` component calls | `n·O((1+(LR² log(2d)/ε)^{1/3}) log^{7/3}(2+LR² log(2d)/ε))` → this result | The leading term improves by a factor of `n^{1/3}` (up to logarithms). Sufficient regime: `LR²/ε ≥ n` and `n ≥ C log¹²(2+d+n+LR²/ε)` | None (same class) | None (Prop. E.8 is deterministic, so it is stronger on output) | Randomized, in expectation only. Slightly worse logarithms when `n` is polylogarithmic |

**Reduction check and proof ancestry.** I read Lemmas E.9–E.11 of Loginov et al. Their outer SP-Prox analysis uses `L` only as the Moreau-envelope weight, together with convexity and `diam₂ Q ≤ 2R`. Replacing that weight with `μ = L/n` gives `Õ((LR²/(nε))^{1/3})` trials per stage. The inner PGD prox solver (Lemma E.9) is then replaced by ProxSVRG ([Xiao–Zhang 2014, Thm 3.1](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/96179.pdf)) on a problem with condition number ≈ n. That costs `O(n·log)` per certified prox, plus a fallback for solver failure. This Catalyst-type composition reproduces the bound up to logarithms. The companion note concedes it. I checked the structure of the substitution, not every inequality with `μ < L`; only stage bookkeeping such as `δ ≤ μR²` changes. No new upper-bound mechanism is needed. [Martínez-Rubio et al., arXiv:2609.21880](https://arxiv.org/abs/2609.21880) (Thm 6, deterministic `Õ((LR²/ε)^{1/3})` with heavier logarithms) is a further full-gradient ancestor.

**Lower bounds (not part of `result`).** Proof modules contain `component_not_convergence` (the budget must exceed `n/4`) and `normalized_not_convergence`. Together they give `Ω(n + n^{2/3}(LR²/ε)^{1/3})` against arbitrary randomized feasible-query methods. This needs `d ≥ 1024(T+1)(k+1)³`, which for the hard instance is roughly `d ≳ n(LR²/(nε))^{4/3}`. `grep` found no `sorry`/`axiom`. I did not build or run the comparator. The construction combines known parts: Woodworth–Srebro dead-zone chains (arXiv:1605.08003), Loginov's ℓ₁ hidden supports (App. D.5.1), and serial component search. I found no prior finite-sum lower bound for this mismatched geometry. The Euclidean `√(nLR²/ε)` lower bound does not transfer.

**Search coverage (2026-11-03).** I searched arXiv and the web for finite-sum, variance-reduced, and mismatched-geometry (ℓ₁/ℓ₂) convex optimization. I read Varag Thm 1 and Loginov Props E.8–E.11 with their Theorem 1 statement. I saw only the MR26 and Zhou (arXiv:2610.04944) abstracts. The theorem was introduced in commit `e9068db8` (2026-11-03), after all cited preprints, and I found no subsequent work. One mismatch with the note: Zhou's abstract says their individual-smoothness lower bound has no zero-respecting restriction. The note says Zhou leaves unrestricted lifting separate. I did not resolve this.

## Conclusion

**The rate is better than that of the checked methods, but the proved upper bound is essentially a routine composition.**

On the same class with the same oracle and expected-gap criterion:

| | component-gradient calls |
|---|---|
| Varag (Euclidean acceleration) | `O(n log n + √(nLR²/ε))` |
| SP-Prox on the mean | `Õ(n(LR²/ε)^{1/3})` |
| this result | `O((n + n^{2/3}(LR²/ε)^{1/3}) log⁴(2+d+n+LR²/ε))` |

This bound is polynomially better when `LR²/ε ≫ n·polylog` and `n ≫ polylog`. For example, with `LR²/ε = n⁴` the cost falls from about `n^{5/2}` to `n²` up to logarithms. It loses logarithmic factors in `d` when `LR²/ε ≲ n`, and its exact selectors have no efficient implementation.

The comparison establishes this gain. However, the gain comes from substituting the prox weight `L/n` into Loginov et al.'s gradient-only SP-Prox and solving each prox with ProxSVRG. That is a standard Catalyst-style reduction, which the note itself acknowledges. The more original piece is a matching unrestricted randomized lower bound in very high dimension. It is proved in supporting lemmas, not stated by `result`, and I did not verify its priority beyond a literature search.

What can be claimed is the first explicit finite-sum `Õ(n + n^{2/3}(LR²/ε)^{1/3})` bound for ℓ₂-smooth components on an ℓ₁ ball, obtained by a known composition, together with a possibly new lower bound.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
