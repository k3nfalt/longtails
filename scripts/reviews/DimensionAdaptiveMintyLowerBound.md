# Novelty assessment: DimensionAdaptiveMintyLowerBound

[`result`](../../LongTails/Theorems/DimensionAdaptiveMintyLowerBound.lean) proves the following for the [setup](../../LongTails/Setups/FiniteDimensionalWeakMinty.lean). For every valid `d ≥ 1`, `L > 0`, `0 ≤ ρ ≤ 1/(20L)` and `0 < ε < LR`, take any randomized adaptive algorithm using exact `F(x)` queries at any `N ≤ ⌊d log(1 + L²R²/(dε²)) / 2²²⌋`. Some `L`-Lipschitz operator with a `ρ`-weak-Minty root `z`, `‖z − x₀‖ ≤ R`, then has expected residual `∫‖F(x̂)‖ > ε`. The operator may depend on the algorithm and on `N`, but not on the seed. The hard fields satisfy the plain Minty condition (`ρ = 0`) ([field](../../LongTails/Proofs/MintyPrefixField.lean), [counting](../../LongTails/Proofs/MintyPrefixLower.lean)). The paired upper bound is [DimensionAdaptiveMinty](../../LongTails/Theorems/DimensionAdaptiveMinty.lean), which uses the [centroid-cut algorithm](../../LongTails/Algorithms/DimensionAdaptiveMinty.lean).

**Necessary oracle calls** (`d` is the dimension, `L` the Lipschitz constant, `R` the root distance, `ε` the target residual):

$$N_{\text{lower}} = \Omega\!\left(d\,\log\!\left(1+\frac{L^2R^2}{d\,\varepsilon^2}\right)\right)
\quad\text{vs.}\quad N_{\text{upper}} = 2\left\lceil 1024\,d\log\!\left(1+\frac{L^2R^2}{d\varepsilon^2}\right)\right\rceil .$$

So the complexity is `Θ(L²R²/ε²)` when `d ≥ L²R²/ε²`, and `Θ(d log(LR/(ε√d)))` when `d ≤ L²R²/(2ε²)`. The universal constants differ by a factor of about `2³³`. The Lean budget is zero, so the statement is vacuous, unless `d log(1+L²R²/(dε²)) ≥ 2²²`; since this quantity is at most `L²R²/ε²`, it requires `LR/ε ≥ 2¹¹`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository: [EuclideanWeakMintyLowerBound](../../LongTails/Theorems/EuclideanWeakMintyLowerBound.lean) (PR #182; prior work in this repository only) | `Ω(min{L²R²/ε², d^{1/3}})` → `Ω(d log(1+L²R²/(dε²)))`; same oracle, randomized algorithms, and expected residual | For `d ≤ L²R²/ε²`: a factor `≥ d^{2/3}`. For `L²R²/ε² ≤ d ≤ L⁶R⁶/ε⁶`: a factor `L²R²/(ε²d^{1/3})`. For `d ≥ L⁶R⁶/ε⁶`: none, same order | `d ≥ 257`, `LR ≥ 28ε` → `d ≥ 1`, `LR > ε` | None | Much worse constant: `2⁻²²` vs `1/784` |
| [Yoon–Ryu, ICML 2021](https://proceedings.mlr.press/v139/yoon21d.html), Thms 3–4 (special case: monotone saddle gradients, a subclass of Minty; deterministic algorithms; `d ≳ LR/ε`) | `Ω(LR/ε)` → `Ω(min{L²R²/ε², d log(LR/(ε√d))})` | Not comparable as the same problem: the old row is a smaller class with `O(LR/ε)` upper bounds. On the Minty class, the known necessary cost rises by a factor `LR/ε` when `d ≥ L²R²/ε²` | Monotone → nonmonotone Minty hard instances; any `d` | Deterministic span-type algorithms → randomized adaptive algorithms | The hard fields are not saddle gradients. The bound says nothing about monotone instances |
| [Anagnostides et al., arXiv 2504.03432 v4, FOCS 2026](https://arxiv.org/abs/2504.03432), Props 6.8/6.10 (summary only) | `Ω(1/ε)` at `d = 1` and `Ω(2^d)` for constant `ε`, both for **MVI solutions** on a compact set → residual bound above | Not comparable: a different accuracy criterion (a global Minty-gap solution, not a local residual) | Not comparable | None | — |

**Reduction check.** I checked three routes. The monotone subclass cannot give more than `O(LR/ε)`, because Halpern-type methods achieve that. The gradients of star-convex functions are covered only by fields of a different kind, and I found no `L²R²/ε²` gradient-norm lower bound for them. Separation-oracle feasibility lower bounds (Nemirovski–Yudin) let the adversary choose the returned halfspaces; here each reply must be the value of a single field that is Lipschitz and Minty everywhere. The genuinely new mechanism is that field: a hidden word sets the root, and the field's components are products of clipped sines and cosines. Each call therefore reveals only `O(1)` bits beyond a matched prefix, which a transcript count turns into `2·4^N·2^k ≤ M^k`. The packing/volume scale `d log(R/(r√d))` and the averaging over the hidden word are standard proof ancestry. The note cites Lobel–Paes Leme–Vladu and Carmon et al. Prop. 8 for this ancestry; I did not verify those citations.

**Search coverage (21 Nov 2026 UTC).** I searched arXiv and ICML/ICLR proceedings for weak-Minty, Minty, star-monotone and fixed-point query lower bounds. I read summaries of Anagnostides et al. and arXiv 2611.11691 (resolvent oracle, SVI gap, no lower bound) and of arXiv 2609.32981 (monotone, weak-solution gap, QP oracle). Anagnostides et al.'s Section 6 and Yoon–Ryu's theorem statements were available only as extracted summaries, not verbatim. The theorem was committed today (dbb83b0d), so any later work is not prior work. The companion note matches the Lean statement, except that it calls PR #182 "earlier" without saying it is a repository result rather than published work.

## Conclusion

**Yes, this is a new lower bound, and with the paired upper bound it pins down the dimension dependence of exact-oracle Minty root finding up to universal constants.**

The strongest published necessary bound I found for this residual criterion is Yoon–Ryu's `Ω(LR/ε)`. It applies only to monotone saddle gradients, which already admit `O(LR/ε)`, so it says nothing about why weak-Minty methods need more. The repository's own earlier bound reached `L²R²/ε²` only when `d ≳ (LR/ε)⁶`. The new statement holds for all dimensions:

| regime | known upper bound | new necessary cost |
|---|---|---|
| `d ≥ L²R²/ε²` | `O(L²R²/ε²)` (extragradient, DDJ 2021) | `Ω(L²R²/ε²)` |
| `d ≤ L²R²/(2ε²)` | `O(d log(LR/(ε√d)))` (paired theorem) | `Ω(d log(LR/(ε√d)))` |

This shows that the dimension-free extragradient rate cannot be beaten in high dimension, even by randomized adaptive methods, and that the `log(t²/d)` form is sharp.

There are two limitations. The constant `2⁻²²` makes the formal budget zero unless `LR/ε` is in the thousands. The hard fields are not saddle gradients, so the minimax-gradient subclass remains open. Priority is less certain than the comparison: I found no earlier `Ω(L²R²/ε²)` or dimension-interpolating residual lower bound for Minty operators, but some sources were read only through summaries.

What can be claimed is a tight, all-dimension, randomized query lower bound for Lipschitz (weak-)Minty residuals, built on a new field construction.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
