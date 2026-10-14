# AcceleratedFiniteSumConvex: novelty assessment

The [theorem](../../LongTails/Theorems/AcceleratedFiniteSumConvex.lean) ([setup](../../LongTails/Setups/FiniteSumSmoothAndConvex.lean), [algorithm](../../LongTails/Algorithms/Vrada.lean), [rate proof](../../LongTails/Proofs/VradaRate.lean)) proves that an epoch-based accelerated SVRG method with epoch length `n` and weights `A₀ = 1/L`, `A_{k+1} = A_k + √(nA_k/(2L))` returns its final epoch's averaged snapshot `x̄` with `E[F(x̄)] − F* ≤ ε` for every `F = n⁻¹Σᵢ fᵢ` whose components are convex and `L`-smooth on a real Hilbert space and which has a minimizer `x*` with `‖x₀ − x*‖ ≤ R`.

**Budget.** Here `n` is the number of components, `L` the component smoothness constant, `R` the initial distance bound and `ε` the target expected objective gap. Each oracle call returns one exact component gradient. The exact budget is `3n(⌈log₂⌈log₂ n⌉⌉ + ⌈√(32LR²/(nε))⌉)`, which gives

  **O( n(1 + log log(n+2)) + √(nLR²/ε) )** component-gradient calls.

Each epoch makes `n` snapshot calls plus 2 calls for each of its `n` inner steps. There are no restarts, and the expectation is over the uniform sampled indices. The updates need `L` and `n`; the stopping rule also needs `R` and `ε`. Boundary cases: if `n = 1`, the cost is `3⌈√(32LR²/ε)⌉`. If `R = 0` or `ε ≥ LR²`, the `n log log n` startup is still paid.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Song–Jiang–Ma, VRADA, [NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/hash/093b60fd0557804c8ba0cbf1453da22f-Abstract.html), [arXiv 2006.10281 v4](https://arxiv.org/abs/2006.10281), Thm. 1, (9)–(11), with `σ = 0`, `m = n`; prior | `O(n(1+log log n) + √(nLR²/ε))` → `O(n(1+log log n) + √(nLR²/ε))` | None: same order. VRADA uses one initial gradient step plus epochs costing `n + 2n` calls. Its bound `A_s ≥ n(s−s₀+2√2)²/(32L)` with `s₀ = 1+⌈log₂log₂(n/2)⌉` gives the same count. | None. The Hilbert-space setting is a routine extension of VRADA's dimension-free proof in `ℝᵈ`. | None. Both need known `L` and stop using `R` and `ε`. Both output the same epoch average: `x̃_s = (A_{s−1}/A_s)x̃_{s−1} + (a_s/(mA_s))Σ_k z_{s,k}`. | The current class is narrower: VRADA also allows a proximal term `l` and a strongly convex variant. With `l = 0`, VRADA's dual-averaging step reduces to the Lean `z`-update. |
| Z. Li, ANITA, [arXiv 2103.11333 v3 (2022)](https://arxiv.org/abs/2103.11333), Thm. 1 / Cor. 1; prior | `O(n·min{1+log⁺(LR²/(ε√n)), log √n} + √(nLR²/ε))` (I restored the scaling by `LR²`) → `O(n log log n + √(nLR²/ε))` | Mixed. The current result is better when `LR²/(n log²n) ≲ ε ≲ LR²/(√n·log n)`, for example by a factor of `log n/log log n` at `ε = LR²/n`. It is worse when `ε ≥ LR²/√n`, where it costs `n log log n` against ANITA's `O(n)`. VRADA already covers this advantage. | None: same assumptions. | Worse output: ANITA guarantees the last iterate `w_T` and does not need `ε` in its parameters. The current result guarantees an epoch average and needs `ε` to stop. | ANITA's loopless method counts gradients in expectation over a geometric first stage. I did not verify whether its call count is almost surely bounded. |
| Repository: [SvrgConvex](../../LongTails/Theorems/SvrgConvex.lean) | `O(n log(LR²/ε) + LR²/ε)` → `O(n log log n + √(nLR²/ε))` | Within this repository only: the `LR²/ε` term becomes `√(nLR²/ε)`, and `log(LR²/ε)` becomes `log log n`. | None | None | None |

**Standard-reduction check.** The theorem is VRADA's Theorem 1 specialized to `l = 0`, `σ = 0`, `m = n`. The only change is that it starts from `A₀ = 1/L` at `x₀`, using `F(x₀) − F* ≤ LR²/2`, instead of taking VRADA's initial gradient step. VRADA supplies both the doubly exponential startup (`b_{k+1} = b_k + √b_k` with `b₀ = 2/n`) and the per-epoch potential argument, so I found no new mechanism. Proof ancestry: this is Katyusha/MiG-style negative momentum with SVRG++-type epoch weighting; neither gives a competing bound on its own.

**Search coverage (2026-10-07).** I read the theorem statements of VRADA and ANITA directly. AdaVRAE/AdaVRAG ([ICML 2022, arXiv 2201.12302](https://arxiv.org/abs/2201.12302)) claim `O(n log log n + √(nL/ε))` without knowing `L`; I checked only the abstract, not their domain assumptions. Varag (Lan–Li–Zhou, NeurIPS 2019) and the Woodworth–Srebro (2016) lower bound `Ω(n + √(nLR²/ε))` come from the comparison tables in VRADA and ANITA; I did not recheck them. I found no later work that removes `log log n` uniformly. There is no companion note. Git history dates the theorem to 2026-09-21 (commit `163fb73`), years after VRADA (2020) and ANITA (2021). An older repository review (`scripts/reviews/AcceleratedFiniteSumConvex.md`) reaches the same identification.

## Conclusion

**No: this theorem re-derives a known complexity bound for a known algorithm.** The strongest baseline is VRADA (Song–Jiang–Ma, NeurIPS 2020, Theorem 1). For the same class (convex, `L`-smooth components, initial distance `R`), it uses the same algorithm with the same expected-gap criterion and averaged output, and proves

  VRADA: `O(n log log n + √(nLR²/ε))` = this result: `O(n log log n + √(nLR²/ε))`.

The Lean method is VRADA without the proximal term. With that term removed, VRADA's dual-averaging step reduces to the Lean update, and the outputs match term for term.

In no regime does this result have a present-day advantage. VRADA matches it everywhere. ANITA (2021) is strictly better for coarse accuracy (`ε ≥ LR²/√n`): it costs `O(n)` there instead of `O(n log log n)`, and it also guarantees the last iterate. Where this result beats ANITA (roughly `ε ≈ LR²/n`), VRADA already achieves the same gain.

What can be claimed is a formal Lean verification of VRADA's general-convex rate on Hilbert spaces, without the composite term. The rate, assumptions, output and proof mechanism are all already in the literature.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
