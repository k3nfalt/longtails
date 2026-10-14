# SvrgConvex: novelty assessment

[`result`](../../LongTails/Theorems/SvrgConvex.lean) proves the following. Take `F = (1/n)∑ᵢ fᵢ` on a real Hilbert space, where each `fᵢ` is convex and its oracle gradient is `L`-Lipschitz, and suppose a minimizer `x*` exists with `‖x₀−x*‖ ≤ R` ([setup](../../LongTails/Setups/FiniteSumSmoothAndConvex.lean)). Then epoch-doubling SVRG ([algorithm](../../LongTails/Algorithms/Svrg.lean)) satisfies `E[F(x̃_S)] − F* ≤ ε`. The method uses step `1/(8L)` and epoch lengths `2,4,…,2^S`. Each epoch starts from the previous epoch's last iterate and uses the previous epoch's average as its snapshot. The output `x̃_S` is the final snapshot, i.e. an epoch average, not a last iterate.

**Complexity.** Here `n` is the number of components, `L` the smoothness constant, `R` the initial distance and `ε` the target expected objective gap. The proved budget is `n⌈log₂⌈17LR²/(2ε)⌉⌉ + ⌈68LR²/ε⌉` component-gradient calls. The proof bounds the actual execution, which makes `nS + 4(2^S−1)` calls. This gives

`O(1 + n·log(1 + LR²/ε) + LR²/ε)`.

The algorithm needs to know `L`, `R` and `ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SVRG++, Allen-Zhu–Yuan, ICML 2016, [arXiv:1506.01972](https://arxiv.org/abs/1506.01972) v3, Thm 4.1 (prior) | The theorem allows any integer `m₀ ≥ 1`. With `m₀=1` and `Δ ≤ LR²/2`: `O(n log(LR²/ε) + LR²/ε)` → `O(1 + n log(1+LR²/ε) + LR²/ε)` | None: same order | None. SVRG++ also covers each `fᵢ` convex and `L`-smooth, plus a proximal term `Ψ` | None. Same snapshot-average output and same expected gap; both need `L` and the budget needs `R`, `ε` | Selected result is narrower: no `Ψ`. Infinite-dimensional `E` is allowed, but the proof is dimension-free. With `m₀ = LR²/Δ`, SVRG++ improves the log term to `n log(Δ/ε)` |
| Katyusha + AdaptReg, Allen-Zhu, STOC 2017 / JMLR 2018, [arXiv:1603.05953](https://arxiv.org/abs/1603.05953), Cor. 3.5 (prior) | `O(n log(Δ/ε) + √(nL)·R/√ε)` ≤ `O(n log(LR²/ε) + √(nLR²/ε))` → `O(1 + n log(1+LR²/ε) + LR²/ε)` | Worse: when `LR²/ε ≥ n`, slower by a factor of up to `√(LR²/(nε))`. Never better beyond constants, since `√(nLR²/ε) ≤ (n + LR²/ε)/2` | None. Same class with optional prox term | None. Same information and the same expected-gap criterion | Katyusha uses a regularization reduction with restarts. These costs are included in Cor. 3.5 |
| VRADA, Song–Jiang–Ma, NeurIPS 2020, [arXiv:2006.10281](https://arxiv.org/abs/2006.10281), Thm 1 / Table 2 (prior); same setup in repo [AcceleratedFiniteSumConvex](../../LongTails/Theorems/AcceleratedFiniteSumConvex.lean), added 2026-09-21 (later) | Repo bound: `3n(⌈log₂⌈log₂n⌉⌉ + ⌈√(32LR²/(nε))⌉)` → `O(1 + n log(1+LR²/ε) + LR²/ε)` | Worse when `LR²/ε ≫ n`. Better only when `log(LR²/ε) < log log n`, i.e. `LR²/ε ≲ log n`. Katyusha+AdaptReg already matches the selected bound in that regime | None | None | None |

**Reduction check.** The result is Theorem 4.1 of SVRG++ with `m₀ = 1` and `η = 1/(8L)` instead of `1/(7L)`, and with `F(x₀)−F* ≤ LR²/2` from smoothness. The proof (`inner_step_bound` → `epochRun_bound`) uses the same telescoping across iterations and epochs that SVRG++ introduced. Remaining differences are the averaging window and the explicit constants. I found no new mechanism. Woodworth–Srebro's lower bound `Ω(n + √(nLR²/ε))`, as quoted in the Katyusha paper (I did not read it directly), shows that the `LR²/ε` term is not optimal for the problem class.

**Search coverage.** On 2026-10-07 I read the theorem statements and algorithms of SVRG++, Katyusha (Thm 4.1 and Cor. 3.5) and VRADA (Thm 1, Table 2) from current arXiv versions. I did not check Varag (Lan–Li–Zhou 2019) or the Allen-Zhu–Hazan reduction paper in detail. Neither could change the verdict, since a matching earlier bound already exists. There is no companion note. The theorem first appears in commit 2075d6c (2026-09-18).

**Conclusion**

**No: this is a re-proof of the known SVRG++ guarantee, not an improvement.** The closest baseline is Allen-Zhu and Yuan's SVRG++ (ICML 2016). It is the same algorithm, and its Theorem 4.1 gives the same bound on the same class, which can also include a proximal term.

| | component-gradient calls for `E[F]−F* ≤ ε` |
|---|---|
| This result | `O(1 + n log(1+LR²/ε) + LR²/ε)` |
| SVRG++ (2016) | `O(n log(LR²/ε) + LR²/ε)` |
| Katyusha + AdaptReg (2017) | `O(n log(LR²/ε) + √(nLR²/ε))` |

Accelerated variance-reduced methods match the selected bound up to constants in every regime and beat it by a factor of up to `√(LR²/(nε))` when `LR²/ε ≫ n`. The selected result needs the same information (`L`, `R`, `ε`) and gives the same averaged-snapshot, expected-gap output. So there is no adaptivity or output gain.

What can be claimed is a formalized, dimension-free proof of SVRG++ with explicit constants (`m₀=1`, step `1/(8L)`), with every oracle call counted. That is a verification contribution, not new mathematics.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
