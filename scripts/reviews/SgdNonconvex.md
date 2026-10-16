# Novelty assessment: `SgdNonconvex`

[`result`](../../LongTails/Theorems/SgdNonconvex.lean) proves the following. Let `f` be bounded below and `L`-smooth on a separable real Hilbert space, with `f(x₀) − inf f ≤ Δ`. Constant-step SGD ([`randomSgd`/`tunedSgd`](../../LongTails/Algorithms/RandomSgd.lean)) uses IID unbiased stochastic gradients with variance at most `σ²` ([setup](../../LongTails/Setups/StochasticSmoothNonconvex.lean)) and the step `η = 1/(L + 2Lσ²/ε²)`. It outputs a uniformly random iterate among `x₀,…,x_{K−1}`, and the theorem proves `∫ ‖∇f(output)‖² ≤ ε²`.

**Complexity.** Here `L` is the smoothness constant, `Δ` is the initial gap, `σ²` is the noise variance, and `ε` is the target root-mean-square gradient norm. The theorem uses exactly `K = ⌈4LΔ/ε² + 8LΔσ²/ε⁴⌉ + 1` stochastic-gradient calls, so

  **K = O(1 + LΔ/ε² + LΔσ²/ε⁴)** (for `L, ε > 0`, `Δ, σ ≥ 0`).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan, RSG, [arXiv:1309.5549](https://arxiv.org/abs/1309.5549) Cor. 2.2, eq. (2.17), with `D̃ = D_f = √(2Δ/L)` (SIAM J. Optim. 23(4), 2013) | (2.17) gives `E‖∇f(x_R)‖² ≤ 2LΔ/N + 2σ√(2LΔ/N)`, so `N = ⌈4LΔ/ε² + 32LΔσ²/ε⁴⌉` → `⌈4LΔ/ε² + 8LΔσ²/ε⁴⌉ + 1` | None: same order (a constant factor of at most 4 on the noise term) | `ℝⁿ` → separable Hilbert space. The proof is dimension-free, so this is a routine extension. | Same output: a uniformly random iterate under a constant step. Their step needs `Δ` and `N`; this step needs only `L, σ, ε`, but the budget `K` still needs `Δ`. Ghadimi–Lan Cor. 2.2 also allows any `D̃ > 0` at a worse constant. | Ghadimi–Lan assume only A1, which allows noise that depends on the iterates; this setup requires IID samples, which is stronger. |
| Arjevani et al., [arXiv:1912.02365](https://arxiv.org/abs/1912.02365) Thms. 1 and 3 (lower bound; Math. Program. 2023) | Lower bound `Ω(LΔσ²/ε⁴)` for `E‖∇f‖ ≤ ε` and `ε ≤ c′√(LΔ)` → the same order is attained | None possible: the `σ`-term is minimax-optimal in its regime | None | None | The lower bound needs high-dimensional hard instances. The criterion `E‖∇f‖² ≤ ε²` implies `E‖∇f‖ ≤ ε`, so the lower bound applies to this result. |

**Reduction check.** The result is a direct substitution into Ghadimi–Lan's Theorem 2.1 descent-and-randomized-output argument, with a constant step and `D_f² = 2Δ/L`. The step `η ≈ min(1/L, ε²/(Lσ²))` is the textbook tuning, and the deterministic term `LΔ/ε²` matches the first-order lower bound `Θ(LΔ/ε²)` that Arjevani et al. cite as ref. [13] (Carmon et al.; I did not reopen that paper). The proof has no new mechanism. The repository's [`GdNonconvex`](../../LongTails/Theorems/GdNonconvex.lean) covers the case `σ = 0`. [`RecursiveGradientNonconvex`](../../LongTails/Theorems/RecursiveGradientNonconvex.lean) concerns a different oracle model, so it is not compared here.

**Search coverage (2026-10-16).** I read the theorem text of Ghadimi–Lan (arXiv v1, Thm. 2.1, Cor. 2.2, eq. (2.17)) and of Arjevani et al. (arXiv v2, Thms. 1 and 3). I did not reopen the journal versions; the venue details come from bibliographic records. The theorem was introduced in commit `3e0c20e` on 2026-10-16. The companion note itself states that this is a "classical SGD bound, not a claim of a new mathematical contribution," and that is consistent with these findings.

## Conclusion

**No: this is the classical SGD guarantee for smooth nonconvex stochastic optimization, with the same complexity, scope, and output.**

The strongest baseline is Ghadimi–Lan's randomized stochastic gradient method from 2013. Under the same smoothness, initial-gap, and unbiased bounded-variance assumptions, it reaches the same criterion `E‖∇f(x_R)‖² ≤ ε²` with the same randomly selected iterate:

| | Stochastic-gradient calls |
|---|---|
| Ghadimi–Lan (2013) | `4LΔ/ε² + 32LΔσ²/ε⁴` |
| This result | `4LΔ/ε² + 8LΔσ²/ε⁴ + 2` |

The only differences are a better constant on the noise term and a step size that does not use `Δ`. The budget still needs `Δ`, so the second difference is not adaptivity. In addition, Arjevani et al. prove that the `LΔσ²/ε⁴` term cannot be improved by any stochastic first-order method in high dimension, so no rate improvement is possible in that regime.

What can be claimed is a correct formalization of a known optimal-order theorem in Lean. It is not a new mathematical result.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
