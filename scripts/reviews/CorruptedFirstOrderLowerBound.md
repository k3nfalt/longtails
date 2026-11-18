# CorruptedFirstOrderLowerBound: novelty assessment

[`result`](../../LongTails/Theorems/CorruptedFirstOrderLowerBound.lean) shows the following. Fix valid parameters, any algorithm in the template and any call budget `N ≤ k + ⌊LΔ/(2²⁵ε²)⌋`. Then there is an `L`-smooth `f` on `ℝ^d` with `f(x₀) − inf f ≤ Δ`, together with an oracle that corrupts at most `k` joint (value, gradient) replies, such that the returned point has `‖∇f‖ > ε` with outer probability `> 1/4`, which exceeds every allowed failure level ([setup](../../LongTails/Setups/CorruptedFirstOrderNonconvex.lean), [high-dimensional restriction](../../LongTails/Setups/CorruptedFirstOrderNonconvex/HighDimensional.lean), [construction](../../LongTails/Proofs/CorruptedFirstOrderLowerBound.lean)). It is a lower bound, so there is no algorithm file.

**Necessary calls:** `Ω(k + LΔ/ε²)`, valid when `LΔ/ε² ≥ 2²⁶` and `d ≥ 2³²(1 + ⌊LΔ/(2²⁵ε²)⌋)⁴`. Here `L` is the gradient-Lipschitz constant, `Δ` the initial gap, `ε` the gradient-norm tolerance, `k` the number of corrupted replies and `d` the dimension. The restrictions do not depend on `k`. The hard oracle answers `(0,0)` to the first `min(N,k)` calls and answers exactly afterwards. The objective is the repository's hidden-coordinate chain, translated to `x₀`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon–Duchi–Hinder–Sidford, *Lower bounds for finding stationary points I*, Thm 2 with p=1 (randomized algorithms; [arXiv 1710.11606](https://arxiv.org/abs/1710.11606), Math. Program. 184, 2020). **Special case k=0.** | `Ω(LΔ/ε²)` for `d ≳ (LΔ/ε²)² log(LΔ/ε²)` → `Ω(k + LΔ/ε²)` for `d ≳ (LΔ/ε²)⁴` | Adds the `+k` term. Applied after the delay below, the old bound already gives this: zeroing `min(N,k)` replies and then using Thm 2 on the remaining `≤ cLΔ/ε²` clean calls yields `Ω(k + LΔ/ε²)`, so nothing beyond the composition | Clean oracle → up to `k` corrupted replies, a modelling extension handled by a 2-line reduction | Carmon et al. count any stationary query; this result counts the returned point. The returned point can be added as one more query | Dimension requirement goes from `T² log T` to `T⁴` (worse). Constant `2⁻²⁵`. Covers non-measurable template maps via outer probability, which is a formalization point |
| Carmon et al., Thm 1 (deterministic or zero-respecting methods, `d ≈ 2T+1`). **Narrower algorithm class.** | `Ω(LΔ/ε²)` (deterministic) → `Ω(k + LΔ/ε²)` (randomized) | `+k` term only, by the same delay argument | Same as above | None | Needs polynomially higher dimension than Thm 1 |
| Trivial `k`-only bound: if all `N ≤ k` replies are corrupted, the output does not depend on `f`. **No `T` term.** | `Ω(k)` (folklore) → `Ω(k + LΔ/ε²)` | `max(k,T)` and `k + T` agree up to a factor 2, so the sum is just the two known bounds combined | None | None | None |

**Gap to upper bounds.** The companion [`CorruptedFirstOrderDescent`](../../LongTails/Theorems/CorruptedFirstOrderDescent.lean) proves `⌈16LΔ/ε²⌉ + 5k + 4` calls in every dimension. So in the regime above, the pair is tight up to universal constants. The lower bound's value is that it certifies the companion's additive form. The replication baseline costs `O((k+1)LΔ/ε²)`.

**Reduction check.** The result is the composition "uninformative corrupted prefix, then Carmon-type clean hardness". The algorithm's state after the prefix depends only on its seed, so it is a randomized clean algorithm. No new hard instance or proof mechanism is needed. Proof ancestry: the hidden-chain, radial-wall and random-embedding technique comes from Carmon et al.; the repository's `AbcHardFunction` chain and a finite counting/averaging argument re-prove it with a cruder dimension bound.

**Search coverage (2026-11-18).** I searched for lower bounds under adversarially corrupted, Byzantine or erroneous first-order oracles, and checked the statement and dimension requirement of Carmon et al. Thm 2. I found no paper stating this exact corrupted-reply lower bound. Given the reduction, that absence does not indicate novelty. Gupta–Koren–Talwar-style `Ω(C)` corruption lower bounds for bandits show the same additive pattern, but I did not check them in detail. The companion note calls the delay "elementary"; I agree. Its description of Carmon's dimension (order `T² log T`) matches the sources. The theorem was introduced in commit `5b11e6b5` (2026-11-18).

**Conclusion**

**No: this lower bound is a standard corollary of the known clean lower bound plus a trivial corruption prefix.**

The strongest baseline is Carmon et al. (2017/2020), Theorem 2. It gives `Ω(LΔ/ε²)` calls for randomized methods on clean smooth nonconvex functions. Here the adversary simply wastes the first `k` replies. After that the algorithm has learned nothing about `f`, and Carmon's bound applies to the remaining calls:

| | necessary calls | dimension |
|---|---|---|
| Carmon et al., clean | `Ω(LΔ/ε²)` | `≳ T² log T` |
| this result, k corruptions | `Ω(k + LΔ/ε²)` | `≳ T⁴`, with `T = LΔ/ε²` |

The `+k` term is exactly what that two-step argument predicts. The formal version needs more dimension than Carmon's, and its constant (`2⁻²⁵`) is much smaller.

The result is still useful as a companion. Together with the repository's `O(LΔ/ε² + k)` descent upper bound, it shows the additive corruption cost is optimal up to constants for every `k` in the high-dimensional regime. That optimality claim is a contribution of the pair, and it rests on the upper bound. My search found no prior paper stating this exact corrupted-oracle bound, but no idea beyond the composition is needed.

What can be claimed is a formal confirmation that the companion upper bound is tight. It is not a new hardness mechanism or a stronger lower bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
