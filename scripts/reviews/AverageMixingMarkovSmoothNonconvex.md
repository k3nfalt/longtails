# Novelty assessment: AverageMixingMarkovSmoothNonconvex

The [theorem](../../LongTails/Theorems/AverageMixingMarkovSmoothNonconvex.lean) concerns an `L`-smooth `f` on `ℝ^d` with gap `Δ`, and replies `g(x,Z_t)` from one **stationary** Markov chain on `ℝ` ([setup](../../LongTails/Setups/AverageMixingMarkovSmoothNonconvex.lean)). The chain mixes on average, `∫ TV(P^t(z,·),π) dπ(z) ≤ 2e^{-t/τ}`, and the noise is controlled only at stationarity: at each fixed `x`, the mean is `∇f(x)` and the centered second moment is at most `σ²`. Under these conditions, [spaced-batch normalized GD](../../LongTails/Algorithms/MarkovNormalizedBatch.lean), returning the start of a uniformly random epoch, achieves `E‖∇f(X)‖ ≤ ε`.

**Proved budget.** `(⌊2048D⌋+1)(⌊256S⌋+1)(⌊τ log(32+8192S)⌋+1)` calls, with `D = LΔ/ε²` and `S = σ²/ε²`. This equals

  **O( τ (1 + LΔ/ε²)(1 + σ²/ε²) log(2 + σ²/ε²) )**.

Here `L` is the smoothness constant, `Δ ≥ f(x₀) − inf f`, `σ²` the stationary noise variance, `τ ≥ 1` the average-mixing scale and `ε > 0` the accuracy. The bound holds for every `d`, and for every `Δ, σ ≥ 0`. Every call is counted, discarded transitions included. All parameters are known to the algorithm.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| *Special-case baseline (uniform mixing, statewise noise):* Beznosikov et al., [NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/file/8c3e38ce55a0fa44bc325bc6fdb7f4e5-Paper-Conference.pdf), Lemma 1 + minibatch GD (Cor. 2 gives `Õ(τD(1+S))`) | `O(D + τDS)` → `O(τ(1+D)(1+S)log(2+S))` | **Worse** on this subclass: by `log(2+S)` when `S ≥ 1`; for `S ≤ 1/τ` the cost is `τD` instead of `D` | Uniform-in-state TV mixing → stationary-average mixing (e.g. a Gaussian AR(1) chain, which is not uniformly ergodic); statewise noise bound → stationary variance only | None (same known parameters, random iterate) | `E‖∇f‖² ≤ ε²` → weaker `E‖∇f‖ ≤ ε` |
| Repository [MarkovNonconvexStationarity](../../LongTails/Theorems/MarkovNonconvexStationarity.lean) (added 2026-11-18): uniform mixing, stationary variance | `O(τDS log(σ²/ε²))` → same | None: same order on the overlap | Uniform → average mixing. Also drops the restrictions `σ ≥ 4096ε`, `LΔ ≥ 2²⁶ε²` and the huge-`d` condition | None | None found |
| Derived reduction, same full class: Berbee/Yu blocking ([Yu 1994, Ann. Probab., Lemma 4.1](https://projecteuclid.org/journals/annals-of-probability/volume-22/issue-1/Rates-of-Convergence-for-Empirical-Processes-of-Stationary-Mixing-Sequences/10.1214/aop/1176988849.full)) on the thinned chain, plus i.i.d. minibatch normalized GD ([Cutkosky–Mehta, ICML 2020](https://arxiv.org/abs/2002.03305), Lemma 2) | `O(τ(1+D)(1+S)log(2+DS))` → `O(τ(1+D)(1+S)log(2+S))` | A factor `log(2+DS)/log(2+S)`, which is unbounded only when `D ≥ (2+S)^{ω(1)}`. Example: `S = 1`, `D → ∞` gives `τD log D → τD` | None | None | None |
| Sun–Wei, [NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/file/1cdbce34681a3aaa0154b300706743d8-Paper-Conference.pdf), Thm 4.4 (finite chains) | `O(τ_mix L̄Δ(1+σ²)/(√π_min ε³))` → selected bound | Not comparable: requires mean-square smoothness `L̄` and depends on `π_min` | Finite state with `π_min` → general real Borel chains | None | Loses the `ε⁻³` rate available on their subclass |

**Reduction check and mechanism.** Row 3 is the decisive check. Normalized steps keep `‖∇f‖ ≤ √(2LΔ) + LNη = O(ε(1+D))` on every run. Yu's lemma then bounds the total coupling error by `NB·β(h)·O(ε(1+D))`, which forces `h ≍ τ log(2+DS)`. The new mechanism avoids this run-wide union cost. It applies one-at-a-time replacement inside each batch's alignment statistic, controlling the covariance between gradient drift and `u(z) = TV(P^h(z,·),π)` by a geometric sum ([alignment proof](../../LongTails/Proofs/MarkovBatchAlignment.lean)). This removes `D` from the logarithm. Proof ancestry is Cutkosky–Mehta's normalized-descent lemma and standard β-mixing blocking.

**Search coverage.** The search ran on 2026-11-19 (UTC) and covered β-mixing, average-mixing and Markovian nonconvex SGD on arXiv and NeurIPS/ICML 2022–2026. I read the assumptions of [Alacaoglu–Lyu (ICML 2023)](https://arxiv.org/abs/2203.15797), whose Assumption 2.2 takes a sup over histories and whose Assumption 2.3 bounds gradients. I also read [Roy–Saminger-Platz (arXiv 2502.03551)](https://arxiv.org/abs/2502.03551), which treats β-mixing for quadratic objectives only. Row 1 and Sun–Wei were checked in this repository's earlier review. [Agarwal–Duchi (IEEE TIT 2013)](https://arxiv.org/abs/1110.2529) and Even (2023) need convexity or uniform/hitting-time models. I found no prior end-to-end nonconvex bound under stationary-average mixing. Two things remain unverified: the exact AR(1) constant `τ`, and the appendices of Alacaoglu–Lyu. The theorem entered in commit `8b172243` (2026-11-19). The companion note's citations are consistent with these sources. However, the note does not quantify the row-3 reduction, which it only alludes to.

**Conclusion**

**Only by a logarithm: the result removes `log D` from a bound that a standard reduction already gives.**

The strongest baseline is not a published theorem. It is a direct composition of β-mixing blocking (Yu 1994) with i.i.d. minibatch normalized GD:

| | calls for `E‖∇f(X)‖ ≤ ε` |
|---|---|
| blocking + normalized GD | `τ(1+D)(1+S)·log(2+DS)` |
| this result | `τ(1+D)(1+S)·log(2+S)` |

The gain appears only when `D = LΔ/ε²` is superpolynomial in `S = σ²/ε²`. For example, at `σ = ε` the cost falls from `τD log D` to `τD`. Uniform mixing with statewise-bounded noise is a subclass of this model, and there Beznosikov et al. plus minibatch GD give a log-free `O(D + τDS)` bound for the stronger criterion `E‖∇f‖² ≤ ε²`; the selected result is worse on that subclass.

The extension from uniform to stationary-average mixing is real. It covers chains such as a Gaussian AR(1) process, where mixing from far-away starting states is arbitrarily slow. However, the same reduction already reaches that extension. With the companion lower bound, the new upper bound closes the remaining `log D` gap in the high-dimensional regime. I found no earlier paper with this bound, but absence from the search does not establish priority. What can be claimed is the removal of `log(LΔ/ε²)` from the mixing overhead under average mixing, via a within-batch replacement argument.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
