# GraceSgd: finite-bit Grace SGD on bandwidth graphs

[`result`](../../LongTails/Theorems/GraceSgd.lean) shows the following for a connected graph with symmetric full-duplex FIFO links of `b_e` bits/s and no latency ([setup](../../LongTails/Setups/GraphBandwidthSmoothNonconvex.lean)). The quantized-minibatch SGD program ([algorithm](../../LongTails/Algorithms/GraceSgd.lean)) returns a uniformly random iterate `x_J` with `E‖∇f(x_J)‖² ≤ ε` by the stated deadline. The objective is `L`-smooth with gap `Δ`. The oracle is unbiased with variance `σ²` and IID samples, and worker `i` takes `h_i` s per sample.

**Elapsed time.** This follows directly from the Lean `budget`, using `K−1 ≤ 32LΔ/ε` and `w+t = O(log(2+d+LΔ/ε+σ²/ε))`:

$$T=O\Big(\tfrac{L\Delta}{\varepsilon}\min_{\emptyset\neq S\subseteq V}\Big[\tfrac{\sigma^2/\varepsilon+|S|}{\sum_{i\in S}h_i^{-1}}+\mathbf 1_{|S|\ge2}\,\tfrac{d\log(2+d+L\Delta/\varepsilon+\sigma^2/\varepsilon)+|E|\,n\log(2+\sigma^2/\varepsilon)}{\alpha(S)}\Big]\Big).$$

Here `α(S)` is the minimum bandwidth of a cut that separates `S`, `n` is the number of workers, `|E|` the number of edges, and `d` the dimension. The budget is `0` when `32LΔ/ε ≤ 1`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Grace SGD, [Tyurin, arXiv:2603.20735v1](https://arxiv.org/abs/2603.20735) (21 Mar 2026, prior, preprint), Thm 1.5 with Thm F.1. Bandwidth counted in "coordinates/bits" per second | `O((LΔ/ε)·min_k[d/w̄_k + min_{p,m}(m+σ²/ε)/Σ_{i≤m}h_{π_i(S_{k,p})}^{-1}])`, where one real coordinate costs one unit → `T` | **Not comparable** (coordinate units vs. bit units). If one bit is treated as one coordinate, this result is **worse** by a factor `log(2+d+LΔ/ε+σ²/ε)` on the `d` term, plus the extra `\|E\|n log(2+σ²/ε)/α(S)` term. The minimum over all `S` is at most the Gomory–Hu prefix choice, and by Tyurin's eq. (17) lower bound it can be smaller by at most `polylog(n)` in coordinate units | Exact real vectors on links → finite binary packets with 64-bit headers. Same function class, noise class, and graph class | None. Both use step `1/(2L)`, total batch `≈σ²/ε`, the same criterion, and a random iterate. Both need `L, Δ, σ, ε, h_i` and the graph | Bit-level cost is a log factor per coordinate. The fill term dominates for short vectors on large graphs. Tree selection is an exact offline optimization. No latency |
| Routine reduction (unpublished, checked here): Grace with Thm F.1 routing, plus a common-grid quantizer clipped at radius `2(√(2LΔ)+L‖x−x₀‖)+√ε+32σ²/√ε`, which the repo already uses in [DistributedBatchedSgd](../../LongTails/Algorithms/DistributedBatchedSgd.lean) (commit `7e154787`, 2026-11-17) | `O(log(dLΔσ²/ε²))` bits per coordinate times the Grace communication term, plus packet headers → `T` | **None: same order.** Both the log factor and the extra additive header/fill term appear on each side | None | None | None beyond the explicit header/fill accounting |

**Reduction check.** The finite-bit extension is a composition of known pieces:
- Tyurin's Grace descent and batching.
- Lau's Steiner-tree packing, as used in Thm F.1, here in a sparse form with at most `|E|+1` trees and carry-free digit sums.
- Clipped grid quantization, which costs `O(ε)` in squared error. This layer already exists in the repository.

I found no new mechanism that removes the `log(LΔ/ε)` precision cost. Contrast [FiniteBitLeon](FiniteBitLeon.md), whose multi-scale anchors do remove it. Steiner packing and Gomory–Hu trees are proof ancestry here, not baselines.

**Search coverage (2026-11-20 UTC).** I searched arXiv and proceedings for:
- bandwidth-graph time complexity: Tyurin 2026; Shadowheart SGD ([arXiv:2402.04785](https://arxiv.org/abs/2402.04785)), which is star-graph only;
- quantized SGD and quantized AllReduce: QSGD; [Global-QSGD](https://arxiv.org/abs/2305.18627);
- tree-packing collectives: ForestColl; DualColl ([arXiv:2610.15704](https://arxiv.org/abs/2610.15704)), a systems paper with no optimization guarantee.

I read Tyurin's Thm 1.5, Cor 1.6, Thm F.1, and the eq. (16)–(17) lower bound in the arXiv HTML. I did not verify Sections 3–7, Appendix K (latency), or the precise lower-bound algorithm class. Tyurin remarks that metadata costs only a constant factor, but the paper does not treat the precision of values. Neither of us has a bit-model lower bound, so whether the log factor is necessary is open. The result entered the repo in commit `ab45b93e` (2026-11-20), after Tyurin v1. The companion note matches the Lean statement and states the limitations honestly. I did not run the build or the axiom audit.

## Conclusion

**No: this is a finite-bit re-derivation of Tyurin's Grace SGD, and its rate is no better.**

The strongest baseline is Tyurin's Theorem 1.5. It covers the same smooth nonconvex homogeneous class, oracle, graph, worker speeds, step size, and criterion `E‖∇f‖² ≤ ε`, but it charges one unit per exact real coordinate. Measured per round:

| | communication per round |
|---|---|
| Tyurin (coordinates) | `d / w̄_k` |
| This result (bits) | `[d·log(2+d+LΔ/ε+σ²/ε) + \|E\|n·log(2+σ²/ε)] / α(S)` |

The computation term `(σ²/ε+|S|)/Σ_{i∈S}h_i^{-1}` is the same on both sides. No regime gives a gain. The new content is honest bit accounting: packet headers, the first-packet fill time, and finite-bit messages for arbitrary real gradients with unbounded stochastic noise.

That finite-bit step is routine. Clip at a radius that grows with `‖x−x₀‖`, round to a common grid with `O(log(dLΔσ²/ε²))` bits, and sum integer digits along the packed trees. This reproduces exactly the selected bound. The quantizer is already in the repository's `DistributedBatchedSgd`.

My search found no published end-to-end bit-level guarantee for graphs, but that does not establish priority. Whether the log factor or the fill term is necessary is unknown. What can be claimed is a carefully audited finite-bit implementation of Grace SGD with explicit packet costs, not a new optimization guarantee.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
