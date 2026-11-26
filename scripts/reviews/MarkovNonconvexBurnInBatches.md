# Novelty assessment: MarkovNonconvexBurnInBatches

[The theorem](../../LongTails/Theorems/MarkovNonconvexBurnInBatches.lean) proves that [normalized minibatch SGD with one burn-in per batch](../../LongTails/Algorithms/MarkovNonconvexBurnInBatches.lean) attains `E‖∇f(X)‖ ≤ ε` at a uniformly random pre-update iterate `X`. The [setup](../../LongTails/Setups/MarkovSmoothNonconvex.lean) is an `L`-smooth nonconvex `f` with `f(x₀) − inf f ≤ Δ` and one stationary Markov stream with `sup_z TV(κᵗ(z,·),π) ≤ 2e^{−t/τ}`. Replies `g(x,z)` are only required to satisfy `E_π g(x,·) = ∇f(x)` and `E_π‖g(x,·) − ∇f(x)‖² ≤ σ²`. There is no statewise noise bound.

**Proved budget:** `⌈8LΔ/ε²⌉·(⌈τ log 16⌉ + ⌈1024τσ²/ε²⌉)` deterministic calls, discarded replies included. On the valid domain this is

  **Θ(τ·LΔσ²/ε⁴)**, at most `9261 τLΔσ²/ε⁴`, with no logarithm.

The additive burn-in term `τLΔ/ε²` is absorbed. The domain is `L,ε > 0`, `τ ≥ 1`, `σ ≥ 4096ε`, `LΔ ≥ 2²⁶ε²` and `d ≥ 2⁴⁰(1+τLΔσ²/ε⁴)⁴`. The dimension condition comes from the paired lower bound; the upper-bound proof does not use it. The algorithm must know `L, Δ, σ, τ` and `ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository: [MarkovNonconvexStationarity](../../LongTails/Theorems/MarkovNonconvexStationarity.lean), introduced 2026-11-19 (clipped, spaced SGD; identical setup) | `O(τLΔσ²/ε⁴ · log(σ²/ε²))` → `O(τLΔσ²/ε⁴)` | Factor `log(σ²/ε²)` removed. The integer budget is smaller at every valid input. | None (identical setup) | None (same output and criterion) | None |
| **Special case**, statewise noise `‖g(x,z)−∇f(x)‖² ≤ σ²` for all `z`: Beznosikov et al., [NeurIPS 2023 / arXiv 2305.15938](https://arxiv.org/abs/2305.15938), Thm 3/Cor 2, plus the any-start batch bound of Lemma 1 combined with minibatch GD | `O(LΔ/ε² + τLΔσ²/ε⁴)` → `O(τLΔσ²/ε⁴)` | None: same order (`σ ≥ 4096ε`) | Statewise bound → stationary second moment only. This newly covers, e.g., centered state noise that is in `L²(π)` but unbounded across states. | None | Criterion: their `E‖∇f‖² ≤ ε²` is stronger than `E‖∇f‖ ≤ ε`. Their relative noise `δ²‖∇f‖²` is not covered here, so the classes are incomparable. Only `σ ≫ ε` is covered. |
| **Special case**, finite chains: Sun–Wei, [NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/file/1cdbce34681a3aaa0154b300706743d8-Paper-Conference.pdf), Lemma 4.1(1) under the same Assumption 2.3, from any state, plus minibatch GD with batch `≍ τ_mix σ²/(√π_min ε²)`. Here `τ_mix ≤ τ log 8`. | `O(LΔ/ε² + τLΔσ²/(√π_min ε⁴))` → `O(τLΔσ²/ε⁴)` | Factor `π_min^{−1/2}` removed. This is a strict gain whenever `π_min ≪ 1`. | Finite state space → general measurable state space | None (same criterion `E‖∇f‖ ≤ ε`) | Needs worst-start geometric TV mixing and a stationary start |

**Reduction check and mechanism.** Plain minibatch SGD after a burn-in does not reduce to the stationary case under stationary-only variance. A first kept state whose law is only TV-close to `π` can make the batch error unbounded. The proof instead normalizes the batch mean, which makes the descent score `⟨∇f, Y/‖Y‖⟩` bounded by `‖∇f‖`. A single `τ log 16` burn-in then costs at most `‖∇f‖/4` by total variation. This works even though the queries are adaptive.

**Proof ancestry.** The pieces are known, and their combination is short:
- the normalized-SGD alignment inequality (in the style of Cutkosky–Mehta, ICML 2020);
- a stationary batch-covariance bound like Beznosikov's Lemma 1, equation (5);
- a TV transfer of a bounded function.

The repository's earlier note sketched exactly this argument.

**Search coverage.** I searched on 2026-11-26 UTC. The theorem entered in commit `2eef45c4` that day, so all cited papers predate it. I read the exact statements of Sun–Wei's Assumption 2.3, Lemma 4.1 and footnote 2. Footnote 2 conjectures `Õ(τ_mix LΔ/ε² + τ_mix σ²LΔ/ε⁴)` under stationary variance, for finite chains. I also read [Huynh et al., NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/file/ba0dd55207ef557f6774bc85332f94a8-Paper-Conference.pdf), Assumptions 3.2 and 4.3 and Theorem 4.5. It is log-free, but it needs a statewise noise bound and a bounded density ratio `C∞`, so the Beznosikov row already dominates it.

Some sources I did not re-read and took from earlier repository reviews: Beznosikov's statements, and the summaries of Sarkar et al. ([arXiv 2606.26316](https://arxiv.org/abs/2606.26316); PL objectives only) and Peng ([arXiv 2607.25785](https://arxiv.org/abs/2607.25785); compact domain). Doan et al., Dorfman–Levy and Even impose statewise or bounded-gradient conditions, and their bounds keep logarithms. The companion note's citations match what I checked.

**Conclusion**

**Yes: in the stationary-variance Markov model, this gives the first logarithm-free, order-optimal bound I could find. It is not a faster rate than the statewise-noise literature.**

The strongest published baseline is Beznosikov et al. (NeurIPS 2023). Combined with plain minibatch GD it already reaches the same order when the noise is bounded in every chain state. Without that statewise bound, the best earlier guarantees are:

| Noise model | Best earlier bound | This result |
|---|---|---|
| statewise `σ` | `O(τLΔσ²/ε⁴)` (Beznosikov et al.) | same |
| stationary `σ`, finite chain | `O(τLΔσ²/(√π_min ε⁴))` (Sun–Wei Lemma 4.1 + minibatch GD) | `O(τLΔσ²/ε⁴)` |
| stationary `σ`, general states | `O(τLΔσ²/ε⁴ · log(σ²/ε²))` (this repository, unpublished) | `O(τLΔσ²/ε⁴)` |

The paired repository lower bound is `Ω(τLΔσ²/ε⁴)` on the identical setup, so the complexity is settled up to a constant. This answers the mixing-time, general-state-space version of Sun–Wei's published conjecture. The limitations:
- the guarantee is for `E‖∇f‖`, not `E‖∇f‖²`;
- relative noise is not covered;
- the formal statement requires `σ ≥ 4096ε` and an astronomically large `d`;
- all of `L, Δ, σ, τ, ε` must be known.

The comparison proves the gains in the table. Priority rests on my searches finding no earlier stationary-variance bound, which is not proof of absence. The mechanism is short, but it removes a real obstacle: a burn-in does not control unnormalized batch errors under stationary-only variance. What can be claimed is a tight `Θ(τLΔσ²/ε⁴)` expected-stationarity complexity for Markov oracles with only stationary moment bounds.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
