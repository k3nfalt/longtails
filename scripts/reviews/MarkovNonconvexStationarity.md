# Novelty assessment: MarkovNonconvexStationarity

The [theorem](../../LongTails/Theorems/MarkovNonconvexStationarity.lean) proves the following for [clipped SGD with spaced queries](../../LongTails/Algorithms/MarkovClippedSgd.lean) and a uniformly random pre-update iterate. Take an `L`-smooth nonconvex `f` on `ℝ^d` and a single **stationary** Markov stream whose kernel satisfies `sup_z TV(κ^t(z,·),π) ≤ 2e^{-t/τ}`. The replies `g(x,z)` are only measurable in `x`, with `E_π g(x,·)=∇f(x)` and `E_π‖g(x,·)−∇f(x)‖² ≤ σ²` ([setup](../../LongTails/Setups/MarkovSmoothNonconvex.lean)). Under these conditions the method attains `E‖∇f(X)‖ ≤ ε`.

**Proved budget:** `(⌈32768 LΔσ²/ε⁴⌉+1)·⌈τ log(8192σ²/ε²)⌉`, which simplifies to

  **O( τ·LΔσ²/ε⁴ · log(σ²/ε²) )** oracle calls, discarded replies included.

Here `L` is the smoothness constant, `Δ ≥ f(x₀) − inf f`, `σ²` the stationary variance, `τ` the TV mixing scale, and `ε` the accuracy. The bound holds only in the `valid` regime: `τ ≥ 1`, `σ ≥ 4096ε`, `LΔ ≥ 2²⁶ε²`, and `d ≥ 2⁴⁰(1+τLΔσ²/ε⁴)⁴`. All parameters are known to the algorithm.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Beznosikov et al., [NeurIPS 2023, arXiv 2305.15938](https://arxiv.org/abs/2305.15938), Thm 3 / Cor. 2 (randomized MLMC-batch GD), with δ=0 | `Õ(τ(LΔ/ε² + LΔσ²/ε⁴))` expected calls, polylog in `σ²/ε²` hidden → `O(τLΔσ²/ε⁴·log(σ²/ε²))` | None up to logs; the selected bound is deterministic, with at most one log | Statewise bound `‖∇F(x,z)−∇f(x)‖² ≤ σ²` for **every** `z` (A4) → stationary second moment only. This covers replies with unbounded statewise noise, e.g. a centered unbounded `L²(π)` vector of the state | None: both use a uniform random iterate and both need `τ,σ,L,Δ` | Criterion weakens from `E‖∇f‖² ≤ ε²` to `E‖∇f‖ ≤ ε` (Jensen gives only the one direction). Valid only for `σ ≫ ε` and huge `d` |
| Verified reduction on the same statewise class: Beznosikov et al. Lemma 1, eq. (6) (any initial law) + minibatch GD, step `1/L`, batch `n ≍ τσ²/ε²` | `O(LΔ/ε² + τLΔσ²/ε⁴)` deterministic, no log → `O(τLΔσ²/ε⁴·log(σ²/ε²))` | **Worse** by a `log(σ²/ε²)` factor on this overlap | Same relaxation as row 1 | None | Same restrictions as row 1 |
| Verified reduction for finite chains: Sun–Wei, [NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/file/1cdbce34681a3aaa0154b300706743d8-Paper-Conference.pdf), Lemma 4.1(1) (stationary variance, any start state) + minibatch GD | `O(LΔ/ε² + τ_mix LΔσ²/(√π_min ε⁴))` → `O(τLΔσ²/ε⁴·log(σ²/ε²))`, with `τ_mix ≤ τ log 8` | Better by about `1/(√π_min log(σ²/ε²))` when `π_min^{-1/2} > log(σ²/ε²)`; worse otherwise | Finite state space with `π_min` dependence → general measurable state spaces, no `π_min` | None | Needs a stationary start and uniform geometric ergodicity |
| Sun–Wei, NeurIPS 2025, Thm 4.4 (MaC-SPIDER), special case | `O(τ_mix L̄Δ(1+σ²)/(√π_min ε³))` (ε ≤ 1 normalization) → `O(τLΔσ²/ε⁴·log(σ²/ε²))` | Not comparable: the prior result needs mean-squared smoothness `L̄` | Finite state, plus mean-squared smoothness (Assumption 2.4) → neither required | None | The selected result loses the `ε⁻³` rate available on that subclass |

**Reduction check and mechanism.** Under statewise-bounded noise the result is a corollary: row 2 shows a log-free bound. For stationary-variance-only noise, batch means started from an arbitrary state are uncontrolled, so that reduction fails. The proof instead clips at `C ≍ σ²/ε` and discards `τ log(σ²/ε²)` transitions between queries. This bounds the TV coupling error by `O(e^{-m/τ}C)`, with a two-case drift bound that avoids a global gradient bound. These ingredients are familiar: data-drop or skip sampling, and clipped Markov blocks (the latter appears for PL objectives in [Sarkar et al., arXiv 2606.26316, June 2026](https://arxiv.org/abs/2606.26316)). Their combination for general nonconvex stationarity appears straightforward.

**Search coverage.** I searched on 2026-11-18 (UTC) and read the theorem statements of Beznosikov et al., Dorfman–Levy ([ICML 2022](https://arxiv.org/abs/2202.04428), Thm 4.3), Sun–Wei NeurIPS 2025, and Peng ([arXiv 2607.25785](https://arxiv.org/abs/2607.25785)). Dorfman–Levy needs bounded gradients, finite states and bounded `f`; Peng needs a compact domain and statewise noise bounds, so neither is comparable. I did not read Sun–Wei ICML 2025 (lower bounds), Doan et al., or Even (2023) in full. The theorem entered in commit `c8bf1984` (2026-11-18). The note's citations check out. Sun–Wei's footnote 2 indeed *conjectures* the `Õ(τ(LΔ/ε²+σ²LΔ/ε⁴))` bound under stationary variance. However, it is stated for finite chains parameterized by hitting time. The note's batch-argument sketch of a log-free bound is unproved. The paired lower bound was not reviewed here.

**Conclusion**

**The rate is not better; the gain is dropping the statewise noise bound, at the cost of one logarithm.**

The strongest baseline is Beznosikov et al. (NeurIPS 2023). Combined with plain minibatch GD, it already gives a log-free bound when the noise is bounded in every chain state:

| Noise model | Before | This result |
|---|---|---|
| statewise `σ` (Beznosikov) | `O(τLΔσ²/ε⁴)` | `O(τLΔσ²/ε⁴·log(σ²/ε²))` |
| stationary `σ` only, general states | no end-to-end bound found (conjectured by Sun–Wei) | same |

On the common statewise class the selected result is a logarithm worse, and it also certifies only `E‖∇f‖ ≤ ε`, not `E‖∇f‖² ≤ ε²`. The new instances are oracles whose noise is square-integrable under `π` but unbounded across states, on general state spaces. Finite chains were partly covered already, at an extra `π_min^{-1/2}` cost.

I found no prior end-to-end bound in this model, and Sun–Wei state it only as a conjecture. That supports priority, but it does not prove it. The gain is modest for three concrete reasons: the mechanism is a direct combination of clipping and data-drop spacing; the bound loses a log against the reduction; and the formal theorem covers only `σ ≥ 4096ε` with astronomically large `d`. What can be claimed is a first, log-lossy expected-stationarity upper bound for Markov SGD under stationary variance only.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
