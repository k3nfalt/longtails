# Novelty assessment: CorruptedFirstOrderDescent

The [theorem](../../LongTails/Theorems/CorruptedFirstOrderDescent.lean) proves the following. Take any differentiable `f : ℝᵈ → ℝ` with an `L`-Lipschitz gradient and `f(x₀) − inf f ≤ Δ`. Clean replies give the value within `ε²/(128L)` and `g(x)`, where `g` is a fixed map with `‖g − ∇f‖ ≤ ε/8`. Along every reachable history, an adaptive adversary may replace up to `k` value–gradient replies arbitrarily. The deterministic [stack-and-vote method](../../LongTails/Algorithms/CorruptedFirstOrderDescent.lean) then outputs a point with `‖∇f‖ ≤ ε` on every seed and fault pattern. It uses `⌈16LΔ/ε²⌉ + 5k + 4` calls ([setup](../../LongTails/Setups/CorruptedFirstOrderNonconvex.lean)).

**Complexity.** With `L > 0`, `ε > 0`, `Δ ≥ 0`, any `d` and any `k ∈ ℕ`, where `L` is the smoothness constant, `Δ` the initial gap, `ε` the gradient-norm target and `k` the number of corrupted calls:

  `N = O(1 + LΔ/ε² + k)` joint value–gradient calls.

The updates and the stopping rule use `L`, `ε` and `k`. `Δ` enters only the budget.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| GD with step `1/L` ([Nesterov, *Lectures on Convex Optimization*, 2018, §1.2.3](https://link.springer.com/book/10.1007/978-3-319-91578-4)), made robust by repeating each query `2k+1` times and taking the majority of the fixed clean vector. This is a folklore reduction, checked here, and it is the direct competitor. | `O((k+1)(1 + LΔ/ε²))` → `O(1 + LΔ/ε² + k)` | Factor `≍ min{k+1, LΔ/ε²}` whenever `LΔ/ε² ≥ 1` and `k ≥ 1`. Example: `k = LΔ/ε²` gives `Θ(T²)` → `Θ(T)`, where `T = LΔ/ε²`. None at `k = 0`. | None: same class | None: both outputs are certified deterministically for every history | The value oracle is also used. Replication needs only gradients, so the new bound requires a joint value reply. Both use known `k`. |
| [Scheinberg–Xie, arXiv 2511.19411 v1 (24 Nov 2025, prior), Thms 1–3, 6](https://arxiv.org/abs/2511.19411): stochastic line search with corrupted zeroth-order and first-order oracles | Not comparable: a high-probability iteration bound `O(ε⁻²)/(p − p_m)` | Not comparable | Incomparable classes. Their failures are independent per query with probability, the value error is bounded a.s. by `ε_f + ε_c`, and gradients are stochastic. Here a deterministic count `k` of replies is corrupted adaptively, with unbounded errors. | Theirs is a high-probability hitting time. Ours is a worst-case returned point. | Their model needs no known `k` or repeatable gradients. It cannot handle `k` adversarially placed, unbounded corruptions. |

**Reduction check.** Replication gives a multiplicative bound. A natural block/checkpoint scheme, which verifies every `B` steps with `2k+1` repeats, gives roughly `T + kB + kT/B`, about `T + k√T` (my heuristic count, not a published bound), not `T + k`. I found no standard reduction that yields the additive bound. The absolute-depth value thresholds and the signed stack potential, in which a clean query gains +1 and a fault loses at most 1, appear to be the substantive mechanism. Proof ancestry: the descent lemma for `1/L` steps and the median/majority arguments. The additive "lie budget" idea resembles searching with lies (Rivest et al., JCSS 1980; cited from memory, not re-read). That is an analogy, not a comparable bound.

**Search coverage.** I searched on 2026-11-19 across arXiv, PMLR/ICML and general web: corrupted or Byzantine oracles, line search with unreliable oracles (Jin–Scheinberg–Xie, NeurIPS 2021; Scheinberg–Xie 2025), robust OCO ([Zhang–Cutkosky, ICML 2025](https://proceedings.mlr.press/v267/zhang25o.html), which gives regret with an additive corruption term for convex losses, not stationarity), and fault-tolerant search. I did not read Maharjan–Watson (FSTTCS 2022), or the Scheinberg–Xie Theorem 3 statement verbatim. Git history shows the result was introduced in commit `dc759af6` (2026-11-19). The companion note's claims agree with the Lean statement. The paired [lower bound](../../LongTails/Theorems/CorruptedFirstOrderLowerBound.lean) `k + ⌊LΔ/(2²⁵ε²)⌋` holds only for `LΔ ≥ 2²⁶ε²` and `d ≥ 2³²(1 + ⌊LΔ/(2²⁵ε²)⌋)⁴`. The upper bound needs neither restriction.

## Conclusion

**Yes: for adversarially corrupted calls, the proved total complexity is better than the natural baseline, and the gain is polynomial.**

The strongest applicable prior approach is clean gradient descent made robust by majority voting over `2k+1` repeats. Here `T = LΔ/ε²`:

| | calls |
|---|---|
| GD + replication | `O((k+1)(1+T))` |
| this result | `O(1 + T + k)` |

The gain is a factor of order `min{k+1, T}`. For example, `k ≍ T` drops from quadratic to linear in `T`. At `k = 0` the bound reduces to the usual GD order. The paired repository lower bound shows `T + k` is unavoidable up to constants in its high-dimensional regime.

The costs: the method needs joint value replies, values accurate to `ε²/(128L)`, repeatable clean gradients, and a known `k`. The corruption model is a worst-case fault count. It is a standard model in fault-tolerant computation, but its use in optimization is motivated only by silent-hardware-fault examples. Probabilistic-corruption analyses such as Scheinberg–Xie cover a different, incomparable class.

The comparison establishes the gain over the replication reduction. The literature search found no prior additive `O(T + k)` stationarity guarantee, but absence of evidence does not prove priority; the fault-tolerant query-complexity literature is the main unchecked area. The claimable contribution is a deterministic `O(LΔ/ε² + k)` bound for reaching an ε-stationary point when `k` value–gradient calls are adversarially corrupted, with a matching-order lower bound in high dimension.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
