# Novelty assessment: LazyAnchoredExtraProximal

For every monotone `F : E → E` on a finite-dimensional real inner-product space with globally `L`-Lipschitz Jacobian and a zero `x⋆` satisfying `‖x₀ − x⋆‖ ≤ D`, the deterministic method returns the last outer iterate `z_N` with `‖F(z_N)‖ ≤ ε` using `N = ⌈(LD²/(mε))^{2/5}⌉ + 1` Jacobian calls and `2¹⁵(m+1)N(log₂(mN)+1)²` operator-value calls ([theorem](../../LongTails/Theorems/LazyAnchoredExtraProximal.lean), [setup](../../LongTails/Setups/UnconstrainedLipschitzJacobianMonotone.lean), [algorithm](../../LongTails/Algorithms/LazyAnchoredExtraProximal.lean)).

Here `L` is the Jacobian-Lipschitz constant, `D` the initial distance bound, `ε` the residual target, and `m ≥ 1` the supplied Jacobian price. This price is also a tuning input. Charging `m` per Jacobian and `1` per value, the total cost is

  `O((m + m^{3/5}(LD²/ε)^{2/5}) · log²(2m + m^{3/5}(LD²/ε)^{2/5}))`,

and this holds for every `m ≥ 1` and `L ≥ 0`. The method also needs no Lipschitz bound on `F`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| AEP Newton, Jiang–Yoon, [arXiv 2609.30212v1](https://arxiv.org/abs/2609.30212) (24 Sep 2026, preprint), Thms 4.4 + 4.6; direct competitor (`H = 0`, same global Assumption 4.1, residual `‖F‖`) | `O(m(1+(LD²/ε)^{2/5})·log(2+LD²/ε))` (each bisection trial uses one `F` and one `DF`) → `O((m + m^{3/5}(LD²/ε)^{2/5})·log²(2m + m^{3/5}(LD²/ε)^{2/5}))` | Factor `≈ min(m, LD²/ε)^{2/5}` up to logs: `m^{2/5}/log(…)` when `LD²/ε ≥ m` | None | None (both use `L, ε`; ours also uses `D, m`. Both output a last iterate) | Ours makes more value calls (`m^{3/5}T^{2/5}` vs `T^{2/5}`) and has an extra log. At `m = O(1)` it is worse by one log. AEP also covers composite inclusions. |
| Zhang et al., [arXiv 2609.23557v1](https://arxiv.org/abs/2609.23557) (20 Sep 2026, preprint), Thms 3.1/5.1; compact `X`, via the verified ball reduction `X = B(x₀,2D)`, `ε/4` | `O(m(1+(LD²/ε)^{2/5}))` → as above | `m^{2/5}/log²(…)` when `LD²/ε ≥ m` | None on the overlap | None | Theirs is log-free and covers constrained VIs |
| LEN, Chen–Liu–Zhang, [ICLR 2025, arXiv 2410.09568v2](https://arxiv.org/abs/2410.09568), Thm 4.1; lazy, but only an **ergodic restricted gap** for convex–concave `f` | gap `ε_g`: `O(m + m^{2/3}(LD³/ε_g)^{2/3})` → `Õ(m + m^{3/5}(LD³/ε_g)^{2/5})` (one-way conversion `ε = ε_g/O(D)`, assuming `‖z_N − x⋆‖ = O(D)`, which the Lean statement does not record) | Exponent `2/3 → 2/5` in `LD³/ε_g` | Minimax → general monotone `F` | Averaged gap → last-iterate residual | Conversion is only one-way |
| `CachedJacobian` (this repository, unmerged branch `ba6da18`, 25 Oct 2026); compact `X`, tangent residual, via the ball reduction | `Õ(m + √(m·LD²/ε))` → as above | `(LD²/(mε))^{1/10}` when `LD²/ε > m` | Not comparable (it covers constraints) | None | Repository overlap only |

**Standard-reduction check.** Plugging a lazy strongly monotone solver into an optimal residual framework gives only `Õ(m + m^{4/5}T^{2/5})`, where `T = LD²/ε`. This composition is reconstructed in the `CachedJacobian` note and not verified here. What is new is an inner solver: Tseng's forward–backward–forward iteration with a frozen Jacobian, an exact relative-error certificate, and per-step cost proportional to the actual step length. Monteiro–Svaiter's Cauchy–Schwarz accounting then gives `m^{3/5}`.

Proof ancestry, not baselines:
- Jiang–Yoon supply the AEP potential (re-derived in Lean).
- Tseng supplies the inner splitting.
- Doikov–Chayti–Jaggi supply the lazy cost model.

**Search coverage (27 Oct 2026).**
- **Checked:** arXiv and proceedings pages for AEP (theorem text read), 2609.23557, 2609.13462 (abstract only), 2608.08463, LEN, lazy Minimax-AIPE ([arXiv 2506.08362](https://arxiv.org/abs/2506.08362), Thm 5.7). Lazy Minimax-AIPE uses a gap criterion on compact domains with extra Lipschitz assumptions and costs `Õ(m + m^{5/7}T^{4/7})`. Also checked [arXiv 2610.03222](https://arxiv.org/abs/2610.03222), which covers convex minimization only. I found no lazy residual result for monotone equations.
- **Not checked:** the full text of 2609.13462, and dimension-dependent cutting-plane methods (`Õ(m + d)`), which beat this bound unless `m^{3/5}T^{2/5} ≪ d`.
- **Note discrepancies:** the note's "uniform `m^{2/5}`" gain ignores the regime `T < m` and the extra log. Its `CachedJacobian` reference is not on `HEAD`.

## Conclusion

**Yes. When Jacobians are priced separately, the proved total cost beats the best known residual guarantee by about `m^{2/5}`.**

The strongest baseline is AEP Newton (Jiang–Yoon). It covers the identical unconstrained class and residual criterion. It is optimal in second-order calls but needs a fresh Jacobian in every line-search trial. With `T = LD²/ε`:

| | weighted cost `m·#DF + #F` |
|---|---|
| AEP Newton | `Õ(m·T^{2/5})` |
| This result | `Õ(m + m^{3/5}T^{2/5})` |

The gain is `m^{2/5}` (minus one log) when `T ≥ m`, and `T^{2/5}` when `T < m`. It disappears when `m = O(1)`: the result is then worse by a log factor. It also uses many more operator values, and it does not handle constraints.

The comparison proves this gain over the published residual methods. It does not establish optimality: the only known lower bound is `Ω(T^{2/5})`. Priority is less certain. Every competitor is a preprint from September 2026, the same groups are actively publishing lazy-oracle results, and I could not exclude unseen concurrent work. The mechanism uses known ingredients, but a lazy inner solver whose cost tracks the actual step length is what beats the naive `m^{4/5}` composition.

What can be claimed is the first lazy-Jacobian residual guarantee for unconstrained monotone equations that I located, with a polynomial `m^{2/5}` improvement in the separately priced Jacobian regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
