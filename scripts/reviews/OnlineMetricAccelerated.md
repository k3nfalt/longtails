# OnlineMetricAccelerated: accelerated learning of the optimal diagonal metric

[`result`](../../LongTails/Theorems/OnlineMetricAccelerated.lean) proves the following. Let `f : ℝ^d → ℝ` be differentiable, with unknown `w > 0` and `μ ∈ (0,1]` satisfying `(μ/2)‖y−x‖²_w ≤ f(y)−f(x)−⟨∇f(x),y−x⟩ ≤ ½‖y−x‖²_w`. Suppose the minimum `f⋆` is attained and `f(x0)−f⋆ ≤ Δ`. Then the deterministic [algorithm](../../LongTails/Algorithms/OnlineMetricAccelerated.lean), which uses only `d`, `x0`, and `f⋆`, returns a point with `f(x̂)−f⋆ ≤ ε` within the public budget. Each oracle call returns the pair `(f, ∇f)`. The class is defined in the [setup](../../LongTails/Setups/DiagonalSmoothStronglyConvex.lean).

The parameters are `κ⋆ = 1/μ`, the diagonally preconditioned condition number, and the dimension `d`. Here `Δ` bounds the initial gap, `ε` is the target accuracy, and `log₊ t = max(0, log t)`. Simplifying the exact budget `2(d+1+⌈log₂(Δ/ε)⌉⌈24√κ⋆+log₂d+2⌉+(d⌈log₂κ⋆⌉+1)⌈110d²(1+ln2d)²√κ⋆⌉)` gives

**O( (√κ⋆ + log 2d)·(1 + log₊(Δ/ε)) + d² log²(2d)·√κ⋆·(1 + d log κ⋆) )** oracle calls.

The updates need none of `w`, `μ`, `Δ`, `ε`, or the Euclidean `L`. The stopping budget does need `μ`, `Δ`, and `ε`. The output `x̂` is the start of the current epoch, which is a stopped iterate.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Secant diagonal + AGD with known-`f⋆` restarts. This is a standard reduction: `s_i=∂_if(x0+e_i)−∂_if(x0)∈[μw_i,w_i]`, so the `s`-metric has condition `≤κ⋆²`. The restart step is [Roulet–d'Aspremont, Prop. 4.1](https://arxiv.org/abs/1702.03828) (NeurIPS 2017; arXiv v2 2019) | `O(d + κ⋆(1+log₊(Δ/ε)))` → bound above | `κ⋆ → √κ⋆` in the ε-dependent term. The gain survives when `log(Δ/ε) ≫ d³log²(2d)log κ⋆/√κ⋆` and `√κ⋆ ≫ log 2d`; the speedup then approaches `√κ⋆` | None (same class) | None (both use `f⋆` and give a stopped iterate) | Worse for moderate `ε` because of the `d³log²d·√κ⋆log κ⋆` warm-up. The large constants (110, 24) make the gain mainly theoretical |
| Multidimensional backtracking, ellipsoid ([Kunstner et al., NeurIPS 2023, Thm 5.3 / Thm 1.1](https://arxiv.org/abs/2306.02527)) | `O(√d·κ⋆ log₊(Δ/ε) + d log(L/α₀))` → bound above | `√d·κ⋆ → √κ⋆` in the leading term, with a speedup approaching `√(dκ⋆)` for small `ε` | None (same class, via their eq. (2)) | The `log(L/α₀)` dependence on the initial guess disappears because of the secant box | Requires `f⋆`, which MB does not. Adds the poly(`d`) warm-up |
| OSGM-R ([Gao–Chu–Ye–Udell, COLT 2025; Part I v2, eq. (5), §6.1](https://arxiv.org/abs/2505.23081)) | `O(κ⋆(1+log₊(Δ/ε)) + κ⋆L²‖P₁−P⋆‖²_F)`, capped by `κ log`, with 2 gradient calls per iteration → bound above | `κ⋆ → √κ⋆` in the leading term on worst-case class instances. OSGM's warm-up depends on the spread of `w` through `L²‖P₁−P⋆‖²_F`; this result's warm-up does not | Not comparable: OSGM's full-matrix `κ⋆` can be far below the diagonal `κ⋆` (≈1 on quadratics) | None (both need `f⋆`) | The result loses wherever full-matrix scaling helps. It also loses to the `κ log` branch when `κ` is small |
| Euclidean AGD + known-`f⋆` restarts ([Roulet–d'Aspremont, Prop. 4.1](https://arxiv.org/abs/1702.03828)) | `O(√κ_E·(1+log₊(Δ/ε)))`, where `κ_E ≤ κ⋆·max w/min w` with equality possible in the class → bound above | Gain when `max w/min w ≫ 1` and `ε` is small | None | None | Worse on instances with small `κ_E`, because of the warm-up |

**Reduction check.** I found no standard reduction that gives a `√κ⋆` leading term. The obvious ones only reach the following:
- **Secant metric:** `κ⋆` in the leading term.
- **Box or Jacobi metric (van der Sluis-type):** `√(dκ⋆)` (the companion note's own intermediate).
- **Restarts:** `μ`-adaptivity only.

The new mechanism is the combination of three parts: an AGD potential with the hindsight comparator `x_{s+2}`, a convex cut-based validity factor `V_s`, and AdaGrad-norm learning of the log-metric across epochs.

**Proof ancestry.** These works supply ingredients, not the complexity:
- **Hypergradient cuts:** Kunstner et al., Props 4.2–4.3.
- **Online-learned scaling:** OSGM.
- **Restarts:** Roulet–d'Aspremont.

**Search coverage.** Searched 2026-10-16 (UTC) across arXiv, NeurIPS, and COLT. The search covered the OSGM series ([Part II §5.3, Question 3](https://arxiv.org/abs/2509.11007) poses exactly this goal for known `f⋆`; [SOSGM, Sep 2026](https://arxiv.org/abs/2609.11751) states no Nesterov guarantee in its abstract), HDM ([2502.11229](https://arxiv.org/abs/2502.11229), abstract only), and [preconditioned Nesterov (2505.23510, Thm 2)](https://arxiv.org/abs/2505.23510). That last paper's `√(LΓ/(μe))` rate needs bounded known scalings and is never better than Euclidean AGD. The search also covered accelerated diagonal AdaGrad (Kovalev 2506.23803; Ene et al., not reopened), which needs bounded domains, and matrix-based optimal-diagonal-preconditioning papers, which cover only quadratics with matrix access.

The result was introduced in commit `22df646` on 2026-10-15, and I found no later work. The companion note's citations match what I checked. Note that OSGM's `κ⋆` is a full-matrix quantity by default, so the note answers Question 3 only for diagonal candidate sets, as the note itself says. I did not run builds or axiom audits.

## Conclusion

**Yes: under the same oracle and the same known `f⋆`, the proved leading complexity improves from κ⋆·log(1/ε) to √κ⋆·log(1/ε) for small ε.** The strongest applicable baselines are the secant-diagonal + restarted-AGD reduction and OSGM-R, both at `κ⋆ log(Δ/ε)`. Multidimensional backtracking does not need `f⋆` but pays `√d·κ⋆ log(Δ/ε)`.

| | oracle calls |
|---|---|
| best checked baseline | `d + κ⋆ log(Δ/ε)` |
| this result | `(√κ⋆ + log d) log(Δ/ε) + d³ log²d · √κ⋆ log κ⋆` |

The gain survives once `log(Δ/ε) ≳ d³log²d·log κ⋆/√κ⋆` and `κ⋆ ≳ log²d`, where it is nearly a `√κ⋆` speedup. The result loses for moderate accuracy, in large dimension, and when full-matrix scaling (OSGM) or Euclidean conditioning is already good. It needs `f⋆`, and its constants are large.

The comparison establishes the gain over every checked method. The literature search supports priority: an OSGM paper explicitly lists this rate as open, and I found no prior or subsequent method achieving it. The result is one day old, so unpublished concurrent work cannot be excluded. The claimable contribution is the first accelerated `√κ⋆ log(1/ε)` guarantee that adapts to an unknown optimal diagonal metric with a first-order oracle and known `f⋆`, at the price of an ε-independent poly(`d`) warm-up.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
