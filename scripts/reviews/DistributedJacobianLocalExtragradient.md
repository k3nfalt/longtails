# Novelty review: DistributedJacobianLocalExtragradient

The [theorem](../../LongTails/Theorems/DistributedJacobianLocalExtragradient.lean) proves that, at deadline `budget p`, an event-driven tree protocol ([setup](../../LongTails/Setups/DistributedJacobianStrongGrowth.lean), [algorithm](../../LongTails/Algorithms/DistributedLocalExtragradientProtocol.lean), [tuning/output](../../LongTails/Algorithms/DistributedLocalExtragradientTuning.lean)) outputs `x` with `E‖x − x*‖² ≤ ε²`. The setting has `n` homogeneous workers, each with an unbiased oracle satisfying `E‖g‖² ≤ ρ‖F‖²` (IID samples), where `F` is `L`-Lipschitz, `μ`-quasi-strongly monotone, and has an `M`-Lipschitz Jacobian.

**Bound (elapsed time, branch `ε < R`, `n ≥ 64κG`).** Notation: κ=L/μ, G=2+ρ/8+ρ²/128. Parameters: τ = compute time per call, λ = latency per hop, β = time per bit, h = tree height, d = dimension, R ≥ ‖x₀−x*‖. Substituting `G^T ≤ n/(64κ)` into `q` gives

`B = O( [τρκ² + h(λ+βd log 2n)]·(1+log(d(1+ρMRn/L))) + τκ log(R/ε) + h(λ+βd log(2+ndR/ε))·(κ/T)·log(2R/ε) )`, with `T = min{⌊κ⌋, ⌊log(n/64κ)/log G⌋} ≥ 1`.

If `n < 64κG`, the protocol falls back to root-only SGD, with `B = τ⌈ρκ² log(R²/ε²)⌉`.

Both baselines below are elapsed-time bounds I derived under this setup's network model; neither paper states a timed theorem. Each extragradient step costs two computation waves and two reduce/broadcast passes, so each communication round costs `O(h(λ+β·bits))`. I did not check finite-bit quantization for the baselines, so their rows assume `βd log(ndR/ε) ≲ λ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gorbunov–Berard–Gidel–Loizou, [AISTATS 2022](https://proceedings.mlr.press/v151/gorbunov22b.html), Thm 4.1 (I-SEG, δ=(ρ−1)L², σ=0), **common-query**: minibatch `b≈18ρκ` spread across workers | `κ log(R/ε)·(τ + hλ)` → `τρκ² log(d(1+ρMRn/L)) + hλ log(…) + κ log(R/ε)(τ + hλ/T)` | Communication term divided by `T ≤ log₂(n/64κ)`. Total gain up to factor `T` when `hλ ≳ Tτ` and `log(R/ε) ≳ ρκ log(dρMRn/L)·τ/(hλ)` | None (adds `M`) | None (both last iterate, `E‖x−x*‖²`) | Requires a Lipschitz Jacobian, `n ≥ 64κG^T` (exponential in `T`), and an additive `τρκ²` startup. Worse when `hλ ≲ τ` or at moderate accuracy |
| Same Thm 4.1, **serial** at the root (b=1) | `τρκ² log(R/ε)`, no communication → as above | Better when `ρκτ ≫ τ + hλ/T` and accuracy dominates the startup (`log(R/ε) ≫ log(dρMRn/L)`) | None | None | Same as above. This is also the selected theorem's own fallback |
| Novoselov–Dorn–Dvinskikh–Gasnikov, [arXiv:2610.12641v1](https://arxiv.org/abs/2610.12641) (8 Oct 2026, preprint), §4.2 / Prop. F.4. **Strongly monotone overlap only** | serial `τρκ log(R/ε)`; common-query `κ log(R/ε)(τ+hλ)` → as above | On the overlap, gain up to `T` in the regime `hλ/T ≪ min(ρτ, hλ)` with large `log(R/ε)`. Example (note): κ=T=t, ρ=t², `log(R/ε)=t⁴`, λ=τt², h=1, `n≍d≍64tG^t`: `τt⁷ → τt⁶` | Their class lacks `M` but needs pairwise strong monotonicity; the classes are incomparable | None | Their nonlinear `D_sched` gains from local steps only through the serial schedule. They report lower bounds matching up to `log m` factors for the broader class (I did not verify this); the gain here lies inside that slack |

**Reductions and ancestry.**
- The Novoselov affine result (§3, Thm 3.3, local extragradient with averaging) and Federated Affine VIs ([arXiv:2611.02598](https://arxiv.org/abs/2611.02598)) do not transfer to nonlinear `F` by substitution, because averaging no longer commutes with the extragradient steps.
- Localizing to a Taylor-linearized operator needs a separate bias bound in terms of `M·E‖X−x*‖²`. It also needs a separate global warm start: the median of independent SGD runs.
- That mean/second-moment split, with variance paid for by `n ≥ 64κG^T` workers, is the new mechanism. Taylor-bias control under bounded curvature already appears in Wang–Kale ([arXiv:2602.09164](https://arxiv.org/abs/2602.09164), NeurIPS 2026). Their LIPPAX assumes additive variance and a bounded operator, and its guarantee is a gap bound. I did not verify the note's claim that it needs `ρκ³` local work.
- Gorbunov et al. supply the standard SEG contraction. Beznosikov et al. ([arXiv:2106.08315](https://arxiv.org/abs/2106.08315), NeurIPS 2022) assume uniform bounded variance, so they give no gain in the homogeneous interpolation case.

**Search coverage.** The search was run on 2026-11-19. It covered arXiv and PMLR/NeurIPS sources on local, federated, and stochastic extragradient under strong growth. I read Gorbunov et al.'s Thm 4.1 verbatim. For Novoselov et al., I read their assumptions and Appendix F.2 verbatim, but §4.2, Prop. F.4 and their lower bounds only as model-extracted summaries. I did not open the Wang–Kale PDF or Sadchikov et al. ([arXiv:2409.10478](https://arxiv.org/abs/2409.10478)), or check Newton-type and finite-difference alternatives. The result was introduced in commit `f3fd2499` (2026-11-19; history squashed), after all cited preprints. The companion note's citations are consistent with what I checked. Its separation example is a valid admissible scaling.

**Conclusion**

**Yes, but only modestly: in a latency-dominated, high-accuracy regime with very many workers, the proved elapsed time beats the checked baselines by at most a factor of `T`.** The strongest baselines are serial and common-query stochastic extragradient (Gorbunov et al. Thm 4.1; Novoselov et al. on the strongly monotone overlap). Ignoring bit costs:

| | accuracy-dependent cost | startup |
|---|---|---|
| best baseline | `κ log(R/ε)·(τ + min(ρτ, hλ))` | — |
| this result | `κ log(R/ε)·(τ + hλ/T)` | `(τρκ² + hλ)·log(d(1+ρMRn/L))` |

The gain requires a Lipschitz Jacobian and `n ≥ 64κ(2+ρ/8+ρ²/128)^T`. So `T`, and therefore the speedup, grows only logarithmically in the number of workers. The result loses at moderate accuracy, where the `ρκ²` startup dominates, and when latency is comparable to compute time.

Nonlinear extension of affine local-averaging gains appears to be new: none of the checked works gives a worker-dependent local-depth gain for nonlinear operators under strong growth. Priority is not certain, since I read Novoselov et al.'s nonlinear results only in summary and did not check Newton-type alternatives.

What can be claimed: a new nonlinear local-extragradient analysis under Jacobian regularity, with a fully charged elapsed-time bound. It improves communication time by a logarithmic-in-`n` factor in an explicit regime, and this mirrors the logarithmic worker gain of the affine theory. The verdict is LIMITED because the improvement is bounded by `log(n/κ)` (at most `κ`), requires exponentially many workers, and adds a `ρκ²` startup.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
