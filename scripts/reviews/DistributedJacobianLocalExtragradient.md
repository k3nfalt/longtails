# Novelty assessment: DistributedJacobianLocalExtragradient

[Theorem](../../LongTails/Theorems/DistributedJacobianLocalExtragradient.lean) · [Setup](../../LongTails/Setups/DistributedJacobianStrongGrowth.lean) · [Algorithm/tuning](../../LongTails/Algorithms/DistributedLocalExtragradientTuning.lean)

The theorem proves an elapsed-time bound. On a rooted tree of `n` homogeneous workers, it reaches `E‖x̂−x*‖² ≤ ε²`, where `x̂` is the last projected block iterate. The class is quasi-strongly monotone, `L`-Lipschitz operators with `M`-Lipschitz Jacobian, and the oracle is unbiased with strong growth `E‖g‖² ≤ ρ‖F‖²`. The algorithm is a quantized median warm start followed by `T`-step local extragradient with averaging.

**Bound.** Let `κ=L/μ`, `G=2+ρ/8+ρ²/128` and `J=log(R/ε)`. Here `τ` is the oracle time, `λ` the per-message latency, `β` the time per bit, `h` the tree depth, `d` the dimension, and `R ≥ ‖x₀−x*‖`. If `n < 64κG`, the budget is `τ⌈ρκ²·2J⌉` (root-only SGD). Otherwise `T = min{⌊κ⌋, ⌊log(n/64κ)/log G⌋}`, and since `G^T ≤ n/(64κ)`, the budget is

`O( [τρκ² + h(λ+βd log 2n)]·[1+log d+log(1+ρMRn/L)] + τκJ + h(λ+βd log(2+ndR/ε))·(κ/T)·J )`.

Below, `D = λ+βd log(2+ndR/ε)` is the cost of one refinement message, and `q = 1+32ρMRG^T/μ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Novoselov–Dorn–Dvinskikh–Gasnikov, [arXiv:2610.12641v1](https://arxiv.org/abs/2610.12641) (8 Oct 2026, preprint), eq. (3), Thm 4.3, serial schedule (29). Applies only to the **strongly monotone, `M`-free** class. | One worker runs batched SEG with batch about `4ρ`: `O(τρκJ)`, with no communication → the bound above. | Possible when `J ≫ ρκ(1+log dq)` and `n ≥ 64κG²`: the speedup is about `min(ρτ, τ+hD)/(τ+hD/T) ≤ min(ρ,T)`. **Worse** when `n < 64κG`, where the fallback costs `τρκ²J`, or when startup dominates. | Strong monotonicity → quasi-strong monotonicity. | None. Same criterion `E‖·‖²`. | Needs a Lipschitz Jacobian. Startup costs `ρκ²log(dq)`. Gains require exponentially many workers. |
| Same paper, common-query schedule (29); Gorbunov et al., [AISTATS 2022](https://proceedings.mlr.press/v151/gorbunov22b.html), Thm 4.1 (quasi-strongly monotone, minibatched SEG). | `n ≥ ρκ` gives `κJ` rounds, so `O(κJ(τ+hD'))`. `D'` is the per-round message cost; quantization for this baseline was not checked formally → the bound above. | For large `J`, the communication term shrinks by a factor of `T ≤ log(n/64κ)/log G`. The total gain is about `(τ+hD)/(τ+hD/T)`, which is `≈ T` once `hD ≥ Tτ`. **Worse** when `λ=β=0`, because of the extra startup. | None relative to Gorbunov (also quasi-strongly monotone). | None. | Same as the row above. |
| Novoselov et al., Thm 4.3 lower bound (`D_info`). This is a lower bound, not a competing method. | At least `κJ/D_info` rounds, where `D_info ∋ K/ρ + log 2m/log(2+ρ log 2m/K)`. | Not a rate comparison: with `K=2T`, the new round count `κJ/T` is close in form to the lower bound's `log m` depth term. | — | — | The lower bound counts rounds, not elapsed time. |

**Reduction check.** On the overlap, the nonlinear bound of Novoselov et al. has no `log m` local-depth gain (`D_sched` lacks it). The affine averaging argument does not transfer, because nonlinear means do not commute. Wang–Kale ([arXiv:2602.09164](https://arxiv.org/abs/2602.09164), NeurIPS 2026) bounds curvature-induced bias, but for bounded operators with additive variance and a gap criterion. The proof ancestry is Taylor-bias control plus averaging. The new step is splitting the endpoint mean, which contracts, from its second moment, which grows like `G^T`, and paying for that growth with `n ≥ 64κG^T` workers. I found no prior result that already gives this.

**Coverage.** Searched 18 Nov 2026: arXiv, NeurIPS, AISTATS, and the local-SGD literature on third-order smoothness (Woodworth et al. 2020; Yuan–Ma 2020; Patel et al., NeurIPS 2025). Novoselov's Proposition F.4 and Wang–Kale's theorem text were not read verbatim. All competitors are 2026 preprints, so priority is time-sensitive. The note's claims match the Lean statement. No build or audit was run.

## Conclusion

**Yes, but only modestly: in an extreme regime it reduces the communication time of the best checked distributed extragradient schedules by at most a logarithmic factor in `n`.** The strongest baselines are Novoselov et al.'s serial and common-query batched SEG schedules (2026).

| | elapsed time |
|---|---|
| best checked baseline | `κJ·min{ρτ, τ+hD}` |
| this result | `τκJ + hD·κJ/T`, plus startup `≈ τρκ² log(dq)` |

Here `T ≤ log(n/64κ)/log(2+ρ/8+ρ²/128)`, so the speedup is at most `min(ρ,T)`. Reaching it requires `n ≥ 64κG^T` workers, a latency-dominated network (`hD ≳ Tτ`), and `log(R/ε) ≫ ρκ log(dq)`. The theorem is worse with cheap communication, at moderate accuracy, or for `n < 64κG`, where its fallback costs `τρκ²J`. It also adds a Lipschitz-Jacobian assumption that the baselines do not need, while relaxing strong monotonicity to quasi-strong monotonicity.

What is established is that this nonlinear local-depth gain resembles the affine-style `log m` term in Novoselov et al.'s lower bound; what remains uncertain is priority among very recent preprints. The claimable contribution is the first nonlinear (Jacobian-regular) local-extragradient guarantee whose round count improves with local depth under strong growth. Its gain is real but at most logarithmic in the worker count.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
