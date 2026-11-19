# Novelty review: DistributedJacobianLocalExtragradient

The [theorem](../../LongTails/Theorems/DistributedJacobianLocalExtragradient.lean) shows that, on a rooted tree of `n` workers, the event-driven [algorithm](../../LongTails/Algorithms/DistributedLocalExtragradientProtocol.lean) ([tuning](../../LongTails/Algorithms/DistributedLocalExtragradientTuning.lean)) outputs a point `x̂` with `E‖x̂ − x*‖² ≤ ε²` by elapsed time `B`. The algorithm runs a median-of-SGD warm start, then local extragradient blocks with clipped, quantized averaging. The [setup](../../LongTails/Setups/DistributedJacobianStrongGrowth.lean) assumes `F` is `L`-Lipschitz and μ-quasi-strongly monotone around the root `x*`, has an `M`-Lipschitz Jacobian, and satisfies `‖x₀−x*‖ ≤ R`. Each worker has an unbiased IID oracle with `E‖gᵢ‖² ≤ ρ‖F‖²`. The time model has compute time `τ` per call, per-edge latency `λ` plus `β` per bit, and tree height `h`.

**Proved budget (elapsed time).** Write κ = L/μ.
- If `R ≤ ε`, then `B = 0`.
- If `n < 64κ(2+ρ/8+ρ²/128)`, only the root runs SGD, and `B = τ⌈ρκ² log(R²/ε²)⌉`.
- Otherwise, with depth `T = min{⌊κ⌋, ⌊log(n/64κ)/log(2+ρ/8+ρ²/128)⌋} ≥ 1` (so `κ/T ≤ 2 max{1, κ log(2+ρ²)/log(n/64κ)}`), and using `G^T ≤ n/(64κ)` to bound `q`:

  `B = O( [τρL²/μ² + h(λ+βd log n)]·(1+log(d(1+ρMRn/L))) + τ(L/μ)log(R/ε) + h(λ+βd log(2+ndR/ε))·(1 + (L/μ)log(2+ρ)/log(nμ/(64L)))·log(2R/ε) )`.

  The three terms are startup, local computation, and communication rounds.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Novoselov–Dorn–Dvinskikh–Gasnikov, [arXiv:2610.12641v1](https://arxiv.org/abs/2610.12641) (8 Oct 2026, preprint), §4.2 eq. (3), Prop. F.4, Thm. I.2. Applies to strongly monotone Lipschitz `F`, SGC, intermittent communication; prior, direct competitor. Their rounds-and-calls model is converted here by charging each round `Kτ + 2h(λ+β·bits)`. Their finite-bit implementation is not checked; the conversion is exact for β = 0. | Best of serial `τρκ log(R/ε)` and minibatch extragradient `κ log(R/ε)·(τ + h(λ+βd log(dR/ε)))` (round count `κ log/D_sched`, with `D_sched = max{K/ρ, min{1, nK/ρ}}`) → the rich-branch `B` above. | Communication-round term divided by `T ≤ min{κ, log₂(n/64κ)}`. For β ≈ 0, `Tτ ≤ hλ ≤ ρτ`, and `log(R/ε) ≥ ρκ log(d(1+ρMRn/L))`, the speedup is at least `T/2`. Worse when `n < 64κG`: `τρκ² log` vs `τρκ log`, a loss of factor κ. Also worse at moderate accuracy, because of startup. | Incomparable classes. This result needs the extra `M`-Lipschitz Jacobian. It allows quasi-strong monotonicity and per-worker oracle maps, but their Prop. F.4 proof uses only the root-directed inequality. | None. Both use known parameters and a last/returned-iterate squared distance. | The Jacobian-Lipschitz assumption is global. The gain needs `n ≥ 64κG^T`, i.e. a number of workers exponential in the gain. Total oracle work is `n(s+2TK)`. |
| Gorbunov et al., [AISTATS 2022](https://proceedings.mlr.press/v151/gorbunov22b.html), Thm. 4.1: independent-sample SEG with δ = (ρ−1)L² variance growth. Prior; the special case is minibatch SEG. | Order `κ + (ρ−1)κ²/b` iterations (the coefficient is as reported in arXiv:2610.12641 §4.2; not re-derived here). With `b = n ≥ ρκ`: `κ log(R/ε)(τ + h·comm)` → `B`. | Same as row 1: rounds reduced by a factor `T`, in the same regime. | Same as row 1. | None. | Same as row 1. |
| Wang–Kale, [arXiv:2602.09164v1](https://arxiv.org/abs/2602.09164) (NeurIPS 2026), LIPPAX Thm. 4; Woodworth et al. 2020, [ICML](https://proceedings.mlr.press/v119/woodworth20a.html), local SGD under third-order smoothness. Prior; special case with bounded additive variance. | Not comparable. Their guarantees use σ² (and a bounded operator or a gap criterion). Under SGC, σ must be localized, and the companion note's derivation that this costs `ρκ³` local work was not independently verified. | Not comparable. | Bounded variance → relative (SGC) noise. These are different noise classes, overlapping only after localization. | Gap or objective criterion → squared distance. | Not comparable. |

**Reduction check.** Minibatching, restarts, or composing the cited theorems gives at best `κ log(R/ε)` communication rounds. The new mechanism keeps per-round progress `T` for nonlinear `F`, which breaks the exact affine averaging used in [arXiv:2611.02598](https://arxiv.org/abs/2611.02598). It does so by tracking the endpoint mean separately from its `G^T`-growing second moment, with Taylor bias `M·E‖X−x*‖²` controlled by localization. With `K = 2T`, this per-round progress `T ≍ log n/log ρ` has the order of the `log(2m)/log(2+ρlog(2m)/K)` term in Novoselov et al.'s lower-bound depth `D_info`. Their upper bound lacks that term. Their hard instance (§H.2, flat edges with `b_ε'' ~ 1/ε`) has an unbounded Jacobian Lipschitz constant. So the restricted class is not covered by their lower bound, and its round-optimality is open. The Taylor-bias principle (Wang–Kale, Woodworth et al.) and median amplification are proof ancestry, not competing bounds.

**Search coverage.** On 19 Nov 2026 I searched arXiv and NeurIPS/ICML/AISTATS for local or federated extragradient, SGC, interpolation, and Hessian/Jacobian-Lipschitz local SGD. I read Novoselov et al. v1 (Defs. 2.4–2.5, §4.2, Props. F.4/I.2, Thm. J.12, §H.2) in full. Gorbunov et al. and Wang–Kale were checked only through abstracts and the companion note's or Novoselov's statements. The result was introduced in commit `03f5f1cc` (18 Nov 2026). I found no prior or subsequent nonlinear SGC result with worker-dependent local depth. I found no mismatch with the companion note, which also concedes the regime limits.

**Conclusion**

**Yes, but only marginally: in a narrow, communication-dominated regime with exponentially many workers, it needs fewer communication rounds than the best prior bound.** The strongest baseline is Novoselov et al. (Oct 2026), whose best schedule needs

`κ log(R/ε)` rounds (minibatch EG)  →  `(κ/T) log(R/ε)` rounds here, with `T ≤ min{κ, log₂(n/64κ)}`,

so the elapsed time drops by about `T/2` when latency dominates (`Tτ ≤ hλ ≤ ρτ`) and accuracy is high (`log(R/ε) ≳ ρκ log(dρMRn/L)`).

The gain is at most logarithmic in the number of workers. It requires an added global Lipschitz-Jacobian assumption and an extra startup cost. When `n < 64κ(2+ρ/8+ρ²/128)`, the fallback bound `τρκ² log` is worse than the serial `τρκ log` already known. On the general Lipschitz class, Novoselov et al.'s lower bound already limits any such gain to about a `log n` factor.

The comparison proves a real, regime-specific improvement in round count for nonlinear operators. The search found no prior result giving it, but priority is established only by an absent counterexample. The claimable contribution is a nonlinear local-averaging extragradient analysis that attains the `log n/log ρ` per-round progress on the Jacobian-Lipschitz subclass. It is a modest, regime-bound speedup, not a new problem-class complexity.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
