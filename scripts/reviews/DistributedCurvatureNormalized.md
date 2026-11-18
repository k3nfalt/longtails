# DistributedCurvatureNormalized: Hessian-Lipschitz downlink savings in distributed elapsed time

[`result`](../../LongTails/Theorems/DistributedCurvatureNormalized.lean) builds an event-driven star-network algorithm ([DistributedNormalizedTraining](../../LongTails/Algorithms/DistributedNormalizedTraining.lean) → [DistributedNormalizedProtocol](../../LongTails/Algorithms/DistributedNormalizedProtocol.lean)) and proves the following for every homogeneous objective in [`DistributedHessianLipschitzNonconvex.spec`](../../LongTails/Setups/DistributedHessianLipschitzNonconvex.lean). The objective has an `L`-Lipschitz gradient and a `Q`-Lipschitz Hessian, and each of the `n` workers has an unbiased oracle with variance `σ²`. Then a uniformly chosen pre-update coordinator iterate `X` satisfies `E‖∇f(X)‖ ≤ ε` by a deterministic deadline, and execution finishes in finitely many events almost surely.

**Proved elapsed time** (O-bound with universal constants suppressed, derived from the Lean `budget`):

```
T = O( (1 + LΔ/ε²) · [ ℓ + H + σ²H/(nε²) + √(dσ²H·b·log(2+d+LΔ/ε²+min{σ²/ε²,n}) / (nε²))
        + b·log(2+d+LΔ/ε²+min{σ²/ε²,n}) · (1 + d·n^(-1/3) + d·min{1, √(Qε)/L}) ] )
```

The parameters are:

- `Δ`: the initial gap.
- `H = max_i h_i`: the deterministic time per gradient.
- `ℓ`: the latency of a packet.
- `b`: the time per bit.
- `d`: the dimension.

This bound is tight up to constants for the Lean formula. The precision widths satisfy `B_u, B_s = Θ(log(…))`. The Lean terms `dc_u/n` and `dc_s/√n` are absorbed into `(d³c_uc_s²/n)^{1/3} = Θ(d·b·log/n^{1/3})`.

In the table below, `Λ` stands for the log factor shown above, and `κ = τ` is a per-coordinate cost, mapped to `b·Λ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Begunov–Tyurin, Inkheart SGD, [arXiv:2605.07795v2](https://arxiv.org/abs/2605.07795v2) (v1 8 May 2026, v2 19 Oct 2026), Thm 2.2 with Props 1.7/1.9. **Prior.** Its target `E‖∇f‖²≤ε_ink` is used with `ε_ink=ε²`. I granted the mapping `κ=τ≈bΛ`. | `(LΔ/ε²)[H + bΛ(1+d/n^{1/3}) + √(dσ²HbΛ/(nε²)) + σ²H/(nε²)] + dbΛ·L_A·Δ/ε²` → the same frontier plus `ℓ(1+LΔ/ε²)`, with the downlink term replaced by `dbΛ·Δ·min{L/ε², √Q/ε^{3/2}}` | The downlink term shrinks by a factor `L_A/min{L,√(Qε)}`. **Verified instance:** `f=Σⱼ(1−cos xⱼ)` has `L=Q=1` and needs `L_A ≥ 2/π`. Take `d=ε^{-7/4}`, `n=ε^{-3/2}` and fix the other parameters. Then the time goes from `ε^{-15/4}Λ` to `ε^{-13/4}Λ`. | Neither class contains the other. Inkheart: smooth `f`, with the rate driven by `L_A`. This result: `Q`-Hessian-Lipschitz `f`, and no small `L_A` is needed. | Expected time → a fixed deterministic deadline | The accuracy criterion is weaker: `E‖∇f‖²≤ε²` becomes `E‖∇f‖≤ε`. Uses `max_i h_i`, whereas Inkheart §4 handles heterogeneous `hᵢ`. Loses when `L_A<√(Qε)`, for example on near-quadratics. Inkheart counts real-valued coordinates and has no latency term. |
| Minibatch synchronous SGD: Inkheart eq. (2), and in this repository [`DistributedBatchedSgd`](../../LongTails/Theorems/DistributedBatchedSgd.lean) on the same network (its `ε` there stands for `ε²`) | `(1+LΔ/ε²)(ℓ + H + σ²H/(nε²) + dbΛ)` → `T` | A gain whenever `dbΛ` dominates `ℓ+H+σ²H/(nε²)`. The speedup is up to `min{n^{1/3}, L/√(Qε), √(dbΛnε²/(σ²H))}`. | None: Hessian-Lipschitz `f` is a subclass of smooth `f` | `E‖∇f‖²` → `E‖∇f‖` (weaker) | Requires `Q`. The repository result uses heterogeneous `hᵢ` (better compute term). |
| Cutkosky–Mehta NIGT, [ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html), Thm 3 ([arXiv v2](https://arxiv.org/abs/2002.03305)). **My reduction:** average one gradient per worker (`σ²→σ²/n`) and exchange full vectors. **Same class and criterion.** | `[LΔ/ε² + Δ√Q·σ²/(nε^{7/2}) + (σ²/n)^{13/6}/(Δ^{4/3}Q^{2/3}ε^{7/3})]·(ℓ+H+dbΛ)` → `T` | **Two-sided.** In the scaling above, `ε^{-15/4}Λ → ε^{-13/4}Λ`. **Worse:** for fixed `d,n` with `σ>0`, `T ≍ σ²HLΔ/(nε⁴)`, which exceeds NIGT's `ε^{-7/2}` term. | None | None (both report a uniform random iterate with `E‖∇f‖`) | Without acceleration of the per-iterate drift, the leading `ε^{-4}` noise term remains |

**Reductions and proof ancestry.** I found no standard reduction that gives `T`:

- Inkheart's Prop 1.9 bounds `L_A` by a sup of Hessian *deviations*. That bound is not small under a Hessian-Lipschitz assumption on all of `ℝᵈ`.
- MARINA-P/M3 ([arXiv:2402.06412v2](https://arxiv.org/abs/2402.06412), Thm 4.6, Cor 4.7 and Thm 5.1; deterministic gradients) keep the same `dL_AΔ/ε` term.
- Minibatched NIGT pays the full-vector cost `d` on every round.

The selected budget reproduces Inkheart's Rand-1 time frontier `t` exactly, and Cutkosky–Mehta supply the normalized norm-error descent. The new ingredient is the quadratic Taylor bound `‖n⁻¹Σ∇f(x+eᵢ)−∇f(x)‖ ≤ L‖ē‖ + Q·n⁻¹Σ‖eᵢ‖²`. It is applied conditionally on fresh downlink errors and only in first moment, which avoids fourth moments. I read this from the proof-module structure and the note; I did not audit the Lean proofs or run builds.

**Search coverage (2026-11-18 UTC).**

- **Read at theorem level:** Inkheart v2 (HTML), MARINA-P v2 and NIGT, together with arXiv/web searches for Hessian-Lipschitz or curvature-based downlink compression.
- **Not verified at theorem level:** Li–Lin (JMLR 2023) and an ICLR 2026 double-optimism result (`ε^{-1.75}+σ²ε^{-3.5}`, seen only as a snippet). Both are accelerated, but in a parallel version they still pay `d` per round, so in the scaling above they plausibly also give `≈ε^{-15/4}`. For `σ=0` and fixed `n` they beat `T` as `ε→0`. Also unverified: local-SGD analyses (Glasgow et al.; Luo et al.), Chayti et al.'s lazy-Hessian reduction and Tyurin's lower bound ([arXiv:2506.23836](https://arxiv.org/abs/2506.23836)).
- **Companion note:** its descriptions of Inkheart and its exponents agree with what I checked.
- **Chronology:** the result was introduced in commit `b9802a4a` (18 Nov 2026), after both Inkheart versions.

**Conclusion**

**Yes: when the dimension and the number of workers are large, the proved elapsed time is polynomially better than the checked baselines, because Hessian-Lipschitz curvature replaces Inkheart's `L_A` in the downlink cost.** The strongest prior method, Inkheart SGD, pays `d·b·L_A·Δ/ε²` for server-to-worker traffic. That cost does not shrink with `n`, and for genuinely nonquadratic objectives `L_A` is of order `L`.

```
Inkheart downlink:  d·b·L_A·Δ/ε²      →      this result:  d·b·Δ·min{L/ε², √Q/ε^{3/2}}   (up to log factors)
```

A separable cosine objective satisfies every assumption and forces `L_A ≥ (2/π)L`, which shows the gain is real on a valid instance. Take `d≈ε^{-7/4}` and `n≈ε^{-3/2}`. Then the total time improves from `ε^{-15/4}` to `ε^{-13/4}` (up to logs) against Inkheart, synchronous SGD and parallel NIGT.

The result is not uniformly better. It needs a known `Q`, certifies the weaker criterion `E‖∇f‖≤ε` rather than `E‖∇f‖²≤ε²`, and is worse than Inkheart when `L_A<√(Qε)`. For fixed `d` and `n` it is also worse than parallel NIGT, by a factor `ε^{-1/2}` in the noise term. I found no prior curvature-based downlink bound, but that is not proof of priority, and accelerated parallel competitors were not checked at theorem level.

What can be claimed is a new elapsed-time upper bound for compressed bidirectional distributed training under Hessian-Lipschitz smoothness, with an `ε^{-1/2}` gain in the high-dimensional regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
