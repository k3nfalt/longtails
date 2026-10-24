# Novelty assessment: RecursiveRelativeErrorConvex

[`result`](../../LongTails/Theorems/RecursiveRelativeErrorConvex.lean) proves that a deterministic recursive Moreau-envelope method ([algorithm](../../LongTails/Algorithms/RecursiveEnvelope.lean)) returns a point with `f(x) − f(x*) ≤ ε` for every adversarial reply sequence. The [setup](../../LongTails/Setups/RecursiveRelativeErrorSmoothConvex.lean) is convex, L-smooth `f` on a real Hilbert space, a minimizer with `‖x₀ − x*‖ ≤ R`, and gradient replies with `‖g − ∇f(x)‖ ≤ α‖∇f(x)‖`. The algorithm knows `L, R, ε`, and the extra regime restriction is `α ≤ e^{−8(1+√log(2+LR²/ε))}/100`.

**Proved complexity** (exact public budget; physical gradient calls; independent of α):

```
N ≤ 4·√(2 + LR²/ε) · (32 + log(2 + LR²/ε))^{32(1 + √log(2 + LR²/ε))} + 1
```

Here L is the smoothness constant, R the initial distance, ε the target objective gap and α the relative-error level. Asymptotically this is `(LR²/ε)^{1/2+o(1)}`, but the o(1) is `≈ 64 log log T/√log T`. Even at `T = LR²/ε → 0` the bound is about 10¹³⁶.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vasin–Gasnikov, [arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376v1) (Mar 2026 preprint), Thm 9.3 (regularized RE-AGM), with the largest admissible τ | `O((√(LR²/ε) + αLR²/ε)·log(LR²/ε))`, for `α ≤ 1/9`, `LR²/ε ≥ 1` → displayed N | At α at the new threshold, `T^{1−o(1)}` → `T^{1/2+o(1)}`. The bound is actually smaller only once `log(2+LR²/ε) ≳ 7.8·10⁵` (computed with VG's constants). | None (the new class is a subset, with α restricted) | None (same last-output objective gap) | Requires `α ≤ e^{−8(1+√log(2+T))}/100`. Far worse for every practical T and whenever `αT log T ≲ N`. |
| Kornilov et al., [arXiv:2310.00506v1](https://arxiv.org/abs/2310.00506v1), Thm 3.1, p=2 (JOTA 2025) | Valid only when `α² ≲ ε/(LR²)`: `O(√T + α^{1/3}T^{2/3} + αT)`. Above that, the `α²LR²` floor prevents accuracy ε → displayed N | Not comparable in most of the new regime. Where both apply (`α ≲ T^{−1/2}`), the prior bound is `O(√T)` and is better. | Covers `T^{−1/2} ≪ α ≤ e^{−8(1+√log(2+T))}/100`, which the prior bound excludes (it has a positive accuracy floor there) | None | Worse by the `T^{o(1)}` factor and an enormous constant wherever the prior bound applies |
| Repository [AcceleratedRelativeErrorConvex](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean) (Lean, 2026-10-14, every α<1) | `⌈7√(T/(1−α)) + 11α²T/(1−α)⌉` → displayed N | Better iff `11α²T/(1−α) > N`. With α = T^{−c}, 0<c<1/4: `T^{1−2c}` → `T^{1/2+o(1)}`. The gain needs `log(2+T) ≳ 8.2·10⁵` even at the largest admissible α. | None | None | Covers only vanishing α. The baseline handles every α<1 and is far smaller for all practical T. |
| Repository two-level proposition, [note "Tightness"](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.md) (hand proof, not machine-checked) | `O((α⁻² + √T + α⁴T)·log(2+T/α²))`, `α ≤ 1/27`, `T ≥ 1` → displayed N | For `α = T^{−c}`, `c < 1/8`: `T^{1−4c}` → `T^{1/2+o(1)}`. Ignoring that bound's constant and log factor, the crossover is at `log T ≈ 8.9·10⁵`. | None | None | Requires the regime cap on α. The two-level scheme is unconditional in α ≤ 1/27. |

**Reduction check.** This is the two-level scheme iterated to depth `d ≈ √(log T/log 4)`. Catalyst-type outer prox schemes ([Lin–Mairal–Harchaoui, JMLR 2018](https://jmlr.org/papers/v18/17-748.html)) and the robust strongly convex inner solver are proof ancestry. Composing published theorems does not give the result: the regularized subproblem receives mixed relative-plus-absolute error, so the pure-relative strongly convex methods ([arXiv:2503.06628v3](https://arxiv.org/abs/2503.06628v3), Thm 4: `α ≲ (μ/L)^{1/2}`) do not apply recursively. The new step is to show that each simulated envelope gradient is again purely relative (`βᵢ = 16βᵢ₋₁`) and to recover the original objective with a total loss factor of at most 2. I did not build the Lean files or run the comparator. A grep found no `sorry`/`axiom` in the RecursiveEnvelope modules.

**Lower-bound conflict.** If correct, the theorem contradicts the literal statement of Vasin–Gasnikov Thm 10.2(1). That statement implies `N ≳ T^{1−o(1)}` when `α = T^{−o(1)}`. Their proof (App. G.3) has two gaps. First, it embeds an absolute-gradient-error oracle into the (δ,L,μ)-oracle class and then invokes the Devolder–Glineur–Nesterov lower bound for that larger class. Second, its stopping test uses the true gradient norm. I agree with the companion note that this does not give a hard instance in the gradient-error class. The repository's hand-proved two-level proposition already conflicted with Thm 10.2 on 2026-10-14.

**Search coverage** (2026-10-24): I searched arXiv and the web for relative and multiplicative gradient error, acceleration, nested and Catalyst-type proximal schemes, and Hallak–Levy (ICML 2024, constrained, unaccelerated). I read the theorem statements of 2603.12376v1 (§7, §9, §10, App. G), 2503.06628v3 (§2, Thm 4–5) and 2310.00506v1 (Thm 3.1). I did not read the JOTA final text of Kornilov et al. I found no prior or later recursive relative-error scheme. The companion note's citations and numbers matched what I checked.

## Conclusion

**Yes, asymptotically: the near-accelerated rate survives a much larger relative error, but only at astronomically large `LR²/ε`.** The strongest applicable baseline is the repository's Lean-verified damped accelerated method. The strongest published one is Vasin–Gasnikov's regularized method.

With `T = LR²/ε` and relative error `α = T^{−c}`, `0 < c < 1/4`:

| Method | Calls |
|---|---|
| Damped acceleration (repo, Lean) | `√T + T^{1−2c}` |
| Vasin–Gasnikov Thm 9.3 | `T^{1−c} log T` |
| This result | `T^{1/2+o(1)}` (budget above) |

So in exponent terms, the tolerated error for near-optimal `T^{1/2+o(1)}` complexity grows from polynomial (`T^{−1/4}`) to subpolynomial (`e^{−O(√log T)}`). If the proof is correct, it also refutes a claimed lower bound.

The gain is real but has no reach: the displayed budget beats every baseline only when `log(LR²/ε) ≳ 8·10⁵`. For every practical T it is worse by many orders of magnitude, it says nothing about fixed α, and no lower bound shows the threshold is sharp. The mechanism is the repository's own two-level nesting, iterated, plus a nontrivial proof that each simulated envelope gradient again has purely relative error.

The comparison establishes an asymptotic gain. My search found no prior result with this tolerance, but that does not prove priority. The claimable contribution is a proof that relative-error tolerance can be subpolynomial in `LR²/ε` while keeping an `(LR²/ε)^{1/2+o(1)}` budget. That is a qualitative, asymptotic statement, not a usable complexity improvement.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
