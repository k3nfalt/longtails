# Cyclic full-width quadratic Perceptron: novelty assessment

The [theorem](../../LongTails/Theorems/CyclicFullWidthPerceptronAcceleration.lean) proves the following. Take the signed data `e=(1,0)` and `q_i=(−(1+ν_i), −μu_i)`, `i<N`, with `‖u_i‖≤1`, a unit `w` satisfying `⟨w,u_i⟩≥κ`, `μ≤κ⁴/2²⁰` and `0≤ν_i≤ν̄≤κ¹²μ²/2⁵⁶` ([setup](../../LongTails/Setups/CyclicFullWidthPerceptron.lean)). The noiseless cyclic two-layer Perceptron `W⁺=W+ηvqᵀ, v⁺=v+ηWq` is started at `W=I, v=0` with `η=κ⁶/2²⁸` ([algorithm](../../LongTails/Algorithms/CyclicFullWidthPerceptron.lean)). Deterministically, its last iterate strictly separates all `N+1` examples after `(N+1)⌈256/κ⁴⌉` per-example oracle calls.

**Complexity:** `O((N+1)/κ⁴)` calls. Here `N` is the number of negative examples, `κ` the latent margin, `μ` the residual scale and `ν̄` the offset bound. The bound holds only in the slab above, and it is independent of `μ`, `ν̄` and the dimension `d`. The updates use `κ`; the budget uses `κ` and `N`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Read-then-solve: query each index once at `W=I, v=0`. The reply's `Wq` block equals `q`, so an offline LP then gives a separator `(W=I, v=z)`. Folklore; checked against `answer` in the setup. | `N+1` → `(N+1)⌈256/κ⁴⌉` | Worse by a factor of `256/κ⁴` in every regime | None. LP works for every separable dataset, with no slab. | None. LP needs no parameters and outputs a strict separator. | Selected: slab restrictions, `κ` must be known, `O(d²)` arithmetic per step. LP: superlinear offline arithmetic. |
| Novikoff's Perceptron on the rescaled data `(x₀, x′/μ)`, i.e. the linear update `v⁺ = v + (q₀, q′/μ²)` (standard reduction; μ is public) | `(N+1)(11/κ²+1)` → `(N+1)⌈256/κ⁴⌉` | Worse by a factor of order `κ⁻²` | None. The reduction does not need the slab. | Selected updates and budget do not use `μ`; the rescaled method needs `μ`. Both stop with a strict separator, and the rescaled method can certify one with a mistake-free pass, without `κ`. | Rescaled method needs `μ`; selected method needs `κ` |
| Constant-step linear Perceptron from zero, any order: more than `1/(2μ²)` calls ([repo comparison](../../LongTails/Proofs/CyclicPerceptronLinearComparison.lean)). Novikoff gives `O((N+1)/(μ²κ²))`. | `>1/(2μ²)` → `(N+1)⌈256/κ⁴⌉` | Better whenever `(N+1)⌈256/κ⁴⌉ < 1/(2μ²)`. For example, with `κ` fixed, `μ=κ⁴/(2²⁰(N+1))` gives `O(N)` vs `Ω(N²)`. | None. Same data class, no step-size or order retuning. | Same strict-separation, last-iterate output | Gain is only against a deliberately weak baseline, i.e. one that never rescales |
| Tyurin, [arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587v2) (21 May 2026; [ICML 2026, PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html)), Thm 5.1. **Special case, not overlapping:** two samples, eq. (5). | `Θ̃(√d/μ)` w.h.p. (noisy QPA, tuned `σ`) → not applicable | Not comparable: per the companion note, Tyurin's dataset lies outside the `ν̄`-slab | Many conflicting residual directions, rather than Tyurin's two-sample instance | Noise-free and deterministic, rather than high-probability with tuned noise | Full width rather than a size-2 convolution. Slab and powers of `κ`. |

To derive the second row, map `ẽ=(1,0)` and `q̃_i=(−(1+ν_i),−u_i)`, so `R²≤2.01`. The separator `(κ/2,−w)` has normalized margin `≥0.43κ`, so the Perceptron makes at most `11/κ²` mistakes. Every full pass before separation contains a mistake, which bounds the call count. The step-size and scale tuning stays inside the oracle model, because keeping `W=I` makes each reply expose `q`.

**Reductions and mechanism.** Standard reductions already beat the selected bound: data recovery plus LP, or the Perceptron after a diagonal rescaling with the known `μ`. What is genuinely new is the proof mechanism for the factorized method: cyclic mistake pairing, an approximate dual-cone energy argument, and finite-error control. Proof ancestry includes Novikoff's argument and the factorization-as-preconditioning view of Arora–Cohen–Hazan ([ICML 2018](https://proceedings.mlr.press/v80/arora18a.html)). Neither supplies this discrete many-sample bound.

**Search coverage.** Searched on 2026-10-24 UTC: arXiv, PMLR/ICML 2026, the Tyurin v2 HTML theorems, Cesa-Bianchi–Conconi–Gentile's second-order Perceptron (Thm 3.1, read but not specialized here) and forward-citation searches. I found no prior many-sample implicit-acceleration theorem for QPA. Tyurin proves acceleration only for two samples and reports larger datasets only empirically. The companion note's NeurIPS 2026 OpenReview item was not accessible to me. The note correctly concedes that it does not improve on stronger linear methods, consistent with the table above.

## Conclusion

**No: as a classification algorithm on this data class, it is beaten by simple methods that use the same oracle.** The strongest baseline reads each example once and solves an LP. A rescaled linear Perceptron is also faster:

| Method | Oracle calls |
|---|---|
| Read + LP | `N+1` |
| Rescaled linear Perceptron (knows μ) | `O((N+1)/κ²)` |
| This result | `O((N+1)/κ⁴)` |

Both baselines cover every separable dataset, so neither the scope nor the output criterion improves. The only gain is against the constant-step linear Perceptron without rescaling, which needs more than `1/(2μ²)` calls. That gain is substantial when `(N+1)/κ⁴ ≪ 1/μ²`, but that baseline is weak by construction.

As a statement about the dynamics, the result is more interesting. The search found no earlier proof that Tyurin's unperturbed factorized Perceptron is implicitly accelerated beyond two samples. Its updates and budget also do not need `μ`. However, the data class is artificial, with a narrow offset slab and large powers of `κ`, and a lack of competing papers is weak evidence of priority.

The claimable contribution is a new method-specific analysis: deterministic implicit acceleration of the cyclic full-width quadratic Perceptron for many conflicting directions. It is not a better guarantee for linear classification.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
