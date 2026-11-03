# Two-sided convolutional perceptron acceleration on arbitrarily many samples

[Lean theorem](TwoSidedConvolutionalPerceptronAcceleration.lean)
(`OracleTemplate.TwoSidedConvolutionalPerceptron.result`),
[setup](../Setups/TwoSidedConvolutionalPerceptron.lean),
[algorithm](../Algorithms/TwoSidedConvolutionalPerceptron.lean),
proof modules `LongTails/Proofs/TwoSidedPerceptron{Dynamics,Potential,Trajectory,Contraction,Counting,Trace,Geometry,Execution,Parameters}.lean`,
explicit instances and linear-model comparison in
`LongTails/Proofs/TwoSidedPerceptron{Instances,LinearComparison}.lean`.

## Summary

The result is a deterministic, contrast-free separation bound for the **quadratic perceptron algorithm
(QPA)** of A. Tyurin, *Gradient Descent as a Perceptron Algorithm: Understanding Dynamics and Implicit
Acceleration* ([arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587v2), ICML 2026,
[PMLR 306](https://proceedings.mlr.press/v306/tyurin26a.html)), on the two-tap convolutional model
`m(b; c, v) = ⟨c₁ b + c₂ P b, v⟩` of that paper, for **arbitrarily many samples** whose two classes
both carry a common background of arbitrary (sample-dependent) intensity and small class-specific
details that are linearly separable after the fixed two-tap difference filter. Starting from the
identity kernel `(1, 0)` with zero readout, the cyclic QPA makes at most
`⌈2²⁴ (R/g)² (1 + log(1 + g/µ)) / κ³⌉` mistakes, hence `(N)·⌈…⌉` oracle calls, independently of the
dimension and logarithmic in the inverse contrast `1/µ`. On an explicit subfamily inside the same
class, the fixed-step batch perceptron (the gradient-descent limit of the *linear* model, Tyurin AAAI
2025 Thm 3.2) and the cyclic perceptron need more than `1/µ` updates. This is the implicit-acceleration
phenomenon of Tyurin's two-sample Theorem 5.1 (`Õ(√d/µ)` versus `Ω(d/µ)`), established for a natural
`N`-sample class, with a mistake bound logarithmic in `1/µ` (against the paper's polynomial `1/µ`
dependence) in the regime where the slow block is favourable (see "What is and is not claimed").

## Setup (`LongTails/Setups/TwoSidedConvolutionalPerceptron.lean`)

Let `e = 1_d/√d` and `P` the cyclic shift. The instance is a family `D : Fin (N) → ℝ^d` of
**signed** samples (`N = samples + 1 ≥ 1`), admissible when a `Geometry` certificate exists:

* `D i = α_i e + µ u_i` with `g ≤ |α_i| ≤ R` (both signs allowed: positives and negatives both have a
  background, with arbitrary intensities in `[g, R]`),
* `u_i ⊥ e`, `‖u_i‖ ≤ 1/√2`,
* a unit vector `w` with `κ ≤ ⟨(u_i − P u_i)/√2, w⟩` for every `i` (derivative margin).

The parameters are `(d, samples, g, R, µ, κ)`; the certificate (`α, u, w`) is not supplied to the
algorithm. The oracle returns, for a queried index `i` and point `θ = ((c₁,c₂), v)`, the exact signed
margin `m(D i; θ)` and its full parameter gradient; every query is one call.

`valid` requires positivity, `g ≤ R`, and the single regime inequality
`κ µ ⌈2²⁴ (R/g)² (1 + log(1 + g/µ)) / κ³⌉ ≤ 3R/2`, i.e. `δ·K ≤ 1/64` with `δ = κµ/(96R)` the
normalized contrast step and `K` the mistake budget; it is exactly the smallness used by the proof.

`allowedAlgorithm` (`family`) enforces the algorithm family: cyclic query order starting at index 0,
start at the identity kernel `((1,0), 0)`, the mistake update
`θ ← θ + η ∇_θ m(D i; θ)` on a nonpositive margin (unchanged otherwise), last iterate as output, and a
step size `η > 0` left to the algorithm.

**Accuracy criterion.** `Separates D θ`: every signed margin `m(D i; θ)` is strictly positive.

## Algorithm (`LongTails/Algorithms/TwoSidedConvolutionalPerceptron.lean`)

The cyclic quadratic perceptron with simultaneous updates of filter and readout, step
`η = κ/(96 R)`, identity start. It knows only `(d, samples, g, R, µ, κ)` through `η` and the scan
length; it never sees `α`, `u` or `w`. The output is the actual final point of `execute`.

## Main theorem

`result : Convergence spec budget` with the one-line budget

```
(samples + 1) * ⌈2^24 * (R/g)^2 * (1 + log(1 + g/µ)) / κ^3⌉₊
```

For every valid parameter vector, every admissible instance and every oracle seed, the output after
this many calls strictly separates all `N` samples. Separately (`mistakes_le` in the Counting module,
`length_lt` in the Trace module) the number of mistaken updates is at most
`⌈2²⁴ (R/g)² (1 + log(1 + g/µ)) / κ³⌉ − 1`; the factor `N` is the cost of the cyclic scan, which
also counts the correct visits that certify separation.

## Mechanism and proof

Write the filter as mean/difference `a = (c₁+c₂)/√2`, `t = (c₁−c₂)/√2`, the readout as
`v = q e + z` (`z ⊥ e`), and the residual features `p_i = (u_i+Pu_i)/√2`, `r_i = (u_i−Pu_i)/√2`.
With `c_i = √2 η α_i`, `δ = ηµ`, one mistake update on sample `i` is exactly
```
a ← a + c_i q + δ⟨p_i,z⟩,  q ← q + c_i a,  t ← t + δ⟨r_i,z⟩,  z ← z + δ(a p_i + t r_i),
```
and the signed margin is `η⁻¹[c_i a q + δ(a⟨p_i,z⟩ + t⟨r_i,z⟩)]`. The background of **every** sample
is governed by the single product `a·q`: the (a,q) block is a hyperbolic map
(`s = a+q ↦ (1+c_i)s`, `h = a−q ↦ (1−c_i)h`, plus the forcing `δ⟨p_i,z⟩`), while the difference channel
`(t, z)` runs a perceptron on the derivative features with coefficient `t`.

1. **Contraction phase.** While the background dominates, every mistake switches the (a,q) block in
   the contracting direction and two consecutive mistakes shrink `W = |s|+|h|` by `(1 − c_lo²/8)`,
   where `c_lo = √2 η g`; expanding mistakes are gated (`|c_i a q| ≤ δ(|a|+t)‖z‖`) and only move `W` by
   `O(δ(|a|+t)‖z‖/W)`. After `O(c_lo⁻² log(g/µ))` mistakes, `W` is at the scale `δ`.
2. **Potential.** `Ψ = ‖z‖² + W²/(4 − 4C)` (`C = √2 η R`) satisfies, at every mistake,
   `ΔΨ ≤ 4C δ(|a|+t)‖z‖ + δ²(|a|+t)² + 3W·δ‖z‖ + 2(δ‖z‖)²`: at a contracting mistake the pollution
   `2|c_i a q|` of `‖z‖²` is paid exactly by the decrease `(8−8C)|c_i a q|` of `W²`; at an expanding
   (residual-driven) mistake the payment `−2|c_i a q|` of `‖z‖²` covers the increase `(8+8C)|c_i a q|`
   of `W²` up to the stated `O(C)` excess. No cone, cap or bootstrap tower is needed.
3. **Progress.** `⟨z, w⟩` grows by at least `δ(tκ − |a|)` at every mistake, while `‖z‖ ≤ √Ψ`. The
   perceptron-type comparison of growth and progress, with the `O(C)` excess absorbed by the margin-tuned
   step `C ≤ κ/65`, gives the mistake bound `O(κ⁻³ (R/g)² log(R/µ) + κ⁻²)`.
4. `t` is controlled only through `|t' − t| ≤ δ‖z‖` and the regime, so `t ∈ [t₀/2, 2t₀]` throughout.

All of this is formalized for an abstract switched system (`Dynamics`, `Potential`, `Trajectory`,
`Contraction`, `Counting`), then connected to the model (`Geometry`: `encode θ`, exact margin and step
identities), to the cyclic scan and `execute` (`Trace`, `Execution`), and to the public parameters
(`Parameters`, which derives every smallness condition from the single `valid` inequality).

## Explicit instances and the linear comparison (`Instances`, `LinearComparison`)

For every `k ≥ 0` and `µ > 0` the module `Instances` builds `N = 2k+2` samples in dimension `4k+8`:
positives `e + µ u_i`, negatives `−((1+µ) e − µ u_i)` (signed), with residuals
`u = (E₀−E₁)/8 ± (E₂−E₃)/4 + (E_{2i+4} − E_{2i+5})/8` (sign `+` for positives, `−` for negatives).
It proves the `Geometry` certificate with `g = 1`, `R = 1+µ`, `κ = 1/6`, separator `−E₁`, that the
residuals are linearly independent (rank `N`), and that the Gram matrix has mixed signs
(`⟨u_i, u_j⟩ < 0` across classes). The intensities are mismatched by `µ` (`1` versus `1+µ`), as in
dataset (5) of the paper.

`LinearComparison` proves, for the same vectors (abstractly, for any `m ≥ 1`, any residuals
`‖u_i‖ ≤ 1/√2`, `u_i ⊥ e`, any `0 < µ ≤ 1/4`, any step `ϕ > 0`):

* **batch perceptron** `z ← z + (ϕ/N) Σ_{i : ⟨a_i,z⟩ ≤ 0} a_i` from `z₀ = 0` (the GD limit of the
  linear model, Tyurin AAAI 2025 Thm 3.2; the comparator of Tyurin's Thm 5.2): for every `t` with
  `t µ ≤ 1` the iterate `z_t` misclassifies some sample (`batch_not_separated`). The background
  coefficient alternates between `(ϕ/2)(1 − kµ)` and `−(ϕ/2)(k+1)µ` while the residual part has norm
  `≤ tϕµ/√2`, exactly the Thm 5.2 trace;
* **cyclic perceptron** in the data order: each of the first `⌊1/µ⌋ + 1` visits is a mistake
  (`cyclic_all_mistakes`), so it makes `Ω(1/µ)` updates and `Ω(1/µ)` calls before any separator.

Hence on this subfamily the linear GD limit needs `Ω(1/µ)` steps while the nonlinear GD limit needs
`O(log(1/µ))` mistakes (and `O(N log(1/µ))` calls). The two statements use the same vectors, the same
zero predictor at the start, the same strict-separation criterion, and (for the cyclic bound) the same
query order; the batch bound counts full-data steps (`N` calls each).

## What is and is not claimed

* **Scope.** The class is the natural `N`-sample version of the paper's dataset (5): a common
  background with sample-dependent intensity and faint class-specific details visible to a two-tap
  edge filter. `N`, `d`, the intensities and the residual directions are arbitrary (interacting,
  mixed Gram signs, full rank allowed). Both classes may carry details.
* **The paper's own instance is excluded.** `κ > 0` requires `r_i ≠ 0` for every sample, so a
  pure-background sample such as `b₁ = 1_d` is not admissible: dataset (5) is only the `κ → 0`
  boundary of the class. The theorem generalizes the *phenomenon*, not Theorem 5.1's instance.
* **Favourable slow block.** The identity start has `t₀ = a₀`, so the difference channel is active
  from the beginning. In the two-sample repository theorem this is the case `ρ = 1`, which already
  gives logarithmic time there. The `log(1/µ)` rate is therefore a different regime from the paper's
  `√d/µ` (random start, slow block must grow); it is not an improvement of Theorem 5.1 on comparable
  terms, and generic (Gaussian) starts are **not** covered.
* **Method versus method.** As in the paper, the comparison is between the GD limit of the
  convolutional model and the GD limit of the linear model from the zero predictor. Since `e` is
  public, "center the data, then run the perceptron" costs `O(N/κ²)` calls, and the oracle reveals
  every sample in `N` calls, so no problem-class oracle complexity is claimed. Second-order and
  smooth/accelerated perceptrons are stronger linear baselines outside this comparison.
* **Worst case over the class.** The QPA bound is uniform over the class; the linear lower bound holds
  on the explicit subfamily. For balanced intensities (`α = ±1`) or rational intensity ratios the
  zero-init perceptron can be fast; the claim is not per-instance dominance, exactly as Thm 5.1 vs 5.2.
* **Step size.** The proof uses the margin-tuned step `η = κ/(96R)`; the paper's `Θ(1/R)` step is not
  covered by the proof (all simulations, with `η = 1/(2R)`, show the same logarithmic behaviour), and
  the linear comparator needs no tuning. The extra `κ⁻²` in the contraction phase is the price.
* **Constants and regime.** The constants (`2²⁴`, `96`) are not optimized. The regime
  `δ K ≤ 1/64` is a sufficient condition from the proof; on the instance family it holds for all
  `µ ≤ 2⁻⁴⁸` (`Instances`), while numerically the method separates for `µ` up to `0.5`. A purely
  polynomial convenience condition (not in Lean) is `µ ≤ κ⁴ g³ / (2⁵⁰ R²)`: it implies the `valid`
  inequality via `1 + log(1 + g/µ) ≤ 2 √(g/µ)` and `κ ≤ 1`, so `κ µ K ≤ 2²⁵ R² √µ /(κ² g^{3/2}) + κ µ ≤ 3R/2`.
* **Deterministic, noiseless.** No Gaussian perturbation (Section 4 of the paper) is used or needed.

## Closest prior results

| Result | samples / data | model, rule, start | guarantee |
|---|---|---|---|
| Tyurin 2026, Thm 5.1 | 2, dataset (5) | conv k=2, priority rule + Gaussian noise, generic start | `Õ(√d/µ)` w.h.p. |
| Tyurin 2026, Thm 5.2 | 2, dataset (5) | batch linear perceptron, small start | `Ω(d/µ)` |
| Repo `TwoSampleQuadraticPerceptronAcceleration` | 2 | conv k=2 / two-layer, priority rule, data-dependent cone | `Õ(√d/µ)`, `O(log)` when `ρ = 1` |
| Repo `ManySampleConvolutionalPerceptronAcceleration` | N, pure positive reference | conv k=2, restart scan + deterministic kick, `((√2,0),0)` | `2³⁵ (R/g)⁴ ℓ² (N + (R/g)ℓ)/κ²` |
| Repo `ClusteredConvolutionalPerceptronAcceleration` | N, cap `‖u_i − u⋆‖ ≤ κ/64` | conv k=2, cyclic, κ-encoded start | `N(128 (R/g)² log(16R²/µ²) + 3)` |
| Repo `CyclicFullWidthPerceptronAcceleration` | N, offset slab `ν ≤ κ¹²µ²/2⁵⁶` | full-width two-layer, cyclic, `(I, 0)` | `(N+1)⌈256/κ⁴⌉` |
| **This result** | N, two-sided intensities in `[g,R]`, derivative margin on all samples | conv k=2, cyclic, identity start `((1,0),0)`, step `κ/(96R)` | `N ⌈2²⁴ (R/g)² (1+log(1+g/µ))/κ³⌉`, deterministic |

Relative to the repository results, the present theorem removes the cluster cap and κ-encoded start
(Clustered), the pure reference and the kick (ManySample), and the offset slab and full-width model
(CyclicFullWidth), keeps a data-free start, and adds a matched **batch** perceptron lower bound on an
explicit family inside the class. Its mistake bound is weaker in `κ` than Clustered's (`κ⁻³` versus
`κ⁻⁰`) because general residuals require a genuine perceptron phase; it is the first of these results
whose residual phase is analysed without a cone or cap.

Related published analyses (Wu–Bartlett–Telgarsky–Yu COLT 2024; Zhang–Wu–Bartlett ICML 2025 and
Zhang–Wu–Lin–Bartlett arXiv:2504.04105, including their `Ω(min{1/γ², ln n})` lower bounds for linear
predictors; Cai et al. NeurIPS 2024; Crawshaw–Liu COLT 2026; Chatterji–Long–Bartlett JMLR 2021;
Ji–Telgarsky ICLR 2019; Lyu–Li ICLR 2020; Yun–Krishnan–Mobahi ICLR 2021; Gunasekar et al. NeurIPS
2018; Arora–Cohen–Hazan ICML 2018) concern linear models, fixed output layers, gradient flow, or
asymptotic implicit bias; none gives a finite-time separation bound for the factorized convolutional
model on more than two samples. The factorized predictor is outside the gradient-span class of the
Zhang–Wu–Lin–Bartlett lower bounds, so there is no contradiction. The repository's five earlier
theorems are the closest prior work and are compared above.

## Literature coverage

Both agents surveyed ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025/2026 and arXiv submissions and
revisions from roughly October 2024 to October 2026 (search date 30 October 2026 UTC), following
citations to the foundational implicit-acceleration and implicit-bias papers. Venue status was checked
through PMLR/ICML pages; OpenReview forum pages returned browser challenges, so the NeurIPS 2026 items
"Classification at the Edge of Stability" and "Fast and slow gradient descent dynamics of logistic
regression through weak alignment" could not be verified at theorem level. No follow-up to Tyurin
2026 with a finite-time separation bound for factorized models on more than two samples was found;
absence of a search hit is not treated as evidence of novelty.

## How the strict requirement is met

The requirement was a nice generalization showing that implicit acceleration of nonlinear models exists
beyond the two-sample example. The theorem keeps the paper's model, oracle and mistake-driven update
family, replaces the two-sample dataset by an arbitrary-size two-sided background+detail class with a
standard margin assumption, proves a deterministic `O(N log(1/µ))`-call bound, and proves on an
explicit `N`-sample subfamily that the linear GD limit (batch and cyclic) needs `Ω(1/µ)` steps.
