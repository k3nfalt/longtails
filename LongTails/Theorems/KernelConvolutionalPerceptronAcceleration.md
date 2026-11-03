# Implicit acceleration of the convolutional quadratic perceptron with any kernel size on many-sample data

Lean theorem: [`KernelConvolutionalPerceptronAcceleration.lean`](KernelConvolutionalPerceptronAcceleration.lean)
(`OracleTemplate.KernelConvolutionalPerceptronAcceleration.result`).
Setup: [`../Setups/KernelConvolutionalPerceptron.lean`](../Setups/KernelConvolutionalPerceptron.lean).
Algorithm: [`../Algorithms/KernelConvolutionalPerceptron.lean`](../Algorithms/KernelConvolutionalPerceptron.lean).
Proofs: [`../Proofs/KernelPerceptronAnalysis.lean`](../Proofs/KernelPerceptronAnalysis.lean) (abstract dynamics,
Phase 1, Phase 2, combined length bound), [`../Proofs/KernelPerceptronBridge.lean`](../Proofs/KernelPerceptronBridge.lean)
(coordinates, oracle identities, cyclic-scan accounting), [`../Proofs/KernelPerceptronParameters.lean`](../Proofs/KernelPerceptronParameters.lean)
(explicit constants), [`../Proofs/KernelPerceptronInstances.lean`](../Proofs/KernelPerceptronInstances.lean)
(the clustered instance family of the repository is admissible for `k = 2`, so its perceptron lower bound
transfers; an explicitly unaligned family is admissible for every `k ≥ 2`).

## Background and the question

Tyurin, *Gradient Descent as a Perceptron Algorithm: Understanding Dynamics and Implicit Acceleration*,
[arXiv:2512.11587v2](https://arxiv.org/abs/2512.11587) (21 May 2026; [ICML 2026](https://proceedings.mlr.press/v306/tyurin26a.html)),
shows that logistic-loss gradient descent on a reparameterised linear model becomes, in the large-norm
limit, the *quadratic perceptron algorithm* (QPA, Thm 2.1): a perceptron whose update is the gradient of the
margin of the nonlinear parameterisation. For the convolutional model with kernel size `k = 2` on the
two-point dataset (5), the paper proves implicit acceleration: the non-batch QPA with injected Gaussian
noise separates in `Õ(√d/μ)` steps (Thm 5.1) whereas the perceptron on the linear model needs `Ω(d/μ)`
(Thm 5.2). Section 6 lists as open: larger kernels `k` ("may require new mathematical tools"; Prop. 6.1
only bounds `‖A_i‖`, observing that the admissible step shrinks with `k`), general two-layer models,
multi-layer models, and more samples; many-sample acceleration is reported only experimentally (App. G).

This repository already contains five results around that paper. The many-sample ones each rest on a
structural crutch: a pure reference sample plus a deterministic kick and restart scan
([ManySampleConvolutionalPerceptronAcceleration](ManySampleConvolutionalPerceptronAcceleration.md)),
a residual cap `‖u_i − u⋆‖ ≤ κ/64` together with a `κ`-encoded initial filter
([ClusteredConvolutionalPerceptronAcceleration](ClusteredConvolutionalPerceptronAcceleration.md)),
or a full-width model with an offset slab `ν ≤ κ¹²μ²/2⁵⁶`
([CyclicFullWidthPerceptronAcceleration](CyclicFullWidthPerceptronAcceleration.md)). All are for `k = 2`.

## Setup (`LongTails/Setups/KernelConvolutionalPerceptron.lean`)

**Model.** Tyurin's convolutional model with an arbitrary kernel size `k ≥ 2`: a filter `c ∈ ℝ^k`, a readout
`v ∈ ℝ^d`, cyclic shift `P`, and `m(b; c, v) = ⟨Σ_{j<k} c_j P^j b, v⟩` (`response`, `margin`). The oracle
returns, for a queried index and point, the exact signed margin and its full parameter gradient
(`direction`): `∂/∂c_j = ⟨P^j b, v⟩`, `∂/∂v = Σ_j c_j P^j b`.

**Data (`Geometry`).** `N = n+1` signed samples (labels absorbed) `D_i = (α_i/√2)·e + μ·u_i` with
`e = 1_d/√d`, where

- `g ≤ |α_i| ≤ R` — every sample has a dominant constant background of *either sign*;
- `⟨e, u_i⟩ = 0`, `‖u_i‖ ≤ 1/√k` — a small residual (contrast `μ`);
- a unit `w` with `κ ≤ ⟨w, highPass_k(u_i)⟩` for all `i`, where
  `highPass_k(u) = (1 − 1/k)^{-1/2} · (u − (1/k) Σ_{j<k} P^j u)` is the normalised high-pass response of
  the identity filter. For `k = 2` this is exactly `(u − Pu)/√2`, the repository's derivative-margin
  feature, and `‖u‖ ≤ 1/√2` is the existing normalisation: the `k = 2` case is literally the two-sided
  class used by the clustered and many-sample results, minus their cap/reference conditions.

Nothing else is assumed: residuals may point in arbitrary, mutually anticorrelated directions, have any
rank, any number `N` (including `N ≫ d`), and any label imbalance.

*Normalisation and the hidden `k`.* The bound `‖u_i‖ ≤ 1/√k` makes every feature the model can realise
from a filter direction `t` with `‖t‖ ≤ 1`, namely `Σ_j t_j P^j u_i`, have norm at most `1`; equivalently,
with unit residuals `v_i = √k · u_i` the contrast is `μ/√k`. Because `‖highPass_k(u)‖ ≤ 2√2 · ‖u‖`, the
margin parameter is necessarily small for large kernels: `κ ≤ 2√2/√k`. In terms of the `k`-free
high-pass margin of unit residuals, `κ_v = √k · κ`, the budget below reads
`N · 2·10⁵ · (R/g)² · k^{3/2} · κ_v⁻³ · log(…)`, the step is `η = κ_v / (8√2 · k · R)`, and the contrast
condition is `μ_phys² (R/g)⁴ log²(…) ≤ κ_v⁶ R² / (k³ · 10¹³)` for the physical contrast `μ_phys = μ/√k`.
We display this so that no `√k` is hidden inside `κ`. The class is the standard
"nuisance background plus small informative residual" model behind Tyurin's dataset (5); the margin
condition is linear separability after fixed high-pass filtering, which the model can realise.

**Admissible algorithms (`family`, enforced through `allowedAlgorithm`).** Tyurin's non-batch QPA as a
cyclic scan: start at the identity filter `c₀ = e₁` (the model *is* the linear model at the start) and
`v₀ = 0`; visit indices cyclically; on a nonpositive margin move by `η · ∇m`, otherwise leave the point;
return the last iterate. The step size `η > 0` is left to the algorithm. The theorem's algorithm uses
`η = κ / (16 √(k/2) R)`.

**Accuracy.** Strict separation of all `N` samples (`Separates`). **Cost.** One oracle call per visited
index, including correct visits.

**Validity (`valid`).** `0 < g ≤ R`, `0 < μ ≤ R`, `0 < κ ≤ 1`, `k ≥ 2`, and the single polynomial
small-contrast inequality

```
μ² · (R/g)⁴ · log²( 128 k R² / (κ μ)² ) ≤ k · κ⁶ · R² / 10¹³ .
```

It is nonempty for every `κ ∈ (0,1]`, every `g ≤ R`, every `k ≥ 2`, and does not involve `N` or `d`;
it says `μ ≲ √k κ³ (g/R)² R / log(1/μ)`.

## Main result

`result : Convergence spec budget` with the one-line budget

```
(N) · ⌈ 200000 · (R/g)² · κ⁻³ · log( 128 k R² / (κ μ)² ) ⌉₊
```

oracle calls. Deterministically, for every admissible dataset and every oracle seed, the last iterate
strictly separates all `N` samples after this many calls (and at every later call). The contrast enters
only through the logarithm. In the normalised margin `κ` the mistake count is `k`-free; in physical units
(unit residuals, margin `κ_v`) it is `∝ k^{3/2}` and the step is `∝ 1/(kR)`, see the normalisation remark
above. Whether the `k^{3/2}` is necessary is open; at the natural step the simulations below show a
`k`-independent count.

## What is new

1. **Arbitrary kernel size.** This is the first finite-time guarantee for Tyurin's convolutional QPA with
   `k > 2` (the paper's first listed open direction). The mechanism is *not* a new eigen-analysis of the
   rank-growing matrices `A_i`: writing the filter as `c = (a/√k)·1_k + t` with `t ⊥ 1_k`, the pair
   `(a, q)` with `q = ⟨v, e⟩` evolves exactly as in the `k = 2` case with `b_i = η α_i √(k/2)`, while the
   high-pass part `t` only drifts by `O(δ‖z‖)` per mistake (`δ = (ημ)²`). So to leading order the extra
   taps are frozen and the residual readout is a perceptron on the fixed high-pass features of the
   initial filter. This is consistent with Prop. 6.1's observation that the natural step scales like
   `1/√k` (the background block has `b_i = ηα_i√(k/2)`); our analysed step `η = κ/(16√(k/2)R)` is a
   further factor `κ/4 = κ_v/(4√k)` below the natural `1/(4√(k/2)R)` because the Phase-2 potential needs
   `β = ηR√(k/2) ≤ κ/16`, and the mistake
   count is `k`-free only in the normalised margin `κ` (`∝ k^{3/2}` in physical units). We state plainly
   that this is a *deflationary* answer: larger kernels inherit the `k = 2` acceleration; the new taps
   are not learned to leading order, and the result does not say what larger kernels learn.
2. **Many samples without crutches.** Both labels with arbitrary background magnitudes in `[g, R]`,
   arbitrary residual geometry (no cap, no pure reference, no Gram-sign or rank assumption), no injected
   noise or deterministic kick, a plain cyclic scan, and the identity-filter start that depends on nothing.
   Compared with the clustered result this removes the cap `‖u_i − u⋆‖ ≤ κ/64` (and its `κ`-encoded
   initial filter), at the price of `κ⁻³` instead of `κ⁰` and a `κ`-dependent step; compared with the
   many-sample result it removes the pure reference, the kick, the restart scan and both labels become
   admissible; compared with the full-width result it treats Tyurin's actual model with arbitrary
   backgrounds instead of a slab.
3. **The mechanism (the content of the proof).** Let `s̃ = a + q`, `h̃ = a − q`. A mistake on sample `i`
   acts *multiplicatively* on the background block, `s̃ ← (1 + b_i) s̃`, `h̃ ← (1 − b_i) h̃` (up to the
   `δ⟨p_i, z⟩` coupling), so `Φ = |a² − q²| = |s̃ h̃|` contracts by exactly `1 − b_i²` at *every* mistake,
   and the bias `ν = aq = (s̃² − h̃²)/4` is a multiplicative (EG±-type) weight whose effective learning
   rate shrinks with the background. The residual readout `z` is an additive perceptron on the high-pass
   features. Two phases:
   - *Phase 1* (background dominated): the ratio `|s̃|/|h̃|` stays within `e^{±3β}` (`β = ηR√(k/2)`),
     because expanding mistakes are only possible when the two coordinates are already balanced to
     within the residual scale; hence `Φ` contracts geometrically and the phase ends after
     `O(log(1/δ)/ρ²)` mistakes, `ρ = ηg√(k/2)`.
   - *Phase 2* (hybrid potential): `W = ‖z − Λw‖² + (1+γ)(S + Φ)/(2δ)`, `S = a² + q²`,
     `γ = β/(2−β)`, satisfies per mistake `ΔW ≤ −(2Λκ* − U²) + c_β·viol + noise` with
     `c_β = 4β/(2−β)`, where `viol` is the residual violation of an *expanding* mistake and
     `viol ≤ U√W − Λκ*`. All first-order terms cancel exactly through the mistake condition
     (`q Δq + δ⟨z, Δz⟩ = η·margin ≤ 0`); the only leak is the second-order multiplicative term, i.e. the
     `η²`-term familiar from exponentiated-gradient analyses. It is absorbed by the Novikoff gain when
     `β ≲ κ/4`, which is why the step is tuned to `κ`.
   This potential argument is the new technical ingredient; the clustered proof's history cone and
   Lorentz invariant need `⟨r_i, r_j⟩ ≥ κ²` for all pairs and do not extend to unaligned residuals.

## Explicit instance families (nonemptiness, formal)

- **Clustered family, `k = 2`** (`KernelPerceptronInstances.familyGeometry`, `parameters_valid` for
  `μ ≤ 10⁻²⁴`): the repository's interleaved family in dimension `2n+4` with `κ = 1/8`, `g = √2`,
  `R = 2√2`; every clustered geometry is a `k = 2` instance (`ofClustered`). This is the family on which
  the perceptron lower bound below is proved.
- **Unaligned family, every `k ≥ 2`** (`KernelPerceptronInstances.unalignedDataset`,
  `unalignedGeometry`, `unalignedParameters_valid` for `μ ≤ 1/(10²² k³)`, `unalignedParameters_admissible`):
  dimension `d = 2n+4`, `N = n+1` samples with alternating labels `α_i = (−1)^i √2` (`g = R = √2`),
  separator `w = alt/√d` with `alt = (+1, −1, +1, …)`, and residuals
  `u_i = k^{-1/2} · ( (1/4) w + (3/4) y_i )`, `y_i = (e_{2i} − e_{2i+2})/2`. Consecutive residual Gram
  entries are `⟨u_i, u_{i+1}⟩ = (1/16 − 9/64)/k = −5/(64k) < 0`, the residual rank is `n+1` (growing
  with `N`), and the derivative margin is exactly `c_k/(4√k) ≥ 1/(8√k)` with
  `c_k = (1 − 1/k)^{-1/2}(1 − [k odd]/k) ∈ [1/2, √2]` (`unaligned_margin`), so `κ = (8√k)⁻¹` matches the
  inherent scaling `κ ≤ 2√2/√k`. The margin computation uses only `P·alt = −alt` (`alt_shift`), i.e.
  `⟨alt, P^j y⟩ = (−1)^j ⟨alt, y⟩`, so no alignment between the `y_i` and `w` is needed: the clustered
  proof's Gram-positivity (`⟨r_i, r_j⟩ ≥ κ²`) fails on this family, the present theorem applies.

## Matched comparison with the linear model

The implicit-acceleration claim is method-versus-method, as in Tyurin's Thm 5.1/5.2. The repository's
clustered instance family (interleaved positives `e + μu_{2i}` and negatives `(1+μ)e − μu_{2i+1}` in
dimension `2n+4`, `κ = 1/8`, `g = √2`, `R = 2√2`) is admissible here with `k = 2`
(`KernelPerceptronInstances.familyGeometry`, `parameters_valid` for `μ ≤ 10⁻²⁴`), and more generally
every clustered geometry is a `k = 2` instance (`ofClustered`). On that family the repository proves
that the ordinary zero-initialised perceptron, and the perceptron that only trains the readout on the
frozen initial filter, make a thresholded mistake in every one of the first `⌊1/(4μ)⌋` pairs
(`ClusteredConvolutionalPerceptronInstances.family_raw_mistakes`, `family_frozen_mistakes`), hence need
`Ω(1/μ)` calls, while the present bound is `O(N log(1/μ))` with `N = 2n+2`. Here the frozen initial filter
is the identity, so the second comparator coincides with the raw perceptron. The `μ ≤ 10⁻²⁴` in
`parameters_valid` is only the explicit witness of nonemptiness; the theorem itself covers all `μ`
allowed by `valid`.

Stronger linear methods remain stronger baselines and no problem-class claim is made:

- *Read the data.* At the identity filter with zero readout the readout gradient is the signed sample
  itself, so `N` calls reveal the dataset and offline linear programming finishes without further calls.
- *Explicit high-pass filtering / centering.* A perceptron on `highPass_k(u_i)` makes `O(κ⁻²)` mistakes,
  independent of `μ`; the nonlinear bound pays `κ⁻³` and `(R/g)²`. The value of the theorem is that
  plain GD on the nonlinear model learns the filtering implicitly from the identity start.
- *Second-order perceptron* ([Cesa-Bianchi–Conconi–Gentile, SICOMP 2005](https://doi.org/10.1137/S0097539703432542))
  achieves `Õ(r κ⁻² log(R/μ))` with matrix computations; *accelerated perceptrons*
  ([Wang et al., ICLR 2023](https://arxiv.org/abs/2210.09371)) use full-data iterations.
- *Span lower bounds.* For the linear model, GD-type methods stay in the span of the data, and
  [Zhang–Wu–Lin–Bartlett, arXiv:2504.04105](https://arxiv.org/abs/2504.04105) give `Ω(min{1/γ², log n})`
  span lower bounds; a uniform acceleration over all margin-`γ` data is impossible, which is why the
  gain is instance-class specific (background plus residual).

## The step size, and what remains open

The proof needs `β = ηR√(k/2) ≤ κ/16`. We made a documented attempt at an absolute-constant step: with the
exact first-order cancellation above, the per-cycle leak is `(2+β)/(2−β)` of the exchanged energy, and
our potential argument closes only if `c_β U ≲ κ*`, i.e. `β ≲ κ/4`; at the natural step `β = 1/4` this
covers only `κ ≳ 1`. We do not know whether this is an artefact: all experiments (our own runs: `k = 2` with
`μ` down to `10⁻⁶`, and `k ∈ {2, 3, 4, 8}` with `μ` down to `10⁻⁴`; and the Reviewer's independent stress test with exact
margins, `N` up to 128, `d` up to 128, `κ` down to `0.05`, `g/R` down to `0.1`, unbalanced labels,
`μ` down to `10⁻⁴`) converge at `η = 1/(4R)` in a few
hundred to `≈ 1300` mistakes with weak `κ`-dependence (roughly `(R/g)² log(1/μ)`), while the analysed
step `η ∝ κ/R` is `10³–10⁴` times slower and matches the `(R/g)² κ⁻² log(1/δ)` Phase-1 prediction.
Consequently the proved regime certifies acceleration over the raw perceptron only when
`N · 2·10⁵ (R/g)² κ⁻³ log(128kR²/(κμ)²) < 1/(4μ)`, i.e. `μ ≲ κ³ (g/R)² / (10⁶ N log)`; this excludes
every cell of the Reviewer's stress table (`κ ≥ 0.05`, `μ ≥ 10⁻⁴`), where the natural-step method is
already `10³×` faster than the perceptron. The natural-step behaviour, and the removal of the `κ⁻³` and of
the large constant, are open. Kernel-size check (`sim/kernel.py`, `d = 24`, `N = 10`, random unit
separators, residual norm `0.7` held fixed in `k`, high-pass margins `0.004–0.1`, `R = 4`): at the
natural step `η = 1/(4√(k/2) R)` the counts were `288/288/322` (`k = 2`), `207/418/365` (`k = 3`),
`173/232/276` (`k = 4`), `182/262/255` (`k = 8`) mistakes for `μ = 10⁻², 10⁻³, 10⁻⁴`, i.e. no visible
`k`-dependence, while at `η = κ/(8√(k/2) R)` the counts were `10⁴–3.5·10⁵` or did not separate within
`3·10⁶` calls.

## Limitations (stated honestly)

- **Method-vs-method.** No new oracle complexity for linear classification (see the baselines).
- **Constants and exponents.** `2·10⁵`, `κ⁻³`, `(R/g)²`, and the contrast condition with `10⁻¹³` are
  conservative sufficient conditions, not necessities.
- **Non-batch rule.** The analysed rule is the paper's non-batch (cyclic) QPA, not the batch limit of
  Thm 2.1; and the QPA is the large-norm limit of GD — no finite-norm GD claim.
- **Dataset (5) is excluded.** Its pure reference `u₁ = 0` carries no residual margin; the class here
  requires residual information in every sample. We generalise the phenomenon, not the instance.
- **Negative result for width-1 two-layer models.** In simulations the width-1 two-layer QPA
  `m = v⟨c, b⟩` fails on both-sign-background data (the scalar output weight flips sign indefinitely),
  so the convolutional model, not the two-layer model, is the right object for this class.
- **Frozen high-pass part.** The larger-kernel result does not analyse learning of the extra taps.
- **Kernel-size dependence in physical units.** `κ ≤ 2√2/√k` is forced by the normalisation, so the
  budget is `∝ k^{3/2}` and the step `∝ 1/(kR)` for unit residuals; the natural-step simulations show no
  `k`-dependence, so these exponents are presumably artefacts of the `κ`-tuned step.
- **Lower bound transferred only for `k = 2`.** The formal `Ω(1/μ)` perceptron bound is the
  repository's clustered-family bound (`k = 2`); for `k > 2` the acceleration claim rests on the same
  linear-model comparison (the perceptron does not depend on `k`), but no `k > 2` family with a formal
  lower bound is included.
- **Identity start only.** A general initial filter `c₀` with nonzero mean and nonzero high-pass part is
  not proved (the same argument applies with features defined by `c₀`'s high-pass part, but the
  constants and the margin definition would depend on `c₀`); random or data-dependent initialisations
  of the filter or the readout are not covered by the theorem, and we have no evidence either way about
  their behaviour.
- **Concurrent work.** An independent concurrent session of this repository formalised the `k = 2`
  case of this class (two-sided convolutional perceptron). The present theorem contains that case as the
  literal special case `k = 2`; the step-size constant and budget constants differ.

## How the scope requirement is met

The requirement was to investigate the paper and the repository's existing results and find a
generalization showing that implicit acceleration of nonlinear models exists beyond the two-sample
example. The theorem covers arbitrary `N` (two-sample is `N = 2`), both labels, arbitrary residual
geometry (unaligned, growing rank), and arbitrary kernel size `k ≥ 2` for the paper's own convolutional
model and its own algorithm (non-batch QPA from the identity filter, enforced through
`allowedAlgorithm`), proves an `O(N log(1/μ))` call bound with the contrast only in the logarithm, and
inherits a proved `Ω(1/μ)` bound for the linear-model perceptron on an admissible family
(`k = 2`); admissible unaligned families exist for every `k`. The repository's prior many-sample results
needed a reference sample plus kick, a residual cap plus `κ`-encoded initialisation, or a full-width
model with a slab; all of these are removed here.

## Literature coverage

Both agents independently surveyed ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025/2026 and arXiv
(October 2024 – October 2026) on 30 October 2026 UTC, reading the primary paper at theorem level
(official PMLR version and arXiv v2), its predecessor (Tyurin, AAAI 2025), large-step logistic GD
(Wu–Bartlett–Telgarsky–Yu COLT 2024; Zhang–Wu–Bartlett ICML 2025; Zhang–Wu–Lin–Bartlett 2025;
Crawshaw–Liu COLT 2026), implicit bias of linear/convolutional networks (Gunasekar et al. NeurIPS 2018;
Ji–Telgarsky ICLR 2019; Yun–Krishnan–Mobahi ICLR 2021), implicit acceleration by depth
(Arora–Cohen–Hazan ICML 2018), and linear baselines. Semantic Scholar and OpenAlex list no citations of
arXiv:2512.11587; the five repository results are the only `N > 2` QPA analyses we found. NeurIPS 2026
items on classification at the edge of stability and on weak alignment were visible only at abstract
level. Absence of hits is not evidence of novelty; the comparison rests on the explicit differences above.
