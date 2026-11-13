# Certified second-order stationary points under variance-only stochastic gradients

**Theorem.** `OracleTemplate.GatedPerturbedEscapeSosp.result` in
[`GatedPerturbedEscapeSosp.lean`](GatedPerturbedEscapeSosp.lean) proves
`Convergence LongTails.Setups.VarianceOnlySecondOrder.spec budget`.

## Setup

[`LongTails/Setups/VarianceOnlySecondOrder.lean`](../Setups/VarianceOnlySecondOrder.lean).

**Objective.** The instance is a function `f : E → ℝ` on a finite-dimensional real inner-product space with
`d = finrank E ≥ 1`. It satisfies:
- `f` is `C²`;
- `∇f` is `L`-Lipschitz and `∇²f` is `ρ`-Lipschitz in operator norm;
- `f x0 − f x ≤ Δ` for all `x`.

**Oracle.** The oracle answers a query `x` with `g(x, ξ_k)`, where the `ξ_k` are i.i.d. with law `P0`. The
setup uses the repository's `IID` structure for the stream law `P`. The only assumptions on `g` are:
- joint measurability;
- unbiasedness: `∫ g(x,ξ) dP0 = ∇f(x)`;
- bounded variance: `∫ ‖g(x,ξ) − ∇f(x)‖² dP0 ≤ σ²`.

There is no per-sample smoothness, no almost-sure bound and no sub-Gaussian tail. This is the standard
bounded-variance model of Ghadimi–Lan (`arXiv:1309.5549`), used with second-order smoothness by
Cutkosky–Mehta (ICML 2020, `arXiv:2002.03305`) and Arjevani et al. (COLT 2020, `arXiv:2006.13476`). The noise
may depend on the query point in arbitrary measurable ways, but not on the history: the seeds are i.i.d. and
independent of past queries. Examples:
- additive heavy-ish noise with finite variance;
- masked or reveal noise `∇f(x)·1{ξ<p(x)}/p(x)`, which gives variance ≤ σ² when `p(x) ≥ ‖∇f(x)‖²/(‖∇f(x)‖²+σ²)`;
- mini-batch gradients of finite sums whose components are not uniformly smooth.

**Validity.** `0 < L, 0 < ρ, 0 ≤ σ, 0 ≤ Δ, 0 < ε, 0 < δ < 1`, `ρε ≤ L²` and `d ≥ 1`. The condition `ρε ≤ L²` is
the usual regime in which an `(ε, √(ρε))`-SOSP is nontrivial.

**Success criterion.** The output must be measurable, and with probability at least `1 − δ` over the
algorithm's Gaussian seed and the oracle samples it must satisfy
`‖∇f(x̂)‖ ≤ ε` and `⟪v, ∇²f(x̂) v⟫ ≥ −√(ρε)‖v‖²` for all `v`.
That is, the returned point is a certified `(ε, √(ρε))`-second-order stationary point with tunable confidence.

## Algorithm

[`LongTails/Algorithms/GatedPerturbedEscape.lean`](../Algorithms/GatedPerturbedEscape.lean), `method cfg x0`.
The constants are given by [`cfgOf`](../Proofs/GatedEscapeBudget.lean). They use `γ = √(ρε)`,
`K = log(20480 d)`, `θ = γ/(240K)`, `r = θ/ρ`, `η = 1/L`, `T = ⌈4KL/γ⌉ + 1` and `M = k = ⌈30ℓ⌉` (with `ℓ` as in the Result section).

**Batching and selection.** Every oracle call belongs to a block of `b` samples at one point, and the block
mean is used. A median-of-means `select M τ` returns the first block mean that is within `2τ` of more than
half of the `M` block means.

The algorithm alternates two phases.

1. **Gradient test** (`M` blocks at `x`). Let `ĝ = select`.
   - If `‖ĝ‖ > ε/2`, take the step `x ← x − ĝ/L` and test again.
   - Otherwise start an escape phase at `x`.
2. **Escape phase** (`k` attempts at the same `x`, fixed length `k(2M+T+1)` blocks). Each attempt:
   - estimates `g0` from `M` blocks at `x`;
   - draws `z ~ N(0, I)` (one wasted block) and sets `v0 = clip_r((r/(256√d)) z)`;
   - runs `T` centred, clipped noisy steps `v ← clip_r(v − η(ḡ(x+v) − g0))`;
   - sets `w = v/‖v‖` and estimates the curvature `q̂ = select` of `⟨w, ḡ(x + r w) − g0⟩/r` over `M` blocks.

   An attempt is accepted if `‖v‖ ≥ r/2` and `q̂ ≤ −2θ`. After the `k` attempts:
   - if some attempt was accepted, the first accepted one moves `x ← x − sign(⟨g0,w⟩)·r·w` and the algorithm
     returns to phase 1;
   - otherwise the algorithm stops and outputs `x`.

The step sign is chosen from `g0`. The proof controls `‖g0 − ∇f(x)‖` in full norm (`≤ rθ/8`), which is what
`escape_decrease` needs because `w` depends on `g0`.

## Result

Write `κ = L/√(ρε) ≥ 1`, `D = √ρ·Δ/ε^{3/2}` (so `LΔ/ε² = κD`), `K = log(20480 d)` and
`ℓ = log(4096·K·κ·(1+D)/δ)`. With probability at least `1 − δ`, the algorithm outputs an `(ε, √(ρε))`-SOSP
after `budget = N·b` oracle calls, where

`N = ⌈2^40 ℓ² K⁴ κ (1 + D)⌉`, `b = ⌈2^54 K⁴ (1 + dσ²√ρ/(L ε^{3/2}) + σ²/ε²)⌉ + 1`.

The theorem file writes this product as one explicit line in `L, ρ, σ, Δ, ε, δ, d`.
[`GatedEscapeBudget.lean`](../Proofs/GatedEscapeBudget.lean) proves that `N` blocks suffice for the actual
execution: `hN_facts` covers the descent count and `hδ_bound` the failure probability. The algorithm uses
`M = k = ⌈30ℓ⌉`. Every oracle call is counted: each block uses `b` calls, including the blocks spent on tests,
on the Gaussian initialisation and on the Rayleigh estimates.

Up to logarithmic factors, and with `Δ̄ = max(Δ, ε^{3/2}/√ρ)`, the cost is

`Õ( (LΔ̄/ε²)(1 + σ²/ε²) + d σ² √ρ Δ̄ / ε^{7/2} )`.

**Certification floor.** The `1 + D` factor is never smaller than `1`. Even when `Δ` is tiny, the algorithm pays for
one full escape phase, which certifies the final point. That costs
`Õ((L/√(ρε))(1 + σ²/ε²) + dσ²/ε²)`. This is why the rate is stated with `Δ̄`.

## What is new, and comparison

**Closest prior SOSP guarantee with only stochastic gradients.** This is Jin, Netrapalli, Ge, Kakade, Jordan
(JACM 2021, `arXiv:1902.04811v2`), Theorem 16. It covers perturbed SGD without their per-sample Lipschitz
Assumption C.
- **Noise.** It assumes norm-sub-Gaussian noise (their Assumption B).
- **Guarantee.** With probability `1 − δ`, perturbed SGD *visits* an ε-SOSP within `Õ(d·LΔσ²/ε⁴)` stochastic
  gradients (plus lower-order terms). It *returns* one only with constant probability, by outputting a uniformly
  random iterate (their Remark 14). It gives no certificate.

Our bound replaces `d·LΔσ²ε^{-4}` by `LΔσ²ε^{-4} + dσ²√ρΔε^{-7/2}`. For `Δ ≳ ε^{3/2}/√ρ` (so `Δ̄ = Δ`), this
is an improvement factor of `min(d, L/√(ρε))` in rate over Jin et al. Thm 16. It comes together with:
- the weaker variance-only noise model;
- a certified output with tunable confidence, where `1 − δ` enters only through `log(1/δ)` factors.

For `Δ ≪ ε^{3/2}/√ρ` we claim no rate improvement. Jin's visit guarantee then pays no certification cost, and
ours pays the floor above.

Dimension-free SOSP rates need extra structure that is not available here, for example:
- per-sample smoothness: Fang–Lin–Zhang (COLT 2019, `arXiv:1902.00247`) and SPIDER-SFO⁺;
- almost-surely bounded or dispersive noise;
- Hessian-vector-product or second-order oracles (Arjevani et al. COLT 2020).

## Lower bound per saddle (proved here, not formalized)

**Proposition.** Fix a `C^∞` nonincreasing `χ : [0,∞) → [0,1]` with `χ = 1` on `[0,1]` and `χ = 0` on `[2,∞)`.
Let `c₁ = sup|χ′|`. Let `K₂, K₃` be the constants, depending only on `χ`, in Step 1 below. Put
`c₀ = max(1, 2K₃)`. Assume:
- `D_amb ≥ 16`, where `D_amb` is the ambient dimension;
- `L ≥ 2(1+K₂)√(ρε)`;
- `Δ ≥ 4c₀² ε^{3/2}/√ρ`;
- `σ > 0`.

Let a randomized algorithm use at most `N` oracle calls and output an `(ε, √(ρε))`-SOSP with probability at
least `2/3` on every instance of the formal class of
[`VarianceOnlySecondOrder.lean`](../Setups/VarianceOnlySecondOrder.lean) with these parameters and `x0 = 0`. Then

`N ≥ D_amb σ² / (192 (1+c₁)² c₀² ε²)`.

**Instances.** Set `γ_b = 4√(ρε)` and `r = c₀√(ε/ρ)`. For a unit vector `e`, let:
- `G(x) = (γ_b/4)‖x‖²`;
- `B_e(x) = −(γ_b/2)⟨e,x⟩² χ(‖x‖/r)`;
- `F_e = G + B_e`.

The oracle is the "reveal" oracle with seeds `ω_k ~ U[0,1]` i.i.d.:

`g_e(x, ω) = ∇G(x) + (∇B_e(x)/p_e(x))·1{ω < p_e(x)}`, where `p_e(x) = ‖∇B_e(x)‖²/(‖∇B_e(x)‖² + σ²)`.

The second term is read as `0` when `∇B_e(x) = 0`. This oracle has the following properties:
- it is jointly measurable;
- it is unbiased;
- its variance is `‖∇B_e‖²(1 − p_e)/p_e = σ²·1{∇B_e(x) ≠ 0} ≤ σ²`.

So it belongs to exactly the admissible class of the setup. It depends on the query point and not on the history.

**Step 1 (regularity).** Write `φ(x) = ⟨e,x⟩²χ(‖x‖/r)`.
- On `‖x‖ < r`, `φ = ⟨e,x⟩²`.
- On the support of `χ′(‖x‖/r)`, we have `r ≤ ‖x‖ ≤ 2r` and `|⟨e,x⟩| ≤ 2r`. There the `k`-th derivatives of `‖x‖`
  are bounded by `C_k r^{1−k}`.

Hence `‖∇²φ‖ ≤ K₂` and `‖∇³φ‖ ≤ K₃/r`, with `K₂, K₃` depending only on `χ`. This gives:
- `‖∇²F_e‖ ≤ (γ_b/2)(1 + K₂) ≤ L`;
- `‖∇³F_e‖ ≤ γ_b K₃/(2r) = 2K₃ρ/c₀ ≤ ρ`, so `∇²F_e` is `ρ`-Lipschitz.

For `‖x‖ ≤ 2r`, `F_e(x) ≥ (γ_b/4)‖x‖² − (γ_b/2)⟨e,x⟩² ≥ −(γ_b/4)⟨e,x⟩² ≥ −γ_b r²`. Outside that ball `F_e ≥ 0`.
So `F_e(0) − inf F_e ≤ γ_b r² = 4c₀² ε^{3/2}/√ρ ≤ Δ`.

**Step 2 (where the SOSPs are).** Write `x = a e + y` with `y ⊥ e`. Then

`∇F_e(x) = (γ_b/2)x − γ_b a χ e − (γ_b/2) a² χ′ x/(r‖x‖)`.

Its component orthogonal to `e` is `(γ_b/2)·y·(1 − a²χ′/(r‖x‖))`. Since `χ′ ≤ 0`, its norm is at least
`(γ_b/2)‖y‖`. So every `ε`-FOSP has `‖y‖ ≤ 2ε/γ_b = ½√(ε/ρ) ≤ r/2`. Moreover:
- For `‖x‖ ≥ 2r`, `‖∇F_e‖ = (γ_b/2)‖x‖ ≥ γ_b r = 4c₀ε > ε`.
- For `‖x‖ ≤ r`, `∇²F_e = (γ_b/2)I − γ_b e eᵀ`, so `λ_min = −2√(ρε) < −√(ρε)`.

Hence every `(ε, √(ρε))`-SOSP `x` satisfies `r < ‖x‖ < 2r` and `|⟨e,x⟩| ≥ ‖x‖ − r/2 > ‖x‖/2`.

**Step 3 (no information before a reveal).** Run the algorithm with its own seed `ξ` against the *null oracle*
`g₀(x, ω) = ∇G(x)`, using the same `ξ` and `ω`'s.
- The null-run queries `x₁, …, x_N` and its output `x̂` are functions of `ξ` alone, so they are independent of
  `e` and of the `ω`'s.
- The real run coincides with the null run until the first `t` with `ω_t < p_e(x_t)`.
- On `‖x‖ ≤ 2r`, `‖∇B_e(x)‖ ≤ γ_b|⟨e,x⟩|(1 + c₁)`, and `∇B_e(x) = 0` for `‖x‖ ≥ 2r`.
- For `e` uniform on the sphere, `E_e⟨e,x⟩² = ‖x‖²/D_amb`. So for each null-run query,
  `E_e p_e(x_t) ≤ E_e ‖∇B_e(x_t)‖²/σ² ≤ 4(1+c₁)² γ_b² r²/(D_amb σ²) = 64(1+c₁)² c₀² ε²/(D_amb σ²)`.

A union bound gives `P(some reveal) ≤ 64(1+c₁)²c₀² N ε²/(D_amb σ²)`. No minimax argument is needed: we average
over `e` for each fixed `ξ`.

**Step 4 (an `e`-independent output fails).** By Step 2, success without a reveal requires
`|⟨e, x̂/‖x̂‖⟩| > 1/2` with `x̂ ≠ 0`. The spherical cap bound `P_e(|⟨e,u⟩| ≥ t) ≤ 2exp(−D_amb t²/2)` gives
probability at most `2e^{−D_amb/8} ≤ 2e^{−2} < 1/3`.

Hence `P(success) ≤ 64(1+c₁)²c₀² Nε²/(D_amb σ²) + 2e^{−2}`. Success probability `≥ 2/3` therefore forces
`N ≥ D_amb σ²/(192(1+c₁)²c₀²ε²)`. Because the instance is averaged over `e`, some fixed `e` already forces this.

**The first-order side at this `Δ`.** Here `Δ = Θ(ε^{3/2}/√ρ)`. The first-order upper bound of normalized SGD
with momentum under second-order smoothness (Cutkosky–Mehta, ICML 2020) has no dimension factor, and its leading
term is `σ²√ρΔ/ε^{7/2} = Θ(σ²/ε²)`. In this particular family `x0 = 0` is even an exact
stationary point.

Certifying second-order stationarity at one saddle therefore costs a factor `Ω(d)` more than first-order
stationarity. This is the gradient-oracle analogue of the `d/θ²` sample requirement for detecting a spike in
PCA (Baik–Ben Arous–Péché; minimax PCA bounds of Vu–Lei type, e.g. `arXiv:2505.10882`). The reveal oracle
follows Arjevani et al. (`arXiv:1912.02365`). We present the mechanism as an adaptation of that lineage, not as a
new phenomenon.

**Tightness.** At `Δ = Θ(ε^{3/2}/√ρ)` our upper bound is `Õ((L/√(ρε))(1 + σ²/ε²) + dσ²/ε²)`. The separation is
therefore tight per saddle, up to logarithmic factors, only for `d ≥ L/√(ρε)`.

**Technical mechanism.** The escape analysis is linear in `d` with no union bound over time. It combines:
- a deterministic *pancake* lemma on noiseless centred gradient orbits
  ([`GatedEscapePancake.lean`](../Proofs/GatedEscapePancake.lean));
- Gaussian slice anti-concentration along the most negative eigenvector
  ([`GatedEscapeGaussian.lean`](../Proofs/GatedEscapeGaussian.lean),
  [`GatedEscapeSlice.lean`](../Proofs/GatedEscapeSlice.lean));
- a *frozen* deviation chain whose truncated, geometrically normalized squared deviation is a
  supermartingale ([`GatedEscapeDeviation.lean`](../Proofs/GatedEscapeDeviation.lean),
  [`GatedEscapeCoupling.lean`](../Proofs/GatedEscapeCoupling.lean)). Markov's inequality on the terminal state
  replaces Doob/Ville, so the batch size grows only like `d`;
- a time-weighted positive-curvature energy and a post-clip negative-mass lemma
  ([`GatedEscapeEnergy.lean`](../Proofs/GatedEscapeEnergy.lean),
  [`GatedEscapeDirection.lean`](../Proofs/GatedEscapeDirection.lean),
  [`GatedEscapeTrajectory.lean`](../Proofs/GatedEscapeTrajectory.lean),
  [`GatedEscapeTrajProb.lean`](../Proofs/GatedEscapeTrajProb.lean)). Together they show that an exit yields a
  direction with Rayleigh quotient `≤ −3θ`, even after clipping and re-entry.

Late or corrupted exits are harmless. An accepted step requires accurate `g0` and `q̂` (median-of-means events),
and these alone force a decrease of `r²θ/5` (`accept_safe` in
[`GatedEscapeAccept.lean`](../Proofs/GatedEscapeAccept.lean); `prob_harm` in
[`GatedEscapeAttemptProb.lean`](../Proofs/GatedEscapeAttemptProb.lean)).

The global high-probability argument is a phase-level *look-ahead martingale*
([`GatedEscapeLookahead.lean`](../Proofs/GatedEscapeLookahead.lean), `global_count` in
[`GatedEscapeGlobal.lean`](../Proofs/GatedEscapeGlobal.lean)). It bounds the expected number of bad phase ends.
A deterministic potential argument (`good_run`) then shows that, on the good event, the algorithm stops at a
certified SOSP within the budget. [`GatedEscapeFinal.lean`](../Proofs/GatedEscapeFinal.lean) connects this to
`execute`.

## Limitations and open questions

- **First-order term.** The gradient phases use mini-batch gradient steps, so the `LΔσ²ε^{-4}` term remains. A
  faster `ε^{-7/2}` engine (normalized SGD with momentum, IGT) with a high-probability conversion would give
  `Õ(σ²√ρΔε^{-7/2}(1+d))`. This stays open.
- **Chained lower bound.** The lower bound above is per saddle and is not formalized. A chained lower bound with
  `K` saddles in a shared ambient space of dimension `D` is not constructed. It would need a global background
  with `O(ρ)` Hessian-Lipschitz constant independent of `K` and no spurious SOSPs. The gap `min(D, K)` between the
  sum-form lower bound and our product-form upper bound therefore stays open. In this item `K` is the number of
  saddles, not the logarithmic factor of the algorithm.
- **Certification floor.** For `Δ ≪ ε^{3/2}/√ρ` the certification floor dominates (see Result).
- **Constants.** The constants (`2^40`, `2^54`, `4096`, `20480`) are crude.
