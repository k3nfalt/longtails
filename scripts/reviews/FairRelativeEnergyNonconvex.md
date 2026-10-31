# Novelty assessment: FairRelativeEnergyNonconvex

[`result`](../../LongTails/Theorems/FairRelativeEnergyNonconvex.lean) proves that a Fair-location, periodically refreshed, normalized variance-reduction method ([algorithm](../../LongTails/Algorithms/FairVarianceReduction.lean), [tuning](../../LongTails/Algorithms/FairTuning.lean)) outputs a uniformly selected pre-update iterate with `E‖∇f(x̂)‖ ≤ ε`. The objective is L-smooth with gap Δ, on a separable Hilbert space. The noise ζ = g − ∇f is marginally symmetric, has no moment assumptions, satisfies `P(‖ζ‖>r) ≤ 1/64`, and has relative energy `E[(‖ζ(x)−ζ(y)‖/(r+‖ζ(x)‖+‖ζ(y)‖))²] ≤ κ²‖x−y‖²`. Every query pair (x,y) shares one IID sample ([setup](../../LongTails/Setups/RelativeEnergySymmetricNonconvex.lean)).

**Proved budget.** The proved budget is `⌈2⁶⁶(1+log A)(A + min{κε,L}R²Δ/ε⁴)⌉`, with R = r+ε and A = (R²+LΔ)/ε². In O-form this is

  N = O( (1 + log(((r+ε)²+LΔ)/ε²)) · [ (r+ε)²/ε² + LΔ/ε² + min{κε, L}(r+ε)²Δ/ε⁴ ] ) oracle calls.

The parameters are: L, the gradient-Lipschitz constant; Δ, the initial gap; r, the central noise radius; κ, the relative-energy constant; and ε, the target accuracy. Paired calls are counted, and so are unused second replies at refreshes. The cost of solving for the Fair root is not counted.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fradin–Sadiev–Condat–Richtárik, [arXiv:2512.18713v2](https://arxiv.org/abs/2512.18713v2) (31 Mar 2026), Thm 4.2, NSGD-MVR with p=q=2. *Special-case baseline: requires finite variance σ and similarity δ.* | O(σ²/ε² + (L+δ)Δ/ε² + δσΔ/ε³) → on the symmetric overlap with r = max(8σ, ε) and κ = δ/r (by Chebyshev, and because the ratio is at most ‖Δζ‖/r): O(log(·)[σ²/ε² + LΔ/ε² + δσΔ/ε³]) for σ ≥ ε | None: same order; this result pays an extra log((σ²+LΔ)/ε²) factor | Finite p-th central moment → no moments at all (central quantile only); unbiasedness → marginal symmetry. Undefined-mean noise, e.g. Cauchy-amplitude noise, becomes covered. | None. Both are averaged/random-iterate expected stationarity with known parameters. | Exact marginal symmetry is required; the extra log factor; uniform r and κ; noncomputable Fair root; constant 2⁶⁶ |
| Same paper, Thm 4.2 with p∈(1,2), q=2. *Special-case baseline: symmetric noise with p-th moment σ₁ and similarity δ.* | O((σ₁/ε)^{p/(p−1)} + (L+δ)Δ/ε² + (δΔ/ε²)(σ₁/ε)^{p/(2(p−1))}) → O(log(·)[σ₁²/ε² + LΔ/ε² + δσ₁Δ/ε³]), using r = max(64^{1/p}σ₁, ε) and κ = δ/r | Polynomial gain when σ₁ ≫ ε: the stochastic term shrinks by (σ₁/ε)^{(2−p)/(2(p−1))} and the initialization term by (σ₁/ε)^{(2−p)/(p−1)}, up to logs. Example: p = 3/2 gives ε^{-7/2} → ε^{-3}. | The same no-moment extension | None | Symmetry is the decisive extra hypothesis. Their matching lower bound (Thm 3.2) is for non-symmetric classes, so beating it is not a contradiction. |
| Armacki–Bajović–Jakovetić–Kar, [arXiv:2507.09093v2](https://arxiv.org/abs/2507.09093v2) (Feb 2026, preprint), nonlinear SGD. *Fresh-sample oracle, symmetric density, no moments.* | High-probability rate Õ(t^{-1/2}), i.e. order ε⁻⁴ for stationarity, with density-dependent constants → the bound above | Not comparable: their constants are density-based, not stated in (r, κ). In-repository, the κ ≥ L/ε cap recovers the refresh-only cost LR²Δ/ε⁴, and κε ≪ L gives κR²Δ/ε³. | Incomparable: no density condition here, but this result needs relative energy | Theirs is a high-probability guarantee; this one holds in expectation | Shared-sample pairs and relative-energy regularity, which they do not need |

**Reduction check.** Plugging σ = R and δ = κR into Fradin's p=2 theorem gives the uncapped rate. That is not a valid derivation, because the raw oracle need not have moments. Robustifying paired differences also fails: under marginal symmetry, the differences need not be symmetric. The genuinely new step is the transfer bound [`integral_idealNoise_difference_sq`](../../LongTails/Proofs/FairRelativeEnergy.lean). It shows that the centred Fair locations on shared blocks have increment second moment at most (2048r)²·(relative energy) plus a failure term. Normalized SPIDER/STORM-type tracking, clipping and biased variance reduction are proof ancestry; they supply the tracking recursion, not this transfer.

**Search coverage.** On 2026-10-25 I searched arXiv and the web for symmetric or moment-free heavy-tailed variance reduction. I read the theorem statements of Fradin et al. (HTML v2) and the abstracts of Puchkin et al. ([AISTATS 2024](https://arxiv.org/abs/2311.04161)), Armacki et al., [Vukovic–Jakovetić 2605.07634](https://arxiv.org/abs/2605.07634) (medoid SGD, neighbourhood convergence, no variance reduction) and [El Bajdali et al., NeurIPS 2026](https://neurips.cc/virtual/2026/poster/148757) (median-of-means with clipped SGD under a β-moment, abstract only; full text unverified). None of these gives a variance-reduced rate under symmetric noise. The theorem was introduced in commit 9bc374f on 2026-10-25, so everything cited predates it. The companion note's claims agree with the Lean statement. I did not verify its AISTATS 2026 acceptance claim for Fradin et al. I did not check its Gaussian-field motivating example, which is not part of the formal statement. I did not run a build or the axiom audit.

**Conclusion**

**Yes: under symmetric noise with mean-square similarity, the proved complexity is better whenever the noise lacks a finite variance, and the result covers noise with no moments at all.** The strongest relevant baseline is Fradin et al.'s NSGD-MVR (Thm 4.2), which is optimal for its unbiased p-th-moment class.

| Symmetric noise, moment p, σ₁ ≫ ε | Fradin et al. | This result |
|---|---|---|
| stochastic term | δΔσ₁^{p/(2(p−1))}/ε^{2+p/(2(p−1))} | δσ₁Δ/ε³ · log |
| p = 2 | δσΔ/ε³ | same, plus a log factor |

At p = 2 nothing improves, apart from losing a logarithm. For p < 2 the gain is polynomial, e.g. ε^{-7/2} → ε^{-3} at p = 3/2. For noise with undefined means, the checked baselines either do not apply or give only fresh-sample ε⁻⁴ rates.

This advantage rests entirely on exact marginal symmetry, shared-sample pairs and the new relative-energy condition. The relative-energy condition is plausible, but its practical motivation is limited to the note's constructed examples. The comparison proves a gain on the stated overlap. My search found no earlier variance-reduction result under symmetric noise, but the full text of El Bajdali et al. remains unchecked, so priority is supported, not proven.

What can be claimed: the first checked ε⁻³ variance-reduced stationarity guarantee for momentless symmetric heavy-tailed noise, via a new robust-location coupling transfer.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
