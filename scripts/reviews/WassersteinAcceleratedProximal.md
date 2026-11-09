# Novelty assessment: WassersteinAcceleratedProximal

The [theorem](../../LongTails/Theorems/WassersteinAcceleratedProximal.lean) proves the following for every exact oracle and seed. Take the [setup](../../LongTails/Setups/WassersteinSmoothComposite.lean)'s objective `G(μ)=∫V dμ+H(μ)`, where `V` is convex with an `L`-Lipschitz gradient, `H` is convex along generalized geodesics, and the domain consists of absolutely continuous measures. Then the [algorithm](../../LongTails/Algorithms/WassersteinAcceleratedProximal.lean) returns a last proximal iterate `μ_K` that is feasible and satisfies `G(μ_K)−G(μ⋆) ≤ ε`. The algorithm is a FISTA-type forward step plus an ordinary JKO step of `H`, with step `h=1/(2L)`, momentum `(k−1)/(k+2)`, and extrapolation through the optimal map `μ_k→μ_{k−1}`.

**Complexity.** The proved budget pools all three oracle types (forward pushforward, JKO of `H`, and OT map):

  N = 2 + 3⌈2R√(L/ε)⌉ = O(1 + R√(L/ε)).

Here `L` is the Lipschitz constant of `∇V`, `R ≥ W₂(μ₀,μ⋆)`, and `ε > 0` is the target objective gap. The internal bound is `4LR²/(k+1)²`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Salim–Korba–Luise, [arXiv:2002.03035v3](https://arxiv.org/abs/2002.03035), Thm 9 / Cor 10 (prior): Wasserstein proximal gradient, gap `R²/(2γn)` with `γ<1/L` | `O(1+LR²/ε)` forward+JKO calls → `O(1+R√(L/ε))` forward+JKO+OT calls | `ε⁻¹ → ε⁻¹ᐟ²`. With unit costs, roughly `LR²/ε → 6R√(L/ε)`, which wins once `LR²/ε ≳ 36` | Lower semicontinuity of `H` is dropped only because the oracle supplies the minimizers. This is not a new class | None (both last iterate) | Adds an exact OT-map oracle `μ_k→μ_{k−1}` at every iteration. SKL also covers `λ`-strongly convex `V` with linear rates |
| Ushiyama–Feng–Fujii–Fujimoto–Isobe, [arXiv:2611.03524v1](https://arxiv.org/abs/2611.03524) (2 Nov 2026, 3 days before this result's commit), Eq. (4), Thms 8/12 (Wasserstein FISTA) | `≈2⌈R√(2L/ε)⌉` gradient + cone-prox calls → `O(1+R√(L/ε))` | None: same order, with a constant-factor difference | None. Their class includes `∫V+H` with `H` entropy-type, and also smooth geodesically convex `F` and constraints | None (both last iterate) | Not comparable oracles: their prox is over the cone of optimal maps from a fixed `ν` in `L²(ν)`, which in general is not a JKO step. Here, ordinary JKO plus an OT map. This result is potential-only and requires generalized-geodesic convexity at every base, not only at `ν` |
| Chang–Iyadomi–Wang, [author preprint](https://taroiyadomi.netlify.app/pdfs/Accelerated_Proximal_Optimization_in_Wasserstein_and_Sobolev_Spaces.pdf), Thm 8 (undated) | `9R²/(2γ(t+2)²)` per JKO step of the **whole** `G` at any `γ` → not comparable | Not comparable: with a whole-`G` prox oracle, `γ` can be taken arbitrarily large | Not comparable | None | Uses a stronger prox oracle (one that includes `∫V`). Its Lemma 7 relies on non-optimal composed maps; this was not verified |

Excluded as baselines: Tanaka ([arXiv:2305.05127v4](https://arxiv.org/abs/2305.05127), Thm 5.5) and Tang–Li–Gangbo ([arXiv:2607.23008](https://arxiv.org/abs/2607.23008), Thm 3.2(ii)) prove discrete `O(k⁻²)` rates only for smooth functionals, and the latter explicitly excludes KL. Park et al. ([NeurIPS 2025](https://arxiv.org/abs/2506.06160)) handles potentials only, at rate `k^{−log₂(1+√2)}`. The Bures–Wasserstein FISTA ([NeurIPS 2026 workshop](https://neurips.cc/virtual/2026/159388)) is restricted to Gaussians.

**Reduction and mechanism.** The result does not follow from the fixed-reference `L²(ν)` lift of Ushiyama et al. or Tang et al., because the reference here moves with `μ_k` and the prox is an ordinary JKO step. The new step is a common-base coupling bound: by nonnegative curvature, a coupling cost upper-bounds `W₂²`, and this bound enters with a negative coefficient. It lets FISTA's extrapolation be handled through an OT map between consecutive iterates. The proof ancestry is the forward–backward inequality of Di Marino–Naldi–Villa ([arXiv:2505.23517v2](https://arxiv.org/abs/2505.23517), Lemma 4.2), which has no acceleration, and the Beck–Teboulle FISTA potential.

**Search coverage.** The search ran on 2026-11-05 and covered arXiv (including 2026 versions), the NeurIPS 2025/2026 and ICML 2026 pages, and the Chang–Iyadomi–Wang PDF. Theorem 8/12 constants in arXiv:2611.03524 and the later sections of 2305.05127 and 2607.23008 were read from extracted summaries, not verbatim. The Chang–Iyadomi–Wang preprint has no verifiable date. The companion note's citations match these findings, and it correctly disclaims any rate gain over Ushiyama et al. I ran no build or axiom audit.

## Conclusion

**The rate is not new; what may be new is getting it with ordinary JKO steps and OT maps between iterates.**

The decisive comparison is Ushiyama et al. (arXiv:2611.03524, posted three days before this result). It already proves the same accelerated last-iterate rate on a class that contains this one up to lower semicontinuity of `H`, and that also covers smooth geodesically convex `F`. The difference is the proximal operation: theirs is constrained to optimal maps from a fixed reference measure.

| Method | Oracle per iteration | Calls to reach `ε` |
|---|---|---|
| Salim–Korba–Luise | forward + JKO(`H`) | `O(1+LR²/ε)` |
| Ushiyama et al. | gradient + fixed-reference cone prox | `O(1+R√(L/ε))` |
| This result | forward + JKO(`H`) + OT map | `O(1+R√(L/ε))` |

Compared with Salim–Korba–Luise, which uses the standard JKO primitive, the gain is real: about `LR²/ε → 6R√(L/ε)`, which pays off once `LR²/ε ≳ 36` (equal unit costs). That gain requires an extra exact OT solve per iteration. Neither the cone prox nor the JKO-plus-OT oracle is shown to be weaker than the other, so no oracle advantage is established.

The comparison shows no improvement in complexity or scope over the strongest prior result. The literature search did not find an earlier accelerated guarantee using split ordinary JKO steps, but undated preprints keep priority uncertain. What can be claimed is a new accelerated analysis for the JKO-based forward–backward method, matching a just-published rate under a different oracle model.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
