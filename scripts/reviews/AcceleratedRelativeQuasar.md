# Continuized acceleration for strongly quasar-convex objectives with relative gradient error

[`result`](../../LongTails/Theorems/AcceleratedRelativeQuasar.lean) proves the following. Let f be L-smooth with a minimizer x⋆ satisfying (γ,μ)-strong quasar-convexity, and let the oracle return a fixed measurable map g with ‖g(x) − ∇f(x)‖ ≤ δ‖∇f(x)‖, where 0 ≤ δ < 1 ([setup](../../LongTails/Setups/RelativeGradientStrongQuasar.lean)). Then the randomized continuized method [`RelativeQuasar`](../../LongTails/Algorithms/RelativeQuasar.lean), after a fixed number of calls, returns a last iterate x_K with 𝔼[f(x_K) − f(x⋆)] ≤ ε.

**Complexity.** Parameters: L is the smoothness constant, μ > 0 and γ ∈ (0,1] are the quasar parameters, δ is the relative error, Δ ≥ f(x₀) − f⋆, and κ = L/μ. Since strong quasar-convexity gives μ ≤ 2L/γ, we have κ ≥ γ/2.

  K = O( [1 + √(κ/(1−δ))/γ + δ²κ/(γ²(1−δ))] · [1 + log(1 + Δ/(γε))] ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Wang–Wibisono, [ICLR 2023](https://openreview.net/pdf?id=yYbhKqdi7Hz), Thm 2 and Cor 2 ([arXiv:2302.07851](https://arxiv.org/abs/2302.07851)); prior; **δ = 0 only** | O((√κ/γ)·log(V₀/ε)), with V₀ ≤ Δ + μ‖x₀−x⋆‖² ≲ Δ/γ → at δ = 0, O((1 + √κ/γ)·log(1 + Δ/(γε))) | None: same order | Exact gradient → relative error δ < 1. The √κ/γ order survives while δ² ≲ γ/√κ | Thm 2 bounds 𝔼[e^{c T_k}(f − f⋆)] at random times T_k; this theorem bounds the fixed-call expectation | Constants roughly 4× larger. Expectation only, whereas Cor 2 gives a high-probability bound |
| GD with step 1/(16L), potential f − f⋆ + (c/2)‖x−x⋆‖², c = min(μ, L, γμ/(8δ²)); my sketch, not a published theorem; δ ≤ 1/2 (for δ > 1/2, PL-GD gives κ/(γ²(1−δ²))) | O([1 + κ/γ + δ²κ/γ²]·log(1 + Δ/(γε))) → O([1 + √κ/γ + δ²κ/γ²]·log(1 + Δ/(γε))) | Gain factor ≈ min(√κ, γ/δ²) when κ ≥ 1, e.g. √κ for δ² ≤ γ/√κ. None (same order) once δ² ≳ γ or κ = O(1) | None | GD gives a deterministic last iterate. This result gives only an expected value | GD allows call-dependent, adversarial errors. This result requires one fixed, non-adaptive map g |
| Kuruzov–Stonyakin, [arXiv:2407.01051v3](https://arxiv.org/abs/2407.01051) (Aug 2026, preprint), Thm 3.3, restarted CG; **absolute error, exact 2-D subspace minimization** | O((√κ/γ)·log(Δ/ε)) gradient calls plus exact subspace solves (cost not bounded by a gradient count; Sec. 4 needs convex subproblems) → as above | Not comparable: different oracle | Their absolute error δ₁² ≲ γ²με, converted locally to relative error, needs δ ≲ γκ^{−1/2}. This result allows δ ≲ √γ κ^{−1/4} | None (both last iterate) | Their guarantee is deterministic. They need a subspace-minimization oracle, which this method avoids |
| Repository [AcceleratedInexactStronglyConvex](../../LongTails/Theorems/AcceleratedInexactStronglyConvex.lean); prior; **μ-strongly convex (γ = 1) overlap** | O((√(κ/(1−δ)) + δ²κ/(1−δ))·log(1 + LR²/ε)) → same order at γ = 1 | None on the overlap | Strongly convex → strongly quasar-convex (nonconvex) | None | On the overlap the sibling is broader: it allows call-dependent errors and an additive error, and its guarantee is deterministic |

**Reduction check and proof ancestry.** The perturbed inequality ⟨g, x−x⋆⟩ ≥ (γ/2)(f − f⋆) + (γμ/2 − δ²L/γ)‖x−x⋆‖² plugs into Wang–Wibisono only when δ ≲ γκ^{−1/2}. Catalyst/proximal reductions fail because proximal subproblems of a quasar-convex f need not be quasar-convex. Batching does not remove a deterministic bias. So the δ ≲ √γ κ^{−1/4} regime is not a routine corollary. The mechanism grafts the repository's strongly convex curvature-reserve argument (a fixed 1/L primal step, with a Young split of θ⟨e, z−x⋆⟩) onto the continuized generator of Wang–Wibisono. It uses one-point quasar reserves in place of convex interpolation. That is a genuine but modest adaptation.

**Search coverage (2026-10-16 UTC).** I searched arXiv, ICLR/ICML/COLT proceedings and journals for quasar/weakly-quasi-convex acceleration with inexact, relative or biased gradients. I read Wang–Wibisono Thm 2/Cor 2, Kuruzov–Stonyakin Thms 3.2–3.4, Hermant et al. [arXiv:2512.16533v2](https://arxiv.org/abs/2512.16533) Assumption 4 (unbiased with strong growth, so no fixed bias) and Kornilov et al. [arXiv:2310.00506](https://arxiv.org/abs/2310.00506) Thm 3.2 (strongly convex, relative error, tolerance δ ≲ κ^{−1/2}). I did not read Hinder–Sidford–Sohoni (COLT 2020; uses function values) beyond secondary summaries, nor Gbaguidi–Hermant or Hallak–Levy. The companion note's claims match what I checked. However, its GD baseline O(κ/γ) holds only for δ² ≤ γ/8. Retuning c extends it to κ/γ + δ²κ/γ², so the δ²κ/γ² term is not an improvement. The theorem was introduced in commit 2f335d4 (2026-10-16). I found no subsequent or concurrent work.

## Conclusion

**Yes, but narrowly: this is the first accelerated relative-error guarantee I found for strongly quasar-convex objectives. The rate gain is only in the √κ term.** Without exact gradients, the strongest applicable baseline is gradient descent with the same relative-error oracle. Up to a shared log(1 + Δ/(γε)) factor and for δ ≤ 1/2:

| | GD (relative error) | this result |
|---|---|---|
| calls | κ/γ + δ²κ/γ² | √κ/γ + δ²κ/γ² |

This is a speedup of up to √κ when κ ≫ 1 and δ² ≲ γ/√κ. There is no gain once δ² ≳ γ. At δ = 0 it only matches Wang–Wibisono's exact-gradient continuized acceleration. The published quasar method with inexact gradients (Kuruzov–Stonyakin) needs exact subspace minimization and tolerates only δ ≲ γ/√κ.

The comparison proves the gain only against my own sketched GD bound and against reductions that I checked fail. It does not prove that no other method does better. The proof adapts the repository's strongly convex relative-error argument to the continuized quasar dynamics. On the strongly convex overlap it adds nothing. It is weaker than GD in two ways: it gives an expected rather than deterministic guarantee, and it requires a fixed rather than call-dependent error map.

What can be claimed is that accelerated √κ/γ complexity survives a fixed relative gradient bias up to δ ≈ √γ κ^{−1/4} on a standard nonconvex class. This extends a known strongly convex result. It is not a new acceleration principle.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
