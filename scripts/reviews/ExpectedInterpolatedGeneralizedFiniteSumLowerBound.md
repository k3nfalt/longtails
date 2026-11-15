# Novelty assessment: ExpectedInterpolatedGeneralizedFiniteSumLowerBound

The [theorem](../../LongTails/Theorems/ExpectedInterpolatedGeneralizedFiniteSumLowerBound.lean) is a `NonConvergence` result in the [setup](../../LongTails/Setups/ExpectedInterpolatedGeneralizedFiniteSum.lean). It covers convex components fᵢ that share a minimizer and satisfy ‖∇²fᵢ‖ ≤ L₀ + L₁‖∇fᵢ‖. Against every randomized, adaptive algorithm that queries component values and gradients, and at every fixed budget up to the one below, some instance (chosen without seeing the seed) has expected objective gap above ε. No algorithm restriction is imposed, so no algorithm file applies.

**Proved necessary budget**, with universal constants suppressed (the Lean statement has the factor 10⁻⁹):

  b ≥ Ω( [ n + √(n L₀R²/ε) + √n·L₁R + n(L₁R)^{2/3} ] / log²(2 + n + L₁R + L₀R²/ε) ) component calls.

- n ≥ 2 is the number of components and R bounds ‖x⋆‖. L₀ > 0 and L₁ ≥ 0 are the curvature constants.
- The initial gap satisfies Δ ≥ 2ε, and the bound does not depend on it.
- The regime requires L₀R²/ε ≥ 4n. This is necessary: under interpolation, SGD avoids the n term otherwise.
- The dimension must be at least 2⁸⁰(1 + n + L₁R + L₀R²/ε)²⁴.
- The regime is nonempty: n = 2, L₀ = 8, R = ε = 1, Δ = 2, with d large.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, [Descending Everest II](https://arxiv.org/abs/2611.04171), Thm 7.1 (preprint; v1 3 Nov 2026, v2 5 Nov 2026; prior). Applies only when heterogeneity δ satisfies L₁²R²δ/ε ≥ 3 | Ω([n(1+(L₁R)^{2/3}) + √(n(L₀+L₁²δ)R²/ε + n(L₁R)²)] / log²(4+n+(L₀+L₁²δ)R²/ε+(L₁R)²)). At the smallest admissible δ = 3ε/(L₁R)² this is the same four terms → the bound above | None: same order. The log arguments agree up to a factor of 2 | Instances with δ ≥ 3ε/(L₁R)² > 0 → the interpolating subclass δ = 0. A lower bound on a subclass is stronger, and §7.2 says Thm 7.1 "cannot be automatically transferred" there. Also covers L₁ = 0 | None. Everest's expected-stopping-time lower bound already covers fixed-budget algorithms | Requires L₀R²/ε ≥ 4n. Explicit polynomial dimension instead of an unspecified large dimension. Common L₀ (Everest also allows L₀,ᵢ = L₀). Constant 10⁻⁹ |
| Woodworth–Srebro, [arXiv 1605.08003](https://arxiv.org/abs/1605.08003), Thm 7 (randomized, smooth convex; NeurIPS 2016 per the authors). Special case L₁ = 0 | Ω(n + √(nL₀R²/ε)) → Ω((n + √(nL₀R²/ε))/log²(2+n+L₀R²/ε)) | Worse by log² at L₁ = 0 | Non-interpolating hard instances (linear terms on a ball; a shared ‖x‖²/2 in the unconstrained remark) → common minimizer | None | Their oracle also includes prox, so their bound covers a stronger oracle. The selected result adds the L₀R²/ε ≥ 4n restriction |

**Reduction check.** The interpolating version is not obtained by substituting into Everest's theorem. Its Assumption 2.6 forces δ > 0, and its hard families need component gradients that cancel at x⋆. The obvious repair, tilting each component by −∇fᵢ(x⋆), changes the (L₀,L₁) constants and depends on hidden data.

The selected proof (companion note; I did not re-derive it) supplies two new pieces:
- public, paired linear centering of the exponential chains, with an additive 2CL₁²/7 absorbed into L₀;
- a link chain spread over distinct hidden component pairs, which produces the n(L₁R)^{2/3} term.

At L₁ = 0 the terms n + √(nH), with H = L₀R²/ε, are routine. Private-block chains without a shared quadratic interpolate automatically. That is my check, not a cited theorem.

Proof ancestry: Everest II's hard families and its hidden-coordinate and Yao-type averaging (App. D), and the Woodworth–Srebro randomized-hiding technique.

**Upper-bound gap (not a competitor).** Everest II Thm 5.1 needs only actual heterogeneity ≤ δ̄. Taking δ̄ = 3ε/(L₁R)² applies it to interpolating instances. It gives expected cost O(T₀ log²(N₀ + Δ/ε)), where T₀ and N₀ are the table-row bound's numerator and log argument at δ = 3ε/(L₁R)². This is about log⁴ above the lower bound for a stopping-time method. Two steps are the companion's and I did not check them: the restart conversion to a fixed budget (an extra log(Δ/ε) factor), and the extension from C² to differentiable gradients.

The repository's [AcceleratedInterpolatedGeneralizedFiniteSum](../../LongTails/Theorems/AcceleratedInterpolatedGeneralizedFiniteSum.lean) proves Õ(n(1+(L₁R)²) + √(nH)) in a related setup, which leaves a gap in L₁R.

Gorbunov et al. ([arXiv 2409.14989v2](https://arxiv.org/abs/2409.14989), §7) prove interpolation SGD bounds on a gap clipped at about L₀/(nL₁²). That is not the expected-gap criterion, and I read §7 only through a summary, so it is not a table row.

**Search coverage (15 Nov 2026).** I searched arXiv and web sources for interpolation, common-minimizer, and (L₀,L₁) finite-sum lower bounds, and found none for δ = 0. I read Everest II v2 §§2, 5, 7.2 and 8.1, but not its Appendix E proofs. I read Woodworth–Srebro's HTML except the §5.2 body. The companion note's citations and its "open in §8.1" claim match what I read. The result was introduced in commit `1e7d4c94` on 15 Nov 2026, twelve days after Everest II v1 posed the question. Work from that window may not be indexed yet.

**Conclusion**

**Yes, for scope: the known finite-sum hardness of (L₀,L₁)-smooth convex finite sums survives interpolation, though the rate itself is unchanged.** The strongest baseline is Everest II Thm 7.1, which proves the same bound only when the components' minima disagree:

| | Instance class | Lower bound (up to log²) |
|---|---|---|
| Everest II, Thm 7.1 | heterogeneity δ ≥ 3ε/(L₁R)² | n + √(nL₀R²/ε) + √n·L₁R + n(L₁R)^{2/3} |
| This result | common minimizer (δ = 0), L₀R²/ε ≥ 4n | same |

The interpolating instances form a subclass, so hardness there is strictly stronger. Everest's authors list this case as open, and their hard instances rely on non-shared minimizers. With Everest's upper bound, this shows interpolation does not reduce worst-case complexity, up to about log⁴ and the companion's unchecked log(Δ/ε) conversion.

There is no new rate or algorithm. The L₁ = 0 part is routine, the constants are astronomically small, and the dimension is huge. The L₀R²/ε ≥ 4n restriction is genuinely needed. Priority rests on a twelve-day window and could change if concurrent work appears.

What can be claimed is the first lower bound I found that keeps all four Everest II terms for interpolating (L₀,L₁)-smooth finite sums, through a new centering construction.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
