# Novelty assessment: StrongGrowthConvexFiniteSumAcceleration

The [theorem](../../LongTails/Theorems/StrongGrowthConvexFiniteSumAcceleration.lean) treats f = n⁻¹Σᵢfᵢ on a finite-dimensional space ([setup](../../LongTails/Setups/FiniteSumStrongGrowthConvex.lean)). Each fᵢ is convex and L-smooth, global strong growth n⁻¹Σ‖∇fᵢ(x)‖² ≤ ρ‖∇f(x)‖² holds, a minimizer x⋆ exists, and ‖x₀−x⋆‖ ≤ R. The mean need not be strongly convex. Under these assumptions, the last primal iterate of an accelerated minibatch proximal-point method ([algorithm](../../LongTails/Algorithms/EmpiricalProximalAcceleration.lean)) satisfies E[f(X)−f(x⋆)] ≤ ε. The method uses batches of r = min{n,⌈1024ρ⌉} indices, solves each prox subproblem with Katyusha, and runs on a deterministic budget that counts every exact component-gradient call.

**Complexity (component-gradient calls).** The proved budget is 7000(r+⌈√(rLR²/ε)⌉)·⌈log₂⌈2³²ρ⁵⌉⌉, which simplifies to

  O( (min{n,ρ} + √(min{n,ρ}·LR²/ε)) · (1+log ρ) ),

valid for L, ε > 0, ρ ≥ 1 and R ≥ 0. Here L is the component smoothness, ρ the strong-growth constant, R the initial distance, n the number of components and ε the accuracy. Below, T = LR²/ε. The mean's smoothness L_f ≤ L and the mean-squared smoothness L̄ ≤ L both enter only the baselines.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SNAG under SGC, [Hermant et al., arXiv 2410.07870v3](https://arxiv.org/abs/2410.07870), Thm 3, eq. (8), and Thm 5 for batching (prior; per the note, ICLR 2025) | O(ρ√(L_fR²/ε)) → O((min{n,ρ}+√(min{n,ρ}T))(1+log ρ)) | For ρ ≤ n: factor ≈ √(ρL_f/L)/log ρ. Needs ρL_f/L ≫ log²ρ and L_fR²/ε ≫ log²ρ. With L_f ≈ L, ρ√T becomes √(ρT). | Incomparable classes: SNAG needs neither a finite sum, nor component convexity, nor component smoothness. | None: both use known constants and bound the expected last iterate. | Needs component convexity and finite-sum reuse. Worse when L_f ≲ L log²ρ/ρ. Extra log ρ factor. |
| Generic accelerated finite-sum methods, e.g. Katyusha ([Allen-Zhu, JMLR 2018](https://jmlr.org/papers/volume18/16-410/16-410.pdf), convex corollary; theorem not re-read) (prior) | O(n + √(nT)), up to a log in the n term → same as above | Factor ≈ √(n/ρ)/log ρ when ρ log²ρ ≪ n ≲ T. Factor ≈ n/(√(ρT) log ρ) when n ≥ T. | None: subclass, because strong growth is added. | None | Strong growth forces a common minimizer. When ρ ≳ n the result is worse by a log ρ factor. |
| Repository: [ProximalStormStrongGrowth](../../LongTails/Theorems/ProximalStormStrongGrowth.lean), 2026-10-18 (prior). It applies on this class with Γ² = ρ−1, since a same-index pair query is available. | O((ρ + ρ^{3/4}√(L̄R²/ε))(1+log ρ)) → same as above | For ρ ≤ n: factor ≈ ρ^{1/4}√(L̄/L). Worse when L̄ < L/√ρ. | None here. That class is broader: stochastic, with no component convexity. | That result selects its output iterate by a seed. | Needs component convexity. Loses when L̄ ≪ L. |
| [Novoselov–Dorn–Dvinskikh–Gasnikov, arXiv 2610.38354v1](https://arxiv.org/abs/2610.38354), 28 Oct 2026, Thm 5.1 (sample-reuse envelope method; prior) | ≈ O(T log(KN)) total samples, from its statistical term H_sR²/min{S,mKN} → same as above | When ρ ≤ n: factor ≈ √(T/ρ)/log ρ for ρ ≪ T. | Not comparable: it assumes interpolation only, with no ρ. Its lower bound shows that interpolation alone forces Ω(T) samples. | None | Needs strong growth, which is stronger than interpolation. |

**Reduction and mechanism.** I found no standard reduction that gives this bound.

- **Regularization.** Adding λ‖x−x₀‖²/2 to the [strongly convex sibling](../../LongTails/Theorems/StrongGrowthFiniteSumAcceleration.lean) moves the minimizer, where the components' gradients become nonzero. Strong growth then fails there.
- **Batched SNAG.** Batching SNAG keeps the linear ρ factor (Hermant Thm 5 and Remark 8).
- **ERM on a subsample.** Running Katyusha on a subsample needs about T samples under interpolation-only optimistic rates.
- **Chadha–Cheng–Duchi.** The accelerated minibatch prox method of [Chadha–Cheng–Duchi, arXiv 2101.02696](https://arxiv.org/abs/2101.02696) (Thm 2 and Cor 3.2) assumes a uniform variance bound σ₀², which strong growth does not supply on an unbounded domain. It also takes exact prox steps and does not bound their cost. Its interpolation results (Thm 3 and Cor 4.1) need quadratic growth.

**Proof ancestry, not competitors.** The proof draws on minibatch prox ([Asi et al., NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/file/fa2246fa0fdf0d3e270c86767b77ba1b-Paper.pdf); Wang–Wang–Srebro, COLT 2017), an accelerated proximal potential, the Katyusha inner solver, and the sibling's variance bound at the fixed prox point. The ingredient that appears new is a stability estimate for the adaptive empirical prox point, closed by the displacement bound D ≤ 8λ²H.

**Instance check.** I verified the note's family by hand, with a fraction 1/q of the components equal to a+qb, the rest equal to a, and φ = s²/2 − log cosh s:

- the ratio n⁻¹Σ‖∇fᵢ‖²/‖∇f‖² = (‖∇a‖²+q‖∇b‖²)/(‖∇a‖²+‖∇b‖²) ≤ q, so ρ = q;
- every component is convex and L-smooth;
- f has quartic, not quadratic, growth in u;
- L_f = L̄ = L.

**Search coverage.** On 2026-11-11 UTC I searched arXiv and the web for strong growth, interpolation, finite-sum acceleration and minibatch prox, and read the cited theorems above. The result was committed on 2026-11-11 (`3435a940`).

- **Read only partly.** I read Novoselov et al. Appendix C only partially; the total cost above is my inversion of Thm 5.1.
- **Not re-read.** I did not re-read Katyusha's corollary, ProximalStorm's proof, or [Mishkin et al.](https://arxiv.org/abs/2404.02378v2). The repository's sibling review records that Mishkin et al. withdrew their √ρ claim in v2.
- **Not checked.** I did not check the inaccessible NeurIPS 2026 OpenReview record that the note flags.
- **The note.** It omits Novoselov et al. Its other comparisons match what I checked.

**Conclusion**

**Yes: when ρ is much smaller than n and LR²/ε, the proved total complexity beats every applicable method I checked.** Strong growth moves the √ρ gain from the strongly convex case to merely convex finite sums. The strongest baselines are SNAG/stochastic AGD under strong growth, generic accelerated finite-sum methods, and the repository's STORM-type bound.

| Method | Component-gradient calls (logs suppressed) |
|---|---|
| Katyusha / accelerated finite sum | n + √(nT) |
| SNAG under strong growth | ρ√(L_fR²/ε) |
| Proximal STORM | ρ + ρ^{3/4}√(L̄R²/ε) |
| This result (ρ ≤ n) | (ρ + √(ρT))·log ρ |

Take ρ = q and n = T = q³, an instance satisfying every assumption with L_f = L̄ = L. Ignoring constants, this result costs q² log q, against q^{9/4} log q, q^{5/2} and q³ for the baselines. It loses when ρ ≳ n (by a log ρ factor against Katyusha), when L̄ ≪ L/√ρ, or when L_f ≪ L log²ρ/ρ. It also needs convex components and repeatable component queries.

The comparison establishes this gain. My search found no earlier ρ+√(ρT) bound for convex finite sums, but that does not prove priority. The gain is polynomial, though modest against the STORM bound (ρ^{1/4}), and no lower bound shows it is optimal.

What can be claimed is a new accelerated component-gradient bound of order ρ+√(ρLR²/ε), up to log ρ, for convex finite sums with strong growth and no strong convexity.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
