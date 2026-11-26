# Novelty assessment: HessianStableNewtonLowerBound

[`result`](../../LongTails/Theorems/HessianStableNewtonLowerBound.lean) proves a lower bound in the setup [`HighDimensionalHessianStableSkewMonotone`](../../LongTails/Setups/HighDimensionalHessianStableSkewMonotone.lean), using the hard instance in [`HsLowerBound`](../../LongTails/Proofs/HsLowerBound.lean). The guarantee is as follows. Take any randomized algorithm, with no `allowedAlgorithm` restriction, that queries exact `F(x)` and `DF(x)`. Give it at most `B` calls on each channel, where B is the budget below. Then some admissible instance has `E‖F(x̂)‖ > ε`. That instance is a gradient field `F = ∇f` (so `S = 0`), with f convex and Hessian-stable in the form `∇²f(y) ⪯ exp(M‖y−x‖)∇²f(x)`. It may depend on the algorithm and the budget, but not on the random seed.

**Proved budget (per channel):**

  B = ⌊(MD / (2¹⁸ log(2+MD)))^{2/3}⌋ = Ω((MD / log(2+MD))^{2/3}).

- **Parameters.** M is the stability constant. D bounds `‖x₀−x⋆‖`. ε is the target for the expected gradient norm. Λ bounds `‖∇²f‖` on `B(x⋆, 3D+1/(4M))`. d is the dimension.
- **Validity conditions.** `MD ≥ 2⁶⁰`, `εM²D ≤ Λ`, and `d ≥ 2²¹(MD)^{10/3}`.
- **No ε in the bound.** This is because the class is invariant under scaling f. The regime is nonempty: at `MD = 2⁶⁰`, B ≈ 2·10⁷.
- **Matching upper bound.** The same setup has [`HessianStableExpectedNewton`](../../LongTails/Theorems/HessianStableExpectedNewton.lean), with budget `⌈2¹⁷(1+(MD)^{2/3}) log³(3+MD+MΛ(D+1/M)²/ε)⌉` per channel. The gap between the two bounds is `O(log^{2/3}(2+MD) · log³(3+MD+MΛ(D+1/M)²/ε))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Carmon et al., [Acceleration with a Ball Optimization Oracle](https://arxiv.org/abs/2003.08078), NeurIPS 2020, Thm 24 and §5 "Smooth functions" (arXiv v1, Mar 2020). Applies only to the convex 1-Lipschitz or O(1/r)-smooth class. | r-local algorithms need Ω((R/r)^{2/3}) queries to reach suboptimality below R^{2/3}r^{1/3}. With r = 1/M and R = D this reads Ω((MD)^{2/3}) → Ω((MD/log(2+MD))^{2/3}) gradient+Hessian calls for E‖∇f‖ ≤ ε. | Not comparable as a number, because the classes differ. On its own class the prior bound is larger by a factor of log^{2/3}(MD). | Lipschitz or Moreau-smoothed max-of-linear hard functions → M-Hessian-stable (and M-QSC) convex functions. The prior hard functions are not Hessian-stable for any finite M, since their Hessians are absent or piecewise constant. This is the class where the Õ((MD)^{2/3}) upper bound lives. | Function-value suboptimality with probability 1−δ → expected gradient norm. These are different criteria and neither is converted to the other. | r-local oracle → pointwise (∇f, ∇²f), which is a weaker oracle and still covered. Needs MD ≥ 2⁶⁰, Λ ≥ εM²D, and d ≥ 2²¹(MD)^{10/3} instead of d ≈ 60(R/r)² log. Loses log^{2/3}. |
| Kornowski–Shamir, [Oracle Complexity of Simplex-based Matrix Games](https://arxiv.org/abs/2412.06990) (COLT 2025; v4, Feb 2026), main theorem. Applies only to bilinear ℓp/simplex games under matvec access. | Ω̃(ε^{-2/3}) two-sided matvecs, for deterministic algorithms → not comparable. | Not comparable. A single Hessian query cannot be simulated by a few matvecs, and these hard instances are not matrix games. | Incomparable classes: a fixed bilinear family versus general Hessian-stable convex functions. | None | Their bound covers only deterministic algorithms (they state randomized as open, §8). This result covers randomized algorithms but uses a different oracle. |
| Repository upper bound [`HessianStableExpectedNewton`](../../LongTails/Theorems/HessianStableExpectedNewton.lean), same setup. This is the gap reference, not a competing lower bound. | O((1+(MD)^{2/3}) log³(3+MD+MΛ(D+1/M)²/ε)) upper bound vs Ω((MD/log(2+MD))^{2/3}) lower bound. | Settles the polynomial dependence on MD. The remaining gap is log^{2/3}(MD)·log³(MD+MΛD²/ε). | None | None | No lower bound for the log(1/ε) or log Λ dependence. When Λ = e^{Θ(MD)}, the gap is poly(MD). |

**Reduction check.** Carmon et al.'s smoothed chain is only C^{1,1}. Softmax-smoothing Nemirovski's function is QSC with M ≍ 1/μ, but every gradient and Hessian then depends on all pieces, so the exact r-robust zero-chain needed for their Lemma 22 fails. Exact flatness also conflicts with Hessian stability: a singular Hessian direction would have to be singular everywhere.

The construction gets around this with a public ridge `λ‖u‖²/2` and compact-bump link profiles. Each bump obeys `|g₃| ≤ 4p g₂ + tiny`, with p ≍ log K. This gives termwise QSC with an M̂ ≍ K log K that does not grow with chain depth, plus exactly flat zero-chain zones and a radial override. To my knowledge this mechanism is new; it is the source of the log loss. Proof ancestry is Carmon et al.'s robust-zero-chain hiding (Lemma 22), the Diakonikolas–Guzmán override for unconstrained queries, and the repository's `SharpChainHiding`. None of these supplies a Hessian-stable instance.

**Search coverage.** The search was run on 2026-11-26, the same day the theorem was introduced (commit 8dd44f68). It covered:
- full text of Carmon et al. 2020 (§§3, 5);
- Doikov, arXiv:2308.14742 v1. Its §7 (Discussion) says that 2/3 is optimal only "for the methods based on the ball-minimization oracle";
- Adil–Bullins–Jambulapati–Sidford, arXiv:2410.24158 v2, which has lower bounds only for zero-respecting proximal and ball-constrained algorithms;
- Ene–Nguyen–Vladu, arXiv:2510.22088, which has no lower bound;
- Kornowski–Shamir v4;
- 2026 second-order lower bounds (arXiv:2610.22208, 2610.03222), both for Lipschitz-Hessian classes;
- web searches across NeurIPS, ICML and COLT.

I found no prior (∇f, ∇²f) lower bound for the Hessian-stable or QSC class. I did not read the Karmarkar–O'Carroll–Sidford papers, and I could not access ICLR 2027 submissions. The companion note's citations that I checked are accurate. I ran no build or axiom audit.

## Conclusion

**Yes: this is a new lower bound, and it shows that the (MD)^{2/3} rate of ball acceleration cannot be beaten by any randomized gradient-plus-Hessian method on this class.** The closest prior result is Theorem 24 of Carmon et al. (2020). It gives Ω((R/r)^{2/3}) for r-local oracles, but only on Lipschitz or smooth hard functions that are not Hessian-stable. It therefore says nothing about the class where their own Õ((MD)^{2/3}) Newton-based upper bound applies, and Doikov (2023) explicitly leaves this open.

| | queries per channel |
|---|---|
| upper bound (same setup) | O((MD)^{2/3} log³(MD + MΛD²/ε)) |
| this lower bound | Ω((MD / log MD)^{2/3}) |

The comparison establishes that the polynomial exponent 2/3 in MD is necessary. It does not settle the logarithmic factors, which can be large when Λ is exponential in MD. The result also needs large dimension, d ≳ (MD)^{10/3}, and a large problem scale, MD ≥ 2⁶⁰. The literature search did not find this result elsewhere, but searching cannot establish priority conclusively, especially for a result introduced today.

The contribution that can be claimed is the first lower bound for randomized algorithms with exact (∇f, ∇²f) access on Hessian-stable/QSC convex minimization, matching the known upper bound in MD up to polylogarithmic factors. It rests on a genuinely new Hessian-stable zero-chain construction.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
