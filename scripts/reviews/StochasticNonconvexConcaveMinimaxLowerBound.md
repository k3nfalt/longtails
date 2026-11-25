# Novelty assessment: randomized lower bound for stochastic nonconvex–concave minimax

[`result`](../../LongTails/Theorems/StochasticNonconvexConcaveMinimaxLowerBound.lean) proves the following for the [setup](../../LongTails/Setups/StochasticNonconvexConcaveMinimax.lean). Take any randomized adaptive algorithm (any seed law, any output in ℝ^{2d}) that makes at most the budgeted number of queries. Then there is a jointly L-smooth function f, concave in y, together with a fresh-sample unbiased oracle of variance at most σ² that returns gradients only, on which E[2L·dist(x̂, prox_{Φ+ι_X}(x̂))] > ε. The hard instance depends on the algorithm but not on its seed ([hard instance and proof](../../LongTails/Proofs/NcConcaveLower.lean)). There is no algorithm definition, because this is a lower bound.

**Necessary budget.** The bound is

  N = Ω( L²DΔ/ε³ + L³D²Δσ²/ε⁶ ),  with the explicit constants 2⁻¹⁰⁰ and 2⁻¹⁶⁵.

- **Parameters.** L is the joint smoothness constant, D the diameter of the dual ball, Δ ≥ max_y f(0,y) − inf_X f(·,0) the initial primal–dual gap, σ² the variance bound, and ε the Moreau-envelope stationarity tolerance.
- **Validity conditions.** σ ≥ 0 is allowed, and the bound requires
  - 2⁶⁷ε² ≤ LΔ and 2³⁶ε ≤ LD;
  - d ≥ 2¹⁸⁰(LΔ/ε²)⁹(LD/ε)⁷(1+σ²LD/ε³), which is polynomial in the parameters.
- **Primal set.** X is public but depends on ε: it is a product of a ball of radius 2⁷√(Δ/L) and a ball of radius 2³³ε/L.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Wu–Gu–Yang, [arXiv:2609.14233v1](https://arxiv.org/abs/2609.14233) (13 Sep 2026, preprint), Thm 4.1 / Cor 4.2 (deterministic) and Thm 5.5 / Cor 5.6 (stochastic) | Ω(L²DΔε⁻³ + L³D²Δσ²ε⁻⁶) for zero-respecting methods → the same bound for arbitrary randomized methods | None: same order | Algorithm class: zero-respecting (support-restricted) → arbitrary randomized adaptive queries and outputs | None. Both use the expected Moreau-envelope criterion at 1/(2L). | Same ε-scaled primal-domain construction; no function values are returned (WGY's deterministic oracle returns them); a large polynomial dimension and huge constants |
| Song–Xu, [arXiv:2610.01662v2](https://arxiv.org/abs/2610.01662) (Oct/Nov 2026), Thm 4.4 (statement read only via summary) | Ω(L²DΔε⁻³ + L³D²Δσ²ε⁻⁶) for zero-respecting methods allowed same-sample batches under mean-square smoothness → the same bound for randomized methods with fresh samples | None: same order | Zero-respecting → arbitrary randomized | None | Incomparable oracle: Song–Xu covers stronger same-sample (variance-reduction) access, which is not covered here |
| W. Wu et al., [arXiv:2610.16991v2](https://arxiv.org/abs/2610.16991) (19 Oct 2026), Table 1, n = 1 row (transfer in §F.1, not read) | Ω(L²DΔε⁻³) for randomized methods, exact oracle with values, X = ℝ^d, success with probability 2/3, possibly exponential dimension (§7) → the same rate in polynomial dimension, plus the σ² term | At σ=0: none, same order. For σ > 0: adds the L³D²Δσ²ε⁻⁶ term, which this paper does not cover. | Exponential → polynomial dimension; deterministic oracle → stochastic oracle | Their probability-2/3 bound already implies an expectation bound at ε/3 by Markov's inequality, so the note's "expectation criterion" gain is not an improvement. | Their primal set is X = ℝ^d; here X is a constrained, ε-dependent set, so the classes are incomparable. Their oracle also returns values. |

**Reduction check and proof ancestry.**
- A y-independent f reduces the problem to the randomized nonconvex minimization lower bound of [Arjevani et al.](https://arxiv.org/abs/1912.02365). That gives only Ω(LΔσ²ε⁻⁴), a factor (LD/ε)² weaker.
- Embedding 2610.16991's finite-sum instance, with uniform component sampling, might give an ε⁻⁶ term at one variance scale. I did not verify its component variance. The note also makes no such claim.
- The base relay/clipped-dual instance and its prox analysis come from Wu–Gu–Yang; the hiding/word-counting lemma is reused from the repository.
- The new mechanism is dead-zone robustification, so that gradients are exactly local; Bernoulli/p masking of the whole frontier; a simulation coupling; and an approximate-prox transfer.
- The note states that the original instance leaks the next coordinate to dense queries. I checked only the Lean entry points, not that claim.

**Search coverage (24 Nov 2026).**
- **Scope.** arXiv 2022–Nov 2026 on NC–C and NC–SC lower and upper bounds, plus SAPD+ (NeurIPS 2022 and arXiv v4). The theorem was introduced in commit 14c09cf5 on 24 Nov 2026, after all cited works.
- **Read only via summaries.** WGY §5–6 and Song–Xu Thm 4.4.
- **Not checked.** Pan–Zheng–Li (2609.14235).
- **Open-problem statements.** Song–Xu's conclusion leaves this exact extension open. The WGY §6 quote comes from a summary of the paper, not the verbatim text.
- **Note discrepancy.** The SAPD+ Theorem 5 proof chains a smoothed weakly convex–strongly concave bound. The v4 abstract gives O(L³D²G₀ε⁻⁴(1+σ²/ε²)), not L³D²G₀ε⁻⁶ for every σ. The note's claim that the problem is "closed up to constants" therefore holds only for σ ≳ ε, and for σ = 0 via Lin–Jin–Jordan up to a logarithm. For 0 < σ < ε, the checked upper and lower bounds differ by a factor min(LD/ε, ε²/σ²).

**Conclusion**

**Yes. The rate itself is not new, but the class of algorithms covered is new.** Wu–Gu–Yang already proved the identical rate, but only for zero-respecting methods:

  Ω(L²DΔε⁻³ + L³D²Δσ²ε⁻⁶)

This theorem proves the same necessary budget for every randomized algorithm. That includes dense, nonlinear queries that a zero-respecting bound says nothing about, and the hard instances need only polynomial dimension.

For the σ-dependent term, this appears to be the first such bound against arbitrary algorithms. Song–Xu explicitly leave this extension open, and the only checked randomized NC–C bound (arXiv:2610.16991) covers just the deterministic term, possibly in exponential dimension. That deterministic term is therefore not new; only its dimension improves. Combined with SAPD+, the bound certifies optimality up to constants for noise σ ≳ ε. A gap of up to min(LD/ε, ε²/σ²) remains for 0 < σ < ε, contrary to the companion note's "closed" claim.

**Remaining uncertainties.**
- The hard family uses a primal set that shrinks with ε, so hardness for a fixed primal domain is not shown.
- Gradients-only replies make the σ=0 statement weaker in oracle terms than 2610.16991.
- Priority rests on a search of a very active two-month preprint stream, and some key statements were read only via summaries.

The claimable contribution is a randomized, polynomial-dimension lower bound that matches the known stochastic NC–C rate.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
