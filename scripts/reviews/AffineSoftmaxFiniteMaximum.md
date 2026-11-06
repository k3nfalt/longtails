# Novelty assessment: AffineSoftmaxFiniteMaximum

[`result`](../../LongTails/Theorems/AffineSoftmaxFiniteMaximum.lean) proves the following. Take `m ≥ 2` components that are convex, `G`-Lipschitz and `L`-smooth on the ball `B(x₀,R)` in any finite-dimensional space, with a constrained minimizer `xstar` ([setup](../../LongTails/Setups/SmoothFiniteMaximum.lean)). Each oracle call returns one component's exact value and gradient. Under these assumptions, the randomized [algorithm](../../LongTails/Algorithms/AffineSoftmaxFiniteMaximum.lean) returns a feasible point with `max_i f_i(x) − max_i f_i(x⋆) ≤ ε` with probability at least 0.9.

**Complexity.** The parameters are: `m` components, Lipschitz bound `G`, smoothness `L`, radius `R`, and accuracy `ε`. The bound below is the public budget `⌈2·10²¹ h⁷ S⌉`, where `h = 1 + ⌈log₂⌈2+m+GR/ε+LR²/ε⌉⌉`:

N = O( log⁷(2+m+GR/ε+LR²/ε) · [ m + m(LR²/ε)^{1/3} + m^{3/4}(LR²/ε)^{1/2} + m^{6/7}(GLR³/ε²)^{2/7} + GR/ε ] ).

The budget counts every call: caches, sampling, searches, the six repetitions, the `6m` scoring calls and padding.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| AGD on the max of linearizations ([Nesterov 2018 §2.3.1](https://link.springer.com/book/10.1007/978-3-319-91578-4); listed in [COLT'21 App. A.3](https://proceedings.mlr.press/v134/carmon21a/carmon21a.pdf) and [SODA'24 Table 1](https://arxiv.org/abs/2311.10886)) | m(1+√(LR²/ε)) → N | Polynomial gain when LR²/ε ≫ 1 and m ≫ max{G²/(L^{3/2}R√ε), G/(√L·√ε)}·polylog. Gain factor ≤ ε^{-1/7} after normalization | None | None. Both use the same oracle and return a point | Deterministic → probability 0.9. Pays log⁷ and a 10²¹ constant. Worse for small m (e.g. m ≲ ε^{-1/2} when G=L=R=1) |
| [Carmon–Jambulapati–Jin–Sidford, COLT 2021](https://proceedings.mlr.press/v134/carmon21a/carmon21a.pdf), Thm 6 (arXiv:2105.01778v1, Thm 2) | Õ(m(GR/ε)^{2/3} + √m(GR/ε + √(LR²/ε))) → N | On the overlap below, always dominated by the AGD or SODA rows, so not decisive | None (COLT assumes a global minimizer within R; this setup a ball-constrained minimizer — a minor variant) | None. COLT's guarantee is already probability 0.99 | None found |
| [Carmon–Jambulapati–Jin–Sidford, SODA 2024](https://arxiv.org/abs/2311.10886) (arXiv v1, 17 Nov 2023), Thm 8.1 | Õ(m(LR²/ε)^{1/3} + (GR/ε)²) evaluations, under ε ≤ min{LR², G²/L} → N | Gain when m ≪ G²R^{4/3}/(L^{1/3}ε^{5/3}), i.e. the (GR/ε)² term dominates. Its ε^{-2} term becomes GR/ε plus mixed terms | None | Expected error with runtime holding w.p. 0.9 → accuracy w.p. 0.9. Markov plus a cutoff converts between them at constant cost | No gain (same order) for m ≳ ε^{-5/3}, where the shared m(LR²/ε)^{1/3} term dominates both. SODA also covers the simplex geometry, which is not part of this setup |

**Normalized comparison.** Set G=L=R=1 and m=ε^{-α}, ignoring polylogs. The new exponent is max{1, α+1/3, (6α+4)/7}. The best prior exponent is min{α+1/2, max(α+1/3, 2)}. The new bound is strictly better for 1/2<α<5/3, and the largest gain, ε^{-1/7}, occurs at α=3/2.

Example: at m=ε^{-3/2}, both AGD and SODA give ε^{-2}, while this result gives ε^{-13/7}. COLT's lower bound (Thm 10) is Ω(m·min{(GR/ε)^{2/3},(LR²/ε)^{1/3}} + min{(GR/ε)², √(mLR²/ε)}) = ε^{-11/6}, so a gap of 1/42 remains. No optimality is claimed.

**Standard-reduction check.** Ball acceleration and multilevel local-to-global reductions come from [Carmon–Hausler, NeurIPS 2022](https://arxiv.org/abs/2203.13225). The reciprocal-product estimator comes from Moka–Kroese–Juneja (2019). Both are proof ancestry.

Substituting SODA's affine-cache ball solver into these frameworks does not give N: the improvement depends on the new variance bound `8(L²r² + G²L²r⁴/τ²)` for the centered estimator. That bound is stated in [`AffineSoftmaxMoments`](../../LongTails/Proofs/AffineSoftmaxMoments.lean) (`seeded_estimator_variance`). This is the variance reduction on larger balls that SODA §1.1 leaves as "a promising direction for future work", and it is the genuinely new mechanism. I did not rebuild the proof or run the axiom audit.

**Search coverage (6 Nov 2026).** I read the theorem statements of SODA Thm 8.1 and COLT Thms 6 and 10, and searched arXiv and the proceedings for 2024–2026 follow-ups on minimizing a maximum or the maximal loss.

- [Gladin et al., ICML 2026](https://proceedings.mlr.press/v306/gladin26a.html) treats LogSumExp, not a max-gap complexity.
- [arXiv:2609.32872](https://arxiv.org/abs/2609.32872) (Sep 2026) gives Õ(mε^{-2}) value queries at k=1 for nonsmooth components.
- Neither improves the baselines. I found no subsequent work matching N.
- The companion note's numbering and claims agree with the sources I checked. I did not verify its unread OpenReview item.

**Conclusion**

**Yes: for an intermediate range of component counts, the proved oracle complexity beats every published upper bound I found.** The strongest baselines are AGD on the max of linearizations, at m√(LR²/ε) calls, and Carmon et al.'s SODA 2024 ball method, at m(LR²/ε)^{1/3} + (GR/ε)². The setup, oracle and accuracy criterion are the same up to a constant-cost conversion between expected and probability-0.9 accuracy.

| G=L=R=1, m=ε^{-α} | prior best | this result |
|---|---|---|
| α=1 | ε^{-3/2} | ε^{-10/7} |
| α=3/2 | ε^{-2} | ε^{-13/7} |

The gain holds strictly for ε^{-1/2} ≪ m ≪ ε^{-5/3}. In general parameters, it needs LR²/ε ≫ 1 and max{G²/(L^{3/2}R√ε), G/√(Lε)} ≪ m ≪ G²R^{4/3}/(L^{1/3}ε^{5/3}), up to logarithms. Outside that range the bound loses: to AGD for small m, and it ties SODA for very large m.

The gain is modest: the speedup is at most a polynomial factor ε^{-1/7}, it carries a log⁷ factor, and it stays 1/42 in the exponent above COLT's lower bound at α=3/2. The improvement does not come from recombining known theorems. It comes from a new centered, reciprocal-corrected Gibbs gradient estimator whose variance stays controlled on the larger balls. SODA named that combination as an open direction.

The comparison establishes the gain. Priority rests on a search that found no later or concurrent match, which does not prove none exists. What can be claimed is a new best-known upper bound on first-order oracle complexity for minimizing a maximum of smooth convex functions in the stated intermediate-m regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
