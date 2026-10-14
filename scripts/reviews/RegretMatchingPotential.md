# RegretMatchingPotential: novelty assessment

The [theorem](../../LongTails/Theorems/RegretMatchingPotential.lean) ([setup](../../LongTails/Setups/RegretMatchingPotential.lean), [algorithm](../../LongTails/Algorithms/RegretMatchingPotential.lean)) proves that zero-initialized, undiscounted, **simultaneous** RM+ in a two-player exact potential game outputs an additive ε-Nash mixed profile, for every admissible game and seed. The output is the last pre-update profile at which both observed regret vectors are ≤ ε. It is neither the last iterate nor an average.

**Proved complexity.** Here m,n ≥ 1 are the action counts, B > 0 bounds the potential P ∈ [0,B]^{m×n}, and ε > 0. Payoff levels are unrestricted. One call returns both exact vectors (Ay, Cᵀx) at an arbitrary query pair. The algorithm knows m, n, and ε; it does not use B in its updates.

  ⌈20000·B²(m+n)⁴/ε²⌉ + 1 = O(1 + B²(m+n)⁴/ε²) calls.

If ε ≥ B, every profile is already ε-Nash, but the budget is still Θ((m+n)⁴).

All rows use paired-vector calls and the same ε-Nash criterion. Prior RM bounds are rescaled from unit-range utilities through RM+'s invariance to shifts and positive scaling: utilities P y ∈ [0,B], so Φ_range ≤ B and ε becomes ε/B. One alternating round costs two calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Anagnostides et al., [arXiv 2510.17067 v2 (17 Nov 2025), ICLR 2026](https://arxiv.org/abs/2510.17067), Cor. 3.5: ε-lazy alternating discounted RM+, γ=1/2 | O(1 + max(m,n)B²/ε²) → O(1 + B²(m+n)⁴/ε²) | Worse by a factor of about (m+n)⁴/max(m,n); the ε and B exponents are the same | None: both cover all n-player exact potential games (prior) ⊇ two-player games (current) | None: both use ε and certify an observable round | Prior uses discounting, sequential updates, and lazy skipping. Current uses ordinary simultaneous RM+, but is limited to two players |
| Same paper, Thm. 3.4: ε-lazy alternating RM+, any initialization including zero | O(1 + max(m,n)²B⁴/ε⁴) → O(1 + B²(m+n)⁴/ε²) | ε⁻⁴ → ε⁻². The gain holds only if ε < B·max(m,n)/(m+n)²; otherwise current is worse | None | None | Same as above; prior is lazy and alternating |
| Same paper, Thm. 3.12: ε-lazy simultaneous RM+ from zero, smooth product-simplex objectives | O_ε(ε⁻⁸) (constants not explicit) → O(1 + B²(m+n)⁴/ε²) | ε⁻⁸ → ε⁻² for fixed m, n, B | None: the prior covers a broader class | Lazy (skip low-gap players) → always update | Current covers only two-player bilinear potentials |
| Direct method (derived): max(m,n) queries (x,y) = (eᵢ, eⱼ) recover A and C; set P(i,j) = A(i,j) − A(1,j) + C(1,j) − C(1,1), up to an additive constant; play argmax P | O(max(m,n)), exact (ε = 0) → O(1 + B²(m+n)⁴/ε²) | Worse in every regime, with no ε dependence in the prior | None | Prior returns an exact pure Nash equilibrium | Prior is centralized and not an uncoupled learning dynamic. The setup's `allowedAlgorithm` excludes it, but it uses the same oracle |

Older methods are also checked. Unilateral better-response dynamics need O(1 + B/ε) calls, since each step raises P by more than ε. Hart–Mas-Colell (GEB 2003) and fictitious-play results are asymptotic. Non-lazy alternating RM+ (Thm. C.7) depends on the instance through δ = initial gap and is not comparable. Soleymani–Piliouras ([arXiv 2609.21976](https://arxiv.org/abs/2609.21976), 18 Sep 2026) prove constant regret for a different, optimistic RM variant, with no Nash rate.

**Standard-reduction check and proof ancestry.** No substitution of a prior theorem gives the current bound for non-lazy, undiscounted, simultaneous play. The new mechanism is the lagged-gain lemma (`lagged_le`) combined with a phase potential (`bound_of_potential`, `size_bound`). It bounds ‖Q_T‖₂ ≤ 100B(m+n)² uniformly in T. Ancestry: Lemma 3.3/C.5 (one-step improvement) and the regret-to-rate link in Thm. 3.4 come from Anagnostides et al. A withdrawn paper ([arXiv 2608.17417](https://arxiv.org/abs/2608.17417), v1 18 Aug 2026, withdrawn 24 Sep 2026 for unverifiable authorship) claims bounded regret only for alternating play.

**Search coverage.** Search on 2026-10-07 UTC covered arXiv, ICLR 2026, and general web searches; theorem texts were read from the 2510.17067v2 PDF. Hart–Mas-Colell and the withdrawn paper's proofs were not re-read. Git introduction: `7b749ed` (2026-10-04); all compared works predate it. The companion note has three discrepancies. It calls ε⁻⁸ *the* zero-initialization rate for potential games, but Thm. 3.4 gives ε⁻⁴ from any initialization (lazy alternating). It omits the ε⁻² discounted bound (Cor. 3.5). It reports bounded regret, which is an internal lemma, not the public theorem. No build or axiom audit was run.

**Conclusion**

**No: the ε-Nash guarantee is not better than existing methods; what is new is an analysis of plain simultaneous RM+.**

The strongest RM-family baseline is discounted alternating RM+ (Anagnostides et al., Cor. 3.5). With the same oracle and accuracy criterion:

| Method | Calls |
|---|---|
| Discounted alternating RM+ (prior) | O(1 + max(m,n)B²/ε²) |
| Simultaneous RM+ (this result) | O(1 + B²(m+n)⁴/ε²) |
| Recover the matrices, then take argmax P | O(max(m,n)), exact |

The selected result beats the earlier lazy RM+ bounds (ε⁻⁴ for any initialization with alternating updates, ε⁻⁸ for zero-initialized simultaneous updates). It does not beat these two methods in any regime, and it covers only two players.

The possibly new content is that RM+ needs no laziness, alternation, discounting, or threshold initialization here. It also gives a uniform-in-T regret bound for this dynamic, which partly answers the ICLR open question. The comparisons establish that this is not an optimization advantage. The literature search did not find this simultaneous-play analysis earlier, but that does not prove priority. The claimable contribution is a method-specific convergence and bounded-regret analysis of unmodified two-player simultaneous RM+, not an improved equilibrium-computation guarantee.

**Verdict: NO IMPROVEMENT** — **Confidence: high**
