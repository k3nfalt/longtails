# Best-bound B&B with hidden constraints: novelty assessment

[`result`](../../LongTails/Theorems/BestBoundHiddenMilp.lean) concerns the problem min cᵀz + dᵀy subject to Az + Gy ≤ b, ℓ ≤ z ≤ u, z ∈ ℤᵖ ([setup](../../LongTails/Setups/HiddenMixedIntegerLinear.lean)). The data are real, and A, G, b are hidden from the algorithm. The theorem proves that best-bound Dakin branch-and-bound with lazy keys ([algorithm](../../LongTails/Algorithms/BestBoundBranchAndBound.lean)) returns an exact optimum or a correct infeasibility certificate. This holds for every exact box-LP oracle, including adversarial choices of optimal solution. Validity requires either an infeasible root LP or a hidden λ ≥ 0 with d + Gᵀλ = 0.

**Complexity (box-LP calls):**

  min( 2N − 1, 1 + 4p·|G_λ| ) = O( min( N, 1 + p·|G_λ| ) ).

The quantities are:
- N = ∏ⱼ (uⱼ − ℓⱼ + 1)₊ is the number of integer points in the box.
- p is the number of integer variables.
- G_λ = { z ∈ ℤᵖ ∩ [ℓ,u] : (c + Aᵀλ)ᵀz − λᵀb ≤ OPT }, where OPT is the MILP optimum.

When the MILP is infeasible, G_λ is the whole box, so the bound is 2N − 1. An empty box gives 0, and p = 0 gives 1. The bound holds for every admissible λ, so effectively the minimum over λ applies.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Dey–Dubey–Molinaro, *B&B solves random binary IPs in polytime*, SODA 2021, [arXiv 2007.15192v4](https://arxiv.org/abs/2007.15192), Thm 3 (Lemmas 1, 3–5). **Special case only:** pure binary IPs (q = 0, z ∈ {0,1}ᵖ), with λ = λ* the optimal root dual | 1 + 2p·\|G_{λ*}\| nodes, one LP each → 1 + 4p·\|G_{λ*}\| (also capped by 2^{p+1} − 1) | None on the overlap. The selected bound is up to 2× larger, because it uses slack ≤ 2p instead of 1 per binary coordinate | Binary → general bounded integers, with the range-free factor 4p replacing the path length Σ(uⱼ − ℓⱼ). Pure → mixed with continuous y. λ* → any dual-feasible λ | None. Both are best-bound runs that certify optimality, under any variable choice and any optimal LP solution | Hidden-data oracle model. DDM count tree nodes; this theorem counts actual calls, with discards that cost no call |
| Classical Land–Doig/Dakin finite-termination bound (repository [LpBranchAndBoundMilp](../../LongTails/Theorems/LpBranchAndBoundMilp.lean); textbook leaf counting) and plain enumeration with degenerate boxes. Both cover the full setup | 2N − 1 (enumeration: N) → min(2N − 1, 1 + 4p·\|G_λ\|) | Better whenever 4p·\|G_λ\| + 1 < N. Example: binary, p = 60, \|G\| ≤ p³ gives about 4p⁴ ≈ 5·10⁷ calls versus 2⁶⁰. Never worse than 2N − 1; still up to 2× worse than enumeration when \|G_λ\| ≈ N | None (same class) | None | None beyond the added hidden λ. The λ is an analysis parameter whose existence follows from LP duality for any bounded-below root |

**Reduction check and mechanism.** The binary pure case is exactly DDM Thm 3, whose proof steps are all reused here: weak duality, best-bound keys ≤ OPT, and rounding a node solution to a good point. The proof adds a slack counter, a point's total slack to the node-box bounds (at most 2p). Branching never increases it, and it drops strictly for the associated good point. This replaces DDM's "chain length ≤ depth" step (Lemma 5), which for general integers would only give a factor of order Σ(uⱼ − ℓⱼ). That short new step, plus the routine elimination of y through d + Gᵀλ = 0, is the technical content. The best-first optimality results that DDM cite (their ref. [31]) are proof ancestry, not a competing bound.

The companion note's adversary lower bound (C(p,r) − 1 calls for any box-LP algorithm, against an upper bound of 1 + 8p·C(p,r)) is a supporting lemma, not part of `result`. The binomial step behind its "minimax-optimal up to O(p)" claim is checked only on paper. I did not search for priority of this lower bound specifically.

**Search coverage.** The searches ran on 2026-11-03 and covered DDM v4 (full text read), Borst–Dadush–Huiberts–Tiwari ([2012.08346](https://arxiv.org/abs/2012.08346)) and Borst–Dadush–Mikulincer ([2203.11863](https://arxiv.org/abs/2203.11863)), which are binary-only B&B corollaries via DDM, and general searches for general-integer or MILP good-point bounds. None of these sources gives such a bound. I could not access Dubey's Georgia Tech thesis (HTTP 403), which could contain an extension. The theorem was introduced in commit 331b31d6 (2026-11-03). The companion note states the DDM relation accurately and itself calls the upper bound "a short extension". Its "matching lower bound" headline goes beyond what `result` proves.

**Conclusion**

**The improvement is in scope: a known binary gap-dependent bound now covers general bounded integers and continuous variables, with the same rate.**

The strongest baseline is Dey–Dubey–Molinaro's Theorem 3, which applies only to pure binary programs:

| Setting | Previous | This result |
|---|---|---|
| pure binary, λ = λ* | 1 + 2p·\|G\| | 1 + 4p·\|G\| (same order, 2× constant) |
| general integer / mixed | classical 2N − 1 | min(2N − 1, 1 + 4p·\|G_λ\|) |

On binary instances, nothing improves. On general-integer and mixed instances, the comparison does prove a gain over the only verified applicable bound whenever 4p·|G_λ| + 1 < N. The factor p does not depend on the variable ranges, and avoiding that dependence is the one new proof step.

The gain is modest for two reasons. The extension is a short adaptation of DDM's association argument: rounding by reduced cost and a slack counter replace their depth bound. Also, no new random-instance bound on |G| for general integers is given, so the practical consequences are inherited from binary results. I found no prior general-integer statement, but one thesis was inaccessible, so priority is likely but not certain.

What can be claimed is a range-free extension of DDM's good-point bound to bounded mixed-integer programs, with exact LP-call accounting in a hidden-constraint model.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
