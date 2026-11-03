# LP-based branch-and-bound for bounded MILP: novelty assessment

[`result`](../../LongTails/Theorems/LpBranchAndBoundMilp.lean) proves the following. Take the problem min cᵀz + dᵀy subject to Az + Gy ≤ b, z ∈ ℤᵖ, ℓ ≤ z ≤ u ([setup](../../LongTails/Setups/BoundedMixedIntegerLinear.lean)), and assume the root LP relaxation is bounded below. Then depth-first Land–Doig/Dakin branch-and-bound ([algorithm](../../LongTails/Algorithms/LpBranchAndBound.lean)) returns either an exact global optimum or a correct infeasibility certificate. This holds for every seed and every exact node-LP oracle, including one that picks among optimal solutions adversarially.

**Complexity (exact LP-oracle calls):**

  2N − 1, where N = ∏ⱼ (uⱼ − ℓⱼ + 1)₊

Here N is the number of integer points in the box [ℓ, u]. The budget is 0 when the box is empty and 1 when p = 0. For binary variables it is 2^{p+1} − 1. The budget does not depend on m, q, A, G, b, c or d.

Each oracle query is an integer box β = (ℓ′, u′). The oracle returns an optimal solution of the relaxation with the extra constraints ℓ′ ≤ z ≤ u′, or `none` if that LP is infeasible.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| LP-based branch-and-bound: Land–Doig, *Econometrica* 28 (1960); Dakin, *Comput. J.* 8(3):250–255 (1965). Textbook finite-termination argument, e.g. Conforti–Cornuéjols–Zambelli, *Integer Programming* (2014), Ch. 9; Wolsey, *Integer Programming*, Ch. 7 | Same algorithm and same node oracle. Leaves are nonempty and disjoint and each contains an integer point, so there are ≤ N leaves and ≤ 2N − 1 nodes → 2N − 1 | None: same bound, from the same leaf-counting argument | None. Both cover bounded integer variables and real data, and both need bounded node LPs | None. Both return an exact optimum or an infeasibility certificate | None found. The version here tolerates any optimal LP solution (not only vertices), which the standard argument already allows |
| Plain enumeration with the same oracle (folklore; also noted in the companion note): query the degenerate box β = (z₀, z₀) for each integer z₀ ∈ [ℓ, u] and keep the best answer | N → 2N − 1 | Worse: about 2× more calls in the worst case. The two are equal only when N ≤ 1 | None | None. Both return an exact optimum or an infeasibility certificate | B&B can prune and in practice often uses far fewer calls, but the theorem proves no such adaptive bound |
| Lenstra (1983, *Math. Oper. Res.* 8) and Kannan (1987): MILP in polynomial time for fixed p | Not comparable: these use the bit size of rational data and arithmetic operations, not node-LP calls | Not comparable | Their scope is incomparable: rational data with unbounded integers, versus real data with bounded z here | — | — |

The enumeration row checks out. With ℓ′ = u′ = z₀, any reply must have z = z₀ exactly. The `valid` assumption makes every node LP bounded, so N calls certify an optimum or infeasibility on exactly the same instances, oracle and output criterion.

**Reduction check and lower bound.** The theorem is the textbook potential/leaf-counting argument, with no new mechanism. Jeroslow ("Trivial integer programs unsolvable by branch-and-bound", *Math. Programming* 6:105–109, 1974) gives infeasible binary programs on which variable branching needs 2^{⌈p/2⌉} nodes. So the exponential budget is inherent to this algorithm family, not just to the proof. I did not verify the theorem text directly; the result is reported in secondary sources. Later work on tree size (e.g., Dey–Dubey–Molinaro, SODA 2021, [arXiv 2007.15192](https://arxiv.org/abs/2007.15192)) studies random or general-disjunction regimes and does not change the worst-case comparison.

**Search coverage.** Searched on 2026-11-03: the original Dakin and Jeroslow records, textbook treatments, and the references in the companion note. I could not open the full texts of Dakin 1965 or Jeroslow 1974, so their exact theorem statements come from the bibliographic and secondary records. The companion note says plainly that the result is classical and claims only a formalization. Git history (commit 48b86a6f, 2026-11-03) shows the task asked for a standard MILP setup, not a novel result. I found no discrepancy between the note and the Lean statement.

**Conclusion**

**No: this is the classical finite-termination bound for LP-based branch-and-bound, and it gives no new complexity, scope or output guarantee.**

The strongest baseline uses the same oracle: enumerate the integer points of the box and solve one degenerate-box LP for each.

| Method (same node-LP oracle) | Worst-case calls |
|---|---|
| Enumeration over z ∈ [ℓ, u] ∩ ℤᵖ | N = ∏ⱼ (uⱼ − ℓⱼ + 1)₊ |
| This theorem (depth-first B&B) | 2N − 1 |

On every instance class, the proved worst-case B&B bound is no better than enumeration, and it is worse by a factor of about 2 whenever N ≥ 2. The 2N − 1 node bound itself is the standard leaf-counting argument for Land–Doig/Dakin branching. The theorem's real-valued data, arbitrary choice of optimal LP solution, and boundedness assumption are all covered by that argument.

What is established is a faithful machine-checked formalization of a textbook theorem in this repository's oracle framework. That is useful infrastructure, but not a new mathematical result. No practical advantage of branch-and-bound (pruning, best-bound search) is quantified by the theorem.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
