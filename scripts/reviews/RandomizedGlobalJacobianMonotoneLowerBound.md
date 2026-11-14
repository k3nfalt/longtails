# Novelty assessment: RandomizedGlobalJacobianMonotoneLowerBound

The [theorem](../../LongTails/Theorems/RandomizedGlobalJacobianMonotoneLowerBound.lean) proves the following, for the [setup](../../LongTails/Setups/GlobalJacobianMonotoneExpected.lean): take any randomized adaptive algorithm with any output rule (no algorithm is constructed; `allowedAlgorithm` is the default) and any budget `b ≤ ⌊(LR²/(4096ε))^{2/5}⌋` of joint `(F(x), DF(x))` calls, with queries allowed anywhere in `ℝ^d`. Then there is a monotone `F` with an `L`-Lipschitz Jacobian and a zero within distance `R` of `x0` for which `E‖F(output)‖ ≤ ε` fails. The instance may depend on the algorithm and on `b`, but not on the realized seed.

**Necessary complexity.** Here `L` is the Lipschitz constant of `DF`, `R` bounds `‖x0 − x*‖`, `ε` is the expected residual-norm target and `d` is the dimension. The theorem shows that

> `N ≥ ⌊(LR²/(4096ε))^{2/5}⌋ + 1 = Ω((LR²/ε)^{2/5})` joint calls are needed,

provided `LR² ≥ 4096ε` and `d ≥ 4096(⌊(LR²/(4096ε))^{2/5}⌋+2)^5`, which is `Θ((LR²/ε)²)`.

The degenerate cases hold. The regime is nonempty: for example `L=4096`, `R=ε=1`, `d=4096·3⁵` gives budget 1. Budget 0 is covered. The proof (`exists_failure` in [LocalizedMonotoneLowerBound](../../LongTails/Proofs/LocalizedMonotoneLowerBound.lean)) even uses `N+1`.

**Upper bound.** Jiang–Yoon (Thm 5.1, per the companion note; not rechecked here) and the repository's [LazyAnchoredExtraProximal](../../LongTails/Theorems/LazyAnchoredExtraProximal.lean), taken with `m=1` and `D=R`, use `K + 2¹⁶K(log₂K+1)²` calls, where `K=⌈(LR²/ε)^{2/5}⌉+1`. Its guarantee is an almost-sure residual bound, which implies the expected-residual criterion. The remaining gap is therefore `O(log²(LR²/ε))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jiang–Yoon, [arXiv:2609.30212v2](https://arxiv.org/abs/2609.30212v2) (v1 24 Sep, v2 8 Nov 2026), Thm 6.1; **prior**. Same global class, unconstrained queries, p-th-order jets; **deterministic algorithms only**. | `Ω((LR²/ε)^{2/5})` deterministic → `Ω((LR²/ε)^{2/5})` randomized | None: same order | Deterministic algorithms → randomized adaptive algorithms (instance chosen before the seed) | Deterministic residual → expected residual over the seed | Dimension `d ≥ 2N+1` → `d ≥ 4096(N+2)⁵`. The chain/gate construction is inherited. |
| Zhang–Wu–Zhang–Fang–Li–Lin, [arXiv:2609.13462v2](https://arxiv.org/abs/2609.13462v2) (19 Oct 2026), Thm 11.3; **prior**. **Restriction:** monotone VI on a ball, with queries confined to the feasible ball. | `Ω((LD²/ε)^{2/5})` with probability ≥ 3/4 of failure → `Ω((LR²/ε)^{2/5})` in expectation | None: same order (on a ball, `D` and `R` are comparable up to a factor 2 only) | Bounded feasible queries and tangent residual → arbitrary queries in `ℝ^d` and global residual `‖F‖`. Their Remark 11.4 and §12 explicitly exclude this case. | Probability-of-failure statement → expected-residual statement. The latter is weaker: theirs implies an expectation failure up to constants, not conversely. | Dimension `O(N³log N)` → `O(N⁵)` |
| Garg–Kothari–Netrapalli–Sherif, [NeurIPS 2021, arXiv:2112.01118](https://arxiv.org/abs/2112.01118), Thm 1. **Restriction:** convex minimization (gradient fields), function-value accuracy. | `Ω̃((LR³/ε_f)^{2/7})`. Converting via `f−f* ≤ R‖∇f‖` needs a bounded output, so it gives at most `Ω̃((LR²/ε)^{2/7})` → `Ω((LR²/ε)^{2/5})` | Larger exponent, `2/7 → 2/5`, for the general monotone class only | Not a relaxation. The hard operators here are not gradients, so nothing new is proved for the convex subclass. | None | The classes are nested (gradients ⊂ monotone). The larger exponent comes from the larger class. |

**Standard-reduction check.** A randomized bound does not follow from Jiang–Yoon's deterministic resisting oracle without a hard distribution. Zhang et al.'s bounded-query instance does not extend directly to a global monotone `F` with the `‖F‖` residual, because an unconstrained algorithm can probe outside the ball. The new step closes that gap: compose the nonexpansive chain with a smooth radial contraction `P`, so that `γ(Id − G∘P)` stays monotone with a Lipschitz Jacobian, and prove a coercivity estimate that forces small-residual outputs into the region where `P` is the identity. This is a monotone-operator adaptation of the familiar radial-compression device for unbounded queries in randomized lower bounds (e.g. Carmon et al., "Lower bounds for finding stationary points I", 2017; not rechecked in detail). It is combined with a finite random coordinate embedding. Proof ancestry: Jiang–Yoon Lemmas 6.2–6.3 supply the chain and gates, and Jang–Ryu (arXiv:2607.05947) supplies earlier chain ideas. Neither gives the randomized global bound.

**Search coverage.** The search was run on 2026-11-14 over arXiv 2018–2026 higher-order VI, minimax and convex lower bounds. It covered 2609.30212, 2609.13462, 2609.28246 (randomized, but bounded feasible queries; saddle class), 2609.23557 (no lower bound) and Garg et al. Parts of the arXiv HTML were read only via summaries. Agarwal–Hazan (COLT 2018) and Carmon et al. were not reread. The theorem was committed 2026-11-14 21:54 UTC, after all of these versions. I found no later competing result. The companion note's citations and characterizations match what I could verify.

## Conclusion

**The rate is not new; what is new is that it now holds for randomized algorithms whose queries may go anywhere in `ℝ^d`.**

The `(LR²/ε)^{2/5}` lower bound for this exact global class was already proved for deterministic algorithms by Jiang–Yoon (Thm 6.1). Zhang et al. (Thm 11.3) had already proved it against randomized algorithms, but only when queries stay inside a bounded feasible ball. This theorem removes that bounded-query restriction for unconstrained monotone equations:

| | algorithms | queries | lower bound |
|---|---|---|---|
| Jiang–Yoon | deterministic | anywhere | `Ω((LR²/ε)^{2/5})` |
| Zhang et al. | randomized | in a ball | `Ω((LD²/ε)^{2/5})` |
| this result | randomized | anywhere | `Ω((LR²/ε)^{2/5})`, for `d ≳ (LR²/ε)²` |

The existing upper bound costs `O((LR²/ε)^{2/5} log²(LR²/ε))` calls, so the result settles randomized global complexity up to `log²` factors. The cost is a much larger dimension, polynomial of degree five in the budget rather than linear or cubic. The accuracy criterion is also weaker: failure in expectation rather than with constant probability.

The comparison shows the gap was real, and the coercivity step is a genuine, if modest, monotone-specific addition. The search did not turn up a prior result covering this case, but HTML access was partial. What can be claimed is that the known optimal exponent extends to randomized algorithms with unrestricted queries, using an adaptation of known radial-localization ideas. That is a modest completion of existing results, not a new rate.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
