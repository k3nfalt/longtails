# Novelty assessment: HighDimensionalConstrainedQuasarLowerBound

[`result`](../../LongTails/Theorems/HighDimensionalConstrainedQuasarLowerBound.lean) proves that every randomized algorithm fails the high-probability accuracy criterion of [the setup](../../LongTails/Setups/HighDimensionalConstrainedQuasar.lean) on some admissible instance when it uses at most `B` calls on each channel. The setup's instance and success predicates are those of [StochasticConstrainedQuasar](../../LongTails/Setups/StochasticConstrainedQuasar.lean). There is no algorithm restriction, and the hard instances are in [QuasarLowerAssembly](../../LongTails/Proofs/QuasarLowerAssembly.lean).

**Proved necessary budget.** The bound counts calls per channel:

$$
\Omega\!\Big(\tfrac{1}{\gamma}\sqrt{LD^2/\varepsilon}+\tfrac{\sigma^2D^2\log(1/\delta)}{\gamma^2\varepsilon^2}\Big),
\qquad
B=\Big\lfloor \tfrac{\sqrt{LD^2/\varepsilon}}{10^4\gamma}+\tfrac{\sigma^2D^2\log(1/\delta)}{8192\gamma^2\varepsilon^2}\Big\rfloor .
$$

**Parameters.**
- **Objective and feasible set.** `L` is the gradient-Lipschitz constant on `X`, and `D` is the diameter of the compact convex set `X`. The objective is γ-quasar-convex with respect to the constrained minimizer, with `0<γ≤1`.
- **Accuracy and oracles.** `σ²` bounds the variance of the unbiased gradient oracle, and the second oracle channel is an exact projection onto `X`. Success means `P(x̂∈X, f(x̂)−f*≤ε) ≥ 1−δ`.

**Required regime (`valid`).**
- Dimension `d ≥ 2³⁴(B+1)⁵`, the oracle seed space is `Bool`, and `LD²/ε ≥ 10⁸`.
- `δ ≤ 1/4`, and either `σ=0` or `σ ≥ 64γε/D`.
- Gradient replies are constrained only on `X`. The hard oracle returns `0` for any query outside `X`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Hinder–Sidford–Sohoni, [arXiv:1906.11985v3](https://arxiv.org/abs/1906.11985), Thm. 3 (COLT 2020) | Ω(γ⁻¹√(LR²/ε)) → Ω(γ⁻¹√(LD²/ε)) in the deterministic term | None: same order. Their unconstrained bound transfers to a ball of diameter 2R, because projections preserve zero-respecting spans. | Lower bound for deterministic first-order methods → lower bound for every randomized algorithm | None | Requires polynomially large dimension. Holds only in the constrained model, where queries outside `X` reveal nothing, so it gives no randomized bound for their unconstrained class. The new information is only the factor 1/γ for γ<1/100; for γ≥1/100 the convex chain is used. |
| Saad–Lee–Orabona, [arXiv:2502.14060v2](https://arxiv.org/abs/2502.14060), Thm. 3.4 (COLT 2025, PMLR 291) | Ω(σ²D²/(γ²ε² log(2/γ))) for expected gap → Ω(σ²D² log(1/δ)/(γ²ε²)) for high-probability success | Gains a factor log(2/γ)·log(1/δ), but under a different criterion | None. Both use smooth quasar-convex objectives on a ball with unbiased bounded-variance noise and randomized algorithms. | Expected gap → probability ≥1−δ. The criteria are incomparable: neither lower bound implies the other without a bounded gap. | Excludes the band 0<σ<64γε/D. Requires δ≤1/4 and much larger dimension than their d ≥ log_{16/15}(4/γ²). |

**Standard reductions and mechanism.**
- *Deterministic term.* The randomized version does not follow verbatim from Carmon–Duchi–Hinder–Sidford's hidden-coordinate technique ([arXiv:1710.11606](https://arxiv.org/abs/1710.11606)), because Hinder–Sidford–Sohoni's chain is not a robust zero-chain. The new step is Lemma Q (`quasar_normalized`), a dead-zone, flat-bottomed variant of their chain that is proved quasar-convex. I did not check whether a random-rotation argument in the style of Woodworth–Srebro could randomize their original chain directly.
- *What the constrained model contributes.* Answering queries outside `X` with zero removes the large-norm handling that unconstrained randomized lower bounds need.
- *Noise term.* This is a routine rare-revelation argument. It uses the observation that quasar wells can have far-field gradients of order γε/D.
- *Proof ancestry.* Hinder–Sidford–Sohoni (Lemma 7 case structure) and Carmon et al. (counting) supply the tools, not the result.

**Search coverage.** On 2026-11-14 I searched for randomized and high-probability lower bounds for quasar-convex and star-convex optimization.
- **Checked.** I read the theorem statements of Hinder–Sidford–Sohoni and Saad–Lee–Orabona. For Martínez-Rubio, [arXiv:2510.01943v3](https://arxiv.org/abs/2510.01943) (constrained upper bound Õ(1/(γ√ε)), preprint), I could only read the abstract; its body may contain lower-bound remarks.
- **Not re-read.** I did not re-read Woodworth–Srebro or the folklore convex high-probability bounds at γ=1.
- **Introduction and checks.** The result entered the repository in commit `fd252a20` (2026-11-14). The companion note's citations match the statements above. I did not run builds or axiom audits.

## Conclusion

**The rate is not new; the novelty is extending the known 1/γ lower bound from deterministic to randomized algorithms, plus a sharper high-probability noise term.**

The strongest prior baseline is Hinder–Sidford–Sohoni's Theorem 3, which holds only for deterministic methods. The comparison:

| | deterministic term | noise term |
|---|---|---|
| before | Ω(γ⁻¹√(LR²/ε)), deterministic algorithms only | Ω(σ²D²/(γ²ε² log(2/γ))) for expected gap (Saad–Lee–Orabona) |
| this result | Ω(γ⁻¹√(LD²/ε)), any randomized algorithm | Ω(σ²D² log(1/δ)/(γ²ε²)) for probability ≥1−δ |

Together with the companion upper bound, this determines the randomized complexity of constrained quasar-convex optimization up to factors log(1/δ)·log²(LD²/(γ²ε)).

The comparison establishes a strictly larger algorithm class at the same order. It does not give a better necessary-call exponent. The gain is limited for concrete reasons:
- **Only small γ is new.** The 1/γ factor is new only for γ<1/100; for larger γ the bound reduces to the known convex randomized bound.
- **Narrow model.** It holds only in a constrained model where queries outside `X` are uninformative, and it needs dimension of order B⁵.
- **Routine noise term.** The noise-term gain is a logarithmic sharpening under a different criterion, obtained by a routine argument.

My search found no prior randomized quasar-convex lower bound, but that does not prove priority, and the abstract-only check of Martínez-Rubio could still change it. What can be claimed: the first randomized, high-probability lower bound I could locate for constrained quasar-convex optimization that matches the companion upper bound Õ(γ⁻¹√(LD²/ε) + σ²D²/(γ²ε²)) up to logarithms, obtained through a new robust quasar chain.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
