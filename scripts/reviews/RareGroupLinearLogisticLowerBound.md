# Novelty assessment: RareGroupLinearLogisticLowerBound

For a fixed linearly separable two-group sample and a fixed start `w₀`, [the theorem](../../LongTails/Theorems/RareGroupLinearLogisticLowerBound.lean) proves the following. Take any constant step `h > 0` in full-gradient logistic GD that stops at its first fit ([setup and `family`](../../LongTails/Setups/RareGroupLinearLogistic.lean), [proof](../../LongTails/Proofs/RareGroupLinearLogistic.lean)). Then no budget `b ≤ B` yields an output that strictly classifies every row.

**Proved budget.** Notation:

- `xᵢ` are the signed rows. The common group has total weight `1−p` and the rare group weight `p`, with `0<p<1`.
- `L` is the weighted mean logistic loss.
- `v` is a certificate with three properties: every strict separator `w` has `⟨v,w⟩>0`; `⟨v,w₀⟩ ≤ 0`; and `⟨v,xᵢ⟩ ≤ 0` for every common row.
- `C = mean over rare rows of max(⟨v,xⱼ⟩,0)`, assumed positive.

The bound is

  `B = max(0, ⌊1 + ⟨v,∇L(w₀)⟩/(pC)⌋)`.

So the first fit needs at least `B+1` gradient calls, for every `h>0`. With fixed geometry and `⟨v,∇L(w₀)⟩ ≥ a > 0`, this is `Ω(a/(pC))`. The instance is the given data: `admissible` forces `D = p.data`. It is a certificate-based trajectory bound for one method, not a lower bound for a problem class or an oracle model.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Crawshaw–Liu, *Tight Bounds for Logistic Regression with Large Stepsize GD in Low Dimension*, COLT 2026 (PMLR 336), [arXiv:2602.12471](https://arxiv.org/abs/2602.12471) v1 Feb 2026, Lemma 3.1 / App. B. Prior. Same algorithm (constant-step GD from `w₀=0`). | Hard set: `x₁=(γ,−γ)` (rare, `p=1/n`), `xᵢ=(γ,√(1−γ²))`. Separation needs `> n/(16γ)` steps, for `η ≥ max(n, 32γ⁻² log(3/γ))`. → With `v=x₁`, `C=2γ²`: `B+1 = ⌊1/2 + (n−1)(√(1−γ²)/γ − 1)/4⌋ + 1 ≈ n/(4γ)`, for all `h>0` | Constant factor only (≈4×), same order `Θ(n/γ)` | One explicit dataset → any weighted separable sample with a certificate `v`. Restriction `η ≥ η₁` → any `h>0`. Their recursion (eqs. 167–178) never uses `η ≥ η₁`, so the step-range extension is immediate. | None (same first-fit criterion and output) | Needs a certificate `v` with every common row nonpositive. Lacks their `Ω(1/γ²)` transition-time term (Lemma 3.2). No upper bound in this general setting. |
| Zhang–Wu–Lin–Bartlett, [arXiv:2504.04105](https://arxiv.org/abs/2504.04105) v2 Apr 2025, Thm 3.2. Applies to any first-order batch method, a broader algorithm class. | `Ω(min(log n, 1/γ²))` on a constructed dataset → `Ω(1/(pC))` for constant-step GD only | Not comparable: different algorithm classes and datasets. Adaptive-step GD separates in `O(1/γ²)` (their Thm 2.1), so this bound does not show that the problem is hard. | None | None | Covers only constant-step GD |
| Tyurin, ICML 2026, [PMLR v306](https://proceedings.mlr.press/v306/tyurin26a.html) / [arXiv:2512.11587](https://arxiv.org/abs/2512.11587), Thm 5.2. Batch perceptron, i.e. the GD limit `η→∞`. | `Ω(d/μ)` on two samples → applied to that dataset, either choice of rare row gives `B ≤ 1` | Not comparable. The rare-weight certificate does not capture the dimension mechanism. | Incomparable mechanisms | None | Does not explain the paper's `Ω(d)` separation |

**Reduction check and proof ancestry.** The proof bounds the projection onto `v`: one exact first step, then an increment of at most `hpC` per step because common votes are nonpositive. This is the Crawshaw–Liu Lemma 3.1 recursion with `x₁` replaced by `v` and `1/n` replaced by `p`. They describe their construction as a slight generalization of Tyurin's (2025) perceptron lower bound. No new technical mechanism is needed. The Lean execution bookkeeping is formalization, not mathematics.

**Search coverage.** On 2026-11-27 I searched for constant- and large-step GD lower bounds for separable logistic regression. I read the relevant statements in Crawshaw–Liu (Lemma 3.1 and its proof), Zhang et al. (Thm 3.2 statement via the HTML text), and Tyurin 2026 (Thm 5.2 statement; Appendix E not read). I did not read Tyurin's 2025 arXiv paper (2412.08424) directly. The theorem was introduced in commit `72242035` on 2026-11-27, after all three papers.

The companion note compares only with Tyurin §5 and PR #253. It does not cite Crawshaw–Liu, which already contains this argument. Its CIFAR counts (254 vs 41) are numerical claims outside the Lean theorem, and I did not rerun them.

**Conclusion**

**No: this is a generalization of an existing argument, not a new or stronger lower bound.**

The closest baseline is Crawshaw–Liu (COLT 2026), Lemma 3.1. They give an explicit dataset with one rare point among `n` on which constant-step GD needs more than `n/(16γ)` steps to separate. Their proof is the same projection recursion: one negative first step, then bounded progress per step.

| | Bound on that dataset | Step range |
|---|---|---|
| Crawshaw–Liu | `> n/(16γ)` | `η ≥ max(n, 32γ⁻² log(3/γ))` |
| This theorem | `≈ n/(4γ)` | every `h > 0` |

The new statement replaces the single dataset with any weighted separable sample that admits a certificate `v`. It also removes a step-size floor that their argument never actually used. On their dataset the gain is a constant factor of about 4. The `1/p` scaling is their `n` dependence rewritten in terms of group weight.

The bound covers only constant-step GD on given data. Adaptive-step GD separates in `O(1/γ²)` steps (Zhang et al.), so it says nothing about problem hardness. Its certificate also misses Tyurin's dimension-based `Ω(d)` example.

What can be claimed is a checkable, data-dependent certificate that generalizes Crawshaw–Liu's rare-point bound to every constant step, plus a Lean formalization of it.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**: Crawshaw–Liu's proof was read directly. The Tyurin 2025 perceptron bound was checked only through their description of it.
