# Novelty assessment: DistributedCurvatureNormalizedSimple

The [theorem](../../LongTails/Theorems/DistributedCurvatureNormalizedSimple.lean) shows the following for the event-driven star-network [algorithm](../../LongTails/Algorithms/DistributedNormalizedTraining.lean), which runs compressed normalized SGD with downlink model compression. It reaches `𝔼‖∇f(X)‖ ≤ ε` by a fixed deadline under `DistributedTemplate.law`, and almost-sure finite-event execution is also proved. The guarantee holds for every lower-bounded, L-smooth f on ℝᵈ with a Q-Lipschitz Hessian, given n workers with independent, IID, unbiased σ²-variance gradient streams ([setup](../../LongTails/Setups/DistributedHessianLipschitzNonconvex.lean)).

**Elapsed time.** Parameters:
- Δ is the initial gap, hᵢ is the per-query compute time and H = maxᵢ hᵢ.
- ℓ is per-packet latency and b is time per bit.
- d ≥ 0 is the dimension; the case d = 0 is handled separately.

Write A = 1+LΔ/ε². Then the time is

T = O( A·[ ℓ + H(1+σ²/(nε²)) + b(1+d/n^{1/3})·(log(e+A√d) + log(e+(d²A+d·min(σ²/ε²,n))/√n)) + d·b·log(e+A√d)·min(1,√(Qε)/L) + √(dHσ²b·log(e+(d²A+d·min(σ²/ε²,n))/√n)/(nε²)) ] ).

This is the Lean `budget` up to its constant 2³².

**Relation to the sibling theorem.** `budget_bounds` (in `Proofs/DistributedBudgetSimplification.lean`) proves T_orig ≤ T_simple ≤ 2048·T_orig against the sibling [DistributedCurvatureNormalized](../../LongTails/Theorems/DistributedCurvatureNormalized.lean). That sibling has the same algorithm, setup and proofs and was added in the same commit (44e283ff, 2026-11-18). The novelty question is therefore entirely about the shared guarantee.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Begunov–Tyurin, Inkheart SGD, [arXiv:2605.07795](https://arxiv.org/abs/2605.07795) (v1 8 May 2026, v2 19 Oct 2026), Thm 2.2 / eq. (7) with κ=τ; prior | Converted to ε here, with κ = s2w/w2s time per coordinate: `O(A·max{h,κ,dκ/n^{1/3},√(dσ²hκ/(nε²)),σ²h/(nε²)} + dκL_AΔ/ε²)`. Under L-smoothness alone, Prop 1.7 gives L_A = L. → Here: the same terms with κ replaced by b·log(·), plus the latency term Aℓ, and the downlink term replaced by `d·b·log·A·min(1,√(Qε)/L)` ≈ `d·b·log·√QΔ/ε^{3/2}` | Downlink term shrinks by a factor of about L/(√(Qε)·log) when √(Qε) < L. Example with L,Q,Δ,σ,h,b fixed, d ≍ ε^{-7/4}, n ≍ ε^{-3/2}: ε^{-15/4} → ε^{-13/4}·log(1/ε) | Incomparable classes. Inkheart needs a small L_A (e.g. near-quadratic f); here Q-Lipschitz Hessians are covered even when L_A ≍ L | None verified (output-selection rule of Inkheart not checked) | Criterion weakened: E‖∇f‖² ≤ ε² → E‖∇f‖ ≤ ε (Inkheart's criterion implies this one). Extra Hessian-Lipschitz assumption. Log bit-width factors instead of real-valued coordinates. Loses when L_A ≲ √(Qε), e.g. f = quadratic + a cos(ωx) with aω² small and aω³ large |
| Repo [DistributedCurvatureNormalized](../../LongTails/Theorems/DistributedCurvatureNormalized.lean) (same commit) | T_orig → T_simple ≤ 2048·T_orig | None: same order | None | None | Constant up to 2048 times looser; shorter formula |
| Repo [DistributedBatchedSgd](../../LongTails/Theorems/DistributedBatchedSgd.lean) (2026-11-17), smooth-only | In ε units: `A·[minᵢ(hᵢ + (1+σ²/ε²)/Σ_{h_j≤h_i}h_j⁻¹) + ℓ + b·d·log]` → T | The b·d·log full-vector cost becomes `b·log·(1+d/n^{1/3}+d·min(1,√(Qε)/L))`. Gain when n ≫ 1 and √(Qε) ≪ L | None (narrower class) | None | Requires Q. Uses max h instead of the Rennala-type heterogeneous-speed term (worse with stragglers). Weaker criterion |

**Reduction check.** I checked whether a localized Inkheart gives this term. Prop 1.9 bounds L_A by the Hessian dispersion D, but Q-Lipschitzness only gives D ≤ 2L globally. A trajectory-radius bound r ≲ Δ/ε gives L_A ≲ QΔ/ε, which yields dκQΔ²/ε³. That is worse than dκ√QΔ/ε^{3/2} whenever √QΔ > ε^{3/2}. Squaring the Taylor remainder inside an L_A-style analysis needs fourth moments of the model discrepancy.

**Mechanism.** The proof bounds the conditional *norm* error ‖n⁻¹Σᵢ∇f(x+eᵢ)−∇f(x)‖ ≤ L‖ē‖ + Q·n⁻¹Σ‖eᵢ‖², using fresh, independent downlink errors, and feeds it into normalized descent. As far as I can find, this is a genuinely new combination.

**Proof ancestry.** Each ingredient is known:
- normalized SGD with second-order smoothness (Cutkosky–Mehta, ICML 2020, Thm 3);
- Rand-K bidirectional compression and the L_A framework (Gruntkowska–Tyurin–Richtárik, NeurIPS 2024; Inkheart).

They supply the descent and compression-variance tools, not this curvature term. Serial NIGT (ε^{-7/2}) and the note's lazy-cubic screen (exponent 29/8) are slower in the example regime. That cubic comparison is the note's own reduction and I did not re-derive it.

**Lower bound.** Tyurin's lower bound ([arXiv:2506.23836](https://arxiv.org/abs/2506.23836), ICLR 2026) contains a dκLΔ/ε term for L-smooth f under random sparsification. That does not contradict this result: its scaled hard instance presumably has Q ≳ L²/ε (I did not check this), and at that point the min(1,√(Qε)/L) factor equals 1. Nothing here proves optimality.

**Search coverage (2026-11-18).**
- Covered: arXiv/web searches on bidirectional and downlink compression with Hessian regularity, the MARINA-P/EF21-P/CORE/Inkheart/Tyurin time-complexity line, and the companion notes.
- Partly read: I read Inkheart v2's introduction and Section 1 verbatim, but not the proof body of Thm 2.2. I did not open the CORE theorems.
- Not confirmed: Inkheart's NeurIPS 2026 status and its expected-vs-fixed-time convention (both asserted by the note).
- Consistency with the notes: the companion note's claim of "no additional novelty" for this file is accurate. Its Inkheart comparison matches what I verified.

## Conclusion

**The selected file adds nothing beyond its same-commit sibling; the guarantee they share does give a regime-specific polynomial speedup over the strongest prior bound, Inkheart SGD.**

Under L-smoothness alone, Inkheart pays a downlink cost of `d·κ·LΔ/ε²`. With an additional Q-Lipschitz Hessian, the shared guarantee pays only

  `d·b·log(·)·√Q·Δ/ε^{3/2}`  (when √(Qε) < L),

and the remaining terms match Inkheart's up to bit-width logarithms. In the example regime (d ≍ ε^{-7/4}, n ≍ ε^{-3/2}, other parameters fixed), the elapsed time drops from ε^{-15/4} to ε^{-13/4}·log(1/ε).

The gain has limits:
- it requires Hessian regularity;
- it uses the weaker accuracy criterion E‖∇f‖ ≤ ε;
- it loses to Inkheart on functions whose L_A is already below √(Qε).

The two classes are incomparable. A naive localization of Inkheart's L_A fails to reproduce the gain.

Priority is less certain. Inkheart v2 appeared only in October 2026, and I did not find earlier work using Hessian Lipschitzness to cut downlink cost, but searches cannot rule out concurrent work. What can actually be claimed is a curvature-sensitive downlink elapsed-time bound for distributed nonconvex SGD. The "Simple" theorem itself contributes only a readable, constant-equivalent restatement of that bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
