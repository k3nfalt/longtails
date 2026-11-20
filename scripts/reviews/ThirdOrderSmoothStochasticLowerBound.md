# Novelty assessment: ThirdOrderSmoothStochasticLowerBound

[Theorem](../../LongTails/Theorems/ThirdOrderSmoothStochasticLowerBound.lean) · [setup](../../LongTails/Setups/HighDimensionalStochasticThirdOrderSmoothNonconvex.lean) (predicates from [StochasticThirdOrderSmoothNonconvex](../../LongTails/Setups/StochasticThirdOrderSmoothNonconvex.lean)) · hard instance in [ThirdOrderLowerBound](../../LongTails/Proofs/ThirdOrderLowerBound.lean) and [ThirdOrderLowerAssembly](../../LongTails/Proofs/ThirdOrderLowerAssembly.lean).

The theorem says this. Take any randomized algorithm that may query anywhere and gets single-sample, unbiased stochastic gradients with variance at most σ². If it makes `b ≤ budget` calls, there is a C³ instance on ℝᵈ on which it fails to reach `E‖∇f(x̂)‖ ≤ ε`. The instance has L₁-, L₂- and L₃-Lipschitz gradient, Hessian and third derivative, and initial gap at most Δ. It may depend on the algorithm and on `b`, but not on the seed.

**Proved bound.** Δ is the initial gap, L₁, L₂, L₃ are the Lipschitz constants of ∇f, ∇²f and ∇³f, σ² is the variance and ε the target. Then

  N_lower = ⌊ (Δ/ε) · min{L₁/ε, √(L₂/ε), (L₃/ε)^{1/3}} · (1 + σ²/ε²) / 2¹⁷⁴ ⌋ = Ω( (Δ/ε)(1 + σ²/ε²) · min{L₁/ε, √(L₂/ε), (L₃/ε)^{1/3}} ).

This holds under two validity conditions:
- Δ·min{…} ≥ 2⁷⁰ε.
- d ≥ 2¹⁴⁰(1 + (Δ/ε)·min{…}·(1 + σ²/ε²))⁴, which forces d ≥ 2⁴²⁰.

The bound is nonzero only when (Δ/ε)·min{…}·(1 + σ²/ε²) ≥ 2¹⁷⁴. For small ε the noise term is Ω(Δσ²L₃^{1/3}ε^{−10/3}).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani–Carmon–Duchi–Foster–Sekhari–Sridharan, [COLT 2020](https://proceedings.mlr.press/v125/arjevani20a.html), Thm 3 ([arXiv:2006.13476v1](https://arxiv.org/abs/2006.13476)), with p = 3 and σ₂ = σ₃ = ∞. **Restriction:** zero-respecting algorithms only. | Ω((Δσ²/ε³)·min{L₁/ε, √(L₂/ε), (L₃/ε)^{1/3}}) for ε ≤ O(σ) → Ω((Δ/ε)(1 + σ²/ε²)·min{…}) | None: same order when ε ≲ σ. The extra Δ·min{…}/ε term for σ < ε is weak; see row 3. | Algorithm class: zero-respecting → all randomized algorithms with arbitrary adaptive queries. The problem class is the same. | None. Their criterion is constant-probability failure, this one is expected-norm failure; the two convert into each other up to constants. | Dimension grows from Θ((Δ/ε)·min{…}) to ≥ 2¹⁴⁰((Δ/ε)·min{…}·(1 + σ²/ε²))⁴. Covers only p = 3 with a first-order oracle; theirs covers every p and stochastic higher-derivative oracles. Constant 2⁻¹⁷⁴. Footnote 3 of that paper already says the bounds "extend to general randomized algorithms via similar arguments to Arjevani et al. (2019a)". |
| Arjevani–Carmon–Duchi–Foster–Srebro–Woodworth, [Math. Program. 2023](https://doi.org/10.1007/s10107-022-01822-7), Thm 3 ([arXiv:1912.02365v2](https://arxiv.org/abs/1912.02365)). **Restriction:** class F₁; the hard instance comes with no L₂ or L₃ bounds. | Ω(ΔL₁σ²/ε⁴), randomized algorithms, d = Õ(Δ²L₁²σ²ε⁻⁶) → the bound above | None where min{…} = L₁/ε. Elsewhere the two are not comparable, because their instances do not satisfy the L₂ and L₃ constraints. | F₁ → F₃: the bound now holds when Hessian and third-derivative Lipschitz constants are imposed (exponent 10/3 instead of 4). | None | Much larger dimension. Their §6 lists higher-order smoothness as open and says "our techniques extend to higher order derivatives and smoothness." |
| Carmon–Duchi–Hinder–Sidford, Lower Bounds II ([arXiv:1711.00841](https://arxiv.org/abs/1711.00841), Math. Program. 2021). **Restriction:** σ = 0 and deterministic algorithms. | Ω(ε^{−8/5}) for arbitrarily smooth f → Ω(Δ·L₃^{1/3}ε^{−4/3}) when σ = 0 | Worse when σ = 0, by a polynomial factor in 1/ε. The algorithm classes also differ (deterministic vs randomized). | None | None | The noiseless regime is not addressed in any competitive way. |

**Standard-reduction check.** The bound follows by combining known pieces:
- The COLT 2020 scaling λ ≍ max{ε/L₁, √(ε/L₂), (ε/L₃)^{1/3}}.
- A probabilistic zero-chain oracle (Arjevani et al. 2019, §3).
- Random-embedding hiding with a radial cutoff (Carmon et al. 2017; Arjevani et al. 2019, §4).

The only step that is not mere substitution is showing that the cut-off chain has a third derivative that is Lipschitz with constants independent of n and d. That is where the `ThirdOrderChainLipschitz` and `ThirdOrderJetDifference` estimates come in. Smoothness of every order for chains of this type is already standard in Carmon et al., so I see no new lower-bound mechanism. The companion note agrees ("closing a known gap with known tools"). The note does not cite footnote 3, which makes the randomized extension look more open than the source presents it. Read alone, the Section 3.2 remark ("we believe … we do not pursue it here") agrees with the note.

**Search coverage (2026-11-20).** Sources checked:
- arXiv and PMLR versions of Arjevani et al. 2019 and 2020.
- Carmon et al. Lower Bounds II.
- Web searches for later randomized stochastic lower bounds under higher-order smoothness (only (L₀,L₁), PL and zeroth-order variants turned up).

The PDFs could not be read as text. Arjevani 2020 was read in HTML only through §4.1, so its appendix proofs and the formal zero-respecting definition were not checked. The theorem entered the repository in commit 84c39ef4 (2026-11-20). I found no earlier written proof for randomized algorithms, but that does not prove none exists.

## Conclusion

**No rate improves; the result proves for all randomized algorithms a lower bound that was already known for zero-respecting ones and was said to extend.**

The strongest baseline is Arjevani et al. (COLT 2020), Theorem 3 with p = 3, which already gives the same order:

  Ω( (Δσ²/ε³) · min{L₁/ε, √(L₂/ε), (L₃/ε)^{1/3}} ),  i.e. Ω(Δσ²L₃^{1/3}ε^{−10/3}) for small ε.

The new formal statement covers algorithms that are not zero-respecting. That is a real widening of the algorithm class, and it makes the companion upper bound tight up to constants in the noise-dominated regime, without logarithms. The price is a dimension of at least 2⁴²⁰ and a 2⁻¹⁷⁴ constant, and the noiseless term is weaker than known deterministic first-order lower bounds.

The comparison shows the result is correct in kind but not stronger in order. The literature search does not give it clear priority either: the original authors stated in a footnote that the randomized extension follows from known arguments. The proof uses exactly those arguments, plus a check that third derivatives stay bounded. What can be claimed is a complete, machine-checked proof of this randomized p = 3 case, which closes a gap that was openly acknowledged but treated as routine.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
