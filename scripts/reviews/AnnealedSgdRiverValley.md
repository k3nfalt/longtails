# Novelty assessment: AnnealedSgdRiverValley

[`result`](../../LongTails/Theorems/AnnealedSgdRiverValley.lean) proves the following for objectives in [`RiverValleyHillNoise.spec`](../../LongTails/Setups/RiverValleyHillNoise.lean). The objective is f(x) = h(Qx) + ½⟨A(Px−φ(Qx)), Px−φ(Qx)⟩, where the split K ⊕ Kᗮ is unknown, h is nonconvex, φ is a curved river, and A is a quadratic hill operator. The method is [`StepDecaySgd`](../../LongTails/Algorithms/StepDecaySgd.lean): it runs τ ~ Unif{0..T} steps with ηs, then K steps with ηc, and outputs the last iterate. This output satisfies **E‖∇f(x_out)‖ ≤ ε** within the budget below. Calls are IID unbiased stochastic gradients.

**Parameters.**
- Lh, ρh: Lipschitz constants of ∇h and ∇²h.
- G: bound on ‖∇h‖.
- LJ, ρJ: Lipschitz constants of Jφ and DJ.
- Γ: turning rate, with ‖A Jφ Q‖ ≤ Γμ.
- μ, Lv: spectral bounds of A on K.
- σu², σv²: river- and hill-block noise variances.
- Δ: bound on the initial objective gap.

From the `budget` line (`T + K ≤ budget`):

  O( LvΔ/ε² + (Δ/ε⁴)·[Lhσu² + (ΓLh+LJG)(Γ+(ΓLh+LJG)/μ)(σu²+σv²) + (ΓLh+LJG)σuσv
     + (GρJ+LJLh+Γρh+GLJ²)σu((σu²+σv²)/Lv + σu²/μ + ΓGσu/Lv) + LJ²σu⁴/Lv]
     + log²(3 + Lv²/μ² + Lv·W/(μ³ε²))·(Lv/μ + W/(μ²ε²)) ),

where W = Gρhσu² + μ²σu² + Lv²σv² + LvLJ²σu⁴/μ.

The exact log argument has μ³(Lvε² + 8·[ε⁻⁴ bracket]) in its denominator, which makes it ε-free when the bracket is positive. Above it is loosened to μ³ε²Lv. The bound requires the following (`valid`):
- μ ≤ Lv;
- Γ ≤ 1/16;
- 64(ΓLh+2LJG) ≤ μ;
- 64(2GρJ+2LJLh+Γρh+GLJ²)σu ≤ μLv;
- 32·Lh·log R ≤ μ.

The tuning (ηs, ηc, T, K) uses these public constants but not K, φ, or A.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ghadimi–Lan, [SIAM J. Optim. 23(4), 2013](https://arxiv.org/abs/1309.5549), Thm 2.1/Cor 2.2 (randomized SGD). **Special case only:** affine river LJ=ρJ=0, where f is L-smooth with Lv ≤ L ≤ Lh+(1+Γ)²Lv ≤ 1.2Lv under `valid`. | O(LvΔ/ε² + LvΔ(σu²+σv²)/ε⁴) → O(LvΔ/ε² + Δ[Lhσu² + Γ²Lh(σu²+σv²) + ΓLhσuσv + Γρhσu((σu²+σv²)/Lv+σu²/μ+ΓGσu/Lv)]/ε⁴ + log²R·(Lv/μ + (Gρhσu²+μ²σu²+Lv²σv²)/(μ²ε²))) | With σ := max(σu,σv) and L′ := Lh+Γρhσ/μ+Γ²ρhG/Lv, the speedup is ≈ min{σ²/ε², Lv/L′, μ²Δ/(Lv ε² log²R)}. The coefficient Lv on the ε⁻⁴ noise term is reduced to the river-side quantity L′. **Worse** when Lv ε² log²R > μ²Δ (cooldown term dominates); **same order** when σ ≲ ε. | Generic L-smooth class → river-valley class. On the overlap, nothing is relaxed. | Output: GL gives E‖∇f‖² ≤ ε² for a random iterate. Here it is only E‖∇f‖ ≤ ε for the last iterate of a randomly stopped two-phase run. Both need Lv/L, σ, Δ for tuning. | Quadratic hills with constant A and a fixed subspace K; ‖∇h‖ ≤ G; C^{2,1} h; valley conditions Lh ≲ μ/log R and 64c′σu ≤ μLv; κv=Lv/μ and log²R appear in the cooldown. |
| Li–Qian–Tian–Rakhlin–Jadbabaie, [NeurIPS 2023 / arXiv 2306.01264](https://arxiv.org/abs/2306.01264), Thm 5.3 (SGD under sub-quadratic ℓ-smoothness). Covers the full curved class. My derivation (not formalized) gives ‖∇²f‖ ≲ Lh+(1+Γ)²Lv+LJ‖∇f‖. | T ≥ max{2ℓ(2G′)F/ε², 16G′²F²/ε⁴}, with F=8(Δ+σ²)/δ and G′ ≥ 2ℓ(0)F ≥ 2LvF. The guarantee is that, with probability 1−δ, the average of ‖∇f(x_t)‖² is ≤ ε². → the bound above | **Not comparable:** different criterion (high-probability average vs. expected norm of one output). Its leading term carries at least Lv²(Δ+σ²)⁴/(δ⁴ε⁴), whereas here Lv is absent from the ε⁻⁴ term. | Curved river: both cover it. The class here is much narrower. | Expected norm of a single output vs. high-probability average; there is no clean conversion either way. | Same structural restrictions as in the first row. |

**Not complexity baselines.**
- Wen et al., [ICLR 2025, arXiv 2410.05192](https://arxiv.org/abs/2410.05192), Thms 3.4–3.5: SGD loss-tracking for a straight river with noise only in the hill directions; no stationarity rate.
- Lu et al., [arXiv 2609.30957](https://arxiv.org/abs/2609.30957) (25 Sep 2026, before this result): deterministic GD/momentum tracking only. Its Appendix B leaves SGD to future work.
- Song et al., [NeurIPS 2025, arXiv 2507.09846](https://arxiv.org/abs/2507.09846): deterministic stability thresholds.
- Two-timescale and bilevel SA methods need the split and separate step sizes.

**Standard-reduction check.**
- When Γ = 0, the river is straight and axis-aligned. The problem then separates into a composition of two known results: Ghadimi–Lan on h, and step-decay last-iterate SGD on a strongly convex quadratic (Ge et al., NeurIPS 2019).
- For Γ > 0, even an affine φ is a *shear*. That is not an orthogonal change of variables, so SGD becomes coupled preconditioned SGD and no reduction applies.
- The new mechanism is the corrected potential h + ⟨m,w⟩ + λ‖w‖² with m = (I+JJᵀ)⁻¹Ja, plus a cooldown free of the hill condition number κv. It shows that the noise transmitted from the hills into the river costs only Γ²Lh·σv², not Lv·σv².
- **Proof ancestry:** Ghadimi–Lan descent, Ge et al.'s step decay, and Poisson-type corrections from two-timescale SA.
- **Lower bounds:**
  - The note's constant-step lower bound (Ω(LvΔσv²/ε⁴) on a separable instance) is a sound-looking paper argument. I checked it only informally, and it concerns that method, not the problem class.
  - A matching class lower bound via Arjevani et al. (Math. Program. 2023), embedded in h, is not checked; the G and ρh constraints are the open point.

**Search coverage (2026-10-20).** I searched arXiv, ICLR/NeurIPS pages, and Google-indexed work on river-valley/WSD theory, step decay, anisotropic noise, and generalized smoothness. The result was introduced in commit `3a534d1` (2026-10-20).
- **Not read:** Liu–Hu (arXiv 2507.04206) beyond its snippet, and Schaipp et al. (ICML 2025).
- **Note mismatch:** the companion note says no prior theory applies when the river is curved. Li et al. Thm 5.3 does apply there, although with weaker constants and a different criterion.

## Conclusion

**Yes: on river-valley objectives, the proved SGD complexity removes the hill curvature Lv from the dominant ε⁻⁴ noise term.**

The strongest checked baseline is generic smooth SGD (Ghadimi–Lan). It applies only when the river is straight but may be tilted (an affine φ) and pays Lv per unit of noise:

| | ε⁻⁴ noise term | extra terms |
|---|---|---|
| Ghadimi–Lan | LvΔσ²/ε⁴ | LvΔ/ε² |
| this result | (Lh + Γρhσ/μ + …)Δσ²/ε⁴ | LvΔ/ε² + log²R·Lv²σv²/(μ²ε²) |

The gain is roughly a factor of Lv/Lh when σ ≫ ε and ε² ≪ μ²Δ/(Lv log²R). When ε is larger than that, the cooldown term makes this result worse. The curved-river case is newly covered at this rate; the only generic baseline there (generalized-smoothness SGD) has a different criterion and still pays Lv.

The class is stylized: hills are exactly quadratic with a fixed subspace, the river gradient is bounded, and four regime conditions must hold. The straight, axis-aligned case is a routine composition of known results. For a turning river, no reduction was found, and the literature search found no prior oracle-complexity result for SGD on this class. That supports priority, but it does not prove it. Optimality is unproved.

What can be claimed is a new expected-stationarity guarantee for annealed SGD on curved river valleys, with an Lv/Lh-type gain over generic SGD theory in an explicit small-ε, high-noise regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
