# Novelty assessment: CoupledMinimaxCappedKkt

[`result`](../../LongTails/Theorems/CoupledMinimaxCappedKkt.lean) proves the following for min over x∈X of max over y∈Y with c(x,y)≤0 of f(x,y), where f is smooth and μ-strongly concave in y, c is convex in y, X and Y are compact, and a uniform qualification holds on the violated constraints only ([setup](../../LongTails/Setups/CoupledStronglyConcaveMinimax.lean)). The deterministic [algorithm](../../LongTails/Algorithms/CoupledMinimax.lean) returns a point (x,y,λ) with λ≥0 satisfying ε-KKT: ‖[c]₊‖≤ε, Σ|λᵢcᵢ|≤ε, and residuals of x- and y-stationarity at most ε. Its cost is the budget below, counted in complete oracle calls returning (f,∇f,c,J_c).

**Parameters.** L_f is the smoothness of f, L_J the Lipschitz constant of the Jacobian, and J, G_x, G_y, C bound ‖J_c‖, ‖∇ₓf‖, ‖∇_y f‖ and ‖c‖. D_X and D_Y are the diameters of X and Y, m is the number of constraints, and (δ,Z) are the qualification constants. The bound below is the proved Lean budget with constants suppressed:

$$
O\!\Big(\Big[1+\sqrt{\tfrac{1+\mu+L_f+(1+\frac{Z(G_y+1)}{\delta})L_J+J}{\mu}}\,
\log\!\Big(2+\tfrac{(1+\mu+L_f+(1+\frac{Z(G_y+1)}{\delta})L_J+J)\,D_Y\,(1+\sqrt m+\frac{Z(G_y+1)}{\delta})(1+\varepsilon)}{\varepsilon}\Big)\Big]
\cdot\Big[1+\tfrac{(1+\mu+L_f+(1+\frac{Z(G_y+1)}{\delta})L_J+J)^2\,(G_xD_X+G_yD_Y+(1+\frac{Z(G_y+1)}{\delta})C)\,(1+\sqrt m+\frac{Z(G_y+1)}{\delta})^2(1+\varepsilon)^2}{\mu\,\varepsilon^2}\Big]\Big).
$$

With the other parameters fixed this is O(ε⁻² log(1/ε)). For comparisons only, write M=1+Z(G_y+1)/δ, B=1+μ+L_f+ML_J+J (the smoothness), Δ=G_xD_X+G_yD_Y+MC, S=1+√m+M and κ=B/μ. The leading term is then κ^{3/2}·BΔS²/ε².

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| ALDER, [arXiv:2611.00691v1](https://arxiv.org/abs/2611.00691) (31 Oct 2026, preprint, before this result), Assumptions 1(A1–A4) and 2, Def. 3, Thm 16 | Penalty γ=C_aug/ε gives ℓ_ε≈L_f+(L_JC+JL_c)C_aug/ε, so O(1+ℓ_ε^{3/2}(f-range+G_x²+G_y²+D_Y²+C²)/(√μ ε²)) = O(ε^{-7/2}) for fixed constants → the bound above, O(ε⁻² log(1/ε)) | ε^{-7/2} → ε⁻² log(1/ε). The gain holds when ε^{3/2}·log(1/ε) ≲ μ·(L_JC+JL_c)^{3/2}C_aug^{3/2}/(B^{5/2}ΔS²), roughly ε ≪ μ^{2/3} with the rest fixed | None. The class is the same: (A4) is the identical violated-only uniform qualification with the same δ, Z | None. Both give a deterministic ε-KKT point in the same criterion | Worse μ-dependence: μ^{-3/2} versus ALDER's μ^{-1/2}, so the result loses when μ is small relative to ε^{3/2}. Nested loop versus single loop. The C_aug constants of Thm 16 were read from a page summary |
| Lu–Mei FAL, [arXiv:2512.22909v2](https://arxiv.org/abs/2512.22909) (Jan 2026; OMS), Assumptions 1, 3, 4, Thm 2 | O(ε^{-7/2} log(1/ε)) operations (Remark 6(ii)); its constants include √κ and κ² factors → O(ε⁻² log(1/ε)) | ε^{-7/2}→ε⁻² up to logs, for fixed constants and small ε | Uniform inner Slater (d_i(x,ŷ_x)≤−δ_d) → violated-only qualification. Slater implies it, with Z=D_Y and d=ŷ_x−y by convexity. Paired equality-type constraints become covered | None | Applies only to FAL's specialization with no outer constraints and p, q indicators. FAL additionally handles outer nonlinear constraints c(x)≤0 and prox-friendly composite terms |
| Tsaknakis–Hong–Zhang ([SIOPT 2023](https://arxiv.org/abs/2110.11210)) and Tsaknakis–Khanduri–Hong–Zhang (JOTA 2026). Special case: linear or separable coupling with Slater | ε⁻²-type rates on that subclass → same ε order | None on the overlap | Linear or structured coupling → general nonlinear c, convex in y | Not checked | Narrower baseline class, so it is not a direct competitor |

**Standard-reduction check.** Under the cap M=1+2Z(G_y+1)/δ, min over λ in {λ≥0, Σλ≤M} of −λᵀc is an exact ℓ∞ penalty. The problem becomes a nonconvex–strongly-concave (NC-SC) minimax over (x,λ)∈X×Λ_M against y∈Y, so any NC-SC solver applies. The step that is not off the shelf is the quantitative transfer from capped stationarity to original feasibility and complementarity ([multiplier lemmas](../../LongTails/Proofs/CoupledMinimaxMultipliers.lean)). It uses the classical exact-penalty direction argument, giving δM≤Z(G_y+e). ALDER's Lemma 9 already uses (A4) to bound multipliers, but it does not make this fixed-cap transfer. Proof ancestry: the accelerated inner solver (similar-triangles type, Vasin et al. 2021) and gradient descent on the smooth envelope supply standard ingredients only.

**This result's κ-dependence is not the best available.** Composing the same cap transfer with Lu–Mei's unconstrained NC-SC solver (Thm 1, O(√κ(LΔ/ε′²+κ²)·log) at ε′=ε/S) would plausibly give O(√κ(BΔS²/ε²+κ²)·log). That beats the proved bound by about a factor of κ in the leading term. I did not verify that composition in detail.

**Search coverage.** I searched on 13 Nov 2026 UTC: arXiv and proceedings for coupled-constraint minimax (FAL, ALDER, Hu–Toh–Wang–Xiao [arXiv:2408.17213](https://arxiv.org/abs/2408.17213), SPACO [arXiv:2605.01246](https://arxiv.org/abs/2605.01246)), linear coupling, and bilevel methods with coupled constraints (BLOCC, [NeurIPS 2024](https://arxiv.org/abs/2406.10148): Õ(ε^{-2.5}) in squared gradient norm). None gives ε⁻² for nonlinear coupled ε-KKT. Hu et al. give only asymptotic results. Proofs and appendices were not read, and the OMS and SIOPT final texts were not checked. The companion note's citations match these sources. Its claim that ALDER's qualification is "the closest" understates the overlap: the assumptions are identical. The result was committed on 13 Nov 2026, after both baselines.

## Conclusion

**Yes: on the same problem class as the strongest baseline, the proved accuracy dependence improves from ε^{-7/2} to ε⁻² log(1/ε).**

ALDER (Oct 2026) assumes exactly this setup: the violated-only qualification, strong concavity, compact sets, and the same ε-KKT criterion. Lu–Mei's FAL covers a Slater subclass. Both pay ε^{-7/2} because their penalty parameter grows like 1/ε.

| | complete first-order calls (other constants fixed) |
|---|---|
| ALDER Thm 16 / FAL Thm 2 | ε^{-7/2} (FAL with an extra log) |
| this result | ε⁻² log(1/ε), with μ^{-3/2} instead of ALDER's μ^{-1/2} |

The gain needs ε small relative to μ, roughly ε ≪ μ^{2/3}. For poorly conditioned instances at moderate accuracy, ALDER's bound can be smaller. The mechanism behind the gain is a short quantitative exact-penalty lemma: a fixed multiplier cap introduces no spurious stationary points. Neither competitor states this lemma, though its ingredients are classical.

The comparison proves an ε-rate gain. The literature search found no prior ε⁻² result for nonlinear coupled constraints, but that does not prove priority. The proved κ^{3/2} dependence is likely improvable to √κ by pairing the same lemma with a known NC-SC solver. The contribution that can be claimed is the fixed-cap transfer and the resulting first O(ε⁻² log(1/ε)) ε-KKT bound found for this class, not an optimal-in-κ algorithm.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
