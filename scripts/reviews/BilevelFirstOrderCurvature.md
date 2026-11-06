# BilevelFirstOrderCurvature: novelty assessment

[`result`](../../LongTails/Theorems/BilevelFirstOrderCurvature.lean) shows that the [restarted accelerated penalty method](../../LongTails/Algorithms/BilevelAccelerated.lean) returns, for every seed, a point x̂ with ‖∇F(x̂)‖ ≤ ε. Here F(x) = f(x, S(x)) is the hyperobjective over the [higher-smoothness nonconvex–strongly-convex bilevel class](../../LongTails/Setups/HigherSmoothBilevel.lean), and the method uses only exact joint (f, g, Df, Dg) queries.

**Parameters.** L is one common bound covering ‖Df‖ and the Lipschitz constants of Df, D²f, Dg, D²g, D³g (Lean uses the max product norm). μ is the strong convexity of g(x, ·), and κ = L/μ. Δ ≥ F(x₀) − inf F, G ≥ ‖∇_y g(x₀, y₀)‖, and the spaces are any finite-dimensional ones. The public budget is ⌈2⁴⁰U(1+W)log(2P)⌉, which gives, for ε < 2L²/μ:

$$
N=O\!\Big(\Big[\tfrac{L}{\mu^{3/4}\varepsilon^{1/4}}+\tfrac{\Delta L^{7/2}}{\mu^{11/4}\varepsilon^{7/4}}\Big]\log\!\Big(\tfrac{2L}{\mu}(1+\tfrac{L}{\varepsilon})(1+\tfrac{\Delta}{\varepsilon})(1+\tfrac{G}{\varepsilon})\Big)\Big)
$$

The second term is Δ L^{3/4} κ^{11/4} ε^{-7/4}. The count covers every inner solve and padding call, and has no dimension dependence.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Chen–Ji–Zhang, [arXiv:2511.22331v4](https://arxiv.org/abs/2511.22331) (Aug 11 2026; prior), App. F, Thm "ub-p2" (AccF²BA⁺: AccF²BA with AGD inner solves) | Õ(Δ L^{3/4} κ^{13/4} ε^{-7/4} log⁶(d_x/(δε))), probability 1−δ → O(Δ L^{3/4} κ^{11/4} ε^{-7/4} log(P)), deterministic | A factor κ^{1/2} (plus the log⁶(d_x/(δε)) factor) when the second term dominates, i.e. Δ√(Lκ⁴/ε³) ≥ 1 | None. Same p=2 class (Def. 2.1, including bounded ∇f), with κ̄ = κ under common constants | Probability 1−δ → every seed; no d_x log | Loses the SOSP guarantee (only FOSP). With heterogeneous constants L_q, the new bound uses L̄ = max L_q and wins only if L̄^{1/4}μ^{1/2} < L₁^{1/2}L₂^{1/4} |
| Chen–Ma–Zhang, [arXiv:2306.14853v5](https://arxiv.org/abs/2306.14853), JMLR 26 (2025), Thm 5.2 (AccF²BA) | Õ(Δ L^{3/4} κ^{15/4} ε^{-7/4}), SOSP w.p. 1−δ → as above | A factor κ in the same regime | None | Same as row 1 | Same as row 1 |
| Yang–Luo–Li–Jordan, [arXiv:2307.00126](https://arxiv.org/abs/2307.00126) (2023; venue not verified), RAHGD, Cor. 3.6 | Õ(κ^{11/4}) f-gradients plus Õ(κ^{13/4}) g-gradients/HVPs, each times L^{3/4}Δε^{-7/4} → O(Δ L^{3/4} κ^{11/4} ε^{-7/4}) joint gradient calls | A factor κ^{1/2} in total calls; the κ^{11/4} exponent itself is not new | None | None | Previous method needs a stronger Hessian-vector oracle; the new one needs gradients only |
| FSBA/LFSBA, Yang–Liu–Chen–Lui, [arXiv:2605.06431](https://arxiv.org/abs/2605.06431), ICML 2026, Thms 3.4/4.3, with finite-difference Hessians (the companion note's derivation; only the reported call counts were checked) | Õ(√κ + D + Δ√L[κ³ + √D κ^{11/4}]ε^{-3/2}), where D = dim X + dim Y → O(Δ L^{3/4} κ^{11/4} ε^{-7/4} log P) | Better, up to constants and logs, iff ε ≥ L/(κ^{1/4} + √D)⁴ (e.g. D ≥ √(L/ε) or κ ≥ L/ε). Worse for smaller ε at fixed dimension | None | No dimension dependence; SOSP → FOSP | Previous route depends on dimension and is Hessian-based; it gives SOSP and the better ε^{-3/2} rate |

**Reduction check.** The total complexity comes from substituting new curvature constants, ‖∇²F‖ ≤ 32Lκ^{5/2} and Lip(∇²F) ≤ 512Lκ⁴, into the known AccF²BA⁺ count √(κL_F)ρ_F^{1/4}Δε^{-7/4}. Previously L_F = O(Lκ³) (Ghadimi–Wang) and ρ_F = O(Lκ⁵) (Huang et al., Lemma 2.4). The substitution gives exactly κ^{1/2}·κ^{5/4}·κ = κ^{11/4}. So the outer and inner method is standard proof ancestry: penalty estimator (Kwon et al.), restarted nonconvex AGD (Li–Lin), and inner AGD. The new ingredient is the energy-norm control of D³g in mixed directions, which yields the two curvature bounds. None of the checked sources states these bounds; Chen–Ma–Zhang and the ICML 2026 FSBA paper both still use κ³/κ⁵. I did not independently verify the companion note's 1-D sharpness examples, and I did not build the Lean proof or run an axiom audit.

**Search coverage.** On 2026-11-05 UTC I searched arXiv, ICML 2026, and JMLR material on deterministic, stochastic, finite-sum, and second-order bilevel methods. I read primary theorem text for Chen–Ji–Zhang (TeX source, App. F), Chen–Ma–Zhang v5, Bi et al. [2606.20534](https://arxiv.org/abs/2606.20534) (symbolic constants, Hessian-based), and Zhou–Niu [2610.24538](https://arxiv.org/abs/2610.24538) (finite-sum, ε^{-2}). Li's [2405.00914](https://arxiv.org/abs/2405.00914) has been withdrawn and was unreadable. The stochastic highly-smooth paper [2509.02937](https://arxiv.org/abs/2509.02937) was not checked for deterministic consequences.

The companion note's table cites Chen–Ji–Zhang's leading term correctly, but that theorem certifies SOSP with probability 1−δ. Chen–Ji–Zhang's Ω(κ^{9/4}Δ√L₁L₂^{1/4}ε^{-7/4}) lower bound uses quadratic f, so its hard instances have unbounded ∇f and it does not directly apply here. The theorem was introduced in commit 1841c1f3 (2026-11-05 23:08 UTC), after every compared source.

**Conclusion**

**Yes: on the common-constant second-order-smooth class, the proved total first-order complexity improves by a factor √κ.** The strongest gradient-only baseline is Chen–Ji–Zhang's AccF²BA⁺:

| | total joint gradient calls for ‖∇F‖ ≤ ε |
|---|---|
| AccF²BA⁺ (2026) | Õ(Δ L^{3/4} κ^{13/4} ε^{-7/4}) (SOSP, w.p. 1−δ, log⁶ d_x) |
| this result | O(Δ L^{3/4} κ^{11/4} ε^{-7/4} · log) (FOSP, deterministic) |

The gain holds whenever the ε^{-7/4} term dominates the startup term. It also beats the Hessian-vector-product method RAHGD in total calls. It loses SOSP certification, and it loses to finite-difference simulation of second-order methods when ε < L/(κ^{1/4} + √dim)⁴.

The mechanism is new sharper curvature estimates for the hyperobjective under third-order smoothness of g. Plugging them into the existing accelerated penalty framework is routine and gives the bound exactly. No checked source contains these estimates, but the literature search cannot prove priority. Optimality is open: the gap to the κ^{9/4} lower bound, which is proved only for unbounded-gradient quadratic instances, remains.

What can be claimed is a dimension-free, gradient-only first-order stationarity bound with κ^{11/4} instead of κ^{13/4}, driven by improved hyperobjective curvature constants.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
