# Constant-momentum SGD with affine step decay: novelty assessment

The [theorem](../../LongTails/Theorems/ConstantMomentumLastIterate.lean) proves that EMA-form SGD with momentum ([algorithm](../../LongTails/Algorithms/ConstantMomentumSgd.lean)) uses a fixed β ∈ [0,1), starts from zero momentum, and takes steps η_t = γ(N+1−t+β/(1−β)) with γ = R/(G(N+2)^{3/2}). For every convex f on a separable Hilbert space with a minimizer x*, ‖x₀−x*‖ ≤ R, and an i.i.d. oracle whose mean is a subgradient and E‖g‖² ≤ G² ([setup](../../LongTails/Setups/MomentumLipschitzConvex.lean)), its **last iterate** x_N satisfies E f(x_N) − f* ≤ ε.

**Proved complexity.** Here G bounds the oracle's second moment, R is the initial distance, β is the given momentum, and ε is the expected objective gap. The proved budget is ⌈100G²R²/ε²⌉ + ⌈4κ²(1+log(1/(1−β)))⌉ with κ = β/(1−β). In O-form, it is

  N = O( G²R²/ε² + β²(1−β)⁻² · log(e/(1−β)) ) oracle calls.

The algorithm requires G, R, β, ε and therefore the horizon. The proof covers only the unconstrained case. The guarantee is in expectation and gives exactly N calls. At R = 0, the algorithm stays at x₀ = x*.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liu–Zhou, [arXiv:2312.08531](https://arxiv.org/abs/2312.08531) v4 (ICLR 2024), Thm 3.4 with L=0, M=2G, σ≤G; deterministic analogue: Zamani–Glineur, [SIOPT 2025](https://epubs.siam.org/doi/abs/10.1137/24M1717762), exact GR/√(T+1) | O(G²R²/ε²) → O(G²R²/ε² + κ² log(e/(1−β))) | Worse: adds a β burn-in term; constant 100 vs. O(1) | None. The class is the same, and Liu–Zhou also covers composite problems, constraints, and general norms | None: both give last-iterate expected gaps with known T | Must use EMA momentum with constant β, while SGD is the β=0 case. Unconstrained only |
| Li–Liu–Orabona, [ALT 2022 / arXiv:2102.07002](https://arxiv.org/abs/2102.07002), Cor. 1 (FTRL-based SGDM, increasing momentum β_t=(t−1)/t, assumption H3: E‖g‖²≤G²) | ≤ 9G²R²/ε² (3GR/√T, with c=R) → O(G²R²/ε² + κ² log(e/(1−β))) | Worse or equal: no regime gives a gain | None: same class | Worse: LLO's γ_t = c/(G√t) option is anytime, while this method needs N | Here momentum is constant instead of increasing and shrinking. This is a choice of algorithm, not a gain in complexity |
| Defazio et al., *The Road Less Scheduled*, [NeurIPS 2024 / arXiv:2405.15682](https://arxiv.org/abs/2405.15682) v4, Thm 1 (Schedule-Free SGD, any constant β∈[0,1]) | G²R²/ε² (DG/√T) → O(G²R²/ε² + κ² log(e/(1−β))) | Worse: Schedule-Free has no β burn-in and a smaller constant | Restricted overlap: Thm 1 requires each f(·,ζ) to be G-Lipschitz, so it does not cover all oracles with E‖g‖²≤G² here | None. Schedule-Free outputs its averaged sequence x_T, which is not the query point y_T | Here the method is EMA momentum, not interpolation or primal averaging |

**Reductions and proof ancestry.** Li–Liu–Orabona's Thm 1 gives a lower bound of (1−β)²G²c·ln T/(4T^α) for constant-β SGDM with steps c·t^{−α}, α ≤ 1/2. This rules out constant or polynomial steps, but it does not cover a horizon-dependent affine schedule. The proof combines three ingredients:

- the exact virtual iterate z_t = x_t − κγτm_{t−1};
- momentum telescoping from Ghadimi et al. ([arXiv:1412.7457](https://arxiv.org/abs/1412.7457));
- last-iterate reference points from Zamani–Glineur and Liu–Zhou.

The ingredient I could not reduce to known results is the new weight sequence W(τ). It keeps all intermediate coefficients nonnegative (`uu_mono`). Treating g_t as an inexact subgradient at z_t bounds f(z_N), not f(x_N), and leaves a β-dependent leading factor. I found no reduction that yields this exact output.

**Search coverage.** On 2026-10-07 I searched arXiv and venue pages for SGDM/EMA, heavy ball, and Schedule-Free methods, last-iterate linear decay, and Kornowski–Shamir ([arXiv:2604.13870](https://arxiv.org/abs/2604.13870)). I read the theorem statements of LLO, Liu–Zhou v4, and Schedule-Free v4. I did not reread Zamani–Glineur's momentum conjecture or check the Hudiani and Tao et al. details. The result first appeared in commit b53d0b2 on 2026-10-05; all cited works precede it.

The companion note's citations match the sources I checked. Its claim "not an improvement of the oracle complexity of the problem class" is accurate. Its title word "optimal" applies only to the G²R²/ε² term; the additive β term has no matching lower bound.

## Conclusion

**No: the result gives a new analysis of a particular method, not a better optimization guarantee.**

For convex objectives with stochastic subgradients satisfying E‖g‖² ≤ G², last-iterate accuracy ε already costs O(G²R²/ε²) calls. Plain SGD with linear decay achieves this (Liu–Zhou, Thm 3.4), and so does Li–Liu–Orabona's increasing-momentum SGDM, which is also anytime. The theorem matches that order for constant-β EMA momentum and adds a burn-in term:

| method | last-iterate calls |
|---|---|
| Liu–Zhou SGD / LLO FTRL-SGDM | O(G²R²/ε²) |
| this theorem | O(G²R²/ε² + β²(1−β)⁻² log(e/(1−β))) |

The problem class is unchanged, the output is the same, and the algorithm needs the same information. The selected method is never better in any regime, and it is strictly worse when β → 1 with G²R²/ε² fixed.

The likely new contribution is a proof that constant EMA momentum, with a β-shifted linear-decay schedule, avoids the ln T loss that Li–Liu–Orabona proved for polynomial steps. The leading constant does not depend on β, and the proof relies on a new weight construction. I found no earlier statement of this result, but that does not establish priority. As in the repository's negative examples, a method-specific analysis without a better total complexity, broader scope, or a stronger output guarantee counts as no improvement.

What can be claimed is a log-free last-iterate analysis of constant-momentum SGD, not a faster or more general method for this problem class.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
