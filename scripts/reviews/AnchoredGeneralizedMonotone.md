# Anchored extragradient for monotone (L0, L1)-Lipschitz root finding

For every continuous monotone F on a real inner-product space that is 1-symmetric (L0, L1)-Lipschitz, with a root x* satisfying ‖x0 − x*‖ ≤ R and ‖F(x0)‖ ≤ G, the step-adaptive anchored extragradient method ([theorem](../../LongTails/Theorems/AnchoredGeneralizedMonotone.lean), [setup](../../LongTails/Setups/GeneralizedLipschitzMonotone.lean), [algorithm](../../LongTails/Algorithms/AnchoredExtragradient.lean)) uses the steps γ_k = min{S_k/3, 1/(4(L0 + L1(‖F x_k‖ + ‖x_k − x0‖/S_k)))}, and its **last iterate** satisfies ‖F(x)‖ ≤ ε deterministically after exactly 2(⌈11L0R/ε + (27L1R + 4)·ln(1 + 8(L0 + L1G)R/ε)⌉ + 1) F-evaluations.

**Complexity** (L0 > 0, L1 ≥ 0: generalized-Lipschitz constants; R: initial distance to a root; G: initial residual; ε: target residual):

  N = O( 1 + L0R/ε + (1 + L1R)·log(1 + (L0 + L1G)R/ε) ).

The updates use only L0, L1 and x0. R, G and ε enter only the budget. Because ‖F(x0)‖ ≤ L0R·e^{L1R} always holds (Choudhury–Loizou, Prop. 3.1), the worst case over G is N = O(1 + L0R/ε + L1²R²).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Choudhury–Loizou, EG with step ν/(L0+L1‖F x_k‖), [arXiv:2510.22421](https://arxiv.org/abs/2510.22421) Thm 3.6 (NeurIPS 2025; v1 2025-10-25). Prior. | O(1 + L0²R²/ε² + L1²R²) → O(1 + L0R/ε + (1+L1R)log(1+(L0+L1G)R/ε)) ≤ O(1 + L0R/ε + L1²R²) | Leading term L0²R²/ε² → L0R/ε. The speedup is Θ(L0R/ε) when ε ≤ L0/(L1²R) and ε ≤ L0R. It is ≥ L0²/(L1ε)² when L0/(L1²R) ≤ ε ≤ L0/L1. For ε ≥ L0/L1 there is a gain only if G is moderate: if log(1+L1G/L0) = O(log(2+L1R)), then L1²R² → L1R·log(2+L1R+L0R/ε). Never worse, up to constants. | ℝ^d → any real inner-product space (minor) | min_{k≤K} residual → last iterate. The baseline is also last-iterate (EG residual is nonincreasing under this step, per the note), and residuals are observable, so this conversion is cheap. Same information (L0, L1). | Only α = 1 (the baseline also covers α ∈ (0,1), Thm 3.7). Requires L0 > 0. No strongly monotone or weak-Minty cases. |
| Yoon–Choudhury–Greenberg–Loizou, PolyakEG / PolyakEG-LS, [arXiv:2609.26581](https://arxiv.org/abs/2609.26581) Thm 3.4, eq. (19), Prop 3.5 (preprint, 2026-09-22). Prior by 11 days. | O(1 + L0²R²/ε² + L1²R²) for the min-iterate residual, plus finite backtracking (count not re-derived) → same as above | Same as the first row | None | Worse in information: PolyakEG-LS needs no L0, L1, but the selected method needs both. | Selected method has no line search |
| FEG / EAG (Lee–Kim [2106.02326](https://arxiv.org/abs/2106.02326); Yoon–Ryu [2102.07922](https://arxiv.org/abs/2102.07922)). Special case L1 = 0 only. | O(1 + L0R/ε) → O(1 + L0R/ε) | None: same order (constant ≈ 5× FEG's) | Global L-Lipschitz → (L0, L1)-Lipschitz | None | None on the overlap |

**Standard-reduction check.** I found no reduction that reproduces the result. The class is Lipschitz on B(x*, 2R) only with a constant of order L0(1+L1R)e^{2L1R}, so FEG gives an exponential bound. Tikhonov regularization (μ ≈ ε/R) plus Choudhury–Loizou Cor. 3.3 carries the burn-in L1R²/(ζμ), where 1/ζ ∝ L0(1 + L1R e^{L1R}). The note's "routine" bound O(L1²R² + (L0R/ε)log(L0R/ε)) is therefore not established by any theorem I checked.

The proof ancestry is the FEG/EAG potential with variable-step anchor weights β_k = γ_k/S_{k+1}. The new ingredients are:
- a closed-form step that certifies both extragradient segments using the observable bound ‖F x_k‖ + ‖x_k − x0‖/S_k;
- a uniform distance bound ‖x_k − x*‖² ≤ (5/4)R² for adaptive anchored iterates;
- a step-growth counting argument.

For L1 = 0, Yoon–Ryu's lower bound for high-dimensional span methods (cited, not re-derived) makes the term L0R/ε unimprovable beyond constants. No lower bound on the L1-dependent additive term is known.

**Search coverage (2026-10-07).** I searched arXiv, PMLR and NeurIPS sources for (L0, L1)/generalized-smooth VIs and for anchored, Halpern and line-search methods under local or non-Lipschitz continuity. I read the theorem statements of 2510.22421, 2609.26581 and Vankov et al. [ICML 2024](https://proceedings.mlr.press/v235/vankov24a.html), which covers structured non-monotone VIs and has no monotone residual rate. Sun–Zhang–Zhao [2607.07585](https://arxiv.org/abs/2607.07585) has rates only under global Lipschitz continuity (Thm 1, Rem. 4). I checked Hölder, higher-order and Tikhonov-anchoring papers only through their abstracts. The theorem was introduced in commit bf9edbc (2026-10-03), and I found no later work on the same setup. The note's citations check out, apart from the unverified routine-bound claim above.

## Conclusion

**Yes. On this operator class, the proved residual complexity is polynomially better than the best published guarantees.** The strongest baselines are the extragradient analyses of Choudhury–Loizou (Thm 3.6) and the Polyak-step extragradient of Yoon et al. Both are unaccelerated:

| | F-evaluations for ‖F(x)‖ ≤ ε |
|---|---|
| EG / PolyakEG (prior) | O(1 + L0²R²/ε² + L1²R²) |
| This result | O(1 + L0R/ε + (1+L1R)·log(1 + (L0+L1G)R/ε)) ≤ O(1 + L0R/ε + L1²R²) |

Up to constants, the new bound is never worse. It is faster by a factor of order L0R/ε whenever ε ≤ min{L0R, L0/(L1²R)}. For example, with L0 = L1 = 1, R = 10 and ε = 10⁻³, the counts are about 10⁸ versus about 10⁴. When ε ≥ L0/L1 it gains only if the initial residual G is moderate; otherwise both bounds are of order L1²R².

The tradeoffs:
- only α = 1 is covered;
- L0 and L1 must be known, whereas PolyakEG-LS is parameter-free at the slower rate;
- for L1 = 0 the result is only FEG with worse constants.

Exponential factors defeat the obvious reductions (local Lipschitz constants on a ball, regularization). The search found no prior accelerated rate for this class, but that does not prove priority.

What can be claimed is the first checked accelerated O(L0R/ε) residual rate for monotone (L0, L1)-Lipschitz operators without exponential factors, obtained through a new step rule and distance analysis.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
