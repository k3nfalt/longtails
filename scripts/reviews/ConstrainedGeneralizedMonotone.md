# ConstrainedGeneralizedMonotone: novelty assessment

The [theorem](../../LongTails/Theorems/ConstrainedGeneralizedMonotone.lean) proves the following for convex `X` with an exact projection oracle and an `F : E → E` that is continuous, monotone, and 1-symmetric `(L₀,L₁)`-Lipschitz on all of `E`. The deterministic projected anchored extragradient method ([algorithm](../../LongTails/Algorithms/ConstrainedAnchoredExtragradient.lean)) returns a last iterate `x ∈ X` with tangent residual `dist(0, F(x) + N_X(x)) ≤ ε` ([setup](../../LongTails/Setups/ConstrainedGeneralizedMonotone.lean)). The updates use only `L₀`, `L₁` and `x₀`.

**Complexity** (2 `F`-calls and 1 projection per iteration):

  `O( (L₀ + L₁G)(1 + L₁R)·R/ε + (1 + L₁R)²·log(2 + (L₀ + L₁G₀)R/ε) )`

Here `R ≥ ‖x₀ − x*‖`, `G ≥ ‖F(x*)‖` for some VI solution `x*`, and `G₀ ≥ ‖F(x₀)‖`. The bound requires `L₀, R, ε > 0`. At `L₁ = 0` it is `O(1 + L₀R/ε)`, which matches the `Ω(LR/ε)` residual lower bound for Lipschitz operators (Yoon–Ryu 2021). The setup leaves `allowedAlgorithm` at its default `True`, which is appropriate because the claim is about the problem class, not about one method.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Cai–Oikonomou–Zheng, composite-EAG, [ICML 2024, arXiv 2206.05248v6](https://arxiv.org/abs/2206.05248), Thm 3.2. *Special case: needs a finite Lipschitz constant `L_X` of `F` on `X`.* | `O(1 + L_X R/ε)`; for `(L₀,L₁)` operators and `diam X = D`, `L_X ≤ (L₀+L₁G)e^{L₁D}` → bound above | Up to `e^{L₁D}/(1+L₁R)` in the leading term. Example: `F(x) = Ge^{L₁(x−x*)}` on `X = [x*, x*+R]` gives `L_X ≈ L₁Ge^{L₁R}`, so the gain is exponential when `L₁R ≫ 1` and `L₀ ≤ L₁G`. None: same order at `L₁ = 0`. | Requires `F` Lipschitz on `X` → allows `(L₀,L₁)` growth, including unbounded `X` where `L_X = ∞` | Same last-iterate tangent residual. `G₀` enters only logarithmically. | The new result is worse by `(1+L₁R)` and `(1+L₁R)²·log` when `F` is nearly Lipschitz but `L₁R` is large. `F` must be defined and monotone on all of `E`, not just on `X`. Composite-EAG also handles comonotone `F` and general proximal `A`. |
| Shen–Kılınç-Karzan, PF-NE-EG with backtracking, [arXiv 2604.07662v2](https://arxiv.org/abs/2604.07662) (Apr 2026, preprint), Prop. 2, Lemma 10, App. A | From the proof: `O(1 + (1/η₀ + L̄)²R²/ε² + log(η₀L̄))`, where `L̄` is the Lipschitz constant on `X ∩ B(x*, R+1)` and `L̄ ≤ (L₀+L₁G)e^{L₁(R+1)}`. The paper itself states only `o(1/√T)`. → bound above | `ε⁻² → ε⁻¹`, and the constant goes from exponential to polynomial in `L₁R` | None: their local-Lipschitz class contains this one | Worse: they need no `L₀`, `L₁` in the updates; here both must be known | The new result needs `F` to be globally `(L₀,L₁)` on `E`; they need only local Lipschitz continuity on `X` |
| Choudhury–Loizou, EG, [NeurIPS 2025, arXiv 2510.22421](https://arxiv.org/abs/2510.22421), Thm 3.6. *Unconstrained special case: `X = E`, `G = 0`.* | `O(L₀²R²/ε² + L₁²R²)` → `O(L₀(1+L₁R)R/ε + (1+L₁R)²log(2+(L₀+L₁G₀)R/ε))` | Better when `L₀R/ε ≫ 1 + L₁R`. Worse by a log factor when the `L₁²R²` term dominates. | Unconstrained → constrained with `F(x*) ≠ 0` | Best iterate → last iterate | None beyond the stated log factor |
| Repository [AnchoredGeneralizedMonotone](../../LongTails/Theorems/AnchoredGeneralizedMonotone.lean). *Unconstrained special case.* | `O(L₀R/ε + (1+L₁R)log(1+(L₀+L₁G)R/ε))` → bound above | Worse at `X = E`, by `(1+L₁R)` in the leading term | Unconstrained → constrained | None | Larger constants |

**Reduction and mechanism.** Running constrained EAG with a Lipschitz constant on `X` or on a ball is the obvious reduction. It gives exponential constants, and none at all when `X` is unbounded and `L₁ > 0`. I did not verify the note's penalty route, which gives `ε⁻²`. The step that is new, as far as I found, is the `one_point` lemma (`ConstrainedAnchoredStep.lean:44`). It tests monotonicity at `y + εv` and uses the `(L₀,L₁)` condition to keep `‖F(x_k)‖ ≤ G + O((L₀+L₁G)R) + O(R(1+L₁R)/S_k)` along the run. The proof builds on prior work:
- the anchored extragradient potentials of Yoon–Ryu (ICML 2021) and Lee–Kim (NeurIPS 2021);
- the device of putting the previous normal vector inside the update, from Cai–Oikonomou–Zheng;
- the repository's unconstrained step rule.

None of these supplies the operator-norm bound when `F(x*) ≠ 0`.

**Search coverage.** I searched on 2026-10-12, covering arXiv, PMLR/ICML, NeurIPS and MOR preprints, and read theorem text for every source above. I also checked the following, which are not competitors here:
- Vankov–Nedić–Sankar ([ICML 2024](https://proceedings.mlr.press/v235/vankov24a.html), Thms 4.1–7.1, and the TMLR 2025 follow-up): constrained, but every rate requires `p`-quasi-sharpness.
- Chorobura–Necoara–Pesquet ([arXiv 2503.01070](https://arxiv.org/abs/2503.01070), Thm 4): a polynomial-type generalized Lipschitz condition with best-iterate `ε⁻²`, which does not cover exponential growth.

Discrepancies with the companion note:
- The note omits Shen–Kılınç-Karzan, which predates this result.
- The note cites constrained EAG as "Cai–Oikonomou–Zheng NeurIPS 2022"; the paper appeared at ICML 2024.

The result was introduced in commit `a89a364` (2026-10-09). I did not run any build or axiom check.

## Conclusion

**Yes: for constrained monotone `(L₀,L₁)`-Lipschitz VIs, this gives the first checked `O(1/ε)` tangent-residual bound with polynomial constants.**

The strongest prior guarantees for the full class have one of two weaknesses. Shen–Kılınç-Karzan's backtracking extragradient needs `ε⁻²` calls, with a non-explicit local Lipschitz constant that can grow exponentially in `L₁R`. Constrained EAG reaches `1/ε` only with a global Lipschitz constant on `X`, which can be exponential in `L₁·diam X` or infinite.

| | tangent-residual calls |
|---|---|
| constrained EAG (when `L_X < ∞`) | `L_X R/ε`, with `L_X` up to `(L₀+L₁G)e^{L₁·diam X}` |
| backtracking EG | `≈ L̄²R²/ε²`, with `L̄` up to `(L₀+L₁G)e^{L₁(R+1)}` |
| this result | `(L₀+L₁G)(1+L₁R)R/ε + (1+L₁R)²log(2+(L₀+L₁G₀)R/ε)` |

A one-dimensional exponential operator on an interval shows that the exponential constant of the Lipschitz route actually occurs. The gain is therefore real whenever `L₁R ≫ 1` or `ε` is small.

The result loses in three places. It must know `L₀` and `L₁`, while backtracking is parameter-free. It requires `F` to be monotone and `(L₀,L₁)` on the whole space. It carries a `(1+L₁R)` factor that makes it worse than the repository's unconstrained bound at `X = E`.

Priority is less certain: the search found no earlier result of this kind, but that does not prove none exists. The claimable contribution is an ε⁻¹ rate with polynomial constants for this constrained class, made possible by a new quantitative operator-norm bound.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
