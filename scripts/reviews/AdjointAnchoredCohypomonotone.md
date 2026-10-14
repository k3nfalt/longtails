# Adjoint-anchored proximal method for cohypomonotone equations with any ρ

[`result`](../../LongTails/Theorems/AdjointAnchoredCohypomonotone.lean) proves the following. Let F : E → E on a finite-dimensional Euclidean space be L-Lipschitz and ρ-cohypomonotone for any ρ ≥ 0, with ρL ≥ 1 allowed. Assume F is differentiable with an L₂-Lipschitz Jacobian and has a zero within distance R of x₀. The oracle answers both F(x) and vector–Jacobian products DF(x)ᵀw ([setup](../../LongTails/Setups/CohypomonotoneAdjoint.lean)). Under these conditions, the deterministic [algorithm](../../LongTails/Algorithms/AdjointAnchoredProximal.lean) outputs a completed outer iterate x̂ with ‖F(x̂)‖ ≤ ε. The algorithm is an anchored inexact proximal point method whose resolvent equations are solved by gradient steps on ½‖v+γF(v)−t‖².

**Complexity** (total F calls plus VJP calls; derived from the Lean `budget`):

  O( (1+ρL)² log(e+ρL) + (1+ρL) log(e+ρL) · LR/ε + (1+ρL)⁴ (L₂R/L) log²(e+LR/ε) ).

Here L is the Lipschitz constant of F, ρ the cohypomonotonicity modulus, L₂ the Lipschitz constant of the Jacobian, R the distance from x₀ to a solution, and ε the target residual. The algorithm needs L, L₂ and ρ. The first additive term comes from the `+2` in the budget, and the companion note's displayed bound omits it.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Alacaoglu–Kim–Wright, [arXiv 2402.05071](https://arxiv.org/abs/2402.05071), ICML 2024, Thm 2.1 / Cor. 2.2, with η=(1+ρL)/(2L), H=0; repo [MultiStepAnchoredCohypomonotone](../../LongTails/Theorems/MultiStepAnchoredCohypomonotone.lean). **Special case: ρL < 1 only** | O(1 + LR log(e/(1−ρL)) / ((1−ρL)²ε)) → O(1 + LR/ε + (L₂R/L) log²(e+LR/ε)) on ρL<1 | Up to a factor (1−ρL)⁻² log(e/(1−ρL)) when ε ≤ L² log(e/(1−ρL)) / (L₂ (1−ρL)² log²(e+LR/ε)). Example: L=R=L₂=1, 1−ρL=10⁻², ε ≤ 10⁻² gives about 10⁴×. Worse by the additive L₂ term when ρL is bounded away from 1 and ε ≳ L²/(L₂ log²(LR/ε)) | ρL < 1 → any ρ ≥ 0; new instances are those with ρL ≥ 1 (for example a linear repelling mode −a with a < L) | None (both: last completed iterate, ‖F‖ ≤ ε, known L and ρ) | Adds an L₂-Lipschitz Jacobian and VJP oracle; unconstrained only (AKW also covers +H with resolvents, and weak-MVI or stochastic variants); finite dimension; also needs L₂ |
| Yoon–Ryu EAG ([ICML 2021](https://proceedings.mlr.press/v139/yoon21d.html)), Halpern methods. **Special case ρ=0** | O(1 + LR/ε) → O(1 + LR/ε + (L₂R/L) log²(e+LR/ε)) | Worse: extra additive term | None | None | Same tradeoffs as the AKW row |
| Exact PP, Gorbunov–Taylor–Horváth–Gidel, [arXiv 2210.13831](https://arxiv.org/abs/2210.13831) v3, ICML 2023, Thm 3.1 (γ>2ρ, any ρ). **Stronger oracle: exact resolvent of F** | O(R²/(γ(γ−2ρ)ε²)) resolvent calls → not comparable | Not comparable: it gives no F-call or VJP-call bound | None; both cover any ρ | Not comparable | PP needs an exact resolvent of a nonmonotone operator; this result implements resolvents inexactly with F and VJP calls |

**Reduction check.** The result is a composition of known steps. For γ ≥ 2ρ, Bauschke–Moursi–Wang (Math. Program. 2021) show that I+γF is expanding. Differentiating that property gives ‖(I+γDF)ᵀr‖ ≥ ‖r‖ in finite dimension. So the inner merit is PL with modulus 1, and gradient descent on a PL function (Polyak 1963) solves each resolvent equation to relative error. Plugging that error into the AKW/repo relative-error anchored scheme gives the leading term, (outer steps LR/((1+ρL)ε)) × (inner steps (1+ρL)² log(e+ρL)). The remaining work is bookkeeping, not a new mechanism: a damped-step burn-in for the locally smooth phase, and a harmonic iterate bound that makes the burn-in independent of 1/ε. Exact PPM and AKW are proof ancestry. The ρ-unrestricted range is unlocked by the VJP oracle, not by a new outer method.

**Search coverage.** I searched on 2026-10-08 and read AKW (v2: Thm 2.1, Cor. 2.2, and the 1/L conjecture), Gorbunov et al. (Table 1, Thms 3.1 and 3.3), and Vyas–Bullins [arXiv 2603.13491](https://arxiv.org/abs/2603.13491) (Mar 2026). Vyas–Bullins uses higher-order solves under a *higher-order* weak-MVI condition ⟨F(z),z−z*⟩ ≥ −(ρ/2)‖F(z)‖^{(s+1)/s} with ρ bounded via L_s, and reports best-iterate accuracy. That class is incomparable, so it is not in the table. Perseus and Agafonov et al. ([arXiv 2405.15990](https://arxiv.org/abs/2405.15990)) treat only the monotone or Minty case (ρ=0). I found no end-to-end F/VJP bound for ρL ≥ 1, but the second-order and Newton-type VI literature was not exhaustively checked. The result was introduced in commit f41bb0b on 2026-10-07; I found no later work.

Discrepancies with the companion note:
- [arXiv 2310.02987](https://arxiv.org/abs/2310.02987) is Cai–Alacaoglu–Diakonikolas on finite-sum monotone inclusions. Its abstract does not state the 1/L conjecture, and I did not verify Cor. 4.5.
- The note's headline "barrier" is not in Lean. It is the classical GMRES-stagnation phenomenon for normal matrices with eigenvalues at roots of −1 (Nachtigal–Reddy–Trefethen 1992), and it says nothing about methods that use VJPs.

## Conclusion

**It covers new instances (ρL ≥ 1), but only because the oracle is strengthened, and the method is a routine composition.** For F-only methods, the strongest baseline is Alacaoglu–Kim–Wright (ICML 2024), which requires ρL < 1. With an added Lipschitz Jacobian and one VJP per inner step, this theorem gives a dimension-free bound for every ρ:

  O((1+ρL) log(e+ρL)·LR/ε + (1+ρL)² log(e+ρL) + (1+ρL)⁴(L₂R/L) log²(e+LR/ε)).

On the overlap ρL < 1, it improves AKW's LR/((1−ρL)²ε) to LR/ε + (L₂R/L)log² when ρL is close to 1 and ε is small, but only with the stronger oracle. When ρ = 0 it is slightly worse than EAG.

I found no prior end-to-end bound for ρL ≥ 1 under any oracle weaker than exact resolvents, so historical novelty is plausible but not certain. The construction is the anchored inexact proximal method plus gradient descent on a PL merit, whose modulus 1 follows directly from known expansiveness of I+γF. The "1/L barrier" framing concerns F-only methods, which this method is not.

What can be claimed is the first explicit complexity bound for Lipschitz-Jacobian cohypomonotone equations with arbitrary ρL, using F and VJP calls, obtained by a straightforward composition of known tools.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
