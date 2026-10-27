# Novelty assessment: envelope cubic Newton for nonconvex–PL minimax

[`EnvelopeCubicNonconvexPL.result`](../../LongTails/Theorems/EnvelopeCubicNonconvexPL.lean) proves the following for the setup [`NonconvexPLSecondOrder`](../../LongTails/Setups/NonconvexPLSecondOrder.lean). Let f(x,y) be defined on finite-dimensional spaces, with an L-Lipschitz gradient and a ρ-Lipschitz joint Hessian. Assume every inner maximum is attained and the uniform inner PL inequality 2μ(Φ(x)−f(x,y)) ≤ ‖∇ᵧf‖² holds. Then the deterministic [envelope cubic method](../../LongTails/Algorithms/PLMinimaxMethod.lean) uses `budget` exact (value, gradient, full Hessian) calls and returns x with ‖∇Φ(x)‖ ≤ ε and ∇²Φ(x) ⪰ −√(100ρ√(L/μ)(4+L/μ)ε)·I. Here Φ = max_y f.

**Proved complexity.** The `budget` formula is:

  N = O( [1 + L/μ + Δ√ρ (L/μ)^{3/4} ε^{−3/2} + Δρ²/μ³] · log²(2 + L/μ + ρ²(Δ+D)/μ³ + ρε/μ² + μ²/(ρε)) ).

The parameters are as follows. Δ ≥ Φ(x₀) − inf Φ, D ≥ Φ(x₀) − f(x₀,y₀), 0 < μ ≤ L, and ρ, ε > 0. There is no restriction on ε. The [budget proof](../../LongTails/Proofs/PLMinimaxBudget.lean) (`explicit_execution_budget`) bounds the full execution count by this formula. I write κ = L/μ only inside the table.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhou–Chen–Luo–Liu, ECRN, [arXiv:2610.20345v1](https://arxiv.org/abs/2610.20345), Thm 11 (preprint, 14 Oct 2026; prior by 13 days). **Applies only to the strongly concave (NC–SC) subclass.** | Õ(√κ + Δ√ρ κ^{3/4} ε^{−3/2}) gradient+Hessian evaluations for ε ≤ L²/(ρ(4+κ)^{3/2}), with curvature tolerance √(ρ(4+κ)^{3/2}ε) → N | None: same order. Running ECRN at ε′ = min(ε, L²/ρ(4+κ)^{3/2}) reproduces the Δρ²/μ³ term, so dropping the ε-restriction gains nothing. | μ-strong concavity in y → uniform PL with attained maxima. This adds nonconcave inner objectives and nonunique, possibly curved maximizer sets. | None. Both return the proximal primal point and certify the same (ε, Θ(√(ρκ^{3/2}ε)))-SOSP of Φ. | Ours has an initialization term κ instead of √κ, a log² factor, and a curvature constant up to 10× looser. Our oracle also returns f-values. |
| Luo–Li–Chen, MCN, [NeurIPS 2022](https://mlanthology.org/neurips/2022/luo2022neurips-finding/) ([arXiv:2110.04814v3](https://arxiv.org/abs/2110.04814)). **Applies only to NC–SC.** | O(κ^{1.5}√ρΔε^{−1.5}) Hessian calls plus Õ(κ²√ρΔε^{−1.5}) gradient calls for an (ε, κ^{1.5}√(ρε))-SOSP → N | κ² → κ^{3/4} in leading joint-call cost when ε ≤ L²/(ρκ^{3/2}), and the curvature tolerance tightens by κ^{3/4}. ECRN already achieves both. | Strong concavity → PL | Stronger curvature certificate | Same as row 1 |
| Yang–Orvieto–Lucchi–He, Smoothed-AGDA, [AISTATS 2022](https://proceedings.mlr.press/v151/yang22b.html), Thm 4.1 plus the Φ-translation remark. **Applies to the full NC–PL class.** | O(κLΔε^{−2}) + Õ(κ) gradient calls for ‖∇Φ‖ ≤ ε only → N | Not comparable: the oracles differ, and ours gives a second-order output. | None. Their class is broader, with no Hessian-Lipschitz assumption. | First-order stationarity → second-order stationarity | Ours requires a ρ-Lipschitz Hessian and a full Hessian per call. |

**Reduction check.** ECRN's Lemmas 4–5 rely on a unique maximizer y*(z) and the inverse of the strongly concave Hessian. Under PL, ∇²ᵧᵧf is singular on the maximizer set, so the method cannot be substituted. Tikhonov regularization −(λ/2)‖y−y₀‖² changes Φ by an amount that is not controlled by Δ or D. I found no reduction from NC–PL to NC–SC.

The new step, which I read in the note and the module structure but did not line-check, is a primal-unique linearized saddle derivative. The joint Hessian kernel has zero x-component, which gives an envelope Hessian Lipschitz constant of O(ρκ^{3/2}) without strong concavity.

Proof ancestry, which supplies tools but not this complexity:
- ECRN contributes the envelope, the curvature transfer (Proposition 3) and NewtonTrack.
- Nouiehed et al. (NeurIPS 2019) give differentiability of Φ under PL.
- Bellavia et al. give Newton convergence under error bounds.

**Lower bound and scope check.** ECRN Thm 18 gives Ω(Δ√ρκ^{3/4}ε^{−3/2}) for deterministic (∇f, ∇²f) algorithms when L ≥ 16μ and ε ≤ cL²/(ρκ^{3/2}). Its hard NC–SC instances are PL with the same μ, so the leading term here is optimal up to logarithms in that regime. I did not verify whether that bound also allows function-value queries.

Strict inclusion is confirmed by the example f = h(x) − Σᵢ q((Ay−Bx)ᵢ) with q(t) = t²/2 + 2(1−cos t). Let A be surjective with a nontrivial kernel and h bounded below with bounded second and third derivatives. I checked the following:
- q″(π) = −1, so the inner objective is not concave.
- |q′(t)| ≥ (1−2/π)|t| and q ≤ 3t²/2, which gives PL with μ = (1−2/π)²σ_min(A)²/3.
- |q″| ≤ 3 and |q‴| ≤ 2.
- The maximizers {Ay = Bx} are attained and nonunique.

**Search coverage (2026-10-27).** I searched arXiv, NeurIPS/AISTATS and the general web for second-order NC–PL minimax and PL-lower-level bilevel methods. Bi–Li–Hong–Zhang ([2606.20534](https://arxiv.org/abs/2606.20534)) treats only strongly convex lower levels. PROBE ([2609.30501](https://arxiv.org/abs/2609.30501)) certifies only lower-level second-order points. Zhang et al. ([2610.16771v2](https://arxiv.org/abs/2610.16771)) treats NC–SC with a first-order criterion. I did not read the second half of the ECRN HTML or the NC–SC Newton preprints 2606.07003 and 2602.14058.

The companion note's citations match what I checked. It omits ECRN's lower bound, which makes the leading term near-optimal rather than merely "preserved". Its "κ^{3/4} improvement" is against a reconstructed reduction, not a published theorem. The theorem was introduced in commit 331bbf8 (2026-10-27).

## Conclusion

**The rate is unchanged; the improvement is replacing strong concavity in y by a uniform PL inequality.**

The strongest baseline is ECRN (Zhou–Chen–Luo–Liu, Oct 2026), which proves the same guarantee only for strongly concave inner problems:

| | class | leading full-Hessian calls |
|---|---|---|
| ECRN | NC–SC | Õ(Δ√ρ (L/μ)^{3/4} ε^{−3/2}) |
| this result | NC–PL | O(Δ√ρ (L/μ)^{3/4} ε^{−3/2} · log²(·)) |

On the NC–SC overlap, this result is no faster. It is slightly worse in its initialization term (L/μ instead of √(L/μ)) and in logarithmic factors. On the larger class, ECRN's lower bound shows that the leading term cannot be improved for deterministic algorithms in the high-accuracy regime.

The gain is in scope. Inner problems may be nonconcave and have nonunique maximizers, and an explicit cosine-perturbed family confirms that such admissible instances exist. The only applicable published NC–PL guarantees I found are first-order (e.g., Smoothed-AGDA), and handling a singular inner Hessian is a real obstacle that I could not reduce to the strongly concave case.

Priority is less certain than the comparison. ECRN appeared only two weeks earlier, and I searched only public sources.

What can be claimed is the first second-order-stationarity guarantee for nonconvex–PL minimax that I found, at the near-optimal NC–SC rate.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
