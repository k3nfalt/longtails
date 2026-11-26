# Novelty review: Hessian reuse over stopped quadratic-model flows

[`result`](../../LongTails/Theorems/HessianReuseModelFlow.lean) proves the following. Take a C³ nonconvex `f` on a finite-dimensional Euclidean space with `‖D³f(x)‖ ≤ L₀ + L₁‖∇f(x)‖`, `f(x₀) − inf f ≤ Δ`, and separate exact gradient and Hessian oracles. The [algorithm](../../LongTails/Algorithms/HessianReuseModelFlow.lean) reuses one Hessian per block of `m` steps and follows the exact flow `e^{-tB}g` of the quadratic model until a speed or energy stopping rule fires. Its output satisfies `‖∇f(x_out)‖ ≤ ε` for every seed ([setup](../../LongTails/Setups/GradientDependentHessian.lean)). The updates use `L₀, L₁, ε, m`, and the horizon also uses `Δ`. The bound `G₀ ≥ ‖∇f(x₀)‖` appears in the setup, but neither the algorithm nor the proof uses it (`steps_accuracy` does not take it as an argument).

**Complexity.** Here `L₀ > 0` and `L₁ ≥ 0` are the absolute and relative third-derivative constants, `Δ` is the initial gap, `ε` is the target gradient norm, and `m ≥ 1` is the reuse length. The budget is `⌊C√m S⌋+1` gradients and `⌊CS/√m⌋+1` Hessians, where `S = Δ√(L₀+L₁ε)/ε^{3/2}` and `C = 9/(2√2)`. In O-form:

`N_g = O(1 + √m·Δ(√L₀ ε^{-3/2} + √L₁ ε^{-1}))`, `N_H = O(1 + Δ(√L₀ ε^{-3/2} + √L₁ ε^{-1})/√m)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fang–Marumo–Takeda, [arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741) (12 Jul 2026, preprint), Assumption 1, Thm. 2, Cor. 1 (Eq. 130), k₀ in Eq. 105. Same class. The method uses a fresh Hessian at every iteration, and its backtracking also uses function values. | Take δ large and `σ_init = L₀+L₁^{3/2}Δ`. Fang then needs `O(Δ(√L₀ε^{-3/2}+√L₁ε^{-1}) + log(2 + L₁G₀/(L₀+L₁^{3/2}Δ)))` gradients and the same number of Hessians, with trials counted. → At `m = 1`, this result needs `O(1 + Δ(√L₀ε^{-3/2}+√L₁ε^{-1}))` of each. | The additive `log G₀` term disappears. That matters only when `log(L₁G₀/(L₀+L₁^{3/2}Δ)) ≳ 1 + Δ√(L₀+L₁ε)ε^{-3/2}`, i.e. when `G₀` is exponentially large in `S`. For `m > 1`, the √m Hessian saving was already proved by EnergyHessianReuse (next row). | None: identical class | None. Both certify a point with `‖∇f‖ ≤ ε` deterministically. | Loses Fang's parameter-freeness: this result needs `L₀, L₁, Δ, ε`. Loses Fang's `λ_min ≥ −δ` guarantee. Gains: it needs no function values, and it does not need `G₀`. |
| Repository [EnergyHessianReuse](../../LongTails/Theorems/EnergyHessianReuse.lean), same setup and oracles (entered 2026-10-17) | Let `k = ⌈log(1+L₁G₀/(mL₀))/log(4/3)⌉` and `u, w` as below. Gradients `k + ⌈√m(27000u+15000w)⌉ + m + 74` → `⌊C√mS⌋+1`. Hessians `k + ⌈(54000u+30000w)/√m⌉ + 146` → `⌊CS/√m⌋+1`. Here `u = Δ√L₀ε^{-3/2}` and `w = Δ√L₁ε^{-1}`. | Uniformly no worse, since `S ≤ u+w`. Gradients improve from `O(m)` to `O(√mS)` when `S ≤ √m`. Hessians improve from `O(1 + log(1+L₁G₀/(mL₀)))` to `O(1)` when `m ≥ S²`. Weighted cost `N_g + mN_H` improves from `O(√mS + m(1+log(1+L₁G₀/(mL₀))))` to `O(√mS + m)`. | None | `G₀` is no longer needed. Little is gained, because one gradient call at `x₀` gives `G₀`. | None |
| Doikov–Chayti–Jaggi, [ICML 2023](https://proceedings.mlr.press/v202/doikov23a.html), [arXiv:2212.00781v3](https://arxiv.org/abs/2212.00781) Thm. 3 / Cor. 3.6. **Special case only**: uniform Hessian-Lipschitz `L` (`L₁ = 0`, `L = L₀`). | `O(√m√L₀Δε^{-3/2})` gradients and `O(√L₀Δε^{-3/2}/√m)` Hessians. The proof assumes `k` is a multiple of `m`, so there may be an extra `+m` gradients. → Same order. | None: same order, apart from that possible `+m` | Uniform Lipschitz Hessian → pointwise `L₀+L₁‖∇f‖` bound (already covered by EnergyHessianReuse) | None | Doikov needs only C² and also bounds the smallest Hessian eigenvalue (Eq. 15). |
| Chen–Liu–Luo–Zhang (NALEN), [arXiv:2501.17488v3](https://arxiv.org/abs/2501.17488), Thm. 4.1. **Special case only**: uniform `H`. I saw only a summary of the statement. | Weighted cost `O(m + m^{1/3}√HΔε^{-3/2})` → `O(m + √m Δ√(L₀+L₁ε)ε^{-3/2})` | Worse by `m^{1/6}` at `L₁ = 0`, `H = L₀`. Better on the intersection only when `H ≳ m^{1/3}(L₀+L₁ε)`. | Same as the row above | None | None beyond the class difference |

**Reduction check and mechanism.** The `G₀`-free bound does not follow by substitution. In both earlier analyses the `log G₀` term pays for adapting the cubic regularization to a possibly huge initial gradient. Here the energy cap `∫‖v‖² ≤ h` bounds `∫L₁‖∇f‖ dℓ` by `L₁h`, so each continuing step gains a decrease that does not depend on `‖g‖`. I could not find this stopping mechanism in prior work. The quadratic-model flow itself is classical (exponential-integrator and ODE trust-region steps; I did not verify the Behrman 1998 citation). Proof ancestry: Doikov et al. supply the lazy-block accounting and Fang et al. supply the class. The flow, its stopping rule and its error recursion are new here.

**Search coverage.** On 2026-11-25 UTC I searched arXiv, PMLR, and Optimization Online for lazy or reused Hessians and for `G₀`-free cubic or second-order methods under `(L₀,L₁)` Hessian smoothness. I checked these sources:
- Fang's Assumption 1. Its Cor. 1 and Eq. 105 I saw only as extracted summaries.
- Doikov's Thm. 3.
- Podorozhny, [arXiv:2608.22129v3](https://arxiv.org/abs/2608.22129): uniform `L_H` (Assumption 2.1).
- Agafonov et al., [arXiv:2609.32977v1](https://arxiv.org/abs/2609.32977) (26 Sep 2026): convex only, so not a competitor.

The Filho–Gonçalves PDF could not be parsed, so its uniform-Lipschitz assumption is taken from the companion note. The result entered on 2026-11-25 UTC (commit bfb95155), after all of these sources. The companion note's comparisons agree with what I checked.

**Conclusion**

**The rate is unchanged; the only established gain is dropping an additive logarithm in the initial gradient norm, plus much smaller constants.** The strongest baseline on the full class is the repository's own EnergyHessianReuse, which already gave the √m Hessian-reuse saving over Fang–Marumo–Takeda's fresh-Hessian cubic Newton. Charging each Hessian as m gradients:

| | weighted cost `N_g + m·N_H` |
|---|---|
| EnergyHessianReuse | `O(√m·S + m(1 + log(1 + L₁G₀/(mL₀))))` |
| This result | `O(√m·S + m)` |

The bound is uniformly no worse. It is strictly better only when `log(1+L₁G₀/(mL₀)) ≫ 1 + S/√m`. In that regime one Hessian is reused for the whole run (`m ≳ S²`), or `G₀` is exponentially large in `S`. Large `G₀` with fixed `Δ, L₀, L₁, ε` is admissible: the quadratic `Hx²/2` with large `H` gives `G₀ = √(2HΔ)`. Against Fang at `m = 1`, the same logarithm is all that is removed. In exchange the result requires known parameters and gives up Fang's second-order guarantee, but it needs no function values.

The comparison proves this gain. The literature search found no earlier `G₀`-free bound for this class, and the energy-capped stopping rule appears new. The gain is still an additive logarithm in an initialization quantity, and it matters only in extreme regimes. What can be claimed is a simpler, `G₀`-free Hessian-reuse bound with explicit small constants for gradient-dependent third-derivative bounds.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
