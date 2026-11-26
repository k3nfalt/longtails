# Novelty review: PointwiseHessianModelFlow

The [theorem](../../LongTails/Theorems/PointwiseHessianModelFlow.lean) proves the following for every C³ nonconvex `f` on `ℝ^d` with `‖∇³f(x)‖ ≤ L₀ + L₁‖∇f(x)‖`, `f(0) − inf f ≤ Δ` and `‖∇f(0)‖ ≤ G`: a deterministic method makes `⌊32S/3⌋ + 1` joint value/gradient/Hessian calls and returns a point with `‖∇f‖ ≤ ε`, where `S = Δ√(L₀+L₁ε)/ε^{3/2}`. The method is the [stopped quadratic-model gradient flow](../../LongTails/Algorithms/PointwiseHessianModelFlow.lean), and the public [setup](../../LongTails/Setups/PointwiseHessianStationarity.lean) additionally requires `G ≥ 16ε`, `S ≥ 2³⁹` and `d ≥ 2¹⁴⁰(1+⌈S⌉)⁴`. The supporting `success` lemma proves the bound on the unrestricted `broadSpec`.

**Complexity.** In joint second-order calls, with `Δ` the initial gap, `L₀, L₁` the third-derivative growth constants, `ε` the target gradient norm and `G` the initial gradient bound (which does not appear):
`O(1 + Δ√L₀/ε^{3/2} + Δ√L₁/ε)`.
This holds for `L₀, L₁ ≥ 0` with `L₀ + L₁ > 0`. The method needs to know `L₀`, `L₁` and `ε`. The matrix exponential, the integrals and the first-zero stopping time are computed exactly and for free.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fang–Marumo–Takeda, [arXiv:2607.10741v1](https://arxiv.org/abs/2607.10741) (12 Jul 2026, preprint), Thm 2 / Cor. 1, Eqs. (105), (130); same Assumption 1(a). The algorithm does not use δ, so δ→∞ gives a first-order bound. | `O(1 + Δ√L₀/ε^{3/2} + Δ√L₁/ε + log(1 + L₁G/(L₀+L₁^{3/2}Δ)) + [log((L₀+L₁^{3/2}Δ)/σ_init)]₊)` → `O(1 + Δ√L₀/ε^{3/2} + Δ√L₁/ε)` | Removes the additive `log(L₁G)` term (and the `σ_init` term). The gain is real only when `log(1 + L₁G/(L₀+L₁^{3/2}Δ)) ≫ Δ(√L₀/ε^{3/2} + √L₁/ε)`. In the public regime `S ≥ 2³⁹` this needs `G` of order `exp(2³⁹)`. | None. `L₀ = 0` follows from their bound by taking `L₀ → 0⁺`. | None. Theirs is parameter-free; this method needs `L₀`, `L₁`. | Loses their δ-second-order stationarity and parameter-freeness. Exact matrix-exponential and first-zero computation, versus their inexact cubic subproblem. |
| Gratton–Jerad–Toint, [arXiv:2505.04807v2](https://arxiv.org/abs/2505.04807) (EJCO 2026), Thm 2.5; Jerad, [arXiv:2606.30225](https://arxiv.org/abs/2606.30225), Thm 3.1 (p=2). Two-point local condition `‖∇²f(y)−∇²f(x)‖ ≤ (L₀+L₁‖∇f(x)‖)‖x−y‖` for `‖x−y‖ ≤ δ`, plus extra curvature bounds. | `O(Δ C ε^{-3/2}|log ε| + log G)`, where `C` combines `√(L₀+L₁)` with `δ`- and algorithm constants and has no `√L₁/ε` split → `O(1 + Δ√L₀/ε^{3/2} + Δ√L₁/ε)` | Removes a `|log ε|` factor and the `log G` term. Separates the `L₁` dependence into `Δ√L₁/ε`. | Incomparable classes: their condition implies a local pointwise bound but adds an `AS.4` curvature bound; the pointwise class is strictly weaker than the global two-point condition (FMT Examples 1–2). | Theirs is adaptive in `L₀`, `L₁`. | Same tradeoffs as above. |
| Repository [PointwiseHessianStationarity](../../LongTails/Theorems/PointwiseHessianStationarity.lean) (2026-11-17), same `spec` | `⌈10⁵S⌉ + 2⌈log(1+L₁G/(L₀+L₁ε))/log(4/3)⌉ + 200` → `⌊32S/3⌋ + 1` | Removes the `log G` term; the constant changes from `10⁵` to `32/3`. | None | None (both use a deterministic stopped iterate) | None |

At `L₁ = 0`, cubic regularization ([Nesterov–Polyak 2006](https://doi.org/10.1007/s10107-006-0706-8), Thm 1) already gives `O(1 + Δ√L₀/ε^{3/2})` with no dependence on `G`.

**Reduction check and mechanism.** I could not get the G-free bound by substitution into the theorems I checked. In FMT, the `4L₁‖g₀‖` term enters `k₀` through Lemma 5 regardless of how `σ_init` is chosen. A known-parameter cubic or trust-region step with regularization `∝ L₀ + L₁‖g_k‖` might also avoid it, but I found no such published theorem, so this possibility is unchecked. The new mechanism is the energy cap. It bounds the Hessian drift by `(L₀+L₁E)ℓ + L₁U` with `U ≤ h`. Each step therefore decreases `f` by at least `3h/4` however large `‖g‖` is, and when the model-gradient threshold is hit, the endpoint is certified stationary without another call. The quadratic-model flow itself is classical (Behrman 1998); the stopping rule and its analysis are what is new here.

**Search coverage.** I searched on 2026-11-25 (UTC): arXiv and the web for second-order and tensor methods under (L₀,L₁)-type Hessian or third-derivative growth. I read the FMT and Gratton–Jerad–Toint statements. Agafonov et al. ([arXiv:2609.32977](https://arxiv.org/abs/2609.32977), subsequent) is convex with a function-gap criterion, so it is not comparable. I did not read Semenov–Jaggi–Doikov ([ICLR 2026](https://arxiv.org/abs/2506.13710)), whose condition is different, or the full text of Xie et al. (AAAI 2024). The companion note's citations and its formula for `k₀` agree with FMT.

## Conclusion

**The rate is unchanged; the only gain is removing an additive logarithm in the initial gradient norm.** The strongest baseline is Fang–Marumo–Takeda's parameter-free cubic Newton method, which works under exactly the same pointwise third-derivative assumption:

| | joint oracle calls to `‖∇f‖ ≤ ε` |
|---|---|
| FMT (Cor. 1, δ → ∞) | `O(1 + Δ√L₀/ε^{3/2} + Δ√L₁/ε + log(1 + L₁G/(L₀+L₁^{3/2}Δ)))` |
| This result | `O(1 + Δ√L₀/ε^{3/2} + Δ√L₁/ε)` |

The gain appears only when that logarithm dominates, i.e. when `G` is exponentially large in `Δ(√L₀/ε^{3/2} + √L₁/ε)`. This regime is admissible: steep quadratics `M(x−a)²/2` keep `Δ` fixed while `G → ∞`. The improvement compares proved upper bounds; FMT's method is not shown to need those extra calls. Within the repository, the result makes the order match with the paired lower bound uniform in `G`, though only in the very high-dimensional public regime.

The price is giving up what FMT also provide: second-order stationarity, no knowledge of `L₀, L₁`, and inexact subproblems. The energy-capped stopping rule looks new, but my search does not establish priority. A known-parameter cubic or trust-region step might also avoid `log G`, and I have not checked that. What can be claimed is a G-independent, constant-explicit first-order bound for this class, which improves a lower-order additive term.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
