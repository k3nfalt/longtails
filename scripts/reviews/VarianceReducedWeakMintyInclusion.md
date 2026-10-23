# Novelty review: VarianceReducedWeakMintyInclusion

The [theorem](../../LongTails/Theorems/VarianceReducedWeakMintyInclusion.lean) covers a finite-sum inclusion `0 ∈ F(x)+A(x)`, with `F=(1/n)ΣFᵢ` and exact resolvents of monotone `A`. It assumes a graph weak-Minty solution for every `ρL<1` ([setup](../../LongTails/Setups/FiniteSumWeakMintyInclusion.lean)). Under these assumptions, the explicit snapshot/negative-momentum Picard method ([algorithm](../../LongTails/Algorithms/VarianceReducedWeakMinty.lean)) returns a uniformly selected pair `(Y,V)`. That pair satisfies `V∈A(Y)` a.s. and `∫‖F(Y)+V‖² dP ≤ ε²`, within a deterministic budget.

**Proved complexity.** Each component evaluation or resolvent counts as one call. The parameters are: `L`, the Lipschitz constant of the average `F`; `Λ ≥ L`, the mean-square component constant; `ρ`, the weak-Minty parameter; `R ≥ ‖x₀−x⋆‖`; and the accuracy `ε`. The budget in the Lean file is

  `N = O( log(2/(1−ρL))/(1−ρL) · min{ n(1 + L²R²/((1−ρL)²ε²)),  [n + Λ²/L² + (√n ΛL + Λ²)R²/((1−ρL)²ε²)]/(1−ρL)³ } )`,

and its universal constant is 2⁴² (explicit and conservative). The first branch is the deterministic method. The second branch is the new one. I write `δ=1−ρL` below.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Full-range deterministic: Alacaoglu–Kim–Wright, [ICML 2024, Thm 3.1/Cor 3.2](https://arxiv.org/abs/2402.05071), with `η=(2−δ)/(2L)` so `η−ρ=δ/(2L)`, `1−ηL=δ/2`; log-free version in Pethick–Mavrothalassitis–Cevher, [ICLR 2025, Cor 6.3](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf). Each `F` call costs `n`. | `O(n·log(2/δ)/δ·(1+L²R²/(δ²ε²)))` (AKW has an extra log in ε) → `N` above | Accuracy term `nL²R²/δ³` → `(√nΛL+Λ²)R²/δ⁶`. Speedup ≈ `min(√n δ³L/Λ, nδ³L²/Λ²)` when `n ≥ Λ²/(L²δ⁶)` and `L²R²/ε² ≳ δ⁻¹(1+Λ²/(nL²))`. Example: `δ=1/2`, `Λ=L`, `n→∞` gives `n·L²R²/ε² → √n·L²R²/ε²`. | None: same class (graph weak Minty, `ρL<1`, exact resolvent) | None. Both have certified graph residuals. A randomly selected iterate converts their best/average bound to this criterion. | Needs the mean-square constant `Λ`. Worse margin powers (`δ⁻⁶` vs `δ⁻³`), so the gain disappears for `n < Λ²/(L²δ⁶)`, where the exact fallback applies. |
| Restricted-range finite-sum VR: Tran-Dinh, [ICML 2025, Cor 4.2–4.3](https://arxiv.org/abs/2406.00937) (condition `Λρ<δ_TD` with `δ_TD<1/4` by its eq. (11)); Tran-Dinh–Nguyen-Trung, [arXiv:2603.15576v2 Cor 3.2–3.3](https://arxiv.org/abs/2603.15576) (`Λρ<1/(24√2)`, preprint, v1 Mar 2026) | `O(n + n^{2/3}Λ²R̂²/ε²)`, `R̂² ≥ R²` (counted as expected calls) → on their range (`δ≈1`): `O(n + Λ²/L² + (√nΛL+Λ²)R²/ε²)` (min with exact branch) | Uniformly no worse up to constants on the overlap, since `√nΛL ≤ n^{2/3}Λ²` and the exact branch covers `Λ²/L²>n`. Accuracy term gains a factor ≥ `min(n^{1/6}Λ/L, n^{2/3})`. | Their classes need `ρΛ < c` with a small constant `c`. This one needs only `ρL<1` (nested: theirs ⊂ this one). | Same criterion (squared graph residual, average/random iterate). Deterministic budget here vs. expected count (SAGA/L-SVRG) there. | Needs exact resolvents for every step size (they also use resolvents) and `Λ ≥ L` known. Larger logarithmic and constant factors. |
| *Special case only* (`A=0`, pairwise cohypomonotone `F`, `ρ` restricted): Cai–Alacaoglu–Diakonikolas, [ICLR 2024, Cor 4.5](https://arxiv.org/abs/2310.02987) | about `Õ(n + √n ΛR/ε)` for `ρ` bounded away from its limit (resolvent-residual criterion; ρ-constants not re-derived) → `O(n + Λ²/L² + (√nΛL+Λ²)R²/ε²)` | Worse on that overlap: `ε⁻²` vs `ε⁻¹` | Cohypomonotone, unconstrained → graph weak Minty with monotone `A`, full range | None | None beyond the narrower overlap; the special-case method wins there. |

**Reduction check.** There are two obvious compositions. One plugs a VR strongly monotone solver into each inexact-KM/proximal subproblem from AKW or Pethick et al. That pays a fresh `n`-call snapshot per outer step, giving `Õ((n+√nΛ/(Lδ))L²R²/(δ²ε²))`, which is no better than deterministic. The other batches the stochastic MLMC/ε⁻⁴ results ([AKW §4.2](https://arxiv.org/abs/2402.05071); [Alacaoglu–Kim, arXiv:2602.05531](https://arxiv.org/abs/2602.05531)). That needs a variance model the setup lacks and still scales as ε⁻⁴. Neither gives `√n·ε⁻²`. The mechanism that does is new to the checked literature: snapshot-relative inner Picard errors absorbed by a negative-momentum `p(1−p)‖x−w‖²` decrease, plus an epoch telescope. Its proof ancestry is the Pethick et al. corrected-proximal energy inequality and the Alacaoglu–Malitsky COLT 2022 negative-momentum idea. Both needed new coupling, which I checked in the companion note and the proof module names but did not re-derive line by line.

**Search coverage.** I searched on 2026-10-23 (UTC): arXiv, ICML 2024–2026, ICLR 2024–2025, and the Tran-Dinh line, reading the theorem statements cited above. [Alizadeh et al., arXiv:2405.10735v3, Cor 2](https://arxiv.org/abs/2405.10735) claims `O(n+Λ²/ε²)` under `ρ ≲ 1/(32Λ)`, for `E dist ≤ ε` at an existentially chosen iterate (a weaker criterion). That would beat this result on its restricted range. I did not verify its proof, and its journal version (OMS 2026) was not accessed. This matches the note's caveat. I found no discrepancy between the note's tuning and the Lean definitions. Repository results such as FullRangeSecondOrderWeakMinty concern different (second-order, deterministic) setups. The result was introduced in commit 34cad2c (2026-10-23).

**Conclusion**

**Yes: for many components, the proved total complexity beats the strongest full-range baseline.** That baseline is the deterministic corrected-proximal/inexact-KM bound (Pethick et al. ICLR 2025; AKW ICML 2024), which pays `n` per operator evaluation:

| | accuracy-dependent cost |
|---|---|
| deterministic, `ρL<1` | `n·L²R²/(δ³ε²)·log(2/δ)` |
| this result | `(√nΛL+Λ²)R²/(δ⁶ε²)·log(2/δ)` |

The gain is about `√n·L/Λ` at fixed margin `δ=1−ρL`. It survives when `n ≳ Λ²/(L²δ⁶)` and accuracy is fine enough to dominate the `(n+Λ²/L²)/δ⁴` startup. Near the boundary `δ→0` it loses to the deterministic method, which the theorem uses as its fallback.

The prior finite-sum variance-reduced weak-Minty methods (Tran-Dinh ICML 2025; Tran-Dinh–Nguyen-Trung 2026) need `ρΛ` below a small constant. On that overlap this bound is also no worse and improves `n^{2/3}` to `√n`. Accelerated cohypomonotone methods remain faster on their narrower class.

Uncertain: whether the disputed Alizadeh et al. claim is correct. It would affect only the restricted range, under a weaker criterion. No lower bound shows that the margin powers are tight. My search found no prior full-range `√n ε⁻²` result, but that does not prove priority. What can be claimed: the first checked amortized finite-sum guarantee over the full weak-Minty range, with a genuine `√n`-versus-`n` gain for large `n`, at the cost of worse dependence on `1−ρL`.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
