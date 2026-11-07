# Novelty assessment: ε⁻² stochastic complexity for χ²-constrained convex DRO

[`result`](../../LongTails/Theorems/ChiSquareBracketedDro.lean) states the following. Take a general population law `P₀` on any measurable space, a closed convex `X` in a Hilbert space, and losses that are convex, lie in `[0,B]`, and have subgradients bounded by `G`. Then [`bracketAlgorithm`](../../LongTails/Algorithms/ChiSquareBracket.lean) makes a deterministic number of i.i.d. calls to an oracle returning (projection, loss, subgradient). It returns a point `x̂ ∈ X` with `E[L(x̂)] − L(x⋆) ≤ ε`, where `L(x) = sup{E_{P₀}[wℓ(x;ξ)] : w ≥ 0, E w = 1, ½E(w−1)² ≤ ρ}` ([setup](../../LongTails/Setups/ChiSquareConstrainedDro.lean)). The point `x̂` is the bracket average with the lowest estimated objective.

**Proved budget, simplified.** Here `ρ>0` is the χ² radius, `G` the Lipschitz bound, `B` the loss range, `R ≥ ‖x₀−x⋆‖`, and `ε` the expected objective accuracy.

```
N = O( log²(2 + (1+ρ)B/(√ρ ε)) · [1 + (1+ρ)G²R²/ε² + (1+ρ)²B²/(ρ ε²)] )
```

To obtain this, I used `√(1+2ρ)(1+ρ^{-1/2}) ≤ 2(1+ρ)/√ρ` in the logarithm and `(1+ρ)(1+1/ρ) = (1+ρ)²/ρ` in the `B²` term.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Levy–Carmon–Duchi–Sidford, NeurIPS 2020, **Thm 4** ([arXiv:2010.05893](https://arxiv.org/abs/2010.05893), v2 Dec 2020). This is a direct competitor on the same population setup. | `(GR)²(ρB + ε log(B/ε)) ε⁻³ log²(1+ρB/ε²)`, valid for `ε<B` → `N` above | **ε⁻³ → ε⁻²**. For `ρ ≥ 1` the gain needs `ε ≲ G²R²B/(G²R²+B²)`; at `GR = B` the speedup is ≈ `B/ε` up to logs. For `ρ ≤ 1` the result is no worse when `ρ ≳ min{B²/(G²R²), √(εB)/(GR)}`. | `diam X ≤ R` → only `‖x₀−x⋆‖ ≤ R`. This is minor; the class is otherwise the same. | Levy et al. select the index by a sketched estimation step (text after Thm 4) and give a high-probability bound on a random number of calls. This result gives a fully proved selection with a deterministic budget. The output type, an expected gap of the selected point, is the same. | **Worse as ρ→0.** The `B²/(ρε²)` term blows up, while Levy's bound tends to `G²R² log(B/ε)/ε²`. Levy is better when `ρ ≪ min{B²/(G²R²), √(εB)/(GR)}`. For `ρ ≥ 1`, the bounds cross at `ε ≍ G²R²B/(G²R²+B²)`; the result does not improve on Levy at larger `ε`. |
| Carmon–Hausler, NeurIPS 2022, nonsmooth f-divergence bound (§4; [arXiv:2203.13225](https://arxiv.org/abs/2203.13225)). *Special case: empirical `P₀` on `N₀` atoms only.* | `Õ(N₀(GR/ε)^{2/3} + (GR/ε)²)`, independent of ρ, with constant success probability → `N` above | On that overlap this result wins only if `N₀ ≫ (1+ρ)(G²R²+B²(1+1/ρ))/(G²R²)^{1/3}ε^{4/3}`, up to logs. Otherwise Carmon–Hausler is better, by up to a factor of `ρ` when `ρ ≫ 1`. | Finite support → general `P₀`. This covers population objectives that a finite-sum method cannot access. | None | Carmon–Hausler need no bounded loss. Their reduction from the constraint to the penalty (App. D.2) was not verified. |
| Duchi–Namkoong subsampling plus a full-batch or cutting-plane method (Levy Table 1; Levy §8 remark). *Requires dimension `d < ∞`.* | `ρ²dε⁻⁴` (subgradient), or roughly `ρ²d²ε⁻²` (cutting plane, a sketch rather than a theorem) → `N` above | Dimension-free. The gain is a factor `≈ ρd²` against the cutting-plane sketch when `ρ ≥ 1` and `GR ≍ B`. | `d < ∞` → infinite-dimensional Hilbert `E` | None | Not comparable as rigorous bounds, since the `d²` figure is not a theorem. |

**Reduction check and proof ancestry.** I checked the obvious reductions, and none gives ε⁻². Bracketing the penalty multiplier λ inherits the `λ⁻¹ε⁻²` penalized cost at `λ ≍ ε/ρ`, which is Levy's ε⁻³. SGD on the perspective dual with a floor `s ≥ ε` has subgradient bound `∝ 1/ε`, which gives ε⁻⁴. Two-level compositional SGD with a √· made Lipschitz by a floor is also slower than ε⁻².

The new mechanism is the self-bounding inequality `s(x,η)² ≤ 2s² + (4s/c)(Φ−L⋆)`, used inside the brackets `[sⱼ,4sⱼ]`. With it, the unbounded noise is absorbed by the descent term. The rest of the proof uses standard ancestry: the joint dual and perspective form (Levy App. A.1.2) and SGD under noise bounded by `A + K·(suboptimality gap)`.

Jia–Lan–Zhang ([arXiv:2407.15368](https://arxiv.org/abs/2407.15368), v1 Jul 2024) treat a related √-moment objective. Theirs is the mean-upper-semideviation `L_p` risk with a nested mean, not the χ² ball. I verified no reduction in either direction.

**Search coverage (2026-11-07).** I searched arXiv, NeurIPS, AAAI, Math. Programming, and general web results from 2016 to 2026. I read the Levy et al. PDF text directly, including Thm 4, §6 and §8. Carmon–Hausler, Im–Grigas (finite support, feasibility), Zhang et al. AAAI 2024 (nonconvex, stationarity, ≈ε⁻¹¹ for χ²), and Jia–Lan–Zhang I read only partly, through HTML or summaries. I could not access Zhu–Gürbüzbalaban–Ruszczyński (Math. Program. 2025).

I found no later work closing Levy's stated gap. The result was introduced in commit `85ee5131` on 2026-11-07, so every source above predates it.

Checks on the companion note:
- Its regime claims match my derivation.
- It cites Duchi–Namkoong Thm 6 for the `Ω(ρε⁻²)` lower bound. I did not verify that theorem number or how the bound transfers, so this report makes no optimality claim.
- Its claim that Levy's display drops `B²` terms is also unverified.

## Conclusion

**Yes: for moderate and large ρ, the proved complexity for χ²-constrained convex DRO over a general population improves from ε⁻³ to ε⁻² (up to log²).** The baseline is Levy et al.'s Theorem 4. Levy et al. themselves list closing this gap as open in §6 and §8.

```
Levy et al.:  (GR)²(ρB + ε log(B/ε)) ε⁻³ · log²
This result:  [(1+ρ)G²R² + (1+ρ)²B²/ρ] ε⁻² · log²
```

For `ρ ≥ 1` and `GR = B`, the speedup is about `B/ε`. The result loses when `ρ ≪ min{B²/(G²R²), √(εB)/(GR)}`, because the `B²/ρ` term grows while Levy's bound approaches the ERM cost. On finite-support `P₀` with few atoms, Carmon–Hausler's ρ-free `N₀ε^{-2/3} + ε⁻²` bound can be better. That restriction to few atoms is not part of this setup.

What the comparison establishes is the regime-specific gain above. Separately, the search found no prior or later ε⁻² guarantee for this population problem; that supports priority but does not prove it. The proof mechanism, self-bounded perspective noise inside geometric brackets, does not follow from the standard reductions I checked. Optimality in ρ is plausible but rests on a lower bound I did not verify.

The claimable contribution is the first ε⁻²·log² stochastic-subgradient complexity known to me for χ²-ball DRO with general `P₀`. It is not uniform: it holds for ρ bounded away from 0, with a `B²/ρ` loss as ρ→0.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
