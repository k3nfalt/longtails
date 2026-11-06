# Novelty assessment: StochasticRegularEqualityKkt

[`result`](../../LongTails/Theorems/StochasticRegularEqualityKkt.lean) proves the following for the [setup](../../LongTails/Setups/StochasticRegularEqualities.lean) and the [algorithm](../../LongTails/Algorithms/StochasticEquality.lean). Take min f(x) subject to c(x)=0 on ℝ^d, where the objective f, the constraints c, and the Jacobian J are all observed only through noisy samples. Then a deterministic number of shared-sample oracle calls returns a point and multiplier (X, λ̂) with 𝔼[‖∇f(X)+Dc(X)*λ̂‖² + ‖c(X)‖²] ≤ ε².

**Parameters.** L_f, L_J are the Lipschitz constants of ∇f and J. L_c bounds ‖J‖_HS. ν > 0 is a uniform smallest singular value of J, assumed on all of ℝ^d. Δ bounds the initial objective gap f(x₀) − inf f, and C₀ bounds ‖c(x₀)‖. σ² is the joint variance of the triple (∇f, c, J) estimates. L_noise is the mean-squared smoothness of the oracle when the same sample is used at two points. The accuracy satisfies 0 < ε ≤ 1. One call returns one triple. Write Σ := 2+L_f+L_c+L_J+ν+ν⁻¹+Δ+C₀+L_noise; this is only shorthand for that literal sum. The proved budget is then

> N = O( [Σ³⁸ + Σ⁴⁸σ²(1+log(Σ/ε)) + Σ⁶⁰σ/ε] · (1+log(Σ/ε)) / ε² ).

With the geometry fixed, this is Õ(ε⁻² + σε⁻³ + σ²ε⁻²).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Cui–Shi–Wang–Xiao, Fletcher AL, [arXiv:2606.28230v1](https://arxiv.org/abs/2606.28230) (26 Jun 2026, prior), Thm 4.2 / Cor 4.1. *Applies only if every iterate stays in a region 𝒳 where ∇f and c are bounded, and the Hessians are Lipschitz.* | Stated: 𝔼[#calls] = O(ε⁻³), counted per oracle. From its (4.8)–(4.11) I get ≈ ε⁻² + (σ²+L²)ε⁻³ with constants not expanded → O(ε⁻² + σε⁻³ + σ²ε⁻²), up to log factors and Σ-powers. | Fixed σ: none, same ε⁻³ order, and this result is worse by a log factor and by Σ⁶⁰. The σε⁻³ form beats the *stated* bound when σ ≪ 1, but retuning its epoch length (τ ≍ σ/ε, a standard SPIDER choice) likely recovers it. That retuning is unverified and earns no credit. | Lipschitz Hessians of f and c → only C^{1,1}. Pathwise containment in a region with ‖∇f‖ ≤ G and ‖c‖ ≤ M → none. Under global strong LICQ, c is onto ℝ^m and so unbounded, so their 𝒳 cannot be the whole space and the containment cannot be checked in advance. | Expected oracle count → deterministic worst-case count. 𝔼‖·‖ → 𝔼‖·‖², with an explicit multiplier returned (this implies their criterion). Both use a randomly selected iterate, not the last one. | Strong LICQ, the Jacobian bounds, and the oracle moments are required on all of ℝ^d, not just on 𝒳. The uniform variance bound rules out random-matrix linear constraints A(ω)x−b. The Σ-polynomials are enormous. |
| Cui et al., exact penalty, [Optimization Online, 6 Nov 2025](https://optimization-online.org/wp-content/uploads/2025/11/Fully_Sto_DLA-8.pdf) (prior), Thm 4.1. *Applies only with containment (Assumption 1.1) and singular values of the estimated Jacobians bounded below at outer iterates (Assumption 4.1).* | O(ε⁻³) gradient/Jacobian calls plus O(ε⁻⁵) constraint-value calls → Õ(ε⁻²+σε⁻³+σ²ε⁻²) joint triples | Fixed σ: ε⁻⁵ → ε⁻³ in triple units, conditional on overlap. | Same containment removal as above. Also removes an assumption on the algorithm's own random estimates. | Expected norm → expected squared norm | Same global restrictions as above. Lipschitz Hessians are not needed by either paper. |
| Alacaoglu–Wright, [AISTATS 2024](https://proceedings.mlr.press/v238/alacaoglu24a.html) ([arXiv v1](https://arxiv.org/abs/2311.00678)), Thm 3.1, case III. *Assumes c and ∇f are bounded on X (A4).* | Õ(ε⁻⁵) → Õ(ε⁻²+σε⁻³+σ²ε⁻²) | Fixed σ: ε⁻⁵ → ε⁻³, but only on an overlap, which is empty when X = ℝ^d (A4 contradicts global LICQ). | Bounded c and ∇f → unbounded allowed. | None (both use a random iterate) | Their theorem also allows a projection onto a closed convex set X, and needs their regularity condition (A5) only along the iterates. |

**Reduction check.** Plugging the C^{1,1} instances into Cui et al. through Gaussian smoothing at radius h ≍ ε still needs the containment assumption, and the note's own calculation gives fixed-σ order ε⁻³. So the fixed-noise rate itself is not new. What is new is avoiding second derivatives through a finite-difference Fletcher-merit argument, plus a localization argument (coercivity of the merit function) that replaces the containment assumption. Proof ancestry: Fletcher's augmented Lagrangian, SPIDER/STORM recursions, and median-of-means validation. None of these supplies the localization step.

**Search coverage.** Searched on 6 Nov 2026 UTC: arXiv, Optimization Online, and AISTATS/ICML/NeurIPS on fully stochastic equality constraints. I read the Cui 2026 HTML (Sections 1–4), the Cui 2025 PDF, and the Alacaoglu–Wright HTML v1 (Section 3; the appendices only partly). I also checked Shi–Wang [arXiv:2511.03210](https://arxiv.org/abs/2511.03210): its fully stochastic rate is Õ(ε⁻⁶), which is weaker. I did not check proceedings versions of the 2025/2026 preprints. The theorem was introduced in commit f996c91e on 6 Nov 2026, so all three baselines are prior. The companion note's account of these baselines agrees with what I checked. Its extra smoothing-reduction exponent gain, ε^{−(3−a)} vs ε⁻³ for σ = ε^a, compares against a reduction the note constructed itself, not a published bound. No repository result overlaps.

## Conclusion

**The rate is not better; the gain is dropping the second-order and containment assumptions while keeping the ε⁻³ cost.**

The strongest baseline is Cui–Shi–Wang–Xiao (2026), and both results reach the same fixed-noise order:

| | assumptions | calls |
|---|---|---|
| Cui et al. Thm 4.2 | Lipschitz Hessians; iterates assumed to stay in a region with bounded ∇f, c | 𝔼 N = O(ε⁻³) |
| this result | C^{1,1} only; no containment assumption; global LICQ | N = Õ(ε⁻²+σε⁻³+σ²ε⁻²)·poly(Σ) |

Where both apply, this result is never faster at fixed σ: it loses a logarithm and carries geometry factors up to Σ⁶⁰. Its better σ-interpolation probably follows from retuning the prior method's epoch length.

The substantive advance is in scope. Prior fully stochastic guarantees assume that the algorithm's own iterates stay where ∇f and c are bounded. Under global strong LICQ, c is unbounded, so that assumption never covers the whole space and cannot be checked before running the method. This theorem proves the localization instead and needs no Hessians. Its costs are uniform LICQ and global oracle bounds on all of ℝ^d, which is a different, incomparable restriction. The count is also deterministic rather than in expectation, and accuracy holds in mean square.

What can be claimed: the first checked ε⁻³ guarantee for fully stochastic equality constraints that needs neither Hessian smoothness nor an assumed region containing the iterates, with no rate gain. Priority rests on a search of preprints from the last year.

The verdict is limited for two concrete reasons. First, the new class does not contain the old one: global LICQ excludes every problem with a compact or bounded constraint set. Second, the rate is not improved on the overlap, and the constants are very large.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
