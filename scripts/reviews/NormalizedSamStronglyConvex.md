# Novelty review: NormalizedSamStronglyConvex

The theorem ([theorem](../../LongTails/Theorems/NormalizedSamStronglyConvex.lean), [setup](../../LongTails/Setups/NormalizedSamStronglyConvex.lean), [algorithm](../../LongTails/Algorithms/NormalizedSam.lean)) proves the following. For a differentiable, L-smooth, μ-strongly convex f on a complete real inner-product space (any dimension) with exact gradient oracle and f(x₀)−f⋆ ≤ Δ, deterministic normalized SAM with fixed radius ρ and step η = 1/(2L+2L²ρ/√(με)) returns its **last iterate** x_K with f(x_K)−f⋆ ≤ ε after 2K gradient calls. The run uses two calls per step and no function values. Here `allowedAlgorithm` enforces these updates and the last-state output for some η>0, and the theorem supplies that η.

**Proved budget.** κ = L/μ is the condition number, ρ is the SAM radius, Δ is the initial gap, and ε is the target accuracy:

$$
N_{\text{SAM}} = 2\Big\lceil\Big(\tfrac{2L}{\mu}+\tfrac{2L^2\rho}{\mu^{3/2}\sqrt{\varepsilon}}\Big)\log(1+\Delta/\varepsilon)\Big\rceil
= O\!\Big(\big[\kappa+\kappa^{3/2}\rho\sqrt{L/\varepsilon}\big]\log(1+\Delta/\varepsilon)\Big),
$$

with N = 0 when Δ = 0. The engine is [`output_gap`](../../LongTails/Proofs/SamStrongConvex.lean): for every 0 < η ≤ 1/(2L), gapₜ ≤ max{(1−μη)ᵗΔ, 4η²L⁴ρ²/μ}.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Si–Yun, NeurIPS 2023, [arXiv:2306.09850v3](https://arxiv.org/abs/2306.09850), Thm 3.1, App. B.2 eq. (6); same normalized SAM, same class (prior) | Eq. (6): min_t gap ≤ (1−ημ)ᵀΔ + η²L⁶ρ²/(2μ³) for η ≤ 1/(2L). Retuning with η = min{1/(2L), μ^{3/2}√ε/(L³ρ)} gives O([κ + κ^{5/2}ρ√(L/ε)] log(1+Δ/ε)) → O([κ + κ^{3/2}ρ√(L/ε)] log(1+Δ/ε)) | Radius term drops by a factor κ. The speedup is Θ(min{κ, 1+κ^{3/2}ρ√(L/ε)}), so it is non-trivial iff ρ ≫ √(εμ)/L·κ^{-1}; it is a full factor κ when ρ ≥ √(εμ)/L. With ρ = 0 or κ = O(1), the bounds have the same order | None (identical class) | Best iterate → last iterate. A gradient-norm-selected iterate can already be certified from Si–Yun's proof with only an O(log κ) loss, so this output gain is modest | None for SAM |
| Gradient descent, η = 1/L; descent lemma + PL (Karimi–Nutini–Schmidt, ECML 2016, Thm 1) (prior, textbook) | O(1 + κ log(1+Δ/ε)) → N_SAM | **Worse**: N_SAM ≥ GD bound in every regime, strictly worse by κ^{3/2}ρ√(L/ε)·log when ρ > √(εμ)/L | None | None (both last iterate, gradient-only) | SAM pays 2 calls per step plus the radius term |
| Nesterov AGD, constant momentum (Nesterov, *Lectures on Convex Optimization*, 2018, §2.2) (prior) | O(1 + √κ log(1+Δ/ε)) → N_SAM | **Worse** by a factor ≥ √κ in every regime | None | None (last iterate) | — |

**Reduction check and mechanism.** Plugging bounded perturbation error (‖e‖ ≤ Lρ) into GD gives only a non-vanishing L²ρ²/μ floor. The κ gain instead comes from a sharper use of cocoercivity coupling g with its own perturbation, ‖e‖² ≤ (Lρ/‖g‖)⟨g,e⟩, together with a max-type contraction induction. Si–Yun's case split supplies the proof template, and the gain is a refinement of their threshold ηL³ρ/μ to ηL²ρ. The companion note's nonlinear cycle lower bound, Ω(η²L⁴ρ²/μ) at fixed small η, is a supporting lemma. It is not part of the public theorem and was not assessed as a deliverable.

**Search coverage (2026-10-16 UTC).** I re-read Si–Yun Thm 3.1/3.2 and App. B.2 from the arXiv v3 PDF. I also ran web searches for 2023–2026 normalized-SAM strongly convex analyses, which surfaced Dai–Ahn–Sra (NeurIPS 2023) and [Oikonomou–Loizou](https://arxiv.org/abs/2503.02225) (ICLR 2025, PL/nonconvex), and no κ-improved deterministic bound. I did not re-read the companion note's other citations or the Nesterov/Karimi theorem texts in this session; those two are standard. The note's comparisons agree with the Lean statement and with Si–Yun's stated bound, and the note itself concedes that GD and AGD are better for this class. The result was introduced in commit 8ac6796 (2026-10-15).

## Conclusion

**No optimization advantage: this is a sharper analysis of SAM, which remains slower than plain gradient descent on the same problem.**

Under the full setup (L-smooth, μ-strongly convex, exact gradients, objective-gap accuracy):

| Method | Gradient calls |
|---|---|
| Si–Yun SAM analysis (best iterate) | [κ + κ^{5/2}ρ√(L/ε)] log(1+Δ/ε) |
| This SAM analysis (last iterate) | [κ + κ^{3/2}ρ√(L/ε)] log(1+Δ/ε) |
| Gradient descent | κ log(1+Δ/ε) |
| Nesterov AGD | √κ log(1+Δ/ε) |

Compared with Si–Yun's analysis of the same method, the radius term improves by a factor κ, a full-factor gain once ρ ≥ √(εμ)/L, and the output becomes the last iterate. This is a real improvement in what is proved about normalized SAM. I found no prior or later paper that already gives it, but a targeted search does not establish priority.

For the problem the theorem certifies, minimizing f to accuracy ε, GD already needs no more calls in every parameter regime and AGD needs √κ times fewer. SAM's motivation (flat minima, generalization) is not represented by this accuracy criterion. Following the repository's negative examples, a better method-specific bound that remains dominated by standard methods does not count as an improvement.

The claimable contribution is a κ-factor sharper, last-iterate convergence bound for constant-radius normalized SAM on smooth strongly convex functions. It is not a better optimization guarantee.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
