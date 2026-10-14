# Accelerated method under relative + absolute gradient error (strongly convex)

[`result`](../../LongTails/Theorems/AcceleratedInexactStronglyConvex.lean) proves the following. Take any L-smooth, μ-strongly convex f on a real Hilbert space, and any (possibly adversarial, call-dependent) oracle with ‖g − ∇f(x)‖ ≤ α‖∇f(x)‖ + δ, where 0 ≤ α < 1. The constant-parameter two-sequence method [`inexactAccelerated`](../../LongTails/Algorithms/InexactAccelerated.lean) uses only L, μ, α and x₀. Its last iterate x_N satisfies f(x_N) − f* ≤ ε for every oracle seed, provided 136δ² ≤ μ(1−α)²ε ([setup](../../LongTails/Setups/InexactGradientStronglyConvex.lean)).

**Complexity** (one oracle call per iteration). Here L is the smoothness constant, μ the strong-convexity constant, α the relative error, δ the absolute error and R ≥ ‖x₀ − x*‖:

  N = O( [ √(L/(μ(1−α))) + α²L/(μ(1−α)) ] · log(1 + LR²/ε) ),  valid for ε ≥ 136δ²/(μ(1−α)²).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Vasin–Gasnikov, [arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376) (Mar 2026, preprint), Thm 6.1, RE-AGM, composite noise; prior | O(max(√(L/μ), αL/μ)·log(LR²/ε)) with constant ≈ 900, valid only for ε ≳ min(√(L/μ), 1/α)·δ²/μ → O((√(L/μ) + α²L/μ)·log(1+LR²/ε)) for ε ≥ 136δ²/μ (α ≤ 1/3) | Factor min(α√(L/μ), 1/α) when √(μ/L) ≤ α ≤ 1/3, up to (L/μ)^{1/4} at α = (μ/L)^{1/4}. For δ > 0 it also covers ε ∈ [136δ²/(μ(1−α)²), min(√(L/μ),1/α)δ²/μ), which Thm 6.1 cannot certify | Accelerated range α ≤ 1/3 → α < 1. Beyond 1/3 the bound is no better than GD (see row 3) | None (both: last iterate, same information L, μ, α) | Floor grows like (1−α)⁻² as α → 1 |
| Vasin et al., [arXiv:2503.06628v3](https://arxiv.org/abs/2503.06628) (v3 Dec 2025, preprint), Thms 4–5, δ = 0; prior | ≈ 14√(L/μ)·log(LR²/ε) for α ≲ 0.016√(μ/L); ≈ 42αL/μ·log(LR²/ε) for α = (1/3)(μ/L)^{1/2−τ} → as above | √κ rate kept up to α ≈ (μ/L)^{1/4} instead of (μ/L)^{1/2}. Gain α√(L/μ) up to (L/μ)^{1/4}, then 1/α | Adds absolute error δ (VKK+25 covers δ = 0 only) | None | None found |
| GD with step 1/L, relative error (Polyak 1987 folklore; VG26 Thm 5.2 for composite/PL) | O(L/(μ(1−α²))·log(LR²/ε)) → as above | Gain when α ≲ 0.16 and L/μ is large, e.g. √(L/μ) vs L/μ at α ≤ (μ/L)^{1/4}. **Worse** by a constant factor (up to ≈ 64) for α ≳ 0.16 | GD (VG26 Thm 5.2) covers PL functions, a broader class | None | Selected result needs strong convexity |
| Gaucher–Dieuleveut–Hendrikx, [arXiv:2602.03329v1](https://arxiv.org/abs/2602.03329) (Feb 2026, preprint), Thm 3.3, α = 0 only | 4√(L/μ)·log(2LR²/ε), floor (1+√(L/μ))·3ζ²/(2μ) → 8√(L/μ)·log(1+2LR²/ε), floor 68ζ²/μ | For ζ²/μ ≲ ε ≲ √(L/μ)ζ²/μ: from no accelerated certificate (GD's L/μ) to √(L/μ) | Adds α > 0 | None | Constant 2× larger in the rate |

**Reduction check and proof ancestry.** I found no checked substitution or composition that gives the result. Cohen–Diakonikolas–Orecchia ([ICML 2018](https://proceedings.mlr.press/v80/cohen18a.html), Thm 6.4) avoid error accumulation only for zero-mean independent noise. Applying the Devolder–Glineur–Nesterov (δ,L,μ)-oracle reduction (VG26 Lemma G.1) inflates the floor by √κ. A strong-convexity ε-subgradient argument inside an A-HPE scheme recovers only the old α ≲ κ^{−1/2} threshold. One plausible competitor is unresolved. My rough sketch suggests that Catalyst with the relative criterion (C2) ([Lin–Mairal–Harchaoui, JMLR 2018, Prop. 8](https://arxiv.org/abs/1712.05654)) plus an inner GD loop driven by the inexact gradients could reach Õ(√κ + α²κ) with an extra inner-loop logarithm. I did not verify its inner error-floor analysis, and no published theorem states it. The proof mechanism (step 1/L cancels the cross term; a Young split of θ⟨e, w⟩ against the strong-convexity slack) is a modification of the RE-AGM two-sequence potential.

**Search coverage (2026-10-07).** I searched arXiv, PMLR and journal sources on relative/composite gradient error, inexact accelerated proximal methods and IQC robustness, and read the cited theorem statements. I did not read Devolder's thesis, Gannot's frequency-domain paper in full, or the IQC papers beyond their abstracts. The companion note's citations check out except one point: it attributes "≈900ακ" partly to VKK+25, whose Thm 5 gives ≈42ακ. That does not change the orders. VG26 Thm 10.1 claims an Ω(α²κ) lower bound. Its Appendix G applies a Devolder–Glineur–Nesterov lower bound, proved for the whole (δ,L,μ)-oracle class, to methods designed only for additive gradient noise. The α = 0 case of this theorem contradicts that step, so I treat the lower bound as unproved. The result was introduced in commit a3b7594 (2026-10-02), after all baselines. I found no subsequent work. The repository's [AcceleratedRelativeErrorConvex](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean) covers the convex class, which does not overlap this one.

## Conclusion

**Yes: under moderate relative error, the proved complexity is polynomially better than the best published accelerated bound.** The strongest prior baseline is RE-AGM ([VKK+25] Thm 5, [VG26] Thm 6.1), with κ = L/μ:

| α regime | previous (RE-AGM) | this result |
|---|---|---|
| α ≤ κ^{−1/2} | √κ·log | √κ·log (constant only) |
| κ^{−1/2} ≤ α ≤ κ^{−1/4} | ακ·log | √κ·log |
| κ^{−1/4} ≤ α ≤ 1/3 | ακ·log | α²κ·log |

For example, at α = κ^{−1/4} the gain is a factor κ^{1/4}. The result also adds accelerated guarantees for absolute error down to ε ≈ δ²/μ. Previous accelerated floors were about √κ·δ²/μ (or δ²/(αμ)), so in that accuracy range only GD's κ·log bound applied before.

It loses for α ≳ 0.16. There it has GD's order κ/(1−α), with a worse constant, so extending the range to α < 1 is not an improvement. Optimality is open: the cited Ω(α²κ) lower bound relies on a reduction that does not apply.

The comparison proves a gain over published theorems. Priority is less certain: a Catalyst-type reduction might give the same trade-off up to an extra logarithm, and I did not resolve that. The claimable contribution is a single-loop, log-free bound of order √κ + α²κ under composite gradient error, with a floor of order δ²/μ that has no √κ factor.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
