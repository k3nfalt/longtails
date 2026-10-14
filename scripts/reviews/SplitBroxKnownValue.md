# SplitBroxKnownValue: what is actually new?

The [theorem](../../LongTails/Theorems/SplitBroxKnownValue.lean) ([setup](../../LongTails/Setups/KnownValueSmoothConvexLocalLinear.lean), [algorithm](../../LongTails/Algorithms/SplitBrox.lean)) gives the following guarantee. The setup is a closed convex set `C` in a real Hilbert space, an objective that is convex and `L`-upper-quadratic on `C`, and a known optimal value `f⋆`. Two exact oracles are available: value plus gradient, and a point-only local linear oracle `argmin{⟨g,v⟩ : v ∈ C, ‖v−x‖ ≤ r}`. With these, the fixed-budget SplitBrox method returns a feasible **last primal iterate** with `f(y_K) − f⋆ ≤ ε` for every oracle seed and tie-breaking rule.

**Complexity (value-gradient plus local-linear calls):**
`N = 3(⌈√(10LR²/ε)⌉ + 1) = O(1 + √(LR²/ε))`.
Here `L` is the smoothness constant on `C`, `R ≥ ‖x₀ − x⋆‖`, and `ε` is the objective accuracy. The algorithm receives `L`, `R`, `ε`, `x₀` and the **exact** `f⋆`. There is no logarithmic factor, and `R = 0` is allowed. The setup permits any algorithm with the stated information and oracle access. The theorem proves existence by constructing SplitBrox with explicit tuning; the last-primal output belongs to that construction, rather than being imposed by `allowedAlgorithm`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Richtárik–Gruntkowska–Li, [BroxGD](https://arxiv.org/abs/2605.08850) (v1 May 9 2026, v2 Sep 28 2026, preprint), Thm 3.2(ii) and Cor. D.2: same oracle, radius `R/√K` | `O(1 + LR²/ε)` → `O(1 + √(LR²/ε))` | Factor `√(LR²/ε)` whenever `LR²/ε ≥ 1` | `L`-Lipschitz gradient on an open neighborhood of `C` → upper and lower models on `C` only (minor) | Best iterate → last iterate | Needs exact `f⋆` and `L`; BroxGD needs neither (only `R` and `K`) |
| Same paper, Thm 3.5 (Polyak radius, `f⋆` known, same information) | Average iterate `O((‖∇f(x⋆)‖+LR)²R²/ε²)` → `O(1 + √(LR²/ε))` | Polynomial: `ε⁻²` → `ε⁻¹ᐟ²`, and no `‖∇f(x⋆)‖` term | None | Averaged → last iterate | Needs `L` and `R`; Thm 3.5 needs neither |
| Deng–Lan–Lin, [APMM](https://arxiv.org/abs/2412.06319) (v3 Apr 2026, accepted to INFORMS J. Comput.), Alg. 1 and Thm 2.1 (`ρ=1`, `X_k = X`) | `O(1 + √(LR²/ε))` exact projections onto `C ∩ {cut}` → same order in local-LMO calls | Not comparable: different oracle | Projection onto `C` intersected with a halfspace → point-only local LMO | APMM needs no `L` or `R`; it uses a monotone value-selected output, while this result returns the last iterate | Loses parameter-freeness (needs `L` and `R`) |
| Lan–Zhou, [CGS](https://optimization-online.org/2014/10/4605/) (SIAM J. Optim. 26, 2016), smooth case. *Special case: bounded `C` with diameter `D`; a global LMO is the local oracle with `r ≥ D`* | `O(√(LD²/ε))` gradient + `O(LD²/ε)` LMO calls → `O(1 + √(LR²/ε))` | On bounded `C`: factor `√(LD²/ε)` in linear-oracle calls (`R ≤ D`) | Bounded `C` → unbounded `C` allowed | None | Needs `f⋆`; uses the stronger local oracle instead of a global LMO |

**Reduction check and proof ancestry.** By KKT, the exact cut projection used by APMM, `P_{C∩{ℓ ≤ f⋆}}(x)`, is a local-LMO reply at one unknown radius ([Richtárik–Mahran](https://arxiv.org/abs/2609.33383), v1 Sep 27 2026, preprint). Substituting a local oracle into APMM therefore needs a radius search. Doubling or bisection yields only inexact projections, which APMM's exact analysis does not cover, and at best a logarithmic factor per iteration. The new step is the split use of adjacent replies. The undercut reply gives the momentum distance decrease, and the crossing reply gives the model inequality. Together they pay for both the curvature error and the rejected trials, so the total call count is linear in `K`. As far as I found, this is a new mechanism. Proof ancestry is as follows: APMM supplies the known-value accelerated primal weighting, and BroxGD Thm 3.1 and Richtárik–Mahran supply the distance-decrease geometry. Neither provides the amortized accelerated count.

**Search coverage (2026-10-12).** I searched arXiv and the web for accelerated local-LMO, ball-LMO, trust-region conditional-gradient, and Polyak/known-value acceleration methods. I read the BroxGD v2 theorem statements and APMM Alg. 1 and Thm 2.1. I did not re-read the theorem text of CGS or Nesterov's (2018) trust-region conditional gradient. Garber–Hazan's LLOO and Hazan's [arXiv:2608.04321](https://arxiv.org/abs/2608.04321) cover only strongly convex objectives. I found no accelerated local-LMO result for merely convex objectives. The companion note's citations match the current versions: v1 of 2605.08850 was titled "Local LMO". The note does omit BroxGD's own known-`f⋆` result (Thm 3.5), which is the same-information baseline. The theorem was introduced in commit `bcc85c2` (2026-10-11), after all cited works.

## Conclusion

**Yes. With the same exact local-linear oracle, it improves the proved complexity from linear to accelerated, but only when the optimal value is known exactly.**

The strongest same-oracle baseline is BroxGD (Richtárik–Gruntkowska–Li, 2026). In combined value-gradient and local-oracle calls:

| | calls | output | needs |
|---|---|---|---|
| BroxGD Thm 3.2(ii) | `O(1 + LR²/ε)` | best iterate | `R`, `K` |
| BroxGD Thm 3.5 (`f⋆` known) | `O((‖∇f(x⋆)‖+LR)²R²/ε²)` | average | `f⋆` |
| SplitBrox | `O(1 + √(LR²/ε))` | last iterate | `f⋆`, `L`, `R` |

The gain is a factor of `√(LR²/ε)` whenever `LR²/ε ≥ 1`, and it has no extra logarithm. It loses in information: BroxGD Thm 3.2 needs neither `f⋆` nor `L`. Accelerated known-value methods (APMM) already exist, but they need exact projections onto `C` intersected with a halfspace. Turning those projections into local-oracle calls is exactly the step this proof resolves without a logarithmic search overhead.

The comparison establishes this gain. The literature search found no earlier accelerated local-LMO bound, but it is not exhaustive, and the area is moving quickly through 2026 preprints. It also remains open whether acceleration is possible with this oracle without knowing `f⋆`. What can be claimed is the first accelerated, log-free oracle complexity found for exact local linear minimization under known `f⋆`, with a last-iterate guarantee.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
