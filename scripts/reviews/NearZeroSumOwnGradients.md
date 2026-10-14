# Novelty assessment: NearZeroSumOwnGradients

[`result`](../../LongTails/Theorems/NearZeroSumOwnGradients.lean) proves the following for compact convex `X × Y` and player costs `h+g` (player x) and `g−h` (player y), as specified in the [setup](../../LongTails/Setups/NearZeroSumGames.lean). The [algorithm `nearZeroSumGameOutput`](../../LongTails/Algorithms/NearZeroSumFoam.lean) is regularized proximal FOAM with projected anchored-extragradient inner solves. It returns a feasible point with `‖z_out − z★‖² ≤ ε` for a Nash equilibrium `z★`, using only the own-gradient field `F = (∇ₓ(h+g), ∇ᵧ(g−h))` and exact projections.

**Complexity.** Parameters: `μ, ν` are the strong convexity of `h` in `x` and strong concavity of `h` in `y`; `m = min(μ,ν)`, `M = max(μ,ν)`; `L` bounds the Lipschitz constants of `∇(h±g)`; `δ` bounds the Lipschitz constant of `∇g`, where `g` is jointly convex; `D` is the diameter. The budget counts every gradient and projection call:

  O( (L/m)·√((m+δ)/(M+m+δ)) · log(2+D²/ε) · log(2+L²D²/(m²ε)) ).

For `D² ≥ ε`, this has the same order as `O((L/√(μν) + (L/m)·min{1,√(δ/M)}) · log(D²/ε) · log(L²D²/(m²ε)))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Luo–Stich–Chatterjee, [ICLR 2026, arXiv:2512.02690v1](https://arxiv.org/abs/2512.02690), Thm 1 / Alg. 1 (ICL) | `(L/√(μν)+(L/m)min{1,√(δ/(μ+ν))})·log(LD²/(mε))·log(D²/ε)` full-gradient queries → the bound above | None: same order (for `D²≥ε`, `log(L²D²/(m²ε)) ≤ 2log(LD²/(mε))`) | None: same game class (Assumptions 1–3 with `μ,ν>0`) | None: same squared-distance criterion, and both use known parameters | **Weaker oracle:** ICL needs `∇g(zₜ)` and the zero-sum part `h`, i.e., full gradients of `u₁, u₂`. This result uses only `F`, whose reply does not determine `∇g`. The budget also counts projections, which Luo et al. do not count explicitly. |
| Extragradient / Tseng FBF on strongly monotone VI (Tseng, J. Comput. Appl. Math. 1995; link not rechecked); `F` is `m`-strongly monotone and `2L`-Lipschitz | `(L/m)·log(2+D²/ε)` → the bound above | Better by a factor ≍ `√((M+δ)/(m+δ)) / log(2+L²D²/(m²ε))`, a gain iff `(m+δ)/(M+δ)·log²(2+L²D²/(m²ε)) ≪ 1`. Example: `δ=m`, `L=M=κm`: `κ·log(D²/ε)` → `√κ·log(D²/ε)·log(κ²D²/ε)` | None (same `F`-only oracle) | None | **Worse by** the factor `log(2+L²D²/(m²ε))` when `M ≍ m` or `δ ≳ M`. Needs `μ,ν,δ,L,D` and the decomposition structure (but not the decomposition itself). |
| Zero-sum special case `δ=0` (`g` affine on the domain): FOAM, [Kovalev–Gasnikov NeurIPS 2022](https://arxiv.org/abs/2205.05653), Thm 3 (unconstrained); lower bound [Zhang–Hong–Zhang, Math. Prog. 2022](https://arxiv.org/abs/1912.07481) | `(L/√(μν))·log(D²/ε)` → `(L/√(μν))·log(D²/ε)·log(L²D²/(m²ε))` | Worse by one log | Restricted baseline: covers only `δ=0` | None | Loses a logarithm on the zero-sum overlap |

**Reduction check.** I did not find a standard reduction to the earlier results. `F` cannot be split into `∇g` and the saddle field of `h`. The only trivial split, `F = ∇(m‖z‖²/2) + remainder`, has an `O(L)` monotone remainder. As a result, the decomposed-oracle acceleration of [Lee–Ryu–Yun, arXiv:2604.11105v1](https://arxiv.org/abs/2604.11105) gives back the `L/m` rate. This preprint is also later than ICL. ICL's linearization needs `∇g(zₜ)`.

The new mechanism writes `F` as the saddle field of `h + g − 2g(x★,·)` plus an error `e`. That function is available only in the analysis, and `‖e‖ ≤ 2δ‖x−x★‖`. FOAM's retained curvature absorbs this error once proximal regularization `β = m+16δ` enforces small coupling. The proof builds on FOAM's potential argument (Kovalev–Gasnikov, Alg. 2, Lemmas 1, 5–7) and on projected anchored extragradient ([Cai–Oikonomou–Zheng, ICML 2024](https://proceedings.mlr.press/v235/cai24f.html)) as the inner solver. These sources provide the template and the subroutine; they do not provide the `F`-only bound.

**Search coverage (2026-10-14 UTC).** I checked the arXiv HTML of 2512.02690v1, including the setting, Algorithm 1, Theorem 1, and Appendices C/E/G; it is still v1. I also checked the abstract of 2604.11105v1 and ran web searches on near-zero-sum and own-gradient acceleration, block-modulus monotone games, and distributed Nash seeking. I did not read Luo et al.'s Section 6 or the ICLR proceedings PDF directly. The PDF text extraction failed. I cited the FOAM and lower-bound rows from Luo et al.'s Proposition 2 and the companion note, without re-reading those papers. I found no `F`-only accelerated bound for this class. The companion note's citations and claims are consistent with these checks. The theorem first appears in the repository's initial commit (2026-10-14), so its in-repository chronology starts there.

## Conclusion

**The rate is not new; what is new is achieving the known near-zero-sum rate with players' own gradients instead of full utility gradients.** The strongest baseline is Luo–Stich–Chatterjee (ICLR 2026). Their bound has the same order up to constants, but their algorithm linearizes the shared cost and therefore needs `∇g`, which the own-gradient oracle does not reveal.

Within the own-gradient (standard VI) oracle, the checked alternative is extragradient:

| | own-gradient calls |
|---|---|
| Extragradient | `(L/m)·log(D²/ε)` |
| This result | `(L/m)·√((m+δ)/(M+δ))·log(D²/ε)·log(L²D²/(m²ε))` |

The gain is polynomial when the curvatures are unbalanced and the coupling is weak, i.e., `(m+δ)/(M+δ)` is small compared with `1/log²(L²D²/(m²ε))`. In that regime, `L/m` becomes about `L/√(mM)`. When the curvatures are balanced or `δ ≳ M`, the result loses one logarithm, and it also loses one logarithm against FOAM in the zero-sum case.

The comparison establishes this gain over the checked baselines. My search found no earlier `F`-only result, but it cannot rule one out. A reader can credit a reduced-information oracle result: the known accelerated near-zero-sum complexity, obtained without separating the competitive and shared gradients, through a non-routine perturbation analysis.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
