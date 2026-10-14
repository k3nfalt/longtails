# BallProximalSharpProfile: novelty assessment

[`result`](../../LongTails/Theorems/BallProximalSharpProfile.lean) proves the following for the [`ConvexBallProximal`](../../LongTails/Setups/ConvexBallProximal.lean) setup. The fixed-radius ball-proximal point method ([`algorithm`](../../LongTails/Algorithms/BallProximal.lean)) queries the exact minimizer of `f` over `C ∩ B(x_k,t)`, using any admissible tie breaking. On every proper closed convex objective in any finite dimension, its last iterate satisfies `f(x_K) − f⋆ ≤ ε` after the budget `K` displayed below. `allowedAlgorithm` requires equality with this method, and compliance is proved by `rfl`, so there is no formalization gap in the method family.

**Proved budget.** Here `R ≥ ‖x₀−x⋆‖`, `Δ ≥ f(x₀)−f⋆`, `t` is the radius, and `ε` is the target accuracy:

```
K = ⌈ min{ R²/t²,  (R/t)·√( min{1/2, (1−ε/Δ)₊}² + ½·log₊(Δ/(2ε)) ) } ⌉
  = O( min{ R²/t², (R/t)·√(log(Δ/ε)) } )   for ε < Δ/2;   K = 0 if ε ≥ Δ.
```

Write `r = ε/Δ`. The √-coefficient is `1−r` for `r ≥ 1/2` and `√((1+2log(1/(2r)))/4)` for `r < 1/2`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gruntkowska–Li–Rane–Richtárik, [arXiv:2502.02002v2](https://arxiv.org/abs/2502.02002v2) (Jul 2025), Thm 8.1(iii) + Cor 8.2 | `⌈min{R²/t², log(Δ/ε)/log(1+t/R)}⌉ ≈ (1+R/t)log(Δ/ε)` → `(R/t)√(½log(Δ/ε))` (capped at `R²/t²`) | √log factor: about `√(2 log(Δ/ε))` when `R/t ≫ √log(Δ/ε)`. This was already obtained in the next row. | None | None | None |
| Richtárik–Li, [arXiv:2609.35147v1](https://arxiv.org/abs/2609.35147v1) (28 Sep 2026, preprint), Thm 3.4 eq. (43) | `⌈min{R²/t², (R/t)√(½log(Δ/ε))}⌉` → selected `K` | Uniformly no worse (checked for all `r`), but same order. Constant factor ≤ 1.18 at `r = 1/2`; the factor tends to 1 as `ε/Δ → 0` | None | None | None |
| Same paper, Remark 3.5 (implicit bound `r² + (K t²/R²)(1+r^{1/K})/(1−r^{1/K}) ≤ 1`) | Large-`K` coefficient `(R/t)√((1−r²)log(1/r)/2)` → selected coefficient above | Asymptotic constant gain ≤ ~4.4% (maximum near `r ≈ 0.2`). It is ~2% at `r = 1/2` and → 0 as `r → 0` or `r → 1` | None | None | Does not dominate at finite `K`: at `K = 1` the implicit bound is exact |
| Same paper, Thm 4.5 (fixed dimension `d`) | `min{⌈R²/t²⌉, 1 + 2C_d R/t}` vs. selected `K` | Worse in fixed `d` once `√log(Δ/ε) ≳ C_d`. Selected is better when `C_d ≳ √log(Δ/ε)` (high `d`) | None | None | Prior bound has no `ε` dependence but has dimension constant `C_d` |

**Reduction / mechanism.** The order `(R/t)√log(Δ/ε)` already follows from Richtárik–Li's Jensen argument over the squared-distance budget. The new ingredient behind the explicit envelope is in the supporting lemmas (`exact_profile_characterization`, `execution_lower_high/low`, `sharp_low_gap_family`, all present in `LongTails/Proofs/`). These lemmas give an if-and-only-if characterization of worst-case BPM executions through the scalar energy `F_K(a,r)`, and the matching instances are max-affine functions in dimension `≤ K`. They also show that the leading coefficient is sharp at fixed `r`. Richtárik–Li §8 explicitly leave this question open: "Determining the optimal bound for convex BPM trajectories … remains open." The public theorem exports only the budget, not the characterization. The proof ancestry comes from the BPM radial-support identity (Gruntkowska et al. Thm 8.1) and the Richtárik–Li distance/gap coupling (Thm 3.3).

**Search coverage (2026-10-12).** I searched arXiv and the web for BPM/broximal work from 2025–2026, including the April 2026 alignment paper, the Hadamard-manifold extension, and BroxGD/Local LMO, as well as PEP literature on proximal point methods (Taylor–Hendrickx–Glineur 2017). I read Richtárik–Li v1 in full text (Thm 3.1, 3.4, Rem 3.5, Thm 4.5, 4.11, §8) and Gruntkowska et al. v2 §8. I found no prior exact worst-case characterization of BPM. Accelerated ball-oracle methods (Carmon et al. 2020/2021) use richer oracles and are not comparable. The companion note's citations and its ≈4.26% gain at `r = 0.2` match my check. The theorem was introduced in commit 130a5cc on 2026-10-11, two weeks after Richtárik–Li v1. Unpublished concurrent work cannot be excluded.

## Conclusion

**The proved complexity is not better in order; it improves only a constant factor, by a few percent against the strongest earlier bound.** The strongest baseline is Richtárik–Li (arXiv:2609.35147v1, Sep 2026). It covers the same exact oracle, the same convex class, and the same last-iterate criterion, and it already gets the √log rate:

| | calls for `f(x_K)−f⋆ ≤ ε` |
|---|---|
| Richtárik–Li Thm 3.4 / Rem 3.5 | `(R/t)·√(½log(Δ/ε))`, or asymptotically `(R/t)·√((1−r²)log(1/r)/2)` |
| This result | `(R/t)·√(¼ + ½log(Δ/(2ε)))` for `r < 1/2`; `(R/t)(1−r)` for `r ≥ 1/2` |

Example: with `Δ/ε = 5` and `R/t = 1000`, the selected budget is 842 calls, compared with ≈879 (Rem 3.5) and ≈897 (Thm 3.4). The gain vanishes as `ε/Δ → 0`. In fixed dimension, the dimension-dependent `O_d(R/t)` termination bound is better at high accuracy.

What is genuinely new, as far as my search shows, is in the supporting lemmas, not the exported theorem. They exactly characterize the worst case of fixed-radius BPM and show the leading constant is sharp, which settles a question Richtárik–Li left open. That is a real, if narrow, method-specific contribution. It yields no improvement in order, scope, oracle, or output.

The claim that can be made: a tight worst-case analysis of ball-proximal steps, with a slightly sharper explicit budget.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
