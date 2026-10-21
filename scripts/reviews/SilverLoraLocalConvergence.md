# Novelty review: SilverLoraLocalConvergence

[`result`](../../LongTails/Theorems/SilverLoraLocalConvergence.lean) proves the following. Take simultaneous scalar-step LoRA-GD `(B,A) ← (B,A) − η_t(GAᵀ, BᵀG)`, with `G = ∇f(BA)` ([algorithm](../../LongTails/Algorithms/LoraSilver.lean), [family](../../LongTails/Algorithms/LoraGd.lean)), run for `K` steps of size `1/(8ρR²)` and then `q` repeated silver blocks. For every globally μ-strongly convex, ρ-smooth `f` with an exact rank-`r` minimizer `B̄Ā` and `‖(B₀,A₀)−(B̄,Ā)‖ ≤ μs²/(256ρR)`, the **last** factors then satisfy `f(B A) − f⋆ ≤ ε` deterministically ([setup](../../LongTails/Setups/LocalSmoothStronglyConvexLora.lean)).

**Complexity.** Here σ_min(B̄), σ_min(Āᵀ) ≥ s, the operator norm of `(h_B,h_A) ↦ h_BĀ + B̄h_A` is at most R (with R ≥ s), and we write κ̂ = ρR²/(μs²) ≥ 1. The exact budget `128⌈64κ̂⌉(k+1) + (2^k−1)q` then gives

  T = O( κ̂ log(2+κ̂) + κ̂^{log_{1+√2}2} · log(2 + ρR⁴/ε) ),  log_{1+√2}2 ≈ 0.786,

full-gradient calls. The `gdFamily` restriction does enforce positive scalar steps, product queries, the given initialization and final-iterate output, and compliance is proved (`allowed`).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Constant-step LoRA-GD (step 1/(8ρR²)), proved in-repo under identical assumptions ([`LoraWarmup.trajectory`](../../LongTails/Proofs/LoraWarmup.lean), gap factor `1−μs²/(256ρR²)`, initial gap ≤ μ²s⁴/(16384ρ)). Same family; this is a reconstruction, not a published theorem. | O(κ̂ log(2+μ²s⁴/(ρε))) → T | κ̂ → κ̂^0.786 on the accuracy term, a speedup of up to ≈κ̂^0.214. The gain survives only when log(2+μ²s⁴/(ρε)) ≫ log(2+κ̂), because log(ρR⁴/ε) = log(μ²s⁴/(ρε)) + 2log κ̂. | None | None (both: last iterate, same known parameters) | Worse at moderate accuracy, where the O(κ̂ log κ̂) warmup dominates; the warmup also carries large constants (128·64). |
| Ambient Nesterov AGD ([Bubeck 2015, Thm 3.18](https://arxiv.org/abs/1405.4980)) from X₀ = B₀A₀, then rank-r SVD truncation (reduction checked below) | O(1 + √(ρ/μ) log(2 + μs⁴/ε)) → T | **Worse or equal in every regime** (same order only when ρ/μ and R/s are O(1)): √(ρ/μ) ≤ κ̂^0.786 and μs⁴ ≤ ρR⁴. The gap is ≥ max{(ρ/μ)^0.286, (R/s)^1.57} up to constants, plus the warmup. | None | None (both output r-column factors and certify the same gap) | AGD keeps dense iterates and momentum, outside `gdFamily`. Each oracle call returns a dense m×n G in both methods. |
| Li–Lin, factored AGD ([arXiv:1702.04959v6](https://arxiv.org/abs/1702.04959), Thm 4 and §7) | O(√(ρ/μ)·‖U⋆‖²/(σ_r(U⋆)·min_i σ_r(U⋆_{S_i})) · log(1/ε)) → T. The σ_r(U⋆_{S_i}) are row-submatrix singular values, which cannot be bounded by R and s. | Not comparable: their rate cannot be expressed in (ρ,μ,R,s). In the condition dependence it is √(ρ/μ) versus κ̂^0.786. | Theirs is broader in f: restricted strong convexity → our global strong convexity | None | Theirs uses momentum, restarts, a balancing regularizer and an index-set constraint, so it lies outside the scalar LoRA-GD family. |

**Reduction check.** The AGD row reduces as follows:

- ‖X₀−X⋆‖ ≤ 2R·μs²/(256ρR) = D.
- AGD reaches an ambient gap δ = με/(4ρ) in 1 + √(ρ/μ)·log((ρ+μ)ρD²/(2με)) calls.
- By Eckart–Young, ‖X̂−X⋆‖ ≤ 2‖X̃−X⋆‖. Hence f(X̂)−f⋆ ≤ 2ρ‖X̃−X⋆‖² ≤ 4(ρ/μ)δ = ε, with no extra oracle calls.

The silver schedule itself does not follow from a standard reduction: f∘product is nonconvex and its minimizers are non-isolated, so the convex silver theorem does not apply directly. The genuinely new mechanism is a factor-repair step combined with a recursive, prefix-stable control of a local interpolation defect under only C¹¹ outer regularity. Proof ancestry: Altschuler–Parrilo's silver schedule ([arXiv:2309.16530](https://arxiv.org/abs/2309.16530)) and Grimmer–Shu–Wang's certificates ([arXiv:2410.16249](https://arxiv.org/abs/2410.16249)) supply the convex step certificates. The local factor geometry and polynomial-cost entry are this result's additions.

**Search coverage (2026-10-20 UTC).** Scope: arXiv and proceedings on silver/long-step GD, including the Riemannian silver work ([arXiv:2506.06160v2](https://arxiv.org/abs/2506.06160); I read only the abstract and could not verify its NeurIPS venue), LoRA convergence ([Wang–Liu–Lui, arXiv:2607.21975v2](https://arxiv.org/abs/2607.21975); [Mu–Klabjan, arXiv:2512.18248v3](https://arxiv.org/abs/2512.18248)), and accelerated or factored low-rank methods. I found no prior silver/long-step analysis for factored or Burer–Monteiro objectives. Prior work [Liu–Ye, arXiv:2609.26873](https://arxiv.org/abs/2609.26873) (Sep 2026) shows that κ^{0.786−o(1)} is nearly optimal for *predetermined* schedules on strongly convex functions; whether that transfers to this class is unverified. The companion note's AGD-plus-truncation comparison agrees with mine but omits Li–Lin. The result was introduced in commit 84dae21 (2026-10-20 22:21 UTC).

**Conclusion**

**No optimization advantage is established: a simple ambient method beats this bound in every regime, so the contribution is a new local analysis of scalar LoRA-GD.**

The strongest baseline is Nesterov AGD on the matrix objective followed by one rank-r SVD truncation. It uses the same gradient oracle and returns factors with the same certified gap:

| | Full-gradient calls |
|---|---|
| AGD + truncation | O(1 + √(ρ/μ) · log(2 + μs⁴/ε)) |
| This result | O(κ̂ log(2+κ̂) + κ̂^0.786 · log(2 + ρR⁴/ε)), κ̂ = ρR²/(μs²) ≥ ρ/μ |

Since κ̂^0.786 ≥ √(ρ/μ), the selected bound is never smaller, and it is polynomially worse when ρ/μ or R/s is large.

Within the shared-scalar-step LoRA-GD family, the comparison does prove a gain over constant steps: the accuracy term improves from κ̂·log(1/ε) to κ̂^0.786·log(1/ε) in the high-accuracy regime log(μ²s⁴/(ρε)) ≫ log κ̂. This is analogous to the known convex silver speedup and remains far from accelerated rates. My search found no prior long-step analysis of factored nonconvex objectives, but that does not prove priority.

What can be claimed is a fixed-method contribution: the first (as far as found) proof that silver steps accelerate unregularized simultaneous LoRA-GD locally, under C¹¹ strongly convex outer losses with exact low-rank optima. It improves no problem-class complexity, and its scope is narrower than Li–Lin's restricted-convexity setting.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
