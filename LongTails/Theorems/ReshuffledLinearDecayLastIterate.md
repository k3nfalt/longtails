# Log-free last-iterate rate for random reshuffling on smooth convex finite sums

This note explains the contribution formalized in
[ReshuffledLinearDecayLastIterate.lean](ReshuffledLinearDecayLastIterate.lean).

The theorem is a last-iterate guarantee for the shuffling gradient method with uniformly random per-epoch permutations (random reshuffling, RR) and a known-horizon linear-decay epoch stepsize. For convex components with Lipschitz gradients it proves

  E f(x_K) − f* ≤ 3‖x₀ − x*‖²/(γK) + 12 γ² L̄ σ*²/n   whenever γ √(L̄ L*) ≤ 1/64,

which after tuning is O(√(L̄L*) R²/K + L̄^{1/3} σ*^{2/3} R^{4/3}/(n^{1/3} K^{2/3})) with no logarithmic factor. The previous last-iterate bounds for this method carry a (1 + log K) factor in the stepsize cap and polylogarithmic factors in the rate; removing it was stated as an open problem by Liu and Zhou (ICML 2024).

Averaged iterates already attain this order (Mishchenko, Khaled, Richtárik 2020). The claim concerns the last iterate only.

## Setup and proved guarantee

The [setup](../Setups/ReshuffledSmoothConvex.lean) is the standard finite-sum model.

- **Objective.** f = (1/n) Σ_i f_i on a real Hilbert space E; every f_i is convex and differentiable.
- **Smoothness.** ∇f_i is ℓ_i-Lipschitz for some constants ℓ_i ≥ 0 with ℓ_i ≤ L* (`Lmax`) and (1/n) Σ ℓ_i ≤ L̄ (`Lavg`). Only the two bounds L̄ ≤ L* are public; the individual ℓ_i are not.
- **Minimizer and noise.** There is a minimizer x* of f with ‖x₀ − x*‖ ≤ R and σ*² := (1/n) Σ_i ‖∇f_i(x*)‖² ≤ σ². Nothing else is assumed: no bounded gradients, bounded domain, uniform variance bound or strong convexity.
- **Oracle.** A query (i, x) returns ∇f_i(x); each query costs one call.
- **Admissible algorithms.** The setup's `allowedAlgorithm` field restricts `Convergence` to the shuffling gradient method itself: for some number of epochs K and epoch stepsizes η_0, η_1, …, the algorithm draws K independent uniformly random permutations π_0, …, π_{K−1} of {1, …, n} and performs, in epoch k, the n steps y ← y − η_k ∇f_{π_k(j)}(y), j = 1, …, n. Its output is its current point, so after n·K calls the output is the last iterate. Averaging, variance reduction or any other method is excluded by the specification, not just by the witness.
- **Success.** The output is measurable, and E f(output) − f(x*) ≤ ε, with the expectation written as an explicit integral over the algorithm's permutations.

**Algorithm.** The [algorithm](../Algorithms/ReshuffledGradient.lean) is run with

  η_k = γ (K − k)/(K n),   γ = 1/(64 √(L̄L*) + 5 σ √(L̄/(n ε))),   k = 0, …, K − 1,

so the effective epoch stepsize n·η_k = γ(K − k)/K decays linearly to γ/K.

**Budget.** The public budget is the one-line formula

  n · ⌈384 √(L̄L*) R²/ε + 30 σ R² √(L̄/(n ε³))⌉

oracle calls (the ceiling is the number of epochs K; the execution makes exactly n·K calls). In rate form this is K = O(√(L̄L*) R²/ε + σ R² √L̄/(√n ε^{3/2})), equivalently the displayed O(1/K + 1/(n^{1/3}K^{2/3})) rate.

**Lean layout.**
- [ReshuffledEpoch](../Proofs/ReshuffledEpoch.lean): finite-sum facts and the pathwise epoch inequality (Lemma 1 below).
- [ReshuffledMoments](../Proofs/ReshuffledMoments.lean): the without-replacement moment bound (Lemma 2) and its deterministic any-order counterpart.
- [ReshuffledConvergence](../Proofs/ReshuffledConvergence.lean): anchors, summation over the permutation seeds, and the reduction to the weight lemma `potential_bound` of [LinearDecaySgdWeights](../Proofs/LinearDecaySgdWeights.lean).
- [ReshuffledExecution](../Proofs/ReshuffledExecution.lean): marginals of the uniform product law, tuning, the execution of the algorithm, and `Convergence`.

## Mechanism

Fix one epoch with start x, permutation π, inner step η and γ = nη. Write y_0 = x, y_{j+1} = y_j − η ∇f_{π(j)}(y_j), x⁺ = y_n, s_i = ∇f_i(x*), P_j = Σ_{m<j} s_{π(m)} and

  W(π) = Σ_{j<n} ℓ_{π(j)} ‖P_j‖².

**Lemma 1 (pathwise epoch inequality, `Hyp.epoch_inequality`).** If γ L̄ ≤ 1/2 then for every reference point z

  ‖x⁺ − z‖² ≤ ‖x − z‖² − 2γ (f(x⁺) − f(z)) + 32 γ³ L̄ L* (f(x) − f*) + 2 η³ (1 + 8γ²L̄²) W(π).

Two features matter. First, the relative error multiplies the gap at the *start of the epoch*, f(x) − f*, not the gap at the reference point f(z) − f*. The existing last-iterate analyses (Liu–Zhou Lemma D.2 and Theorem C.1; Cai–Diakonikolas Lemma 2.1) carry the error at the reference point, in the form of a multiple of f(z) − f(x*), and Cai and Diakonikolas note that such error terms "inherently deteriorate the growth rate of {w_k}". Second, the noise enters only through W(π), which depends on the permutation and on the gradients at x*, but not on x or z. The proof bounds the inner drift by a Gronwall step that tracks the prefix sums P_j explicitly, ρ ≤ 2Q + 2η Σ_j ℓ_{π(j)} ‖P_j‖ with ρ = Σ_j ‖∇f_{π(j)}(y_j) − s_{π(j)}‖; this keeps the whole noise contribution proportional to W(π), with no additional higher-order noise term and no "large K" condition.

**Lemma 2 (without-replacement moment, `scatter_sum_le`).** For a uniformly random permutation, E W(π) ≤ n² L̄ σ*². The proof uses only transpositions of positions: cross terms E⟨s_{π(m)}, s_{π(m')}⟩ are nonpositive because Σ s_i = 0, so E‖P_j‖² = E‖Σ_{m≥j} s_{π(m)}‖² ≤ (n − j) σ*², and E[ℓ_{π(j)}‖P_j‖²] = E[ℓ_{π(m)}‖P_j‖²] for every position m ≥ j, which averages the weight to at most n L̄/(n − j). For an arbitrary fixed permutation one only has W(π) ≤ n³ L̄ σ*² (`scatter_le`).

**Reference points and weights.** Following Zamani–Glineur, take anchors z_0 = x*, z_{k+1} = (w_k/w_{k+1}) z_k + (1 − w_k/w_{k+1}) x_{k+1}. The weights are the absorbing-charge weights of this repository's [LinearDecaySgdLastIterate](LinearDecaySgdLastIterate.md): w_{k+1}(S_{k+1} + c_{k+1}) = w_k S_k with S_k = Σ_{j≥k} γ_j and a charge c_k that dominates 16 γ_k³ L̄ L*. Under linear decay Σ_k c_k/S_k is bounded by an absolute constant, so the product Π(1 + c_k/S_k) that the relative term costs is horizon-free. With constant epoch steps the same product is K^{Θ(γ² L̄ L*)}, which is exactly why the constant-step analyses need γ√(L̄L*) ≲ 1/√(log K). Lemma 1 at z = z_k, convexity of f at z_{k+1} and the contraction of ‖x_{k+1} − z_{k+1}‖² are all pathwise and linear in the path quantities, so they are summed over the permutation seeds and fed to the deterministic lemma `potential_bound`. The only probabilistic input is Lemma 2 applied to the k-th marginal; no conditional expectation is needed because W(π_k) does not depend on the trajectory.

**What is not new.** Linear-decay stepsizes for last iterates are due to Zamani–Glineur, and Liu–Zhou already use the linear-decay epoch stepsize η_k ∝ (K − k + 1) for proximal shuffling with *Lipschitz* components (their Theorem 4.7). The absorbing-charge weights and the lemma `potential_bound` come from this repository's i.i.d. SGD theorem and are reused verbatim. The new ingredients are Lemma 1 (start-of-epoch relative error, noise isolated in W(π)), the prefix-sum Gronwall step that preserves the full 1/n gain, and the resulting log-free rate for smooth components.

## Relation to prior results

- **Liu and Zhou (ICML 2024, [arXiv:2403.07723](https://arxiv.org/abs/2403.07723)).**
  - Theorem 4.4 (full statement Theorem C.1) gives, for the proximal shuffling gradient method with constant stepsize η ≤ 1/(4n√(2L̄L*(1+log K))), the last-iterate rates Õ(√(L̄L*)D²/K + L̄^{1/3}σ_any^{2/3}D^{4/3}/K^{2/3}) for any permutations and Õ(√(L̄L*)D²/K + L̄^{1/3}σ_rand^{2/3}D^{4/3}/(n^{1/3}K^{2/3})) for uniformly random ones.
  - Section 6 states: "the extra factor 1 + log K in the stepsizes seems necessary in our analysis. Whether, and if so how, it can be removed is an important problem."
  - This theorem removes the factor for their "Random" row when there is no regularizer (ψ = 0, where σ_rand = σ_any = σ*), with the same dependence on L̄, L*, σ*, n and K. The improvement is the factor (1 + log K) in the stepsize cap and the polylogarithmic factors in the rate, nothing more.
- **Cai and Diakonikolas (ICLR 2025, [arXiv:2403.06873](https://arxiv.org/abs/2403.06873)).** Theorem 2.3 bounds the last iterate of the incremental gradient method with η ≤ 1/(√β n L), and takes β = 4 log K; Corollary 2.5 is the analogous statement for uniformly random orders (RR/SO), with the stepsize smaller by a factor of order 1/√(log K). Corollary 2.4 removes the logarithm only for an increasing-weight average of the iterates.
- **Liu (COLT 2026, [arXiv:2606.32005](https://arxiv.org/abs/2606.32005)).** Analyses averaged iterates of RR for larger stepsizes and describes the two last-iterate results above as holding "up to additional polylogarithmic factors".
- **Lower bound.** Cha, Lee, Yun (ICML 2023, [arXiv:2303.07160](https://arxiv.org/abs/2303.07160)), Corollary 3.5: for n ≥ 2 there is a two-dimensional F with L-smooth convex components such that, for K ≥ c₃ max{L²D²n/ν², ν/(μ D n^{1/2})} and any *constant* stepsize η ≤ 1/(c₂ L n), every weighted average of the RR epoch iterates, including the final one, has E F(x̂) − F* = Ω(L^{1/3}ν^{2/3}D^{4/3}/(n^{1/3}K^{2/3})). The rate proved here has the same order as that bound. The lower bound is stated for constant stepsizes, so it does not formally cover the decaying schedule used here; no optimality claim is made.
- **Last-iterate SGD.** Zamani–Glineur ([arXiv:2307.11134](https://arxiv.org/abs/2307.11134)) and Liu–Zhou ([arXiv:2312.08531](https://arxiv.org/abs/2312.08531)) obtain log-free last iterates with linear decay for Lipschitz or uniformly-bounded-variance i.i.d. settings; neither treats sampling without replacement on smooth components.
- **Standard reductions that do not give the result.** Averaging gives the rate for an average. Treating an epoch as an inexact gradient step and using near-monotonicity of f loses a factor Kγ√(L̄L*) on the noise term. Constant epoch steps with the inequality of Lemma 1 still lose K^{Θ(γ²L̄L*)}.

## Further consequences of the same proof

- **Arbitrary orders.** For any deterministic choice of per-epoch permutations (incremental gradient, adversarial orders), the supporting lemma `any_order_gap` gives f(x_K) − f* ≤ 3R²/(γK) + 12γ²L̄σ*² under the same condition on γ, that is, O(√(L̄L*)R²/K + L̄^{1/3}σ*^{2/3}R^{4/3}/K^{2/3}) without logarithms. This is the "Any" row of Liu–Zhou's Theorem 4.4 with ψ = 0. No lower bound is known for that row. It is a lemma in the proof module, not a second `Convergence` theorem.
- **Single shuffling.** The argument uses only that each π_k is marginally uniform, never independence across epochs. The same bound therefore holds when one uniformly random permutation is reused in every epoch. This is not formalized.

## Scope and limitations

- **No regularizer or constraint.** The proof uses Σ_i ∇f_i(x*) = 0. The baseline of Liu–Zhou allows a proximal term ψ; that case is not covered.
- **Known horizon and constants.** The schedule needs K, and γ is tuned with L̄, L*, σ, R and ε. The baseline's constant stepsize also depends on K. Log-free last iterates for constant or anytime stepsizes remain open.
- **Constants.** The constants 384 and 30 are not optimized; on random small instances the bound is loose by an order of magnitude.
- **Literature search.** No log-free last-iterate bound for shuffling methods on smooth convex components was found in the 2024–2026 literature that was searched (arXiv, ICML/ICLR/NeurIPS/COLT listings, and papers citing the two baselines as far as they could be located). The search was by keyword and is not exhaustive.
