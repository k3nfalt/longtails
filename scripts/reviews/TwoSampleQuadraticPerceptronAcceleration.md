# Novelty assessment: TwoSampleQuadraticPerceptronAcceleration

The [theorem](../../LongTails/Theorems/TwoSampleQuadraticPerceptronAcceleration.lean) proves that the noise-free, non-batch two-sample quadratic perceptron ([algorithm](../../LongTails/Algorithms/TwoSampleQuadraticPerceptron.lean), `γ = 1/(2R)`, last iterate) deterministically reaches a separator of both samples. The [setup](../../LongTails/Setups/TwoSampleQuadraticPerceptron.lean) covers the kernel-2 convolutional model and the width-1 two-layer linear model. The bound holds for every start in a data-dependent cone and stays valid at every later step.

**Proved budget (exact margin-and-gradient calls on both samples, one call per step):**

N = O( (R log ρ/μ + 1) · (R/g + 1)² · (1 + β⁺ log ρ/μ + log(S/a + S R³/(β⁻³ z))) ).

The parameters are:
- R ≥ ‖b₁‖, ‖b₂‖ bounds the sample norms.
- g ≤ λ₁, λ₂ lower-bounds the two fast eigenvalues.
- β⁻ ≤ β ≤ β⁺ brackets the coupling eigenvalue.
- μ lower-bounds the slow eigenvalue. It is used only for the conv model; for the two-layer model ρ = 1, so the μ terms vanish.
- ρ ≥ |r₀+y₀|/|r₀−y₀| bounds the slow-block ratio of the start.
- a, z, S are the start's cone margin σ(p₀+q₀), depth |z₀| and size 2σp₀+2|z₀|.

All logarithms are nonnegative, because S ≥ a. On Tyurin's dataset (5) we have R ≈ √d, g ≈ √(2d) and β ≈ μ, so the bound is O((√d log ρ/μ + 1)(1 + log ρ + log(S/a + S d^{3/2}/(μ³z)))).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2512.11587](https://arxiv.org/abs/2512.11587) Thm 5.1 (v1 Dec 2025, v2 May 2026; ICML 2026 poster). **Special-case baseline: conv model, dataset (5), μ ≤ 1/10, noisy QPA** | O(√d/μ · L₁L₂ log(√d L₁L₂/μ)), with failure probability δ, where L₁ = log(‖θ₀‖²/(δ³⟨θ₀,v_{μ,+}⟩²)) and L₂ = log(d‖θ₀‖²/(μ⟨θ₀,v_{μ,+}⟩²)) (constant 2²⁷) → the bound above, constant 24 | None in order: both are √d/μ up to logarithms. The log factors use different initialization statistics, so they are not ordered. If r₀y₀ ≤ 0 (ρ = 1), the new bound is logarithmic in d/μ | Dataset (5) → general conv data (constant b₁, positive-mean b₂); adds the two-layer width-1 model with any data satisfying ⟨b₁,b₂⟩ > 0 and b₂ ∦ b₁ | Probability-(1−δ) bound for the noisy method → deterministic bound for the noiseless method | Only starts in the cone {σ(p₀+q₀) > 0, σ(p₀−q₀) ≥ 0, z₀ ≠ 0} are covered (the note says 1/4 of Gaussian starts; I did not verify this), versus almost every start in Thm 5.1. The cone depends on the data and cannot be chosen by the algorithm |
| Trivial direct method on the same setup and oracle | — → the bound above | Worse: 1 call suffices. Querying θ = (0,1) (two-layer) or ((1,0), v) (conv) returns b₁ and −b₂ through the gradient. Any linear separator, which exists because b₂ is not a nonnegative multiple of b₁, can then be output | None | None | The QPA bound is a method-specific statement; it does not improve the problem-class complexity |
| Tyurin Thm 5.2 (batch linear perceptron, dataset (5)) | Ω(d/μ) lower bound for starts near 0 | Not a competing upper bound; it is the method-vs-method contrast inherited from Tyurin | — | — | Different model (linear) |

**Standard-reduction check.** The result does not follow by substitution into Thm 5.1: that proof relies on the injected noise to escape stalling subspaces, and Tyurin's Thm 4.2 shows such non-convergent subspaces exist. The new ingredients are an invariant cone and two Lyapunov arguments for the switched system: a two-step-contracting potential and a count of slow-block obstacle steps. The proof ancestry is Tyurin's QPA reduction (Thm 2.1) and his eigen-decomposition (Prop. 5.3).

**Search coverage (2026-10-23).** I searched arXiv, the ICML 2026 listing, the web, and Semantic Scholar citations (none indexed), and read Thm 5.1, Thm 5.2 and Sec. 4–8 of the v2 PDF. I found no deterministic or noise-free analysis and no two-layer width-1 QPA result. That absence does not prove priority. The theorem was introduced in commit 1a1868d (2026-10-23), after Tyurin v2.

The companion note has two discrepancies with the paper:
- It says the paper asks for a "significantly simpler proof". The paper's phrase refers to simpler *algorithmic steps*; its stated open directions are larger kernels, general two-layer and multi-layer models, activations, and the small-norm regime.
- Its claim that Gaussian starts fall in the cone with probability 1/4 is not formalized.

## Conclusion

**No optimization complexity improves; what is new is a noise-free, deterministic analysis of Tyurin's perceptron dynamics on a cone of starts, extended to more data and to a second model.**

The strongest baseline is Tyurin's Theorem 5.1. On dataset (5), both bounds are √d/μ up to logarithms:

| | Thm 5.1 | This result |
|---|---|---|
| Method | noisy non-batch QPA | noiseless non-batch QPA |
| Guarantee | probability 1−δ, almost every start | deterministic, cone starts only |
| Steps | Õ(√d/μ) | Õ(√d/μ), or O(log(dS/(μ a z))) if r₀y₀ ≤ 0 |

As an optimization problem, separating two samples takes a single oracle call, so the theorem does not improve problem-class complexity.

The genuine gains are threefold. First, the artificial noise and the high-probability event are removed. Second, the result covers general conv data and width-1 two-layer networks, where the bound is logarithmic. Third, the constants are explicit. These gains come at a cost: only a data-dependent cone of starts is covered, the method is still the non-batch rule rather than the batch limit of GD, and there is no statement about finite-norm GD. Together they are a modest step on one of Tyurin's open directions (two-layer, width 1 only).

The comparison shows that the rates match on the overlap. The literature search found no prior deterministic analysis, but it cannot establish priority. What can be claimed is a simpler, noise-free proof of implicit acceleration for the non-batch QPA on a cone of starts, with a modest extension of its scope.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
