# Many-sample cyclic quadratic perceptron with reference perturbations

## Result and scope

[The theorem](ManySampleConvolutionalPerceptronAcceleration.lean) gives a deterministic finite component-oracle bound for a perturbed, two-coefficient cyclic convolutional quadratic perceptron on an arbitrary finite collection of small defects around a positive reference. The [setup](../Setups/ManySampleConvolutionalPerceptron.lean) specifies the data and exact signed-margin/gradient oracle; the [algorithm](../Algorithms/ManySampleConvolutionalPerceptron.lean) supplies the particular QPA witness. The setup does not artificially exclude other algorithms.

This addresses the larger-dataset extension of `TwoSampleQuadraticPerceptronAcceleration.lean` and [Tyurin, ICML 2026, arXiv:2512.11587v2](https://arxiv.org/html/2512.11587v2). It retains genuine cyclic convolution with a filter of length two, simultaneous filter/readout updates, and strict separation as the output criterion. It replaces the two-point spectral analysis by a switched, coupled many-sample argument. It also changes the initialization and perturbation mechanism; this is not a theorem about the unchanged noisy algorithm in that paper. Neither the setup nor the theorem asserts best possible complexity among all algorithms for this data class.

Let `d` be any positive dimension, `N=n+1` the number of samples, `P` cyclic shift, and `e` the unit constant vector. The reference is `b₀=(α₀/√2)e`, with positive label. Each negative sample is

`bᵢ=(αᵢ/√2)e+μuᵢ`,

where `g≤αᵢ≤R`, including `i=0`, `μ>0`, `⟨e,uᵢ⟩=0`, and `‖uᵢ‖≤1/√2`. A unit vector `w` satisfies

`−⟨(uᵢ−Puᵢ)/√2,w⟩≥κ`, with `0<κ≤1`.

The geometry and separator are existential witnesses; the algorithm receives only `d,n,g,R,μ,κ` and oracle replies. There is no Gram-sign, orthogonality, rank, sparsity, or common-eigenbasis assumption. The score in filter/readout parameters is bilinear and the two channels interact. The result concerns this structured classification problem, not general nonlinear empirical-risk minimization.

Define

`ρ=g/(4R)`, `δ=(μ/(4R))²`, `B=ceil(8ρ⁻² log(1/δ))+2`, `b=B+1`.

The explicit contrast regime is

`δ≤exp(−1)`, `δb³≤κ³/2²⁴`, and `δb²≤κ²ρ⁴/2²⁴`.

These are sufficient small-contrast restrictions required by the proof, not lower bounds or intrinsic necessities of QPA. They are stronger than merely having a separating derivative. The theorem is not uniform over all contrasts. The dependence on dimension is through the geometry and its parameters; there is no suppressed dimension-independent claim about `κ` for arbitrary growing-dimensional data.

## Execution, output, and oracle cost

The raw filter starts at `(√2,0)` and the readout at zero. The step size is `η=1/(4R)`. A scan starts with the reference, then visits the negative samples in their given order. A strictly correct reply advances the cursor; a nonpositive signed margin triggers the simultaneous QPA gradient update and restarts the scan at the reference. On a mistaken reference only, both raw filter coefficients receive an additional equal increment

`δ² sign₊(a+q)/√2`,

where `a` is the filter mean, `q=⟨v,e⟩`, and `sign₊(0)=1`. Thus the perturbation is deterministic and uses an available constant-background coordinate. It does not query or use the separator. All other mistaken updates are unperturbed QPA. A complete correct scan can repeat; the point then remains fixed.

The returned output is the actual final filter/readout pair defined by `output`, using `execute`. Every signed margin is strictly positive at the prescribed budget, for every seed. The oracle is deterministic in its replies even though the framework permits arbitrary oracle seed spaces. No hidden probability distribution, expected accuracy, or high-probability qualification is used.

Put `ℓ=log(16R²/μ²)=log(1/δ)`. The public budget is exactly

`ceil(2³⁵ (R/g)⁴ ℓ² [N+(R/g)ℓ]/κ²)`.

Each oracle call returns one sample's signed margin and simultaneous parameter gradient. All correct replies, mistaken replies, reference retries, and the final scan are included. Arithmetic cost is not equated with oracle cost: vectors have dimension `d`, and a direct implementation uses dimension-dependent arithmetic. For fixed `R/g` and `κ`, the bound is near-linear in dataset size with polylogarithmic contrast dependence. When `κ` deteriorates, the explicit `κ⁻²` factor remains and can dominate the guarantee.

## Technical mechanism

Set `pᵢ=(uᵢ+Puᵢ)/√2`, `rᵢ=(uᵢ−Puᵢ)/√2`, and write the filter mean/difference as `a,t` and the readout as `qe+ημz`. A negative update is exactly

`a'=a−cᵢq−δ⟨pᵢ,z⟩`, `q'=q−cᵢa`,

`t'=t−δ⟨rᵢ,z⟩`, `z'=z−apᵢ−trᵢ`,

with `cᵢ=ηαᵢ`. The reference changes `a,q` and leaves `t,z` fixed. In particular, neither the cross-channel forcing nor drift of the difference filter is discarded.

The main mechanism is contraction selected by the reference-first mistake rule. For `s=a+q`, `h=a−q`, and `V=|s|+|h|`, the unforced permitted switch satisfies `V'=V−cD`, `D'=|D−cV|`, where `D=||s|−|h||`. Two consecutive updates contract by `1−ρ²/2`. A forced recurrence controls the actual dynamics without assuming continuity of the switching map across ties.

A finite-prefix bootstrap then proves `|a|,|q|≤2`, `|t−1|≤1/2`, and `‖z‖≤H`, with `H=256(B+1)/κ`. After burn-in, `|a|,|q|≤A=8δ(H+1)/ρ²≤κ/4`. Each negative mistake makes at least `κ/4` progress in separator projection, while the residual norm-squared increment is at most four. The exact contrast conditions control accumulated filter drift and cross-channel forcing, closing the bootstrap without presupposing a mistake bound. A first-crossing argument rules out `M=ceil(4096((B+1)/κ)²)` negative updates.

The reference perturbation prevents trapping on its stable line: after `L=ceil(4ρ⁻¹log(8/δ²))+2` consecutive reference updates, the unstable coordinate has magnitude at least eight while the stable coordinate has magnitude at most five. Consequently, there cannot be `L+1` consecutive reference mistakes. The scanner invariant is `Q≤n m+k+cursor`, with `m` negative mistakes and `k` total mistaken updates. Together with `k≤(L+1)m+L` this yields the additive call bound `(M+1)(N+L)`, rather than multiplying all reference retries by `N`. The public budget above is a proved simplification of this execution bound.

These arguments are in the Dynamics, Stability, Trajectory, Bootstrap, Parameters, Termination, Geometry, Counting, Trace, Execution, Budget, and Convergence proof modules sharing this basename. The independent finite-prefix bootstrap and treatment of genuine cyclic cross-channel forcing are the mathematical content; formal verification alone is not the novelty claim.

## Nontrivial instances and necessity of qualifications

For any `m≥1` and `d≥m+2`, consider arbitrary nonnegative mixtures `xᵢ=Σⱼ₌₀ᵐ⁻¹λᵢⱼEⱼ`, with total mass `Aᵢ∈[a₀,1/√2]`. Set `uᵢ=xᵢ−(Aᵢ/√d)e`. A centered unit ramp on coordinates `0,…,m`, with entries proportional to `j−m/2`, gives

`κ=a₀ sqrt(6/[m(m+1)(m+2)])`.

Neighboring pure defects have derivative inner product `−A²/2`, and nonzero plus/minus cross inner product `A²/2`. Thus this family includes overlapping mixtures, negative Gram entries, nonzero coupling, derivative rank `m`, and arbitrarily many samples. The proper-arc support is an example, not a theorem assumption. Raw signals `b₀=e`, `bᵢ=e+μxᵢ`, for `μ≤1`, fit the normalization with `g=√2`, `R=2√2`, hence `ρ=1/8`.

The regime is nonempty for every positive `κ,ρ` in range: `δ=(κρ/2)⁶⁴` suffices. This is only a conservative witness, not the required contrast rate. At fixed `ρ,a₀`, a sufficiently small constant times `δ=m⁻⁵` meets the actual conditions for all sufficiently large `m`; then `κ=Θ(m⁻³ᐟ²)` and the bound retains its polynomial dependence on `m`.

The many-sample derivative-margin class is introduced here; its margin condition is ordinary linear separability after fixed cyclic differencing, not a claim that this exact raw-data setup is a previously standard model. The pure positive reference and derivative separability have independent interpretations as detecting localized additive defects against a common background. They still exclude substantial parts of general multi-sample classification. Centering is a decomposition of background and defect, whereas derivative separability is a genuine geometric restriction. The small-contrast inequalities are new quantitative sufficient conditions, introduced to control the coupled dynamics; existing papers do not establish that these particular powers or constants are necessary. No favorable initial projection onto an unknown defect direction is assumed. The deterministic kick is essential to the proof's uniform escape statement; no noiseless cold-start convergence claim is made.

## Closest work and limits of the contribution

[Tyurin's accepted ICML 2026 paper](https://proceedings.mlr.press/v306/tyurin26a.html), [arXiv v2, 21 May 2026](https://arxiv.org/html/2512.11587v2), Theorem 5.1, analyzes two special inputs, an all-ones reference and one localized defect, with a nonzero initial spectral projection and tuned Gaussian perturbations. Its high-probability bound is `Õ(√d/μ)` in its unnormalized coordinates. Section 6 gives a representation for arbitrary data, not the finite many-sample guarantee proved here. Our change is arbitrary derivative-separable defects with full cyclic channel coupling and a finite, all-call guarantee, under the explicit stronger contrast regime and different initialization/perturbation above. It is not valid to substitute the new dataset into that two-point theorem. Neither raw `μ` nor dimensional constants should be compared without translating the normalizations.

[Yun, Krishnan, and Mobahi, ICLR 2021](https://arxiv.org/html/2010.02501v3), Theorem 2 and short-filter Corollary 4, concern gradient flow, exponential loss, structural tensor decomposition, and additional initialization/directional-convergence conditions; the short-filter corollary is for a single sample. The September 2021 v3 correction is relevant. Those results do not give the discrete switched mistake bound here. Zero initialization of one layer is already known in linear-network training and is not claimed as a new idea.

[Zhang and Peyré, arXiv:2610.09356v1](https://arxiv.org/html/2610.09356v1), Theorem 3.6, is an October 2026 unreviewed preprint on two-layer linear-network training with a smooth PL predictor objective, covariance support-gap conditions, and a step restriction depending on the initialization gap. It is not a result about these nonsmooth mistake-selected short-filter updates. General linear-network convergence is not evidence by itself for the present bound.

The decisive complexity comparison is with methods outside QPA. Explicit derivative preprocessing gives vectors `−rᵢ` of norm at most one and separating margin `κ`. Ordinary perceptron therefore has `O(κ⁻²)` mistaken updates. [Wang et al., ICLR 2023, arXiv:2210.09371v1](https://arxiv.org/html/2210.09371v1), Theorems 2–3 and Algorithm 1, give the smooth-perceptron guarantee in `O(√log(n)/κ)` full-data iterations (use `log(2n)` to include `n=1`). Taking a sufficiently large constant in the iteration bound gives strict positive margin through their regret bound, rather than relying on equality at its nonnegative-margin threshold. Each iteration forms data-wide weighted sums and scores, using `O(nd)` arithmetic on stored vectors; it is not a single component-oracle call. This is an iteration comparison, not a new oracle-class lower bound.

[Cesa-Bianchi, Conconi, and Gentile's second-order perceptron, SIAM 2005](https://doi.org/10.1137/S0097539703432542), as stated precisely in [Cesa-Bianchi's 2007 survey, Theorem 1](https://cesa-bianchi.di.unimi.it/Pubblicazioni/J30.pdf), gives the data-dependent mistake bound

`m ≤ L(u)+sqrt((a‖u‖²+uᵀAₘu) Σⱼlog(1+λⱼ(Aₘ)/a))`,

where `Aₘ` sums outer products of mistaken examples, `a>0` is regularization, and `L` is cumulative unit-margin hinge loss. This already exploits spectral anisotropy and logarithmic conditioning terms. It does not by itself assert a uniform logarithmic mistake bound for our entire geometry class: the quadratic form and spectrum still depend on the mistaken sequence. Thus logarithmic contrast dependence alone is not our novelty, and no superiority to second-order perceptron is claimed.

More decisively, at raw filter `(1,0)` and zero readout, this exact oracle's readout-gradient component is the signed sample itself. One query per sample therefore reconstructs and caches the entire dataset in `N` calls. All subsequent centering, derivative computation, and ordinary or accelerated perceptron calculations use stored vectors and cost **no additional oracle calls**. Unrestricted offline separation can obtain a centered witness `w` with norm at most one and derivative margin `κ`: projection onto the centered subspace preserves the derivative inequalities and cannot increase its norm. For example, filter mean `a=κ/4`, difference `t=1`, and readout `(μ/R)e+w` then give positive reference margin and negative margins at most `−μκ/2`, using `‖pᵢ‖≤1`; thus the cached-data solution yields an admissible raw output, not just a different classification representation. This uses no unavailable oracle information.

Relative to that `N`-call upper bound, the multiplicative gap of the proved QPA budget is

`O(κ⁻²(R/g)⁴ ℓ² [1+(R/g)ℓ/N])`.

For fixed `κ,R/g` and `N≥(R/g)ℓ`, it is `O(ℓ²)`. Small `κ`, ill-balanced backgrounds, or a small dataset leave the displayed additional gaps. Reconstruction may require storing `O(Nd)` data, whereas this scanner keeps the current `O(d)` parameter state; no memory-constrained optimality claim or artificial memory restriction is imposed in the setup. The result is a method-dynamics contribution, not new state-of-the-art problem-class oracle complexity.

The contribution is therefore specifically a finite many-sample short-filter QPA dynamics guarantee, with a proved perturbation mechanism, coupled-channel stability, and explicit regime/cost accounting. For fixed geometry parameters it approaches the `N`-call information baseline up to logarithmic factors, while for small `κ` or large `R/g` the stated polynomial gaps remain. It neither establishes universal superiority nor improves all known classification algorithms. The stronger contrast conditions, pure reference, and directed perturbation are substantive limitations when assessing its significance.

Both independent searches covered the latest publicly available ICML, ICLR, and NeurIPS editions and approximately the preceding two years of arXiv material as of 23 October 2026, following relevant older citations. Versions above distinguish accepted proceedings from preprints. The ICLR 2021 OpenReview PDF was inaccessible during the search; the corrected arXiv primary text was accessible. No absent search hit is treated as proof of novelty. The comparison is about the theorem and mechanism, not the fact that these statements are newly formalized in Lean.
