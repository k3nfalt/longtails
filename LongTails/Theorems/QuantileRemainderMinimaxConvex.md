# The minimax cost of centered asymmetry with quantile-only gradient noise

The [convergence theorem](QuantileRemainderMinimaxConvex.lean) gives expected objective accuracy for general smooth convex optimization when the stochastic gradient need not have an expectation, or any finite positive moment. The accompanying [oracle lower bound](../Proofs/QuantileMinimax.lean) identifies an asymmetry penalty of order `d² M² R⁴ / ε⁴`, up to a logarithmic factor in the upper bound, in the small-accuracy regime specified below. The contribution is this minimax characterization of a centered asymmetric remainder under only a noise quantile bound. The estimator, accelerated descent analysis, and testing inequality are established ingredients; the upper bound alone is not claimed as a new state of the art.

## Problem and oracle

The [Lean setup](../Setups/QuantileSymmetricRemainderConvex.lean) assumes a differentiable convex objective on `ℝᵈ`, an `L`-Lipschitz gradient, and a minimizer `xstar` with `‖x0-xstar‖ ≤ R`. Here `d ≥ 1`, `L,R,r,ε > 0`, and `M ≥ 0`. Each oracle call returns a vector `g(x,ξ)`. The oracle is jointly measurable. Samples are IID with an abstract probability law and independent of the algorithm's random seed; the public specification does not prescribe a product probability space.

For every point and coordinate, the law `μ` of `g_i(x,ξ)-∇_i f(x)` must satisfy

- `μ = S + A`, where `S,A` are positive finite measures and `S` is invariant under reflection;
- `∫ z dA = 0` and `∫ z² dA ≤ M`, with both integrability conditions explicit;
- `μ{|z| > r} ≤ 1/64`.

Neither component labels nor the decomposition are available to the algorithm. The components are subprobability measures, not normalized conditional laws. Coordinate dependence is unrestricted, and their laws may depend on the query point. The full oracle has no unbiasedness or variance assumption. Its center must not be interpreted as an ordinary or principal-value expectation.

The model extends the centered odd-part condition in Puchkin et al., [AISTATS 2024, Assumption 2.1](https://proceedings.mlr.press/v238/puchkin24a/puchkin24a.pdf). For a density `p`, write `r_p(z)=(p(z)-p(-z))/2`. If `∫z r_p(z)dz=0` and `∫z²|r_p(z)|dz≤M`, take the symmetric density `min(p(z),p(-z))` and remainder `(p(z)-p(-z))_+`. The remainder is centered and its second moment equals that weighted absolute odd-part moment. Conversely a decomposition above bounds the weighted absolute odd part by `M` and makes its first moment zero. Thus the formulations agree on densities. Here density existence and Puchkin et al.'s convolution-tail control are replaced by a single fixed quantile condition. The class relation is not an assertion that every numerical choice of their parameters yields the same `r`; a uniform `r` must be obtained from the particular baseline tail assumption.

Quantile rather than moment control also has a primary precedent in Novikov, Steurer and Tiegel, [NeurIPS 2023, Definition 1.2 and Definition A.1](https://proceedings.neurips.cc/paper_files/paper/2023/file/6c59ace4fc4872a14df13d91762ad4f0-Paper-Conference.pdf). Their semi-product model combines coordinate central-mass bounds with symmetry and independence conditions on signs. The present combination with a centered asymmetric remainder is the target extension, not their unchanged model: it imposes no sign independence but uses a known high central quantile, of mass at least `63/64`. A weaker central-mass bound at the same radius does not imply this numerical condition without additional information. The radius here is explicitly the scale of that high quantile.

This is a mixture-corruption model with a possibly moment-free symmetric background and a centered finite-second-moment asymmetric component. For example, independently of the query, take

`S=(1-ρ-η)δ₀+η H`, `A=ρ[(2/3)δ_{-a}+(1/3)δ_{2a}]`,

where `a≥0`, `0≤ρ,η`, `ρ+η≤1`, `η≤1/64`, `r≥2a`, and `H` has symmetric density `1/[2(e+|z|) log²(e+|z|)]`. Then `M=2ρa²` suffices, and every positive noise moment is infinite if `η>0`. This mechanism applies, for example, to interacting nonlinear objectives `Σ_j w_j log cosh(a_j·x-b_j)+μ‖x‖²/2`, with positive weights, `μ>0`, and dense nonorthogonal vectors `a_j`. Their smoothness constant is at most `μ+Σ_j w_j‖a_j‖²`; a valid radius bound remains part of the problem data. The theorem does not require separability, quadratics, or a fixed dimension.

## Algorithm and proved upper bound

The [algorithm](../Algorithms/CharacteristicGradient.lean) uses projected accelerated stochastic-gradient updates, with query points in the ball of radius `R` around `x0`. It returns the final projected accelerated primal iterate, as named by `output`. Smoothness and the minimizer radius imply `‖∇f(x)‖≤2LR` at every query; there is no global bounded-gradient assumption.

For readability define

`a = √d R(2LR+r)/ε + 8dMR²/ε²`,

`H = 8(2LR+r)+64√d MR/ε`, `t=1/H`,

`K = 1+ceil(log(1+512a)/log 2)`,

`N = 1+ceil(4√(LR²/ε)+32768a²)`,

`D = 2L+64NdH²/ε`.

At each of the `N` iterations, the method makes exactly `K` raw oracle calls at the same query. For each coordinate of those replies `Y_j`, set `U_j=1-exp(itY_j)` and return the scalar gradient estimate

`-Im[Σ_{k=1}^K (U₁⋯U_k)/k]/t`.

The finite product-series construction is a known device: see Chopin, Crucinio and Singh, [Biometrika 2025, equation (4) and Proposition 7; arXiv v3](https://arxiv.org/html/2403.20313v3). No new-estimator claim is made here. Independent samples make its expectation a truncated logarithm of the characteristic function. Symmetry contributes no imaginary part, and centering plus the asymmetric second-moment bound gives noise phase bias at most `Mt`. The quantile condition gives a contraction for the bounded complex transforms. The proved vector bias is at most `√d(Mt+2^{-K}/t)` and its error second moment at most `4d/t²`, even if the original gradients have no moments. Coordinate independence is unnecessary.

The [local projected analysis and execution proof](../Proofs/CharacteristicConvergence.lean), with [explicit tuning inequalities](../Proofs/CharacteristicTuning.lean), establish measurability, integrability, and

`∫ [f(output)-f(xstar)] dP ≤ ε`.

The public budget is the fully expanded `N K` formula in the theorem file. There are no uncounted pilot, reference-gradient, validation, or output-selection calls. Its order is

`O(log(2+a) [1+√(LR²/ε)+dR²(2LR+r)²/ε²+d²M²R⁴/ε⁴])`.

The algorithm uses the public bounds `d,L,R,r,M` and target `ε`; it does not adapt to unknown values of those bounds. The abstract IID execution law is derived internally from independence; it is not an extra sampling restriction.

## Matching lower bound and new mechanism

The lemma `oracle_complexity_lower` in [QuantileMinimax.lean](../Proofs/QuantileMinimax.lean) rules out uniform success for every adaptive randomized oracle algorithm with `N` calls when `M>0`,

`ε ≤ LR²/16`, `ε ≤ rR√d/16`, `ε² ≤ dMR²/2¹⁷`,

and

`N ≤ d²M²R⁴/(2³¹ ε⁴)`.

It uses the same fixed `d,L,R,r,M` class, with the sufficiently rich, fixed public sample space `Ω=ℝ` and `x0=0`. It does not assert a lower bound for every sample-space type, which would be false for a singleton. Outputs and internal randomness are unrestricted except for the measurability and integrability required by success itself. A finite-prefix measure-transfer proof connects arbitrary adaptive execution to testing; strictly positive finite-code weights justify integrability of every seed section.

The central construction is a pair of remote-shell distributions. Set `w=1/64`, `k=ceil(M/(4h²))`, and `a_shell=1/(3k)`. Each law puts mass `1-w` at zero, and distributes masses `w/2±a_shell` uniformly over the grids `jh`, `j=k,…,2k`, and their negatives. The two laws have centers `±h`. After translating by their centers, a symmetric overlap can be removed, leaving a positive centered remainder with second moment at most `3kh²≤M`. Their quantile radius stays at `r` when `h≤r`, yet their testing divergence is at most `4096h⁴/M²`. All membership, moment, reflection, and divergence bounds are proved in [QuantileShellOracle.lean](../Proofs/QuantileShellOracle.lean).

Embed the scalar laws along `v=(1,…,1)/√d`, with objectives `f_±(x)=(h√d/(2R))‖x∓Rv‖²` and common oracle answer `g(x,Y)=(h√d/R)x-Y(1,…,1)`. Adaptive queries reveal only the same raw scalar observations. Wrong-sign decoding costs at least `hR√d/2`. Choosing `h=16ε/(R√d)` yields the bound above.

The new ingredient is preserving the fixed quantile and centered-remainder constraints while making center separation `h` have divergence of order `h⁴/M²`. A generic bounded-variance lower bound cannot simply be instantiated with variance `M²/h²`: Gaussian hard instances violate the fixed quantile, while the usual rare-event asymmetric hard instances violate the fixed remainder second-moment bound. Remote symmetric mass and a small imbalance resolve both constraints simultaneously. The subsequent testing-to-optimization reduction is standard; compare Agarwal et al., [2012, Definition 1 and Section 4.2](https://www.stat.berkeley.edu/~bartlett/papers/abrw-itlbocsco-12.pdf). The general contamination modulus framework of Chen, Gao and Ren, [Theorem 3.2](https://arxiv.org/pdf/1511.04144), does not itself compute this class's centered-remainder modulus or its uncontaminated IID oracle complexity.

The factor `d²` is a worst-case consequence of per-coordinate `M` and permitted correlated noise: the embedded direction has effective remainder scale `dM`. It is not a new high-dimensional packing phenomenon, nor a lower bound for independent coordinate noise. The lower-bound objectives are quadratics, as witnesses inside the general nonlinear upper-bound class. The hard laws vary with accuracy, as in an ordinary minimax lower bound; this is not a pointwise asymptotic statement about one fixed noise law. The witnesses have finite moments individually, although no uniform total-noise moment bound is imposed.

The construction is not inherently discrete. Convolving both raw laws with the same independent uniform law on `[-h/2,h/2]` gives densities. Symmetry and centering are preserved, the asymmetric second moment increases by at most `h²/12`, and

`3kh²+h²/12 ≤ 3M/4+(37/12)h² ≤ 4645M/6144 < M`

when `h²≤M/512`. The quantile condition becomes `3h/2≤r`. Testing cannot become easier after common smoothing, or one can retain the independent smoothing variables as ancillary data. This robustness calculation explains why atomic support is not the source of the penalty; the formal lower-bound witness uses the simpler atomic version.

## Closest results, limitations, and literature coverage

Puchkin et al.'s [AISTATS 2024 paper](https://proceedings.mlr.press/v238/puchkin24a.html), especially Assumption 2.1, Lemma A.1, Lemma 4.5, and Theorem 5.7, is the closest structural baseline. Its symmetric-heavy-tail plus centered asymmetric remainder model and biased accelerated optimization machinery are prior work. Standard smoothing, batching, median estimation, and clipping already give upper bounds of the relevant order after parameter adjustment; the present upper bound is not advertised as novel merely because it uses characteristic functions. For finite polynomial-tail assumptions, analogous proposed improvements can also follow from those reductions and are not claimed here.

For completeness, the standard reduction calculation is as follows. Put `G=2LR`, add independent Gaussian smoothing of scale `θ≥G+r` to each raw coordinate, and use a coordinate median of `m` smoothed samples, clipped at a threshold of order `G+θ`. The second-derivative comparison underlying Puchkin et al.'s Lemma A.1 bounds the CDF difference from the symmetrized law by `O(M/θ²)`; the median's CDF is Lipschitz in its input CDF with constant at most `m`. Integrating over the clipping interval gives bias `O(mM/θ)+O(G exp(-cm))`, while the second moment is `O(θ²)`. The central quantile supplies a uniform amount of mass on the smoothing scale; no total-noise moment is used. Choose `m` of order `log(2+G√dR/ε)` and `θ` of order `G+r+mM√dR/ε`, with sufficiently large universal constants. Biased accelerated optimization then takes order `m[1+√(LR²/ε)+dR²θ²/ε²]` raw oracle calls, including every sample used by the median. Its dominant term is `d²M²R⁴/ε⁴` times logarithmic factors. This is a derived composition of known arguments, not a claim that a published theorem already states the unchanged quantile-only assumptions. It rules out claiming the upper exponent alone as the contribution.


Armacki et al., [AISTATS 2025, Assumption 5 and Theorem 3](https://proceedings.mlr.press/v258/armacki25a.html), study a symmetric density with a small arbitrary asymmetric contamination, obtaining a nonzero stationarity neighborhood. Arbitrary contamination is not the centered finite-second-remainder class here. The sharper [moment-free nonlinear-SGD analysis, arXiv 2507.09093 v2](https://arxiv.org/html/2507.09093v2), uses symmetry for its principal guarantee and an exact reference gradient in its arbitrary-asymmetry construction; oracle access and accuracy criteria therefore differ. The authors report its IEEE Transactions on Information Theory publication ([DOI 10.1109/TIT.2026.3682577](https://doi.org/10.1109/TIT.2026.3682577)); the publisher page and final journal full text were inaccessible during this survey. These results must not be described as superseded under their own assumptions.

Exact symmetry is materially easier: with a fixed central quantile, logarithmic batching plus coordinate medians and clipping yields the usual noise-dependent convex `ε⁻²` order despite arbitrarily heavy tails. The `ε⁻⁴` lower bound identifies the price of allowing a nonzero centered asymmetric remainder while retaining only quantile information. For example, within the lower-bound regime, `ε≤√dMR/(2LR+r)` and `d²M²R⁴/ε⁴≥1+√(LR²/ε)` ensure that the displayed upper budget is of order `d²M²R⁴/ε⁴` times its logarithmic batching factor. These conditions hold eventually as `ε→0` for every fixed positive `d,L,R,r,M`. The matching claim applies to this noise-dominated regime; there is no claim of simultaneous optimality in all parameters, exact constants, logarithmic factors, or the `M=0` case. In particular, the upper bound retains a `2LR` term and is not the strongest symmetric-noise guarantee.

The Researcher and independent Reviewer separately surveyed official ICML 2025–2026, ICLR 2025–2026, and NeurIPS 2024–2025 material and approximately the preceding two years of arXiv submissions and revisions, beginning on 18 October 2026 UTC, then followed older primary references. Relevant versions checked include Puchkin et al. 2311.04161 v2 (17 April 2024), Chopin et al. 2403.20313 v3 (31 March 2025), Armacki et al. 2410.13954 v2 (21 March 2025), 2410.15637 v2 (22 March 2025), and 2507.09093 v2 (10 February 2026). Recent finite-moment, symmetric-unimodal, reference-gradient, and contamination results were compared separately rather than transferred across models. Classical symmetric-core contamination and location-estimation references were also checked; Jaeckel's 1971 full text and the final IEEE journal text above were inaccessible. A December-2025 heavy-tail manuscript, arXiv 2512.14686, had inconsistent abstract/HTML version dates; its checked assumptions require positive moments and differ from this class. This is a scoped primary-source survey, not a proof that no related result can exist.
