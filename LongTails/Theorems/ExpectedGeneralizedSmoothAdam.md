# Expected stationarity of Adam at linear generalized smoothness

The [Lean theorem](ExpectedGeneralizedSmoothAdam.lean) proves an expected squared-gradient guarantee for ordinary, uncorrected coordinate Adam under linear generalized smoothness and bounded central oracle variance. The [setup](../Setups/GeneralizedSmoothAdam.lean) fixes the Adam update family and uniform pre-update output rule, and the [algorithm](../Algorithms/GeneralizedSmoothAdam.lean) supplies explicit tuning. This is a method-specific result, not an improvement over the best oracle complexity of the problem class.

## Statement and oracle model

For arbitrary finite dimension d, the objective is differentiable everywhere, has initial gap at most Δ above a global lower bound, and satisfies

‖∇f(y)−∇f(x)‖ ≤ (L₀+L₁‖∇f(x)‖)‖y−x‖ whenever L₁‖y−x‖≤1.

The stochastic oracle g is jointly measurable, unbiased at every point, and has integrable central squared error with E‖g(x,ξ)−∇f(x)‖²≤σ². Samples are IID under an abstract sequence law; its product representation is derived inside the proof. The sample space need not be finite. Neither bounded gradients, convexity, global Lipschitz gradients, nor higher noise moments are assumed. The gap, variance, and smoothness bounds are public tuning information.

Fix any first-moment coefficient b∈[0,1). Put K=4(1+L₀+L₁), a=(1−b)²/[2²⁰(d+1)(1+K)²], and

T = ⌈2¹⁰⁰(d+1)²(1+L₀+L₁)¹⁰(1+σ²)(1+Δ)¹²/[(1−b)⁴ε⁴] + 2/(1−b)⌉.

Starting with m₀=0 and every coordinate of v₀ equal to 1+σ², use η=a/√T, β₂=1−1/T, and damping 1. At each step, update m with coefficient b and v with coefficient β₂, then subtract η m/(√v+1) coordinatewise. There is no bias correction, clipping, batching, restart, or objective-value query. After exactly T stochastic-gradient calls, return a uniformly selected point among x₀,…,x_{T−1}, independently of the samples. The theorem proves measurability of the output and integrability of its squared gradient norm and

E‖∇f(output)‖² ≤ ε².

Thus the RMS gradient norm is at most ε. The oracle budget includes the final call even when the selected point occurs earlier. All tuning and the budget are explicit in Lean; the large constants and parameter exponents are conservative.

## Closest results and contribution

[Jin et al., arXiv:2609.37787v2, 5 October 2026](https://arxiv.org/html/2609.37787v2), appears in the [NeurIPS 2026 accepted-paper index](https://neurips.cc/Downloads/2026). Under Assumptions 3.1–3.3, Theorem B.1 covers high probability for generalized-smoothness exponent p<2; Theorem B.2 covers expectation for p<1. Claim B.1 strengthens the globally smooth bounded-variance case. Our expected squared-gradient result reaches p=1, but restricts the broader conditional oracle to IID bounded central variance and does not improve that globally smooth special case. Proposition B.2's growing-variance obstruction does not settle our case.

The high-probability theorem is not an automatic proof of this expectation statement: its p=1 calibration in Section D.6 shrinks the step prefactor with log(1/δ). Fixing a positive prefactor leaves an uncontrolled tail below a positive confidence threshold. Integrating bounds for differently tuned algorithms does not bound one fixed execution. This is a limitation of that reduction, not a lower bound on Adam.

[Jin, Liang and Zou, *Why Adam Can Beat SGD: Second-Moment Normalization Yields Sharper Tails*, arXiv:2603.03099v8, 18 May 2026](https://arxiv.org/html/2603.03099v8), develops second-moment normalization and higher-moment control under global smoothness (Assumptions 2–3). Those ideas are prior work; higher-moment control alone is not the novelty here. Applying a globally smooth theorem to log(1+f−f_lower) changes both Adam moment histories, because each gradient is divided by its current objective height. It therefore analyzes a different algorithm. The present proof analyzes the original Adam execution through a logarithmic potential and then returns to the original objective.

[Pang, UAI 2026, PMLR 337](https://proceedings.mlr.press/v337/pang26a.html), uses globally bounded true gradients in Assumption 3.1 and a relaxed stationarity criterion. Those conditions and output guarantee differ from the unbounded-gradient, ordinary squared-gradient result here. [Peng et al., arXiv:2507.05966v1](https://arxiv.org/abs/2507.05966) studies sign-like behavior with a different expected norm criterion and additional trajectory restrictions; its conference status was not verified. These distinctions are scope comparisons, not claims of universal superiority.

The claimed contribution is an expected O(T⁻¹ᐟ²) squared-gradient guarantee for this ordinary Adam family at linear generalized smoothness, beyond the checked expectation theorem's exponent range. The corresponding ε⁻⁴ dependence is not a new problem-class exponent. Significance rests on resolving an expectation boundary for a widely used method without bounded gradients or higher noise moments.

## Technical mechanism

The proof first derives ‖∇f(x)‖≤K(1+f(x)−f_lower) and global smoothness of the logarithm of this positive height, using only the stated local gradient condition. An auxiliary momentum trajectory separates the current normalized innovation from denominator variation. A scalar normalization estimate controls its conditional bias and variance using only the oracle's central second moment.

A logarithmic accumulator bound and an exponential martingale maximum estimate close a feedback inequality for the maximum objective height along the original trajectory. With the explicit small step prefactor, the proof derives a uniform sixteenth moment of that height. This is a consequence, not an oracle or trajectory assumption. The original-objective auxiliary descent then yields a second-moment bound on cumulative normalized descent. A separate second-moment bound on a common denominator envelope, followed by Cauchy–Schwarz, removes the normalization and gives the expected ordinary squared-gradient bound. Future-dependent trajectory maxima are used only after taking expectations of predictable conditional variance bounds.

The main steps are in [log geometry](../Proofs/AdamLogGeometry.lean), [trajectory analysis](../Proofs/AdamGeneralizedAnalysis.lean), [original-objective descent](../Proofs/AdamGeneralizedDescent.lean), [expectation bounds](../Proofs/AdamGeneralizedExpectation.lean), and [execution and output transport](../Proofs/AdamGeneralizedExecution.lean). The intermediate bound is 2¹⁷K³√(1+σ²)(1+Δ)⁶/(a√T). Supporting algebra proves that the displayed public budget suffices.

## Instances and limitations

A nonlinear interacting-coordinate example is f(x)=Σᵢ(cosh((Ax)ᵢ)−1), with A=I+(1/(2d))11ᵀ for d≥2. Its Hessian is unbounded; A has singular values between 1 and 3/2. The inequalities ‖∇²f(x)‖≤(9/4)(1+‖∇f(x)‖) and cosh(u+t)≤exp(|t|)cosh(u) imply the stated local condition with L₀=L₁=9/2. Along x=t·1, ‖∇f(x)‖=(3/2)√d sinh(3t/2) and ‖∇²f(x)‖=(9/4)cosh(3t/2). Their ratio ‖∇²f(x)‖/‖∇f(x)‖ᵖ diverges for every p<1 as t→∞, excluding every sublinear generalized-smoothness exponent covered by the compared expectation theorem. Thus the example exhibits the added boundary class and is not confined to scalar or quadratic objectives. Additive centered noise with finite variance and infinite fourth moment is allowed, for example symmetric magnitudes 2ᵏ for integers k≥1 with probabilities proportional to 2⁻³ᵏ, scaled to the desired variance along a fixed dense unit vector.

The theorem concerns uncorrected Adam with positive second-moment initialization, constant damping, horizon-dependent β₂, and a fixed first-moment coefficient. It does not establish the same claim for zero initialization, bias correction, fixed β₂ independent of T, arbitrary adapted conditional oracles, or a last iterate. It does not assert sharp dependence on dimension, smoothness, gap, variance, or b. In particular, its conservative dependence can be much worse than existing bounds in overlapping regimes. No minimizer is required; the accuracy criterion is stationarity, not objective suboptimality.

The literature search covered public ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025/2026 material, roughly October 2024–October 2026 arXiv work and revisions, and relevant older citations. The key versions above were rechecked on 23 October 2026 UTC. This is targeted coverage, not an exhaustive certification. Some OpenReview pages, including the page associated with the Peng comparison, were inaccessible; unverified acceptance status is not used as evidence. The novelty claim must remain limited to the compared assumptions, output criterion, and actual oracle cost.
