# Additive stochastic fixed-point complexity in power-smooth geometry

[Main theorem](PowerSmoothAnchoring.lean), [setup](../Setups/StochasticPowerSmoothFixedPoint.lean), [algorithm and output](../Algorithms/PowerSmoothAnchoring.lean).

The result concerns a nonexpansive map on a whole Banach space, accessed through fresh unbiased noisy evaluations. It separates the cost of approaching a fixed point from the cost of estimating noisy evaluations. Its main intended improvement is for non-Hilbert geometry, particularly finite-dimensional ℓp spaces with 1 < p < 2. It is an oracle-complexity result for the problem class; the specification does not restrict competing algorithms to the constructed iteration.

The specification assumes a complete, second-countable real normed space E, a nonexpansive map T:E→E, and a fixed point xstar with ‖x0−xstar‖≤D. Parameters satisfy 1<s≤2, K≥1, D>0, σ≥0 and ε>0. The geometric assumption is the standard power-smooth inequality

\[
 \|x+y\|^s\le \|x\|^s+s j(x)[y]+K\|y\|^s,
\]

where each j(x) is a continuous linear functional. This is a geometric condition on the norm, independent of T, the oracle, and the requested accuracy. The [geometry certificate](../Proofs/PowerSmoothLpGeometry.lean) proves this condition with s=p and dimension-independent K=4 for finite-dimensional ℓp, 1<p≤2. The selected functional is used only at frozen points when taking a conditional expectation; no measurability assumption on its selection is hidden in the setup.

The oracle G is jointly measurable, Bochner integrable at every query, and satisfies E G(x,ξ)=T(x) and E‖G(x,ξ)−T(x)‖^s≤σ^s. The latter power is integrable. Samples are IID under an abstract probability law, using the repository's shared IID structure. No samplewise Lipschitz property, bounded noise, finite sample space, or ability to evaluate the same sample at two queries is assumed. The algorithm knows the displayed setup parameters and x0, but not xstar or T(x).

The returned last-stage point is the named `output` defined through `execute`. The proved accuracy is the explicit integral E‖output−T(output)‖≤ε, including integrability. This is an expected residual guarantee, not an objective-gap or high-probability theorem.

The public budget is

\[
 \left\lceil512\left(1+\frac D\epsilon+
 \left[65536K\left(\frac\sigma\epsilon\right)^s\right]^{1/(s-1)}\right)
 \left[3+\log_2\left(1+\frac{16D}\epsilon\right)\right]^{2+s/(s-1)}\right\rceil.
\]

For fixed s and K this is
\(\widetilde O(1+D/\epsilon+(K\sigma^s/\epsilon^s)^{1/(s-1)})\).
Constants and logarithmic exponents deteriorate as s approaches one; no uniform endpoint claim is made. Every execution call, including padding after the state has stopped changing, is included in the budget.

The method uses recursive anchors. Set m=clog₂(⌈16D/ε⌉+1), S=m+1, a_j=2^{j−m},

\[
 \delta=\left[1+2^m+(65536K(\sigma/\epsilon)^sS^s)^{1/(s-1)}\right]^{-1},
 \qquad N=\lceil8S/\delta\rceil.
\]

Starting with anchor A₀=a₀x0, stage j performs N updates
\(x^+=(1-\alpha_j)x+\alpha_j(G(x,\xi)+A_j)/(1+a_j)\), where
\(\alpha_j=\delta(1+a_j)/a_j\). It then adds a_j times the stage endpoint to its anchor. All step sizes lie in [0,1].

The proof tracks the normalized power error a_j^s E‖x−u_j‖^s around the exact anchored root u_j. Conditional centering and power smoothness yield a contraction by 1−δ, with stationary normalized noise floor Kδ^{s−1}σ^s independent of a_j. Doubling the anchor increases the normalized starting error by at most 3^s≤9. Consequently all stage endpoint errors stay below (ε/(32S))^s. The formal proof uses an elementary moment conversion with factor two and the metric anchor correction estimate to obtain the final residual. This cancellation of the anchor strength in the stochastic floor is the mechanism responsible for the additive complexity. Scalar norm inequalities and recursive anchoring themselves are established ingredients.

The closest same-domain comparison is [Lee, arXiv:2610.26484v1](https://arxiv.org/html/2610.26484v1), Theorem 3 and Assumptions 1–2. For whole-space ℓp, 1<p<2, matching bounded second moment, initial radius D, and expected norm residual, its bound is O(D/ε+Dσ^{p/(p−1)}/ε^{(2p−1)/(p−1)}). Taking s=p here removes the multiplicative D/ε from the statistical term, at the expense of logarithmic factors and explicit constants. Finite second moment implies the required p-moment. In particular, for fixed D>0, σ>0 and 1<p<2 as ε tends to zero, the accuracy exponent improves from (2p−1)/(p−1) to p/(p−1), up to logarithms. More generally, writing r=D/ε, A=(σ/ε)^{p/(p−1)} and L=3+log₂(1+16r), the orders compare as r(1+A) versus L^{2+p/(p−1)}(1+r+A), with constants depending on p and K. Thus min(r,A) growing faster than that logarithmic factor is a sufficient asymptotic improvement regime. There is no statistical improvement at zero noise, and no universal numerical improvement for every parameter choice is asserted.

[Diakonikolas, Guzmán and Martínez-Rubio, arXiv:2609.09524v1](https://arxiv.org/abs/2609.09524), Theorem 5 and Corollary 6, address nonexpansive self-maps of compact convex domains in general norms. Their domain model is broader in a different direction. Our whole-space theorem does not solve that constrained problem: noisy updates here may leave a prescribed compact domain. Nonexpansive retractions allow a standard reduction for special domains, but arbitrary constraints do not. In particular, this result does not contradict their high-dimensional ℓ∞ lower bound.

[Diakonikolas, arXiv:2607.09097v1](https://arxiv.org/html/2607.09097v1), Section 4.5, equation (40), discusses a prospective extension beyond second moments. Its quadratically smoothable setting and high-probability guarantees differ. Merely replacing a second moment by a lower moment is not the main novelty claimed here. Likewise, the repository's existing two-smooth Banach anchoring result already has additive complexity; neither infinite-dimensional scope nor formalization alone is claimed as new.

The assumptions allow nonlinear maps with interacting coordinates in arbitrary finite dimension. For example, T(x)=Σ_i c_i v_i tanh(⟨w_i,x⟩+b_i) is nonexpansive in ℓp if Σ_i |c_i|‖v_i‖p‖w_i‖q≤1, where q is conjugate to p. Dense vectors give coordinate interaction. Its bounded range and continuity imply a fixed point by Brouwer on a sufficiently large ball. Additive centered noise with the specified moment gives a valid oracle. This example explains scope; it is not an extra restriction imposed on the theorem.

A classical statistical comparison comes from constant maps T(x)=μ, which reduce the problem to mean estimation. With d=2n coordinates, hidden signs θ, and observations Aθ_J e_J for uniform J, at least d−n signs remain unseen after n calls. This gives expected ℓp error at least min(D/2,c_p σ n^{1/p−1}) for A=min(σ/2,Dd^{1−1/p}); the centered noise is bounded by σ. Thus the statistical exponent p/(p−1) cannot be improved uniformly over dimensions, even with bounded noise. This is a classical sparse-sign argument, not a new mean-estimation lower bound. It does not establish fixed-dimension optimality, optimal logarithms, or a matching deterministic lower bound for the full displayed complexity. This lower comparison is not formalized in Lean. The Lean convergence theorem formalizes the upper bound; the lower comparison is mathematical context rather than a second public convergence theorem.

Literature versions were checked on 3 November 2026. The three 2026 references above were each available as arXiv v1; no conference acceptance was verified for them. The research survey also examined the two most recent publicly available ICML, ICLR and NeurIPS editions and recent arXiv work, then followed stronger older references. The comparison is about theorem assumptions and oracle costs, not publication status. The mathematical novelty claim concerns the additive statistical term in the stated whole-space model.
