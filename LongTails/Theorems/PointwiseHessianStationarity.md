# Matching upper bound with a joint second-order oracle

The [theorem](PointwiseHessianStationarity.lean) supplies the upper half of the oracle-complexity characterization described in the [lower-bound contribution note](PointwiseHessianStationarityLowerBound.md). The new research contribution is the paired lower bound. This upper result is a faithful oracle and accuracy transfer of the repository's existing [EnergyHessianReuse](EnergyHessianReuse.lean), not a claim of a new algorithm or improved upper complexity.

The [setup](../Setups/PointwiseHessianStationarity.lean), `broadSpec`, permits any finite dimension and C³ nonconvex objective with finite initial gap Δ, initial gradient norm at most G, and global pointwise bound
\(\|D^3f(x)\|\le L_0+L_1\|\nabla f(x)\|\).
Here both coefficients are nonnegative, their sum is positive, and ε,Δ are positive. One oracle call returns the exact value, gradient and Hessian. No algorithm-family restriction is imposed.

Let \(S=\Delta\sqrt{L_0+L_1\varepsilon}/\varepsilon^{3/2}\). The proved public budget is
\[
\lceil100000S\rceil+
2\left\lceil\frac{\log(1+L_1G/(L_0+L_1\varepsilon))}{\log(4/3)}\right\rceil+200.
\]
The [algorithm](../Algorithms/JointHessianStationarity.lean) uses EnergyHessianReuse with reuse length one and absolute parameter \(L_0+L_1\varepsilon>0\). A gradient or Hessian request becomes one joint-oracle request, discarding the unused components. The returned point is the smallest observed gradient-norm point, including initialization. All burn-in, validation-gradient and Hessian calls are counted. Internal model minimization is free computation in the stated oracle model.

[JointHessianStationarity](../Proofs/JointHessianStationarity.lean) proves the actual execution equals the named `output` and its gradient norm is at most ε. This output is deterministic for every exact admissible oracle, so measurability, integrability and the expected-norm criterion follow without a probability amplification or selection oracle. [JointHessianBudget](../Proofs/JointHessianBudget.lean) proves the displayed formula dominates the complete plan length. Tuning uses the public parameters; no parameter-free adaptivity claim is made.

[Fang–Marumo–Takeda, arXiv:2607.10741v1](https://arxiv.org/html/2607.10741v1), Corollary 1, is the closest preprint upper comparison. Its first-order polynomial dependence agrees with this bound. The paired contribution note gives the precise lower regime, stronger second-order guarantees in prior work, assumption provenance, standard-reduction check and literature limitations. The public upper theorem uses the same canonical `spec` as the lower theorem: G≥16ε, S≥2^39 and d≥2^140(1+⌈S⌉)^4. This shared interface is required by the repository audit convention. The supporting `success` lemma proves the broader `broadSpec` guarantee without those three restrictions; they are not assumptions needed by the upper algorithm or its analysis. Matching is claimed in the common public regime, up to the displayed additive logarithm. The pure L0=0 boundary is handled by the positive parameter substitution rather than by assuming a nonexistent globally Lipschitz Hessian.
