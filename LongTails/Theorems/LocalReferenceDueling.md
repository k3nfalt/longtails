# Strongly convex optimization from flat comparison feedback

How many noisy pairwise preferences suffice to minimize a loss on a fixed Euclidean unit ball? For each fixed odd transfer order, the minimax number of comparisons for expected objective error ε scales as **Θ(d²/ε²)** on the normalized class below. Even when an almost tied pair produces a nearly fair coin, the algorithm can choose a third point as its opponent. Strong convexity supplies informative opponents everywhere in the ball, including at its boundary. [Upper theorem](LocalReferenceDueling.lean) · [Lower theorem and regime](LocalReferenceDuelingLowerBound.md)

## Problem and returned point

The loss has a continuously differentiable extension to Euclidean space of arbitrary dimension d ≥ 1. On the unit ball it is μ-strongly convex, L-smooth and G-Lipschitz. Each query specifies two feasible points x,y and returns one sign of mean ρ(f(x)−f(y)), using a fresh IID sample. The unknown common transfer ρ is bounded by one in absolute value, odd, nondecreasing and continuously differentiable. For |t| ≤ r its derivative lies between c|t|ᵏ and M. The algorithm knows the bounds, the integer k ≥ 0 and ε. Its only observations are comparison bits. The objective minimizer u is relative to the ball. [Lean specification](../Setups/StronglyConvexDueling.lean)

These conditions permit coupled nonlinear losses. For example, add a linear tilt and a sum of positive multiples of log cosh of nonorthogonal linear forms to a positive definite quadratic. The Hessian lies between the quadratic Hessian and that Hessian plus the weighted sum of the corresponding rank-one matrices. The gradient is bounded on the unit ball, and a sufficiently large tilt places the constrained minimizer on its boundary. An example transfer is ρ(t) = arctan(tᵖ)/4 for odd p = k+1. Its derivative vanishes at ties for p > 1.

Put C = max(1,8G/r), s = 1/C, m = c(μs²/4)ᵏ/3 and h = min(s,m√(με)/(4ML)). Starting at zero, at iteration t choose an independent uniform sphere direction v and uniformly choose one of the three opponents z, z+se, z−se, where z = (1−s)x and e is a fixed unit coordinate vector. Compare (1−h)x+hv to that opponent. For the observed sign b use the estimate (d/h)bv and take a projected step of size 4/[mμ(t+2)]. Return the average of the pre-update iterates with weights t+1, starting at t = 0. Each update costs one comparison, including its random choice of opponent. [Algorithm and execution output](../Algorithms/DuelingReferenceDescent.lean)

## Guarantee and proof

The expected loss of the returned average is at most f(u)+ε. The public comparison budget is the ceiling of

$$
\frac{72d^2(4/\mu)^{2k} C^{4k+2}}{c^2\mu\varepsilon}
+
\frac{10368(dML)^2(4/\mu)^{4k} C^{8k}}{(c^2\mu\varepsilon)^2}.
$$

The three opponent values span at least μs²/2 by midpoint strong convexity. For each query value at least one opponent differs by μs²/4 or more, and all differences lie inside the local derivative window. Thus the average transfer derivative is at least m. Freeze the opponent distribution at x while smoothing the query point. The sphere-to-ball identity expresses the conditional mean estimate as a positive multiple of ∇f(x) plus a vector of norm at most 2MLh. This error bound uses smoothness of the loss and the upper bound on the transfer derivative. The unknown multiplier can vary each iteration. A weighted projected-descent inequality absorbs the error using curvature and sums directly in the original objective. The estimator has squared norm d²/h², which accounts for the second inverse power of ε. [Conditional descent](../Proofs/DuelingReferenceConvergence.lean) · [Execution-level expectation](../Proofs/DuelingReferenceUpperBound.lean)

## Comparison and limits

Saha, Koren and Mansour use the same local derivative lower envelope (Assumption 1 with p = k+1). Their ICML 2025 Theorem 4 gives a returned point with tunable confidence, with comparison complexity scaling as d^(2p+1) ε^(−2p) up to logarithms for fixed regularity parameters. They assume the global minimizer lies in the domain. On the common fixed-ball class, the loss range is at most 2G, so their bound at tolerance ε/2 and failure probability min(1/2,ε/(4G)) gives expected error at most ε. For p > 1 the new bound improves both exponents, and for p = 1 it improves the dimension dependence of that theorem. Our guarantee is in expectation. The unit ball supplies room for a feasible reference chord of fixed length. We assume a common odd C¹ link and a public local derivative upper bound. Quantitative regularity and a radius independent of ε matter for the comparison. [ICML proceedings, Assumption 1 and Theorem 4](https://proceedings.mlr.press/v267/saha25a.html)

Random-opponent comparisons also appear in the Borda-function approach of Xu et al., whose Proposition 1 in §3.2 uses a pointwise bi-Lipschitz link. That argument supplies no positive pointwise lower slope at a flat tie. Repeating a nearly tied comparison estimates its sign at a cost inverse quadratic in its mean. The three local references give a uniform slope after averaging with one comparison per iteration. The lower bound in Jamieson, Nowak and Recht uses a general comparison-margin model and an accuracy-dependent query cube in Lemma 1. Its different regime allows the range of reference values to shrink. [Xu et al., UAI 2020](https://proceedings.mlr.press/v124/xu20b/xu20b.pdf) · [Jamieson, Nowak and Recht, NeurIPS 2012](https://proceedings.neurips.cc/paper_files/paper/2012/file/e6d8545daa42d5ced125a4bf747b3688-Paper.pdf)

The paired lower bound matches the dimension and accuracy dependence for fixed j with k=2j, μ=1/2, L=2, G=4, r=1, c=(2j+1)/8 and M=(2j+1)/4 for 0 < ε ≤ 1/64. Dependence on increasing flatness order, a shrinking derivative window, confidence and conditioning remains open. [Normalized lower-bound specification](../Setups/FlatTransferDueling.lean)
