# A fixed-ball lower bound for noisy pairwise optimization

For dimension d ≥ 1, integer j ≥ 0 and 0 < ε ≤ 1/64, for every randomized adaptive algorithm and every budget up to and including

$$
\left\lfloor\frac{d^2}{65536(2j+1)^2\varepsilon^2}\right\rfloor,
$$

there is an admissible loss and comparison oracle on which that algorithm fails at that budget. Success requires a measurable feasible output with integrable objective gap and expected gap at most ε. The domain is the same unit Euclidean ball for every budget. The setup specializes the paired upper theorem to μ=1/2, L=2, G=4, r=1, k=2j, c=(2j+1)/8 and M=(2j+1)/4. It inherits the full class of randomized algorithms, their available information and the IID one-bit comparison interface. These choices give matching Θ(d²/ε²) comparison complexity as a function of dimension and accuracy for each fixed j. [Lower theorem](LocalReferenceDuelingLowerBound.lean) · [Setup](../Setups/FlatTransferDueling.lean) · [Upper theorem and algorithm](LocalReferenceDueling.md)

## Hard family and information bound

Set h²=1024ε/d and choose a hidden vector of signs θ. The loss is the sum over coordinates i of

$$
\tfrac12 x_i^2-\tfrac14\theta_i h^2\sin((x_i-\theta_i h/4)/h).
$$

The minimum is attained at xᵢ=θᵢh/4, which lies in the unit ball throughout the stated regime. Each coordinate has second derivative between 3/4 and 5/4. Every wrong output sign contributes at least h²/64 to the gap. The lower-bound family is separable, while the upper theorem includes interacting nonlinear objectives. The hard link is the same for every instance, ρ(t)=arctan(t^(2j+1))/4. It is smooth, saturates and satisfies the required local derivative envelope. [Loss and minimizer](../Proofs/DuelingSignFamily.lean) · [Transfer](../Proofs/DuelingFlatTransfer.lean) · [Admissible oracle](../Proofs/DuelingSignOracle.lean)

Flipping one hidden sign changes the loss at any point by at most h²/2. Even when comparing distant points, the two Bernoulli success probabilities differ by at most (2j+1)h²/8. Both lie in [1/4,3/4]. Conditioning on the algorithm seed yields a binary decision tree. A recursive affinity bound for neighboring trees shows that the sum of the two sign-testing errors is at least 1/4 at the stated budget. Averaging over the hypercube gives at least d/8 sign mistakes, hence at least 2ε average objective gap. Integrating over algorithm seeds gives a single hard instance independent of the realized seed. The template includes budget zero. An algorithm that decides its output early can retain it through the remaining queries while ignoring their replies. [Binary testing](../Proofs/DuelingBinaryTesting.lean) · [Execution](../Proofs/DuelingTestingExecution.lean) · [Minimax proof](../Proofs/DuelingReferenceLowerBound.lean)

## Relation to prior work

The accuracy-dependent query cube in Jamieson, Nowak and Recht, Lemma 1 and Theorem 1, can suppress the signal of every reference as the target error decreases. A fixed ball and a single stationary transfer permit informative reference queries even near the minimizer. The uniformly bounded sign perturbation bounds the information in every such query on the full domain. Shamir's Theorem 7 obtains a related dimension-dependent obstruction for smooth strongly convex optimization under noisy function-value feedback. Its oracle returns real values and its testing calculation does not directly cover nonlinear one-bit comparisons. Here the paired upper bound and the testing argument apply to the same query and error model. [Jamieson et al., NeurIPS 2012](https://proceedings.neurips.cc/paper_files/paper/2012/file/e6d8545daa42d5ced125a4bf747b3688-Paper.pdf) · [Shamir, COLT 2013](https://proceedings.mlr.press/v30/Shamir13.pdf)

Saha, Koren and Mansour's ICML 2025 Theorem 4 has inverse accuracy exponent 2p for link order p under its high-probability criterion. For an odd order p=2j+1 on the normalized class, the two present results give exponent two for expected gap. The upper proof needs a fixed radius, a public local derivative upper bound and the geometry of the ball. The lower proof gives the full dimension and accuracy obstruction there. A matching dependence on j or general upper-theorem parameters and a tunable-confidence comparison remain unresolved. [ICML proceedings](https://proceedings.mlr.press/v267/saha25a.html) · [Upper proof and comparison](LocalReferenceDueling.md)
