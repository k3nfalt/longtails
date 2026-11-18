# Two necessary time scales for convex optimization on a dependent stream

How long must a first-order method observe a single stationary stream to attain a prescribed objective accuracy with confidence $1-δ$? The lower bound applies even when the method knows the moment and mixing parameters, can randomize, and can adapt each query to every previous answer. For fixed moment order and mixing exponent, its two terms give the polynomial dependence on accuracy and confidence attained by the companion upper bound, up to powers of the confidence logarithm. [Lower theorem](PolynomialMixingConfidenceLowerBound.lean) · [Upper theorem and comparison](PolynomialMixingConfidenceUpperBound.md)

## Problem and guarantee

The domain is the Euclidean ball of radius $R$ in any finite dimension $d≥1$. At call $t$, the algorithm chooses $x$ and receives $g(x,Z_t)$. The real Borel stream is stationary, with past–future absolute regularity coefficient at lag $t$ at most $(1+t/τ)^{-β}$. For each fixed $x$, the stationary mean of the jointly measurable reply supports the convex objective on the ball, and its raw norm has $p$-th moment at most $G^p$. The formal success predicate requires a measurable returned point and objective gap at most $ε$ with probability at least $1-δ$. One call advances the stream once. There is no query restriction beyond staying in the ball. [Setup](../Setups/PolynomialMixingSubgradient.lean)

Write $a=p/(p-1)$, $S=(GR/ε)^a$, and $L=\log(1/δ)$. For $1<p≤2$, $β>0$, $τ≥1$, $0<ε≤GR/8$, and $0<δ≤1/32$, for each algorithm and each nonnegative integer budget at most the following bound, some admissible instance makes its output fail the accuracy criterion

$$
\left\lfloor\frac{τ}{8(1+2β)}
\left[\left(\frac{GR}{8ε}\right)^{a(1+1/β)}\log\frac1{4δ}
+(16δ)^{-1/β}\right]\right\rfloor .
$$

Thus for fixed $p,β$ the necessary call count has order at least $τ[S^{1+1/β} L + δ^{-1/β}]$. The first term dominates when $S^{β+1}L^β≥1/δ$, up to constants depending on the fixed exponents. At fixed accuracy, taking confidence sufficiently close to one makes the second term dominant. For $p=2$ and $β=τ=G=R=1$, the inclusive lower budget is 29 at $ε=1/32,δ=1/64$, and 2731 at $ε=1/8,δ=2^{-20}$. The exponent-dependent constants matter when comparing different $p$ or $β$.

## Why both terms are necessary

Use independent Bernoulli arrivals and let the latent state mark whether a window of $m$ consecutive innovations contains an arrival. All window locations and their law are fixed before the algorithm draws its seed. To compare the whole past–future law with its product, erase the shared innovations from the past. The modified past is independent of the entire future. Each of the two law comparisons costs at most the probability of an arrival among the shared coordinates. At lag at least $m$ the windows are independent. This permits rare states of mass of order $b$ to persist for order $τ b^{-1/β}$ steps while respecting the specified mixing envelope. [Burst law](../Proofs/PolynomialMixingBurstLaw.lean) · [Width calibration](../Proofs/PolynomialMixingBurstCalibration.lean)

For the accuracy term, put the distinguishing gradient in the rare state and scale its magnitude as $G b^{-1/p}$. Choosing $b$ of order $1/S$ keeps the raw moment within budget and separates the two linear optima. A long stretch without arrivals gives identical replies for opposite objectives. For the confidence term, take $b=8δ$ and interchange the roles of active and silent states. One arrival shared by all windows can now suppress *every* informative reply throughout a stretch of order $τδ^{-1/β}$. In each test the common-transcript event has probability strictly greater than $2δ$. Conditional on the same private seed, the two outputs coincide on that event, and no output can solve both signs. One sign therefore fails the confidence criterion. The hard objectives use one coordinate and embed in every admitted dimension. [Prefix probabilities](../Proofs/PolynomialMixingBurstTesting.lean) · [Execution test](../Proofs/PolynomialMixingLinearTesting.lean) · [Hard instances](../Proofs/PolynomialMixingHardInstance.lean)

## Relation to prior lower bounds

The sticky-chain reduction in Sarkar, Chakrabartty, and Aggarwal gives a related heavy-tail lower bound for geometrically mixing Markov noise and smooth PL objectives. Its constant-probability heavy-tail test does not resolve how a prescribed failure probability interacts with polynomial absolute regularity. Here two laws in the same oracle class give separate obstructions, including a confidence cost that persists at fixed accuracy. Lerasle and Oliveira's dependent-block results already exhibit a mixing penalty at high confidence for scalar estimation. The contribution of the pair is the joint necessity and sufficiency, to logarithmic accuracy, of the two time scales for adaptive convex optimization. The exact logarithmic gap remains open. [Sarkar et al., v1, Corollary 3 and Theorem 4](https://arxiv.org/pdf/2606.26316) · [Lerasle and Oliveira, v1, Proposition 16 and Remark 15](https://arxiv.org/pdf/1112.3914)

The existing smooth Markov results already give the same leading accuracy exponent in their noise-dominated regime for expected objective gap. Their centered-noise and smoothness parameters enter separate terms. An expected-gap bound gives constant-confidence accuracy by Markov’s inequality, while attaining variable confidence on one dependent trajectory also requires controlling rare uninformative stretches and selecting the returned point. The new lower confidence term and its matching upper exponent concern this latter problem. [Previous lower bound](PolynomialMixingHeavyTailedConvexLowerBound.lean) · [Previous upper bound](AcceleratedHeavyTailedMarkovConvex.lean)
