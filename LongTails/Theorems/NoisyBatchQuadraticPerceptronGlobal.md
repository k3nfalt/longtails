The result proves global convergence of the noisy, averaged-batch quadratic perceptron for an arbitrary finite linearly separable dataset and arbitrary initialization. It concerns the width-one two-layer model $m(b;c,v)=v\langle b,c\rangle$, with both factors trained. With fixed positive Gaussian noise and a fixed explicit step size, the method almost surely discovers a strict separator. Its certified output then remains constant. An explicit finite-confidence oracle budget is also proved. The contribution is a global dynamics guarantee for this method, not an improvement in the best complexity of linear classification or a proof of acceleration.

The formal entry points are the [main convergence theorem](NoisyBatchQuadraticPerceptronGlobal.lean), [setup and update-family specification](../Setups/NoisyBatchQuadraticPerceptron.lean), [algorithm and named output](../Algorithms/NoisyBatchQuadraticPerceptron.lean), and [almost-sure and regeneration proofs](../Proofs/NoisyBatchQuadraticPerceptronRegeneration.lean). The almost-sure statement is `output_eventually_constant_separating_ae`; the exported `result : Convergence spec budget` gives the finite-confidence guarantee for actual `execute` calls.

For signed observations $a_i=y_i b_i\in\mathbb R^d$, $i\in[n]$, assume $n\ge1$, $0<\delta\le R$, $\|a_i\|\le R$, and a unit vector $u$ with $\langle a_i,u\rangle\ge\delta$. The algorithm knows $n,R,\delta$, its initial weights $w_0=(c_0,v_0)$, and a noise scale $\sigma>0$. It does not know the separator $u$. Data are accessed through an indexed oracle returning the signed margin $v\langle a_i,c\rangle$ and its parameter gradient $(v a_i,\langle a_i,c\rangle)$. The specification quantifies over all oracles giving these exact replies, including arbitrary oracle seed laws.

The data assumptions are the standard bounded, positive-margin linear-separability assumptions. They do not impose sample rank, a special spectrum, two-sample geometry, coordinate separability, or a cone condition on initialization. For example, take $a_i=\delta u+b_i$, where $b_i\perp u$, $\|b_i\|\le\sqrt{R^2-\delta^2}$, and choose arbitrarily many dense, mutually interacting $b_i$. This includes rank-deficient and full-span datasets in arbitrary finite dimension. For $R>\delta$, the orthogonal components need not share any eigenbasis or have a prescribed covariance. Dimension zero has no admissible positive-margin instance.

Set
\[
\eta=\frac{\delta}{8(n+1)R^2},\qquad
 g_t=\frac1n\sum_{i:v_t\langle a_i,c_t\rangle\le0}a_i.
\]
Until certification, each full scan holds the weights fixed, aggregates all violated examples, and performs the simultaneous update
\[
(c_{t+1},v_{t+1})=(c_t+\eta v_tg_t,\ v_t+\eta\langle g_t,c_t\rangle)+\sigma Z_t,
\qquad Z_t\stackrel{\mathrm{IID}}\sim N(0,I_{d+1}).
\]
Ties are included among violations. A full scan with every margin strictly positive freezes the output before another perturbation is applied. The state machine, query rule, simultaneous averaged update, fixed positive step size, and output rule are enforced by `family` and its compliance proof. Confidence affects only the execution budget, not the step size, noise, or trajectory. The noise is specified on an abstract probability space using the repository's IID structure, with measurable sample maps, independence, and Gaussian marginal laws; a product sample space is not imposed.

This is the noisy QPA mechanism motivated in §4 of [Tyurin, arXiv:2512.11587v2, 21 May 2026](https://arxiv.org/html/2512.11587v2), specialized to the width-one case of its two-layer model. Its Theorem 5.1 studies a non-batch two-sample convolutional instance with specially tuned noise and initialization conditions. The present result instead covers arbitrary sample count, all initial weights, and one fixed positive noise scale for an infinite trajectory. It does **not** subsume that convolutional theorem or retain its acceleration rate. The existing repository theorem `TwoSampleQuadraticPerceptronAcceleration`, which has both two-layer and convolutional cases, remains unchanged. The overlap is its two-layer model; the new result changes its noiseless priority updates to noisy averaged batches. Thus the requested extension is in dataset coverage and almost-sure convergence within the paper's QPA family, not a larger-dataset acceleration theorem. [Official ICML 2026 proceedings](https://proceedings.mlr.press/v306/tyurin26a.html) confirm acceptance; comparisons here use the accessible arXiv v2 text.

Write $D=d+1$, $E_0=\|w_0\|^2$, and
\[
M=(n+1)^2(R/\delta)^2,\qquad A=25000D^2M^2.
\]
For every $0<\rho<1$, the public budget is the single explicit formula
\[
\boxed{\quad
\left\lceil \frac{100000n}{\rho}
\left(M+\frac{E_0}{D\sigma^2}\right)
\left(\frac2\rho\right)^{5\exp(A)}\right\rceil.
\quad}
\]
At this budget, the probability that the named output has any nonpositive training margin is at most $\rho$, under the product of the algorithm's explicit noise law and the oracle's seed law. The proof also applies at larger budgets. Every individual example query is counted, including scans used for unsuccessful trials, the preliminary update, certification, and any calls made by fixed-budget execution after freezing. The bound is intentionally conservative: for fixed geometry it is a power of $1/\rho$, with an exponent exponential in $D^2(n+1)^4(R/\delta)^4$. No optimality or practical efficiency is asserted.

The almost-sure result is stronger than a family of guarantees for differently tuned algorithms. For the same fixed $\eta,\sigma$, almost every noise realization has a finite random $N_0$ and a strictly separating weight $w_*$ such that the actual output equals $w_*$ for **every** call budget $L\ge N_0$ and every oracle seed sequence. This is convergence of the certified, frozen output. It is not convergence of an indefinitely perturbed, unfrozen weight process, nor a claim that `execute` stops issuing calls. The proof does not establish finite expected time to final discovery. The case $\sigma=0$ is excluded; Gaussian positivity is essential to the escape argument. At zero initialization, independence of the classification trajectory from positive noise scale after rescaling is elementary homogeneity, not the novelty claim.

The new mechanism controls both-factor dynamics without assuming bounded iterates. Define
\[
p(c)=\frac1n\sum_i(\langle a_i,c\rangle)_+,\quad
q(c)=\frac1n\sum_i(-\langle a_i,c\rangle)_+,\quad
m=\frac1n\sum_i a_i.
\]
The proof uses the nonsmooth potential
\[
V(c,v)=\|c\|^2-v^2+\eta v\langle m,c\rangle
 +2(v-\eta p(c))_+^2+2(-v-\eta q(c))_+^2.
\]
For the chosen step size, $\tfrac12\|w\|^2\le V(w)\le2\|w\|^2$. Adding Gaussian noise increases its mean by at most $6D\sigma^2$. Away from a low-gap region and two robust escape regions, the noiseless update decreases it by at least $\eta^2(pq+R^2v^2)/4$. The low-gap region is unbounded; the argument does not replace it by a compact set or assume a stationary distribution.

Two complementary ingredients handle exits from that drift region. In the low-gap and small-output cases, a uniformly bounded Gaussian displacement produces a separator. In the large-output escape cases, a shifted imbalance controls the coupled factors for a finite sequence of small perturbations and forces separation by a margin-progress contradiction. A common lower bound on conditional trial success is $e^{-A}$, with trial length $B=\lceil16n/(\eta\delta)\rceil+2\le129M$. These are state-dependent successful noise events analyzed uniformly; the algorithm itself performs no restarts or tests of these proof regions.

Finite-history exit partitions transfer these bounds to random cycle starts. Positive-time zero-output events are removed only as Gaussian null sets. The proofs establish summability before rearranging exit costs and do not assume independent cycles or treat a defaulted first-exit index as a stopping time. Active mass is at most $(1-e^{-A})^j$, and starting-potential mass is at most $128^j(4E_0+(2+B)D\sigma^2)$. The accumulated clock includes paths that succeed early, with all subsequent durations zero. It satisfies
\[
\mathbb E C_J\le128^J\left(2+\frac{E_0}{D\sigma^2}+2B\right).
\]
Geometric active mass proves almost-sure discovery. Combining it with the clock bound gives the explicit horizon and simplified public budget; the [budget proofs](../Proofs/NoisyBatchQuadraticPerceptronBudget.lean) retain rounding and the final certification scan.

Standard reductions do not provide this dynamics theorem. Although the represented classifier is linear, the induced update of $x=vc$ contains both $v^2g$ and $\langle g,c\rangle c$, a quadratic cross term, and multiplicative effects of the additive factor noise. It is not the classical perceptron update. Clipping, projection, regularization, fixing the output factor, or restarting would change the algorithm under study. Full-support Gaussian noise alone does not guarantee return from infinity, so local accessibility is insufficient; the stopped potential and uniform escape analysis supply the missing global control.

Unrestricted classification is much easier in this oracle model. Querying each example at $(c,v)=(0,1)$ reveals its entire signed vector, so $n$ queries suffice to recover the dataset and solve for a separator offline. Accordingly, neither `allowedAlgorithm` nor this budget establishes a new problem-class oracle complexity. As computational baselines, [Yu, Kilinc-Karzan and Carbonell, ICML 2014, Theorem 3(a)](https://proceedings.mlr.press/v32/yuc14.html) give accelerated separation by Mirror-Prox, and [Wang et al., arXiv:2210.09371, ICLR 2023](https://arxiv.org/abs/2210.09371) give accelerated perceptron analysis. Their linear-classifier iteration guarantees are far stronger efficiency benchmarks. The present claim must be assessed on the independent significance of global convergence for the prescribed coupled noisy dynamics.

Global convergence through noise injection is also not new by itself. [Wang, Giannakis and Chen, IEEE TSP 2019, Algorithm 1 and Theorem 1](https://gangwg.github.io/papers/tsp2019relus.pdf) train a ReLU first layer with a fixed, mixed-sign output layer, injecting noise into selected activation indicators and bounding nonzero updates. Those assumptions and updates do not imply the present both-factor additive-state-noise result. General nonsmooth SGD results such as [Bianchi, Hachem and Schechtman, arXiv:2005.08513v3](https://arxiv.org/abs/2005.08513) require stability/coercivity or projection conditions and address critical-point behavior; those conditions are not supplied merely by separability here.

The literature assessment initially covered the two most recent publicly available ICML, ICLR and NeurIPS editions and roughly two years of arXiv work, then followed older classification and stochastic-stability references. The closest sources were checked again on 24 October 2026 UTC, including the latest visible arXiv versions and followups. The official Tyurin proceedings PDF was inaccessible through the available web tool, and an authenticated repository retrieval failed; the arXiv v2 full text and official acceptance metadata were accessible. This limitation is not evidence of novelty. Broader convolutional models, higher width, nonseparable data, logistic-GD trajectories before the QPA limit, sharper tails, finite expected discovery time, and acceleration remain outside this theorem.
