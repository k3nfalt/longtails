# Three passes of logistic gradient descent on two ranking chains

Learning two adjacent convolution coefficients can change how quickly full-batch gradient descent finds its first strict separator, even though the model represents the same linear scores as an ordinary readout. On a family with two paths of $n$ comparisons each, joint GD separates every comparison in three passes. Every single fixed two-tap convolution, including an independently chosen filter and adaptive readout step sizes, can require order $n$ passes on the same observations. The gap grows with the number of distinct observations. [Upper theorem](SpatialRankingLogisticAcceleration.lean) · [Lower theorem and scope](SpatialRankingFrozenFilterLowerBound.md)

## The optimization problem

Write $S$ for cyclic shift by one pixel and $T_c=aI+bS$ for a two-tap convolution. On signed rows $x_i=y_i b_i$, the margin is $m_i=\langle T_c x_i,v\rangle$. Both $(c,v)$ and the raw readout represent ordinary linear classifiers because $T_c^*v$ is an effective linear predictor and $c=(1,0)$ realizes every such predictor. The objective is the mean of $\log(1+e^{-m_i})$. An indexed query returns the negative component gradient at the supplied parameters. Full-batch GD sums the replies at the same point before changing parameters. Each example costs one call per pass. [Setup](../Setups/SpatialRankingLogistic.lean) · [Algorithm and output](../Algorithms/SpatialRankingLogistic.lean) · [Execution proof](../Proofs/SpatialRankingExecution.lean)

The observations are adjacent preferences along two ordered collections of localized signals. In group $g$, observation $j$ is $x_{gj}=f_g(u_{gj}-u_{g,j+1})$, for $0\le j<n$. Pairwise logistic likelihood and path comparisons are standard models for learning an ordering from comparisons. Published Bradley–Terry analyses study statistical estimation or convergence to a finite likelihood maximizer. Here each comparison has a consistent direction and success means ranking *all* adjacent pairs correctly. [Shah et al., JMLR 2016, §§2–3](https://www.jmlr.org/beta/papers/v17/15-189.html) · [Vojnović, Yun and Zhou, AISTATS 2020, §3](https://proceedings.mlr.press/v108/vojnovic20a/vojnovic20a.pdf)

The spatial arrangement below is a constructed test family. All items are orthonormal. The groups have disjoint spatial support in the explicit construction and zero cross-group shifted inner products in the setup. Within a group write $D_{ij}=\langle u_i,Su_j\rangle$. Its diagonal is $d_0$ at the two endpoints and $d_I$ elsewhere. For $1\le j<n$, $D_{j0}=\tau_j$ and $D_{nj}=-\tau_j$. All other off-diagonal entries vanish.

| Group | $f_g$ | $d_0$ | $d_I$ | Values of $\sqrt n\,\tau_j$, linearly spaced |
|---|---:|---:|---:|---|
| First | 1 | −1/2 | 3/4 | 1/8 down to 1/16 |
| Second | 1/2 | 1/2 | 1/4 | 1/16 up to 1/8 |

These constants, opposite contact slopes and exact sparsity are design choices. They isolate two populations that require incompatible fixed spatial responses. Each interior item is a run of positive pixels followed by equally many negative pixels. Each endpoint touches a different end of every run after one shift. Guard pixels and private endpoint coordinates realize the table in an ordinary one-dimensional signal. Every embedding with these two Gram matrices is covered. At fixed finite $n,d$, the original GD update is continuous in the rows and all third-iterate margins are strictly positive, so the three-pass success persists in some open neighborhood of each instance. The proved lower bound uses the exact contact and sparsity identities. The construction works for every $n\ge8$ and $d\ge32(n+1)$; the upper implication applies in any dimension admitting such data. [Pixel construction](../Proofs/SpatialRankingPixels.lean) · [Proof of realization](../Proofs/SpatialRankingRealization.lean)

## Why three gradients suffice

Set the initial taps to $(1,0)$, the readout to zero, and the constant mean-loss step to $4n$. Thus each parameter update uses twice the *sum* of the negative component gradients. The optimizer needs only the public dimensions and the oracle. It returns its third iterate unconditionally, including when later iterates might misclassify a row. The budget is exactly $6n$, with no additional validation pass.

All posterior weights start at $1/2$. Summing the consecutive differences telescopes, so the first readout update contains only the four endpoints. On the next pass the two end comparisons in each group have weight $\sigma(-f_g^2)$ and all interior comparisons still have weight $1/2$. The second readout therefore adds only the items next to each endpoint. Its tap change depends on both populations. This is where unequal signal strengths and endpoint autocorrelations enter. [First two updates](../Proofs/SpatialRankingGradients.lean)

At the third gradient evaluation, all but the two outer comparisons on either side of each path have a common weight. Summation by parts reduces the full gradient in that path to six vertex coefficients. Write the second and third tap pairs as $(a_2,b_2)$ and $(a_3,b_3)$, the endpoint masses of the third evaluation as $L_g,R_g$, and the second readout's first endpoint coefficient as $A_g$. In the interior the new item score has slope in $\tau_j$ equal to

$$
C_g=2a_3b_2 L_g+b_3(A_g+2a_2R_g).
$$

The first term transports the third update through the earlier filter. The second term scores the accumulated readout with the new filter. The finite sigmoid weights of the two populations make $C_g$ have opposite signs. Both populations consequently acquire positive interior margins despite their opposite contact slopes. The proof checks the boundary comparisons separately and certifies a margin greater than $10^{-3}/(\sqrt n(n-2))$ on every comparison. The scalar checks use rational enclosures valid for all $n\ge8$, with a proved error bound for the sigmoid. [Third posterior](../Proofs/SpatialRankingMargins.lean) · [Margin and third update](../Proofs/SpatialRankingThirdStep.lean) · [Uniform inequalities](../Proofs/LogisticPathBounds.lean)

For comparison, any fixed filter gives the same sign of the interior response coefficient in both groups until information from the ends reaches the middle. One path must retain a nonpositive margin. The lower proof allows arbitrary initial frozen taps and every positive, potentially adaptive, scalar readout step. This is an adaptivity separation within the training methods at issue in Figure 1. The lower bound does not cover training separate fixed-filter heads and combining their predictors; such combinations already succeed in numerical tests on these paths. [Lower-bound argument](SpatialRankingFrozenFilterLowerBound.md)

## What Figure 1 measures

Tyurin compares two parameterizations of the same classifier on a balanced sample of 5,000 CIFAR-10 airplanes and automobiles. The fastest displayed raw step reaches 100% training accuracy after approximately 330,000 iterations, and the fastest learned two-tap run takes approximately 20,000. Accuracy oscillates. The question is the *first* iteration at which all signed margins are positive. Training loss, asymptotic max-margin direction and test accuracy measure different outcomes. Section 1 motivates a perceptron interpretation of large steps. Theorems 2.1 and 5.1–5.2 develop a limiting dynamics and a two-example separation; their statements do not specify the hitting times of the finite image runs. [Tyurin, ICML 2026, Figure 1 and §§1–2, 5](https://proceedings.mlr.press/v306/tyurin26a.html) · [Full paper and Appendix G](https://arxiv.org/html/2512.11587v2)

### Reproduction

We sampled 2,500 examples from each class without replacement using NumPy `default_rng(20261125)` in CIFAR training order. We flattened RGB channel-first, mapped intensities by $2p/255-1$, and signed the first class negative. We generated the shared readout and initial taps from the default PyTorch CPU uniform generator seeded 20261125, using half-widths $1/\sqrt d$ and $1/\sqrt2$. The paper leaves the sampling seed unspecified. We tested every published step size in float32 on an H100 with TF32 disabled, checking strict margins at every iterate up to 400,000. Input scaling matters. On the same sample in $[0,1]$ raw GD missed the horizon at every step and the learned model first succeeded at 97,644. Channel standardization gave 274,644 versus 14,708.

| Raw step | First separator | Learned-filter step | First separator |
|---:|---:|---:|---:|
| 0.001 | >400,000 | 1/64 | 181,723 |
| 0.01 | >400,000 | 1/32 | 92,786 |
| 0.1 | >400,000 | 1/16 | 46,672 |
| 1 | 328,519 | 1/8 | **23,676** |
| 10 | **319,077** | 1/4 | Nonfinite |
| 100 | 323,672 | 1/2 | Nonfinite |
| | | 1 | Nonfinite |

| Iteration | 0 | 128 | 4,096 | 10,000 | 20,000 | 23,676 | 100,000 | 319,077 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Correct, raw step 10 | 2,898 | 3,895 | 3,695 | 4,161 | 4,191 | 4,419 | 4,658 | 5,000 |
| Correct, joint step 1/8 | 2,829 | 4,108 | 4,665 | 4,929 | 4,998 | 5,000 | 5,000 | 5,000 |

On CIFAR cats versus horses (classes 3 and 7), raw GD missed 400,000 while the learned model separated at 90,647. On the full MNIST 7-versus-8 training set, raw GD won, 6,757 versus 38,398. Repeating with identity taps and zero readout as in the theorem gave respectively 311,522 versus 23,067; >400,000 versus 91,231; and 6,426 versus 29,359. The exact path Gram assumptions describe the theorem's construction; these image datasets have their own measured spatial geometry.

<details>
<summary>Reproduce the 13 CIFAR curves</summary>

The following code uses the original 50,000-row training parquet, NumPy sampling without replacement, PyTorch 2.12.1 and CUDA. The sample-index vector as little-endian 64-bit integers has SHA-256 `6016298cc0cc1916374372cf30da4964341cc524ff87dfc872a01b1ac94d6c7a`. The measured run captured 32 repetitions of this same update in a CUDA graph. Floating-point kernels and evaluation order can change first-hit times near an oscillatory boundary. [CIFAR training data, pinned revision](https://huggingface.co/datasets/uoft-cs/cifar10/tree/0b2714987fa478483af9968de7c934580d0bb9a2/plain_text)

```python
import io, math
import numpy as np
import pyarrow.parquet as pq
import torch
from PIL import Image

seed = 20261125
torch.manual_seed(seed)
torch.set_float32_matmul_precision("highest")
table = pq.read_table("train-00000-of-00001.parquet")
labels = np.array(table.column("label").to_pylist())
rng = np.random.default_rng(seed)
ix = np.concatenate(
    [rng.choice(np.flatnonzero(labels == c), 2500, replace=False) for c in (0, 1)]
)
rows = [table.column("img")[int(i)].as_py() for i in ix]
raw = np.stack(
    [
        np.asarray(Image.open(io.BytesIO(row["bytes"]))).transpose(2, 0, 1).reshape(-1)
        for row in rows
    ]
)
X = torch.from_numpy(raw).to(device="cuda", dtype=torch.float32).div_(255)
X.mul_(2).sub_(1)
X[:2500].neg_()
n, d = X.shape
lin_steps = [10.0**i for i in range(-3, 3)]
cv_steps = [2.0**i for i in range(-6, 1)]
k = len(lin_steps)
eta = torch.tensor(lin_steps + cv_steps, device="cuda")
h = eta.numel()
v0 = torch.rand((d, 1)).mul_(2 / math.sqrt(d)).sub_(1 / math.sqrt(d))
c0 = torch.rand((2, 1)).mul_(2 / math.sqrt(2)).sub_(1 / math.sqrt(2))
v = v0.repeat(1, h).cuda()
c = c0.repeat(1, h).cuda()
c[0, :k] = 1
c[1, :k] = 0
learn = torch.arange(h, device="cuda") >= k
eta_v = eta / n


def direction():
    u = c[0] * v + c[1] * v.roll(-1, 0)
    margins = X @ u
    g = X.T @ torch.sigmoid(-margins)
    sg = g.roll(1, 0)
    dv = c[0] * g + c[1] * sg
    dc = torch.stack([(g * v).sum(0), (sg * v).sum(0)]) * learn
    return margins, dv, dc


for t in range(400001):
    margins, dv, dc = direction()
    # Record the count and the first all-positive iterate for each column.
    correct = (margins > 0).sum(0)
    if t == 0:
        first = torch.full_like(correct, -1)
    first = torch.where((first < 0) & (correct == n), t, first)
    if t < 400000:
        v.add_(dv * eta_v)
        c.add_(dc * eta_v)
print(first.cpu().tolist())
```

</details>

### Which data properties explain the image result?

Let $G=X^\top X/N$ for the signed image matrix $X$, and let $s=2ab/(a^2+b^2)$. Readout training acts on the effective linear predictor through
$$
T_c^*T_c=(a^2+b^2)\left[I+\tfrac{s}{2}(S+S^*)\right].
$$
The strength and the preferred spatial frequencies can both change. Positive $s$ reinforces the spatial sum, and negative $s$ reinforces the spatial difference. Updating the taps adds two more first-order terms and a simultaneous-update term of order $\eta^2$. These terms and their two-step response to oscillating gradients admit exact finite-iteration identities. [Finite-step identities and data-dependent motion bound](../Proofs/TwoTapLogisticMetric.lean)

* **Pixel order.** On native CIFAR the largest eigenvalue of the covariance of $(x-Sx)/\sqrt2$ is 3.12, against 271.06 for raw inputs. Randomly reindexing the pixels preserves every raw margin and every raw GD step under matched initialization. It raises difference-feature sharpness to 128–131 in three permutations and delays the learned classifier from about 23,700 iterations to 375,744, 386,526 and 379,040. The transposed and RGB-interleaved orders give 68,836 and 94,520. Spatial adjacency predicts an effect that the raw Gram matrix alone cannot distinguish. Attenuating the top 32 spatial covariance directions by a factor of eight lowered the top eigenvalue to 4.235 and changed the raw Euclidean margin from about 0.01239 to 0.01233. In that control raw GD improved from 317,538 to 4,570 iterations and the learned model from 22,990 to 3,849. The large raw delay is sensitive to fast covariance modes even when Euclidean separability changes very little. Normalized margin or sharpness alone fails to account for the MNIST reversal.
* **How the filter moves.** A low-dimensional model built before training from the leading covariance eigenvector and eight supervised ridge directions predicts the sign of the learned shape on CIFAR and MNIST. The ridge directions are $(G+\lambda I)^{-1}\bar x$ for $\lambda=10^{-4},\ldots,10^3$. With $U$ an orthonormal basis for their span and the leading eigenvector, project the input rows onto $U$ and use the compressed shift $U^*SU$ in the parameter updates. On CIFAR the early smooth turn is followed by a turn towards differences; on MNIST the filter remains predominantly smooth over the relevant horizon. From CIFAR iteration 4,096 through the exact first hit, the nine-direction forecast had maximum angular error below $1.60^\circ$ against the independently validated trajectory. Prescribing its angles to the full readout and training the scalar magnitude predicted 23,377 CIFAR iterations and 38,160 MNIST iterations. Fixing the magnitude at initialization missed the horizon of 131,072 on both.
* **Intervention.** After iteration 128 we projected each new filter direction to the closest direction satisfying $ab\ge0$, preserving that update's filter norm. On CIFAR every published joint step then missed 400,000. The opposite constraint $ab\le0$ gave 23,382 versus 23,702 for unconstrained GD in the matched run. Freezing the angle at 512 also missed 400,000, while freezing it at 4,096 gave 34,538. On MNIST the smooth constraint preserved 38,398. Forcing differences gave 26,411, still slower than raw GD. A tuned fixed difference filter can outperform joint GD on native CIFAR. The all-frozen-filter lower bound applies to the constructed ranking paths.
* **Why plain GD takes longer.** For a convex mixture $y$ of signed rows, a strict separator must give $y$ positive margin. Each raw update can increase it by at most $\eta N^{-1}\sum_i[\langle x_i,y\rangle]_+$, regardless of the sigmoid weights. On the disclosed sample one witness has raw margin $-1.47838$ after 16,384 steps at $\eta=1$, and per-step gain at most 0.000154376. It precludes separation through 25,960. Joint GD has already raised the same mixture to $+2.2538$ by step 16,384. Holding the metric magnitude fixed, setting $s=-0.99$ increases the directional gain ceiling by a factor of 6.73. This ceiling bounds how quickly a particular obstructing direction can be repaired; it does not give the hitting time by itself.
* **Predicting the counts.** A raw-GD approximation separates the top 32 covariance eigenvectors from their orthogonal complement. In each block it makes eight ordinary logistic updates in the top subspace with the complement frozen, then applies the sum of the eight complementary gradients once. This uses the data and initialization only. Native CIFAR first-hit forecasts at raw steps $1,10,100$ were 328,512, 318,112 and 325,320, all within 0.51% of the measured counts. The three smaller steps missed the horizon. Combining the best raw forecast with the independent angle-based joint forecast gives $318112/23377=13.61$, versus the observed $319077/23676=13.48$. Unchanged on CIFAR 3/7, the raw approximation missed 400,000 at all six steps. On MNIST it predicted a best raw count of 6,672 versus 6,757, but interchanged the two largest step sizes, with up to 23.4% error at a given step. For the two stable CIFAR steps 0.001 and 0.01, summing per-step defects around the compensated block approximation and using nonexpansiveness independently certifies nonseparation throughout iterations 0–399,999. The large-step clock is an empirical dynamics model. A uniform theorem predicting these counts from an eigengap is open.

### Why opposite directions are compatible with the two datasets

The projected data give a way to test the direction before running the full network. Write $Z=XU$, $K_s=I+s\,U^*(S+S^*)U/2$, $r=\|c\|$, and let $\beta$ be the effective predictor in the projected coordinates. At posterior $q_i=\sigma(-(Z\beta)_i)$, set $W=Z^*\operatorname{diag}(q_i(1-q_i))Z/N$. The readout Hessian has largest eigenvalue $r^2\lambda_{\max}(W^{1/2}K_sW^{1/2})$. Among readouts realizing $\beta$ at these taps the minimum squared norm is $\beta^*K_s^{-1}\beta/r^2$ when $K_s$ is invertible. Consequently, whenever the active readout satisfies $\|v\|^2-r^2\le\rho$, one must have

$$
r^2\ \ge\ \frac{\sqrt{\rho^2+4\beta^*K_s^{-1}\beta}-\rho}{2}.
$$

This limits the ability to reduce readout curvature by making the taps small while compensating with an arbitrarily large readout. To bound the right-hand side over a sublevel set $F(\beta)\le f$, any logistic dual weights $p_i\in[0,1]$ give $F(\beta)\ge\overline{H(p)}-\langle Z^*p/N,\beta\rangle$, where $H$ is binary entropy. Cauchy–Schwarz in the $K_s$ metric then gives a lower bound on $\sqrt{\beta^*K_s^{-1}\beta}$. The curvature calculation also uses the Bernoulli relative-entropy identity at a finite projected optimum to bound how far feasible posteriors can move from its posteriors.

On the nine-direction CIFAR data, a numerical evaluation of these inequalities over $s\in[-0.8,1]$, $F\le0.20$ and $\rho\le6.5$ gives $\eta\lambda_{\max}(\nabla^2_{vv}F)\ge2.81$ at $\eta=1/8$. A balanced fit in this loss range with nonexpansive readout linearization therefore requires a difference-favoring filter, $s<-0.8$. On MNIST a balanced pure-sum choice $s=1$ attains $F=0.02946$ and full parameter sharpness $\eta\lambda_{\max}=1.321$ at $\eta=1/16$. These are finite-loss tests on projected data. Stability at every full-GD update would be an additional assumption, and the projected optimum on MNIST can enter a different regime at still lower loss. The finite-orbit and sign-constraint experiments check which direction actual GD selects.

### Exact-arithmetic checks and limitations

For rational centered CIFAR pixels and the recorded float initialization treated as exact, a 1,024-bit reference calculation with a posteriori bounds on accumulated error certifies the joint first hit at **23,431**, step $1/8$. The minimum margin there exceeds $6.49\times10^{-5}$; at every earlier iterate some margin was below $-1.30\times10^{-4}$. The per-margin error enclosure was at most $1.01\times10^{-10}$. Each block bounds the linearized error using a restarted product of Jacobians and bounds the nonlinear remainder on the resulting parameter neighborhood. The floating-point and exact hitting times refer to different arithmetics.

For the same exact initialization and pixels, every one of the six raw step sizes is slower than the certified joint run. The table gives inclusive horizons through which a strictly correct raw iterate is excluded.

| Raw step | 0.001 | 0.01 | 0.1 | 1 | 10 | 100 |
|---|---:|---:|---:|---:|---:|---:|
| Last iteration ruled out | 399,999 | 399,999 | 25,000 | 25,960 | 25,843 | 24,690 |

For the three largest steps, a validated prefix and a single convex combination of the images suffice. The same nonnegative integer mixture weights work at all three rates. For instance, at step size 100 the mixture margin at iteration 15,360 is $-144.046814$ with certified error below $2.7\times 10^{-9}$ around the unrounded value. The maximal future increase per pass is $0.015437585$, even allowing arbitrary subsequent posteriors in $[0,1]$. The next 9,330 passes still cannot separate. The finite grid therefore gives a certified real-arithmetic factor of at least $24691/23431>1.053$ in favor of joint training. The measured float32 factor is 13.48. Counting the reference calculations or forecasting models as GD oracle calls would answer a different cost question.

There is also a short-horizon check of the predicted change of direction that takes no realized training trajectory as an input. A fixed 26-dimensional data and initialization subspace together with bounds on discarded gradients gives the second tap $b_8\in[0.00489,0.01948]$, from $b_0=-0.13351$. A predictor enriched to 81 directions using gradients of its own reduced trajectories gives positive $b_{256}$ and negative $b_{384},b_{512}$ for the full finite-GD model after certified residual correction. The scored intervals are centered at $0.07566577,-0.00199183,-0.09584748$, respectively, with error below $1.3\times10^{-11}$ around the *unrounded* centers. Validation uses full-dimensional gradient and Jacobian products. It is an explanation and check of a prediction, not a less expensive way to train. The exact-arithmetic certificates are external numerical analyses; the Lean theorems quantify over ranking instances. A fresh stopping algorithm that queries data to verify candidate margins must charge those validation queries.

The hard quadratic-perceptron update suggested by the limiting dynamics missed separation through 400,000 iterations at every published joint step on this sample. Finite sigmoid weights continue to grow the filter magnitude even on correctly classified rows. In particular $m\sigma(-m)=\min(m,0)+|m|\sigma(-|m|)$; the second contribution disappears in a hard-sign update. The spatial metric, its changing magnitude, the interventions and the separate raw dynamics account quantitatively for the reproduced speed gap. Exact real-arithmetic speed ratios across arbitrary steps, new image samples or arbitrary reorderings remain undetermined.

## Closest formal and published comparisons

PR 253 proves a finite-step two-example result from a sufficiently small random sphere, with an $O((\sqrt d/\mu)\log(1/r))$ query upper bound. We retain the logistic loss, the cyclic two-tap model and actual simultaneous GD, change the data and initialization, and compare against finite logistic GD on the very same observations. The two instance families are distinct. PR 254 proves an advantage over raw constant-step GD using a six-row construction with cross-frequency orthogonality. PR 255 obtains two-pass separation under a different calibration; raw GD can also separate the matched data in two passes. PR 256 treats a positive reference and translated negative defects and compares against a batch perceptron. The growing chain length, adversarially selected *single frozen filter*, adaptive scalar rates and finite propagation obstruction are different here. [PR 253](https://github.com/k3nfalt/longtails/pull/253) · [PR 254](https://github.com/k3nfalt/longtails/pull/254) · [PR 255](https://github.com/k3nfalt/longtails/pull/255) · [PR 256](https://github.com/k3nfalt/longtails/pull/256)

Arora, Cohen and Hazan derive effective preconditioning from depth. Gunasekar et al. study implicit bias in linear convolutional networks. Musat and Boumal analyze first perfect classification for separable linear GD at large steps. Zhang, Wu and Bartlett obtain fast risk decay with adaptive steps and averaging. These results neither give a three-pass strict separator for the simultaneous two-tap update here nor the same-instance impossibility for every frozen filter. Our comparison concerns a training mechanism. An unrestricted optimizer can obtain every signed row in $2n$ queries at $((1,0),0)$, where the readout gradient reply is $x_i/2$. It can then solve $\langle w,x_i\rangle\ge1$ by linear programming with free internal computation. The finite strict separator proved here can be rescaled to make that system feasible. The $6n$ upper budget is three times this available construction. The quadratic lower budget concerns training with a single frozen filter. [Arora et al., ICML 2018, §4](https://proceedings.mlr.press/v80/arora18a.html) · [Gunasekar et al., NeurIPS 2018](https://arxiv.org/abs/1806.00468) · [Musat and Boumal, arXiv:2610.26748, §5](https://arxiv.org/abs/2610.26748) · [Zhang et al., ICML 2025](https://proceedings.mlr.press/v267/zhang25cf.html)
