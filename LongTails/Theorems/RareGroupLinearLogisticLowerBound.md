# How one image can delay every constant step of logistic gradient descent

On one set of **2,041 equally weighted CIFAR-10 images**, plain logistic GD needs at least **254 updates at every positive constant step size**. Joint GD on a circular two-tap filter and its readout classifies the same images in **41 updates at step 1**, starting from identical predictions. The factor is at least **6.19×** even against the best positive plain step. The Lean theorem proves the general plain-GD lower bound. The joint count for these images comes from an independent interval calculation of the actual updates. The original, unfiltered 5,000-image comparison and the attempts to explain it are documented separately. [Setup](../Setups/RareGroupLinearLogistic.lean) · [Proof](../Proofs/RareGroupLinearLogistic.lean) · [Theorem](RareGroupLinearLogisticLowerBound.lean) · [Experiments and approaches](ConstantStepLogisticImageContrast.md)

## What the theorem says

Write each signed row as $x_i=y_i u_i$. The common and rare groups have total mass $1-p$ and $p$ with $0<p<1$, distributed uniformly within each nonempty group. Suppose the rows are strictly linearly separable. Plain GD starts at a specified readout $w_0$, takes the full negative gradient $g(w)$ of the weighted mean logistic loss, and uses the same positive step $h$ throughout. One oracle call at $w$ returns the gradient vote and a Boolean testing strict fit on all rows. The algorithm stays at the first fit, or returns its current readout when the budget runs out. The tables count updates. To observe the fit flag at the first successful iterate takes one further full-data query.

Choose a vector $v$ such that every strict separator has positive inner product with $v$, the opening readout has $\langle v,w_0\rangle\le0$, and every common row has $\langle v,x_i\rangle\le0$. A signed row itself, or a positive combination of signed rows, is a directly checkable choice for the first condition. Let $C>0$ be the rare-group mean of $\max(\langle v,x_j\rangle,0)$, and $g_0=g(w_0)$. In Lean the scalar `g` is the signed projection $\langle v,g_0\rangle$. The setup requires exact equalities for both `g` and `C`; neither is revealed to GD. All quantities use the sample and the initialization. Every allowed algorithm fails at every full-gradient budget up to and including

$$
 B=\max\!\left(0,\left\lfloor 1-\frac{\langle v,g_0\rangle}{pC}\right\rfloor\right).
$$

**Proof.** The first update changes the projection by exactly $h\langle v,g_0\rangle$. Each row's negative-gradient vote is $x_i/(1+\exp(\langle w,x_i\rangle))$. Every common vote has nonpositive projection; together, the rare votes can contribute at most $hpC$ per update. Hence after $t\ge1$ updates the projection is at most $h[\langle v,g_0\rangle+(t-1)pC]$ so long as no fit has occurred. A nonpositive projection rules out a strict fit, which proves the bound inductively. Update zero is covered by the opening condition. The first possible successful output is at least $B+1$ updates away. The Lean proof identifies the vote with the actual loss derivative and follows the oracle execution for every seed and every componentwise smaller budget.

If the common opening vote projects to at most $-a<0$ with fixed rows and initialization, this gives $\Omega(1/p)$ as $p\downarrow0$ uniformly over step sizes. For a small explicit example take common row $(-2,1)$, rare row $(1,0)$, $v=(1,0)$ and $w_0=0$. The readout $(1,3)$ separates both; the first strict fit satisfies $T\ge1+\lfloor1/p-1/2\rfloor$. The theorem permits any finite dimension and any number of rows in either group. A negative common opening vote is sufficient for this scaling; the finite bound itself requires only the stated projection conditions.

## Worked image comparison

We chose the probe $v=x_{4813}$ and tested each image's alignment with it **before training**. For each of two fixed filters, the sum and the difference of adjacent pixels, we solved a unit-margin hard-margin problem on a fixed generator set. For threshold $q$, retain rows whose two separator scores exceed $q$ and whose dot product with the probe is negative, then add the probe. The original generator set is included automatically at the five thresholds. The designated rare group for the theorem consists **only of the probe**. Thus $p=1/n$, and the denominator in the budget reduces to $\|x_{4813}\|^2/n$. Every retained image has the same weight. The row indices were chosen in a geometry search on the reproduction draw, so these are selected examples of the mechanism.

| Endpoint threshold $q$ | Images | Earliest possible plain fit, any $h>0$ | Actual joint first fit | Joint $h$ | Fastest measured plain fit, six-step grid |
|---:|---:|---:|---:|---:|---:|
| 0.0001 | 2,041 | 254 | 41 | 1 | 299 |
| 0.01 | 1,992 | 248 | 38 | 1 | 291 |
| 0.05 | 1,840 | 229 | 29 | 1 | 277 |
| 0.2 | 1,235 | 152 | 17 | 1 | 169 |
| 0.5 | 361 | 43 | 6 | 1/2 | 46 |

Both models start with the joint model's predictions. On the 2,041-image set the exact-budget expression before rounding lies between 253.70 and 253.71. For the joint count, an interval calculation bounds every margin away from a false first fit: each earlier iterate has a row with margin below $-0.01420$, and every margin at update 41 exceeds $0.06628$. The calculation used integer signed pixels and fixed-point iterates with denominator $2^{1536}$. It enclosed sigmoid values with 1,664-bit Arb ball arithmetic and propagated an upper bound on the Euclidean error of each simultaneous update. This gives a finite comparison on the specified data and initialization. A general upper bound for training both layers that would predict 41 from static geometry alone remains open.

The enclosure can be reconstructed from a per-update error bound. Write $z$ for the two taps and readout together and $R=80>\sqrt{2d}$ for $d=3072$. Every signed bilinear margin $m_i$ has Hessian norm at most $R$ and $\|\nabla m_i(z)\|\le R\|z\|$. At a fixed-point center $z$ with parameter error radius $e$, the full update is Lipschitz on that ball with constant at most
$$
 1+h\left(R+\tfrac14 R^2(\|z\|+e)^2\right).
$$
This follows from the sigmoid derivative bound $1/4$ and the chain rule. If the computed posterior weights have absolute error below $2/D$ and the update is rounded componentwise to a multiple of $1/D$, the local error is at most $(2hR\|z\|+\sqrt{d+2})/D$. Multiply the old radius by the Lipschitz bound and add this local error, rounding upper bounds outward. Starting with $e=0$ and $D=2^{1536}$ gives the bounds reported above. To test a margin, enlarge its value at the fixed-point center by $\pm R e(\|z\|+e)$. The strict inequalities certify a first fit without assuming that any future iterate succeeds.

The role of weights can also be tested while fixing the images. On a different set with four common and 274 rare images, at $p=1/4096$ a separate interval calculation gives a fastest possible plain fit of 2,948 across all positive constant steps, attained at 0.258. Joint GD at 1/8 fits at 346. With equal per-image weights, plain GD at 10 fits in two updates and joint GD at 1/8 takes eight. The 2,948 value uses a sharper step-by-step calculation than the public budget; that value is not a consequence of substituting $p$ in the theorem.

## What changes relative to previous results

Tyurin's §5 separation on a minimal construction scales in the feature dimension. PR #253 studies actual finite-radius two-tap logistic GD on its two examples. Here the formal result is an all-constant-step lower bound on *plain* GD computable from the opening vote and signed rows of a general separable sample. The image comparison shows why it can be informative in 3,072 dimensions with thousands of rows. It is method-specific: another optimizer or a precomputed separating readout need not incur these updates. We claim neither an optimal lower bound for logistic regression nor an improved upper bound for learning the filter on arbitrary data. [Tyurin, §5](https://proceedings.mlr.press/v306/tyurin26a.html) · [PR #253](https://github.com/k3nfalt/longtails/pull/253)

The native 5,000-image split has additional rows that can help the probe. Discarding them changes the denominator and would invalidate the 254 bound there. At the successful native joint step of 1/8 the 2,041-image control actually takes 485 updates, slower than its best tested plain step. The 41-update result uses a different, fixed step and explains a specific finite-data separation. Predicting the size of the 13.48× native advantage still requires a general bound on how the learned filter moves. [Native reproduction and comparison to PRs #279 and #280](ConstantStepLogisticImageContrast.md)

## Reproduce the 2,041-image calculation

Use the pinned CIFAR-10 training parquet (the order matters). Run the following Python program with its local path as the sole argument. It reconstructs the signed images and CPU initialization, uses the active rows of the two hard-margin systems to select the same subset, and evaluates the two models in binary64. Expected output is `253 41 299`: the last forbidden plain update from the theorem, the joint first fit at step 1, and the plain first fit at step 10. This short replay illustrates the result; the interval bounds above account separately for real-arithmetic error. [Training data](https://huggingface.co/datasets/uoft-cs/cifar10/tree/0b2714987fa478483af9968de7c934580d0bb9a2/plain_text)

```python
import hashlib
import io
import sys

import numpy as np
import pyarrow.parquet as pq
import torch
from PIL import Image
from scipy.special import expit

source = pq.ParquetFile(sys.argv[1]).read(columns=["label", "img"])
labels = np.asarray(source["label"])
rng = np.random.default_rng(20261125)
ids = np.concatenate(
    [rng.choice(np.flatnonzero(labels == y), 2500, replace=False) for y in (0, 1)]
)
assert hashlib.sha256(ids.astype("<i8").tobytes()).hexdigest() == (
    "6016298cc0cc1916374372cf30da4964341cc524ff87dfc872a01b1ac94d6c7a"
)
pixels = [
    np.asarray(Image.open(io.BytesIO(source["img"][int(i)].as_py()["bytes"])))
    for i in ids
]
X = (
    2 * np.stack(pixels).astype(float).transpose(0, 3, 1, 2).reshape(5000, -1) - 255
) / 255
X[:2500] *= -1
torch.manual_seed(20261125)
d = X.shape[1]


def initial(k):
    return torch.rand(k).mul_(2 / np.sqrt(k)).sub_(1 / np.sqrt(k)).double().numpy()


v = initial(d)
c = initial(2)
w = c[0] * v + c[1] * np.roll(v, -1)

minus = [
    3638,
    1960,
    1021,
    1568,
    1308,
    1314,
    1412,
    1082,
    1813,
    475,
    2554,
    680,
    4799,
    1636,
    806,
    2074,
    3064,
    4205,
    2697,
    1329,
    2267,
    1551,
    736,
    4295,
    1288,
    779,
]
plus = [3638, 1412, 1082, 1288]


def endpoint(sign, support):
    Y = X + sign * np.roll(X, 1, axis=1)
    B = Y[support]
    return Y @ (B.T @ np.linalg.solve(B @ B.T, np.ones(len(B))))


score = np.minimum(endpoint(-1, minus), endpoint(1, plus))
probe = X[4813]
price = X @ probe
keep = ((price < 0) & (score > 0.0001)) | (np.arange(len(X)) == 4813)
Z = X[keep]
r = price[keep]
assert len(Z) == 2041 and w @ probe < 0 and np.count_nonzero(r > 0) == 1
B = np.floor(1 - expit(-Z @ w) @ r / np.maximum(r, 0).sum())


def first(joint, step, limit):
    u = v.copy() if joint else w.copy()
    a, b = c if joint else (1.0, 0.0)
    for t in range(limit + 1):
        shifted = np.roll(u, -1)
        margins = Z @ (a * u + b * shifted)
        if margins.min() > 0:
            return t
        g = Z.T @ expit(-margins) / len(Z)
        dg = np.roll(g, 1)
        du = a * g + b * dg
        if joint:
            a, b = a + step * (u @ g), b + step * (u @ dg)
        u += step * du


print(int(B), first(True, 1.0, 50), first(False, 10.0, 320))
```
