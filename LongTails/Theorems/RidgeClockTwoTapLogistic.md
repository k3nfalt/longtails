# First strict fit for gradient descent on a two-tap convolution

A two-tap circular filter and a linear readout implement a linear classifier on the original pixels. Joint training changes how quickly the classifier moves, even though every score it can represent is also available to the raw linear model. Tyurin exhibits this effect on 5,000 CIFAR-10 airplanes and cars. The winner changes across tasks in Appendix G. In particular, both MNIST class pairs favor the ordinary readout in our full-data reproductions. [Tyurin, ICML 2026, Figure 1 and Appendix G](https://proceedings.mlr.press/v306/tyurin26a.html)

## Problem and returned iterate

The rows are arbitrary labeled vectors with their labels multiplied into them. At taps $a,b$ and readout $v$, row $x_i$ has signed score $m_i=a\langle x_i,v\rangle+b\langle Sx_i,v\rangle$, where $S$ is the cyclic shift. The optimization objective is the mean logistic loss. A single full-batch pass returns its negative parameter gradient and the flag that every score is strictly positive. GD updates both taps and the readout from the same old state, with one fixed positive step. It returns the first strict fit, freezing there when the flag is true. The framework can spend its remaining budget querying the frozen point. At each failed query it receives the exact mean negative gradient. The algorithm knows the dimensions, initialization and step. The certificate used in the proof gives it no additional oracle information. [Setup](../Setups/RidgeClockTwoTapLogistic.lean) · [Algorithm](../Algorithms/FirstFitGradientDescent.lean) · [Oracle execution](../Proofs/FirstFitGradientExecution.lean)

## Work per pass

Let $R=(a^2+b^2+\lVert v\rVert^2)/2$, $q_i=1/(1+\exp(m_i))$, $W=n^{-1}\sum_i q_i m_i$, and let $g$ denote the full negative gradient. The exact GD update gives
$$
R_{t+1}-R_t=2\eta W_t+\tfrac12\eta^2\lVert g_t\rVert^2.
$$
For the raw linear model the same calculation advances $\lVert v\rVert^2/2$ by $\eta W_t+\eta^2\lVert g_t\rVert^2/2$. The important difference appears when comparing at the size of the classifier that acts on pixels. A balanced two-factor representation can reach a predictor of size proportional to $R$; the raw model reaches size proportional to the square root of its energy. These equalities alone give no first-fit time. The signed work can be negative, the filter can suppress useful image directions, and a single difficult row can delay first fit after almost every other row has a positive score. [Radial identity](../Proofs/TwoTapRadialClock.lean)

The setup measures a reference work curve at approximately stationary ridge-regularized logistic solutions computed on the image rows. A second profile in a specified normalized filter measures the first zero of the interpolated minimum score. Its optional continuation moves the quadratic penalty's center using the previous solution. The finite interpolation is part of the specification. A match to the continuously regularized solution path would require an additional error estimate.

The theorem uses image and finite polynomial certificates to transfer work and a separation threshold to the actual nonlinear GD updates. On each block of $B$ updates the guaranteed gain must cover the speed assigned to every radius interval it crosses. This matters when one block overshoots several intervals. The clipped integral of reciprocal speed then advances by at least one per block until it reaches its terminal value. Writing $I=\sum_j (R_{j+1}-R_j)/(c_jW_j)$, the budget in full passes is
$$
1+t_0+B\left\lceil\frac{I}{2\eta B}\right\rceil .
$$
The leading pass charges detection. The proof uses one ceiling for the whole sum. The geometric hypotheses and numerical work needed to check them are part of the result. They are stronger than linear separability. No bound over all separable image datasets follows from the radial identity. [Theorem](RidgeClockTwoTapLogistic.lean) · [Reciprocal-work proof](../Proofs/RadialWorkPotential.lean) · [Connection to actual GD](../Proofs/RidgeClockTwoTapConvergence.lean)

## Shared-image experiments

Our Figure 1 draw uses seed 20261125, 2,500 training images per class, channel-major order and centered intensities. Both models receive exactly the same images and initial readout. A full-batch update uses $n$ individual gradient contributions. Learning rates in any one run stay constant. On the author's model-specific grids, the earliest FP32 hits are 319,077 updates at step 10 and 23,676 at step $1/8$, giving 13.48×. Giving both models all 35 rates $2^{j/2}$, $j=-20,\ldots,14$, gives 292,117 and 18,539 updates, a 15.76× ratio. Each figure compares the winning runs. If each trial stops at its first hit or at 400,000 updates, the plotted-grid searches consume 2,171,274 raw and 1,544,864 joint flagged passes in total. The matched 35-rate searches consume 12,716,170 and 11,189,300. Measuring the complete curves runs every trial to the horizon. FP32 kernel layout affects first-hit counts near instability. For the stated real-arithmetic centered data and step $1/8$, earlier high-precision work found the joint first fit at 23,431. [Prior native first-fit analysis, PR 279](https://github.com/k3nfalt/longtails/pull/279)

| Dataset and training classes | Raw first fit | Joint first fit | Published-grid comparison |
|---|---:|---:|---|
| CIFAR-10 0/1, 5,000 | 319,077 | 23,676 | Joint 13.48× |
| CIFAR-10 3/7, 5,000 | >400,000 | 58,697 | Joint >6.81× |
| CIFAR-10 0/1, all 10,000 centered | >400,000 | >400,000 | Both curves censored |
| EuroSAT 3/7, two independent 5,000-image draws | 89,497 and 89,903 | 7,827 and 6,707 | Joint 11.43× and 13.40× |
| EuroSAT 0/1, two independent 5,000-image draws | >100,000 on both | 17,728 and 18,102 | Joint >5.64× and >5.52× |
| Fashion-MNIST 5/7, 5,000 | 360,191 | 115,640 | Joint 3.11× |
| Fashion-MNIST 7/9, 5,000 | 60,381 | 33,576 | Joint 1.80× |
| MNIST 0/1, all 12,665 | 2,737 | 3,344 | Raw 1.22× |
| MNIST 7/8, all 12,116 | 6,654 | 32,266 | Raw 4.85× |
| Gisette, all 6,000, centered | 2,418 | 1,350 | Joint 1.79× |
| Gisette, same rows scaled to [0,1] | 334 | 381 | Raw 1.14× |

A data-only forecast forms a readout space from principal components, their shifts, regularized classifiers, and difficult training rows. The filter still changes during the forecast. The forecast can also include readouts representing the same scores after a change of filter. On the new CIFAR-10 3/7 draw the first version missed every joint fit. A transported version specified before seeing full-GD results predicted a winning 79,802 updates at the correct step $1/4$. On Fashion-MNIST 5/7 it predicted 442,233 raw versus 131,236 joint, recovering the winner and the winning joint step. On an independent EuroSAT 3/7 draw the original projection predicted 8,233 joint updates but missed the raw fit before 100,000. These are forecasts with observable errors. Computing the forecast is additional offline work.

On the centered 10,000-row CIFAR-10 0/1 instance, an exact positive-null certificate on 3,225 signed rows proves that neither bias-free model can ever fit. The same data admit a strict affine separator, and the uncentered data admit a strict homogeneous separator. The paper does not state the pixel centering, so the original curves alone cannot identify which obstruction operated there.

## Comparison and limitations

PR 253 analyzes a specially constructed pair of samples. PR 262 gives a many-sample first-fit result under two separating shifted views and an initialization condition. PR 279 certifies a final portion of two specific learned-filter trajectories from a frozen Hessian, a signed spectral-work check and nonlinear error estimates. Its airplane/car budget of 24,456 starts the local calculation at update 20,914. These comparisons require their stated step, accuracy, initialization and data assumptions. [PR 253](https://github.com/k3nfalt/longtails/pull/253) · [PR 262](https://github.com/k3nfalt/longtails/pull/262) · [PR 279](https://github.com/k3nfalt/longtails/pull/279)

The independently replayed small-step CIFAR certificate gives 2,936,805 full passes at $\eta=.001$ and 3,007,289 at $1/1024$. The same image-work profile excludes a raw fit for at least 131.45 million updates over all $0<\eta\le .001$. The resulting ratio exceeds 44.7× when the joint model takes $.001$ and the raw model may use any constant step in $(0,.001]$. The verified joint continuum is $[7/8192,.001]$. The ratio 13.48× comes from the plotted grids, whose best steps are much larger. A small-step theorem establishes a different quantitative statement.

### What certifies the plotted joint step

At $\eta=1/8$ on the focal CIFAR draw, nine raw ridge anchors determine the reference work and 491 filtered ridge anchors determine the separation radius. In the causal profile the filter is proportional to $(1,-0.9)$. Each regularized problem centers its penalty along the previous readout. The first positive sampled minimum margin occurs at radius 309.6343. Sampling and interpolation are fixed before the nonlinear tail calculation. The proof must still establish that each actual image benefits from movement of the trainable filter and readout.

For an image, the exact change of score has a term linear in the full GD increment and a second term bilinear in the tap and readout increments. The certificate integrates both over blocks of 128 updates. A lower bound $d_i$ on a block's work changes that row's exponential contribution to the margin sum by a factor of at most $\exp(-10d_i)$. Rows have different starting weights, and some rows lose margin. Bounds on both sides of each weight allow the proof to sum these signed changes. The initial sum and the block changes bound the sum when the radial calculation reaches the first positive ridge knot. A sum below one forces strict positivity on every row. Checking the mean logistic loss against $\log(2)/5000$ misses this phenomenon. The observed loss at first fit is about 0.014, more than 100 times that sufficient threshold. [Signed exponential-work proof](../Proofs/ExponentialMarginWork.lean)

The clock starts after 512 updates, uses 41 intervals, and yields 216 blocks or **28,161 oracle calls**. A validated cold prefix supplies the enclosure through update 20,000. From that join an independent polynomial collocation uses the images and GD vector field to construct the tail. Its signed-work calculation starts at update 20,096. Across its 27 blocks, 720 nonlinear-gradient nodes give lower bounds for 3,456 native score increments on each image. The final block reaches radius at least 310.80174, and the upper bound on the log of the exponential sum divided by ten is below $-0.022$. This calculation uses no observed first-fit index or successful endpoint as the terminal margin bound. Summing the work lower bound from the initial radius edge 2.41 gives a gain of at least 308.11060, reaching 310.52060 on block 180. No later observed radius or endpoint reset is needed to show this crossing. Substituting the forward work sums for the pointwise lower radii across all blocks also verifies all 223 intersected block/interval inequalities. In the early-crossing branch the accumulated work alone suffices to prove arrival by block 180. The full-budget branch supplies a separate reciprocal-work argument when no early crossing is given. For a stricter check, one can also replace the radius argument of the filtered margin profile at every one of the 27 signed-work blocks with the forward sum since update 512. Rounding each block gain down to a multiple of $2^{-20}$ still keeps the surplus positive and gives a closing upper bound of $-0.01533$ on the log mass divided by ten. This check uses the initial certified radius and subsequent work, with no later radius measurements in the score comparison. The formula reports the reciprocal-work bound of 216 blocks. The precision, spectral enclosure checks and construction of the prefix and ridge anchors are offline costs. The 720 nodes are only the signed-work quadrature portion of that construction.

The identical frozen readout at $\eta=1/8$ cannot strictly fit through update 393,216. Counting detection, the ratio of its lower bound to the new joint upper bound is at least $393218/28161=13.96$. This comparison holds a common step fixed. Allowing both models to choose any constant step in the common 12-rate union of the two plotted grids gives a rigorous comparison of at least $29900/28161>1.0617$. The raw runs all fail through update 29,898, while the joint run at $1/8$ suffices. Using its certified work crossing at update 23,552 strengthens the instance-specific comparison to $29900/23553>1.269$. These are different comparisons from selecting the fastest observed run on a 35-rate grid. PR 279's earlier spectral certificate has the **smaller** upper bound for this particular focal run. The new result contributes the reference work, the image-derived gate, and a way to transfer many signed score increments to that gate across datasets. It provides no improved class-wide separable-logistic complexity.

On centered Gisette the same reciprocal-work argument uses nine raw anchors, a zero-centered profile with normalized filter proportional to $(1,-1/2)$, and a gate at $4/3$ of its interpolated zero. This setting uses a different safety factor. At $\eta=1/32$ it gives 1,716 full calls. The actual real-arithmetic first fit is update 1,351. Every raw rate on the common 12-rate union fails through update 2,400, so the oracle comparison gives a factor of $2402/1716\approx1.40$. Sixty-four initialization updates and 34 polynomial cells suffice for the joint certificate. The numerical certificates for the concrete datasets are checked computations outside the Lean kernel. Lean proves the implication from the specified inequalities to success of the executed algorithm, for any finite image dimension and positive sample count.

### Which image properties transfer

A cyclic shift preserves different features depending on pixel order. Along the Fourier directions a filter $(a,b)$ has gains $|a+b\exp(i\theta)|$. Which directions must carry weight to separate the difficult rows can be measured with regularized classifiers in the raw and shifted views before training. A change of taps can also preserve the scores while changing the required readout. Including such readouts explicitly improves the projection used to forecast GD. The resolvent identity in the supporting proof bounds the residual of interpolating these transported classifiers at fresh filter ratios. This construction depends on the ordering of features even when their raw Gram matrix stays fixed. [Filter transport](../Proofs/TwoTapFilterTransport.lean)

On nine configurations spanning the five datasets, the enriched projection recovered the winning architecture, the winning joint step and 113 of 117 success/censoring decisions. Most of these comparisons are retrospective. On the focal instance it predicts the joint winner at 25,131 versus 23,676 updates, but censors every raw run through 400,000. It therefore cannot give the actual tuned ratio there. A prospective control randomly permuted the pixel coordinates on the focal CIFAR data and applied the same permutation to the initial readout. This preserves the entire raw orbit up to that permutation. Before running full GD the projected model predicted that all seven joint rates would fail to fit by 50,000. All seven did, including the formerly winning $1/8$, which never exceeded 4,707 of 5,000 correct through 50,000 updates. On CIFAR 3/7, three same-rank alternatives using arbitrary directions, extra principal components or additional difficult rows all missed fits the transported readouts recovered.

The pretraining predictors require labeled data, layout and initialization. Computing them consumes additional resources, and the projection itself runs a lower-dimensional optimizer. The rigorously certified improvement at plotted rates covers focal CIFAR and centered Gisette. The other data test transfer empirically. Centering changes the Gisette winner and can destroy homogeneous separability on CIFAR. The formal positive-null obstruction applies to both parameterizations. [Image separation](../Proofs/TwoTapImageSeparation.lean)

### Relation to optimization theory

Tyurin's Theorems 5.1 and 5.2 compare quadratic and ordinary perceptron dynamics on a constructed two-example family and exhibit a square-root dimensional advantage. The present comparison follows simultaneous finite-step logistic GD on all rows. A norm or a separability margin alone misses both the signed cancellation and the interaction with the cyclic shift. Arora, Cohen and Hazan derived an effective preconditioned update for factorized linear networks. Ji, Dudík, Schapire and Telgarsky's Theorem 5 relates the limiting direction of raw GD to the regularization path. Wu, Bartlett, Telgarsky and Yu's Theorem 1 and Corollary 2 bound raw logistic risk through its stable and nonmonotone phases. Substitution of the sufficient risk target $\log(2)/n$ in a risk upper bound addresses the raw model and loses the first-fit scale observed here. These results supply precedents for factorization and ridge geometry. They give no finite signed-work transfer from a filtered classifier path to these bilinear cyclic updates. [Tyurin, ICML 2026](https://proceedings.mlr.press/v306/tyurin26a.html) · [Arora et al., ICML 2018](https://proceedings.mlr.press/v80/arora18a.html) · [Ji et al., COLT 2020, Theorem 5](https://proceedings.mlr.press/v125/ji20a/ji20a.pdf) · [Wu et al., COLT 2024, Theorem 1 and Corollary 2](https://proceedings.mlr.press/v247/wu24b/wu24b.pdf)

Zhang, Wu, Lin and Bartlett prove that from zero initialization, risk-adaptive GD with a sufficiently large scale returns a separating averaged iterate in order $1/\gamma^2$ steps on normalized margin-$\gamma$ data. They also give the comparable best-iterate conclusion. For $0<\gamma<1/6$ and $n>16$, their Theorem 8 constructs instances requiring at least $\min\{(\log_2 n)/8,1/(30\gamma^2)\}$ batch steps within a raw gradient-span model. That lower bound is existential over datasets, and the upper bound changes the step at each iterate. Jagadeesan, Razenshteyn and Gunasekar characterize the minimum weight norm for representing linear predictors with bounded-support convolutional kernels. This gives a static cost for a classifier. Counting the time to realize a separator from a given initialization additionally requires the finite-step work comparison here. [Zhang et al., JMLR 2026, Theorems 2 and 8](https://jmlr.org/papers/volume27/25-1941/25-1941.pdf) · [Jagadeesan et al., COLT 2022](https://proceedings.mlr.press/v178/jagadeesan22a.html)

The raw model admits a different pretraining timing diagnostic that also explains the MNIST reversal. Write its signed rational image matrix as $X=Z/D$ with integral $Z$. At very large positive step, a wrong row casts one full vote and a correct row casts zero. The first update uses the exact fractional logistic votes $q_0$ at the shared readout. Subsequent hard updates add integer columns of $ZZ^\top$ to $ZZ^\top q_0$. Thus enclosing the fractional parts of this initial vector away from integers fixes the signs in the entire hard-vote computation. If $U=\max_i\lVert x_i\rVert$ and $\tau=\min_i\operatorname{dist}((ZZ^\top q_0)_i,\mathbb Z)/(nD^2)>0$, then
$$U\big(\lVert v_0\rVert/\eta+TUe^{-\eta\tau/2}\big)<\tau/2$$
suffices to transfer the first $T$ hard signs to the finite-step raw dynamics after the initial update. Indeed the scaled readout starts within $\lVert v_0\rVert/\eta$ of the first hard update. At a correctly coupled step each sigmoid differs from its hard vote by at most $e^{-\eta\tau/2}$, adding at most $Ue^{-\eta\tau/2}$ to the scaled readout error.

This offline hard-vote calculation gives 323,174 updates for focal CIFAR, 95,053 for the second EuroSAT 3/7 draw, 384,602 and 61,644 for the Fashion pairs, 2,748 and 6,650 for the MNIST pairs, and 2,430 and 335 for the two Gisette scalings. All eight lie within 6.8% of the measured fastest raw runs. CIFAR 3/7 and EuroSAT 0/1 remain censored at their experimental horizons. The large-step condition can require steps far above the plotted rates. Using the hard raw count and projected joint timing as separate empirical proxies gives $323174/25131=12.86$ for the observed $13.48$ on focal CIFAR and $2748/3340=0.82$ on MNIST 0/1, where raw wins. These retrospective timing comparisons do not establish optimality over continuous step sizes. The proxy's own hard-vote iterations and matrix operations cost additional work.

The new data restrictions are explicit. Every certificate must bound nonlinear GD on the full perturbation balls around its polynomial pieces. The radius and work inequalities cover every occupied or crossed interval. Certified success also needs either strict margins on all possible crossing balls or the signed exponential-work inequalities. Linear separability by itself implies none of these quantitative comparisons. The certificate is a proof witness specific to the images, initialization and step, and its construction can cost more than training. The rigorous cross-dataset results give a class with concrete large instances. They do not give a uniform factor for arbitrary images or a purely spectral pretraining test sufficient for that factor. The full-budget branch applies on the small-step CIFAR continuum and on centered Gisette. The focal plotted-rate calculation uses its forward accumulated-work crossing.

## Reproducible experiments

The three source files below reproduce the curves, the matched focal sweep and the transported forecasts. Each collapsed section can be saved as its named file. Run the programs in a common directory. The original backend used an NVIDIA H100, Python with PyTorch 2.12.1+cu130, NumPy 2.4.6, PyArrow 23.0.1, Pillow 11.3.0 and Matplotlib 3.11.0. The output records the sampled index array, its hash, all strict correct-count curves and first-fit indices. For focal CIFAR the index hash in little-endian int64 is `6016298cc0cc1916374372cf30da4964341cc524ff87dfc872a01b1ac94d6c7a`. The paper gives the random sampling rule without the original indices. The readout and taps in all focal runs use the same initialization, with the raw taps held at $(1,0)$.

Use the training Parquet at the pinned CIFAR revision, the two standard gzip training IDX files in a directory for each MNIST archive, the RGB EuroSAT zip, and the original UCI Gisette zip. The code contains the class pairs, sample sizes, seeds, scaling, channel order, grid and horizon of every panel. In particular EuroSAT uses all $64\times64$ pixels, and Gisette uses its published feature order. [CIFAR-10 training file](https://huggingface.co/datasets/uoft-cs/cifar10/tree/0b2714987fa478483af9968de7c934580d0bb9a2/plain_text) · [MNIST](https://storage.googleapis.com/cvdf-datasets/mnist/) · [Fashion-MNIST](https://github.com/zalandoresearch/fashion-mnist/tree/master/data/fashion) · [EuroSAT RGB](https://huggingface.co/datasets/torchgeo/eurosat/resolve/c877bcd43f099cd0196738f714544e355477f3fd/EuroSAT.zip) · [Gisette](https://archive.ics.uci.edu/static/public/170/gisette.zip)

```sh
python run.py cifar train-00000-of-00001.parquet cifar
python draw.py
python run.py cifar train-00000-of-00001.parquet cifar-matched --matched
python run.py cifar37 train-00000-of-00001.parquet cifar37
python run.py euro37 EuroSAT.zip euro37
python run.py fashion57 fashion-mnist fashion57
python run.py mn01all mnist mn01all
python run.py gisette-signed gisette.zip gisette-signed
```

Use `--forecast` with a separate output directory to run the reduced model on the same images. The other case names are `cifar01all`, `euro01`, `fashion79`, `mn78all` and `gisette-unit`. The Figure 1 plot decimates to every 256th iterate and independently marks the first actual strict fit from the full counts.

<details>
<summary>run.py</summary>

```python
import argparse
import gzip
import hashlib
import io
import json
import math
import zipfile
from pathlib import Path

import numpy as np
import pyarrow.parquet as pq
import torch
from PIL import Image

cases = {
    "cifar": ("cifar", 0, 1, 2500, 20261125, 400000, list(range(-6, 1))),
    "cifar37": ("cifar", 3, 7, 2500, 2026112737, 400000, list(range(-6, 1))),
    "cifar01all": ("cifar", 0, 1, 0, 2026112740, 400000, list(range(-6, 1))),
    "mn01all": ("mnist", 0, 1, 0, 2026112741, 50000, list(range(-6, 4))),
    "mn78all": ("mnist", 7, 8, 0, 2026112742, 50000, list(range(-6, 4))),
    "fashion57": ("fashion", 5, 7, 2500, 20261127, 500000, list(range(-4, 1))),
    "fashion79": ("fashion", 7, 9, 2500, 2026112702, 500000, list(range(-4, 1))),
}


def load(name, source):
    ds, a, b, k, seed, _T, _er = cases[name]
    if ds == "cifar":
        tab = pq.ParquetFile(source).read()
        lab = np.array(tab["label"])
    else:
        src = source
        lab = np.frombuffer(
            gzip.decompress((src / "train-labels-idx1-ubyte.gz").read_bytes()),
            np.uint8,
            offset=8,
        )
        pixel = np.frombuffer(
            gzip.decompress((src / "train-images-idx3-ubyte.gz").read_bytes()),
            np.uint8,
            offset=16,
        ).reshape(len(lab), -1)
    rg = np.random.default_rng(seed)
    ix = np.concatenate(
        [
            (
                rg.choice(np.flatnonzero(lab == c), k, replace=False)
                if k
                else np.flatnonzero(lab == c)
            )
            for c in [a, b]
        ]
    )
    if ds == "cifar":
        img = np.stack(
            [
                np.asarray(Image.open(io.BytesIO(tab["img"][int(i)].as_py()["bytes"])))
                .transpose(2, 0, 1)
                .reshape(-1)
                for i in ix
            ]
        )
        X = torch.from_numpy(img).cuda().float().div_(255).mul_(2).sub_(1)
    else:
        X = torch.from_numpy(pixel[ix].astype(float) / 127.5 - 1).cuda().float()
    X[: np.sum(lab[ix] == a)].neg_()
    return X, ix


def get(archive, pair, seed):
    rng = np.random.default_rng(seed)
    with zipfile.ZipFile(archive) as z:
        names = sorted(
            k
            for k in z.namelist()
            if k.lower().endswith(".jpg") and "__MACOSX" not in k
        )
        classes = sorted({f.split("/")[-2] for f in names})
        labels = np.array([classes.index(f.split("/")[-2]) for f in names])
        ix = np.concatenate(
            [
                rng.choice(np.flatnonzero(labels == int(cl)), 2500, replace=False)
                for cl in pair
            ]
        )
        pixels = np.stack(
            [
                np.asarray(Image.open(io.BytesIO(z.read(names[k]))).convert("RGB"))
                .transpose(2, 0, 1)
                .reshape(-1)
                for k in ix
            ]
        )
    X = torch.from_numpy(pixels).cuda().float().div_(255).mul_(2).sub_(1)
    X[:2500].neg_()
    return X, ix, hashlib.sha256(pixels.tobytes()).hexdigest()


def simulate(rows, rates, nlinear, seed, horizon):
    n, d = rows.shape
    torch.manual_seed(seed)
    readout = torch.rand((d, 1)).mul_(2 / math.sqrt(d)).sub_(1 / math.sqrt(d))
    taps = torch.rand((2, 1)).mul_(2 / math.sqrt(2)).sub_(1 / math.sqrt(2))
    size = len(rates)
    v = readout.repeat(1, size).cuda()
    c = taps.repeat(1, size).cuda()
    learn = torch.arange(size, device="cuda") >= nlinear
    eta = torch.tensor(rates, device="cuda") / n
    block_size = 32
    counts = torch.empty((block_size, size), dtype=torch.int32, device="cuda")

    def reset():
        v.copy_(readout.repeat(1, size))
        c.copy_(taps.repeat(1, size))
        c[0, :nlinear] = 1
        c[1, :nlinear] = 0

    def scores():
        return rows @ (c[0] * v + c[1] * v.roll(-1, 0))

    def block():
        for t in range(block_size):
            m = scores()
            counts[t].copy_((m > 0).sum(0))
            g = rows.T @ torch.sigmoid(-m)
            shifted = g.roll(1, 0)
            dv = c[0] * g + c[1] * shifted
            dc = torch.stack([(g * v).sum(0), (shifted * v).sum(0)]) * learn
            v.add_(dv * eta)
            c.add_(dc * eta)

    reset()
    stream = torch.cuda.Stream()
    stream.wait_stream(torch.cuda.current_stream())
    with torch.cuda.stream(stream):
        block()
    stream.synchronize()
    reset()
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        block()
    result = np.empty((horizon + 1, size), dtype=np.int32)
    for t in range(0, horizon, block_size):
        graph.replay()
        result[t : t + block_size] = counts.cpu().numpy()
    result[-1] = (scores() > 0).sum(0).cpu().numpy()
    return result, taps.numpy().ravel().tolist()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "case", choices=[*cases, "euro37", "euro01", "gisette-signed", "gisette-unit"]
    )
    ap.add_argument("source", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--matched", action="store_true")
    ap.add_argument("--forecast", action="store_true")
    args = ap.parse_args()
    if args.forecast and args.matched:
        ap.error("Forecast uses the plotted grid")
    torch.set_float32_matmul_precision("highest")
    if args.case.startswith("euro"):
        pair = args.case[-2:]
        seed = 2026112775 if pair == "37" else 2026112776
        rows, ix, _ = get(args.source, pair, seed)
        horizon = 100000
        exp = range(-5, 1)
    elif args.case.startswith("gisette"):
        with zipfile.ZipFile(args.source) as z:
            with z.open("GISETTE/gisette_train.data") as data:
                pixels = np.stack(
                    [
                        np.fromstring(row.decode(), dtype=np.int16, sep=" ")
                        for row in data
                    ]
                )
            labels = np.fromstring(
                z.read("GISETTE/gisette_train.labels").decode(), dtype=np.int8, sep=" "
            )
        rows = torch.tensor(pixels, device="cuda").float() / 999
        if args.case == "gisette-signed":
            rows = 2 * rows - 1
        rows *= torch.tensor(labels[:, None], device="cuda")
        ix = np.arange(len(rows))
        seed, horizon, exp = 20261125, 10000, range(-6, 1)
    else:
        _, _, _, _, seed, horizon, exp = cases[args.case]
        rows, ix = load(args.case, args.source)
    raw = [10.0**j for j in range(-3, 3)]
    joint = [2.0**j for j in exp]
    if args.matched:
        raw = joint = [2.0 ** (j / 2) for j in range(-20, 15)]
    if args.forecast:
        from predict import proj

        counts, _ = proj(rows, seed, raw + joint, horizon, args.case.startswith("euro"))
    else:
        counts, _ = simulate(
            rows, raw + joint, len(raw), seed, 32 * ((horizon + 31) // 32)
        )
    counts = counts[: horizon + 1]
    hits = [
        int(k[0]) if len(k) else None
        for k in (np.flatnonzero(c == len(rows)) for c in counts.T)
    ]
    args.output.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(args.output / "correct.npz", correct=counts)
    np.save(args.output / "indices.npy", ix)
    report = dict(
        seed=seed,
        raw=raw,
        joint=joint,
        hits=hits,
        index_sha256=hashlib.sha256(ix.astype("<i8").tobytes()).hexdigest(),
    )
    (args.output / "summary.json").write_text(json.dumps(report, indent=2))
    print(report)


if __name__ == "__main__":
    main()
```

</details>

<details>
<summary>predict.py</summary>

```python
import math

import numpy as np
import torch


def enriched(X, v0):
    X = X.double()
    n = len(X)
    d = X.shape[1]
    Y = X.roll(1, 1)
    V = torch.linalg.eigh(X.T @ X / n)[1][:, -16:]
    cols = [v0[:, 0].double().cuda(), *V.T, *V.roll(1, 0).T]
    selects = []
    for angle in [0.0, -0.71, 0.4]:
        Z = (math.cos(angle) * X + math.sin(angle) * Y).contiguous()
        v = cols[0] * 0
        for k in range(1, 9):
            L = 10 ** (-k)
            for _ in range(40):
                m = Z @ v
                q = torch.sigmoid(-m)
                g = L * v - Z.T @ q / n
                H = (Z.T * (q * (1 - q) / n)) @ Z
                H.diagonal().add_(L)
                dv = torch.cholesky_solve(g[:, None], torch.linalg.cholesky(H))[:, 0]
                if g @ dv < 1e-16:
                    break
                a = 1.0
                f = torch.nn.functional.softplus(-m).mean() + L * (v @ v) / 2
                while a > 1e-6:
                    cand = v - a * dv
                    if (
                        torch.nn.functional.softplus(-Z @ cand).mean()
                        + L * (cand @ cand) / 2
                        <= f
                    ):
                        break
                    a /= 2
                v = cand
            cols.append(v.clone())
            if k == 6:
                selects.extend(torch.argsort(Z @ v)[:8].tolist())
    for j, angle in enumerate([0.0, -0.71, 0.4]):
        ca, sa = math.cos(angle), math.sin(angle)
        shift = torch.exp(
            2j * torch.pi * torch.arange(d, device=X.device, dtype=X.dtype) / d
        )
        for k in [5, 6, 7]:
            w = cols[33 + 8 * j + k]
            pred = ca * w + sa * torch.roll(w, -1)
            physgrad = X.T @ torch.sigmoid(-X @ pred) / n
            for a in [-1.4, -1.1, -0.95, -0.85, -0.65, -0.4, 0.0, 0.4, 0.8, 1.2]:
                sw = torch.fft.ifft(
                    torch.fft.fft(pred) * math.hypot(1.0, a) / (1 + a * shift)
                ).real
                wg = (physgrad + a * torch.roll(physgrad, 1)) / math.hypot(1.0, a)
                cols.extend([sw, wg])
    ix = sorted(set(selects))
    cols.extend(X[ix])
    cols.extend(Y[ix])
    # Numerical rank determination handles identical hard rows across views.
    C = torch.stack(cols, dim=1)
    U, S, V = torch.linalg.svd(C / C.norm(dim=0), full_matrices=False)
    return U[:, S > S[0] * 1e-9].contiguous().float(), ix


def kernel_basis(X, v0):
    X = X.double()
    n, d = X.shape
    Y = X.roll(1, 1)
    K = X @ X.T / n
    spectrum, V = torch.linalg.eigh(K)
    V = (X.T @ V[:, -16:]) / (n * spectrum[-16:]).sqrt()
    cols = [v0[:, 0].double().cuda(), *V.T, *V.roll(1, 0).T]
    sel = []
    identity = torch.eye(n, dtype=X.dtype, device="cuda")
    for angle in [0.0, -0.71, 0.4]:
        Z = math.cos(angle) * X + math.sin(angle) * Y
        K = (Z @ Z.T) / n
        b = Z.new_zeros(n)
        for k in range(1, 9):
            L = 10.0 ** (-k)
            for it in range(40):
                m = K @ b
                q = (-m).sigmoid()
                s = q * (1 - q)
                z = L * b - q
                db = torch.linalg.solve(s[:, None] * K + L * identity, z)
                delta = z @ (K @ db) / n
                if float(delta) < 1e-16:
                    break
                f = torch.nn.functional.softplus(-m).mean() + L * (b @ m) / (2 * n)
                a = 1.0
                while a > 1e-6:
                    bn = b - a * db
                    mn = K @ bn
                    if (
                        torch.nn.functional.softplus(-mn).mean()
                        + L * (bn @ mn) / (2 * n)
                        <= f
                    ):
                        break
                    a /= 2
                b = bn
            cols.append(Z.T @ b / n)
            if k == 6:
                sel.extend(torch.argsort(K @ b)[:8].tolist())
    for j, angle in enumerate([0.0, -0.71, 0.4]):
        ca, sa = math.cos(angle), math.sin(angle)
        shift = torch.exp(
            2j * torch.pi * torch.arange(d, device=X.device, dtype=X.dtype) / d
        )
        for k in [5, 6, 7]:
            w = cols[33 + 8 * j + k]
            pred = ca * w + sa * torch.roll(w, -1)
            physgrad = X.T @ torch.sigmoid(-X @ pred) / n
            for a in [-1.4, -1.1, -0.95, -0.85, -0.65, -0.4, 0.0, 0.4, 0.8, 1.2]:
                sw = torch.fft.ifft(
                    torch.fft.fft(pred) * math.hypot(1.0, a) / (1 + a * shift)
                ).real
                wg = (physgrad + a * torch.roll(physgrad, 1)) / math.hypot(1.0, a)
                cols.extend([sw, wg])
    ix = sorted(set(sel))
    cols.extend(X[ix])
    cols.extend(Y[ix])
    C = torch.stack(cols, dim=1)
    U, S, V = torch.linalg.svd(C / C.norm(dim=0), full_matrices=False)
    B = U[:, S > S[0] * 1e-9].contiguous().float()
    return B, ix


def proj(X, seed, rates, T, kernel):
    n, d = X.shape
    torch.manual_seed(seed)
    v0 = torch.rand((d, 1)).mul_(2 / math.sqrt(d)).sub_(1 / math.sqrt(d))
    c0 = torch.rand((2, 1)).mul_(2 / math.sqrt(2)).sub_(1 / math.sqrt(2))
    basis, hard = kernel_basis(X, v0) if kernel else enriched(X, v0)
    y = X @ basis
    z = X.roll(1, 1) @ basis
    h = len(rates)
    eta = X.new_tensor(rates) / n
    flag = torch.arange(h, device="cuda") >= 6
    v = (basis.T @ v0.cuda()).repeat(1, h)
    c = c0.cuda().repeat(1, h)
    c[0, :6] = 1
    c[1, :6] = 0
    initv = v.clone()
    initc = c.clone()
    stat = torch.empty((32, h), device="cuda", dtype=torch.int32)

    def block():
        for i in range(32):
            f = y @ v
            g = z @ v
            m = c[0] * f + c[1] * g
            q = torch.sigmoid(-m)
            dv = c[0] * (y.T @ q) + c[1] * (z.T @ q)
            dc = torch.stack([(q * f).sum(0), (q * g).sum(0)]) * flag
            stat[i] = (m > 0).sum(0)
            v.add_(dv * eta)
            c.add_(dc * eta)

    block()
    v.copy_(initv)
    c.copy_(initc)
    G = torch.cuda.CUDAGraph()
    with torch.cuda.graph(G):
        block()
    counts = np.empty((T + 1, h), np.int32)
    for t in range(0, T + 1, 32):
        G.replay()
        nn = min(T + 1 - t, 32)
        counts[t : t + nn] = stat[:nn].cpu().numpy()
    return counts, {"basis": basis.shape[1], "hard": hard}
```

</details>

<details>
<summary>draw.py</summary>

```python
from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).parent
counts = np.load(root / "cifar" / "correct.npz")["correct"]
rates = [
    [0.001, 0.01, 0.1, 1, 10, 100],
    [1 / 64, 1 / 32, 1 / 16, 1 / 8, 1 / 4, 1 / 2, 1],
]
fig, axs = plt.subplots(1, 2, figsize=(11, 4), sharey=True, constrained_layout=True)
for ax, start, etas, title in zip(
    axs, [0, 6], rates, ["Linear readout", "Two learned taps and readout"]
):
    for k, eta in enumerate(etas):
        col = counts[:, start + k]
        peak = np.flatnonzero(col == 5000)
        lab = f"{eta:g}"
        ax.plot(
            np.arange(0, len(col), 256),
            col[::256] / 5000,
            linewidth=0.75,
            alpha=0.85,
            label=lab,
        )
        if peak.size:
            ax.scatter(peak[0], 1, s=13, zorder=5)
    ax.set(xlabel="Full-gradient updates", title=title, ylim=(0.77, 1.008))
    ax.ticklabel_format(axis="x", style="sci", scilimits=(3, 3))
    ax.legend(title="Constant step", ncol=2, fontsize=8)
    ax.grid(alpha=0.15)
axs[0].set_ylabel("Fraction of 5,000 training images classified correctly")
fig.savefig(root / "figure1.png", dpi=180)
```

</details>
