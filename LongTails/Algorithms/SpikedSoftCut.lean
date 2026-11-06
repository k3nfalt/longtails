import LongTails.Setups.SpikedSubGaussianConvex
import LongTails.Algorithms.CovarianceSoftCut
import Mathlib.Data.List.MinMax

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Algorithms.SpikedSoftCut

open LongTails.Setups.SpikedSubGaussianConvex

abbrev InnerSpace (q : Params) := EuclideanSpace ℝ (Fin q.m)

def join (q : Params) (a : ℝ) (y : InnerSpace q) : Space q :=
  WithLp.toLp 2 (Fin.cons a y)

def head (q : Params) (x : Space q) : ℝ := x 0

def tail (q : Params) (x : Space q) : InnerSpace q :=
  WithLp.toLp 2 (fun i => x i.succ)

def innerParams (q : Params) (α : ℝ) : LongTails.Setups.CovarianceBoundedConvex.Params where
  d := q.m
  Ω := q.Ω
  L := q.G
  R := q.R / 2
  σ := 0
  ε := α

def certificateScore (q : Params) (α : ℝ) {T : ℕ}
    (points estimates : Fin T → InnerSpace q) (θ : Fin T → ℝ) : ℝ :=
  (∑ i, θ i * (α / 2 - ⟪estimates i, points i⟫)) -
    q.R * ‖∑ i, θ i • estimates i‖

def gridCoefficients {T n : ℕ} (k : Fin T → Fin (n + 1)) : Fin T → ℝ :=
  fun i => (k i).val / (n : ℝ)

def coefficientGrid (T n : ℕ) : List (Fin T → Fin (n + 1)) := Finset.univ.toList

def selectedCoefficients (q : Params) (α : ℝ) (T n : ℕ)
    (points estimates : Fin T → InnerSpace q) : Fin T → ℝ :=
  gridCoefficients (((coefficientGrid T n).argmax
    (fun k => certificateScore q α points estimates (gridCoefficients k))).getD (fun _ => 0))

def certificateWeights (q : Params) (α : ℝ) (T n : ℕ)
    (points estimates : Fin T → InnerSpace q) : Fin T → ℝ :=
  let θ := selectedCoefficients q α T n points estimates
  if 0 < ∑ i, θ i then fun i => θ i / ∑ j, θ j
  else fun i => if i.val = 0 then 1 else 0

def innerPoints (q : Params) (α : ℝ) (T b : ℕ)
    (replies : ℕ → InnerSpace q) : Fin T → InnerSpace q :=
  fun i => CovarianceSoftCut.generatorPoint (innerParams q α) α (2 / α) b i.val replies

def innerEstimates (q : Params) (α : ℝ) (T b : ℕ)
    (replies : ℕ → InnerSpace q) : Fin T → InnerSpace q :=
  fun i => CovarianceSoftCut.batchMean (innerParams q α) b i.val replies

def innerWeights (q : Params) (α : ℝ) (T b n : ℕ)
    (replies : ℕ → InnerSpace q) : Fin T → ℝ :=
  certificateWeights q α T n (innerPoints q α T b replies) (innerEstimates q α T b replies)

def innerOutput (q : Params) (α : ℝ) (T b n : ℕ)
    (replies : ℕ → InnerSpace q) : InnerSpace q :=
  ∑ i, innerWeights q α T b n replies i • innerPoints q α T b replies i

end LongTails.Algorithms.SpikedSoftCut
