import LongTails.Setups.CovarianceBoundedConvex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Algorithms.CovarianceSoftCut

open LongTails.Setups.CovarianceBoundedConvex

abbrev Cut (q : Params) := Space q × Space q

def hinge (q : Params) (α : ℝ) (cut : Cut q) (y : Space q) : ℝ :=
  max 0 (⟪cut.1, y - cut.2⟫ + α / 2)

def lossSum (q : Params) (α : ℝ) (cuts : List (Cut q)) (y : Space q) : ℝ :=
  ∑ i ∈ Finset.range cuts.length, hinge q α (cuts.getD i (0, 0)) y

def coreWeight (q : Params) (α η : ℝ) (cuts : List (Cut q)) (y : Space q) : ℝ :=
  Real.exp (-η * lossSum q α cuts y)

def weight (q : Params) (α η : ℝ) (cuts : List (Cut q)) (y : Space q) : ℝ :=
  if ‖y‖ ≤ 2 * q.R then coreWeight q α η cuts y else 0

def mass (q : Params) (α η : ℝ) (cuts : List (Cut q)) : ℝ :=
  ∫ y, weight q α η cuts y

def centroid (q : Params) (α η : ℝ) (cuts : List (Cut q)) : Space q :=
  (mass q α η cuts)⁻¹ • ∫ y, weight q α η cuts y • y

def batchMean (q : Params) (b t : ℕ) (replies : ℕ → Space q) : Space q :=
  (b : ℝ)⁻¹ • ∑ i : Fin b, replies (t * b + i.val)

def generatorCuts (q : Params) (α η : ℝ) (b : ℕ) :
    (n : ℕ) → (ℕ → Space q) → Fin n → Cut q
  | 0, _ => Fin.elim0
  | n + 1, replies =>
      let previous := generatorCuts q α η b n replies
      Fin.append previous (fun _ : Fin 1 =>
        (batchMean q b n replies, centroid q α η (List.ofFn previous)))

def generatorPoint (q : Params) (α η : ℝ) (b n : ℕ) (replies : ℕ → Space q) : Space q :=
  centroid q α η (List.ofFn (generatorCuts q α η b n replies))

def generatorCandidates (q : Params) (α η : ℝ) (b T : ℕ) (replies : ℕ → Space q) :
    List (Space q) :=
  List.ofFn (fun i : Fin T => generatorPoint q α η b i.val replies)

def segmentMid (q : Params) (ends : Space q × Space q) : Space q :=
  (1 / 2 : ℝ) • (ends.1 + ends.2)

def segmentDirection (q : Params) (ends : Space q × Space q) : Space q :=
  ‖ends.2 - ends.1‖⁻¹ • (ends.2 - ends.1)

def bisectUpdate (q : Params) (a : ℝ) (ends : Space q × Space q) (estimate : ℝ) : Space q × Space q :=
  if 2 * a < estimate then (ends.1, segmentMid q ends)
  else if estimate < -(2 * a) then (segmentMid q ends, ends.2)
  else (segmentMid q ends, segmentMid q ends)

def bisectRun (q : Params) (a : ℝ) (initial : Space q × Space q) (estimates : ℕ → ℝ) :
    ℕ → Space q × Space q
  | 0 => initial
  | n + 1 => bisectUpdate q a (bisectRun q a initial estimates n) (estimates n)

def directionalMean (q : Params) (n : ℕ) (u : Space q) (replies : Fin n → Space q) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ⟪replies i, u⟫

def directionalMom (q : Params) (n m : ℕ) (u : Space q) (replies : ℕ → Space q) : ℝ :=
  ((List.ofFn (fun j : Fin m => directionalMean q n u (fun i => replies (j.val*n+i.val)))).mergeSort
    (· ≤ ·)).getD (m / 2) 0

def groupIndex (n m : ℕ) (j : Fin m) (i : Fin n) : Fin (n*m) :=
  ⟨j.val*n+i.val, by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul, Nat.mul_comm m n] at h
    have hi := i.isLt
    omega⟩

def directionalMomBlock (q : Params) (n m : ℕ) (u : Space q) (replies : Fin (n*m) → Space q) : ℝ :=
  ((List.ofFn (fun j : Fin m => directionalMean q n u (fun i => replies (groupIndex n m j i)))).mergeSort
    (· ≤ ·)).getD (m / 2) 0

def bisectReplyRun (q : Params) (a : ℝ) (n m : ℕ) (initial : Space q × Space q)
    (replies : ℕ → Space q) : ℕ → Space q × Space q
  | 0 => initial
  | k + 1 =>
    let ends := bisectReplyRun q a n m initial replies k
    bisectUpdate q a ends (directionalMomBlock q n m (segmentDirection q ends)
      (fun i => replies (k*(n*m)+i.val)))

def bisectProbe (q : Params) (a : ℝ) (n m : ℕ) (initial : Space q × Space q)
    (replies : ℕ → Space q) (k : ℕ) : Space q × Space q :=
  let ends := bisectReplyRun q a n m initial replies k
  (segmentMid q ends, segmentDirection q ends)

def selectionBlocks (K h : ℕ) : ℕ := (2^h-1)*K

def selectionOutput (q : Params) (a : ℝ) (K n m : ℕ) :
    ℕ → (ℕ → Space q) → (ℕ → Space q) → Space q
  | 0, leaves, _ => leaves 0
  | h+1, leaves, replies =>
    let C := selectionBlocks K h * (n*m)
    let left := selectionOutput q a K n m h leaves replies
    let right := selectionOutput q a K n m h (fun i => leaves (2^h+i)) (fun i => replies (C+i))
    segmentMid q (bisectReplyRun q a n m (left, right) (fun i => replies (2*C+i)) K)

def selectionProbe (q : Params) (a : ℝ) (K n m : ℕ) :
    ℕ → (ℕ → Space q) → (ℕ → Space q) → ℕ → Space q × Space q
  | 0, _, _, _ => (0, 0)
  | h+1, leaves, replies, t =>
    let B := selectionBlocks K h
    let C := B*(n*m)
    if t < B then selectionProbe q a K n m h leaves replies t
    else if t < 2*B then selectionProbe q a K n m h
      (fun i => leaves (2^h+i)) (fun i => replies (C+i)) (t-B)
    else
      let left := selectionOutput q a K n m h leaves replies
      let right := selectionOutput q a K n m h (fun i => leaves (2^h+i)) (fun i => replies (C+i))
      bisectProbe q a n m (left, right) (fun i => replies (2*C+i)) (t-2*B)

def writeBlock (q : Params) (B start : ℕ) (replies : ℕ → Space q) (values : Fin B → Space q) :
    ℕ → Space q := fun i =>
  if h : start ≤ i ∧ i < start+B then values ⟨i-start, by omega⟩ else replies i

def historyMethod (q : Params) (query : ℕ → (ℕ → Space q) → Space q)
    (output : (ℕ → Space q) → Space q) : OracleTemplate.Algorithm (Space q) (Space q) (Space q) where
  State := ℕ × (ℕ → Space q)
  initial _ := (0, fun _ => 0)
  query s := (0, query s.1 s.2)
  update s reply := (s.1+1, Function.update s.2 s.1 reply)
  output s := output s.2

end LongTails.Algorithms.CovarianceSoftCut
