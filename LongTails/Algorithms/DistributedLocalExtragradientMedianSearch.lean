import LongTails.Algorithms.DistributedLocalExtragradientWarmStart
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.DistributedLocalExtragradientMedianSearch

open LongTails.Algorithms.DistributedQuantization

noncomputable def countBelow {n d width : ℕ} (codes : Fin n → Grid d width)
    (j : Fin d) (threshold : ℕ) : ℕ :=
  ∑ i, if (codes i j).val < threshold then 1 else 0

def binarySearch (test : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, lo => lo
  | w + 1, lo =>
      if test (lo + 2 ^ w) then binarySearch test w lo
      else binarySearch test w (lo + 2 ^ w)

noncomputable def medianCode {n d width : ℕ} (codes : Fin n → Grid d width)
    (j : Fin d) : ℕ :=
  binarySearch (fun threshold => decide (n / 2 < countBelow codes j threshold)) width 0

def countWidth (n : ℕ) : ℕ := Nat.log2 n + 1

def nextLower {d : ℕ} (remaining : ℕ) (lo : Fin d → ℕ) (decisions : Fin d → Bool) : Fin d → ℕ :=
  fun j => if decisions j then lo j else lo j + 2 ^ remaining

end LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
