import LongTails.Proofs.LeonCalendar
import LongTails.Proofs.LeonRoundTrace

namespace LongTails.Proofs.LeonTiming

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonCalendar
open DistributedTemplate

noncomputable def computeUnit (p : Params) : Time :=
  Finset.univ.sup p.h + (∑ i, p.h i) * (p.σ ^ 2 / ((p.n : ℝ)^2 * resolution p ^ 2)).toNNReal

noncomputable def linkUnit (p : Params) : Time :=
  p.l + p.b * (64 + blockSize p * (8 + Nat.log2 ((p.n : ℕ) * (p.d + 1))) : ℕ)

lemma batch_time (p : Params) (hh : ∀ i, 0 < p.h i) (i : Fin p.n) (l : ℕ) :
    (batch p i l : ℕ) * p.h i ≤ (2 : Time)^l * computeUnit p := by
  let A := p.σ ^ 2 / ((p.n : ℝ)^2 * resolution p ^ 2)
  let H := ∑ j, (p.h j : ℝ)
  have hi : (0 : ℝ) < p.h i := by exact_mod_cast hh i
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hmax : (p.h i : ℝ) ≤ (Finset.univ.sup p.h : Time) := by
    exact_mod_cast Finset.le_sup (f := p.h) (Finset.mem_univ i)
  have he : p.σ ^ 2 * H / ((p.n : ℝ)^2 * resolution p ^ 2 * (p.h i : ℝ)) = A * H / (p.h i : ℝ) := by
    dsimp [A]; ring
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ A * H / (p.h i : ℝ) by positivity)).le
  have hceil : (max 1 ⌈A * H / (p.h i : ℝ)⌉₊ : ℝ) ≤ 1 + A * H / (p.h i : ℝ) :=
    max_le (by linarith [show 0 ≤ A * H / (p.h i : ℝ) by positivity]) (by linarith)
  apply NNReal.coe_le_coe.mp
  simp only [computeUnit, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, NNReal.coe_sum]
  change ((2 ^ l * max 1 ⌈p.σ^2 * H / ((p.n : ℝ)^2 * resolution p ^ 2 * (p.h i : ℝ))⌉₊ : ℕ) : ℝ) * (p.h i : ℝ) ≤
    2 ^ l * ((Finset.univ.sup p.h : Time) + H * A.toNNReal)
  rw [he, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.coe_toNNReal _ hA, Nat.cast_max, Nat.cast_one, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (mul_le_mul_of_nonneg_right hceil hi.le).trans
  rw [add_mul, one_mul, div_mul_cancel₀ _ hi.ne', mul_comm A]
  exact add_le_add hmax le_rfl

lemma width_time (p : Params) (l : ℕ) :
    p.l + p.b * (64 + blockSize p * width p l : ℕ) ≤ (2 : Time)^l * linkUnit p := by
  let a := Nat.log2 ((p.n : ℕ) * (p.d + 1))
  have hl : l + 1 ≤ 2^l := by
    induction l with
    | zero => decide
    | succ l ih => rw [pow_succ]; omega
  have ht : 1 ≤ (2:ℕ)^l := by omega
  have hw : width p l ≤ 2^l * (8 + a) := by
    have h := Nat.mul_le_mul_right a ht
    change 7 + a + 2*l ≤ _
    rw [Nat.mul_add]; omega
  have hsize : 64 + blockSize p * width p l ≤ 2^l * (64 + blockSize p * (8 + a)) := by
    rw [Nat.mul_add, Nat.mul_left_comm _ (blockSize p)]
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ hw)
  have ht' : 1 ≤ (2 : Time)^l := by exact_mod_cast ht
  unfold linkUnit
  rw [mul_add, mul_left_comm _ p.b]
  apply add_le_add
  · simpa using mul_le_mul_of_nonneg_right ht' zero_le
  · apply mul_le_mul_of_nonneg_left _ zero_le
    exact_mod_cast hsize

noncomputable def roundTime (p : Params) (l : ℕ) : Time :=
  (2 : Time)^l * (computeUnit p + 2 * linkUnit p)

lemma calendar_time (p : Params) :
    ((levels (height p)).map (roundTime p)).sum ≤
      8 * (1 + ⌈2 * p.L * p.Δ / resolution p ^ 2⌉₊ : ℕ) * (computeUnit p + 2 * linkUnit p) := by
  let ls := levels (height p)
  let C := computeUnit p + 2 * linkUnit p
  have hsum (xs : List ℕ) : (xs.map (roundTime p)).sum = (((xs.map (fun j => 2^j)).sum : ℕ) : Time) * C := by
    induction xs with
    | nil => simp
    | cons j xs ih => simp [roundTime, ih, C, add_mul]
  rw [hsum]
  apply mul_le_mul_of_nonneg_right _ zero_le
  have hnat : ((levels (height p)).map (fun j => (2:ℕ)^j)).sum ≤
    8 * (1 + ⌈2 * p.L * p.Δ / resolution p ^ 2⌉₊) := by
      have h := LeonCalendar.batch_work (height p)
      have hb := LeonBatchTuning.iterations_upper p
      unfold iterations at hb
      exact ((Nat.le_add_right _ _).trans h.le).trans ((Nat.mul_le_mul_left 2 hb).trans_eq (by ring))
  exact_mod_cast hnat

end LongTails.Proofs.LeonTiming

namespace LongTails.Proofs.LeonClosedBudget

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonCalendar
open LeonTiming

lemma sufficient (p : Params) :
    ((levels (height p)).map (roundTime p)).sum ≤
      8 * (1 + ⌈2^19 * p.L * p.Δ / p.ε^2⌉₊ : ℕ) * (Finset.univ.sup p.h +
        (∑ i, p.h i) * (2^18 * p.σ^2 / ((p.n : ℝ)^2 * p.ε^2)).toNNReal +
        2 * (p.l + p.b * (64 + ((p.d + p.n - 1) / p.n) * (8 + Nat.log2 ((p.n : ℕ) * (p.d + 1))) : ℕ))) := by
  apply (calendar_time p).trans_eq
  have hi : 2 * p.L * p.Δ / resolution p ^ 2 = 2^19 * p.L * p.Δ / p.ε^2 := by
    unfold resolution
    rw [div_pow,div_div_eq_mul_div]
    ring
  have hn : p.σ^2 / ((p.n : ℝ)^2 * resolution p^2) = 2^18*p.σ^2 / ((p.n : ℝ)^2 * p.ε^2) := by
    unfold resolution
    rw [div_pow,← mul_div_assoc,div_div_eq_mul_div]
    ring
  simp only [computeUnit,linkUnit,blockSize,hi,hn]

end LongTails.Proofs.LeonClosedBudget
