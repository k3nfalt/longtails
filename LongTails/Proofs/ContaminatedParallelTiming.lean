import LongTails.Proofs.ContaminatedParallelSchedule
import LongTails.Proofs.ContaminatedValidationCalendar

namespace LongTails.Proofs.ContaminatedParallelTiming

open DistributedTemplate
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (resolution height iterations blockSize width)
open ContaminatedParallelSchedule ContaminatedValidationCalendar ContaminatedCalendarBudget

noncomputable def variance (p : Params) := (∑ j, (p.h j : ℝ)*p.σ j^2) / ((p.n:ℝ)^2 * resolution (network p)^2)
noncomputable def computeUnit (p : Params) := Finset.univ.sup p.h + (variance p).toNNReal
noncomputable def baseTime (p : Params) := ((1+Nat.log2 p.n:ℕ):Time) * Finset.univ.sup p.h + p.l +
  p.b * (64 + blockSize (network p) * (8 + Nat.log2 ((p.n:ℕ)*(p.d+1))) : ℕ)

lemma compute_bound (p : Params) (hh : ∀ i, 0 < p.h i) (op : Operation) (hq : 1 ≤ op.precision p) :
    computeTime p op ≤ 2^26 * op.precision p * computeUnit p +
      8 * (1+Nat.log2 p.n:ℕ) * Finset.univ.sup p.h := by
  apply Finset.sup_le
  intro i _
  let H : ℝ := (Finset.univ.sup p.h : Time)
  let A := variance p
  let h := (p.h i:ℝ)
  let r := (op.precision p:ℝ)
  let z := Nat.log2 p.n
  have hh₀ : 0 < h := by exact_mod_cast hh i
  have hH : h ≤ H := by exact_mod_cast Finset.le_sup (f := p.h) (Finset.mem_univ i)
  have hr : 1 ≤ r := by dsimp only [r]; exact_mod_cast hq
  have hA : 0 ≤ A := by dsimp [A,variance]; positivity
  have he : (∑ j, (p.h j:ℝ)*p.σ j^2) / ((p.n:ℝ)^2*resolution (network p)^2*(p.h i:ℝ)) = A/h := by dsimp [A,variance,h]; ring
  have hc := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (show 0 ≤ A/h by positivity)).le hh₀.le
  rw [add_mul,div_mul_cancel₀ _ hh₀.ne',one_mul] at hc
  have hl : 1 ≤ 16777216*op.precision p*(1+⌈A/h⌉₊) := by
    have := Nat.mul_le_mul (show 1 ≤ 16777216 by decide) hq
    nlinarith
  apply NNReal.coe_le_coe.mp
  simp only [computeUnit,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_natCast,NNReal.coe_ofNat,
    Real.coe_toNNReal (variance p) hA]
  change ((pilotCount p (op.precision p)+freshCount p (op.precision p) i:ℕ):ℝ)*h ≤ _
  unfold pilotCount freshCount
  rw [he,max_eq_right hl]
  push_cast
  change (8*(1+z+r)+16777216*r*(1+(⌈A/h⌉₊:ℝ)))*h ≤ 2^26*r*(H+A)+8*(1+z)*H
  nlinarith only [mul_le_mul_of_nonneg_left hc (show 0 ≤ r by positivity),
    mul_le_mul_of_nonneg_left hH (show 0 ≤ r by positivity),
    mul_le_mul_of_nonneg_left hH (show 0 ≤ 1+(z:ℝ) by positivity),
    mul_nonneg (show 0 ≤ r by positivity) hA, mul_nonneg (show 0 ≤ r by positivity) hh₀.le]

lemma cost_bound (p : Params) (hh : ∀ i, 0 < p.h i) (op : Operation) (hq : 1 ≤ op.precision p) :
    cost p op ≤ 2^26 * (op.precision p:Time) * computeUnit p +
      16 * (1+(op.level:Time)) * baseTime p := by
  let H := ((1+Nat.log2 p.n:ℕ):Time) * Finset.univ.sup p.h
  let W := (8+Nat.log2 ((p.n:ℕ)*(p.d+1)):ℕ)
  let B := (blockSize (network p):Time)
  let m := (op.level:Time)
  have hw : 1 ≤ (W:Time) := by dsimp [W]; exact_mod_cast (by omega : 1 ≤ 8+Nat.log2 ((p.n:ℕ)*(p.d+1)))
  have hW : B ≤ B*(W:Time) := le_mul_of_one_le_right zero_le hw
  have hb : p.b*B ≤ p.b*(64+B*W) := mul_le_mul_of_nonneg_left (hW.trans le_add_self) zero_le
  have hbase : p.b*B ≤ baseTime p := by
    apply hb.trans
    unfold baseTime
    push_cast
    dsimp [B,W]
    push_cast
    exact le_add_self
  have hlink : linkTime p op.level ≤ baseTime p + 2*m*baseTime p := by
    have h := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2*m from zero_le)
    unfold linkTime width baseTime at *
    dsimp only [B,m] at *
    push_cast at *
    apply NNReal.coe_le_coe.mp
    have h' := NNReal.coe_le_coe.mpr h
    push_cast at h' ⊢
    nlinarith only [h',show (0:ℝ) ≤ (1+(Nat.log2 p.n:ℝ))*((Finset.univ.sup p.h:Time):ℝ) by positivity,
      show (0:ℝ) ≤ (p.b:ℝ) * blockSize (network p) by positivity]
  have hH : H ≤ baseTime p := by unfold baseTime; exact (le_self_add.trans le_self_add)
  have hc := compute_bound p hh op hq
  change _ ≤ 2^26*(op.precision p:Time)*computeUnit p + _ at hc
  have h8 : 8*(1+Nat.log2 p.n:ℕ)*(Finset.univ.sup p.h:Time) = 8*H := by dsimp [H]; ring
  rw [h8] at hc
  unfold cost
  change _ ≤ _ + 16*(1+m)*baseTime p
  apply NNReal.coe_le_coe.mp
  have h₁ := NNReal.coe_le_coe.mpr hc
  have h₂ := NNReal.coe_le_coe.mpr hlink
  have h₃ := NNReal.coe_le_coe.mpr hH
  push_cast at h₁ h₂ h₃ ⊢
  nlinarith only [h₁,h₂,h₃, show (0:ℝ) ≤ baseTime p by positivity, show (0:ℝ) ≤ (m:ℝ)*(baseTime p:ℝ) by positivity]

end LongTails.Proofs.ContaminatedParallelTiming
