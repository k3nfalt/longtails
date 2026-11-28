import LongTails.Proofs.BrightnessLogisticSeparation
import LongTails.Proofs.BrightnessLogisticGradient

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features Space)
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)

namespace LongTails.Proofs.BrightnessLogisticFirstFit

open ManySampleConvolutionalPerceptronDynamics (State)
open ManySampleConvolutionalPerceptronGeometry (decode)
open BrightnessLogisticModes BrightnessLogisticField BrightnessLogisticHorizon
open BrightnessLogisticConstants BrightnessLogisticForces BrightnessLogisticSeparation
open BrightnessLogisticGradient

lemma centered (p : Params) (hp : Valid p) (k : ℕ) : ⟪axis p.d,(orbit p k).z⟫=0 := by
  induction k with
  | zero => exact hp.startCentered
  | succ k ih =>
    rw [BrightnessLogisticHorizon.next]
    exact step_center p hp _ ih

lemma actual (p : Params) (hp : Valid p) (k : ℕ) :
    decode 1 (orbit p k) =
      (fun z => z + p.input.step • (answer (u := p.input) p.rows z).1)^[k] p.input.start := by
  induction k with
  | zero => exact start_decode p
  | succ k ih =>
    rw [BrightnessLogisticHorizon.next,actual_step p hp _ (centered p hp k),Function.iterate_succ_apply',ih]

lemma first_fit (p : Params) (hp : Valid p) :
    ∃ k ≤ ⌈2*(p.n : ℝ)*p.M/(p.κ/p.R)⌉₊, fits (u := p.input) p.rows
      ((fun z => z+p.input.step • (answer (u := p.input) p.rows z).1)^[k] p.input.start) := by
  let h := p.κ/p.R
  let N := ⌈2*(p.n : ℝ)*p.M/h⌉₊
  have hn : 0 < (p.n : ℝ) := by positivity
  have hh : 0 < h := (step_size p hp).1
  by_contra! hfail
  have hf : Prefit p N := by
    intro j hj
    have hx := hfail j hj.le
    rw [← actual p hp j] at hx
    change ¬ ∀ i, _ at hx
    push Not at hx
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,(margin_eq p hp _ (centered p hp j) i) ▸ hi⟩
  have htime : ∀ j ≤ N, clock p j < p.M := by
    intro j
    induction j with
    | zero =>
      intro _
      change (∑ j ∈ Finset.range 0,_) < _
      simpa using zero_lt_one.trans_le (horizon p hp)
    | succ j ih =>
      intro hj
      have hprev := ih (Nat.le_of_succ_le hj)
      apply before_collision p hp (j+1) (fun k hk => hf k (hk.trans_le hj))
      change (∑ k ∈ Finset.range (j+1),tick p (orbit p k)) ≤ _
      rw [Finset.sum_range_succ]
      change clock p j+tick p (orbit p j) ≤ _
      exact add_le_add hprev.le ((tick_range p hp _).2.trans (step_size p hp).2)
  have hfloor (j : ℕ) (hj : j ∈ Finset.range N) : h*(2*(p.n : ℝ))⁻¹ ≤ tick p (orbit p j) := by
    obtain ⟨i,hi⟩ := hf j (Finset.mem_range.mp hj)
    exact mul_le_mul_of_nonneg_left (BrightnessLogisticVotes.mass_floor _ i hi) hh.le
  have hsum := Finset.sum_le_sum hfloor
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  change N*(h*(2*(p.n : ℝ))⁻¹) ≤ clock p N at hsum
  have hceil : 2*(p.n : ℝ)*p.M ≤ N*h := (div_le_iff₀ hh).mp (Nat.le_ceil _)
  have hN := htime N le_rfl
  have hprice : p.M ≤ N*(h*(2*(p.n : ℝ))⁻¹) := by
    rw [← mul_assoc,← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    linarith
  linarith

end LongTails.Proofs.BrightnessLogisticFirstFit
