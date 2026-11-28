import LongTails.Proofs.BrightnessLogisticField

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticHorizon

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticConstants BrightnessLogisticField

noncomputable def orbit (p : Params) (k : ℕ) := (BrightnessLogisticModes.step p)^[k] (start p)

noncomputable def clock (p : Params) (k : ℕ) := ∑ j ∈ Finset.range k, tick p (orbit p j)

noncomputable def spending (p : Params) (k : ℕ) :=
  ∑ j ∈ Finset.range k, (beta p (orbit p j))^2*((orbit p j).a^2+(orbit p j).q^2)

def Prefit (p : Params) (k : ℕ) := ∀ j < k, ∃ i, scores p (orbit p j) i ≤ 0

lemma next (p : Params) (k : ℕ) : orbit p (k+1)=BrightnessLogisticModes.step p (orbit p k) :=
  Function.iterate_succ_apply' _ k _

lemma clock_mono (p : Params) (hp : Valid p) : Monotone (clock p) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold clock
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (tick_range p hp _).1

lemma initial_bound (p : Params) (hp : Valid p) :
    size (start p) ≤ 1+3*(p.p₀^2+p.t^2)+p.q₀^2+‖p.w‖^2 := by
  have hR : 0 < p.R := zero_lt_one.trans_le hp.scale
  have hs : |p.t/p.R| ≤ |p.t| := by
    rw [abs_div,abs_of_pos hR,div_le_iff₀ hR]
    nlinarith only [mul_le_mul_of_nonneg_left hp.scale (abs_nonneg p.t)]
  have hsq := mul_self_le_mul_self (abs_nonneg _) hs
  have ht : (p.t/p.R)^2 ≤ p.t^2 := by simpa [← sq,sq_abs] using hsq
  dsimp [size,start,BrightnessLogisticEnergy.energy,BrightnessLogisticEnergy.fast]
  rcases le_total (p.p₀^2) ((p.t/p.R)^2) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith only [ht,sq_nonneg p.p₀]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith only [ht,sq_nonneg p.t,sq_nonneg (p.t/p.R)]

lemma phase_bound (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1) :
    size (orbit p K)+spending p K ≤ p.B := by
  let C := 6*p.L+22*p.J+5*p.J^2
  have hJ := hp.forcePos
  have hL := log_bound p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := BrightnessLogisticFastMode.energy_and_dissipation (fun j => size (orbit p j))
    (fun j => (beta p (orbit p j))^2*((orbit p j).a^2+(orbit p j).q^2))
    (fun j => tick p (orbit p j)) C K hC (zero_le_one.trans (size_one _))
    (fun j => by positivity) (fun j => (tick_range p hp _).1) (by
      intro j hj
      obtain ⟨i,hi⟩ := hf j hj
      rw [next]
      exact energy_step p hp _ i hi)
  apply hs.trans
  change Real.exp (C*clock p K)*size (start p) ≤ _*Real.exp (C*(p.M+1))
  rw [mul_comm (Real.exp _) (size (start p))]
  exact mul_le_mul (initial_bound p hp) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm hC))
    (Real.exp_pos _).le (zero_le_one.trans (initial_energy p hp))

lemma bounds (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1) :
    (∀ j ≤ K, size (orbit p j) ≤ p.B) ∧ spending p K ≤ p.B := by
  constructor
  · intro j hj
    have h := phase_bound p hp j (fun k hk => hf k (lt_of_lt_of_le hk hj)) ((clock_mono p hp hj).trans hm)
    have h0 : 0 ≤ spending p j := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  · linarith [phase_bound p hp K hf hm,size_one (orbit p K)]

end LongTails.Proofs.BrightnessLogisticHorizon
