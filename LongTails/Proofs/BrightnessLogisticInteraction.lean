import LongTails.Proofs.BrightnessLogisticForces

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean vote)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticInteraction

open BrightnessLogisticModes BrightnessLogisticForces BrightnessLogisticRawDynamics

lemma support_force {d : ℕ} {n : ℕ+} (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i)
    (X : Fin n → Features d) (v : Features d) {a : ℝ} (h : ∀ i, a ≤ ⟪v,X i⟫) :
    a*mean g ≤ ⟪v,force g X⟫ := by
  rw [real_inner_comm,force_inner,← mean_scale]
  apply mean_mono
  intro i
  rw [← real_inner_comm (X i) v,mul_comm a]
  exact mul_le_mul_of_nonneg_left (h i) (hg i)

lemma cross_force {d : ℕ} {n : ℕ+} (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i)
    (X : Fin n → Features d) (v : Features d) {a : ℝ} (h : ∀ i, |⟪v,X i⟫| ≤ a) :
    |⟪v,force g X⟫| ≤ a*mean g := by
  have hlow := support_force g hg X v (fun i => (abs_le.mp (h i)).1)
  have hu := support_force g hg X (-v) (a := -a) (fun i => by
    rw [inner_neg_left]; exact neg_le_neg (abs_le.mp (h i)).2)
  rw [inner_neg_left] at hu
  rw [abs_le]
  constructor <;> linarith

lemma cross_prefix {d : ℕ} {n : ℕ+} (g : ℕ → Fin n → ℝ) (B A : Fin n → Features d)
    (v : ℕ → Features d) (p : ℕ → ℝ) {h S χ : ℝ} (hh : 0 ≤ h) (K : ℕ)
    (hg : ∀ k i, 0 ≤ g k i) (hs : ∀ k < K, |p k| ≤ S)
    (hv : ∀ k, v (k+1)=v k+h • (p k • force (g k) B))
    (hcross : ∀ i j, |⟪A i,B j⟫| ≤ χ) (hstart : ∀ i, 0 ≤ ⟪v 0,A i⟫) (i : Fin n) :
    -(χ*S*(∑ k ∈ Finset.range K, h*mean (g k))) ≤ ⟪v K,A i⟫ := by
  induction K with
  | zero => simpa using hstart i
  | succ k ih =>
    have hprev := ih (fun j hj => hs j (Nat.lt_succ_of_lt hj))
    have hb := cross_force (g k) (hg k) B (A i) (hcross i)
    rw [← real_inner_comm (A i) _] at hb
    have hS := (abs_nonneg _).trans (hs k (Nat.lt_succ_self _))
    have hh' := mul_le_mul (hs k (Nat.lt_succ_self _)) hb (abs_nonneg _) hS
    rw [← abs_mul] at hh'
    have hlow := neg_abs_le (p k*⟪force (g k) B,A i⟫)
    rw [hv,inner_add_left,real_inner_smul_left,real_inner_smul_left,Finset.sum_range_succ]
    nlinarith only [hprev,mul_le_mul_of_nonneg_left (show -(S*(χ*mean (g k))) ≤
      p k*⟪force (g k) B,A i⟫ by linarith only [hlow,hh']) hh]

lemma balance (q h : ℝ) (w b A : Features d) :
    let qs := q+h*⟪A,w+b⟫
    let ws := w+h • (q • A)
    qs^2-‖ws‖^2-(q^2-‖w‖^2) =
      2*h*q*⟪b,A⟫+h^2*(⟪A,w+b⟫^2-q^2*‖A‖^2) := by
  dsimp only
  rw [norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_right,inner_add_right,
    real_inner_comm A w,real_inner_comm A b]
  ring

end LongTails.Proofs.BrightnessLogisticInteraction
