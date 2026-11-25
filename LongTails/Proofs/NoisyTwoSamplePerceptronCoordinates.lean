import LongTails.Proofs.NoisyTwoSamplePerceptronExecution
import LongTails.Proofs.NoisyTwoSamplePerceptronComplement
import LongTails.Proofs.FiniteLogisticTwoTapEntry

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap (Weights signedInput answer sampleMatrix)
open LongTails.Setups.TwoSampleQuadraticPerceptron (ones)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.FiniteLogisticTwoTapSpectrum
open LongTails.Proofs.NoisyTwoSamplePerceptronComplement
open LongTails.Proofs.NoisyTwoSamplePerceptronExecution

namespace LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates

noncomputable def proj (z : Coords) : E := vec z.p z.q z.u ((z.r-z.v)/Real.sqrt 2)

noncomputable def gamma (d : ℕ) := 1/(4*Real.sqrt d)

lemma slow_coords {d : ℕ} (i : Fin d) (x : Weights d) :
    slowProjection i x = -((coords i x).r+(coords i x).v)/Real.sqrt 2 := by
  dsimp [slowProjection,coords]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

lemma defect_all {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i) (w : Weights d) :
    let z := coords i w
    let a := Real.sqrt 2 / Real.sqrt d
    let B := Real.sqrt (1-2/(d:ℝ))
    coords i (sampleMatrix (EuclideanSpace.single i 1) w) =
      ⟨a*z.q-B*z.u,a*z.p,-B*z.p,-z.v,-z.r⟩ := by
  rcases eq_or_lt_of_le hd with h|h
  · subst d
    dsimp only [coords]
    rw [sum_defect,defect_action]
    obtain rfl|rfl : i=0 ∨ i=1 := by fin_cases i <;> decide
    all_goals norm_num [readSum,Fin.sum_univ_two]
    · rw [show finRotate 2 0 = 1 by decide]
      and_intros <;> ring
    · rw [show finRotate 2 1 = 0 by decide]
      and_intros <;> ring
  · exact coords_defect h i hi w

lemma scores_all {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (μ : ℝ) (w : Weights d) :
    let z := coords i w
    let L := Real.sqrt 2*Real.sqrt d
    (answer (signedInput μ i false) w).margin = L*z.p*z.q ∧
    (answer (signedInput μ i true) w).margin = -(L+μ*(Real.sqrt 2/Real.sqrt d))*z.p*z.q +
      μ*Real.sqrt (1-2/(d:ℝ))*z.p*z.u+μ*z.r*z.v := by
  rcases eq_or_lt_of_le hd with h|h
  · subst d
    have H : (sampleMatrix (signedInput μ i true) w) =
        (-μ) • sampleMatrix (EuclideanSpace.single i 1) w - sampleMatrix (ones 2) w := by
      have K := congrArg (fun M : Weights 2 →L[ℝ] Weights 2 => M w) (sum_matrices μ i)
      simp only [add_apply,smul_apply] at K
      change sampleMatrix (ones 2) w + _ = _ at K
      rw [← K]; abel
    dsimp only [answer,coords]
    rw [H]
    change ⟪sampleMatrix (ones 2) w,w⟫ / 2 = _ ∧ _
    rw [first_action,defect_action]
    simp [inner_sub_left,inner_add_left,real_inner_smul_left,inner_background,
      EuclideanSpace.inner_single_left,readSum,Fin.sum_univ_two]
    fin_cases i <;> norm_num <;> and_intros <;> field_simp <;> ring_nf <;> norm_num <;> ring
  · exact score_coordinates h i μ w

lemma direction_first {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (μ : ℝ) (x : Weights d) :
    let z := coords i x
    gamma d • proj (coords i ((answer (signedInput μ i false) x).direction)) =
      matrix (gamma d*μ) (Real.sqrt 2/Real.sqrt d) (Real.sqrt (1-2/(d:ℝ))) false (proj z) := by
  dsimp only [answer]
  change gamma d • proj (coords i (sampleMatrix (ones d) x)) = _
  rw [coords_first (by omega)]
  have hD : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  ext k
  fin_cases k <;> simp [matrix,action,proj,vec,c,gamma]
  all_goals field_simp

lemma direction_second {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i)
    (μ : ℝ) (x : Weights d) :
    let z := coords i x
    gamma d • proj (coords i ((answer (signedInput μ i true) x).direction)) =
      matrix (gamma d*μ) (Real.sqrt 2/Real.sqrt d) (Real.sqrt (1-2/(d:ℝ))) true (proj z) := by
  have H := congrArg (fun M : Weights d →L[ℝ] Weights d => M x) (sum_matrices μ i)
  simp only [add_apply,smul_apply] at H
  change sampleMatrix (ones d) x + _ = _ at H
  have hh : (answer (signedInput μ i true) x).direction =
      0 + (-μ) • sampleMatrix (EuclideanSpace.single i 1) x + (-1:ℝ) • sampleMatrix (ones d) x := by
    change sampleMatrix (signedInput μ i true) x = _
    rw [← H]
    simp
  have hD : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hf := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  rw [hh,coords_euler,defect_all hd i hi,coords_first (by omega)]
  have hz : coords i (0:Weights d) = ⟨0,0,0,0,0⟩ := by simp [coords,readSum]
  rw [hz]
  ext k
  fin_cases k <;> simp [matrix,action,proj,vec,c,gamma] <;> field_simp <;> ring

lemma proj_move {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i)
    (μ σ : ℝ) (x g : Weights d) (b : Bool) :
    let R := proj (coords i x)
    proj (coords i (move μ (gamma d) σ i x g b)) =
      R + matrix (gamma d*μ) (Real.sqrt 2/Real.sqrt d) (Real.sqrt (1-2/(d:ℝ))) b R +
        σ • proj (coords i g) := by
  have H : gamma d • proj (coords i ((answer (signedInput μ i b) x).direction)) =
      matrix (gamma d*μ) (Real.sqrt 2/Real.sqrt d) (Real.sqrt (1-2/(d:ℝ))) b (proj (coords i x)) := by
    cases b with
    | false => exact direction_first hd i μ x
    | true => exact direction_second hd i hi μ x
  dsimp only
  rw [← H]
  dsimp only [move]
  rw [coords_euler]
  ext k
  fin_cases k <;> simp [proj,vec]
  ring

lemma score_split {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (μ : ℝ) (x : Weights d) (b : Bool) :
    let z := proj (coords i x)
    let m := matrix (gamma d*μ) (Real.sqrt 2/Real.sqrt d) (Real.sqrt (1-2/(d:ℝ))) b
    2*gamma d*(answer (signedInput μ i b) x).margin =
      ⟪m z,z⟫+(if b then gamma d*μ*(slowProjection i x)^2 else 0) := by
  obtain ⟨h₁,h₂⟩ := scores_all hd i μ x
  have hD : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hf := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  rw [slow_coords]
  cases b <;> simp [h₁,h₂,matrix,action,inner_eq,proj,vec,c,gamma] <;> field_simp <;> ring_nf
  all_goals simp [hf]
  ring

end LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
