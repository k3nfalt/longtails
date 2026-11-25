import LongTails.Proofs.FiniteLogisticTwoTapSpectrum
import LongTails.Proofs.FiniteLogisticTwoTapExecution
import LongTails.Proofs.FiniteLogisticTwoTapGeometry

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (ones)
open LongTails.Proofs.FiniteLogisticTwoTapSpectrum
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding (shift_ones)

namespace LongTails.Proofs.FiniteLogisticTwoTapCoordinates

noncomputable def readSum {d : ℕ} (w : Weights d) : ℝ := ∑ k : Fin d, w (.inr k)

structure Coords where
  p : ℝ
  q : ℝ
  u : ℝ
  r : ℝ
  v : ℝ

noncomputable def coords {d : ℕ} (i : Fin d) (w : Weights d) : Coords :=
  let j := finRotate d i
  let V := readSum w
  ⟨(w (.inl 0) + w (.inl 1)) / Real.sqrt 2, V / Real.sqrt d,
    (2*V/d - (w (.inr i) + w (.inr j))) / (Real.sqrt 2 * Real.sqrt (1-2/(d : ℝ))),
    (w (.inl 0) - w (.inl 1)) / Real.sqrt 2, (w (.inr j) - w (.inr i)) / Real.sqrt 2⟩

lemma inner_background {d : ℕ} (w : Weights d) : ⟪liftReadout (ones d), w⟫ = readSum w := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, liftReadout, ones, readSum]

lemma first_action {d : ℕ} (w : Weights d) :
    sampleMatrix (ones d) w =
        readSum w • (EuclideanSpace.single (.inl 0) 1 + EuclideanSpace.single (.inl 1) 1) +
        (w (.inl 0) + w (.inl 1)) • liftReadout (ones d) := by
  simp only [sampleMatrix, shift_ones, add_apply, InnerProductSpace.rankOne_apply, inner_background,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  module

lemma sum_first {d : ℕ} (w : Weights d) :
    readSum (sampleMatrix (ones d) w) = d * (w (.inl 0) + w (.inl 1)) := by
  rw [first_action]
  simp [readSum, liftReadout, ones, mul_add]

lemma sum_defect {d : ℕ} (i : Fin d) (w : Weights d) :
    readSum (sampleMatrix (EuclideanSpace.single i 1) w) = w (.inl 0) + w (.inl 1) := by
  rw [defect_action]
  simp [readSum, Finset.sum_add_distrib]

lemma coords_first {d : ℕ} (hd : 0 < d) (i : Fin d) (w : Weights d) :
    let c := coords i w
    coords i (sampleMatrix (ones d) w) =
      ⟨Real.sqrt 2 * Real.sqrt d * c.q, Real.sqrt 2 * Real.sqrt d * c.p, 0, 0, 0⟩ := by
  have h₂ := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have hD := Real.sq_sqrt (Nat.cast_nonneg d)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := Real.sqrt_pos.mpr hd'
  dsimp only [coords]
  rw [sum_first, first_action]
  simp [liftReadout, ones]
  field_simp [hs.ne', hd'.ne']
  ring_nf
  simp [hD, h₂, mul_comm]

lemma coords_defect {d : ℕ} (hd : 2 < d) (i : Fin d) (hi : finRotate d i ≠ i) (w : Weights d) :
    let c := coords i w
    let a := Real.sqrt 2 / Real.sqrt d
    let b := Real.sqrt (1 - 2 / (d : ℝ))
    coords i (sampleMatrix (EuclideanSpace.single i 1) w) =
      ⟨a * c.q - b * c.u, a * c.p, -b * c.p, -c.v, -c.r⟩ := by
  have hd' : (2 : ℝ) < d := by exact_mod_cast hd
  have hD₀ : (0 : ℝ) < d := by linarith
  have hD := Real.sq_sqrt hD₀.le
  have hs := Real.sqrt_pos.mpr hD₀
  have he : 0 < 1 - 2 / (d : ℝ) := sub_pos.mpr ((div_lt_one hD₀).mpr hd')
  have hb := Real.sqrt_pos.mpr he
  have hβ := Real.sq_sqrt he.le
  have h₂ := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  dsimp only [coords]
  rw [sum_defect, defect_action]
  simp [-finRotate_apply, hi, Ne.symm hi]
  generalize hB : Real.sqrt (1 - 2 / (d : ℝ)) = B at hb hβ ⊢
  have hβ' : (d : ℝ) * B^2 = d - 2 := by
    rw [hβ]
    field_simp
  field_simp [hs.ne', hb.ne', hD₀.ne']
  ring_nf
  simp [hD, h₂]
  grind

lemma score_coordinates {d : ℕ} (hd : 2 < d) (i : Fin d) (μ : ℝ) (w : Weights d) :
    let c := coords i w
    let L := Real.sqrt 2 * Real.sqrt d
    (answer (signedInput μ i false) w).margin = L*c.p*c.q ∧
      (answer (signedInput μ i true) w).margin =
        -(L+μ*(Real.sqrt 2/Real.sqrt d))*c.p*c.q +
        μ*Real.sqrt (1-2/(d : ℝ))*c.p*c.u + μ*c.r*c.v := by
  have hd' : (2 : ℝ) < d := by exact_mod_cast hd
  have hD₀ : (0 : ℝ) < d := by linarith
  have hs := Real.sqrt_pos.mpr hD₀
  have he : 0 < 1 - 2 / (d : ℝ) := sub_pos.mpr ((div_lt_one hD₀).mpr hd')
  have hb := Real.sqrt_pos.mpr he
  have h₂ := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have hD := Real.sq_sqrt hD₀.le
  have hfirst : (answer (signedInput μ i false) w).margin =
      (w (.inl 0) + w (.inl 1)) * readSum w := by
    change (answer (ones d) w).margin = _
    rw [FiniteLogisticTwoTapGeometry.first_layer_score, shift_ones, inner_background, add_mul]
  have H := congrArg (fun M : Weights d →L[ℝ] Weights d => ⟪M w,w⟫ / 2) (sum_matrices μ i)
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left, add_div] at H
  have hlocal : ⟪sampleMatrix (EuclideanSpace.single i 1) w,w⟫ / 2 =
      w (.inl 0)*w (.inr i) + w (.inl 1)*w (.inr (finRotate d i)) := by
    rw [defect_action]
    simp [inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left]
    ring
  change (answer (signedInput μ i false) w).margin + (answer (signedInput μ i true) w).margin =
    _ at H
  rw [hfirst, mul_div_assoc, hlocal] at H
  dsimp only [coords]
  rw [hfirst]
  generalize hB : Real.sqrt (1 - 2 / (d : ℝ)) = B at hb ⊢
  constructor
  · field_simp
  · field_simp [hs.ne', hb.ne', hD₀.ne']
    grind

lemma coords_euler {d : ℕ} (i : Fin d) (w x y : Weights d) (s t : ℝ) :
    let c := coords i w
    let a := coords i x
    let b := coords i y
    coords i (w + s • x + t • y) = ⟨c.p + s*a.p + t*b.p, c.q + s*a.q + t*b.q,
      c.u + s*a.u + t*b.u, c.r + s*a.r + t*b.r, c.v + s*a.v + t*b.v⟩ := by
  simp [coords, readSum, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

lemma raw_step {d : ℕ} (μ η : ℝ) (i : Fin d) (w : Weights d) :
    let a := Real.sigmoid (-(answer (signedInput μ i false) w).margin)
    let b := Real.sigmoid (-(answer (signedInput μ i true) w).margin)
    FiniteLogisticTwoTapExecution.step μ η i w =
      w + (η/2*(a-b)) • (sampleMatrix (ones d) w) +
        (-(η/2*μ*b)) • (sampleMatrix (EuclideanSpace.single i 1) w) := by
  intro a b
  have HS := congrArg (fun M : Weights d →L[ℝ] Weights d => M w) (sum_matrices μ i)
  simp only [add_apply, smul_apply] at HS
  have H : sampleMatrix (signedInput μ i true) w =
      (-μ) • sampleMatrix (EuclideanSpace.single i 1) w - sampleMatrix (ones d) w := by
    change sampleMatrix (ones d) w + _ = _ at HS
    rw [← HS]
    abel
  change w + (η / 2) • (a • sampleMatrix (ones d) w + b • sampleMatrix (signedInput μ i true) w) = _
  rw [H]
  module

lemma step_coordinates {d : ℕ} (hd : 2 < d) (i : Fin d) (hi : finRotate d i ≠ i)
    (μ η : ℝ) (w : Weights d) :
    let c := coords i w
    let a := Real.sigmoid (-(answer (signedInput μ i false) w).margin)
    let b := Real.sigmoid (-(answer (signedInput μ i true) w).margin)
    let h := η / 2 * ((Real.sqrt 2 * Real.sqrt d) * (a-b) - μ * (Real.sqrt 2 / Real.sqrt d) * b)
    let j := η / 2 * μ * Real.sqrt (1-2/(d : ℝ)) * b
    let l := η / 2 * μ * b
    coords i (FiniteLogisticTwoTapExecution.step μ η i w) =
      ⟨c.p+h*c.q+j*c.u, c.q+h*c.p, c.u+j*c.p, c.r+l*c.v, c.v+l*c.r⟩ := by
  rw [raw_step, coords_euler, coords_first (by omega), coords_defect hd i hi]
  simp only [Coords.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

end LongTails.Proofs.FiniteLogisticTwoTapCoordinates
