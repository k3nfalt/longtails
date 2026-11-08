import LongTails.Proofs.BirchNonEuclideanEnergy

namespace LongTails.Proofs.BirchResourceGeometry

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open OracleTemplate.NormBallLMO
open LongTails.Setups.BirchNonEuclidean

noncomputable def axial {d : ℕ} (i : Fin d) : Seminorm ℝ (Point d) :=
  normSeminorm ℝ (Point d) + (normSeminorm ℝ ℝ).comp (EuclideanSpace.projₗ i)

lemma axial_apply {d : ℕ} (i : Fin d) (x : Point d) : axial i x = ‖x‖ + |x i| := rfl

lemma axial_distortion {d : ℕ} (i : Fin d) (x : Point d) :
    ‖x‖ ≤ axial i x ∧ axial i x ≤ 2 * ‖x‖ := by
  rw [axial_apply]
  have h : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  exact ⟨by linarith [abs_nonneg (x i)], by linarith⟩

lemma axial_continuous {d : ℕ} (i : Fin d) : Continuous (axial i) := by
  have h : Continuous (fun x : Point d => x i) := (EuclideanSpace.proj i : Point d →L[ℝ] ℝ).continuous
  exact continuous_norm.add h.abs

lemma axial_definite {d : ℕ} (i : Fin d) (x : Point d) (hx : axial i x = 0) : x = 0 :=
  norm_eq_zero.mp (le_antisymm ((axial_distortion i x).1.trans_eq hx) (norm_nonneg _))

lemma axial_dual {d : ℕ} (i : Fin d) (v : Point d) :
    ‖v‖ / 2 ≤ dualNorm (axial i) v ∧ dualNorm (axial i) v ≤ ‖v‖ := by
  have hR : ∀ x, axial i x ≤ 1 → ‖x‖ ≤ 1 := fun x hx => (axial_distortion i x).1.trans hx
  refine ⟨?_, by simpa using dualNorm_le_norm hR v⟩
  by_cases hv : v = 0
  · subst v
    simpa using dualNorm_nonneg hR (0 : Point d)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : Point d := (2 * ‖v‖)⁻¹ • v
  have hnorm : ‖u‖ = 1 / 2 := by
    rw [show u = (2 * ‖v‖)⁻¹ • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (2 * ‖v‖)⁻¹)]
    field_simp
  have hu : axial i u ≤ 1 := (axial_distortion i u).2.trans_eq (by rw [hnorm]; norm_num)
  have hinner : inner ℝ v u = ‖v‖ / 2 := by
    rw [show u = (2 * ‖v‖)⁻¹ • v from rfl, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  simpa only [hinner] using inner_le_dualNorm hR v hu

lemma axial_regular {d : ℕ} (i : Fin d) : DualRegular (axial i) 4 := by
  refine ⟨⟨normSeminorm ℝ (Point d), 1, id, fun x hx => norm_eq_zero.mp (show ‖x‖ = 0 from hx), continuous_norm,
    le_rfl, by norm_num, continuous_id, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro z
      simp [InnerProductSpace.toDual_apply_apply]
  · intro x y
    change (1 / 2 : ℝ) * ‖x + y‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 + inner ℝ x y + 1 / 2 * ‖y‖ ^ 2
    rw [norm_add_sq_real]
    linarith
  · intro v
    exact (sq_le_sq₀ (dualNorm_nonneg (fun x hx => (axial_distortion i x).1.trans hx) v)
      (norm_nonneg v)).2 (axial_dual i v).2
  · intro v
    change ‖v‖ ^ 2 ≤ 4 / 1 * dualNorm (axial i) v ^ 2
    have hv := (axial_dual i v).1
    have h0 := norm_nonneg v
    have hd : 0 ≤ dualNorm (axial i) v := by linarith
    nlinarith only [mul_nonneg (show 0 ≤ 2 * dualNorm (axial i) v - ‖v‖ by linarith)
      (show 0 ≤ 2 * dualNorm (axial i) v + ‖v‖ by positivity)]

lemma inner_coordinate {d : ℕ} (v : Point d) (j : Fin d) :
    inner ℝ v (EuclideanSpace.single j (1 : ℝ)) = v j := by
  rw [EuclideanSpace.inner_single_right, one_mul]
  rfl

lemma axial_sharp_support {d : ℕ} (i j : Fin d) (lmo : Point d → Point d)
    (hlmo : IsBallLMO (axial i) 1 lmo) (v : Point d) (hv : v j = 0) :
    (dualNorm (axial i) v • lmo v) j = 0 := by
  by_cases hz : v = 0
  · subst v
    have hd : dualNorm (axial i) (0 : Point d) = 0 := by
      have h := axial_dual i (0 : Point d)
      rw [norm_zero, zero_div] at h
      exact le_antisymm h.2 h.1
    simp [hd]
  let w := lmo v
  suffices h : w j = 0 by
    change dualNorm (axial i) v * w j = 0
    rw [h, mul_zero]
  by_contra hw
  let e := EuclideanSpace.single j (1 : ℝ)
  let z := w - w j • e
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have hd : 0 < dualNorm (axial i) v := (div_pos hn (by norm_num)).trans_le (axial_dual i v).1
  have hinner : inner ℝ v w < 0 := by
    have hR : ∀ x, axial i x ≤ 1 → ‖x‖ ≤ 1 := fun x hx => (axial_distortion i x).1.trans hx
    change inner ℝ v (lmo v) < 0
    rw [lmo_dualNorm_eq hR (by norm_num) hlmo, one_mul]
    exact neg_neg_of_pos hd
  have hzinner : inner ℝ v z = inner ℝ v w := by
    unfold z e
    rw [inner_sub_right, inner_smul_right, inner_coordinate, hv, mul_zero, sub_zero]
  have hzn : 0 < axial i z := by
    by_contra! h
    have hzero := axial_definite i z (le_antisymm h (apply_nonneg _ _))
    rw [hzero, inner_zero_right] at hzinner
    linarith only [hzinner, hinner]
  have hnorm : ‖z‖ < ‖w‖ := by
    have he : ‖e‖ = 1 := by simp [e]
    have hsq : ‖z‖ ^ 2 = ‖w‖ ^ 2 - (w j) ^ 2 := by
      unfold z
      rw [norm_sub_sq_real, inner_smul_right, show inner ℝ w e = w j from inner_coordinate w j,
        norm_smul, he, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have hlt : ‖z‖ ^ 2 < ‖w‖ ^ 2 := by rw [hsq]; linarith [sq_pos_of_ne_zero hw]
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hlt
  have hcoord : |z i| ≤ |w i| := by
    by_cases h : i = j
    · subst i
      change |w j - w j * e j| ≤ |w j|
      simp [e]
    · change |w i - w j * e i| ≤ |w i|
      simp [e, h]
  have hlt : axial i z < 1 :=
    (by simpa only [axial_apply] using add_lt_add_of_lt_of_le hnorm hcoord :
      axial i z < axial i w).trans_le (hlmo.feasible v)
  let u := (axial i z)⁻¹ • z
  have hu : axial i u ≤ 1 := by
    unfold u
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzn), inv_mul_cancel₀ hzn.ne']
  have hbad := hlmo.minimal v u hu
  change inner ℝ v w ≤ inner ℝ v ((axial i z)⁻¹ • z) at hbad
  rw [inner_smul_right, hzinner] at hbad
  have hlarge : (1 : ℝ) < (axial i z)⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hzn).2 (by simpa only [one_mul] using hlt)
  have hneg := mul_lt_mul_of_neg_right hlarge hinner
  linarith only [hbad, hneg]

end LongTails.Proofs.BirchResourceGeometry
