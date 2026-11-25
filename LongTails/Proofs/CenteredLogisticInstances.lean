import LongTails.Proofs.CenteredLogisticComparison

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticInstances

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift ones)
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open CenteredLogisticGeometry CenteredLogisticPairs CenteredLogisticComparison
open ClusteredConvolutionalPerceptronInstances TwoSampleQuadraticPerceptronEmbedding

lemma residual_alignment (k : ℕ) (i j : Fin (2 * k + 2)) :
    (1 / 32 : ℝ) ≤ ⟪residual k i,residual k j⟫ := by
  let c := center k
  have hnorm := PiLp.norm_apply_le (center k) (⟨0,by omega⟩ : Fin (2 * k + 4))
  rw [center_coordinate_zero, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hnorm
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 4) hnorm
  have h1 := (abs_real_inner_le_norm (residual k i - c) (residual k j)).trans
    (mul_le_mul (residual_cap k i) (residual_norm k j) (norm_nonneg _) (by norm_num))
  have h2 := (abs_real_inner_le_norm c (residual k j - c)).trans
    (mul_le_mul (center_norm k) (residual_cap k j) (norm_nonneg _) (by norm_num))
  have hl1 := (abs_le.mp h1).1
  have hl2 := (abs_le.mp h2).1
  rw [inner_sub_left] at hl1
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hl2
  change (1 / 4 : ℝ) * (1 / 4) ≤ ‖c‖ * ‖c‖ at hsq
  nlinarith

def multiplicity (k : ℕ) : ℕ+ := ⟨2 * k + 2, by omega⟩

noncomputable def distinctCloud (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ' : μ ≤ 1 / 4096) :
    Geometry (params (2 * k + 4) (multiplicity k))
      (samples (n := multiplicity k) (axis _) (residual k) μ) := by
  apply instanceGeometry (n := multiplicity k) (axis (2 * k + 4)) (residual k) (κ := 1 / 32)
    (ManySampleConvolutionalPerceptronGeometry.axis_norm (by omega))
    (residual_centered k) (residual_norm k) (residual_alignment k) hμ (by linarith)
  rw [ManySampleConvolutionalPerceptronGeometry.shift_axis, sub_self, norm_zero]
  linarith

noncomputable def referencePair {d : ℕ} (j : Fin d) (μ : ℝ) : Data (params d 1) :=
  pair (fun _ => ones d) (fun _ => -(ones d + μ • unitVector j))

noncomputable def referenceGeometry {d : ℕ} (hd : 3 ≤ d) (j : Fin d) {μ : ℝ}
    (hμ : 0 < μ) (hμ' : μ ≤ 1 / 10) : Geometry (params d 1) (referencePair j μ) := by
  let δ := μ / 2
  let u := unitVector j
  let b := ones d + δ • u
  let B := ‖b‖
  let e := B⁻¹ • b
  let g : Fin (1 : ℕ) → Features d := fun _ => -δ • u
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1 / 20 := by dsimp [δ]; linarith
  have huu : ⟪u,u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, unit_norm, one_pow]
  have hou : ⟪ones d,u⟫ = 1 := by simp [u, unitVector, EuclideanSpace.inner_single_right, ones]
  have hB2 : B ^ 2 = d + 2 * δ + δ ^ 2 := by
    change ‖ones d + δ • u‖ ^ 2 = _
    rw [norm_add_sq_real, ← real_inner_self_eq_norm_sq, inner_ones_ones,
      real_inner_smul_right, hou, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, unit_norm]
    ring
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hBn : 0 ≤ B := norm_nonneg _
  have hB : 8 / 5 ≤ B := by nlinarith [sq_nonneg δ]
  have hBp : 0 < B := by linarith
  have he : ‖e‖ = 1 := by
    change ‖B⁻¹ • b‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hBp)]
    exact inv_mul_cancel₀ hBp.ne'
  have heb : B • e = b := by rw [show e = B⁻¹ • b from rfl, smul_smul, mul_inv_cancel₀ hBp.ne', one_smul]
  have hpair : referencePair j μ = pairedData (n := 1) B e g := by
    funext i
    change Fin (1 + 1) at i
    change pair (m := 1) (fun _ => ones d) (fun _ => -(ones d + μ • u)) i =
      (label i * B) • e + duplicate g i
    obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective i
    cases a <;> simp only [label, duplicate, at_pair,
      Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul, neg_smul, heb, b, g, δ] <;> module
  have hbe : ⟪e,u⟫ = (1 + δ) / B := by
    simp only [e, b, real_inner_smul_left, inner_add_left, hou, huu, mul_one, div_eq_inv_mul]
  have hd2 : 2 * (1 + δ) ^ 2 ≤ B ^ 2 := by
    have hδ2 := mul_self_le_mul_self hδ.le hδ'
    nlinarith
  have hcos : ⟪e,u⟫ ^ 2 ≤ 1 / 2 := by
    rw [hbe, div_pow, div_le_iff₀ (sq_pos_of_pos hBp)]
    linarith
  have hdiff : ‖shift e - e‖ ≤ 2 * δ / B := by
    have hx : shift e - e = (B⁻¹ * δ) • (shift u - u) := by
      simp only [e, b, shift_smul, shift_add, shift_ones]
      module
    rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr hBp) hδ)]
    have hn := norm_sub_le (shift u) u
    rw [norm_shift, unit_norm] at hn
    calc _ ≤ B⁻¹ * δ * (1 + 1) := mul_le_mul_of_nonneg_left hn (mul_nonneg (inv_nonneg.mpr hBp.le) hδ.le)
         _ = _ := by ring
  have hsmall : (9 + 17 * ‖shift e - e‖) * δ < B / 2 := by
    have hr : 2 * δ / B ≤ 1 / 16 := (div_le_iff₀ hBp).mpr (by linarith)
    have hbd := mul_le_mul (show 9 + 17 * ‖shift e - e‖ ≤ 9 + 17 / 16 by linarith [hdiff.trans hr])
      hδ' hδ.le (by norm_num : (0 : ℝ) ≤ 9 + 17 / 16)
    linarith
  rw [hpair]
  apply pairGeometry (n := 1) g he hBp hδ (by linarith)
  · intro i
    simp [g, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, u, unit_norm]
  · have hg (i : Fin (1 + 1)) : duplicate g i = -δ • u :=
      bounds_pair (P := fun x => x = -δ • u) g (fun _ => rfl) i
    change ∀ i : Fin (1 + 1), (9 + 17 * ‖shift e - e‖) * δ ^ 3 <
      B * ⟪duplicate g i,(𝔼 j, duplicate g j) - ⟪e,𝔼 j, duplicate g j⟫ • e⟫
    simp_rw [hg, Fintype.expect_const]
    intro i
    simp only [inner_sub_right, real_inner_smul_left, real_inner_smul_right, huu,
      real_inner_comm e u]
    have hproj := mul_le_mul_of_nonneg_right hcos (sq_nonneg δ)
    have hproj' := mul_le_mul_of_nonneg_left hproj hBp.le
    nlinarith [mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hδ)]

end LongTails.Proofs.CenteredLogisticInstances
