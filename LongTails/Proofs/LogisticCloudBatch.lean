import LongTails.Proofs.LogisticCloudModel

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudAverages
open LongTails.Proofs.LogisticCloudModel

namespace LongTails.Proofs.LogisticCloudBatch

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def avgWeight (w : Weights p.d) : ℝ := 𝔼 i, bweight G w i

noncomputable def texture (w : Weights p.d) (f : Fin p.n → Features p.d) :=
  (p.n : ℝ)⁻¹ • ∑ i, bweight G w i • f i

noncomputable def localFeature (w : Weights p.d) (i : Fin p.n) :=
  w (.inl 0) • G.z i + w (.inl 1) • G.y i

noncomputable def hCoeff (η : ℝ) (w : Weights p.d) :=
  η/2*(Real.sigmoid (-score G.e 0 w) - (1+p.μ*p.a)*avgWeight G w)

noncomputable def slowCoeff (η : ℝ) (w : Weights p.d) := η/2*p.μ*avgWeight G w

lemma positive_weight (w : Weights p.d) : 0 < avgWeight G w := by
  rw [avgWeight,Fintype.expect_eq_sum_div_card]
  exact div_pos (Finset.sum_pos (fun _ _ => Real.sigmoid_pos _) Finset.univ_nonempty)
    (by simp)

lemma shifted_texture (w : Weights p.d) (u : Features p.d) (f : Fin p.n → Features p.d) :
    texture G w (fun i => u+f i) = avgWeight G w • u + texture G w f := by
  simp [texture,avgWeight,Fintype.expect_eq_sum_div_card,smul_add,Finset.sum_add_distrib,
    ← Finset.sum_smul,smul_smul,div_eq_inv_mul]

lemma averaged_update (η : ℝ) (w : Weights p.d) :
    let h := hCoeff G η w
    let l := slowCoeff G η w
    let j := Real.sqrt (1-p.a^2)*l
    gradientStep G η w = w + action
      (h • G.e+j • G.u-(η/2) • texture G w G.z)
      (l • G.v-(η/2) • texture G w G.y) w := by
  obtain ⟨C,hC⟩ := action_columns w
  have he : (p.n : ℝ)⁻¹ • ∑ i, bweight G w i • action (zcol G i) (ycol G i) w =
      C (texture G w (zcol G), texture G w (ycol G)) := by
    simp_rw [← hC, ← C.map_smul]
    rw [← map_sum,← C.map_smul]
    apply congrArg C
    ext1
    · simp [texture,Prod.fst_sum]
    · simp [texture,Prod.snd_sum]
  have hz : texture G w (zcol G) = avgWeight G w • (G.e-p.μ • axis G) + texture G w G.z :=
    shifted_texture G w _ _
  have hy : texture G w (ycol G) = avgWeight G w • (-(p.μ • G.v)) + texture G w G.y :=
    shifted_texture G w _ _
  dsimp only
  rw [gradientStep,he,hz,hy,← hC,← hC,← C.map_smul,← map_sub,← C.map_smul]
  congr 1
  apply congrArg C
  ext1 <;> simp [hCoeff,slowCoeff,axis] <;> module

lemma texture_ortho (w : Weights p.d) {b : Features p.d} (hb : b ∈ ({G.e,G.u,G.v} : Set _)) :
    ⟪b,texture G w G.z⟫ = 0 ∧ ⟪b,texture G w G.y⟫ = 0 := by
  have H := G.orthogonal
  simp [texture,inner_sum,real_inner_smul_right,fun i => (H i b hb).1,
    fun i => (H i b hb).2]

lemma texture_read (w : Weights p.d) (f : Fin p.n → Features p.d)
    (hf : ∀ i, ‖f i‖ ≤ 1) (ho : ∀ i, ⟪G.e,f i⟫ = 0 ∧ ⟪G.u,f i⟫ = 0 ∧ ⟪G.v,f i⟫ = 0) :
    |⟪texture G w f,readout w⟫| ≤ avgWeight G w * ‖transverse G w‖ := by
  have he (i : Fin p.n) : ⟪f i,readout w⟫ = ⟪f i,transverse G w⟫ := by
    obtain ⟨h₁,h₂,h₃⟩ := ho i
    rw [decomposition G w]
    simp [inner_add_right,real_inner_smul_right,(real_inner_comm _ _).trans h₁,
      (real_inner_comm _ _).trans h₂,(real_inner_comm _ _).trans h₃]
  have h := weighted_inner_bound (transverse G w) f (bweight G w)
    (fun i => Real.sigmoid_nonneg _) hf
  simp only [texture,real_inner_smul_left,sum_inner,he]
  simpa [avgWeight,Fintype.expect_eq_sum_div_card,div_eq_inv_mul] using h

lemma local_ortho (w : Weights p.d) (i : Fin p.n) :
    ⟪localFeature G w i,readout w⟫ = ⟪localFeature G w i,transverse G w⟫ := by
  have H (b : Features p.d) (hb : b ∈ ({G.e,G.u,G.v} : Set _)) :
      ⟪localFeature G w i,b⟫ = 0 := by
    obtain ⟨hz,hy⟩ := G.orthogonal i b hb
    simp [localFeature,inner_add_left,real_inner_smul_left,(real_inner_comm _ _).trans hz,
      (real_inner_comm _ _).trans hy]
  rw [decomposition G w]
  simp [inner_add_right,real_inner_smul_right,H _ (by simp : G.e ∈ ({G.e,G.u,G.v} : Set _)),
    H _ (by simp : G.u ∈ ({G.e,G.u,G.v} : Set _)),H _ (by simp : G.v ∈ ({G.e,G.u,G.v} : Set _))]

lemma local_centered (w : Weights p.d) : ∑ i, localFeature G w i = 0 := by
  simp [localFeature,Finset.sum_add_distrib,← Finset.smul_sum,G.centered_z,G.centered_y]

lemma local_norm (w : Weights p.d) (i : Fin p.n) : ‖localFeature G w i‖ ≤
    |w (.inl 0)| + |w (.inl 1)| := by
  refine (norm_add_le ..).trans ?_
  simp only [norm_smul,Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_left (G.bound_z i) (abs_nonneg (w (.inl 0))),
    mul_le_mul_of_nonneg_left (G.bound_y i) (abs_nonneg (w (.inl 1)))]

end LongTails.Proofs.LogisticCloudBatch
