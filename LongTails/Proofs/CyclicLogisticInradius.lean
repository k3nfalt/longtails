import LongTails.Proofs.CyclicLogisticGroups

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicLogisticInradius

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def axes (e f : E) : Fin 6 → E := ![e,e,-e,f,f,-f]

lemma inradius (e f : E) {r : ℝ} (hr : 0 < r) (he : r ≤ ‖e‖) (hf : r ≤ ‖f‖)
    (hef : ⟪e,f⟫ = 0) (v : E) (hv : v ∈ Submodule.span ℝ (Set.range (axes e f))) :
    ∃ i, ⟪axes e f i,v⟫ ≤ -(r / 2) * ‖v‖ := by
  have rep : ∃ a b : ℝ, v = a • e + b • f := by
    induction hv using Submodule.span_induction with
    | mem x h =>
      obtain ⟨i,rfl⟩ := h
      fin_cases i
      · exact ⟨1,0,by simp [axes]⟩
      · exact ⟨1,0,by simp [axes]⟩
      · exact ⟨-1,0,by simp [axes]⟩
      · exact ⟨0,1,by simp [axes]⟩
      · exact ⟨0,1,by simp [axes]⟩
      · exact ⟨0,-1,by simp [axes]⟩
    | zero => exact ⟨0,0,by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a,b,rfl⟩ := hx
      obtain ⟨c,d,rfl⟩ := hy
      exact ⟨a+c,b+d,by simp only [add_smul]; abel⟩
    | smul c x _ hx =>
      obtain ⟨a,b,rfl⟩ := hx
      exact ⟨c*a,c*b,by rw [smul_add, smul_smul, smul_smul]⟩
  obtain ⟨a,b,hab⟩ := rep
  have hfe : ⟪f,e⟫ = 0 := (real_inner_comm ..).trans hef
  have hae : |⟪e,v⟫| = ‖a • e‖ * ‖e‖ := by
    simp [hab, inner_add_right, real_inner_smul_right, hef,
      abs_mul, norm_smul, sq, Real.norm_eq_abs]
    ring
  have hbf : |⟪f,v⟫| = ‖b • f‖ * ‖f‖ := by
    simp [hab, inner_add_right, real_inner_smul_right, hfe,
      abs_mul, norm_smul, sq, Real.norm_eq_abs]
    ring
  by_contra! bad
  have h₁ := bad 0
  have h₂ := bad 2
  have h₃ := bad 3
  have h₄ := bad 5
  simp [axes, inner_neg_left] at h₁ h₂ h₃ h₄
  have hA : |⟪e,v⟫| < r / 2 * ‖v‖ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hB : |⟪f,v⟫| < r / 2 * ‖v‖ := abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [hae] at hA
  rw [hbf] at hB
  have hv' : ‖v‖ ≤ ‖a • e‖ + ‖b • f‖ := hab ▸ norm_add_le _ _
  nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg (a • e)),
    mul_le_mul_of_nonneg_left hf (norm_nonneg (b • f)), mul_le_mul_of_nonneg_right hv' hr.le]

end LongTails.Proofs.CyclicLogisticInradius
