import LongTails.Algorithms.ComparisonOrth

open scoped RealInnerProductSpace

namespace OracleTemplate.ComparisonOrth

variable {n : ℕ}

def UnitOrZero (u : Pt n) : Prop := u = 0 ∨ ‖u‖ = 1

structure Frame (u1 u2 u3 : Pt n) : Prop where
  h1 : UnitOrZero u1
  h2 : UnitOrZero u2
  h3 : UnitOrZero u3
  o12 : ⟪u1, u2⟫ = 0
  o13 : ⟪u1, u3⟫ = 0
  o23 : ⟪u2, u3⟫ = 0

noncomputable def proj3 (u1 u2 u3 v : Pt n) : Pt n :=
  ⟪v, u1⟫ • u1 + ⟪v, u2⟫ • u2 + ⟪v, u3⟫ • u3

def InSpan (u1 u2 u3 v : Pt n) : Prop := proj3 u1 u2 u3 v = v

lemma UnitOrZero.inner_mul_self {u : Pt n} (hu : UnitOrZero u) (v : Pt n) :
    ⟪v, u⟫ * ⟪u, u⟫ = ⟪v, u⟫ := by
  rcases hu with h | h
  · subst h; simp
  · rw [real_inner_self_eq_norm_sq, h]; ring

lemma UnitOrZero.smul_self {u : Pt n} (hu : UnitOrZero u) (c : ℝ) : (c * ⟪u, u⟫) • u = c • u := by
  rcases hu with h | h
  · subst h; simp
  · rw [real_inner_self_eq_norm_sq, h]; ring_nf

lemma UnitOrZero.norm_le {u : Pt n} (hu : UnitOrZero u) : ‖u‖ ≤ 1 := by
  rcases hu with h | h
  · subst h; simp
  · rw [h]

lemma unitOrZero_nrm (v : Pt n) : UnitOrZero (nrm v) := by
  by_cases hv : v = 0
  · left; simp [nrm, hv]
  · right
    rw [nrm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma nrm_decomp (v : Pt n) : v = ‖v‖ • nrm v := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [nrm, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

lemma inner_nrm_left (v w : Pt n) : ⟪nrm v, w⟫ = ‖v‖⁻¹ * ⟪v, w⟫ := by
  rw [nrm, inner_smul_left]; rfl

lemma nrm_smul_pos (v : Pt n) {c : ℝ} (hc : 0 < c) : nrm (c • v) = nrm v := by
  simp only [nrm, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_inv, smul_smul]
  congr 1
  field_simp

section FrameLemmas

variable {u1 u2 u3 : Pt n} (F : Frame u1 u2 u3)
include F

lemma Frame.o21 : ⟪u2, u1⟫ = 0 := by rw [real_inner_comm]; exact F.o12

lemma Frame.o31 : ⟪u3, u1⟫ = 0 := by rw [real_inner_comm]; exact F.o13

lemma Frame.o32 : ⟪u3, u2⟫ = 0 := by rw [real_inner_comm]; exact F.o23

lemma Frame.inner_proj_u1 (v : Pt n) : ⟪proj3 u1 u2 u3 v, u1⟫ = ⟪v, u1⟫ := by
  simp only [proj3, inner_add_left, inner_smul_left, RCLike.conj_to_real, F.o21, F.o31,
    mul_zero, add_zero]
  exact F.h1.inner_mul_self v

lemma Frame.inner_proj_u2 (v : Pt n) : ⟪proj3 u1 u2 u3 v, u2⟫ = ⟪v, u2⟫ := by
  simp only [proj3, inner_add_left, inner_smul_left, RCLike.conj_to_real, F.o12, F.o32,
    mul_zero, add_zero, zero_add]
  exact F.h2.inner_mul_self v

lemma Frame.inner_proj_u3 (v : Pt n) : ⟪proj3 u1 u2 u3 v, u3⟫ = ⟪v, u3⟫ := by
  simp only [proj3, inner_add_left, inner_smul_left, RCLike.conj_to_real, F.o13, F.o23,
    mul_zero, zero_add]
  exact F.h3.inner_mul_self v

omit F in
lemma inner_proj_comm (v w : Pt n) :
    ⟪proj3 u1 u2 u3 v, w⟫ = ⟪v, proj3 u1 u2 u3 w⟫ := by
  simp only [proj3, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm u1 w, real_inner_comm u2 w, real_inner_comm u3 w]
  ring

lemma Frame.inSpan_comb (a b c : ℝ) : InSpan u1 u2 u3 (a • u1 + b • u2 + c • u3) := by
  unfold InSpan proj3
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, F.o12, F.o13, F.o23,
    F.o21, F.o31, F.o32, mul_zero, add_zero, zero_add]
  rw [F.h1.smul_self, F.h2.smul_self, F.h3.smul_self]

omit F in
lemma inner_projOut_of_inSpan (v w : Pt n) (hw : InSpan u1 u2 u3 w) :
    ⟪v - proj3 u1 u2 u3 v, w⟫ = 0 := by
  rw [inner_sub_left, inner_proj_comm, hw, sub_self]

omit F in
lemma inSpan_add {v w : Pt n} (hv : InSpan u1 u2 u3 v) (hw : InSpan u1 u2 u3 w) :
    InSpan u1 u2 u3 (v + w) := by
  unfold InSpan at *
  conv_rhs => rw [← hv, ← hw]
  simp only [proj3, inner_add_left, add_smul]
  abel

omit F in
lemma inSpan_smul {v : Pt n} (hv : InSpan u1 u2 u3 v) (c : ℝ) : InSpan u1 u2 u3 (c • v) := by
  unfold InSpan at *
  conv_rhs => rw [← hv]
  simp only [proj3, inner_smul_left, RCLike.conj_to_real, smul_add, smul_smul]

omit F in
lemma inSpan_sub {v w : Pt n} (hv : InSpan u1 u2 u3 v) (hw : InSpan u1 u2 u3 w) :
    InSpan u1 u2 u3 (v - w) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ w]
  exact inSpan_add hv (inSpan_smul hw (-1))

lemma Frame.inner_projOut_u1 (v : Pt n) : ⟪v - proj3 u1 u2 u3 v, u1⟫ = 0 := by
  rw [inner_sub_left, F.inner_proj_u1, sub_self]

lemma Frame.inner_projOut_u2 (v : Pt n) : ⟪v - proj3 u1 u2 u3 v, u2⟫ = 0 := by
  rw [inner_sub_left, F.inner_proj_u2, sub_self]

lemma Frame.inner_projOut_u3 (v : Pt n) : ⟪v - proj3 u1 u2 u3 v, u3⟫ = 0 := by
  rw [inner_sub_left, F.inner_proj_u3, sub_self]

lemma Frame.norm_comb_sq (a b c : ℝ) :
    ‖a • u1 + b • u2 + c • u3‖ ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, F.o12, F.o13, F.o23, F.o21, F.o31, F.o32, mul_zero, add_zero, zero_add]
  have h1 : ⟪u1, u1⟫ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]; nlinarith [F.h1.norm_le, norm_nonneg u1]
  have h2 : ⟪u2, u2⟫ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]; nlinarith [F.h2.norm_le, norm_nonneg u2]
  have h3 : ⟪u3, u3⟫ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]; nlinarith [F.h3.norm_le, norm_nonneg u3]
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

lemma Frame.norm_projOut_le (v : Pt n) : ‖v - proj3 u1 u2 u3 v‖ ≤ ‖v‖ := by
  have hspan : InSpan u1 u2 u3 (proj3 u1 u2 u3 v) := F.inSpan_comb _ _ _
  have horth := inner_projOut_of_inSpan v _ hspan
  have hsq : ‖v‖ ^ 2 = ‖v - proj3 u1 u2 u3 v‖ ^ 2 + ‖proj3 u1 u2 u3 v‖ ^ 2 := by
    have := norm_add_sq_real (v - proj3 u1 u2 u3 v) (proj3 u1 u2 u3 v)
    rw [sub_add_cancel, horth] at this
    linarith
  nlinarith [norm_nonneg v, norm_nonneg (v - proj3 u1 u2 u3 v),
    sq_nonneg ‖proj3 u1 u2 u3 v‖]

omit F in
lemma abs_inner_le_of_unitOrZero {u : Pt n} (hu : UnitOrZero u) (v : Pt n) :
    |⟪v, u⟫| ≤ ‖v‖ :=
  (abs_real_inner_le_norm v u).trans (by nlinarith [hu.norm_le, norm_nonneg v, norm_nonneg u])

end FrameLemmas

end OracleTemplate.ComparisonOrth
