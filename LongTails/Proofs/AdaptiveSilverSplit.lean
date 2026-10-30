import Mathlib.Analysis.InnerProductSpace.Spectrum
import LongTails.Proofs.AdaptiveSilverScalar

namespace LongTails.Proofs.AdaptiveSilverSplit

open scoped RealInnerProductSpace
open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.AdaptiveSilverScalar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma eq_of_coords (b : OrthonormalBasis ι ℝ E) {u v : E} (h : ∀ j, ⟪b j, u⟫ = ⟪b j, v⟫) :
    u = v :=
  b.repr.injective (by ext j; simp [OrthonormalBasis.repr_apply_apply, h j])

lemma inner_coords (b : OrthonormalBasis ι ℝ E) (u v : E) :
    ⟪u, v⟫ = ∑ i, ⟪b i, u⟫ * ⟪b i, v⟫ := by
  rw [← b.sum_inner_mul_inner u v]
  exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_comm u (b i)])

lemma norm_sq_coords (b : OrthonormalBasis ι ℝ E) (u : E) :
    ‖u‖ ^ 2 = ∑ i, ⟪b i, u⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords b]
  exact Finset.sum_congr rfl (fun i _ => by ring)

variable [DecidableEq ι]

noncomputable def proj (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) : E →L[ℝ] E :=
  ∑ i, c i • (innerSL ℝ (b i)).smulRight (b i)

omit [DecidableEq ι] in
lemma proj_apply (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (v : E) :
    proj b c v = ∑ i, (c i * ⟪b i, v⟫) • b i := by
  simp [proj, smul_smul]

lemma proj_coord (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ) (v : E) (j : ι) :
    ⟪b j, proj b c v⟫ = c j * ⟪b j, v⟫ := by
  rw [proj_apply, inner_sum]
  simp_rw [inner_smul_right, b.inner_eq_ite]
  simp

noncomputable def cpos (eig : ι → ℝ) (j : ι) : ℝ := if 0 ≤ eig j then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
lemma cpos_sq (eig : ι → ℝ) (j : ι) : cpos eig j * cpos eig j = cpos eig j := by
  by_cases h : 0 ≤ eig j <;> simp [cpos, h]

omit [Fintype ι] [DecidableEq ι] in
lemma cpos_nonneg (eig : ι → ℝ) (j : ι) : 0 ≤ cpos eig j := by
  by_cases h : 0 ≤ eig j <;> simp [cpos, h]

omit [Fintype ι] [DecidableEq ι] in
lemma cpos_le_one (eig : ι → ℝ) (j : ι) : cpos eig j ≤ 1 := by
  by_cases h : 0 ≤ eig j <;> simp [cpos, h]

omit [Fintype ι] [DecidableEq ι] in
lemma eig_cpos_nonneg (eig : ι → ℝ) (j : ι) : 0 ≤ eig j * cpos eig j := by
  by_cases h : 0 ≤ eig j <;> simp [cpos, h]

omit [Fintype ι] [DecidableEq ι] in
lemma eig_cneg_nonpos (eig : ι → ℝ) (j : ι) : eig j * (1 - cpos eig j) ≤ 0 := by
  by_cases h : 0 ≤ eig j
  · simp [cpos, h]
  · simp only [cpos, h, ↓reduceIte, sub_zero, mul_one]
    linarith [not_le.mp h]

section Spectral

variable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
  (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)

noncomputable def P : E →L[ℝ] E := proj b (cpos eig)

include hc

omit hc in
lemma P_coord' (v : E) (j : ι) : ⟪b j, P b eig v⟫ = cpos eig j * ⟪b j, v⟫ :=
  proj_coord b _ v j

omit hc in
lemma P_idem (v : E) : P b eig (P b eig v) = P b eig v := by
  apply eq_of_coords b
  intro j
  rw [P_coord', P_coord', ← mul_assoc, cpos_sq]

omit hc in
lemma P_symm (u v : E) : ⟪P b eig u, v⟫ = ⟪u, P b eig v⟫ := by
  rw [inner_coords b, inner_coords b u]
  exact Finset.sum_congr rfl (fun i _ => by rw [P_coord', P_coord']; ring)

lemma P_comm (v : E) : H (P b eig v) = P b eig (H v) := by
  apply eq_of_coords b
  intro j
  rw [hc, P_coord', P_coord', hc]
  ring

omit hc in
lemma P_norm_le (v : E) : ‖P b eig v‖ ≤ ‖v‖ := by
  have h : ‖P b eig v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_coords b, norm_sq_coords b v]
    apply Finset.sum_le_sum
    intro i _
    rw [P_coord', mul_pow]
    have h0 := cpos_nonneg eig i
    have h1 := cpos_le_one eig i
    have : cpos eig i ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ⟪b i, v⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit hc in
lemma Q_norm_le (v : E) : ‖v - P b eig v‖ ≤ ‖v‖ := by
  have h : ‖v - P b eig v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_coords b, norm_sq_coords b v]
    apply Finset.sum_le_sum
    intro i _
    rw [inner_sub_right, P_coord']
    have h0 := cpos_nonneg eig i
    have h1 := cpos_le_one eig i
    have : (⟪b i, v⟫ - cpos eig i * ⟪b i, v⟫) ^ 2 = (1 - cpos eig i) ^ 2 * ⟪b i, v⟫ ^ 2 := by
      ring
    rw [this]
    have : (1 - cpos eig i) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ⟪b i, v⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma pos_part (v : E) : 0 ≤ ⟪P b eig v, H (P b eig v)⟫ := by
  rw [inner_coords b]
  apply Finset.sum_nonneg
  intro i _
  rw [hc, P_coord']
  have h := eig_cpos_nonneg eig i
  have h2 := cpos_sq eig i
  have : cpos eig i * ⟪b i, v⟫ * (eig i * (cpos eig i * ⟪b i, v⟫)) =
      eig i * cpos eig i * ⟪b i, v⟫ ^ 2 := by
    rw [show cpos eig i * ⟪b i, v⟫ * (eig i * (cpos eig i * ⟪b i, v⟫)) =
      eig i * (cpos eig i * cpos eig i) * ⟪b i, v⟫ ^ 2 by ring, h2]
  rw [this]
  exact mul_nonneg h (sq_nonneg _)

lemma neg_part (w : E) (hw : P b eig w = 0) : ⟪w, H w⟫ ≤ 0 := by
  rw [inner_coords b]
  apply Finset.sum_nonpos
  intro i _
  have hz : cpos eig i * ⟪b i, w⟫ = 0 := by
    rw [← P_coord', hw, inner_zero_right]
  rw [hc]
  have h := eig_cneg_nonpos eig i
  have : ⟪b i, w⟫ * (eig i * ⟪b i, w⟫) = eig i * (1 - cpos eig i) * ⟪b i, w⟫ ^ 2 := by
    have : eig i * (1 - cpos eig i) * ⟪b i, w⟫ ^ 2 =
        eig i * ⟪b i, w⟫ ^ 2 - eig i * ⟪b i, w⟫ * (cpos eig i * ⟪b i, w⟫) := by ring
    rw [this, hz]
    ring
  rw [this]
  exact mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)

lemma cross_zero (v w : E) (hw : P b eig w = 0) : ⟪P b eig v, H w⟫ = 0 := by
  rw [P_symm, ← P_comm b eig H hc, hw, map_zero, inner_zero_right]

omit [DecidableEq ι] in
lemma eig_le_norm (j : ι) : |eig j| ≤ ‖H‖ := by
  have h1 := hc j (b j)
  rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j, one_pow, mul_one] at h1
  rw [← h1]
  calc |⟪b j, H (b j)⟫| ≤ ‖b j‖ * ‖H (b j)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖b j‖ * (‖H‖ * ‖b j‖) := by gcongr; exact H.le_opNorm _
    _ = ‖H‖ := by rw [b.orthonormal.1 j]; ring

noncomputable def lin (L : ℝ) (hs : List ℝ) (u : E) : E := run (fun v => (1 / L) • H v) hs u

omit [DecidableEq ι] in
lemma lin_coord (L : ℝ) (hs : List ℝ) (u : E) (j : ι) :
    ⟪b j, lin H L hs u⟫ = pr (eig j / L) hs * ⟪b j, u⟫ := by
  induction hs generalizing u with
  | nil => simp [lin, run, pr_nil]
  | cons h t ih =>
    simp only [lin, run] at ih ⊢
    rw [ih, pr_cons, inner_sub_right, inner_smul_right, inner_smul_right, hc]
    ring

lemma lin_P (L : ℝ) (hs : List ℝ) (u : E) : P b eig (lin H L hs u) = lin H L hs (P b eig u) := by
  apply eq_of_coords b
  intro j
  rw [P_coord', lin_coord b eig H hc, lin_coord b eig H hc, P_coord']
  ring

omit [DecidableEq ι] in
lemma lin_sub (L : ℝ) (hs : List ℝ) (u v : E) :
    lin H L hs (u - v) = lin H L hs u - lin H L hs v := by
  apply eq_of_coords b
  intro j
  rw [inner_sub_right, lin_coord b eig H hc, lin_coord b eig H hc, lin_coord b eig H hc,
    inner_sub_right]
  ring

omit [DecidableEq ι] in
lemma lin_smul (L : ℝ) (hs : List ℝ) (a : ℝ) (u : E) :
    lin H L hs (a • u) = a • lin H L hs u := by
  apply eq_of_coords b
  intro j
  rw [inner_smul_right, lin_coord b eig H hc, lin_coord b eig H hc, inner_smul_right]
  ring

lemma lin_bound (L : ℝ) (hs : List ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : ∀ j, 0 ≤ eig j → |pr (eig j / L) hs| ≤ W) (u : E) :
    ‖lin H L hs (P b eig u)‖ ≤ W * ‖P b eig u‖ := by
  have h : ‖lin H L hs (P b eig u)‖ ^ 2 ≤ (W * ‖P b eig u‖) ^ 2 := by
    rw [mul_pow, norm_sq_coords b, norm_sq_coords b (P b eig u), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [lin_coord b eig H hc, P_coord', mul_pow]
    by_cases hi : 0 ≤ eig i
    · have h1 := hb i hi
      have h2 : pr (eig i / L) hs ^ 2 ≤ W ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [sq_nonneg (cpos eig i * ⟪b i, u⟫)]
    · simp [cpos, hi]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

end Spectral

end LongTails.Proofs.AdaptiveSilverSplit
