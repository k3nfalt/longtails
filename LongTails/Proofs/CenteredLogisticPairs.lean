import LongTails.Proofs.CenteredLogisticGeometry
import LongTails.Proofs.TwoSidedPerceptronLinearComparison

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticPairs

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open CenteredLogisticGeometry

abbrev params (d : ℕ) (n : ℕ+) : Params := ⟨d, ⟨(n : ℕ) + n, add_pos n.pos n.pos⟩⟩

def pair {m : ℕ} {α : Type*} (f g : Fin m → α) (i : Fin (m + m)) : α :=
  Sum.elim f g (finSumFinEquiv.symm i)

def label {m : ℕ} : Fin (m + m) → ℝ := pair (fun _ => 1) (fun _ => -1)

def duplicate {m : ℕ} {α : Type*} (f : Fin m → α) := pair f f

lemma at_pair {m : ℕ} {α : Type*} (f g : Fin m → α) (i : Fin m ⊕ Fin m) :
    pair f g (finSumFinEquiv i) = Sum.elim f g i := by simp [pair]

lemma label_abs {m : ℕ} (i : Fin (m + m)) : |label i| = 1 := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [label, at_pair, Sum.elim_inl, Sum.elim_inr, abs_neg, abs_one]

lemma label_sq {m : ℕ} (i : Fin (m + m)) : label i * label i = 1 := by
  nlinarith [label_abs i, sq_abs (label i)]

lemma cancellation {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℚ≥0 E] (f : Fin m → E) :
    (𝔼 i, pair f (-f) i) = 0 := by
  rw [Finset.expect_univ, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [at_pair, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Finset.sum_neg_distrib,
    add_neg_cancel, smul_zero]

lemma label_balance (m : ℕ) : (𝔼 i : Fin (m + m), label i) = 0 :=
  cancellation (fun _ : Fin m => (1 : ℝ))

lemma centered_pair {m d : ℕ} (f : Fin m → Features d) :
    (𝔼 i, label i • duplicate f i) = 0 := by
  rw [← cancellation f]
  apply Finset.expect_congr rfl
  intro i _
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [label, duplicate, at_pair, Sum.elim_inl, Sum.elim_inr, one_smul,
    neg_smul, Pi.neg_apply]

lemma bounds_pair {m : ℕ} {α : Type*} {P : α → Prop} (f : Fin m → α)
    (h : ∀ j, P (f j)) (i : Fin (m + m)) : P (duplicate f i) := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simpa only [duplicate, at_pair, Sum.elim_inl, Sum.elim_inr] using h _

noncomputable def pairedData {n : ℕ+} {d : ℕ} (B : ℝ) (e : Features d)
    (g : Fin n → Features d) : Data (params d n) :=
  fun i => (label i * B) • e + duplicate g i

noncomputable def pairGeometry {n : ℕ+} {d : ℕ} {B δ : ℝ} {e : Features d}
    (g : Fin n → Features d) (he : ‖e‖ = 1) (hB : 0 < B) (hδ : 0 < δ)
    (hsize : 32 * δ ≤ B) (hg : ∀ j, ‖g j‖ ≤ δ)
    (hgap : let m := 𝔼 i, duplicate g i
      ∀ i, (9 + 17 * ‖shift e - e‖) * δ ^ 3 < B * ⟪duplicate g i, m - ⟪e,m⟫ • e⟫) :
    Geometry (params d n) (pairedData B e g) := by
  let R := Real.sqrt (B ^ 2 + (𝔼 i, ‖duplicate g i‖ ^ 2))
  have hvar : 0 ≤ 𝔼 i, ‖duplicate g i‖ ^ 2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 < R := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos hB) hvar)
  have hR2 : R ^ 2 = B ^ 2 + (𝔼 i, ‖duplicate g i‖ ^ 2) := Real.sq_sqrt ((sq_nonneg _).trans (le_add_of_nonneg_right hvar))
  have hBR : B ≤ R := by nlinarith
  let h := fun i => R⁻¹ • (label i • duplicate g i)
  have hnorm i : ‖h i‖ = ‖duplicate g i‖ / R := by
    simp [h, norm_smul, Real.norm_eq_abs, label_abs, abs_of_pos hR, div_eq_inv_mul]
  have hm : (𝔼 i, label i • h i) = R⁻¹ • (𝔼 i, duplicate g i) := by
    rw [Finset.smul_expect]
    apply Finset.expect_congr rfl
    intro i _
    dsimp [h]
    rw [smul_comm (label i) R⁻¹, smul_smul (label i) (label i), label_sq, one_smul]
  have hfull : (𝔼 i, label i • ((B / R) • e + h i)) = 𝔼 i, label i • h i := by
    simp only [smul_add, Finset.expect_add_distrib, mean_varying_smul, label_balance,
      zero_smul, zero_add]
  refine ⟨R, δ / R, B / R, e, h, label, hR, div_pos hδ hR, (div_le_iff₀ hR).2 (by linarith),
    he, label_abs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ‖𝔼 i : Fin ((n : ℕ) + n), label i • ((B / R) • e + h i)‖ ≤ δ / R
    rw [hfull]
    apply mean_norm_le
    intro i
    rw [norm_smul, Real.norm_eq_abs, label_abs, one_mul, hnorm]
    exact div_le_div_of_nonneg_right (bounds_pair (P := fun x => ‖x‖ ≤ δ) g hg i) hR.le
  · change (B / R) ^ 2 + (𝔼 i : Fin ((n : ℕ) + n), ‖h i‖ ^ 2) = 1
    simp_rw [hnorm, div_pow, ← Finset.expect_div]
    rw [← add_div, ← hR2, div_self (pow_ne_zero _ hR.ne')]
  · exact (Finset.smul_expect R⁻¹ _ _).symm.trans
      ((congrArg (R⁻¹ • ·) (centered_pair g)).trans (smul_zero _))
  · intro i
    change Fin ((n : ℕ) + n) at i
    rw [hnorm i]
    exact div_le_div_of_nonneg_right (bounds_pair (P := fun x => ‖x‖ ≤ δ) g hg i) hR.le
  · intro i
    change Fin ((n : ℕ) + n) at i
    change (label i * B) • e + duplicate g i = (label i * R) • ((B / R) • e + h i)
    rw [smul_add, smul_smul]
    dsimp only [h]
    rw [smul_smul, smul_smul, show (label i * R) * (B / R) = label i * B by field_simp,
      show (label i * R * R⁻¹) * label i = 1 by rw [mul_inv_cancel_right₀ hR.ne', label_sq],
      one_smul]
  · change ∀ i : Fin ((n : ℕ) + n), (9 + 17 * ‖shift e - e‖) * (δ / R) ^ 3 < label i *
      ⟪h i, (𝔼 j, label j • ((B / R) • e + h j)) - ⟪e, 𝔼 j, label j • ((B / R) • e + h j)⟫ • e⟫
    rw [hfull, hm]
    intro i
    have hi := hgap i
    have hinner : 0 < ⟪duplicate g i,
        (𝔼 j, duplicate g j) - ⟪e, 𝔼 j, duplicate g j⟫ • e⟫ := by
      by_contra! hnon
      have hpos : 0 < (9 + 17 * ‖shift e - e‖) * δ ^ 3 := by positivity
      linarith [mul_nonpos_of_nonneg_of_nonpos hB.le hnon]
    have ht : R⁻¹ • (𝔼 j, duplicate g j) - ⟪e, R⁻¹ • (𝔼 j, duplicate g j)⟫ • e =
        R⁻¹ • ((𝔼 j, duplicate g j) - ⟪e, 𝔼 j, duplicate g j⟫ • e) := by
      rw [real_inner_smul_right, smul_sub, smul_smul]
    rw [ht]
    simp only [h, real_inner_smul_left, real_inner_smul_right]
    have hsign := label_sq i
    have hmul := mul_le_mul_of_nonneg_right hBR hinner.le
    field_simp
    rw [show label i ^ 2 = 1 by simpa only [sq] using hsign, mul_one]
    exact hi.trans_le hmul

end LongTails.Proofs.CenteredLogisticPairs
