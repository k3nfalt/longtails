import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def separatorCone {ι : Type*} (u : ι → E) : Set E :=
  {s | ∀ i, 0 ≤ ⟪s, u i⟫}

omit [CompleteSpace E] in
lemma separatorCone_convex {ι : Type*} (u : ι → E) :
    Convex ℝ (separatorCone u) := by
  intro x hx y hy a b ha hb _ i
  simp only [inner_add_left, inner_smul_left]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

omit [CompleteSpace E] in
lemma separatorCone_closed {ι : Type*} (u : ι → E) :
    IsClosed (separatorCone u) := by
  have he : separatorCone u = ⋂ i, {s : E | 0 ≤ ⟪s, u i⟫} := by
    ext s
    simp [separatorCone]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le continuous_const
    (continuous_id.inner continuous_const)

lemma cone_projection {K : Set E} (hc : Convex ℝ K) (hclosed : IsClosed K)
    (hzero : (0 : E) ∈ K) (hscale : ∀ x ∈ K, (2 : ℝ) • x ∈ K) (u : E) :
    ∃ p ∈ K, ⟪u - p, p⟫ = 0 ∧ (∀ x ∈ K, ⟪u - p, x⟫ ≤ 0) ∧ ‖p‖ ≤ ‖u‖ := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    ⟨0, hzero⟩ hclosed.isComplete hc u
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hc hp).mp hmin
  have hz := hvar 0 hzero
  have htwo := hvar (2 • p) (hscale p hp)
  have horth : ⟪u - p, p⟫ = 0 := by
    simp only [zero_sub, inner_neg_right] at hz
    have he : (2 : ℝ) • p - p = p := by module
    rw [he] at htwo
    linarith
  refine ⟨p, hp, horth, ?_, ?_⟩
  · intro x hx
    have hv := hvar x hx
    rw [inner_sub_right, horth, sub_zero] at hv
    exact hv
  · have hi := real_inner_le_norm u p
    have he : ⟪u, p⟫ = ‖p‖ ^ 2 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
      linarith
    rw [he] at hi
    nlinarith [norm_nonneg p, norm_nonneg u]

omit [CompleteSpace E] in
lemma projection_margin {u p w : E} {κ : ℝ}
    (hw : ‖w‖ = 1) (hmargin : κ ≤ ⟪u, w⟫) (hpolar : ⟪u - p, w⟫ ≤ 0) :
    κ ≤ ‖p‖ := by
  have hi := real_inner_le_norm p w
  rw [hw, mul_one] at hi
  rw [inner_sub_left] at hpolar
  linarith

omit [CompleteSpace E] in
lemma approximate_cone_score {u p w s : E} {δ κ : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hu : ‖u‖ ≤ 1) (hp : ‖p‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) (hpolar : ⟪u - p, s + (δ / κ) • w⟫ ≤ 0) :
    ⟪u, s⟫ ≤ ⟪p, s⟫ + 2 * δ / κ := by
  have hu' := abs_real_inner_le_norm u w
  have hp' := abs_real_inner_le_norm p w
  have hu1 : ‖u‖ * ‖w‖ ≤ 1 := by nlinarith [norm_nonneg u, norm_nonneg w]
  have hp1 : ‖p‖ * ‖w‖ ≤ 1 := by nlinarith [norm_nonneg p, norm_nonneg w]
  have hlu : -1 ≤ ⟪u, w⟫ := by have := (abs_le.mp (hu'.trans hu1)).1; linarith
  have hhp : ⟪p, w⟫ ≤ 1 := (abs_le.mp (hp'.trans hp1)).2
  simp only [inner_add_right, inner_smul_right, inner_sub_left] at hpolar
  have hmul := mul_nonneg (div_nonneg hδ hκ.le) (show 0 ≤ ⟪u, w⟫ - ⟪p, w⟫ + 2 by linarith)
  rw [mul_div_assoc]
  nlinarith

lemma exists_cloud_projection {ι : Type*} (u : ι → E) (i₀ : ι) (w : E) (κ : ℝ)
    (hκ : 0 < κ) (hu : ∀ i, ‖u i‖ ≤ 1) (hw : ‖w‖ = 1)
    (hmargin : ∀ i, κ ≤ ⟪w, u i⟫) :
    ∃ p : E, κ ≤ ‖p‖ ∧ ‖p‖ ≤ 1 ∧ ⟪p, u i₀⟫ = ‖p‖ ^ 2 ∧
      (∀ i, 0 ≤ ⟪p, u i⟫) ∧ (∀ x ∈ separatorCone u, ⟪u i₀ - p, x⟫ ≤ 0) := by
  have hzero : (0 : E) ∈ separatorCone u := by simp [separatorCone]
  have hscale : ∀ x ∈ separatorCone u, (2 : ℝ) • x ∈ separatorCone u := by
    intro x hx i
    simp only [real_inner_smul_left]
    exact mul_nonneg (by norm_num) (hx i)
  obtain ⟨p, hp, ho, hpol, hn⟩ := cone_projection (separatorCone_convex u)
    (separatorCone_closed u) hzero hscale (u i₀)
  have hwm : w ∈ separatorCone u := fun i => hκ.le.trans (hmargin i)
  have hl : κ ≤ ‖p‖ := projection_margin hw
    (by simpa only [real_inner_comm] using hmargin i₀) (hpol w hwm)
  have he : ⟪p, u i₀⟫ = ‖p‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
    have hc := real_inner_comm p (u i₀)
    linarith
  exact ⟨p, hl, hn.trans (hu i₀), he, hp, hpol⟩

omit [CompleteSpace E] in
lemma approximate_cone_membership {ι : Type*} (u : ι → E) (s w : E) (δ κ : ℝ)
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hs : ∀ i, -δ ≤ ⟪s, u i⟫)
    (hw : ∀ i, κ ≤ ⟪w, u i⟫) : s + (δ / κ) • w ∈ separatorCone u := by
  intro i
  simp only [inner_add_left, real_inner_smul_left]
  have hm := mul_le_mul_of_nonneg_left (hw i) (div_nonneg hδ hκ.le)
  have he : δ / κ * κ = δ := div_mul_cancel₀ _ (ne_of_gt hκ)
  linarith [hs i]

omit [CompleteSpace E] in
lemma square_completion (s p : E) (k : ℝ) :
    ‖p‖ ^ 2 * (k ^ 2 / 4 + k / 2) ≤
      ‖s‖ ^ 2 - k * ⟪s, p⟫ + ‖p‖ ^ 2 * k * (k + 1) / 2 := by
  have h := norm_sub_sq_real s ((k / 2) • p)
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  nlinarith [sq_nonneg ‖s - (k / 2) • p‖]

lemma tolerant_norm_count (r k m κ : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (hm : 0 ≤ m)
    (hκ : 0 < κ) (hprogress : κ * m ≤ r)
    (hgrowth : r ^ 2 ≤ 2 * k * r + 2 * m / κ) :
    m ≤ 2 * k / κ + 2 / κ ^ 3 := by
  by_cases hr0 : r = 0
  · have hm0 : m = 0 := by nlinarith
    rw [hm0]
    positivity
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hmul := mul_le_mul_of_nonneg_left hgrowth (sq_nonneg κ)
    have he : κ ^ 2 * (2 * k * r + 2 * m / κ) =
        2 * κ ^ 2 * k * r + 2 * κ * m := by
      field_simp
    rw [he] at hmul
    have hrbound : κ ^ 2 * r ≤ 2 * κ ^ 2 * k + 2 := by nlinarith
    have hmBound : κ ^ 3 * m ≤ 2 * κ ^ 2 * k + 2 := by
      have ht := mul_le_mul_of_nonneg_left hprogress (sq_nonneg κ)
      nlinarith
    have he' : 2 * k / κ + 2 / κ ^ 3 = (2 * κ ^ 2 * k + 2) / κ ^ 3 := by
      field_simp
    rw [he']
    exact (le_div_iff₀ (pow_pos hκ 3)).mpr (by nlinarith)

lemma tolerant_bias_obstruction (κ t C : ℝ) (hκ₁ : κ ≤ 1) (ht : 32 ≤ t)
    (hC : C * κ ^ 4 ≥ t ^ 2 / 4 - 4 * t - 2 * κ) : 1 < C * κ ^ 4 := by
  have ht₂ : 32 * t ≤ t ^ 2 := by nlinarith
  nlinarith

lemma energy_norm_growth (r k m q v z β δ κ E₀ : ℝ)
    (hk : 0 ≤ k) (hkm : k ≤ m) (hq : q ≤ 1) (hv : 0 ≤ v) (hz : z ≤ r)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 6)
    (hE : E₀ ≤ β * m + k * z - v * k * (k + 1) / 2 + k * (q + 2 * δ / κ))
    (haux : r ^ 2 ≤ 2 * (E₀ - β * m) + m * (1 + 2 * δ) - k * (q + 1 + 2 * δ)) :
    r ^ 2 ≤ 2 * k * r + 2 * m / κ := by
  have hm : 0 ≤ m := hk.trans hkm
  have hproj := mul_nonneg hk (sub_nonneg.mpr hz)
  have hq' := mul_nonneg hk (sub_nonneg.mpr hq)
  have hv' : 0 ≤ v * k * (k + 1) := by positivity
  have hδk : 0 ≤ δ * k := mul_nonneg hδ hk
  have hbase : r ^ 2 ≤ 2 * k * r + m * (1 + 2 * δ) + 4 * k * δ / κ := by
    simp only [div_eq_mul_inv] at hE ⊢
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbase hκ.le
  have he : κ * (2 * k * r + m * (1 + 2 * δ) + 4 * k * δ / κ) =
      2 * κ * k * r + κ * m * (1 + 2 * δ) + 4 * k * δ := by
    field_simp
  rw [he] at hmul
  have h1 := mul_le_mul_of_nonneg_right hκ₁ (show 0 ≤ m * (1 + 2 * δ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hkm (show 0 ≤ 4 * δ by positivity)
  have h3 := mul_le_mul_of_nonneg_left hδ₁ (show 0 ≤ 6 * m by positivity)
  have hfinal : κ * r ^ 2 ≤ 2 * κ * k * r + 2 * m := by nlinarith
  apply (mul_le_mul_iff_right₀ hκ).mp
  have he' : κ * (2 * k * r + 2 * m / κ) = 2 * κ * k * r + 2 * m := by
    field_simp
  rw [he']
  nlinarith

lemma total_count_bound (κ k m : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hk : k ≤ 32 / κ ^ 3 + 1) (hm : m ≤ 2 * k / κ + 2 / κ ^ 3) :
    m ≤ 68 / κ ^ 4 := by
  have hκ₂ : κ ^ 2 ≤ 1 := by nlinarith
  have hκ₃ : κ ^ 3 ≤ 1 := by nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hκ₂)]
  have hk' := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 / κ by positivity)
  have hh : 2 / κ * (32 / κ ^ 3 + 1) + 2 / κ ^ 3 =
      (64 + 2 * κ ^ 3 + 2 * κ) / κ ^ 4 := by field_simp; ring
  have hstep : m ≤ (64 + 2 * κ ^ 3 + 2 * κ) / κ ^ 4 := by
    rw [← hh]
    simp only [div_eq_mul_inv] at hm hk' ⊢
    nlinarith
  exact hstep.trans ((div_le_div_iff_of_pos_right (pow_pos hκ 4)).mpr (by nlinarith))

end LongTails.Proofs.CyclicPerceptronCone
