import LongTails.Proofs.SymmetricReverseFisherDynamics
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherAlignment
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherGradient
lemma aligned_gradient {p : Params} (e : Space p) {a u : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    gradient (loss (a • e)) (u • e) = alignedForce a u • e := by
  rw [gradient_loss, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, he, mul_one,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, he, mul_one,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  norm_num only [one_pow, mul_one]
  rw [alignedForce, ← radialFirst_eq_force, radialFirst_eq_alpha, radialForce_eq_ridgeForce]
  rw [mul_comm u a]
  module
lemma alignedForce_abs_bound {p : Params} (e : Space p) {a u : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    |alignedForce a u| ≤ (48 + 20 * a) * |u - a| := by
  have h := gradient_loss_lipschitz (a • e) (u • e) (a • e)
  rw [aligned_gradient e he ha hu, aligned_gradient e he ha ha, alignedForce_self,
    zero_smul, sub_zero, norm_smul, Real.norm_eq_abs, he, mul_one,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, he, mul_one,
    ← sub_smul, norm_smul, Real.norm_eq_abs, he, mul_one] at h
  exact h
lemma positive_secant {D x κ L : ℝ} (_hκ : 0 ≤ κ) (hκL : κ ≤ L)
    (hlo : κ * x ^ 2 ≤ x * D) (hhi : |D| ≤ L * |x|)
    (hz : x = 0 → D = 0) : ∃ b ∈ Set.Icc κ L, D = b * x := by
  by_cases hx : x = 0
  · exact ⟨κ, ⟨le_rfl, hκL⟩, by rw [hz hx, hx, mul_zero]⟩
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have he : D / x * x = D := div_mul_cancel₀ _ hx
  have hb : κ ≤ D / x := by
    have hex := congrArg (fun t : ℝ => t * x) he
    by_contra hn
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hx2
    nlinarith
  have hu : D / x ≤ L := by
    have hab : |D / x| ≤ L := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr hx)).mpr hhi
    exact (le_abs_self _).trans hab
  exact ⟨D / x, ⟨hb, hu⟩, he.symm⟩
lemma aligned_coercivity_coefficient {a u q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hqa : q ≤ a) (hu : q / 8 ≤ u) :
    q ^ 2 / 960 ≤ min u 1 * min (u + a) 1 / 120 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : q / 8 ≤ min u 1 := le_min hu (by linarith)
  have h2 : q ≤ min (u + a) 1 := le_min (by linarith) hq1
  have hm := mul_le_mul h1 h2 hq (show 0 ≤ min u 1 by positivity)
  nlinarith
lemma aligned_secant {p : Params} (e : Space p) {a u q : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hu0 : 0 < u)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hqa : q ≤ a) (hu : q / 8 ≤ u) :
    ∃ b ∈ Set.Icc (q ^ 2 / 960) (48 + 20 * a), alignedForce a u = b * (u - a) := by
  apply positive_secant (by positivity) (by nlinarith [sq_nonneg (q - 1)])
  · have hc := alignedForce_coercive ha hu0
    have hl := mul_le_mul_of_nonneg_right
      (aligned_coercivity_coefficient hq hq1 hqa hu) (sq_nonneg (u - a))
    exact hl.trans hc
  · exact alignedForce_abs_bound e he ha hu0.le
  · intro h
    have hua : u = a := by linarith
    rw [hua, alignedForce_self]
lemma projected_gradient_perturbation {p : Params} (e v : Space p) {a u : ℝ}
    (he : ‖e‖ = 1) (ha : 0 ≤ a) (hu : 0 ≤ u) (hv : ⟪v, e⟫ = 0) :
    |⟪gradient (loss (a • e)) (u • e + v), e⟫ - alignedForce a u| ≤ 48 * ‖v‖ := by
  have hg := radial_gradient_lipschitz (u • e + v) (u • e)
  have hn : ‖u • e‖ = u := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, he, mul_one]
  have hdiff : u • e + v - u • e = v := by abel
  rw [hdiff] at hg
  have hid : ⟪gradient (loss (a • e)) (u • e + v), e⟫ - alignedForce a u =
      ⟪alpha ‖u • e + v‖ • (u • e + v) - alpha ‖u • e‖ • (u • e), e⟫ := by
    rw [gradient_loss, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, he, mul_one,
      coordinate_inner e v u a he hv, alignedForce, ← radialFirst_eq_force,
      radialFirst_eq_alpha, radialForce_eq_ridgeForce]
    simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he,
      inner_add_left, hv, hn, one_pow, mul_one, add_zero]
    ring
  rw [hid]
  exact (abs_real_inner_le_norm _ e).trans (by simpa [he] using hg)
lemma perturbed_aligned_contraction {u a κ L η D G E : ℝ}
    (hκ : 0 ≤ κ) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hquot : ∃ t ∈ Set.Icc κ L, D = t * (u - a)) (herror : |G - D| ≤ E) :
    |u - η * G - a| ≤ (1 - η * κ) * |u - a| + η * E := by
  have hc := LongTails.Proofs.SymmetricReverseFisherGeometry.aligned_contraction
    u a κ L η D hκ hη hηL hquot
  have he : u - η * G - a = (u - η * D - a) + η * (D - G) := by ring
  rw [he]
  calc
    _ ≤ |u - η * D - a| + |η * (D - G)| := abs_add_le _ _
    _ = |u - η * D - a| + η * |G - D| := by rw [abs_mul, abs_of_nonneg hη, abs_sub_comm D G]
    _ ≤ _ := add_le_add hc (mul_le_mul_of_nonneg_left herror hη)
end LongTails.Proofs.SymmetricReverseFisherAlignment
