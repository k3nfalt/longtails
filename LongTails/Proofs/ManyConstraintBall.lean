import LongTails.Proofs.ManyConstraintCoupling

open Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManyConstraintBall

open LongTails.Proofs.ManyConstraintCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def projBall (x0 : E) (ρ : ℝ) (w : E) : E :=
  if ‖w - x0‖ ≤ ρ then w else x0 + (ρ / ‖w - x0‖) • (w - x0)

lemma projBall_mem {x0 : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (w : E) : projBall x0 ρ w ∈ closedBall x0 ρ := by
  rw [mem_closedBall, dist_eq_norm]
  unfold projBall
  split_ifs with h
  · exact h
  · push Not at h
    have hpos : 0 < ‖w - x0‖ := lt_of_le_of_lt hρ h
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hpos.ne']

lemma projBall_min {x0 : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (w : E) {v : E} (hv : v ∈ closedBall x0 ρ) :
    ‖projBall x0 ρ w - w‖ ≤ ‖v - w‖ := by
  rw [mem_closedBall, dist_eq_norm] at hv
  unfold projBall
  split_ifs with h
  · simp
  · push Not at h
    have hpos : 0 < ‖w - x0‖ := lt_of_le_of_lt hρ h
    have hd : x0 + (ρ / ‖w - x0‖) • (w - x0) - w = ((ρ / ‖w - x0‖) - 1) • (w - x0) := by
      module
    rw [hd, norm_smul, Real.norm_eq_abs]
    have hlt : ρ / ‖w - x0‖ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hpos]; exact h.le
    rw [abs_of_nonpos hlt]
    have htri : ‖w - x0‖ ≤ ‖v - w‖ + ‖v - x0‖ := by
      calc ‖w - x0‖ = ‖(v - x0) - (v - w)‖ := by congr 1; abel
        _ ≤ ‖v - x0‖ + ‖v - w‖ := norm_sub_le _ _
        _ = _ := by ring
    have : -(ρ / ‖w - x0‖ - 1) * ‖w - x0‖ = ‖w - x0‖ - ρ := by
      field_simp; ring
    linarith

noncomputable def reg (μ : ℝ) (x0 x : E) : ℝ := μ / 2 * ‖x - x0‖ ^ 2

lemma reg_strong (μ : ℝ) (x0 : E) (K : Set E) (hK : Convex ℝ K) :
    StrongConvexOn K μ (reg μ x0) := by
  refine ⟨hK, fun x _ y _ a b ha hb hab => ?_⟩
  have hx : a • x + b • y - x0 = a • (x - x0) + b • (y - x0) := by
    calc a • x + b • y - x0 = a • (x - x0) + b • (y - x0) + (a + b - 1) • x0 := by module
      _ = _ := by rw [hab]; simp
  have hnorm : ‖a • (x - x0) + b • (y - x0)‖ ^ 2 =
      a * ‖x - x0‖ ^ 2 + b * ‖y - x0‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
    have hxy : x - y = (x - x0) - (y - x0) := by abel
    rw [hxy, norm_add_sq_real, norm_sub_sq_real (x - x0) (y - x0), norm_smul, norm_smul,
      real_inner_smul_left, inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hb]
    obtain rfl := eq_sub_of_add_eq hab
    ring
  simp only [reg, smul_eq_mul, hx, hnorm]
  nlinarith [sq_nonneg ‖x - y‖]

noncomputable def center (μ : ℝ) (x0 : E) (a : ℝ) (z g : E) : E :=
  (1 / (1 / a + μ)) • ((1 / a) • z - g + μ • x0)

noncomputable def proxBall (μ : ℝ) (x0 : E) (ρ a : ℝ) (z g : E) : E :=
  projBall x0 ρ (center μ x0 a z g)

lemma proxObj_diff {μ a : ℝ} (ha : 0 < a) (hμ : 0 ≤ μ) (x0 z g v : E) :
    proxObj (reg μ x0) a z g v - proxObj (reg μ x0) a z g (center μ x0 a z g) =
      (1 / a + μ) / 2 * ‖v - center μ x0 a z g‖ ^ 2 := by
  set c := center μ x0 a z g with hc
  have hk : 0 < 1 / a + μ := by positivity
  have hcen : (1 / a + μ) • c = (1 / a) • z - g + μ • x0 := by
    rw [hc, center, smul_smul, mul_one_div_cancel hk.ne', one_smul]
  have e1 : ∀ w : E, ‖v - w‖ ^ 2 = ‖v - c‖ ^ 2 + 2 * ⟪v - c, c - w⟫ + ‖c - w‖ ^ 2 := by
    intro w
    have : v - w = (v - c) + (c - w) := by abel
    rw [this, norm_add_sq_real]
  simp only [proxObj, reg]
  rw [e1 z, e1 x0]
  have hlin : ⟪g, v - z⟫ - ⟪g, c - z⟫ = ⟪g, v - c⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  have hkey : (1 / a) * ⟪v - c, c - z⟫ + μ * ⟪v - c, c - x0⟫ + ⟪g, v - c⟫ = 0 := by
    have : (1 / a) • (c - z) + μ • (c - x0) + g = 0 := by
      have h2 : (1 / a) • (c - z) + μ • (c - x0) + g = (1 / a + μ) • c - ((1 / a) • z - g + μ • x0) := by
        module
      rw [h2, hcen, sub_self]
    have := congrArg (fun w => ⟪v - c, w⟫) this
    simp only [inner_add_right, inner_smul_right, inner_zero_right] at this
    rw [real_inner_comm g (v - c)] at this; linarith
  linear_combination hkey + hlin

lemma proxBall_mem {μ : ℝ} {x0 : E} {ρ a : ℝ} (hρ : 0 ≤ ρ) (z g : E) :
    proxBall μ x0 ρ a z g ∈ closedBall x0 ρ := projBall_mem hρ _

lemma proxBall_min {μ : ℝ} {x0 : E} {ρ a : ℝ} (ha : 0 < a) (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (z g : E) :
    IsMinOn (proxObj (reg μ x0) a z g) (closedBall x0 ρ) (proxBall μ x0 ρ a z g) := by
  intro v hv
  change proxObj (reg μ x0) a z g (proxBall μ x0 ρ a z g) ≤ proxObj (reg μ x0) a z g v
  have h1 := proxObj_diff ha hμ x0 z g v
  have h2 := proxObj_diff ha hμ x0 z g (proxBall μ x0 ρ a z g)
  have hm := projBall_min hρ (center μ x0 a z g) hv
  have hk : 0 ≤ (1 / a + μ) / 2 := by positivity
  have hsq : ‖proxBall μ x0 ρ a z g - center μ x0 a z g‖ ^ 2 ≤ ‖v - center μ x0 a z g‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hm 2
  nlinarith [mul_le_mul_of_nonneg_left hsq hk]

end LongTails.Proofs.ManyConstraintBall
