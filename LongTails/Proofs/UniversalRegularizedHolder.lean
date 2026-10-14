import LongTails.Proofs.UniversalRegularizedConvergence

open scoped RealInnerProductSpace

namespace OracleTemplate.HolderMonotone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma continuous_of_holder {F : E → E} {L H α : ℝ} (hα0 : 0 < α)
    (hhol : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖ + H * ‖x - y‖ ^ α) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  have hb : Filter.Tendsto (fun y : E => L * ‖y - x‖ + H * ‖y - x‖ ^ α) (nhds x) (nhds 0) := by
    have h1 : Continuous fun y : E => ‖y - x‖ := by fun_prop
    have hc : Continuous fun y : E => L * ‖y - x‖ + H * ‖y - x‖ ^ α :=
      (continuous_const.mul h1).add
        (continuous_const.mul (h1.rpow_const fun _ => Or.inr hα0.le))
    have := hc.tendsto x
    simpa [Real.zero_rpow hα0.ne'] using this
  have hn : Filter.Tendsto (fun y : E => ‖F y - F x‖) (nhds x) (nhds 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun y => hhol y x) hb
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma holder_scale {H α ε : ℝ} (hH : 0 < H) (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε)
    {d : ℝ} (hd : 0 ≤ d) :
    H * d ^ α ≤ ε / (8 * (ε / (8 * H)) ^ (1 / α)) * max d ((ε / (8 * H)) ^ (1 / α)) := by
  have hbase : 0 < ε / (8 * H) := by positivity
  set r := (ε / (8 * H)) ^ (1 / α) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hbase _
  have hrα : r ^ α = ε / (8 * H) := by
    rw [hr, ← Real.rpow_mul hbase.le, one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one]
  have hHr : H * r ^ α = ε / 8 := by
    rw [hrα]
    field_simp
  rcases le_total r d with hle | hle
  · rw [max_eq_left hle]
    have hdpos : 0 < d := lt_of_lt_of_le hrpos hle
    have e1 : d ^ α * d ^ (1 - α) = d := by
      rw [← Real.rpow_add hdpos]
      simp
    have e2 : r ^ α * r ^ (1 - α) = r := by
      rw [← Real.rpow_add hrpos]
      simp
    have h1 : r ^ (1 - α) ≤ d ^ (1 - α) := Real.rpow_le_rpow hrpos.le hle (by linarith)
    have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd _
    have hrα0 : 0 ≤ r ^ α := Real.rpow_nonneg hrpos.le _
    have h2 : H * d ^ α * r ≤ ε / 8 * d := by
      calc H * d ^ α * r = H * d ^ α * (r ^ α * r ^ (1 - α)) := by rw [e2]
        _ ≤ H * d ^ α * (r ^ α * d ^ (1 - α)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hH.le hdα)
          exact mul_le_mul_of_nonneg_left h1 hrα0
        _ = H * r ^ α * (d ^ α * d ^ (1 - α)) := by ring
        _ = ε / 8 * d := by rw [e1, hHr]
    have e3 : ε / (8 * r) * d = ε / 8 * d / r := by
      field_simp
    rw [e3, le_div_iff₀ hrpos]
    exact h2
  · rw [max_eq_right hle]
    have h1 : d ^ α ≤ r ^ α := Real.rpow_le_rpow hd hle hα0.le
    have e3 : ε / (8 * r) * r = ε / 8 := by
      field_simp
    rw [e3, ← hHr]
    exact mul_le_mul_of_nonneg_left h1 hH.le

lemma holder_radius {H α ε R : ℝ} (hH : 0 < H) (hα0 : 0 < α) (hε : 0 < ε) (hR : 0 < R) :
    R / (ε / (8 * H)) ^ (1 / α) = (8 * H * R ^ α / ε) ^ (1 / α) := by
  have hbase : 0 < ε / (8 * H) := by positivity
  have hRα : 0 ≤ R ^ α := Real.rpow_nonneg hR.le _
  have e1 : 8 * H * R ^ α / ε = (ε / (8 * H))⁻¹ * R ^ α := by
    field_simp
  have e2 : (R ^ α) ^ (1 / α) = R := by
    rw [← Real.rpow_mul hR.le, mul_one_div_cancel hα0.ne', Real.rpow_one]
  rw [e1, Real.mul_rpow (inv_nonneg.mpr hbase.le) hRα, e2, Real.inv_rpow hbase.le, div_eq_inv_mul]

theorem exists_runCtx {F : E → E} {L H α ε R r0 : ℝ} {x0 xs : E}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hα0 : 0 < α) (hα1 : α ≤ 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R)
    (hε : 0 < ε) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hhol : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖ + H * ‖x - y‖ ^ α)
    (hxs : F xs = 0) (hR : ‖x0 - xs‖ ≤ R) :
    ∃ r c1, RunCtx F L r ε c1 (16 * L * R / ε + 2 * (8 * H * R ^ α / ε) ^ (1 / α)) R r0 x0 xs := by
  have hRpos : 0 < R := lt_of_lt_of_le hr0 hr0R
  have hcont := continuous_of_holder hα0 hhol
  have hX : 0 ≤ (8 * H * R ^ α / ε) ^ (1 / α) := by
    apply Real.rpow_nonneg
    have := Real.rpow_nonneg hRpos.le α
    positivity
  rcases eq_or_lt_of_le hH with h0 | hpos
  · refine ⟨R, 16 * L / ε, ⟨hcont, hmono, fun x y => ?_⟩, hRpos, hε, hL, hxs, hR, hr0, hr0R, le_rfl,
      fun ρ hρ hρR => ?_, ?_⟩
    · have h1 := hhol x y
      rw [← h0, zero_mul, add_zero] at h1
      have h2 : 0 ≤ ε / (8 * R) * max ‖x - y‖ R := by positivity
      linarith
    · have h1 : 2 * ρ / R ≤ 4 := by
        rw [div_le_iff₀ hRpos]
        linarith
      have h2 : 0 ≤ 16 * L / ε * ρ := by positivity
      linarith
    · have e : 16 * L / ε * R = 16 * L * R / ε := by ring
      rw [e]
      linarith
  · set r := (ε / (8 * H)) ^ (1 / α) with hr
    have hrpos : 0 < r := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨r, 16 * L / ε + 2 / r, ⟨hcont, hmono, fun x y => ?_⟩, hrpos, hε, hL, hxs, hR, hr0, hr0R,
      ?_, fun ρ hρ _ => ?_, ?_⟩
    · have h1 := hhol x y
      have h2 := holder_scale hpos hα0 hα1 hε (norm_nonneg (x - y))
      rw [← hr] at h2
      linarith
    · have : 0 ≤ 2 / r := by positivity
      linarith
    · have h1 : 0 ≤ 16 * L / ε * ρ := by positivity
      have e : (16 * L / ε + 2 / r) * ρ = 16 * L / ε * ρ + 2 * ρ / r := by ring
      rw [e]
      linarith
    · have e : (16 * L / ε + 2 / r) * R = 16 * L * R / ε + 2 * (R / r) := by ring
      rw [e, hr, holder_radius hpos hα0 hε hRpos]

end OracleTemplate.HolderMonotone
