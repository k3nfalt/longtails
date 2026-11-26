import LongTails.Proofs.TerminalClippingEnergy

open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClippingSingleLog

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def mix (m : ℝ) (z y : E) : E :=
  ((m-1)/(m+1)) • z + (2/(m+1)) • y

noncomputable def energy (m : ℝ) (y z : E) : ℝ := ‖y-z‖^2/(m*(m+1))

noncomputable def direction (m k : ℝ) (y z : E) : E := (2*k/(m+1)) • (y-z)

lemma mix_weights {m : ℝ} (hm : 1 ≤ m) :
    0 ≤ (m-1)/(m+1) ∧ 0 ≤ 2/(m+1) ∧ (m-1)/(m+1)+2/(m+1)=1 := by
  have hd : 0 < m+1 := by linarith
  exact ⟨div_nonneg (by linarith) hd.le, by positivity, by field_simp; ring⟩

lemma mix_energy {m : ℝ} (hm : 1 ≤ m) (y z : E) :
    energy (m-1) y (mix m z y) ≤ energy m y z := by
  have h := mix_weights hm
  have he : y-mix m z y = ((m-1)/(m+1)) • (y-z) := by
    have eqc := h.2.2
    unfold mix
    linear_combination (norm := module) congrArg (fun a : ℝ => a • y) eqc.symm
  rcases eq_or_lt_of_le hm with hh|hh
  · subst m
    simp [energy]
    positivity
  · have hpos : 0 < m-1 := by linarith
    have hd : 0 < m+1 := by linarith
    unfold energy
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg h.1]
    field_simp
    nlinarith [sq_nonneg ‖y-z‖]

lemma weighted_step {m k M : ℝ} (hm : 1 ≤ m) (hk : 0 < k) (hM : 0 ≤ M)
    {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f) {y z y' u h c : E}
    (hz : z ∈ K) (hy' : y' ∈ K)
    (hp : ‖y'-z‖^2 ≤ ‖y-(k*m) • c-z‖^2)
    (hs : ‖y'-y‖ ≤ k*m*‖c‖)
    (hsub : f y-f z ≤ ⟪h,y-z⟫) (hlip : f y'-f y ≤ M*‖y'-y‖) :
    energy m y' z + k*(f (mix m z y')-f u) ≤
      energy m y z + k*(f z-f u) + 2*k^2*(M^2/2+‖c‖^2) +
        ⟪h-c,direction m k y z⟫ := by
  have hm0 : 0 < m := by linarith
  have hd : 0 < m+1 := by linarith
  have hw := mix_weights hm
  have hmix := mul_le_mul_of_nonneg_left (hf.2 hz hy' hw.1 hw.2.1 hw.2.2) hk.le
  have hone := TerminalClipping.projected_objective_step (f := f) (mul_pos hk hm0) hM hp hs hsub hlip
  have hh := mul_le_mul_of_nonneg_left hone (show 0 ≤ 2/(m*(m+1)) by positivity)
  have hmixed : k*(f (mix m z y')-f u) ≤ k*(f z-f u)+(2*k/(m+1))*(f y'-f z) := by
    dsimp only [mix, smul_eq_mul] at *
    convert sub_le_sub_right hmix (k*f u) using 1 <;> field_simp
    ring
  unfold energy direction
  rw [real_inner_smul_right]
  apply (add_le_add_right hmixed _).trans
  have hsq : 0 ≤ k^2*(M^2/2+‖c‖^2) := by positivity
  field_simp at hh ⊢
  nlinarith [mul_nonneg hm0.le hsq]

omit [InnerProductSpace ℝ E] in
lemma energy_distance {r m : ℝ} (hr : 0 < r) (hm : 1 ≤ m) {x z : E}
    (he : energy m x z ≤ 2*r^2) : ‖x-z‖ ≤ (29/20)*r*(m+1) := by
  have hm0 : 0 < m := by linarith
  have hd : 0 < m+1 := by linarith
  have hh := (div_le_iff₀ (mul_pos hm0 hd)).mp he
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [sq_nonneg (r*m), mul_nonneg (sq_nonneg r) hm0.le, sq_nonneg r]

lemma direction_bound {r m k : ℝ} (hr : 0 < r) (hm : 1 ≤ m) (hk : 0 ≤ k) {x z : E}
    (he : energy m x z ≤ 2*r^2) : ‖direction m k x z‖ ≤ 3*k*r := by
  have hd : 0 < m+1 := by linarith
  rw [direction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (energy_distance hr hm he) (show 0 ≤ 2*k/(m+1) by positivity)
  apply hh.trans
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hk hr.le) hd.le]

lemma mix_displacement {r m : ℝ} (hr : 0 < r) (hm : 1 ≤ m) {y z : E}
    (he : energy m y z ≤ 2*r^2) : ‖mix m z y-z‖ ≤ (29/10)*r := by
  have hd : 0 < m+1 := by linarith
  have hw := (mix_weights hm).2.2
  have hid : mix m z y-z = (2/(m+1)) • (y-z) := by
    unfold mix
    linear_combination (norm := module) congrArg (fun a : ℝ => a • z) hw
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (energy_distance hr hm he) (show 0 ≤ 2/(m+1) by positivity)).trans
  field_simp
  linarith

end OracleTemplate.TerminalClippingSingleLog
