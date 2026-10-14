import LongTails.Proofs.NearZeroSumConjugate

open scoped RealInnerProductSpace

namespace OracleTemplate.NearZeroSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma foam_dual_step {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (z x f g : E) :
    2 * α * ‖(1 / 2 : ℝ) • (z - x)‖ ^ 2 ≤
      α * ‖z‖ ^ 2 + α * ‖f‖ ^ 2 + 2 * ⟪x + f, g - α • z - f⟫ +
      8 * ‖f + (1 / 2 : ℝ) • (x - g)‖ ^ 2 - 1 / 8 * ‖x + g‖ ^ 2 := by
  have hid : α * ‖z‖ ^ 2 + α * ‖f‖ ^ 2 + 2 * ⟪x + f, g - α • z - f⟫ +
      8 * ‖f + (1 / 2 : ℝ) • (x - g)‖ ^ 2 - 1 / 8 * ‖x + g‖ ^ 2 -
      2 * α * ‖(1 / 2 : ℝ) • (z - x)‖ ^ 2 =
      α * (1 / 2 * ‖z - x - (2 : ℝ) • f‖ ^ 2 +
        7 / 8 * ‖x + (16 / 7 : ℝ) • f - (9 / 7 : ℝ) • g‖ ^ 2 +
        3 / 7 * ‖f - g‖ ^ 2) +
      (1 - α) * (15 / 8 * ‖x + (8 / 5 : ℝ) • f - (3 / 5 : ℝ) • g‖ ^ 2 +
        6 / 5 * ‖f - g‖ ^ 2) := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm x z, real_inner_comm f z,
      real_inner_comm f x, real_inner_comm g x, real_inner_comm g f]
    ring
  have h₁ : 0 ≤ α * (1 / 2 * ‖z - x - (2 : ℝ) • f‖ ^ 2 +
        7 / 8 * ‖x + (16 / 7 : ℝ) • f - (9 / 7 : ℝ) • g‖ ^ 2 +
        3 / 7 * ‖f - g‖ ^ 2) := by positivity
  have h₂ : 0 ≤ (1 - α) * (15 / 8 * ‖x + (8 / 5 : ℝ) • f - (3 / 5 : ℝ) • g‖ ^ 2 +
        6 / 5 * ‖f - g‖ ^ 2) := mul_nonneg (sub_nonneg.mpr hα₁) (by positivity)
  linarith

lemma foam_primal_step {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (y f q : E) :
    2 * ‖(1 - α / 2) • y + (α / 2) • f - (α / 2) • q‖ ^ 2 ≤
      (2 - α) * ‖y‖ ^ 2 + α * ‖f‖ ^ 2 - 2 * α * ⟪q, y⟫ +
        8 * α ^ 2 * ‖q‖ ^ 2 := by
  have hid : (2 - α) * ‖y‖ ^ 2 + α * ‖f‖ ^ 2 - 2 * α * ⟪q, y⟫ +
        8 * α ^ 2 * ‖q‖ ^ 2 -
      2 * ‖(1 - α / 2) • y + (α / 2) • f - (α / 2) • q‖ ^ 2 =
      α * (1 - α) * ‖f - y‖ ^ 2 + α ^ 2 / 2 * ‖f - y + q‖ ^ 2 +
        7 * α ^ 2 * ‖q‖ ^ 2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm f y, real_inner_comm q y, real_inner_comm q f]
    ring
  have h : 0 ≤ α * (1 - α) * ‖f - y‖ ^ 2 := by
    exact mul_nonneg (mul_nonneg hα (sub_nonneg.mpr hα₁)) (sq_nonneg _)
  nlinarith [sq_nonneg ‖f - y + q‖, sq_nonneg ‖q‖]


set_option maxHeartbeats 2000000 in
lemma foam_scaled_step {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a b α : ℝ} (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hα₁ : α ≤ 1)
    (htune : α ^ 2 = b / a) (z x f p : E) (y v w r : F)
    (hres : a ^ 2 * ‖f + (1 / 2 : ℝ) • (x - (α • z + (1 - α) • p))‖ ^ 2 +
      ‖w + (a / 8) • (v - (α • y + (1 - α) • r))‖ ^ 2 ≤
      a ^ 2 / 64 * (‖x + (α • z + (1 - α) • p)‖ ^ 2 +
        ‖v - (α • y + (1 - α) • r)‖ ^ 2)) :
    2 * a * ‖(1 / 2 : ℝ) • (z - x)‖ ^ 2 +
      2 * b / α * ‖(1 - α / 2) • y + (α / 2) • v - (α / (2 * b)) • w‖ ^ 2 ≤
      a * ‖z‖ ^ 2 + (1 - α / 2) * (2 * b / α * ‖y‖ ^ 2) + a * ‖f‖ ^ 2 + b * ‖v‖ ^ 2 +
      2 * ((1 - α) / α) * (a * ⟪x + f, p - f⟫ + ⟪w, r - v⟫) +
      2 * (a * ⟪x + f, -f⟫ + ⟪w, -v⟫) := by
  have hd := mul_le_mul_of_nonneg_left
    (foam_dual_step hα.le hα₁ z x f (α • z + (1 - α) • p)) (show 0 ≤ a / α by positivity)
  have hp := mul_le_mul_of_nonneg_left
    (foam_primal_step hα.le hα₁ y v ((1 / b) • w)) (show 0 ≤ b / α by positivity)
  have hw : (α / 2) • ((1 / b) • w) = (α / (2 * b)) • w := by
    rw [smul_smul]; congr 1; field_simp
  rw [hw] at hp
  have hr := mul_le_mul_of_nonneg_left hres (show 0 ≤ 8 / (a * α) by positivity)
  have ht : a * α ^ 2 = b := by apply (eq_div_iff ha.ne').mp at htune; nlinarith
  have he : ‖w + (a / 8) • (v - (α • y + (1 - α) • r))‖ ^ 2 =
      ‖w‖ ^ 2 + a / 4 * ⟪w, v - (α • y + (1 - α) • r)⟫ +
      a ^ 2 / 64 * ‖v - (α • y + (1 - α) • r)‖ ^ 2 := by
    simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right]
    ring
  rw [he] at hr
  simp only [inner_add_right, inner_sub_right, inner_neg_right, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hd hp hr ⊢
  simp only [real_inner_smul_left] at hp
  have hid :
      (a / α * (α * ‖z‖ ^ 2 + α * ‖f‖ ^ 2 +
        2 * ⟪x + f, (α • z + (1 - α) • p) - α • z - f⟫ +
        8 * ‖f + (1 / 2 : ℝ) • (x - (α • z + (1 - α) • p))‖ ^ 2 -
        1 / 8 * ‖x + (α • z + (1 - α) • p)‖ ^ 2)) +
      (b / α * ((2 - α) * ‖y‖ ^ 2 + α * ‖v‖ ^ 2 -
        2 * α * (1 / b * ⟪w, y⟫) + 8 * α ^ 2 * ((1 / b) ^ 2 * ‖w‖ ^ 2))) +
      (8 / (a * α) * (a ^ 2 / 64 *
        (‖x + (α • z + (1 - α) • p)‖ ^ 2 + ‖v - (α • y + (1 - α) • r)‖ ^ 2) -
        (a ^ 2 * ‖f + (1 / 2 : ℝ) • (x - (α • z + (1 - α) • p))‖ ^ 2 +
        (‖w‖ ^ 2 + a / 4 * ⟪w, v - (α • y + (1 - α) • r)⟫ +
          a ^ 2 / 64 * ‖v - (α • y + (1 - α) • r)‖ ^ 2)))) =
      a * ‖z‖ ^ 2 + (1 - α / 2) * (2 * b / α * ‖y‖ ^ 2) + a * ‖f‖ ^ 2 + b * ‖v‖ ^ 2 +
      2 * ((1 - α) / α) * (a * ⟪x + f, p - f⟫ + ⟪w, r - v⟫) +
      2 * (a * ⟪x + f, -f⟫ + ⟪w, -v⟫) := by
    simp only [inner_add_right, inner_sub_right, inner_neg_right, real_inner_smul_right]
    rw [← ht]
    field_simp
    ring
  simp only [inner_add_right, inner_sub_right, inner_neg_right, real_inner_smul_right] at hid
  have hl₁ : a / α * (2 * α * ((1 / 2 : ℝ) ^ 2 * ‖z - x‖ ^ 2)) =
      2 * a * ((1 / 2 : ℝ) ^ 2 * ‖z - x‖ ^ 2) := by field_simp
  have hl₂ : b / α * (2 * ‖(1 - α / 2) • y + (α / 2) • v - (α / (2 * b)) • w‖ ^ 2) =
      2 * b / α * ‖(1 - α / 2) • y + (α / 2) • v - (α / (2 * b)) • w‖ ^ 2 := by ring
  rw [hl₁] at hd
  rw [hl₂] at hp
  linarith

lemma foam_contraction_algebra {α a b c Dz Dy Dnext Vprev Vnext Z X Y V ep es : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) (hc : 0 ≤ c) (hDz : 0 ≤ Dz) (hVp : 0 ≤ Vprev)
    {ip is : ℝ}
    (hstep : Dnext ≤ Dz / 2 + (1 - α / 2) * Dy + Z + b * Y ^ 2 +
      2 * ((1 - α) / α) * ip + 2 * is)
    (hprev : ip ≤ Vprev - Vnext - c / 2 * V ^ 2 + ep)
    (hstar : is ≤ -Vnext - Z / 2 - (b + c) / 2 * Y ^ 2 - a / 2 * X ^ 2 + es)
    (herr : 2 * ((1 - α) / α) * ep + 2 * es ≤
      a * X ^ 2 + c / 2 * Y ^ 2 + c / 2 * ((1 - α) / α) * V ^ 2) :
    Dnext + 2 / α * Vnext ≤
      (1 - α / 2) * (Dz + Dy + 2 / α * Vprev) := by
  have ht : 0 ≤ (1 - α) / α := div_nonneg (sub_nonneg.mpr hα₁) hα.le
  have hp := mul_le_mul_of_nonneg_left hprev (show 0 ≤ 2 * ((1 - α) / α) by positivity)
  have heq : 2 * ((1 - α) / α) + 2 = 2 / α := by field_simp; ring
  have h₁ : 0 ≤ c / 2 * Y ^ 2 := by positivity
  have h₂ : 0 ≤ c / 2 * ((1 - α) / α) * V ^ 2 := by positivity
  have hmid : Dnext + 2 / α * Vnext ≤
      Dz / 2 + (1 - α / 2) * Dy + 2 * ((1 - α) / α) * Vprev := by
    rw [← heq]
    nlinarith
  have hz : Dz / 2 ≤ (1 - α / 2) * Dz := by nlinarith
  have hv : 2 * ((1 - α) / α) * Vprev ≤ (1 - α / 2) * (2 / α * Vprev) := by
    have he : (1 - α / 2) * (2 / α * Vprev) -
        2 * ((1 - α) / α) * Vprev = Vprev := by field_simp; ring
    linarith
  nlinarith


lemma perturbed_foam_contraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a b c α δ Vprev Vnext : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hα : 0 < α) (hα₁ : α ≤ 1) (htune : α ^ 2 = b / a)
    (hsmall : 8 * δ ^ 2 ≤ a * α * c)
    (z x f p : E) (y v w r e : F) (herr : ‖e‖ ≤ 2 * δ * ‖x‖) (hVp : 0 ≤ Vprev)
    (hres : a ^ 2 * ‖f + (1 / 2 : ℝ) • (x - (α • z + (1 - α) • p))‖ ^ 2 +
      ‖w + (a / 8) • (v - (α • y + (1 - α) • r))‖ ^ 2 ≤
      a ^ 2 / 64 * (‖x + (α • z + (1 - α) • p)‖ ^ 2 +
        ‖v - (α • y + (1 - α) • r)‖ ^ 2))
    (hprev : Vnext + a * ⟪x + f, p - f⟫ + ⟪w - e, r - v⟫ + c / 2 * ‖r - v‖ ^ 2 ≤ Vprev)
    (hstar : Vnext + a * ⟪x + f, -f⟫ + ⟪w - e, -v⟫ + a / 2 * ‖f‖ ^ 2 +
      (b + c) / 2 * ‖v‖ ^ 2 + a / 2 * ‖x‖ ^ 2 ≤ 0) :
    2 * a * ‖(1 / 2 : ℝ) • (z - x)‖ ^ 2 +
      2 * b / α * ‖(1 - α / 2) • y + (α / 2) • v - (α / (2 * b)) • w‖ ^ 2 +
      2 / α * Vnext ≤
      (1 - α / 2) * (2 * a * ‖z‖ ^ 2 + 2 * b / α * ‖y‖ ^ 2 + 2 / α * Vprev) := by
  have hstep := foam_scaled_step ha hb hα hα₁ htune z x f p y v w r hres
  have he := coupling_pairings_absorbed hc hα hα₁ hsmall herr (u := -v) (v := r - v)
  rw [norm_neg] at he
  apply foam_contraction_algebra (a := a) (b := b) hα hα₁ hc.le
    (show 0 ≤ 2 * a * ‖z‖ ^ 2 by positivity) hVp
    (ip := a * ⟪x + f, p - f⟫ + ⟪w, r - v⟫)
    (is := a * ⟪x + f, -f⟫ + ⟪w, -v⟫)
    (ep := ⟪e, r - v⟫) (es := ⟪e, -v⟫) (X := ‖x‖) (Y := ‖v‖)
    (V := ‖r - v‖) (Z := a * ‖f‖ ^ 2)
  · nlinarith only [hstep]
  · simp only [inner_sub_left] at hprev
    linarith
  · simp only [inner_sub_left] at hstar
    linarith
  · linarith


lemma initial_gap_from_support {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a b c V : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (x wx : E) (y wy e : F)
    (hs : V + a * ⟪x + ((1 / a) • wx - x), -((1 / a) • wx - x)⟫ +
      ⟪wy - e, -y⟫ + a / 2 * ‖(1 / a) • wx - x‖ ^ 2 + (b + c) / 2 * ‖y‖ ^ 2 +
      a / 2 * ‖x‖ ^ 2 ≤ 0) :
    V ≤ ‖wx‖ ^ 2 / (2 * a) + ⟪wy - e, y⟫ := by
  have he : a * ⟪x + ((1 / a) • wx - x), -((1 / a) • wx - x)⟫ +
      a / 2 * ‖(1 / a) • wx - x‖ ^ 2 + a / 2 * ‖x‖ ^ 2 =
      -‖wx‖ ^ 2 / (2 * a) + a * ‖x‖ ^ 2 := by
    simp only [inner_add_left, inner_sub_left, inner_neg_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm x wx]
    field_simp
    ring
  have hx : 0 ≤ a * ‖x‖ ^ 2 := by positivity
  have hy : 0 ≤ (b + c) / 2 * ‖y‖ ^ 2 := by positivity
  simp only [inner_neg_right] at hs he
  linear_combination hs - he + hx + hy

omit [InnerProductSpace ℝ E] in
lemma initial_gap_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a L D δ V : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (x wx : E) (y wy e : F)
    (hv : V ≤ ‖wx‖ ^ 2 / (2 * a) + ⟪wy - e, y⟫)
    (hxy : ‖x‖ ^ 2 + ‖y‖ ^ 2 ≤ D ^ 2)
    (hwx : ‖wx‖ ^ 2 ≤ 4 * L ^ 2 * D ^ 2) (hwy : ‖wy‖ ≤ 2 * L * D)
    (he : ‖e‖ ≤ 2 * δ * ‖x‖) :
    V ≤ 2 * L ^ 2 * D ^ 2 / a + (2 * L + δ) * D ^ 2 := by
  have hyD : ‖y‖ ≤ D := by nlinarith [norm_nonneg y, sq_nonneg ‖x‖]
  have heip := (real_inner_le_norm (-e) y).trans
    (mul_le_mul_of_nonneg_right (by simpa only [norm_neg] using he) (norm_nonneg y))
  have hwip := (real_inner_le_norm wy y).trans
    (mul_le_mul_of_nonneg_right hwy (norm_nonneg y))
  have hwyD := mul_le_mul_of_nonneg_left hyD (show 0 ≤ 2 * L * D by positivity)
  have hc : 2 * δ * ‖x‖ * ‖y‖ ≤ δ * D ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hxy hδ
    have hh := mul_nonneg hδ (sq_nonneg (‖x‖ - ‖y‖))
    nlinarith
  have hw := div_le_div_of_nonneg_right hwx (show 0 ≤ 2 * a by positivity)
  have hid : 4 * L ^ 2 * D ^ 2 / (2 * a) = 2 * L ^ 2 * D ^ 2 / a := by ring
  rw [hid] at hw
  simp only [inner_sub_left, inner_neg_left] at hv heip
  nlinarith

lemma foam_tuning {M m δ : ℝ} (hm : 0 < m) (hM : m ≤ M)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ m / 8) :
    let a := M / 2
    let b := m / 2
    let c := m / 2 - δ
    let α := Real.sqrt (m / M)
    0 < α ∧ α ≤ 1 ∧ α ^ 2 = b / a ∧ 0 < c ∧ 8 * δ ^ 2 ≤ a * α * c := by
  dsimp only
  have hMp : 0 < M := hm.trans_le hM
  have hr : 0 < m / M := div_pos hm hMp
  have hα := Real.sqrt_pos.mpr hr
  have hαsq := Real.sq_sqrt hr.le
  have hr₁ : m / M ≤ 1 := (div_le_one hMp).mpr hM
  have hα₁ : Real.sqrt (m / M) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (m / M)]
  have hαr : m / M ≤ Real.sqrt (m / M) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hαr hMp.le
  have hcancel : M * (m / M) = m := by field_simp
  rw [hcancel] at hprod
  have hc : 0 < m / 2 - δ := by linarith
  have hprod₂ := mul_le_mul_of_nonneg_right hprod hc.le
  have hδsq := mul_self_le_mul_self hδ hsmall
  have hmc := mul_le_mul_of_nonneg_left hsmall hm.le
  refine ⟨hα, hα₁, ?_, hc, ?_⟩
  · rw [hαsq]
    field_simp
  · nlinarith

end OracleTemplate.NearZeroSum
