import LongTails.Proofs.StronglyMonotoneZero

open scoped RealInnerProductSpace

namespace OracleTemplate.HolderMonotone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def reg (F : E → E) (μ : ℝ) (x0 x : E) : E := F x + μ • (x - x0)

structure Hyp (F : E → E) (L r ε : ℝ) : Prop where
  cont : Continuous F
  mono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫
  scale : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖ + ε / (8 * r) * max ‖x - y‖ r

lemma reg_sub (F : E → E) (μ : ℝ) (x0 x y : E) :
    reg F μ x0 x - reg F μ x0 y = (F x - F y) + μ • (x - y) := by
  unfold reg
  rw [show x - x0 = (x - y) + (y - x0) by abel, smul_add]
  abel

lemma reg_strong {F : E → E} (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) (μ : ℝ) (x0 x y : E) :
    μ * ‖x - y‖ ^ 2 ≤ ⟪reg F μ x0 x - reg F μ x0 y, x - y⟫ := by
  rw [reg_sub, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [RCLike.conj_to_real]
  linarith [hmono x y]

lemma reg_norm_sub_le {F : E → E} {L r ε : ℝ} (h : Hyp F L r ε) {μ : ℝ} (hμ : 0 ≤ μ) (x0 x y : E) :
    ‖reg F μ x0 x - reg F μ x0 y‖ ≤
      (L + μ) * ‖x - y‖ + ε / (8 * r) * max ‖x - y‖ r := by
  rw [reg_sub]
  have h1 := norm_add_le (F x - F y) (μ • (x - y))
  have h2 : ‖μ • (x - y)‖ = μ * ‖x - y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
  have h3 := h.scale x y
  linarith

lemma exists_reg_zero [FiniteDimensional ℝ E] {F : E → E} (hc : Continuous F)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {μ : ℝ} (hμ : 0 < μ) (x0 : E) :
    ∃ z, reg F μ x0 z = 0 := by
  refine StronglyMonotoneZero.exists_zero (G := reg F μ x0) ?_ hμ (reg_strong hmono μ x0)
  unfold reg
  fun_prop

lemma anchor_dist {F : E → E} (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {μ : ℝ} (hμ : 0 < μ)
    {x0 z xs : E} (hz : reg F μ x0 z = 0) (hxs : F xs = 0) : ‖z - x0‖ ≤ ‖x0 - xs‖ := by
  have hF : F z = -(μ • (z - x0)) := by
    unfold reg at hz
    exact eq_neg_of_add_eq_zero_left hz
  have h1 := hmono z xs
  rw [hxs, sub_zero, hF, inner_neg_left, inner_smul_left] at h1
  simp only [RCLike.conj_to_real] at h1
  have h2 : ⟪z - x0, z - xs⟫ ≤ 0 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith
  have e : z - xs = (z - x0) + (x0 - xs) := by abel
  rw [e, inner_add_right, real_inner_self_eq_norm_sq] at h2
  have h3 : -(‖z - x0‖ * ‖x0 - xs‖) ≤ ⟪z - x0, x0 - xs⟫ := by
    have := abs_real_inner_le_norm (z - x0) (x0 - xs)
    linarith [neg_abs_le ⟪z - x0, x0 - xs⟫]
  by_contra hcon
  have hcon := not_le.mp hcon
  have hpos : 0 < ‖z - x0‖ := lt_of_le_of_lt (norm_nonneg _) hcon
  nlinarith

lemma fejer_step {G : E → E} {μ : ℝ} (hμ : 0 ≤ μ)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    {z : E} (hz : G z = 0) {s : ℝ} (hs : 0 ≤ s) (hsμ : s * μ ≤ 1 / 8) (x : E)
    (htest : ‖G (x - s • G x) - G x‖ ≤ ‖G x‖ / 2) :
    ‖x - s • G (x - s • G x) - z‖ ^ 2 ≤ (1 - s * μ) * ‖x - z‖ ^ 2 := by
  set gx := G x with hgx
  set gy := G (x - s • gx) with hgy
  set a := x - z with ha
  have e1 : x - s • gy - z = a - s • gy := by rw [ha]; abel
  have e2 : x - s • gx - z = a - s • gx := by rw [ha]; abel
  have hm := hstrong (x - s • gx) z
  rw [hz, sub_zero, e2, ← hgy] at hm
  have n1 : ‖a - s • gy‖ ^ 2 = ‖a‖ ^ 2 - 2 * s * ⟪gy, a⟫ + s ^ 2 * ‖gy‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm]
    ring
  have n2 : ‖a - s • gx‖ ^ 2 = ‖a‖ ^ 2 - 2 * s * ⟪a, gx⟫ + s ^ 2 * ‖gx‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have n3 : ‖a - (2 * s) • gx‖ ^ 2 = ‖a‖ ^ 2 - 4 * s * ⟪a, gx⟫ + 4 * s ^ 2 * ‖gx‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have n4 : ‖gy - gx‖ ^ 2 = ‖gy‖ ^ 2 - 2 * ⟪gy, gx⟫ + ‖gx‖ ^ 2 := norm_sub_sq_real gy gx
  have n5 : ⟪gy, a - s • gx⟫ = ⟪gy, a⟫ - s * ⟪gy, gx⟫ := by
    rw [inner_sub_right, inner_smul_right]
  have t1 : ‖gy - gx‖ ^ 2 ≤ ‖gx‖ ^ 2 / 4 := by
    have h0 : 0 ≤ ‖gy - gx‖ := norm_nonneg _
    nlinarith
  have p3 : 0 ≤ ‖a - (2 * s) • gx‖ ^ 2 := sq_nonneg _
  have hN : ‖a‖ ^ 2 / 2 - s ^ 2 * ‖gx‖ ^ 2 ≤ ‖a - s • gx‖ ^ 2 := by
    rw [n2]; rw [n3] at p3; linarith
  rw [n5] at hm
  have hX : 0 ≤ ‖gx‖ ^ 2 := sq_nonneg _
  have hsμ0 : 0 ≤ s * μ := mul_nonneg hs hμ
  have k1 : s * μ * (‖a‖ ^ 2 / 2 - s ^ 2 * ‖gx‖ ^ 2) ≤ s * (⟪gy, a⟫ - s * ⟪gy, gx⟫) := by
    have := mul_le_mul_of_nonneg_left hN hsμ0
    have h' := mul_le_mul_of_nonneg_left hm hs
    nlinarith
  have k2 : s ^ 2 * (‖gy‖ ^ 2 - 2 * ⟪gy, gx⟫ + ‖gx‖ ^ 2) ≤ s ^ 2 * (‖gx‖ ^ 2 / 4) := by
    rw [← n4]
    exact mul_le_mul_of_nonneg_left t1 (sq_nonneg s)
  have k3 : s * μ * (s ^ 2 * ‖gx‖ ^ 2) ≤ 1 / 8 * (s ^ 2 * ‖gx‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hsμ (mul_nonneg (sq_nonneg s) hX)
  rw [e1, n1]
  nlinarith

lemma pass_test {F : E → E} {L r ε : ℝ} (h : Hyp F L r ε) (hr : 0 < r) (hε : 0 < ε)
    {μ : ℝ} (hμ : 0 ≤ μ) (x0 : E) {s : ℝ} (hs : 0 ≤ s) (hsL : s * (L + μ) ≤ 1 / 4)
    (hsr : s ≤ 2 * r / ε) (x : E) (hg : ε / 2 < ‖reg F μ x0 x‖) :
    ‖reg F μ x0 (x - s • reg F μ x0 x) - reg F μ x0 x‖ ≤ ‖reg F μ x0 x‖ / 2 := by
  set g := reg F μ x0 x with hgdef
  have hb := reg_norm_sub_le h hμ x0 (x - s • g) x
  have ht : ‖x - s • g - x‖ = s * ‖g‖ := by
    rw [show x - s • g - x = -(s • g) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs]
  rw [ht] at hb
  have hgpos : 0 < ‖g‖ := by linarith
  have h1 : (L + μ) * (s * ‖g‖) ≤ ‖g‖ / 4 := by
    have := mul_le_mul_of_nonneg_right hsL hgpos.le
    nlinarith
  have h2 : ε / (8 * r) * max (s * ‖g‖) r ≤ ‖g‖ / 4 := by
    have hc : 0 < ε / (8 * r) := by positivity
    rcases le_total (s * ‖g‖) r with hle | hle
    · rw [max_eq_right hle]
      have : ε / (8 * r) * r = ε / 8 := by field_simp
      rw [this]; linarith
    · rw [max_eq_left hle]
      have h3 : s * ‖g‖ ≤ 2 * r / ε * ‖g‖ := mul_le_mul_of_nonneg_right hsr hgpos.le
      have h4 : ε / (8 * r) * (2 * r / ε * ‖g‖) = ‖g‖ / 4 := by field_simp; ring
      calc ε / (8 * r) * (s * ‖g‖) ≤ ε / (8 * r) * (2 * r / ε * ‖g‖) :=
            mul_le_mul_of_nonneg_left h3 hc.le
        _ = ‖g‖ / 4 := h4
  linarith

lemma small_of_close {F : E → E} {L r ε : ℝ} (h : Hyp F L r ε) (hr : 0 < r) (hε : 0 < ε)
    {μ : ℝ} (hμ : 0 ≤ μ) (hL : 0 ≤ L) (x0 : E) {z : E} (hz : reg F μ x0 z = 0)
    {sb : ℝ} (hsL : sb * (L + μ) ≤ 1 / 4) (hsr : sb ≤ 2 * r / ε) (x : E)
    (hd : ‖x - z‖ ≤ ε * sb) : ‖reg F μ x0 x‖ ≤ ε / 2 := by
  have hb := reg_norm_sub_le h hμ x0 x z
  rw [hz, sub_zero] at hb
  have hLμ : 0 ≤ L + μ := add_nonneg hL hμ
  have h1 : (L + μ) * ‖x - z‖ ≤ ε / 4 := by
    have := mul_le_mul_of_nonneg_left hd hLμ
    nlinarith
  have h2r : ‖x - z‖ ≤ 2 * r := by
    have : ε * sb ≤ ε * (2 * r / ε) := mul_le_mul_of_nonneg_left hsr hε.le
    have e : ε * (2 * r / ε) = 2 * r := by field_simp
    linarith
  have h2 : ε / (8 * r) * max ‖x - z‖ r ≤ ε / 4 := by
    have hc : 0 < ε / (8 * r) := by positivity
    have hm : max ‖x - z‖ r ≤ 2 * r := max_le h2r (by linarith)
    have e : ε / (8 * r) * (2 * r) = ε / 4 := by field_simp; ring
    calc ε / (8 * r) * max ‖x - z‖ r ≤ ε / (8 * r) * (2 * r) :=
          mul_le_mul_of_nonneg_left hm hc.le
      _ = ε / 4 := e
  linarith

lemma norm_le_reg (F : E → E) {μ : ℝ} (hμ : 0 ≤ μ) (x0 x : E) :
    ‖F x‖ ≤ ‖reg F μ x0 x‖ + μ * ‖x - x0‖ := by
  have e : F x = reg F μ x0 x - μ • (x - x0) := by unfold reg; abel
  have h1 := norm_sub_le (reg F μ x0 x) (μ • (x - x0))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at h1
  rw [e]
  simpa using h1

end OracleTemplate.HolderMonotone
