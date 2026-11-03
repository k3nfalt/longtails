import LongTails.Proofs.ComparisonTrustAgd

namespace LongTails.Proofs.ComparisonTrustQuadratic

open LongTails.Algorithms.GuardedMetricAcceleration LongTails.Proofs.ComparisonTrustAgd
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def quad (b : E) (M : E →L[ℝ] E) (s : E) : ℝ := ⟪b, s⟫ + ⟪s, M s⟫ / 2

def qgrad (b : E) (M : E →L[ℝ] E) (s : E) : E := b + M s

variable {b : E} {M : E →L[ℝ] E}

lemma quad_zero : quad b M 0 = 0 := by simp [quad]

lemma quad_expand (hM : M.toLinearMap.IsSymmetric) (u y : E) :
    quad b M u = quad b M y + ⟪qgrad b M y, u - y⟫ + ⟪u - y, M (u - y)⟫ / 2 := by
  have hs : ⟪y, M (u - y)⟫ = ⟪M y, u - y⟫ := (hM y (u - y)).symm
  simp only [quad, qgrad, map_sub, inner_sub_left, inner_sub_right, inner_add_left] at hs ⊢
  have h1 : ⟪u, M y⟫ = ⟪M u, y⟫ := (hM u y).symm
  have h2 : ⟪M u, y⟫ = ⟪y, M u⟫ := real_inner_comm _ _
  have h3 : ⟪M y, u⟫ = ⟪u, M y⟫ := real_inner_comm _ _
  linarith

lemma quad_value_grad (x : E) :
    quad b M x = ⟪qgrad b M x, x⟫ - ⟪x, M x⟫ / 2 := by
  simp only [quad, qgrad, inner_add_left]
  rw [real_inner_comm (M x) x]
  ring

lemma support_of_check (hM : M.toLinearMap.IsSymmetric) {μ e : ℝ} {u y G : E}
    (hcheck : μ * ‖u - y‖ ^ 2 ≤ ⟪u - y, M (u - y)⟫) (hG : ‖G - qgrad b M y‖ ≤ e) :
    quad b M y + ⟪G, u - y⟫ + μ / 2 * ‖u - y‖ ^ 2 ≤ quad b M u + e * ‖u - y‖ := by
  rw [quad_expand hM u y]
  have : ⟪G, u - y⟫ - ⟪qgrad b M y, u - y⟫ ≤ e * ‖u - y‖ := by
    rw [← inner_sub_left]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
  linarith

lemma descent_quad (hM : M.toLinearMap.IsSymmetric) {L e : ℝ} (hL : 0 < L) (hML : ‖M‖ ≤ L)
    {y G : E} (hG : ‖G - qgrad b M y‖ ≤ e) :
    quad b M (gradientStep L y G) ≤ quad b M y - ‖G‖ ^ 2 / (2 * L) + e * ‖G‖ / L := by
  rw [quad_expand hM (gradientStep L y G) y]
  have hd : gradientStep L y G - y = -(L⁻¹ • G) := by simp [gradientStep]
  rw [hd]
  have hMG : ⟪-(L⁻¹ • G), M (-(L⁻¹ • G))⟫ ≤ L * ‖L⁻¹ • G‖ ^ 2 := by
    calc _ ≤ ‖-(L⁻¹ • G)‖ * ‖M (-(L⁻¹ • G))‖ := real_inner_le_norm _ _
      _ ≤ ‖-(L⁻¹ • G)‖ * (‖M‖ * ‖-(L⁻¹ • G)‖) :=
          mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖-(L⁻¹ • G)‖ * (L * ‖-(L⁻¹ • G)‖) := by gcongr
      _ = L * ‖L⁻¹ • G‖ ^ 2 := by rw [norm_neg]; ring
  have hlin : ⟪qgrad b M y, -(L⁻¹ • G)⟫ = -(L⁻¹ * ‖G‖ ^ 2) + L⁻¹ * ⟪G - qgrad b M y, G⟫ := by
    rw [inner_neg_right, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_comm G]
    ring
  have herr : ⟪G - qgrad b M y, G⟫ ≤ e * ‖G‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL] at hMG
  have hsq : L * (L⁻¹ * ‖G‖) ^ 2 = ‖G‖ ^ 2 / L := by field_simp
  have hk : L⁻¹ * ⟪G - qgrad b M y, G⟫ ≤ e * ‖G‖ / L := by
    rw [div_eq_inv_mul, ← mul_assoc, mul_comm L⁻¹ e, mul_assoc]
    rw [mul_comm e, mul_assoc]
    have := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hL.le)
    linarith
  have hk2 : L⁻¹ * ‖G‖ ^ 2 = 2 * (‖G‖ ^ 2 / (2 * L)) := by field_simp
  have hk3 : ‖G‖ ^ 2 / L = 2 * (‖G‖ ^ 2 / (2 * L)) := by field_simp
  linarith

lemma quad_lower {μ : ℝ} {x : E} (hcheck : μ * ‖x‖ ^ 2 ≤ ⟪x, M x⟫) :
    -(‖b‖ * ‖x‖) + μ / 2 * ‖x‖ ^ 2 ≤ quad b M x := by
  unfold quad
  have := neg_le_of_abs_le (abs_real_inner_le_norm b x)
  linarith

lemma quad_segment {x : E} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hpos : 0 ≤ ⟪x, M x⟫) :
    quad b M (t • x) ≤ t * quad b M x := by
  unfold quad
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  have : t * t ≤ t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hpos]

lemma norm_extrapolate_le {a A : ℝ} (ha : 0 ≤ a) {x z : E} (hx : ‖x‖ ≤ A) (hz : ‖z‖ ≤ A) :
    ‖extrapolate a x z‖ ≤ A := by
  unfold extrapolate
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + a)]
  have h : ‖x + a • z‖ ≤ A + a * A := by
    calc ‖x + a • z‖ ≤ ‖x‖ + ‖a • z‖ := norm_add_le _ _
      _ ≤ A + a * A := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
        gcongr
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith

lemma valid_mono {R : Run E} {N k : ℕ} (hv : R.Valid N) (hk : k ≤ N) : R.Valid k :=
  ⟨hv.ha, hv.ha₁, hv.hμ, hv.hL, hv.htune, hv.x0, hv.z0, fun j hj => hv.step j (by omega)⟩

structure Bounds (R : Run E) (b : E) (M : E →L[ℝ] E) (N : ℕ) (B e1 e0 : ℝ) : Prop where
  valid : R.Valid N
  sym : M.toLinearMap.IsSymmetric
  norm : ‖M‖ ≤ R.L
  hb : ‖b‖ ≤ B
  hB : 0 ≤ B
  he1 : 0 ≤ e1
  he0 : 0 ≤ e0
  err : ∀ k < N, ‖R.Gs k - qgrad b M (R.ys k)‖ ≤ e1 * ‖R.ys k‖ + e0
  c1 : ∀ k < N, R.μ * ‖R.xs k - R.ys k‖ ^ 2 ≤ ⟪R.xs k - R.ys k, M (R.xs k - R.ys k)⟫
  c2 : ∀ k < N, R.μ * ‖R.ys k‖ ^ 2 ≤ ⟪R.ys k, M (R.ys k)⟫
  c3 : ∀ k < N, R.μ * ‖R.xs (k + 1)‖ ^ 2 ≤ ⟪R.xs (k + 1), M (R.xs (k + 1))⟫

def radius (R : Run E) (B ℓ : ℝ) : ℝ := 2 * B / R.μ + ℓ

def slackR (R : Run E) (B ℓ e1 e0 : ℝ) : ℝ := e1 * radius R B ℓ + e0

def gmax (R : Run E) (B ℓ e1 e0 : ℝ) : ℝ := B + R.L * radius R B ℓ + slackR R B ℓ e1 e0

def slack (R : Run E) (B ℓ e1 e0 : ℝ) : ℝ :=
  slackR R B ℓ e1 e0 * (4 * radius R B ℓ + 2 * gmax R B ℓ e1 e0 / R.L)

lemma steps_ok {R : Run E} {N : ℕ} {B ℓ e1 e0 : ℝ} (hℓ : 0 < ℓ) (hb : Bounds R b M N B e1 e0) (k : ℕ)
    (hk : k < N) (hy : ‖R.ys k‖ ≤ radius R B ℓ) (hx : ‖R.xs k‖ ≤ radius R B ℓ) :
    ‖R.Gs k - qgrad b M (R.ys k)‖ ≤ slackR R B ℓ e1 e0 ∧ ‖R.Gs k‖ ≤ gmax R B ℓ e1 e0 ∧
    quad b M (R.ys k) + ⟪R.Gs k, R.xs k - R.ys k⟫ + R.μ / 2 * ‖R.xs k - R.ys k‖ ^ 2 ≤
      quad b M (R.xs k) + slack R B ℓ e1 e0 ∧
    quad b M (R.ys k) + ⟪R.Gs k, 0 - R.ys k⟫ + R.μ / 2 * ‖0 - R.ys k‖ ^ 2 ≤
      quad b M 0 + slack R B ℓ e1 e0 ∧
    quad b M (R.xs (k + 1)) ≤ quad b M (R.ys k) - ‖R.Gs k‖ ^ 2 / (2 * R.L) +
      slack R B ℓ e1 e0 := by
  have hv := hb.valid
  have hrad : ℓ ≤ radius R B ℓ := by
    unfold radius
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.hB) hv.hμ.le
    linarith
  have he : ‖R.Gs k - qgrad b M (R.ys k)‖ ≤ slackR R B ℓ e1 e0 := by
    refine (hb.err k hk).trans ?_
    unfold slackR
    have := mul_le_mul_of_nonneg_left hy hb.he1
    linarith
  have heR : 0 ≤ slackR R B ℓ e1 e0 := le_trans (norm_nonneg _) he
  have hq : ‖qgrad b M (R.ys k)‖ ≤ B + R.L * radius R B ℓ := by
    unfold qgrad
    calc ‖b + M (R.ys k)‖ ≤ ‖b‖ + ‖M (R.ys k)‖ := norm_add_le _ _
      _ ≤ B + ‖M‖ * ‖R.ys k‖ := add_le_add hb.hb (M.le_opNorm _)
      _ ≤ B + R.L * radius R B ℓ := by
        gcongr
        · exact hv.hL.le
        · exact hb.norm
  have hG : ‖R.Gs k‖ ≤ gmax R B ℓ e1 e0 := by
    unfold gmax
    have := norm_le_norm_add_norm_sub' (R.Gs k) (qgrad b M (R.ys k))
    have h2 : ‖R.Gs k‖ ≤ ‖qgrad b M (R.ys k)‖ + ‖R.Gs k - qgrad b M (R.ys k)‖ := by
      have := norm_sub_norm_le (R.Gs k) (qgrad b M (R.ys k))
      linarith
    linarith
  have hgm : 0 ≤ gmax R B ℓ e1 e0 := le_trans (norm_nonneg _) hG
  have hsl1 : slackR R B ℓ e1 e0 * (2 * radius R B ℓ) ≤ slack R B ℓ e1 e0 := by
    unfold slack
    have : 0 ≤ 2 * gmax R B ℓ e1 e0 / R.L := div_nonneg (by linarith) hv.hL.le
    nlinarith
  have hsl2 : slackR R B ℓ e1 e0 * radius R B ℓ ≤ slack R B ℓ e1 e0 := by
    have : 0 ≤ slackR R B ℓ e1 e0 * radius R B ℓ := mul_nonneg heR (by linarith)
    linarith
  have hsl3 : slackR R B ℓ e1 e0 * gmax R B ℓ e1 e0 / R.L ≤ slack R B ℓ e1 e0 := by
    unfold slack
    have h0 : 0 ≤ slackR R B ℓ e1 e0 * (4 * radius R B ℓ) := mul_nonneg heR (by linarith)
    have : slackR R B ℓ e1 e0 * gmax R B ℓ e1 e0 / R.L ≤
        slackR R B ℓ e1 e0 * (2 * gmax R B ℓ e1 e0 / R.L) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ heR
      apply div_le_div_of_nonneg_right _ hv.hL.le
      linarith
    nlinarith
  refine ⟨he, hG, ?_, ?_, ?_⟩
  · have h1 := support_of_check hb.sym (hb.c1 k hk) he
    have hxy : ‖R.xs k - R.ys k‖ ≤ 2 * radius R B ℓ :=
      (norm_sub_le _ _).trans (by linarith)
    have := mul_le_mul_of_nonneg_left hxy heR
    linarith
  · have hc : R.μ * ‖0 - R.ys k‖ ^ 2 ≤ ⟪0 - R.ys k, M (0 - R.ys k)⟫ := by
      have := hb.c2 k hk
      simpa [norm_neg, map_neg, inner_neg_left, inner_neg_right] using this
    have h1 := support_of_check hb.sym hc he
    have : slackR R B ℓ e1 e0 * ‖0 - R.ys k‖ ≤ slackR R B ℓ e1 e0 * radius R B ℓ := by
      rw [zero_sub, norm_neg]
      exact mul_le_mul_of_nonneg_left hy heR
    linarith
  · obtain ⟨hx1, _⟩ := hv.step k hk
    rw [hx1]
    have h1 := descent_quad hb.sym hv.hL hb.norm he
    have : slackR R B ℓ e1 e0 * ‖R.Gs k‖ / R.L ≤ slackR R B ℓ e1 e0 * gmax R B ℓ e1 e0 / R.L := by
      apply div_le_div_of_nonneg_right _ hv.hL.le
      exact mul_le_mul_of_nonneg_left hG heR
    linarith

lemma radius_bound {R : Run E} {N : ℕ} {B ℓ e1 e0 : ℝ} (hℓ : 0 < ℓ) (hb : Bounds R b M N B e1 e0)
    (hθ : 8 * slack R B ℓ e1 e0 ≤ R.a * R.μ * ℓ ^ 2) :
    ∀ k ≤ N, ‖R.xs k‖ ≤ radius R B ℓ ∧ ‖R.zs k‖ ≤ radius R B ℓ := by
  have hv := hb.valid
  have hrad : ℓ ≤ radius R B ℓ := by
    unfold radius
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.hB) hv.hμ.le
    linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkN
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [hv.x0, hv.z0, norm_zero]
      exact ⟨by linarith, by linarith⟩
    have hprev : ∀ j < k, ‖R.ys j‖ ≤ radius R B ℓ ∧ ‖R.xs j‖ ≤ radius R B ℓ := by
      intro j hj
      obtain ⟨h1, h2⟩ := ih j hj (by omega)
      exact ⟨norm_extrapolate_le hv.ha.le h1 h2, h1⟩
    have hok := fun j (hj : j < k) => steps_ok hℓ hb j (by omega) (hprev j hj).1 (hprev j hj).2
    have hsl : 0 ≤ slack R B ℓ e1 e0 := by
      have := hok 0 hkpos
      have h := this.1
      unfold slack
      have heR : 0 ≤ slackR R B ℓ e1 e0 := le_trans (norm_nonneg _) h
      have hgm : 0 ≤ gmax R B ℓ e1 e0 := le_trans (norm_nonneg _) this.2.1
      have : 0 ≤ 2 * gmax R B ℓ e1 e0 / R.L := div_nonneg (by linarith) hv.hL.le
      exact mul_nonneg heR (by linarith)
    obtain ⟨hval, hz⟩ := inexact_value (quad b M) R (valid_mono hv hkN) hsl 0
      (fun j hj => (hok j hj).2.2.1) (fun j hj => (hok j hj).2.2.2.1)
      (fun j hj => (hok j hj).2.2.2.2)
    rw [quad_zero, sub_self, zero_add, norm_zero] at hval hz
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      sub_zero, zero_sub, norm_neg] at hval hz
    have h4 : 4 * slack R B ℓ e1 e0 / R.a ≤ R.μ * ℓ ^ 2 / 2 := by
      rw [div_le_iff₀ hv.ha]
      linarith
    have hcx : R.μ * ‖R.xs k‖ ^ 2 ≤ ⟪R.xs k, M (R.xs k)⟫ := by
      have := hb.c3 (k - 1) (by omega)
      rwa [Nat.sub_add_cancel hkpos] at this
    have hlow := quad_lower (b := b) hcx
    have hbx : ‖b‖ * ‖R.xs k‖ ≤ B * ‖R.xs k‖ := mul_le_mul_of_nonneg_right hb.hb (norm_nonneg _)
    have hX : ‖R.xs k‖ ≤ radius R B ℓ := by
      unfold radius
      by_contra hcon
      push Not at hcon
      have hμ := hv.hμ
      have hX1 : ℓ < ‖R.xs k‖ := by
        have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.hB) hμ.le
        linarith
      have : R.μ * ‖R.xs k‖ > 2 * B + R.μ * ℓ := by
        have := mul_lt_mul_of_pos_left hcon hμ
        rw [mul_add, mul_div_cancel₀ _ hμ.ne'] at this
        linarith
      have : R.μ * ℓ * ℓ < R.μ * ℓ * ‖R.xs k‖ := mul_lt_mul_of_pos_left hX1 (by positivity)
      nlinarith
    refine ⟨hX, ?_⟩
    have hzsq : R.μ / 2 * ‖R.zs k‖ ^ 2 ≤ B * radius R B ℓ + R.μ * ℓ ^ 2 / 2 := by
      have : 0 ≤ R.μ / 2 * ‖R.xs k‖ ^ 2 := by have := hv.hμ; positivity
      have := mul_le_mul_of_nonneg_left hX hb.hB
      linarith
    have hR2 : 2 * B / R.μ * radius R B ℓ + ℓ ^ 2 ≤ radius R B ℓ ^ 2 := by
      have : radius R B ℓ ^ 2 = radius R B ℓ * (2 * B / R.μ + ℓ) := by unfold radius; ring
      rw [this]
      have h0 := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.hB) hv.hμ.le
      have : ℓ * ℓ ≤ radius R B ℓ * ℓ := mul_le_mul_of_nonneg_right hrad hℓ.le
      nlinarith
    have hz2 : ‖R.zs k‖ ^ 2 ≤ radius R B ℓ ^ 2 := by
      have hμ := hv.hμ
      have : ‖R.zs k‖ ^ 2 ≤ 2 * B / R.μ * radius R B ℓ + ℓ ^ 2 := by
        have e : 2 * B / R.μ * radius R B ℓ + ℓ ^ 2 =
            (B * radius R B ℓ + R.μ * ℓ ^ 2 / 2) * (2 / R.μ) := by field_simp
        have e2 : ‖R.zs k‖ ^ 2 = (R.μ / 2 * ‖R.zs k‖ ^ 2) * (2 / R.μ) := by field_simp
        rw [e, e2]
        exact mul_le_mul_of_nonneg_right hzsq (div_pos two_pos hμ).le
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) (by norm_num)).mp hz2

def wmax (R : Run E) (B ℓ e1 e0 : ℝ) : ℝ := radius R B ℓ + gmax R B ℓ e1 e0 / R.L

lemma final_grad {R : Run E} {N : ℕ} {B ℓ e1 e0 : ℝ} (hℓ : 0 < ℓ) (hb : Bounds R b M N B e1 e0)
    (hθ : 8 * slack R B ℓ e1 e0 ≤ R.a * R.μ * ℓ ^ 2) {GN : E}
    (hGN : ‖GN - qgrad b M (R.xs N)‖ ≤ e1 * ‖R.xs N‖ + e0)
    (hc4 : ∀ k < N, R.μ * ‖gradientStep R.L (R.xs N) GN - R.ys k‖ ^ 2 ≤
      ⟪gradientStep R.L (R.xs N) GN - R.ys k,
        M (gradientStep R.L (R.xs N) GN - R.ys k)⟫) :
    ‖R.xs N‖ ≤ radius R B ℓ ∧
      ‖qgrad b M (R.xs N)‖ ≤ ‖GN‖ + slackR R B ℓ e1 e0 ∧
      ‖GN‖ ^ 2 ≤ 2 * R.L * ((1 - R.a) ^ N * (B * wmax R B ℓ e1 e0 +
        (R.L + R.μ) / 2 * wmax R B ℓ e1 e0 ^ 2) + 5 * slack R B ℓ e1 e0 / R.a) := by
  have hv := hb.valid
  have hrad := radius_bound hℓ hb hθ
  have hxN := (hrad N le_rfl).1
  have hrad1 : ℓ ≤ radius R B ℓ := by
    unfold radius
    have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.hB) hv.hμ.le
    linarith
  have hprev : ∀ j < N, ‖R.ys j‖ ≤ radius R B ℓ ∧ ‖R.xs j‖ ≤ radius R B ℓ := by
    intro j hj
    obtain ⟨h1, h2⟩ := hrad j hj.le
    exact ⟨norm_extrapolate_le hv.ha.le h1 h2, h1⟩
  have hok := fun j (hj : j < N) => steps_ok hℓ hb j hj (hprev j hj).1 (hprev j hj).2
  have heN : ‖GN - qgrad b M (R.xs N)‖ ≤ slackR R B ℓ e1 e0 := by
    refine hGN.trans ?_
    unfold slackR
    have := mul_le_mul_of_nonneg_left hxN hb.he1
    linarith
  have heR : 0 ≤ slackR R B ℓ e1 e0 := le_trans (norm_nonneg _) heN
  have hq : ‖qgrad b M (R.xs N)‖ ≤ B + R.L * radius R B ℓ := by
    unfold qgrad
    calc ‖b + M (R.xs N)‖ ≤ ‖b‖ + ‖M (R.xs N)‖ := norm_add_le _ _
      _ ≤ B + ‖M‖ * ‖R.xs N‖ := add_le_add hb.hb (M.le_opNorm _)
      _ ≤ B + R.L * radius R B ℓ := by
        gcongr
        · exact hv.hL.le
        · exact hb.norm
  have hGNb : ‖GN‖ ≤ gmax R B ℓ e1 e0 := by
    unfold gmax
    have := norm_sub_norm_le GN (qgrad b M (R.xs N))
    linarith
  have hgm : 0 ≤ gmax R B ℓ e1 e0 := le_trans (norm_nonneg _) hGNb
  set w := gradientStep R.L (R.xs N) GN
  have hw : ‖w‖ ≤ wmax R B ℓ e1 e0 := by
    unfold wmax
    simp only [w, gradientStep]
    calc ‖R.xs N - R.L⁻¹ • GN‖ ≤ ‖R.xs N‖ + ‖R.L⁻¹ • GN‖ := norm_sub_le _ _
      _ ≤ radius R B ℓ + gmax R B ℓ e1 e0 / R.L := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hv.hL, ← div_eq_inv_mul]
        gcongr
        exact hv.hL.le
  have hwm : 0 ≤ wmax R B ℓ e1 e0 := le_trans (norm_nonneg _) hw
  have hsl : 0 ≤ slack R B ℓ e1 e0 := by
    unfold slack
    have : 0 ≤ 2 * gmax R B ℓ e1 e0 / R.L := div_nonneg (by linarith) hv.hL.le
    exact mul_nonneg heR (by linarith)
  have hS2w : ∀ k < N, quad b M (R.ys k) + ⟪R.Gs k, w - R.ys k⟫ +
      R.μ / 2 * ‖w - R.ys k‖ ^ 2 ≤ quad b M w + slack R B ℓ e1 e0 := by
    intro k hk
    have h1 := support_of_check hb.sym (hc4 k hk) (hok k hk).1
    have hd : ‖w - R.ys k‖ ≤ 2 * radius R B ℓ + gmax R B ℓ e1 e0 / R.L := by
      calc ‖w - R.ys k‖ ≤ ‖w‖ + ‖R.ys k‖ := norm_sub_le _ _
        _ ≤ wmax R B ℓ e1 e0 + radius R B ℓ := add_le_add hw (hprev k hk).1
        _ = _ := by unfold wmax; ring
    have : slackR R B ℓ e1 e0 * ‖w - R.ys k‖ ≤ slack R B ℓ e1 e0 := by
      unfold slack
      have h2 := mul_le_mul_of_nonneg_left hd heR
      have : 0 ≤ slackR R B ℓ e1 e0 * (2 * radius R B ℓ + gmax R B ℓ e1 e0 / R.L) := by
        have : 0 ≤ gmax R B ℓ e1 e0 / R.L := div_nonneg hgm hv.hL.le
        exact mul_nonneg heR (by linarith)
      have h3 : slackR R B ℓ e1 e0 * (2 * radius R B ℓ + gmax R B ℓ e1 e0 / R.L) ≤
          slackR R B ℓ e1 e0 * (4 * radius R B ℓ + 2 * gmax R B ℓ e1 e0 / R.L) := by
        apply mul_le_mul_of_nonneg_left _ heR
        have : 0 ≤ gmax R B ℓ e1 e0 / R.L := div_nonneg hgm hv.hL.le
        have : 2 * gmax R B ℓ e1 e0 / R.L = 2 * (gmax R B ℓ e1 e0 / R.L) := by ring
        linarith
      linarith
    linarith
  obtain ⟨hval, _⟩ := inexact_value (quad b M) R hv hsl w
    (fun j hj => (hok j hj).2.2.1) hS2w (fun j hj => (hok j hj).2.2.2.2)
  have hdesc := descent_quad hb.sym hv.hL hb.norm heN
  have hdesc' : slackR R B ℓ e1 e0 * ‖GN‖ / R.L ≤ slack R B ℓ e1 e0 := by
    unfold slack
    have : slackR R B ℓ e1 e0 * ‖GN‖ / R.L ≤ slackR R B ℓ e1 e0 * (2 * gmax R B ℓ e1 e0 / R.L) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ heR
      apply div_le_div_of_nonneg_right _ hv.hL.le
      linarith
    have : 0 ≤ slackR R B ℓ e1 e0 * (4 * radius R B ℓ) := mul_nonneg heR (by linarith)
    nlinarith
  have hC : quad b M 0 - quad b M w + R.μ / 2 * ‖w‖ ^ 2 ≤
      B * wmax R B ℓ e1 e0 + (R.L + R.μ) / 2 * wmax R B ℓ e1 e0 ^ 2 := by
    rw [quad_zero]
    unfold quad
    have h1 : -⟪b, w⟫ ≤ B * wmax R B ℓ e1 e0 := by
      have := neg_le_of_abs_le (abs_real_inner_le_norm b w)
      have : ‖b‖ * ‖w‖ ≤ B * wmax R B ℓ e1 e0 := mul_le_mul hb.hb hw (norm_nonneg _) hb.hB
      linarith
    have h2 : -(⟪w, M w⟫ / 2) ≤ R.L / 2 * wmax R B ℓ e1 e0 ^ 2 := by
      have : |⟪w, M w⟫| ≤ R.L * ‖w‖ ^ 2 := by
        calc _ ≤ ‖w‖ * ‖M w‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖w‖ * (R.L * ‖w‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact (M.le_opNorm w).trans (mul_le_mul_of_nonneg_right hb.norm (norm_nonneg _))
          _ = R.L * ‖w‖ ^ 2 := by ring
      have := neg_le_of_abs_le this
      have : ‖w‖ ^ 2 ≤ wmax R B ℓ e1 e0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      nlinarith [hv.hL]
    have h3 : R.μ / 2 * ‖w‖ ^ 2 ≤ R.μ / 2 * wmax R B ℓ e1 e0 ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hw 2
      have := hv.hμ
      nlinarith
    nlinarith
  refine ⟨hxN, ?_, ?_⟩
  · have := norm_sub_norm_le (qgrad b M (R.xs N)) GN
    rw [norm_sub_rev] at this
    linarith
  · have hpow : 0 ≤ (1 - R.a) ^ N := pow_nonneg (sub_nonneg.mpr hv.ha₁) N
    have hmul := mul_le_mul_of_nonneg_left hC hpow
    have h4 : slack R B ℓ e1 e0 ≤ slack R B ℓ e1 e0 / R.a := by
      rw [le_div_iff₀ hv.ha]
      nlinarith [hv.ha₁]
    have : ‖GN‖ ^ 2 / (2 * R.L) ≤
        (1 - R.a) ^ N * (B * wmax R B ℓ e1 e0 + (R.L + R.μ) / 2 * wmax R B ℓ e1 e0 ^ 2) +
          5 * slack R B ℓ e1 e0 / R.a := by
      have : 5 * slack R B ℓ e1 e0 / R.a = 4 * slack R B ℓ e1 e0 / R.a + slack R B ℓ e1 e0 / R.a := by
        ring
      linarith
    rwa [div_le_iff₀ (by have := hv.hL; positivity), mul_comm] at this

end

end LongTails.Proofs.ComparisonTrustQuadratic
