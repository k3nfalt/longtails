import LongTails.Proofs.SecondOrderMintyChainBounds
import LongTails.Proofs.LocalizedMonotoneRadial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SecondOrderMintyInstance

open SecondOrderMintyChain LocalizedMonotoneRadial ContinuousLinearMap

noncomputable def field {d n : ℕ} (κ r b : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    Space d :=
  chain κ r π (radial b x) + κ • (x - radial b x)

noncomputable def jacobian {d n : ℕ} (κ r b : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    Space d →L[ℝ] Space d :=
  (chainJacobian κ r π (radial b x)).comp (radialJacobian b x) +
    κ • (ContinuousLinearMap.id ℝ (Space d) - radialJacobian b x)

lemma field_hasFDerivAt {d n : ℕ} (κ r b : ℝ) (hr : 0 < r) (hb : 0 < b)
    (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    HasFDerivAt (field κ r b π) (jacobian κ r b π x) x := by
  have hc := (chain_hasFDerivAt κ r hr π (radial b x)).comp x (radial_hasFDerivAt b hb x)
  have hw := ((hasFDerivAt_id x).sub (radial_hasFDerivAt b hb x)).const_smul κ
  exact hc.add hw

lemma field_lipschitz {d n : ℕ} (κ r b : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b)
    (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    ‖field κ r b π x - field κ r b π y‖ ≤ 14 * κ * ‖x - y‖ := by
  have hp := radial_nonexpansive b hb x y
  have hc := chain_lipschitz κ r hκ hr π (radial b x) (radial b y)
  have he : field κ r b π x - field κ r b π y =
      (chain κ r π (radial b x) - chain κ r π (radial b y)) +
        κ • ((x - y) - (radial b x - radial b y)) := by
    simp only [field, smul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖chain κ r π (radial b x) - chain κ r π (radial b y)‖ +
        κ * (‖x - y‖ + ‖radial b x - radial b y‖) := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_of_nonneg hκ]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hκ
    _ ≤ 12 * κ * ‖x - y‖ + κ * (‖x - y‖ + ‖x - y‖) := by
      have h1 := hc.trans (mul_le_mul_of_nonneg_left hp (by positivity))
      have h2 := mul_le_mul_of_nonneg_left (add_le_add_left hp ‖x - y‖) hκ
      linarith
    _ = 14 * κ * ‖x - y‖ := by ring

lemma jacobian_difference {d n : ℕ} (κ r b : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b)
    (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    ‖jacobian κ r b π x - jacobian κ r b π y‖ ≤
      (256 * κ / r + 416 * κ / b) * ‖x - y‖ := by
  set Cx := chainJacobian κ r π (radial b x)
  set Cy := chainJacobian κ r π (radial b y)
  set Px := radialJacobian b x
  set Py := radialJacobian b y
  have he : jacobian κ r b π x - jacobian κ r b π y =
      (Cx - Cy).comp Px + Cy.comp (Px - Py) - κ • (Px - Py) := by
    simp only [jacobian, Cx, Cy, Px, Py, comp_sub, sub_comp, smul_sub]
    abel
  have hC := (chainJacobian_difference κ r hκ hr π (radial b x) (radial b y)).trans
    (mul_le_mul_of_nonneg_left (radial_nonexpansive b hb x y) (by positivity))
  have hP := radialJacobian_difference b hb x y
  have hPx : ‖Px‖ ≤ 1 := radialJacobian_norm_le b hb x
  have hCy : ‖Cy‖ ≤ 12 * κ := chainJacobian_norm κ r hκ π _
  rw [he]
  have h1 : ‖(Cx - Cy).comp Px‖ ≤ 256 * κ / r * ‖x - y‖ :=
    (opNorm_comp_le _ _).trans (by
      have := mul_le_mul hC hPx (norm_nonneg _) (by positivity)
      linarith)
  have h2 : ‖Cy.comp (Px - Py)‖ ≤ 12 * κ * (32 / b * ‖x - y‖) :=
    (opNorm_comp_le _ _).trans (mul_le_mul hCy hP (norm_nonneg _) (by positivity))
  have h3 : ‖κ • (Px - Py)‖ ≤ κ * (32 / b * ‖x - y‖) := by
    rw [norm_smul, Real.norm_of_nonneg hκ]
    exact mul_le_mul_of_nonneg_left hP hκ
  calc
    _ ≤ ‖(Cx - Cy).comp Px‖ + ‖Cy.comp (Px - Py)‖ + ‖κ • (Px - Py)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ 256 * κ / r * ‖x - y‖ + 12 * κ * (32 / b * ‖x - y‖) + κ * (32 / b * ‖x - y‖) := by
      linarith
    _ = _ := by ring

lemma field_inner {d n : ℕ} (κ r b R : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (hT : ‖target r π‖ ≤ R)
    (hG : ∀ y, ‖chain κ r π y‖ ≤ κ * R) (x : Space d) (s : ℝ) (hs1 : s ≤ 1)
    (hψ : radial b x = s • x) :
    κ * (1 - s) * ‖x‖ * (‖x‖ - 2 * R) ≤ ⟪field κ r b π x, x - target r π⟫ := by
  set T := target r π
  have hfield : field κ r b π x = chain κ r π (s • x) + (κ * (1 - s)) • x := by
    simp only [field, hψ]
    rw [show x - s • x = (1 - s) • x by rw [sub_smul, one_smul], smul_smul]
  have hsplit : x - T = (s • x - T) + (1 - s) • x := by
    rw [sub_smul, one_smul]; abel
  rw [hfield, inner_add_left]
  have hm := chain_minty κ r hκ hr π (s • x)
  have hc : -(‖chain κ r π (s • x)‖ * ‖x‖) ≤ ⟪chain κ r π (s • x), x⟫ := by
    have := abs_real_inner_le_norm (chain κ r π (s • x)) x
    linarith [neg_abs_le ⟪chain κ r π (s • x), x⟫]
  have h1s : 0 ≤ 1 - s := by linarith
  have hfirst : -((1 - s) * (κ * R * ‖x‖)) ≤ ⟪chain κ r π (s • x), x - T⟫ := by
    rw [hsplit, inner_add_right, inner_smul_right]
    have hb := mul_le_mul_of_nonneg_right (hG (s • x)) (norm_nonneg x)
    have := mul_le_mul_of_nonneg_left (show -(κ * R * ‖x‖) ≤ ⟪chain κ r π (s • x), x⟫ by
      linarith) h1s
    nlinarith
  have hxT : ⟪x, T⟫ ≤ ‖x‖ * R := (real_inner_le_norm x T).trans
    (mul_le_mul_of_nonneg_left hT (norm_nonneg x))
  have hsecond : (κ * (1 - s)) * (‖x‖ ^ 2 - ‖x‖ * R) ≤ ⟪(κ * (1 - s)) • x, x - T⟫ := by
    rw [inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

lemma chain_norm_le {d n : ℕ} (κ r R : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hR : 0 ≤ R)
    (π : Fin (n + 1) ↪ Fin d) (hnr : (n + 1) * r ^ 2 ≤ R ^ 2) (y : Space d) :
    ‖chain κ r π y‖ ≤ κ * R := by
  have h := chain_norm_sq κ r hκ hr π y
  have h2 : ‖chain κ r π y‖ ^ 2 ≤ (κ * R) ^ 2 := by
    calc
      _ ≤ (n + 1) * (κ * r) ^ 2 := h
      _ = κ ^ 2 * ((n + 1) * r ^ 2) := by ring
      _ ≤ κ ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hnr (sq_nonneg κ)
      _ = (κ * R) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h2

lemma target_norm_le {d n : ℕ} (r R : ℝ) (hR : 0 ≤ R) (π : Fin (n + 1) ↪ Fin d)
    (hnr : (n + 1) * r ^ 2 ≤ R ^ 2) : ‖target r π‖ ≤ R := by
  have h : ‖target r π‖ ^ 2 ≤ R ^ 2 := by rw [target_norm_sq]; exact hnr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR (by norm_num)).mp h

lemma field_minty {d n : ℕ} (κ r b R : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b)
    (hR : 0 ≤ R) (hbR : 2 * R ≤ b) (π : Fin (n + 1) ↪ Fin d)
    (hnr : (n + 1) * r ^ 2 ≤ R ^ 2) (x : Space d) :
    0 ≤ ⟪field κ r b π x, x - target r π⟫ := by
  by_cases hx : ‖x‖ ≤ b
  · have hψ := radial_eq_self b x hx
    have : field κ r b π x = chain κ r π x := by simp [field, hψ]
    rw [this]
    exact chain_minty κ r hκ hr π x
  · obtain ⟨s, hs0, hs1, hψ⟩ := radial_contraction_factor b hb x
    have h := field_inner κ r b R hκ hr π (target_norm_le r R hR π hnr)
      (chain_norm_le κ r R hκ hr hR π hnr) x s hs1 hψ
    have : 0 ≤ κ * (1 - s) * ‖x‖ * (‖x‖ - 2 * R) := by
      have : 0 ≤ ‖x‖ - 2 * R := by linarith
      have : 0 ≤ 1 - s := by linarith
      positivity
    linarith

lemma field_target {d n : ℕ} (κ r b R : ℝ) (hR : 0 ≤ R) (hbR : R ≤ b)
    (π : Fin (n + 1) ↪ Fin d) (hnr : (n + 1) * r ^ 2 ≤ R ^ 2) :
    field κ r b π (target r π) = 0 := by
  have hψ := radial_eq_self b (target r π) ((target_norm_le r R hR π hnr).trans hbR)
  simp [field, hψ, chain_target]

lemma field_floor {d n : ℕ} (κ r b R : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hb : 0 < b)
    (hR : 0 ≤ R) (hbR : 8 * R ≤ b) (π : Fin (n + 1) ↪ Fin d)
    (hnr : (n + 1) * r ^ 2 ≤ R ^ 2) (x : Space d) (i : Fin (n + 1))
    (hi : radial b x (π i) ≤ r / 2) :
    3 / 10 * (κ * r) ≤ ‖field κ r b π x‖ := by
  set t := ‖x - radial b x‖ with ht
  have hkr : 0 ≤ κ * r := by positivity
  have hA : 3 / 4 * (κ * r) - κ * t ≤ ‖field κ r b π x‖ := by
    have hf := chain_floor κ r hκ hr π (radial b x) i hi
    have hn : ‖chain κ r π (radial b x)‖ - ‖κ • (x - radial b x)‖ ≤ ‖field κ r b π x‖ := by
      have he : chain κ r π (radial b x) = field κ r b π x - κ • (x - radial b x) := by
        simp [field]
      have := norm_sub_le (field κ r b π x) (κ • (x - radial b x))
      rw [← he] at this
      linarith
    rw [norm_smul, Real.norm_of_nonneg hκ] at hn
    linarith
  by_cases hsmall : t ≤ 9 / 20 * r
  · nlinarith
  · push Not at hsmall
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) hsmall
    have hxb : b < ‖x‖ := by
      by_contra hc
      push Not at hc
      rw [ht, radial_eq_self b x hc, sub_self, norm_zero] at ht0
      exact lt_irrefl _ ht0
    obtain ⟨s, hs0, hs1, hψ⟩ := radial_contraction_factor b hb x
    have hts : t = (1 - s) * ‖x‖ := by
      rw [ht, hψ, show x - s • x = (1 - s) • x by rw [sub_smul, one_smul], norm_smul,
        Real.norm_of_nonneg (by linarith)]
    have hinner := field_inner κ r b R hκ hr π (target_norm_le r R hR π hnr)
      (chain_norm_le κ r R hκ hr hR π hnr) x s hs1 hψ
    have hupper : ⟪field κ r b π x, x - target r π⟫ ≤ ‖field κ r b π x‖ * (‖x‖ + R) := by
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have := target_norm_le r R hR π hnr
      exact (norm_sub_le _ _).trans (by linarith)
    have hx8 : 8 * R ≤ ‖x‖ := by linarith
    have hratio : 2 / 3 * (‖x‖ + R) ≤ ‖x‖ - 2 * R := by linarith
    have hB : 2 / 3 * (κ * t) * (‖x‖ + R) ≤ ‖field κ r b π x‖ * (‖x‖ + R) := by
      have hkt : 0 ≤ κ * t := by positivity
      have := mul_le_mul_of_nonneg_left hratio hkt
      have e : κ * (1 - s) * ‖x‖ * (‖x‖ - 2 * R) = κ * t * (‖x‖ - 2 * R) := by rw [hts]; ring
      nlinarith
    have hpos : 0 < ‖x‖ + R := by linarith
    have hB' : 2 / 3 * (κ * t) ≤ ‖field κ r b π x‖ := le_of_mul_le_mul_right hB hpos
    nlinarith

end LongTails.Proofs.SecondOrderMintyInstance
