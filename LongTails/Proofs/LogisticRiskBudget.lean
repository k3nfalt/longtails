import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import LongTails.Setups.TwoTapLogisticSeparation

open scoped BigOperators

namespace LongTails.Proofs.LogisticRiskBudget

open LongTails.Setups.TwoTapLogisticSeparation (loss)

lemma loss_pos (m : ℝ) : 0 < loss m := by
  apply Real.log_pos
  linarith [Real.exp_pos (-m)]

lemma posterior_le_loss (m : ℝ) : Real.sigmoid (-m) ≤ loss m := by
  have hp : 0 < 1 + Real.exp (-m) := by positivity
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at h
  have hq : Real.sigmoid (-m) = 1-(1+Real.exp (-m))⁻¹ := by
    simp only [Real.sigmoid, neg_neg, Real.exp_neg]
    field_simp
    ring
  rw [hq]
  unfold loss
  linarith

lemma loss_step (m s : ℝ) (hs : |s| ≤ 1) :
    loss (m+s) - loss m ≤ Real.sigmoid (-m) * (-s+s^2) := by
  have hp : 0 < 1+Real.exp (-m) := by positivity
  have hp' : 0 < 1+Real.exp (-(m+s)) := by positivity
  have hid : (1+Real.exp (-(m+s)))/(1+Real.exp (-m)) - 1 =
      Real.sigmoid (-m) * (Real.exp (-s)-1) := by
    rw [neg_add, Real.exp_add, Real.sigmoid, neg_neg, Real.exp_neg m]
    field_simp
    ring
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp' hp)
  rw [Real.log_div hp'.ne' hp.ne', hid] at h1
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -s) (by simpa using hs))).2
  change Real.log (1+Real.exp (-(m+s))) - Real.log (1+Real.exp (-m)) ≤ _
  exact h1.trans (mul_le_mul_of_nonneg_left (by nlinarith) (Real.sigmoid_nonneg _))

lemma work_le_tangent (m y : ℝ) :
    m * Real.sigmoid (-m) + loss m ≤ y * Real.sigmoid (-m) + loss y := by
  let q := Real.sigmoid (-m)
  have hq : 0 ≤ q := (Real.sigmoid_pos _).le
  have hq' : q ≤ 1 := (Real.sigmoid_lt_one _).le
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (m-y))
    (sub_nonneg.mpr hq') hq (show (1-q)+q=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have hfrac : 1-q+q*Real.exp (m-y) = (1+Real.exp (-y))/(1+Real.exp (-m)) := by
    dsimp [q, Real.sigmoid]
    rw [neg_neg, Real.exp_sub, Real.exp_neg, Real.exp_neg]
    field_simp
    ring
  rw [hfrac] at h
  have hl := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_div (by positivity) (by positivity)] at hl
  change m*q + Real.log (1+Real.exp (-m)) ≤ y*q + Real.log (1+Real.exp (-y))
  linarith

lemma work_le_scaled_risk (m F : ℝ) (hF : 0 < F) :
    m * Real.sigmoid (-m) + loss m ≤
      Real.log (2/F) * Real.sigmoid (-m) + F/2 := by
  apply (work_le_tangent m _).trans
  apply add_le_add_right
  unfold loss
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  linarith [Real.log_le_sub_one_of_pos (show 0 < 1+F/2 by positivity)]

lemma mean_work_le {ι : Type*} [Fintype ι] (w m : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (F : ℝ)
    (hF : 0 < F) (hmean : ∑ i, w i * loss (m i) = F) :
    ∑ i, w i * (m i * Real.sigmoid (-m i)) ≤
      Real.log (2/F) * (∑ i, w i * Real.sigmoid (-m i)) - F/2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (work_le_scaled_risk (m i) F hF) (hw i)
  simp only [mul_add, Finset.sum_add_distrib, hmean] at h
  have he : (∑ i, w i * (Real.log (2/F) * Real.sigmoid (-m i))) =
      Real.log (2/F) * (∑ i, w i * Real.sigmoid (-m i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he, ← Finset.sum_mul, hs, one_mul] at h
  linarith

lemma risk_pays_growth (F Q L : ℝ) (hF : 0 < F) :
    4 * (Q * L - F/2) ≤ 2 * (Q*L)^2/F := by
  apply (le_div_iff₀ hF).2
  nlinarith [sq_nonneg (Q*L-F)]

lemma radius_growth_charge {F nextF Q L A nextA η g2 u γ : ℝ}
    (hF : 0 < F) (hη : 0 < η) (hu : 0 < u) (hγ : 0 < γ)
    (hdom : γ^2 * u * Q^2 ≤ g2)
    (hdes : η*g2 ≤ 2*(F-nextF))
    (hwork : nextA-A ≤ 4*η*(Q*L-F/2)) :
    (nextA-A) * (γ^2*u*F) ≤ 4 * L^2 * (F-nextF) := by
  have hpay := (le_div_iff₀ hF).mp (risk_pays_growth F Q L hF)
  calc
    _ ≤ (4*η*(Q*L-F/2))*(γ^2*u*F) :=
      mul_le_mul_of_nonneg_right hwork (by positivity)
    _ = (4*(Q*L-F/2)*F)*(η*γ^2*u) := by ring
    _ ≤ (2*(Q*L)^2)*(η*γ^2*u) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = (2*L^2*η)*(γ^2*u*Q^2) := by ring
    _ ≤ (2*L^2*η)*g2 := mul_le_mul_of_nonneg_left hdom (by positivity)
    _ = (2*L^2)*(η*g2) := by ring
    _ ≤ (2*L^2)*(2*(F-nextF)) := mul_le_mul_of_nonneg_left hdes (by positivity)
    _ = _ := by ring

lemma log_cube_pays_decrease {F f : ℝ} (hf : 0 < f) (hle : f ≤ F) (hF : F ≤ 2) :
    (Real.log (2/F))^2 * ((F-f)/F) ≤
      (Real.log (2/f))^3 - (Real.log (2/F))^3 := by
  have hp : 0 < F := hf.trans_le hle
  have ha : 0 ≤ Real.log (2/F) := Real.log_nonneg ((le_div_iff₀ hp).2 (by linarith))
  have hd := Real.log_le_sub_one_of_pos (div_pos hf hp)
  rw [Real.log_div hf.ne' hp.ne'] at hd
  have hlog : Real.log (2/f) - Real.log (2/F) = Real.log F - Real.log f := by
    rw [Real.log_div (by norm_num) hf.ne', Real.log_div (by norm_num) hp.ne']
    ring
  have hlin : (F-f)/F ≤ Real.log (2/f)-Real.log (2/F) := by
    rw [hlog, sub_div, div_self hp.ne']
    linarith
  have hab : 0 ≤ Real.log (2/f)-Real.log (2/F) :=
    (div_nonneg (sub_nonneg.mpr hle) hp.le).trans hlin
  have hb : 0 ≤ Real.log (2/f) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hlin (sq_nonneg (Real.log (2/F)))
  nlinarith [mul_nonneg (mul_nonneg ha hb) hab,
    mul_nonneg (sq_nonneg (Real.log (2/f))) hab]

lemma radius_square_step {F f Q A B g2 u γ η κ : ℝ}
    (hf : 0 < f) (hle : f ≤ F) (hF : F ≤ 2)
    (hη : 0 < η) (hu : 0 < u) (hγ : 0 < γ) (hκ : 0 ≤ κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : A+B ≤ κ*u)
    (hdom : γ^2*u*Q^2 ≤ g2)
    (hdes : η*g2 ≤ 2*(F-f))
    (hwork : B-A ≤ 4*η*(Q*Real.log (2/F)-F/2)) :
    γ^2 * (B^2-A^2) ≤ 4*κ*((Real.log (2/f))^3-(Real.log (2/F))^3) := by
  have hp := hf.trans_le hle
  have ht := radius_growth_charge hp hη hu hγ hdom hdes hwork
  have hcube := log_cube_pays_decrease hf hle hF
  by_cases h : A ≤ B
  · have hk := mul_le_mul_of_nonneg_left hs (mul_nonneg (sq_nonneg γ) (sub_nonneg.mpr h))
    have h1 : γ^2*(B-A)*u ≤ 4*(Real.log (2/F))^2*((F-f)/F) := by
      field_simp [hp.ne']
      nlinarith only [ht]
    calc
      _ = γ^2*(B-A)*(A+B) := by ring
      _ ≤ γ^2*(B-A)*(κ*u) := hk
      _ = κ*(γ^2*(B-A)*u) := by ring
      _ ≤ κ*(4*(Real.log (2/F))^2*((F-f)/F)) := mul_le_mul_of_nonneg_left h1 hκ
      _ = 4*κ*((Real.log (2/F))^2*((F-f)/F)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by positivity)
  · have hdiff : B^2-A^2 ≤ 0 := by nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (add_nonneg hA hB)]
    have hcube0 := (mul_nonneg (sq_nonneg (Real.log (2/F))) (div_nonneg (sub_nonneg.mpr hle) hp.le)).trans hcube
    exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg γ) hdiff).trans (by positivity)

lemma radius_floor {U V D p : ℝ} (hp : p^2 ≤ U*V)
    (hD : V-U ≤ D) (hDn : 0 ≤ D) (hU : 0 ≤ U) :
    min 1 (p^2/(1+D)) ≤ U := by
  by_cases h : 1 ≤ U
  · exact (min_le_left _ _).trans h
  · apply (min_le_right _ _).trans
    apply (div_le_iff₀ (by positivity)).2
    exact hp.trans (mul_le_mul_of_nonneg_left (by linarith) hU)

lemma energy_controls_curvature {F A E K : ℝ}
    (hF : 0 < F) (hF' : F ≤ 1) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (h : A^2 ≤ E^2 + K^2 * (Real.log (2/F))^3) : F*A ≤ E+4*K := by
  have hL : 0 ≤ Real.log (2/F) := Real.log_nonneg ((le_div_iff₀ hF).2 (by linarith))
  have hsmall := Real.pow_div_factorial_le_exp _ hL 3
  rw [Real.exp_log (by positivity)] at hsmall
  norm_num at hsmall
  have h1 : (Real.log (2/F))^3 * F ≤ 12 := by
    have haux := (le_div_iff₀ hF).mp hsmall
    linarith
  have h2 : F^2 * (Real.log (2/F))^3 ≤ 12 := by
    have hh := mul_le_mul_of_nonneg_right h1 hF.le
    nlinarith only [hh, hF']
  have he : (F*E)^2 ≤ E^2 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa using mul_le_mul_of_nonneg_right hF' hE
  have hbound := mul_le_mul_of_nonneg_left h (sq_nonneg F)
  have hrem := mul_le_mul_of_nonneg_left h2 (sq_nonneg K)
  nlinarith only [hbound, hrem, he, mul_nonneg hE hK, hF, hK, hE,
    sq_nonneg (F*A-(E+4*K)), sq_nonneg K]

lemma risk_step_of_margins {ι : Type*} [Fintype ι]
    (p m s : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∀ i, |s i| ≤ 1)
    (η G C : ℝ)
    (hmean : η*G*(1-C) ≤ ∑ i, (p i*Real.sigmoid (-m i))*s i)
    (hvar : ∑ i, (p i*Real.sigmoid (-m i))*(s i)^2 ≤ η*G*(1/2-C)) :
    (∑ i, p i*loss (m i+s i)) ≤ (∑ i, p i*loss (m i)) - η*G/2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (loss_step (m i) (s i) (hs i)) (hp i)
  simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, mul_add,
    Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib] at hh
  linarith only [hh, hvar, hmean]

lemma reciprocal_progress {F f η K : ℝ} (hf : 0 < f) (hle : f ≤ F)
    (hη : 0 ≤ η) (hK : 0 < K) (h : η*F^2 ≤ K*(F-f)) :
    η/K ≤ 1/f-1/F := by
  have hp := hf.trans_le hle
  field_simp [hK.ne', hf.ne', hp.ne']
  have hh := mul_le_mul_of_nonneg_left hle (mul_nonneg hη hp.le)
  nlinarith only [h, hh]

lemma half_margin_of_loss (m : ℝ) : Real.log 2 - loss m ≤ m/2 := by
  have hh := work_le_tangent 0 m
  simp [loss, Real.sigmoid] at hh ⊢
  linarith

lemma loss_le_margin (m : ℝ) : loss m ≤ Real.log 2 + |m| := by
  have ha : 1 ≤ Real.exp |m| := Real.one_le_exp (abs_nonneg _)
  have hb := Real.exp_le_exp.mpr (neg_le_abs m)
  rw [← Real.log_exp |m|, ← Real.log_mul (by norm_num) (Real.exp_pos _).ne']
  exact Real.log_le_log (by positivity) (by linarith)

lemma loss_le_weighted_posterior (m : ℝ) :
    loss m ≤ (1+loss m)*Real.sigmoid (-m) := by
  have ht : loss m ≤ Real.exp (-m) := by
    unfold loss
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1+Real.exp (-m) by positivity)]
  have hp : 0 < 1+Real.exp (-m) := by positivity
  have hq : Real.sigmoid (-m) = Real.exp (-m)/(1+Real.exp (-m)) := by
    simp only [Real.sigmoid, neg_neg, Real.exp_neg]
    field_simp
    ring
  rw [hq, ← mul_div_assoc]
  apply (le_div_iff₀ hp).2
  linarith

lemma risk_from_posterior {ι : Type*} [Fintype ι] (p m : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (b : ℝ) (hm : ∀ i, |m i| ≤ b) :
    (∑ i, p i * loss (m i)) ≤
      (1+Real.log 2+b)*(∑ i, p i*Real.sigmoid (-m i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := loss_le_weighted_posterior (m i)
  have ht : 1+loss (m i) ≤ 1+Real.log 2+b :=
    by linarith [loss_le_margin (m i), hm i]
  have hb := h.trans (mul_le_mul_of_nonneg_right ht (Real.sigmoid_nonneg _))
  calc _ ≤ p i*((1+Real.log 2+b)*Real.sigmoid (-m i)) :=
         mul_le_mul_of_nonneg_left hb (hp i)
       _ = _ := by ring

lemma mean_loss_to_layer_product {ι : Type*} [Fintype ι] (p m : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Real.log 2 - ∑ i, p i * loss (m i) ≤ (∑ i, p i*m i)/2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (half_margin_of_loss (m i)) (hp i)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul,
    ← mul_div_assoc, ← Finset.sum_div] at h
  exact h

lemma logit_step_bounds {η R z Q G l c : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hz : 0 ≤ z) (hQ : 0 ≤ Q) (hG : 0 ≤ G) (hQ1 : Q ≤ 1)
    (hstep : η*R ≤ 1/8) (hcurv : η*R^2*z*Q ≤ 1/32)
    (hg : G ≤ 4*R^2*z*Q^2) (hl : l^2 ≤ 4*R^2*z*G) (hc : |c| ≤ R*G) :
    |η*l+η^2*c| ≤ 1 ∧ (η*l+η^2*c)^2 ≤ 9*η^2*R^2*z*G := by
  let Z := Real.sqrt z
  let g := Real.sqrt G
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hgn : 0 ≤ g := Real.sqrt_nonneg _
  have hZZ : Z^2=z := Real.sq_sqrt hz
  have hgg : g^2=G := Real.sq_sqrt hG
  have hg' : g ≤ 2*R*Z*Q := by
    apply (sq_le_sq₀ hgn (by positivity)).mp
    calc g^2 = G := hgg
         _ ≤ 4*R^2*z*Q^2 := hg
         _ = _ := by rw [← hZZ]; ring
  have hl' : |l| ≤ 2*R*Z*g := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    calc _ ≤ 4*R^2*z*G := hl
         _ = _ := by rw [← hZZ, ← hgg]; ring
  have hqsmall : 2*(η*R*Q) ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left hQ1 (mul_nonneg hη hR)
    nlinarith only [ht, hstep]
  have haux : η*R*g ≤ R*Z := by
    calc _ ≤ η*R*(2*R*Z*Q) := mul_le_mul_of_nonneg_left hg' (mul_nonneg hη hR)
         _ = (2*(η*R*Q))*(R*Z) := by ring
         _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hqsmall (mul_nonneg hR hZ)
  have hbig : |η*l+η^2*c| ≤ 3*η*R*Z*g := by
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_of_nonneg hη, abs_of_nonneg (sq_nonneg η)]
    have ha := mul_le_mul_of_nonneg_right haux (mul_nonneg hη hgn)
    have hb := mul_le_mul_of_nonneg_left hc (sq_nonneg η)
    rw [← hgg] at hb
    nlinarith only [ha, hb, mul_le_mul_of_nonneg_left hl' hη]
  constructor
  · apply hbig.trans
    have hb := mul_le_mul_of_nonneg_left hg' (show 0 ≤ 3*η*R*Z by positivity)
    rw [← hZZ] at hcurv
    nlinarith only [hb, hcurv]
  · have hb := pow_le_pow_left₀ (abs_nonneg _) hbig 2
    rw [sq_abs] at hb
    rw [← hgg, ← hZZ]
    nlinarith only [hb]

end LongTails.Proofs.LogisticRiskBudget
