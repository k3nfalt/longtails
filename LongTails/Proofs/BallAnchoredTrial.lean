import LongTails.Proofs.BallAnchoredSearch

open scoped RealInnerProductSpace

namespace LongTails.Proofs.BallAnchoredTrial

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.HessianStableNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch

noncomputable section

variable {p : Public} {F : p.E → p.E} {S : p.E →L[ℝ] p.E}

def finalPoint (F : p.E → p.E) (k : ℕ) (A : ℝ) (z g : p.E) (a : ℝ) : p.E :=
  iter F a (wOf p A z a) (cOf p A z g a) (newtonCount k a ‖fderiv ℝ F (cOf p A z g a)‖)

lemma tolerance_pos (hreg : Regular p F S) (k : ℕ) : 0 < tolerance p k := by
  unfold tolerance; have := radius_pos hreg; positivity

lemma tolerance_le (hreg : Regular p F S) (k : ℕ) : tolerance p k ≤ radius p / 12 := by
  unfold tolerance
  have hr := radius_pos hreg
  have hk : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma final_close (hreg : Regular p F S) (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a) :
    (1 + 4 * a * ‖fderiv ℝ F (cOf p A z g a)‖) *
        ‖finalPoint F k A z g a - ballSol hreg A z g a ha‖ ≤ tolerance p k := by
  obtain ⟨hus, hvi⟩ := ballSol_spec hreg A z g ha
  have h := iter_accuracy hreg ha hus hvi k
  have hX : 0 < 1 + 4 * a * ‖fderiv ℝ F (cOf p A z g a)‖ := by positivity
  unfold finalPoint
  rw [le_div_iff₀ hX] at h
  linarith

lemma final_close' (hreg : Regular p F S) (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a) :
    ‖finalPoint F k A z g a - ballSol hreg A z g a ha‖ ≤ tolerance p k := by
  have h := final_close hreg k A z g ha
  have h1 : ‖finalPoint F k A z g a - ballSol hreg A z g a ha‖ ≤
      (1 + 4 * a * ‖fderiv ℝ F (cOf p A z g a)‖) *
        ‖finalPoint F k A z g a - ballSol hreg A z g a ha‖ := by
    have : 0 ≤ 4 * a * ‖fderiv ℝ F (cOf p A z g a)‖ := by positivity
    nlinarith [norm_nonneg (finalPoint F k A z g a - ballSol hreg A z g a ha)]
  linarith

lemma dhat_phi (hreg : Regular p F S) (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a) :
    |‖finalPoint F k A z g a - cOf p A z g a‖ - phi hreg A z g a ha| ≤ tolerance p k := by
  unfold phi
  have h := abs_norm_sub_norm_le (finalPoint F k A z g a - cOf p A z g a)
    (ballSol hreg A z g a ha - cOf p A z g a)
  rw [sub_sub_sub_cancel_right] at h
  exact h.trans (final_close' hreg k A z g ha)

lemma resolvent_zero (hreg : Regular p F S) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a)
    (hφ : phi hreg A z g a ha < radius p) :
    a • F (ballSol hreg A z g a ha) + ballSol hreg A z g a ha - wOf p A z a = 0 := by
  obtain ⟨-, hvi⟩ := ballSol_spec hreg A z g ha
  exact interior_zero hφ hvi

lemma final_residual (hreg : Regular p F S) (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a)
    (hφ : phi hreg A z g a ha < radius p) :
    ‖a • F (finalPoint F k A z g a) + finalPoint F k A z g a - wOf p A z a‖ ≤
      tolerance p k := by
  obtain ⟨hus, -⟩ := ballSol_spec hreg A z g ha
  have hz := resolvent_zero hreg A z g ha hφ
  have hus' : ‖ballSol hreg A z g a ha - cOf p A z g a‖ ≤ radius p := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hus; exact hus
  have hx : ‖finalPoint F k A z g a - cOf p A z g a‖ ≤ radius p := by
    unfold finalPoint
    obtain ⟨hus2, hvi2⟩ := ballSol_spec hreg A z g ha
    have := (iter_spec hreg ha hus2 hvi2 (newtonCount k a ‖fderiv ℝ F (cOf p A z g a)‖)).1
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    exact this
  exact (certificate_bound hreg ha hus' hx hz).trans (final_close hreg k A z g ha)

lemma resolvent_dist (hreg : Regular p F S) {xs : p.E} (hxs : F xs = 0) {a : ℝ} (ha : 0 < a)
    {u w : p.E} (hz : a • F u + u - w = 0) : ‖u - xs‖ ≤ ‖w - xs‖ := by
  have hm := monotone_F hreg u xs
  rw [hxs, sub_zero] at hm
  have e : w - xs = (u - xs) + a • F u := by rw [← sub_eq_zero.mp hz]; abel
  have h1 : ‖u - xs‖ ^ 2 ≤ ⟪w - xs, u - xs⟫ := by
    rw [e, inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left]
    have : 0 ≤ ⟪F u, u - xs⟫ := hm
    nlinarith [mul_nonneg ha.le this]
  have h2 := real_inner_le_norm (w - xs) (u - xs)
  rcases eq_or_lt_of_le (norm_nonneg (u - xs)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

lemma phi_le (hreg : Regular p F S) {xs : p.E} {Λ A : ℝ} {z g : p.E} (hR : Region p F xs Λ)
    (hO : OuterOK p xs Λ A z g) {a : ℝ} (ha : 0 < a) :
    phi hreg A z g a ha ≤ a * (2 * Λ * rho p) := by
  have h1 := phi_le_G hreg A z g ha
  rw [G_center p A z g a (F (cOf p A z g a))] at h1
  have hA := hO.A_nonneg
  have hc : ‖cOf p A z g a - xs‖ ≤ rho p := by
    have := c_dist hreg hR hO ha
    have hr := radius_pos hreg
    unfold rho; linarith
  have hFc := region_norm hreg hR hc
  have hAa : 0 < A + a := by linarith
  have hγ0 : 0 ≤ a * A / (A + a) := by positivity
  have hγ : a * A / (A + a) ≤ a := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc phi hreg A z g a ha ≤ ‖a • F (cOf p A z g a) - (a * A / (A + a)) • g‖ := h1
    _ ≤ ‖a • F (cOf p A z g a)‖ + ‖(a * A / (A + a)) • g‖ := norm_sub_le _ _
    _ = a * ‖F (cOf p A z g a)‖ + (a * A / (A + a)) * ‖g‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha,
        abs_of_nonneg hγ0]
    _ ≤ a * (Λ * rho p) + a * (Λ * rho p) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (hFc.trans (mul_le_mul_of_nonneg_left hc hR.Λ_nonneg)) ha.le)
        (mul_le_mul hγ hO.g_bound (norm_nonneg _) ha.le)
    _ = _ := by ring

lemma w_sub (p : Public) {A a a' : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (ha' : 0 < a') (z : p.E) :
    wOf p A z a - wOf p A z a' = (a / (A + a) - a' / (A + a')) • (p.x0 - z) := by
  have h1 : A / (A + a) = 1 - a / (A + a) := by
    have : A + a ≠ 0 := by linarith
    field_simp; ring
  have h2 : A / (A + a') = 1 - a' / (A + a') := by
    have : A + a' ≠ 0 := by linarith
    field_simp; ring
  unfold wOf
  rw [h1, h2]
  module

lemma phi_lip (hreg : Regular p F S) {xs : p.E} {Λ A : ℝ} {z g : p.E} (hR : Region p F xs Λ)
    (hO : OuterOK p xs Λ A z g) {a a' lo : ℝ} (hlo : 0 < lo) (hla : lo ≤ a) (hla' : lo ≤ a') :
    |phi hreg A z g a' (lt_of_lt_of_le hlo hla') - phi hreg A z g a (lt_of_lt_of_le hlo hla)| ≤
      |a - a'| * (2 * Λ * rho p + a' * Λ * ((2 * p.D + radius p) / lo + Λ * rho p)) := by
  have ha := lt_of_lt_of_le hlo hla
  have ha' := lt_of_lt_of_le hlo hla'
  have hA := hO.A_nonneg
  have hst := vi_stability hreg A z g ha ha'
  set us := ballSol hreg A z g a ha
  set c := cOf p A z g a
  set c' := cOf p A z g a'
  set w := wOf p A z a
  set w' := wOf p A z a'
  set y' := c' + (us - c) with hy'
  set β := a / (A + a)
  set β' := a' / (A + a')
  set γ := a * A / (A + a)
  set γ' := a' * A / (A + a')
  obtain ⟨hus, -⟩ := ballSol_spec hreg A z g ha
  have husc : ‖us - c‖ ≤ radius p := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hus; exact hus
  have hy'c : ‖y' - c'‖ ≤ radius p := by
    rw [hy', add_sub_cancel_left]; exact husc
  have hus_r := ball_in_region hreg hR hO ha husc
  have hy'_r := ball_in_region hreg hR hO ha' hy'c
  have hX : (a • F us + us - w) - (a' • F y' + y' - w') =
      (a - a') • F us + a' • (F us - F y') + (γ' - γ) • g := by
    have hc : c = w - γ • g := rfl
    have hc' : c' = w' - γ' • g := rfl
    rw [hy', hc, hc']
    module
  have hcc : us - y' = (β - β') • (p.x0 - z) - (γ - γ') • g := by
    have hc : c = w - γ • g := rfl
    have hc' : c' = w' - γ' • g := rfl
    have hww : w - w' = (β - β') • (p.x0 - z) := w_sub p hA ha ha' z
    rw [hy']
    calc us - (c' + (us - c)) = c - c' := by abel
      _ = (w - w') - (γ - γ') • g := by rw [hc, hc']; module
      _ = _ := by rw [hww]
  have hβ : |β - β'| ≤ |a - a'| / lo := beta_diff hA hlo hla hla'
  have hγ : |γ - γ'| ≤ |a - a'| := gamma_diff hA ha ha'
  have hx0z : ‖p.x0 - z‖ ≤ 2 * p.D + radius p := by
    have h1 : ‖p.x0 - z‖ ≤ ‖p.x0 - xs‖ + ‖z - xs‖ := by
      calc ‖p.x0 - z‖ = ‖(p.x0 - xs) - (z - xs)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have := hR.x0_dist
    have := hO.z_dist
    have := radius_pos hreg
    linarith
  have hΛ := hR.Λ_nonneg
  have hρ : 0 ≤ rho p := by unfold rho; have := radius_pos hreg; have := hreg.D_pos; positivity
  have hFus : ‖F us‖ ≤ Λ * rho p :=
    (region_norm hreg hR hus_r).trans (mul_le_mul_of_nonneg_left hus_r hΛ)
  have hlip := region_lip hreg hR hus_r hy'_r
  have hdist : ‖us - y'‖ ≤ |a - a'| * ((2 * p.D + radius p) / lo + Λ * rho p) := by
    rw [hcc]
    calc ‖(β - β') • (p.x0 - z) - (γ - γ') • g‖
        ≤ ‖(β - β') • (p.x0 - z)‖ + ‖(γ - γ') • g‖ := norm_sub_le _ _
      _ = |β - β'| * ‖p.x0 - z‖ + |γ - γ'| * ‖g‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (|a - a'| / lo) * (2 * p.D + radius p) + |a - a'| * (Λ * rho p) := by
        gcongr
        exact hO.g_bound
      _ = _ := by ring
  have hg := hO.g_bound
  calc |phi hreg A z g a' ha' - phi hreg A z g a ha|
      ≤ ‖(a • F us + us - w) - (a' • F y' + y' - w')‖ := hst
    _ = ‖(a - a') • F us + a' • (F us - F y') + (γ' - γ) • g‖ := by rw [hX]
    _ ≤ ‖(a - a') • F us‖ + ‖a' • (F us - F y')‖ + ‖(γ' - γ) • g‖ := norm_add₃_le
    _ = |a - a'| * ‖F us‖ + a' * ‖F us - F y'‖ + |γ' - γ| * ‖g‖ := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos ha']
    _ ≤ |a - a'| * (Λ * rho p) + a' * (Λ * (|a - a'| * ((2 * p.D + radius p) / lo +
          Λ * rho p))) + |a - a'| * (Λ * rho p) := by
      have t1 : |a - a'| * ‖F us‖ ≤ |a - a'| * (Λ * rho p) :=
        mul_le_mul_of_nonneg_left hFus (abs_nonneg _)
      have t2 : a' * ‖F us - F y'‖ ≤
          a' * (Λ * (|a - a'| * ((2 * p.D + radius p) / lo + Λ * rho p))) :=
        mul_le_mul_of_nonneg_left (hlip.trans (mul_le_mul_of_nonneg_left hdist hΛ)) ha'.le
      have t3 : |γ' - γ| * ‖g‖ ≤ |a - a'| * (Λ * rho p) :=
        mul_le_mul (by rw [abs_sub_comm]; exact hγ) hg (norm_nonneg _) (abs_nonneg _)
      linarith
    _ = _ := by ring

end

end LongTails.Proofs.BallAnchoredTrial
