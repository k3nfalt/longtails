import LongTails.Proofs.BallAnchoredInner

open scoped RealInnerProductSpace
open Set

namespace LongTails.Proofs.BallAnchoredSearch

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.HessianStableNewton
open LongTails.Proofs.BallAnchoredInner

noncomputable section

variable {p : Public} {F : p.E → p.E} {S : p.E →L[ℝ] p.E}

def wOf (p : Public) (A : ℝ) (z : p.E) (a : ℝ) : p.E :=
  (a / (A + a)) • p.x0 + (A / (A + a)) • z

def cOf (p : Public) (A : ℝ) (z g : p.E) (a : ℝ) : p.E :=
  wOf p A z a - (a * A / (A + a)) • g

def ballSol (hreg : Regular p F S) (A : ℝ) (z g : p.E) (a : ℝ) (ha : 0 < a) : p.E :=
  Classical.choose (ball_vi_exists hreg ha (wOf p A z a) (cOf p A z g a))

lemma ballSol_spec (hreg : Regular p F S) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a) :
    ballSol hreg A z g a ha ∈ Metric.closedBall (cOf p A z g a) (radius p) ∧
      ∀ v ∈ Metric.closedBall (cOf p A z g a) (radius p),
        0 ≤ ⟪a • F (ballSol hreg A z g a ha) + ballSol hreg A z g a ha - wOf p A z a,
          v - ballSol hreg A z g a ha⟫ := by
  unfold ballSol
  have h := Classical.choose_spec (ball_vi_exists hreg ha (wOf p A z a) (cOf p A z g a))
  exact ⟨h.1, h.2⟩

structure Region (p : Public) (F : p.E → p.E) (xs : p.E) (Λ : ℝ) : Prop where
  zero : F xs = 0
  x0_dist : ‖p.x0 - xs‖ ≤ p.D
  Λ_nonneg : 0 ≤ Λ
  bound : ∀ x, ‖x - xs‖ ≤ 3 * p.D + 1 / (4 * p.M) → ‖fderiv ℝ F x‖ ≤ Λ

def rho (p : Public) : ℝ := 3 * p.D + 2 * radius p

lemma rho_eq (hreg : Regular p F S) : 3 * p.D + 1 / (4 * p.M) = rho p := by
  unfold rho radius; have := hreg.M_pos.ne'; field_simp; ring

lemma region_lip (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} (hR : Region p F xs Λ)
    {x y : p.E} (hx : ‖x - xs‖ ≤ rho p) (hy : ‖y - xs‖ ≤ rho p) :
    ‖F x - F y‖ ≤ Λ * ‖x - y‖ := by
  have hs : Convex ℝ (Metric.closedBall xs (rho p)) := convex_closedBall xs _
  have hd : ∀ u ∈ Metric.closedBall xs (rho p),
      HasFDerivWithinAt F (fderiv ℝ F u) (Metric.closedBall xs (rho p)) u :=
    fun u _ => (hreg.diff u).hasFDerivWithinAt
  have hb : ∀ u ∈ Metric.closedBall xs (rho p), ‖fderiv ℝ F u‖ ≤ Λ := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    exact hR.bound u (by rw [rho_eq hreg]; exact hu)
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy)
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx)

lemma region_norm (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} (hR : Region p F xs Λ)
    {x : p.E} (hx : ‖x - xs‖ ≤ rho p) : ‖F x‖ ≤ Λ * ‖x - xs‖ := by
  have h0 : ‖xs - xs‖ ≤ rho p := by
    rw [sub_self, norm_zero]; unfold rho; have := radius_pos hreg; have := hreg.D_pos; positivity
  have h := region_lip hreg hR hx h0
  rwa [hR.zero, sub_zero] at h

structure OuterOK (p : Public) (xs : p.E) (Λ A : ℝ) (z g : p.E) : Prop where
  A_nonneg : 0 ≤ A
  z_dist : ‖z - xs‖ ≤ p.D + radius p / 6
  g_A : A * ‖g‖ ≤ 2 * p.D
  g_bound : ‖g‖ ≤ Λ * rho p

lemma w_dist (hreg : Regular p F S) {xs : p.E} {Λ A : ℝ} {z g : p.E} (hR : Region p F xs Λ)
    (hO : OuterOK p xs Λ A z g) {a : ℝ} (ha : 0 < a) :
    ‖wOf p A z a - xs‖ ≤ p.D + radius p / 6 := by
  have hA := hO.A_nonneg
  have hAa : 0 < A + a := by linarith
  have e : wOf p A z a - xs = (a / (A + a)) • (p.x0 - xs) + (A / (A + a)) • (z - xs) := by
    unfold wOf
    have : a / (A + a) + A / (A + a) = 1 := by rw [← add_div, add_comm a A, div_self hAa.ne']
    rw [smul_sub, smul_sub]
    calc _ = (a / (A + a)) • p.x0 + (A / (A + a)) • z - (a / (A + a) + A / (A + a)) • xs := by
          rw [this, one_smul]
      _ = _ := by rw [add_smul]; abel
  rw [e]
  have h1 : 0 ≤ a / (A + a) := by positivity
  have h2 : 0 ≤ A / (A + a) := by positivity
  have hr := radius_pos hreg
  calc _ ≤ ‖(a / (A + a)) • (p.x0 - xs)‖ + ‖(A / (A + a)) • (z - xs)‖ := norm_add_le _ _
    _ = a / (A + a) * ‖p.x0 - xs‖ + A / (A + a) * ‖z - xs‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
        abs_of_nonneg h2]
    _ ≤ a / (A + a) * (p.D + radius p / 6) + A / (A + a) * (p.D + radius p / 6) := by
      gcongr
      · linarith [hR.x0_dist]
      · exact hO.z_dist
    _ = _ := by rw [← add_mul, ← add_div, add_comm a A, div_self hAa.ne', one_mul]

lemma c_dist (hreg : Regular p F S) {xs : p.E} {Λ A : ℝ} {z g : p.E} (hR : Region p F xs Λ)
    (hO : OuterOK p xs Λ A z g) {a : ℝ} (ha : 0 < a) :
    ‖cOf p A z g a - xs‖ ≤ 3 * p.D + radius p / 6 := by
  have hA := hO.A_nonneg
  have hAa : 0 < A + a := by linarith
  have hw := w_dist hreg hR hO ha
  have hγ : (a * A / (A + a)) * ‖g‖ ≤ 2 * p.D := by
    have h1 : a * A / (A + a) * ‖g‖ = (a / (A + a)) * (A * ‖g‖) := by ring
    rw [h1]
    have h2 : a / (A + a) ≤ 1 := by rw [div_le_one hAa]; linarith
    have h3 := hO.g_A
    have h4 : 0 ≤ A * ‖g‖ := by positivity
    nlinarith [div_nonneg ha.le hAa.le]
  unfold cOf
  calc ‖wOf p A z a - (a * A / (A + a)) • g - xs‖
      = ‖(wOf p A z a - xs) - (a * A / (A + a)) • g‖ := by congr 1; abel
    _ ≤ ‖wOf p A z a - xs‖ + ‖(a * A / (A + a)) • g‖ := norm_sub_le _ _
    _ = ‖wOf p A z a - xs‖ + (a * A / (A + a)) * ‖g‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ _ := by linarith

lemma ball_in_region (hreg : Regular p F S) {xs : p.E} {Λ A : ℝ} {z g : p.E}
    (hR : Region p F xs Λ) (hO : OuterOK p xs Λ A z g) {a : ℝ} (ha : 0 < a) {x : p.E}
    (hx : ‖x - cOf p A z g a‖ ≤ radius p) : ‖x - xs‖ ≤ rho p := by
  have hc := c_dist hreg hR hO ha
  have hr := radius_pos hreg
  calc ‖x - xs‖ = ‖(x - cOf p A z g a) + (cOf p A z g a - xs)‖ := by congr 1; abel
    _ ≤ ‖x - cOf p A z g a‖ + ‖cOf p A z g a - xs‖ := norm_add_le _ _
    _ ≤ rho p := by unfold rho; linarith

def phi (hreg : Regular p F S) (A : ℝ) (z g : p.E) (a : ℝ) (ha : 0 < a) : ℝ :=
  ‖ballSol hreg A z g a ha - cOf p A z g a‖

lemma phi_le_G (hreg : Regular p F S) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a) :
    phi hreg A z g a ha ≤
      ‖a • F (cOf p A z g a) + cOf p A z g a - wOf p A z a‖ := by
  obtain ⟨hus, hvi⟩ := ballSol_spec hreg A z g ha
  set us := ballSol hreg A z g a ha
  set c := cOf p A z g a
  set w := wOf p A z a
  have h1 := hvi c (Metric.mem_closedBall_self (radius_pos hreg).le)
  have hm := monotone_F hreg us c
  have e : ⟪a • F us + us - w, c - us⟫ =
      -(a * ⟪F us - F c, us - c⟫) - ‖us - c‖ ^ 2 - ⟪a • F c + c - w, us - c⟫ := by
    have : c - us = -(us - c) := by abel
    rw [this, inner_neg_right, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    ring
  rw [e] at h1
  have hcs : -⟪a • F c + c - w, us - c⟫ ≤ ‖a • F c + c - w‖ * ‖us - c‖ := by
    have := abs_real_inner_le_norm (a • F c + c - w) (us - c)
    linarith [neg_abs_le ⟪a • F c + c - w, us - c⟫]
  have h2 : ‖us - c‖ ^ 2 ≤ ‖a • F c + c - w‖ * ‖us - c‖ := by
    nlinarith [mul_nonneg ha.le hm]
  show ‖us - c‖ ≤ ‖a • F c + c - w‖
  rcases eq_or_lt_of_le (norm_nonneg (us - c)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

lemma G_center (p : Public) (A : ℝ) (z g : p.E) (a : ℝ) (Fc : p.E) :
    a • Fc + cOf p A z g a - wOf p A z a = a • Fc - (a * A / (A + a)) • g := by
  unfold cOf; abel


lemma vi_stability (hreg : Regular p F S) (A : ℝ) (z g : p.E) {a a' : ℝ} (ha : 0 < a)
    (ha' : 0 < a') :
    |phi hreg A z g a' ha' - phi hreg A z g a ha| ≤
      ‖(a • F (ballSol hreg A z g a ha) + ballSol hreg A z g a ha - wOf p A z a) -
        (a' • F (cOf p A z g a' + (ballSol hreg A z g a ha - cOf p A z g a)) +
          (cOf p A z g a' + (ballSol hreg A z g a ha - cOf p A z g a)) - wOf p A z a')‖ := by
  obtain ⟨hus, hvi⟩ := ballSol_spec hreg A z g ha
  obtain ⟨hus', hvi'⟩ := ballSol_spec hreg A z g ha'
  set us := ballSol hreg A z g a ha
  set us' := ballSol hreg A z g a' ha'
  set c := cOf p A z g a
  set c' := cOf p A z g a'
  set w := wOf p A z a
  set w' := wOf p A z a'
  set v := us - c with hv
  set v' := us' - c' with hv'
  have hvn : ‖v‖ ≤ radius p := by
    have := hus; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
  have hvn' : ‖v'‖ ≤ radius p := by
    have := hus'; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
  have m1 : c + v' ∈ Metric.closedBall c (radius p) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hvn'
  have m2 : c' + v ∈ Metric.closedBall c' (radius p) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hvn
  have i1 := hvi _ m1
  have i2 := hvi' _ m2
  have e1 : c + v' - us = v' - v := by rw [hv]; abel
  have e2 : c' + v - us' = -(v' - v) := by rw [hv']; abel
  rw [e1] at i1
  rw [e2, inner_neg_right] at i2
  set P := a' • F (c' + v) + (c' + v) - w' with hP
  have hm := monotone_F hreg us' (c' + v)
  have hsm : ‖v' - v‖ ^ 2 ≤ ⟪(a' • F us' + us' - w') - P, v' - v⟫ := by
    have e3 : us' - (c' + v) = v' - v := by rw [hv']; abel
    rw [e3] at hm
    have e4 : (a' • F us' + us' - w') - P = a' • (F us' - F (c' + v)) + (v' - v) := by
      rw [hP, ← e3]; module
    rw [e4, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg ha'.le hm]
  have h3 : ‖v' - v‖ ^ 2 ≤ ⟪(a • F us + us - w) - P, v' - v⟫ := by
    rw [inner_sub_left] at hsm ⊢
    linarith
  have hcs := real_inner_le_norm ((a • F us + us - w) - P) (v' - v)
  have h4 : ‖v' - v‖ ≤ ‖(a • F us + us - w) - P‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (v' - v)) with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · nlinarith
  have h5 : |‖v'‖ - ‖v‖| ≤ ‖v' - v‖ := abs_norm_sub_norm_le v' v
  unfold phi
  exact h5.trans h4

lemma beta_diff {A a a' lo : ℝ} (hA : 0 ≤ A) (hlo : 0 < lo) (ha : lo ≤ a) (ha' : lo ≤ a') :
    |a / (A + a) - a' / (A + a')| ≤ |a - a'| / lo := by
  have h0 : 0 < a := lt_of_lt_of_le hlo ha
  have h0' : 0 < a' := lt_of_lt_of_le hlo ha'
  have e : a / (A + a) - a' / (A + a') = A * (a - a') / ((A + a) * (A + a')) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_nonneg hA, abs_of_pos (by positivity : 0 < (A + a) * (A + a'))]
  rw [div_le_div_iff₀ (by positivity) hlo]
  have h1 : A * lo ≤ (A + a) * (A + a') := by nlinarith
  nlinarith [abs_nonneg (a - a')]

lemma gamma_diff {A a a' : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (ha' : 0 < a') :
    |a * A / (A + a) - a' * A / (A + a')| ≤ |a - a'| := by
  have e : a * A / (A + a) - a' * A / (A + a') = A ^ 2 * (a - a') / ((A + a) * (A + a')) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_nonneg (sq_nonneg A),
    abs_of_pos (by positivity : 0 < (A + a) * (A + a'))]
  rw [div_le_iff₀ (by positivity)]
  have h1 : A ^ 2 ≤ (A + a) * (A + a') := by nlinarith
  nlinarith [abs_nonneg (a - a')]

end

end LongTails.Proofs.BallAnchoredSearch
