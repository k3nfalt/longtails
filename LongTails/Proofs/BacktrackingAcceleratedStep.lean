import LongTails.Algorithms.BacktrackingAccelerated
import LongTails.Proofs.GeneralizedGradientStep
import LongTails.Proofs.GdConvex

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.ParameterFreeGeneralized

open LongTails.Setups.GeneralizedSmoothParameterFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Hyp (f : E → ℝ) (g : E → E) (L0 L1 : ℝ) (u : E) : Prop where
  L0_pos : 0 < L0
  L1_nonneg : 0 ≤ L1
  convex : ConvexOn ℝ univ f
  grad : ∀ x, HasGradientAt f (g x) x
  diff : Differentiable ℝ g
  hess : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖
  min : IsMinOn f univ u

structure Inv (f : E → ℝ) (u : E) (R : ℝ) (s : Core E) : Prop where
  A_nonneg : 0 ≤ s.A
  h_pos : 0 < s.h
  potential : s.A * (f s.x - f u) + 1 / 2 * ‖s.v - u‖ ^ 2 ≤ R ^ 2 / 2
  x_dist : ‖s.x - u‖ ≤ R

def Accepted (g : E → E) (s : Core E) : Prop :=
  ‖g (trialPoint s)‖ ^ 2 / 2 ≤
    ⟪g (trialPoint s - s.h • g (trialPoint s)), g (trialPoint s)⟫

omit [CompleteSpace E] in
lemma trial_accepted {g : E → E} {s : Core E} (h : Accepted g s) :
    trial g s = ⟨s.A + stepWeight s, trialPoint s - s.h • g (trialPoint s),
      s.v - stepWeight s • g (trialPoint s), 2 * s.h⟩ := by
  unfold trial resolve
  exact ite_eq_left h

omit [CompleteSpace E] in
lemma trial_rejected {g : E → E} {s : Core E} (h : ¬Accepted g s) :
    trial g s = ⟨s.A, s.x, s.v, s.h / 2⟩ := by
  unfold trial resolve
  exact ite_eq_right h

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
omit [NormedAddCommGroup E] in
lemma stepWeight_pos {s : Core E} (hh : 0 < s.h) : 0 < stepWeight s := by
  unfold stepWeight
  have := Real.sqrt_nonneg (s.h ^ 2 + 4 * s.h * s.A)
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
omit [NormedAddCommGroup E] in
lemma stepWeight_sq {s : Core E} (hA : 0 ≤ s.A) (hh : 0 < s.h) :
    stepWeight s ^ 2 = s.h * (s.A + stepWeight s) := by
  unfold stepWeight
  have hr : Real.sqrt (s.h ^ 2 + 4 * s.h * s.A) ^ 2 = s.h ^ 2 + 4 * s.h * s.A :=
    Real.sq_sqrt (by positivity)
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
omit [NormedAddCommGroup E] in
lemma stepWeight_zero {s : Core E} (hA : s.A = 0) (hh : 0 < s.h) : stepWeight s = s.h := by
  unfold stepWeight
  rw [hA, mul_zero, add_zero, Real.sqrt_sq hh.le]
  ring

omit [CompleteSpace E] in
lemma trialPoint_zero {s : Core E} (hA : s.A = 0) (hh : 0 < s.h) : trialPoint s = s.v := by
  unfold trialPoint
  rw [stepWeight_zero hA hh, hA, zero_div, zero_smul, zero_add, zero_add, div_self hh.ne',
    one_smul]

lemma accept_descent {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (y : E) {h : ℝ} (hh : 0 ≤ h)
    (hacc : ‖g y‖ ^ 2 / 2 ≤ ⟪g (y - h • g y), g y⟫) :
    f (y - h • g y) ≤ f y - h / 2 * ‖g y‖ ^ 2 := by
  have hc := Gradient.convex_support H.convex H.grad (y - h • g y) y
  have he : y - (y - h • g y) = h • g y := by module
  rw [he, inner_smul_right] at hc
  nlinarith [mul_le_mul_of_nonneg_left hacc hh]

lemma small_step_accept {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (y : E) {h : ℝ} (hh : 0 ≤ h) (hs : 4 * (L0 + L1 * ‖g y‖) * h ≤ 1) :
    ‖g y‖ ^ 2 / 2 ≤ ⟪g (y - h • g y), g y⟫ := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hn : 0 ≤ ‖g y‖ := norm_nonneg _
  have hdist : ‖y - h • g y - y‖ = h * ‖g y‖ := by
    have he : y - h • g y - y = -(h • g y) := by module
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  have hsmall : L1 * (h * ‖g y‖) ≤ 1 / 4 := by nlinarith [mul_nonneg hL0.le hh]
  have hexp : Real.exp (L1 * (h * ‖g y‖)) ≤ 2 := by
    apply (Real.exp_le_exp.mpr hsmall).trans
    have h4 := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h4
    linarith
  have hb := GeneralizedAccelerated.gradient_growth hL0.le hL1 H.diff H.hess (y - h • g y) y
  rw [hdist] at hb
  have hc : 0 ≤ L0 + L1 * ‖g y‖ := by positivity
  have hdiff : ‖g (y - h • g y) - g y‖ ≤ ‖g y‖ / 2 := by
    calc
      _ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * (h * ‖g y‖)) * (h * ‖g y‖) := hb
      _ ≤ (L0 + L1 * ‖g y‖) * 2 * (h * ‖g y‖) := by gcongr
      _ ≤ ‖g y‖ / 2 := by nlinarith [mul_le_mul_of_nonneg_right hs hn]
  have hinner : ⟪g (y - h • g y), g y⟫ =
      ‖g y‖ ^ 2 + ⟪g (y - h • g y) - g y, g y⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    ring
  have hcs := abs_real_inner_le_norm (g (y - h • g y) - g y) (g y)
  have hlow : -(‖g (y - h • g y) - g y‖ * ‖g y‖) ≤ ⟪g (y - h • g y) - g y, g y⟫ :=
    (abs_le.mp hcs).1
  rw [hinner]
  nlinarith [mul_le_mul_of_nonneg_right hdiff hn]

lemma self_bound {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u) (x : E) :
    ‖g x‖ ^ 2 ≤ 8 * (L0 + L1 * ‖g x‖) * (f x - f u) := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hc : 0 < L0 + L1 * ‖g x‖ := by positivity
  have hh : 0 ≤ 1 / (4 * (L0 + L1 * ‖g x‖)) := by positivity
  have hs : 4 * (L0 + L1 * ‖g x‖) * (1 / (4 * (L0 + L1 * ‖g x‖))) ≤ 1 := by
    rw [mul_one_div_cancel (by positivity)]
  have hd := accept_descent H x hh (small_step_accept H x hh hs)
  have hm : f u ≤ f (x - (1 / (4 * (L0 + L1 * ‖g x‖))) • g x) := H.min (mem_univ _)
  have h1 : 1 / (4 * (L0 + L1 * ‖g x‖)) / 2 * ‖g x‖ ^ 2 ≤ f x - f u := by linarith
  have h2 : 1 / (4 * (L0 + L1 * ‖g x‖)) / 2 * ‖g x‖ ^ 2 =
      ‖g x‖ ^ 2 / (8 * (L0 + L1 * ‖g x‖)) := by
    field_simp
    ring
  rw [h2, div_le_iff₀ (by positivity)] at h1
  linarith

lemma gradient_gap_bound {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (x : E) : L1 * ‖g x‖ ≤ L0 + 10 * L1 ^ 2 * (f x - f u) := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hs := self_bound H x
  have hgap : 0 ≤ f x - f u := sub_nonneg.mpr (H.min (mem_univ x))
  have hn : 0 ≤ ‖g x‖ := norm_nonneg _
  by_contra hcon
  push Not at hcon
  have ht : 0 ≤ L1 * ‖g x‖ := by positivity
  have hd : 0 ≤ L1 ^ 2 * (f x - f u) := by positivity
  have hsq : (L1 * ‖g x‖) ^ 2 ≤ 8 * (L0 + L1 * ‖g x‖) * (L1 ^ 2 * (f x - f u)) := by
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg L1)
    nlinarith
  nlinarith [mul_nonneg ht hd, mul_nonneg hL0.le hd]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma v_dist {f : E → ℝ} {u : E} {R : ℝ} {s : Core E} (hR : 0 ≤ R)
    (hmin : IsMinOn f univ u) (hI : Inv f u R s) : ‖s.v - u‖ ≤ R := by
  have hgap : 0 ≤ f s.x - f u := sub_nonneg.mpr (hmin (mem_univ _))
  have hp := hI.potential
  have hA := mul_nonneg hI.A_nonneg hgap
  have hsq : ‖s.v - u‖ ^ 2 ≤ R ^ 2 := by linarith
  exact (abs_le_of_sq_le_sq' hsq hR).2

omit [CompleteSpace E] in
lemma coupling_identity {s : Core E} (hA : 0 ≤ s.A) (hh : 0 < s.h) :
    s.A • (trialPoint s - s.x) + stepWeight s • (trialPoint s - s.v) = 0 := by
  have ha := stepWeight_pos hh
  have hs : s.A + stepWeight s ≠ 0 := by positivity
  unfold trialPoint
  match_scalars
  all_goals field_simp
  all_goals ring

lemma accept_potential {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    {s : Core E} (hA : 0 ≤ s.A) (hh : 0 < s.h) (hacc : Accepted g s) :
    (s.A + stepWeight s) * (f (trialPoint s - s.h • g (trialPoint s)) - f u) +
        1 / 2 * ‖s.v - stepWeight s • g (trialPoint s) - u‖ ^ 2 ≤
      s.A * (f s.x - f u) + 1 / 2 * ‖s.v - u‖ ^ 2 := by
  have ha := stepWeight_pos hh
  have hsq := stepWeight_sq hA hh
  have hdesc := accept_descent H (trialPoint s) hh.le hacc
  have hcx := Gradient.convex_support H.convex H.grad (trialPoint s) s.x
  have hcu := Gradient.convex_support H.convex H.grad (trialPoint s) u
  have hid := coupling_identity (s := s) hA hh
  have hinner := congrArg (fun w => ⟪g (trialPoint s), w⟫) hid
  simp only [inner_add_right, inner_smul_right, inner_sub_right, inner_zero_right] at hinner
  simp only [inner_sub_right] at hcx hcu
  have hvnorm : ‖s.v - stepWeight s • g (trialPoint s) - u‖ ^ 2 =
      ‖s.v - u‖ ^ 2 - 2 * stepWeight s * ⟪g (trialPoint s), s.v - u⟫ +
        stepWeight s ^ 2 * ‖g (trialPoint s)‖ ^ 2 := by
    have he : s.v - stepWeight s • g (trialPoint s) - u =
        (s.v - u) - stepWeight s • g (trialPoint s) := by module
    rw [he, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm]
    ring
  have hvin : ⟪g (trialPoint s), s.v - u⟫ =
      ⟪g (trialPoint s), s.v⟫ - ⟪g (trialPoint s), u⟫ := inner_sub_right _ _ _
  rw [hvnorm, hvin]
  have h1 := mul_le_mul_of_nonneg_left hdesc (by positivity : 0 ≤ s.A + stepWeight s)
  have h2 := mul_le_mul_of_nonneg_left hcx hA
  have h3 := mul_le_mul_of_nonneg_left hcu ha.le
  have h4 : (s.A + stepWeight s) * (s.h / 2 * ‖g (trialPoint s)‖ ^ 2) =
      stepWeight s ^ 2 / 2 * ‖g (trialPoint s)‖ ^ 2 := by
    rw [hsq]
    ring
  nlinarith

omit [CompleteSpace E] in
lemma accept_point {s : Core E} (hA : 0 ≤ s.A) (hh : 0 < s.h) (w u : E) :
    trialPoint s - s.h • w - u =
      (s.A / (s.A + stepWeight s)) • (s.x - u) +
        (stepWeight s / (s.A + stepWeight s)) • (s.v - stepWeight s • w - u) := by
  have ha := stepWeight_pos hh
  have hsq := stepWeight_sq hA hh
  have hs : s.A + stepWeight s ≠ 0 := by positivity
  have hh' : s.h = stepWeight s ^ 2 / (s.A + stepWeight s) := by
    rw [eq_div_iff hs]
    linarith
  unfold trialPoint
  generalize stepWeight s = a at *
  rw [hh']
  match_scalars
  all_goals field_simp
  all_goals ring

lemma accept_inv {f : E → ℝ} {g : E → E} {L0 L1 R : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hR : 0 ≤ R) {s : Core E} (hI : Inv f u R s) (hacc : Accepted g s) :
    Inv f u R (trial g s) := by
  rw [trial_accepted hacc]
  have hA := hI.A_nonneg
  have hh := hI.h_pos
  have ha := stepWeight_pos hh
  have hpot := (accept_potential H hA hh hacc).trans hI.potential
  have hI' : Inv f u R ⟨s.A + stepWeight s, trialPoint s - s.h • g (trialPoint s),
      s.v - stepWeight s • g (trialPoint s), 2 * s.h⟩ := by
    refine ⟨by positivity, by positivity, hpot, ?_⟩
    change ‖trialPoint s - s.h • g (trialPoint s) - u‖ ≤ R
    have hgap : 0 ≤ f (trialPoint s - s.h • g (trialPoint s)) - f u :=
      sub_nonneg.mpr (H.min (mem_univ _))
    have hsq : ‖s.v - stepWeight s • g (trialPoint s) - u‖ ^ 2 ≤ R ^ 2 := by
      have := mul_nonneg (by positivity : 0 ≤ s.A + stepWeight s) hgap
      linarith
    have hv := (abs_le_of_sq_le_sq' hsq hR).2
    rw [accept_point hA hh]
    have hs : 0 < s.A + stepWeight s := by positivity
    calc
      _ ≤ ‖(s.A / (s.A + stepWeight s)) • (s.x - u)‖ +
          ‖(stepWeight s / (s.A + stepWeight s)) •
            (s.v - stepWeight s • g (trialPoint s) - u)‖ := norm_add_le _ _
      _ = s.A / (s.A + stepWeight s) * ‖s.x - u‖ +
          stepWeight s / (s.A + stepWeight s) *
            ‖s.v - stepWeight s • g (trialPoint s) - u‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ s.A / (s.A + stepWeight s) * R + stepWeight s / (s.A + stepWeight s) * R := by
        gcongr
        exact hI.x_dist
      _ = R := by
        field_simp
  exact hI'

omit [CompleteSpace E] in
lemma reject_inv {f : E → ℝ} {g : E → E} {R : ℝ} {u : E} {s : Core E}
    (hI : Inv f u R s) (hrej : ¬Accepted g s) : Inv f u R (trial g s) := by
  rw [trial_rejected hrej]
  exact ⟨hI.A_nonneg, by have := hI.h_pos; positivity, hI.potential, hI.x_dist⟩

lemma pass_zero {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    {s : Core E} (hA : s.A = 0) (hh : 0 < s.h)
    (hs : 4 * (L0 + L1 * ‖g s.v‖) * s.h ≤ 1) : Accepted g s := by
  unfold Accepted
  rw [trialPoint_zero hA hh]
  exact small_step_accept H s.v hh.le hs

omit [CompleteSpace E] in
lemma trialPoint_dist {f : E → ℝ} {u : E} {R : ℝ} {s : Core E} (hR : 0 ≤ R)
    (hmin : IsMinOn f univ u) (hI : Inv f u R s) :
    ‖trialPoint s - s.x‖ ≤ stepWeight s / (s.A + stepWeight s) * (2 * R) := by
  have hA := hI.A_nonneg
  have hh := hI.h_pos
  have ha := stepWeight_pos hh
  have hs : s.A + stepWeight s ≠ 0 := by positivity
  have he : trialPoint s - s.x = (stepWeight s / (s.A + stepWeight s)) • (s.v - s.x) := by
    unfold trialPoint
    match_scalars
    all_goals field_simp
    all_goals ring
  have hvx : ‖s.v - s.x‖ ≤ 2 * R := by
    have h1 := v_dist hR hmin hI
    have h2 := hI.x_dist
    have h3 : s.v - s.x = (s.v - u) - (s.x - u) := by module
    rw [h3]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr

lemma pass_pos {f : E → ℝ} {g : E → E} {L0 L1 R : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hR : 0 < R) {s : Core E} (hI : Inv f u R s) (hA : 0 < s.A)
    (h1 : 32 * L0 * s.h ≤ 1) (h2 : s.h * (2 + 13 * (L1 * R)) ^ 2 ≤ 2 * s.A) :
    Accepted g s := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hh := hI.h_pos
  have ha := stepWeight_pos hh
  have hsq := stepWeight_sq hA.le hh
  have ht : 0 ≤ L1 * R := by positivity
  have hdist := trialPoint_dist hR.le H.min hI
  have hsum : 0 < s.A + stepWeight s := by positivity
  obtain ⟨q, hq⟩ : ∃ q, q = stepWeight s / (s.A + stepWeight s) := ⟨_, rfl⟩
  rw [← hq] at hdist
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqsq : q ^ 2 * (s.A + stepWeight s) = s.h := by
    rw [hq, div_pow, hsq]
    field_simp
  have hqA : q ^ 2 * s.A ≤ s.h := by
    have := mul_nonneg (sq_nonneg q) ha.le
    linarith
  have hq2 : q ^ 2 * (2 + 13 * (L1 * R)) ^ 2 ≤ 2 := by
    have h3 : q ^ 2 * (2 + 13 * (L1 * R)) ^ 2 * s.A ≤ 2 * s.A := by
      have := mul_le_mul_of_nonneg_right hqA (sq_nonneg (2 + 13 * (L1 * R)))
      linarith
    exact le_of_mul_le_mul_right h3 hA
  have hqs : q * (2 + 13 * (L1 * R)) ≤ 3 / 2 := by
    have h3 : (q * (2 + 13 * (L1 * R))) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
      rw [mul_pow]
      linarith
    exact (abs_le_of_sq_le_sq' h3 (by norm_num)).2
  have hLd : L1 * ‖trialPoint s - s.x‖ ≤ 3 / 13 := by
    have h3 := mul_le_mul_of_nonneg_left hdist hL1
    linarith
  have hexp : Real.exp (L1 * ‖trialPoint s - s.x‖) ≤ 2 := by
    apply (Real.exp_le_exp.mpr (hLd.trans (by norm_num : (3 / 13 : ℝ) ≤ 1 / 4))).trans
    have h4 := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h4
    linarith
  have hb := GeneralizedAccelerated.gradient_growth hL0.le hL1 H.diff H.hess (trialPoint s) s.x
  have hgx : 0 ≤ ‖g s.x‖ := norm_nonneg _
  have hc : 0 ≤ L0 + L1 * ‖g s.x‖ := by positivity
  have h5 : ‖g (trialPoint s) - g s.x‖ ≤
      (L0 + L1 * ‖g s.x‖) * 2 * ‖trialPoint s - s.x‖ := by
    refine hb.trans ?_
    gcongr
  have hdy : L1 * ‖g (trialPoint s) - g s.x‖ ≤ 6 / 13 * (L0 + L1 * ‖g s.x‖) := by
    have h6 := mul_le_mul_of_nonneg_left h5 hL1
    have h7 := mul_le_mul_of_nonneg_left hLd (by positivity : 0 ≤ (L0 + L1 * ‖g s.x‖) * 2)
    linarith
  have hgy : L1 * ‖g (trialPoint s)‖ ≤ L1 * ‖g s.x‖ + 6 / 13 * (L0 + L1 * ‖g s.x‖) := by
    have h6 : ‖g (trialPoint s)‖ ≤ ‖g (trialPoint s) - g s.x‖ + ‖g s.x‖ :=
      norm_le_norm_sub_add _ _
    have := mul_le_mul_of_nonneg_left h6 hL1
    linarith
  have hgb := gradient_gap_bound H s.x
  have hgap : 0 ≤ f s.x - f u := sub_nonneg.mpr (H.min (mem_univ _))
  have hAgap : s.A * (f s.x - f u) ≤ R ^ 2 / 2 := by
    have := hI.potential
    have := sq_nonneg ‖s.v - u‖
    linarith
  have hbound : L0 + L1 * ‖g (trialPoint s)‖ ≤
      38 / 13 * L0 + 190 / 13 * (L1 ^ 2 * (f s.x - f u)) := by linarith
  have hfirst : 4 * (38 / 13 * L0) * s.h ≤ 19 / 52 := by linarith
  have h8 : s.h * (13 * (L1 * R)) ^ 2 ≤ 2 * s.A := by
    have : 0 ≤ s.h * (4 + 52 * (L1 * R)) := by positivity
    linarith
  have h9 : s.h * (13 * (L1 * R)) ^ 2 * (f s.x - f u) ≤ R ^ 2 := by
    have := mul_le_mul_of_nonneg_right h8 hgap
    linarith
  have hR2 : 0 < R ^ 2 := by positivity
  have h11 : s.h * (L1 ^ 2 * (f s.x - f u)) * 169 ≤ 1 := by
    have h10 : s.h * (L1 ^ 2 * (f s.x - f u)) * 169 * R ^ 2 ≤ 1 * R ^ 2 := by linarith
    exact le_of_mul_le_mul_right h10 hR2
  have hsecond : 4 * (190 / 13 * (L1 ^ 2 * (f s.x - f u))) * s.h ≤ 9 / 26 := by linarith
  apply small_step_accept H (trialPoint s) hh.le
  have := mul_le_mul_of_nonneg_right hbound hh.le
  linarith

end OracleTemplate.ParameterFreeGeneralized
