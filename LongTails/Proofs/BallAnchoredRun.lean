import LongTails.Proofs.BallAnchoredOuter

open scoped RealInnerProductSpace

namespace LongTails.Proofs.BallAnchoredRun

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredTrial

noncomputable section

variable {p : Public}

def reply (F : p.E → p.E) (q : Fin 2 × p.E) : p.E ⊕ (p.E →L[ℝ] p.E) := by
  classical
  exact if q.1 = 0 then Sum.inl (F q.2) else Sum.inr (fderiv ℝ F q.2)

def trueStep (F : p.E → p.E) (s : State p) : State p := update s (reply F (query s))

lemma advance_of_ne (s : State p) (h : s.t + 1 ≠ s.T) :
    s.advance = { s with phase := .stepValue, u := s.newton, t := s.t + 1 } := by
  unfold State.advance; rw [ite_eq_right h]

lemma advance_of_eq (s : State p) (h : s.t + 1 = s.T) :
    s.advance = { s with phase := .finalValue, u := s.newton, t := s.t + 1 } := by
  unfold State.advance; rw [ite_eq_left h]

lemma newtonCount_ge (k : ℕ) (a Γ : ℝ) : 9 ≤ newtonCount k a Γ := by
  unfold newtonCount; omega

variable (F : p.E → p.E) (k : ℕ) (A : ℝ) (z g : p.E) (h : ℕ) (bis : Bool) (lo hi a : ℝ)

def trialCount : ℕ := newtonCount k a ‖fderiv ℝ F (cOf p A z g a)‖

def stepState (t : ℕ) (Fu : p.E) (Ju : p.E →L[ℝ] p.E) : State p :=
  ⟨.stepValue, k, A, z, g, h, bis, lo, hi, a, ‖fderiv ℝ F (cOf p A z g a)‖, t,
    iter F a (wOf p A z a) (cOf p A z g a) t, Fu, Ju⟩

def trialEnd : State p :=
  State.afterFinal ⟨.finalValue, k, A, z, g, h, bis, lo, hi, a, 0, 0,
    finalPoint F k A z g a, F (finalPoint F k A z g a), 0⟩

lemma tick_center :
    trueStep F (trueStep F (trialStart k A z g h bis lo hi a)) =
      stepState F k A z g h bis lo hi a 1 (F (cOf p A z g a))
        (fderiv ℝ F (cOf p A z g a)) := by
  have e : trueStep F (trueStep F (trialStart k A z g h bis lo hi a)) =
      State.advance ⟨.centerJac, k, A, z, g, h, bis, lo, hi, a,
        ‖fderiv ℝ F (cOf p A z g a)‖, 0, cOf p A z g a, F (cOf p A z g a),
        fderiv ℝ F (cOf p A z g a)⟩ := rfl
  rw [e, advance_of_ne]
  · rfl
  · show 0 + 1 ≠ newtonCount k a ‖fderiv ℝ F (cOf p A z g a)‖
    have := newtonCount_ge k a ‖fderiv ℝ F (cOf p A z g a)‖
    omega

lemma tick_step (t : ℕ) (Fu : p.E) (Ju : p.E →L[ℝ] p.E)
    (ht : t + 1 ≠ trialCount F k A z g a) :
    trueStep F (trueStep F (stepState F k A z g h bis lo hi a t Fu Ju)) =
      stepState F k A z g h bis lo hi a (t + 1)
        (F (iter F a (wOf p A z a) (cOf p A z g a) t))
        (fderiv ℝ F (iter F a (wOf p A z a) (cOf p A z g a) t)) := by
  have e : trueStep F (trueStep F (stepState F k A z g h bis lo hi a t Fu Ju)) =
      State.advance ⟨.stepJac, k, A, z, g, h, bis, lo, hi, a,
        ‖fderiv ℝ F (cOf p A z g a)‖, t, iter F a (wOf p A z a) (cOf p A z g a) t,
        F (iter F a (wOf p A z a) (cOf p A z g a) t),
        fderiv ℝ F (iter F a (wOf p A z a) (cOf p A z g a) t)⟩ := rfl
  rw [e, advance_of_ne]
  · rfl
  · exact ht

lemma tick_last (t : ℕ) (Fu : p.E) (Ju : p.E →L[ℝ] p.E)
    (ht : t + 1 = trialCount F k A z g a) :
    trueStep F (trueStep F (trueStep F (stepState F k A z g h bis lo hi a t Fu Ju))) =
      trialEnd F k A z g h bis lo hi a := by
  have e : trueStep F (trueStep F (stepState F k A z g h bis lo hi a t Fu Ju)) =
      State.advance ⟨.stepJac, k, A, z, g, h, bis, lo, hi, a,
        ‖fderiv ℝ F (cOf p A z g a)‖, t, iter F a (wOf p A z a) (cOf p A z g a) t,
        F (iter F a (wOf p A z a) (cOf p A z g a) t),
        fderiv ℝ F (iter F a (wOf p A z a) (cOf p A z g a) t)⟩ := rfl
  rw [e, advance_of_eq]
  · have hT : finalPoint F k A z g a = iter F a (wOf p A z a) (cOf p A z g a) (t + 1) := by
      unfold finalPoint
      rw [show newtonCount k a ‖fderiv ℝ F (cOf p A z g a)‖ = t + 1 from ht.symm]
    unfold trialEnd
    rw [hT]
    rfl
  · exact ht

lemma steps_run (Fu : p.E) (Ju : p.E →L[ℝ] p.E) :
    ∀ j, 1 + j < trialCount F k A z g a → ∃ Fu' Ju',
      (trueStep F)^[2 * j] (stepState F k A z g h bis lo hi a 1 Fu Ju) =
        stepState F k A z g h bis lo hi a (1 + j) Fu' Ju'
  | 0, _ => ⟨Fu, Ju, rfl⟩
  | j + 1, hj => by
    obtain ⟨Fu', Ju', e⟩ := steps_run Fu Ju j (by omega)
    refine ⟨F (iter F a (wOf p A z a) (cOf p A z g a) (1 + j)),
      fderiv ℝ F (iter F a (wOf p A z a) (cOf p A z g a) (1 + j)), ?_⟩
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply, e]
    have := tick_step F k A z g h bis lo hi a (1 + j) Fu' Ju' (by omega)
    rw [show 1 + (j + 1) = 1 + j + 1 by ring]
    exact this

lemma trial_run :
    (trueStep F)^[2 * trialCount F k A z g a + 1] (trialStart k A z g h bis lo hi a) =
      trialEnd F k A z g h bis lo hi a := by
  set T := trialCount F k A z g a with hT
  have hT9 : 9 ≤ T := newtonCount_ge _ _ _
  obtain ⟨Fu', Ju', e⟩ := steps_run F k A z g h bis lo hi a (F (cOf p A z g a))
    (fderiv ℝ F (cOf p A z g a)) (T - 2) (by omega)
  have hsplit : 2 * T + 1 = (3 + 2 * (T - 2)) + 2 := by omega
  rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply]
  have e2 : (trueStep F)^[2] (trialStart k A z g h bis lo hi a) =
      stepState F k A z g h bis lo hi a 1 (F (cOf p A z g a))
        (fderiv ℝ F (cOf p A z g a)) := tick_center F k A z g h bis lo hi a
  rw [e2, e]
  have hlast := tick_last F k A z g h bis lo hi a (1 + (T - 2)) Fu' Ju' (by omega)
  exact hlast


lemma trialEnd_eq :
    trialEnd F k A z g h bis lo hi a =
      if ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3 then
        (if bis = true then trialStart k A z g h true a hi ((a + hi) / 2)
          else if h = 0 then
            outerStart (k + 1) (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a))
          else trialStart k A z g h true a (2 * a) (3 * a / 2))
      else if 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖ then
        (if bis = true then trialStart k A z g h true lo a ((lo + a) / 2)
          else trialStart k A z g (h + 1) false 0 0 (a / 2))
      else outerStart (k + 1) (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) := by
  unfold trialEnd State.afterFinal State.accept
  rfl

lemma trialEnd_low_bis (hd : ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3) :
    trialEnd F k A z g h true lo hi a = trialStart k A z g h true a hi ((a + hi) / 2) := by
  rw [trialEnd_eq, ite_eq_left hd, ite_eq_left (rfl : true = true)]

lemma trialEnd_low_term (hd : ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3) :
    trialEnd F k A z g 0 false lo hi a =
      outerStart (k + 1) (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) := by
  rw [trialEnd_eq, ite_eq_left hd, ite_eq_right Bool.false_ne_true, ite_eq_left (rfl : (0 : ℕ) = 0)]

lemma trialEnd_low_bracket (hd : ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3)
    (hh : h ≠ 0) :
    trialEnd F k A z g h false lo hi a = trialStart k A z g h true a (2 * a) (3 * a / 2) := by
  rw [trialEnd_eq, ite_eq_left hd, ite_eq_right Bool.false_ne_true, ite_eq_right hh]

lemma trialEnd_high_bis (hd : ¬ ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3)
    (hd' : 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    trialEnd F k A z g h true lo hi a = trialStart k A z g h true lo a ((lo + a) / 2) := by
  rw [trialEnd_eq, ite_eq_right hd, ite_eq_left hd', ite_eq_left (rfl : true = true)]

lemma trialEnd_high_halve (hd : ¬ ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3)
    (hd' : 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    trialEnd F k A z g h false lo hi a = trialStart k A z g (h + 1) false 0 0 (a / 2) := by
  rw [trialEnd_eq, ite_eq_right hd, ite_eq_left hd', ite_eq_right Bool.false_ne_true]

lemma trialEnd_accept (hd : ¬ ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3)
    (hd' : ¬ 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    trialEnd F k A z g h bis lo hi a =
      outerStart (k + 1) (A + a) (finalPoint F k A z g a) (F (finalPoint F k A z g a)) := by
  rw [trialEnd_eq, ite_eq_right hd, ite_eq_right hd']

lemma step_finished (s : State p) (hs : s.phase = .finished) : trueStep F s = s := by
  unfold trueStep update
  rw [hs]

end

end LongTails.Proofs.BallAnchoredRun
