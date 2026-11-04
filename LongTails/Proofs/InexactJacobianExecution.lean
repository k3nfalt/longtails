import LongTails.Proofs.InexactJacobianOuter
import LongTails.Proofs.ExecutionHistory

namespace LongTails.Proofs.InexactJacobianExecution

open OracleTemplate
open LongTails.Setups.InexactJacobianMonotone
open LongTails.Algorithms.NestedAnchoredInexactJacobian
open InexactJacobianInner InexactJacobianOuter

noncomputable section

variable {p : Params}

def trueStep (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (sc : State p × ℕ) : State p × ℕ :=
  (update sc.1 (F (query sc.1).2, J sc.2 (query sc.1).2), sc.2 + 1)

lemma step_model (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) :
    trueStep F J (trialAt F J base k z Fz j i, base + attemptOffset (p := p) k j + 2 * i) =
      (certificateAt F J base k z Fz j i, base + attemptOffset (p := p) k j + 2 * i + 1) := rfl

lemma step_certificate (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) (n : ℕ) :
    trueStep F J (certificateAt F J base k z Fz j i, n) =
      (afterCertificate (certificateAt F J base k z Fz j i)
        (F (certificateAt F J base k z Fz j i).pending), n + 1) := rfl

lemma certificate_success (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} {j i : ℕ} (h : acc F J base k z Fz j i) :
    afterCertificate (certificateAt F J base k z Fz j i)
      (F (certificateAt F J base k z Fz j i).pending) =
      outerStart (k + 1) (certificateAt F J base k z Fz j i).pending
        (F (certificateAt F J base k z Fz j i).pending) := by
  change (certificateAt F J base k z Fz j i).accepted
    (F (certificateAt F J base k z Fz j i).pending) at h
  simp only [afterCertificate, h, ↓reduceIte]
  rfl

lemma certificate_failure (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} {j i : ℕ} (h : ¬acc F J base k z Fz j i) :
    afterCertificate (certificateAt F J base k z Fz j i)
      (F (certificateAt F J base k z Fz j i).pending) =
      if i + 1 = innerCount p k j then trialAt F J base k z Fz (j + 1) 0
      else trialAt F J base k z Fz j (i + 1) := by
  change ¬(certificateAt F J base k z Fz j i).accepted
    (F (certificateAt F J base k z Fz j i).pending) at h
  simp only [afterCertificate, h, ↓reduceIte]
  have hk : (certificateAt F J base k z Fz j i).k = k := rfl
  have hj : (certificateAt F J base k z Fz j i).j = j := rfl
  have hi : (certificateAt F J base k z Fz j i).i = i := rfl
  rw [hk, hj, hi]
  split_ifs <;> rfl

lemma pair_success (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} {j i : ℕ} (h : acc F J base k z Fz j i) :
    (trueStep F J)^[2] (trialAt F J base k z Fz j i, base + attemptOffset (p := p) k j + 2 * i) =
      (outerStart (k + 1) (certificateAt F J base k z Fz j i).pending
        (F (certificateAt F J base k z Fz j i).pending),
        base + attemptOffset (p := p) k j + 2 * (i + 1)) := by
  change trueStep F J (trueStep F J _) = _
  rw [step_model, step_certificate, certificate_success F J h]
  congr 1

lemma pair_failure (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} {j i : ℕ} (h : ¬acc F J base k z Fz j i) :
    (trueStep F J)^[2] (trialAt F J base k z Fz j i, base + attemptOffset (p := p) k j + 2 * i) =
      (if i + 1 = innerCount p k j then trialAt F J base k z Fz (j + 1) 0
        else trialAt F J base k z Fz j (i + 1),
        base + attemptOffset (p := p) k j + 2 * (i + 1)) := by
  change trueStep F J (trueStep F J _) = _
  rw [step_model, step_certificate, certificate_failure F J h]
  congr 1

lemma iterate_attempt_prefix (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) (hi : i < innerCount p k j)
    (hfail : ∀ l < i, ¬acc F J base k z Fz j l) :
    (trueStep F J)^[2 * i] (trialAt F J base k z Fz j 0, base + attemptOffset (p := p) k j) =
      (trialAt F J base k z Fz j i, base + attemptOffset (p := p) k j + 2 * i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hprev := ih (by omega) (fun l hl => hfail l (by omega))
    rw [show 2 * (i + 1) = 2 + 2 * i by omega, Function.iterate_add_apply, hprev,
      pair_failure F J (hfail i (by omega))]
    rw [ite_eq_right (by omega)]
    congr 1
    omega

lemma iterate_attempt_failure (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j : ℕ)
    (hfail : ∀ i < innerCount p k j, ¬acc F J base k z Fz j i) :
    (trueStep F J)^[2 * innerCount p k j]
      (trialAt F J base k z Fz j 0, base + attemptOffset (p := p) k j) =
      (trialAt F J base k z Fz (j + 1) 0, base + attemptOffset (p := p) k (j + 1)) := by
  have hN := InexactJacobianModel.innerCount_pos (p := p) k j
  have he : innerCount p k j - 1 + 1 = innerCount p k j := by omega
  have hp := iterate_attempt_prefix F J base k z Fz j (innerCount p k j - 1)
    (by omega) (fun i hi => hfail i (by omega))
  rw [show 2 * innerCount p k j = 2 + 2 * (innerCount p k j - 1) by omega,
    Function.iterate_add_apply, hp, pair_failure F J (hfail _ (by omega)), he, ite_eq_left rfl]
  congr 1
  simp only [attemptOffset, Finset.sum_range_succ]
  omega

lemma iterate_attempts (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j : ℕ)
    (hfail : ∀ l < j, ∀ i < innerCount p k l, ¬acc F J base k z Fz l i) :
    (trueStep F J)^[attemptOffset (p := p) k j] (trialAt F J base k z Fz 0 0, base) =
      (trialAt F J base k z Fz j 0, base + attemptOffset (p := p) k j) := by
  induction j with
  | zero => simp [attemptOffset]
  | succ j ih =>
    have hprev := ih (fun l hl => hfail l (by omega))
    have he : attemptOffset (p := p) k (j + 1) = 2 * innerCount p k j + attemptOffset (p := p) k j := by
      simp [attemptOffset, Finset.sum_range_succ, Nat.add_comm]
    rw [he, Function.iterate_add_apply, hprev, iterate_attempt_failure F J base k z Fz j (hfail j (by omega))]
    rw [he]

lemma iterate_attempt_success (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} {j i : ℕ} (hi : i < innerCount p k j)
    (hfail : ∀ l < i, ¬acc F J base k z Fz j l) (hacc : acc F J base k z Fz j i) :
    (trueStep F J)^[2 * (i + 1)] (trialAt F J base k z Fz j 0, base + attemptOffset (p := p) k j) =
      (outerStart (k + 1) (certificateAt F J base k z Fz j i).pending
        (F (certificateAt F J base k z Fz j i).pending),
        base + attemptOffset (p := p) k j + 2 * (i + 1)) := by
  rw [show 2 * (i + 1) = 2 + 2 * i by omega, Function.iterate_add_apply,
    iterate_attempt_prefix F J base k z Fz j i hi hfail, pair_success F J hacc]
  congr 1
  omega

lemma iterate_outer (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} (hk : k ≠ outerCount p) (hs : Succeeds F J base k z Fz) :
    (trueStep F J)^[outerTicks F J base k z Fz] (outerStart k z Fz, base) =
      (outerStart (k + 1) (nextPoint F J base k z Fz) (F (nextPoint F J base k z Fz)),
        base + outerTicks F J base k z Fz) := by
  obtain ⟨hi, hacc, hfail, hno⟩ := first_spec F J hs
  have hstart : outerStart k z Fz = trialAt F J base k z Fz 0 0 := by
    simp only [outerStart, hk, ↓reduceIte]
    rfl
  rw [hstart]
  unfold outerTicks
  rw [Nat.add_comm (attemptOffset (p := p) k (firstAttempt F J base k z Fz)),
    Function.iterate_add_apply, iterate_attempts F J base k z Fz _ hfail,
    iterate_attempt_success F J hi hno hacc]
  change (_, base + attemptOffset (p := p) k (firstAttempt F J base k z Fz) +
    2 * (firstIndex F J base k z Fz + 1)) = (_, base +
      (2 * (firstIndex F J base k z Fz + 1) + attemptOffset (p := p) k (firstAttempt F J base k z Fz)))
  congr 1
  omega

lemma iterate_total (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (hs : ∀ base k z Fz, Succeeds F J base k z Fz) :
    ∀ k, k ≤ outerCount p →
      (trueStep F J)^[(outerSeq F J k).1] (initial, 0) =
        (outerStart k (outerSeq F J k).2.1 (outerSeq F J k).2.2, (outerSeq F J k).1) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev := ih (by omega)
    have he : (outerSeq F J (k + 1)).1 =
        outerTicks F J (outerSeq F J k).1 k (outerSeq F J k).2.1 (outerSeq F J k).2.2 +
          (outerSeq F J k).1 := by simp only [outerSeq]; omega
    rw [he, Function.iterate_add_apply, hprev, iterate_outer F J (by omega) (hs _ _ _ _)]
    simp only [outerSeq, Nat.add_comm]

lemma iterate_finished (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (z Fz : p.E) (base n : ℕ) :
    (trueStep F J)^[n] (outerStart (outerCount p) z Fz, base) =
      (outerStart (outerCount p) z Fz, base + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hph : (outerStart (p := p) (outerCount p) z Fz).phase = .finished := by simp [outerStart]
    simp only [trueStep, update, hph]
    congr 1

lemma iterate_budget (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (hs : ∀ base k z Fz, Succeeds F J base k z Fz) {B : ℕ}
    (hB : (outerSeq F J (outerCount p)).1 ≤ B) :
    ((trueStep F J)^[B] (initial, 0)).1.z = (outerSeq F J (outerCount p)).2.1 := by
  have he : B = (B - (outerSeq F J (outerCount p)).1) + (outerSeq F J (outerCount p)).1 := by omega
  rw [he, Function.iterate_add_apply, iterate_total F J hs _ le_rfl, iterate_finished]
  rfl

def historyJacobian (O : Oracle p.E (p.E × (p.E →L[ℝ] p.E)))
    (ξ : (k : ℕ) → O.Seed k) (n : ℕ) (x : p.E) : p.E →L[ℝ] p.E :=
  (executeAnswerAt O (algorithm p) () ξ n (0, x)).2

lemma historyJacobian_error (F : p.E → p.E) (O : Oracle p.E (p.E × (p.E →L[ℝ] p.E)))
    (ξ : (k : ℕ) → O.Seed k)
    (hO : ∀ history x seed, (O.answer history (0, x) seed).1 = F x ∧
      ‖(O.answer history (0, x) seed).2 - fderiv ℝ F x‖ ≤ p.δ) (n : ℕ) (x : p.E) :
    ‖historyJacobian O ξ n x - fderiv ℝ F x‖ ≤ p.δ :=
  (hO _ _ _).2

lemma execute_eq_iterate (F : p.E → p.E) (O : Oracle p.E (p.E × (p.E →L[ℝ] p.E)))
    (ξ : (k : ℕ) → O.Seed k)
    (hO : ∀ history x seed, (O.answer history (0, x) seed).1 = F x) (B : ℕ) :
    output O B ξ = ((trueStep F (historyJacobian O ξ))^[B] (initial, 0)).1.z := by
  unfold output execute
  erw [executeWithTrace_eq_executeIndexedState]
  change (executeIndexedState O (algorithm p) () ξ B).1.z = _
  erw [executeIndexedState_eq_executeAnswerAt]
  have he : (fun sc : State p × ℕ =>
      ((algorithm p).update sc.1 (executeAnswerAt O (algorithm p) () ξ sc.2 ((algorithm p).query sc.1)), sc.2 + 1)) =
      trueStep F (historyJacobian O ξ) := by
    funext sc
    unfold trueStep
    congr 1
    change update sc.1 (executeAnswerAt O (algorithm p) () ξ sc.2 (query sc.1)) = _
    congr 1
    have hq : query sc.1 = (0, (query sc.1).2) := by
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hq]
    apply Prod.ext
    · exact hO _ _ _
    · rfl
  erw [he]
  rfl

lemma execute_eq_outer (F : p.E → p.E) (O : Oracle p.E (p.E × (p.E →L[ℝ] p.E)))
    (ξ : (k : ℕ) → O.Seed k)
    (hO : ∀ history x seed, (O.answer history (0, x) seed).1 = F x)
    (hs : ∀ base k z Fz, Succeeds F (historyJacobian O ξ) base k z Fz) {B : ℕ}
    (hB : (outerSeq F (historyJacobian O ξ) (outerCount p)).1 ≤ B) :
    output O B ξ = (outerSeq F (historyJacobian O ξ) (outerCount p)).2.1 := by
  rw [execute_eq_iterate F O ξ hO]
  exact iterate_budget F _ hs hB

end

end LongTails.Proofs.InexactJacobianExecution
