import LongTails.Proofs.HomotopyNewtonOuter
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HomotopyNewtonExecution

open OracleTemplate
open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP
open LongTails.Proofs.HomotopyNewtonSchedule
open LongTails.Proofs.MonotoneTensorBounds
open LongTails.Proofs.StiffNewtonStage
open LongTails.Proofs.HomotopyNewtonInner
open LongTails.Proofs.HomotopyNewtonOuter

noncomputable section

variable {p : Params}

def reply (F : p.E → p.E) : Fin 2 × p.E → p.E ⊕ (p.E →L[ℝ] p.E)
  | (i, x) => if i = 0 then Sum.inl (F x) else Sum.inr (fderiv ℝ F x)

def trueStep (F : p.E → p.E) (s : State p) : State p := update s (reply F (query s))

def attemptStart (k : ℕ) (z Fz Fc : p.E) (j : ℕ) : State p :=
  ⟨.newtonValue, k, z, Fz, Fc, j, 0, center p k z Fz, 0⟩

def iterState (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) (ph : Phase) : State p :=
  ⟨ph, k, z, Fz, F (center p k z Fz), j, i, innerSeq F k z Fz j i, 0⟩

lemma state_g (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) (ph : Phase) :
    (iterState F k z Fz j i ph).g = gval F k z Fz := rfl

lemma step_center (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (hk : k ≠ outerCount p) :
    trueStep F (outerStart k z Fz) =
      if gval F k z Fz = 0 then outerStart (k + 1) (center p k z Fz) (F (center p k z Fz))
      else attemptStart k z Fz (F (center p k z Fz)) 0 := by
  classical
  have hph : (outerStart (p := p) k z Fz).phase = .centerValue := by
    simp [outerStart, nextPhase, hk]
  simp only [trueStep, update, query, hph, reply, Fin.isValue, ↓reduceIte, readValue,
    afterCenter]
  rfl

lemma attemptStart_eq (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) :
    attemptStart k z Fz (F (center p k z Fz)) j = iterState F k z Fz j 0 .newtonValue := rfl

lemma step_value (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    trueStep F (iterState F k z Fz j i .newtonValue) =
      ⟨.newtonJac, k, z, Fz, F (center p k z Fz), j, i, innerSeq F k z Fz j i,
        F (innerSeq F k z Fz j i)⟩ := by
  simp only [trueStep, update, query, iterState, reply, Fin.isValue, ↓reduceIte, readValue]

lemma newtonStep_eq (F : p.E → p.E) (b : ℝ) (v y : p.E) :
    newtonStep p b v y (F y) (fderiv ℝ F y) = newton F b v y := rfl

lemma step_jac (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j i : ℕ) :
    trueStep F ⟨.newtonJac, k, z, Fz, F (center p k z Fz), j, i, innerSeq F k z Fz j i,
        F (innerSeq F k z Fz j i)⟩ =
      if i + 1 = programLength p k (gval F k z Fz) j then iterState F k z Fz j (i + 1) .certify
      else iterState F k z Fz j (i + 1) .newtonValue := by
  simp only [trueStep, update, query, reply, Fin.isValue, one_ne_zero, ↓reduceIte, readJacobian,
    afterJacobian]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

lemma iterate_attempt (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) :
    ∀ i, i < programLength p k (gval F k z Fz) j →
      (trueStep F)^[2 * i] (iterState F k z Fz j 0 .newtonValue) =
        iterState F k z Fz j i .newtonValue
  | 0, _ => rfl
  | i + 1, hi => by
    rw [show 2 * (i + 1) = 2 + 2 * i by ring, Function.iterate_add_apply,
      iterate_attempt F k z Fz j i (by omega)]
    rw [show (trueStep F)^[2] (iterState F k z Fz j i .newtonValue) =
      trueStep F (trueStep F (iterState F k z Fz j i .newtonValue)) from rfl,
      step_value, step_jac]
    simp only [show i + 1 ≠ programLength p k (gval F k z Fz) j by omega, ↓reduceIte]

lemma iterate_attempt_full (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) :
    (trueStep F)^[2 * programLength p k (gval F k z Fz) j]
        (iterState F k z Fz j 0 .newtonValue) =
      iterState F k z Fz j (programLength p k (gval F k z Fz) j) .certify := by
  have hpos : 0 < programLength p k (gval F k z Fz) j := by unfold programLength; omega
  obtain ⟨n, hn⟩ : ∃ n, programLength p k (gval F k z Fz) j = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hn, show 2 * (n + 1) = 2 + 2 * n by ring, Function.iterate_add_apply,
    iterate_attempt F k z Fz j n (by omega)]
  rw [show (trueStep F)^[2] (iterState F k z Fz j n .newtonValue) =
    trueStep F (trueStep F (iterState F k z Fz j n .newtonValue)) from rfl, step_value, step_jac]
  simp only [hn, ↓reduceIte]

lemma step_certify_pos (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) (hacc : acc F k z Fz j) :
    trueStep F (iterState F k z Fz j (programLength p k (gval F k z Fz) j) .certify) =
      outerStart (k + 1) (attemptPoint F k z Fz j) (F (attemptPoint F k z Fz j)) := by
  simp only [trueStep, update, query, iterState, reply, Fin.isValue, ↓reduceIte, readValue,
    afterCertify]
  split_ifs with hc
  · rfl
  · exact absurd hacc hc

lemma step_certify_neg (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) (hacc : ¬ acc F k z Fz j) :
    trueStep F (iterState F k z Fz j (programLength p k (gval F k z Fz) j) .certify) =
      iterState F k z Fz (j + 1) 0 .newtonValue := by
  simp only [trueStep, update, query, iterState, reply, Fin.isValue, ↓reduceIte, readValue,
    afterCertify]
  split_ifs with hc
  · exact absurd hc hacc
  · rfl

def attemptTicks (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) : ℕ :=
  2 * programLength p k (gval F k z Fz) j + 1

def failTicks (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : ℕ → ℕ
  | 0 => 0
  | j + 1 => attemptTicks F k z Fz j + failTicks F k z Fz j

lemma iterate_attempt_pos (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) (hacc : acc F k z Fz j) :
    (trueStep F)^[attemptTicks F k z Fz j] (iterState F k z Fz j 0 .newtonValue) =
      outerStart (k + 1) (attemptPoint F k z Fz j) (F (attemptPoint F k z Fz j)) := by
  unfold attemptTicks
  rw [Function.iterate_succ_apply', iterate_attempt_full, step_certify_pos F k z Fz j hacc]

lemma iterate_attempt_neg (F : p.E → p.E) (k : ℕ) (z Fz : p.E) (j : ℕ) (hacc : ¬ acc F k z Fz j) :
    (trueStep F)^[attemptTicks F k z Fz j] (iterState F k z Fz j 0 .newtonValue) =
      iterState F k z Fz (j + 1) 0 .newtonValue := by
  unfold attemptTicks
  rw [Function.iterate_succ_apply', iterate_attempt_full, step_certify_neg F k z Fz j hacc]

lemma iterate_fails (F : p.E → p.E) (k : ℕ) (z Fz : p.E) :
    ∀ j, (∀ l < j, ¬ acc F k z Fz l) →
      (trueStep F)^[failTicks F k z Fz j] (iterState F k z Fz 0 0 .newtonValue) =
        iterState F k z Fz j 0 .newtonValue
  | 0, _ => rfl
  | j + 1, h => by
    rw [failTicks, Function.iterate_add_apply, iterate_fails F k z Fz j (fun l hl => h l (by omega)),
      iterate_attempt_neg F k z Fz j (h j (by omega))]

def outerTicks (F : p.E → p.E) (k : ℕ) (z Fz : p.E) : ℕ := by
  classical
  exact if gval F k z Fz = 0 then 1
    else 1 + (failTicks F k z Fz (firstAttempt F k z Fz) +
      attemptTicks F k z Fz (firstAttempt F k z Fz))

lemma iterate_outer (F : p.E → p.E) {k : ℕ} {z Fz : p.E} (hk : k ≠ outerCount p)
    (h : Succeeds F k z Fz) :
    (trueStep F)^[outerTicks F k z Fz] (outerStart k z Fz) =
      outerStart (k + 1) (nextPoint F k z Fz) (F (nextPoint F k z Fz)) := by
  classical
  by_cases hg : gval F k z Fz = 0
  · have hn : nextPoint F k z Fz = center p k z Fz := by simp [nextPoint, hg]
    have ht : outerTicks F k z Fz = 1 := by simp [outerTicks, hg]
    rw [ht, Function.iterate_one, step_center F k z Fz hk, hn]
    simp [hg]
  · have hex : ∃ j, acc F k z Fz j := by
      rcases h with h0 | h0
      · exact absurd h0 hg
      · exact h0
    obtain ⟨hacc, hmin⟩ := first_spec hex
    have hn : nextPoint F k z Fz = attemptPoint F k z Fz (firstAttempt F k z Fz) := by
      simp [nextPoint, hg]
    have ht : outerTicks F k z Fz = attemptTicks F k z Fz (firstAttempt F k z Fz) +
        failTicks F k z Fz (firstAttempt F k z Fz) + 1 := by
      simp only [outerTicks, hg, ↓reduceIte]; ring
    rw [ht, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one,
      step_center F k z Fz hk]
    simp only [hg, ↓reduceIte]
    rw [attemptStart_eq, iterate_fails F k z Fz _ hmin, iterate_attempt_pos F k z Fz _ hacc, hn]

def totalTicks (F : p.E → p.E) : ℕ → ℕ
  | 0 => 0
  | k + 1 => outerTicks F k (outerSeq F k).1 (outerSeq F k).2 + totalTicks F k

lemma iterate_total (F : p.E → p.E) :
    ∀ k, k ≤ outerCount p → (∀ l < k, Succeeds F l (outerSeq F l).1 (outerSeq F l).2) →
      (trueStep F)^[totalTicks F k] initial = outerStart k (outerSeq F k).1 (outerSeq F k).2
  | 0, _, _ => rfl
  | k + 1, hk, hs => by
    rw [totalTicks, Function.iterate_add_apply,
      iterate_total F k (by omega) (fun l hl => hs l (by omega)),
      iterate_outer F (by omega) (hs k (by omega))]
    rfl

lemma step_finished (F : p.E → p.E) (z Fz : p.E) :
    trueStep F (outerStart (outerCount p) z Fz) = outerStart (outerCount p) z Fz := by
  have hph : (outerStart (p := p) (outerCount p) z Fz).phase = .finished := by
    simp [outerStart, nextPhase]
  simp only [trueStep, update, hph]

lemma iterate_finished (F : p.E → p.E) (z Fz : p.E) (n : ℕ) :
    (trueStep F)^[n] (outerStart (outerCount p) z Fz) = outerStart (outerCount p) z Fz := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, step_finished]

def channelCount (F : p.E → p.E) (ch : Fin 2) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => (query ((trueStep F)^[u] (initial (p := p)))).1 = ch)).card

lemma channelCount_succ (F : p.E → p.E) (ch : Fin 2) (t : ℕ) :
    channelCount F ch (t + 1) = channelCount F ch t +
      (if (query ((trueStep F)^[t] (initial (p := p)))).1 = ch then 1 else 0) := by
  classical
  unfold channelCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma channelCount_le (F : p.E → p.E) (ch : Fin 2) (t : ℕ) : channelCount F ch t ≤ t := by
  unfold channelCount
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma answer_eq (p : Params) (F : p.E → p.E)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2) (h : spec.admissible p F O)
    (hist : List ((Fin 2 × p.E) × (p.E ⊕ (p.E →L[ℝ] p.E)))) (q : Fin 2 × p.E)
    (seed : O.Seed hist.length) : O.answer hist q seed = reply F q := by
  obtain ⟨i, x⟩ := q
  have h01 : ∀ c : Fin 2, c = 0 ∨ c = 1 := by decide
  rcases h01 i with h0 | h1
  · subst h0; simp only [reply, ↓reduceIte]; exact h.1 hist x seed
  · subst h1; simp only [reply, Fin.isValue, one_ne_zero, ↓reduceIte]; exact h.2.1 hist x seed

lemma execution_output (p : Params) (F : p.E → p.E)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2) (h : spec.admissible p F O)
    (hs : ∀ l < outerCount p, Succeeds F l (outerSeq F l).1 (outerSeq F l).2)
    (budget : Fin 2 → ℕ) (hb : ∀ ch, totalTicks F (outerCount p) ≤ budget ch)
    (seed : (algorithm (p := p)).Seed) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (algorithm (p := p)) budget seed ξ = (outerSeq F (outerCount p)).1 := by
  have htot := iterate_total F (outerCount p) le_rfl hs
  set T := totalTicks F (outerCount p)
  let state : ℕ → State p := fun t => (trueStep F)^[t] (initial (p := p))
  let remaining : ℕ → Fin 2 → ℕ := fun t ch => budget ch - channelCount F ch t
  apply OracleTemplate.execute_eq_of_safe_prefix O (algorithm (p := p)) budget seed ξ state
    remaining T (outerSeq F (outerCount p)).1
  · rfl
  · intro hist
    change (trueStep F)^[hist.length + 1] initial =
      update ((trueStep F)^[hist.length] initial)
        (O.answer hist (query ((trueStep F)^[hist.length] initial)) (ξ hist.length))
    rw [answer_eq p F O h, Function.iterate_succ_apply']
    rfl
  · funext ch; simp [remaining, channelCount]
  · intro t
    change (fun ch => budget ch - channelCount F ch (t + 1)) =
      Function.update (fun ch => budget ch - channelCount F ch t)
        (query ((trueStep F)^[t] (initial (p := p)))).1
        (budget (query ((trueStep F)^[t] (initial (p := p)))).1 -
          channelCount F (query ((trueStep F)^[t] (initial (p := p)))).1 t - 1)
    funext ch
    rw [channelCount_succ]
    by_cases hc : (query ((trueStep F)^[t] (initial (p := p)))).1 = ch
    · subst hc
      simp only [ite_true, Function.update_self]
      omega
    · have hc' : ch ≠ (query ((trueStep F)^[t] (initial (p := p)))).1 := fun e => hc e.symm
      simp only [hc, ite_false, add_zero, Function.update_of_ne hc']
  · intro t ht
    change 0 < budget (query ((trueStep F)^[t] (initial (p := p)))).1 -
      channelCount F (query ((trueStep F)^[t] (initial (p := p)))).1 t
    have h1 := channelCount_le F (query ((trueStep F)^[t] (initial (p := p)))).1 t
    have h2 := hb (query ((trueStep F)^[t] (initial (p := p)))).1
    omega
  · intro t ht
    change (((trueStep F)^[t] (initial (p := p))).z) = _
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [add_comm, Function.iterate_add_apply, htot, iterate_finished]
    rfl
  · have := hb 0
    simp only [Fin.sum_univ_two]
    omega

end

end LongTails.Proofs.HomotopyNewtonExecution
