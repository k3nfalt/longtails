import LongTails.Proofs.LazyAnchoredOuter
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LazyAnchoredExecution

open OracleTemplate
open LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
open LongTails.Algorithms.LazyAnchoredExtraProximal
open LongTails.Proofs.LazyAnchoredInner
open LongTails.Proofs.LazyAnchoredOuter

noncomputable section

variable {p : Params}

def active : Phase → ℕ
  | .jacobian => 0
  | .centerValue => 1
  | .trial => 1
  | .correction => 1
  | .finished => 0

lemma update_count (s : State p) (r : p.E ⊕ (p.E →L[ℝ] p.E)) :
    (update s r).k + active (update s r).phase =
      s.k + active s.phase + (if (query s).1 = 1 then 1 else 0) := by
  classical
  rcases hs : s.phase with _ | _ | _ | _ | _
  · simp only [update, query, hs, active, ↓reduceIte]
  · simp only [update, query, hs, active, Fin.isValue, zero_ne_one, ↓reduceIte]
  · simp only [update, query, hs, Fin.isValue, zero_ne_one, ↓reduceIte, afterTrial]
    split_ifs
    · simp only [outerStart, nextPhase, active]
      split_ifs <;> simp
    · simp [active]
  · simp only [update, query, hs, Fin.isValue, zero_ne_one, ↓reduceIte, afterCorrection]
    split_ifs <;> simp [active]
  · simp only [update, query, hs, active, Fin.isValue, zero_ne_one, ↓reduceIte]

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

lemma channelCount_mono (F : p.E → p.E) (ch : Fin 2) {t t' : ℕ} (h : t ≤ t') :
    channelCount F ch t ≤ channelCount F ch t' := by
  unfold channelCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

lemma channelCount_le (F : p.E → p.E) (ch : Fin 2) (t : ℕ) : channelCount F ch t ≤ t := by
  unfold channelCount
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma jacobian_count (F : p.E → p.E) (t : ℕ) :
    channelCount F 1 t = ((trueStep F)^[t] (initial (p := p))).k +
      active ((trueStep F)^[t] (initial (p := p))).phase := by
  induction t with
  | zero =>
    simp [channelCount, initial, outerStart, nextPhase]
    split_ifs <;> simp [active]
  | succ t ih =>
    rw [channelCount_succ, ih, Function.iterate_succ_apply']
    unfold trueStep
    rw [update_count]


lemma regular_of_admissible (p : Params) (hp : spec.valid p) (F : p.E → p.E)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2) (h : spec.admissible p F O) :
    Regular p F :=
  ⟨hp.1, fun x => (h.2.2.1 x).hasFDerivAt, h.2.2.2.1, h.2.2.2.2.1⟩

lemma answer_eq (p : Params) (F : p.E → p.E)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2) (h : spec.admissible p F O)
    (hist : List ((Fin 2 × p.E) × (p.E ⊕ (p.E →L[ℝ] p.E)))) (q : Fin 2 × p.E)
    (seed : O.Seed hist.length) : O.answer hist q seed = reply F q := by
  obtain ⟨i, x⟩ := q
  fin_cases i
  · simp only [reply, Fin.isValue, Fin.zero_eta, zero_ne_one, ↓reduceIte]
    exact h.1 hist x seed
  · simp only [reply, Fin.isValue, Fin.mk_one, ↓reduceIte]
    exact h.2.1 hist x seed

lemma iterate_finished (F : p.E → p.E) (z Fz : p.E) (n : ℕ) :
    (trueStep F)^[n] (outerStart (outerCount p) z Fz) = outerStart (outerCount p) z Fz := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, step_finished]

lemma execution_output (p : Params) (hp : spec.valid p) (F : p.E → p.E)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2) (h : spec.admissible p F O)
    (budget : Fin 2 → ℕ) (hJ : outerCount p ≤ budget 1)
    (hF : totalTicks F (outerCount p) ≤ budget 0)
    (seed : (algorithm (p := p)).Seed) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (algorithm (p := p)) budget seed ξ = (outerSeq F (outerCount p)).1 := by
  have hreg := regular_of_admissible p hp F O h
  have hpp : 0 < p.D ∧ 0 < p.ε := ⟨hp.2.1, hp.2.2.1⟩
  obtain ⟨xs, hxs, hD⟩ := h.2.2.2.2.2
  obtain ⟨hall, -⟩ := aep_invariant F hreg hpp hxs hD (outerCount p) le_rfl
  have htot := iterate_total F (outerCount p) le_rfl (fun l hl => (hall l hl).1)
  set T := totalTicks F (outerCount p)
  let state : ℕ → State p := fun t => (trueStep F)^[t] (initial (p := p))
  let remaining : ℕ → Fin 2 → ℕ := fun t ch => budget ch - channelCount F ch t
  have hcountT : channelCount F 1 T = outerCount p := by
    rw [jacobian_count, htot]
    simp [outerStart, nextPhase, active]
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
    set ch := (query ((trueStep F)^[t] (initial (p := p)))).1 with hch
    have hq : ch = (query ((trueStep F)^[t] (initial (p := p)))).1 := rfl
    have h01 : ∀ c : Fin 2, c = 0 ∨ c = 1 := by decide
    rcases h01 ch with h0 | h1
    · have := channelCount_le F ch t
      have : t < budget 0 := lt_of_lt_of_le ht hF
      rw [h0] at *
      omega
    · have hsucc := channelCount_succ F 1 t
      have hmono := channelCount_mono F 1 (show t + 1 ≤ T by omega)
      rw [hcountT] at hmono
      rw [h1] at hq
      rw [← hq] at hsucc
      simp only [ite_true] at hsucc
      rw [h1]
      omega
  · intro t ht
    change (((trueStep F)^[t] (initial (p := p))).z) = _
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [add_comm, Function.iterate_add_apply, htot, iterate_finished]
    rfl
  · simp only [Fin.sum_univ_two]
    omega

end

end LongTails.Proofs.LazyAnchoredExecution
