import LongTails.Proofs.GeneralizedMirrorBlocks
import LongTails.Proofs.GeneralizedMirrorNoise
import LongTails.Proofs.AdaptiveIID

open MeasureTheory
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorExecution

namespace LongTails.Proofs.GeneralizedMirrorProcess

noncomputable def queryPoint (q : Public) (ell : ℝ) {m : ℕ} (s : State q m) : q.E :=
  mix s.A (stepWeight q ell s.A) s.x s.z

noncomputable def blockCenter (q : Public) (ell : ℝ) (m : ℕ)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω) : Dual q :=
  OracleTemplate.RobustGradient.pilotCenter (clipRadius q)
    (fun i : Fin m => g (queryPoint q ell s) (b ⟨i.val, by omega⟩))

noncomputable def blockDirection (q : Public) (ell : ℝ) (m : ℕ)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω) : Dual q :=
  OracleTemplate.RobustGradient.centeredClip (clipRadius q) (blockCenter q ell m g s b)
    (g (queryPoint q ell s) (b ⟨m, by omega⟩))

noncomputable def guardedProx (q : Public) (I : Instance q) (a : ℝ) (z : q.E)
    (v : Dual q) : q.E := if 0 < a then I.prox a z v else q.x0

noncomputable def phaseNext (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω) : State q m :=
  if 0 < s.A ∧ s.A < q.R ^ 2 / q.ε then
    let a := stepWeight q ell s.A
    let p := guardedProx q I a s.z (blockDirection q ell m g s b)
    { A := s.A + a
      x := mix s.A a s.x p
      z := p
      stage := 0
      received := 0
      pilot := fun _ => 0
      center := 0
      direction := 0 }
  else s

@[fun_prop] lemma measurable_queryPoint (q : Public) (ell : ℝ) (m : ℕ) :
    Measurable (queryPoint q ell (m := m)) := by
  unfold queryPoint mix
  fun_prop

lemma measurable_blockCenter (q : Public) (ell : ℝ) (m : ℕ)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (blockCenter q ell m g)) := by
  have hy := (measurable_queryPoint q ell m).comp
    (show Measurable (Prod.fst : State q m × (Fin (m + 2) → q.Ω) → State q m) from measurable_fst)
  have hv : Measurable (fun w : State q m × (Fin (m + 2) → q.Ω) =>
      fun i : Fin m => g (queryPoint q ell w.1) (w.2 ⟨i.val, by omega⟩)) := by
    apply Measurable.of_eval
    intro i
    exact hg.comp (hy.prodMk ((measurable_pi_apply ⟨i.val, by omega⟩).comp measurable_snd))
  exact (OracleTemplate.RobustGradient.measurable_pilotCenter m).comp
    ((measurable_const (a := clipRadius q)).prodMk hv)

lemma measurable_blockDirection (q : Public) (ell : ℝ) (m : ℕ)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (blockDirection q ell m g)) := by
  have hc := measurable_blockCenter q ell m hg
  have hy := (measurable_queryPoint q ell m).comp
    (show Measurable (Prod.fst : State q m × (Fin (m + 2) → q.Ω) → State q m) from measurable_fst)
  have hv := hg.comp (hy.prodMk ((measurable_pi_apply (⟨m, by omega⟩ : Fin (m + 2))).comp measurable_snd))
  exact hc.add ((OracleTemplate.GeneralNormClipping.measurable_clip (clipRadius q)).comp (hv.sub hc))

lemma measurable_phaseNext (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (hp : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2)) :
    Measurable (Function.uncurry (phaseNext q ell m I g)) := by
  have hf : Measurable (Prod.fst : State q m × (Fin (m + 2) → q.Ω) → State q m) := measurable_fst
  have hA := (measurable_state_A q m).comp hf
  have hx := (measurable_state_x q m).comp hf
  have hz := (measurable_state_z q m).comp hf
  have ha := (measurable_stepWeight q ell).comp hA
  have hv := measurable_blockDirection q ell m hg
  have hpoint := hp.comp (ha.prodMk (hz.prodMk hv))
  have hmix : Measurable (fun w : State q m × (Fin (m + 2) → q.Ω) =>
      mix w.1.A (stepWeight q ell w.1.A) w.1.x
        (guardedProx q I (stepWeight q ell w.1.A) w.1.z (blockDirection q ell m g w.1 w.2))) := by
    unfold mix
    exact ((hA.div (hA.add ha)).smul hx).add ((ha.div (hA.add ha)).smul hpoint)
  exact (measurable_state_mk (hA.add ha) hmix hpoint measurable_const measurable_const
    measurable_const measurable_const measurable_const).ite
      ((measurableSet_lt measurable_const hA).inter (measurableSet_lt hA measurable_const)) hf

def Entry {q : Public} {m : ℕ} (s : State q m) : Prop :=
  s.stage = 0 ∧ s.received = 0 ∧ s.pilot = fun _ => 0

lemma phaseNext_entry (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω)
    (hs : Entry s) : Entry (phaseNext q ell m I g s b) := by
  unfold phaseNext
  split_ifs
  · exact ⟨rfl, rfl, rfl⟩
  · exact hs

lemma phaseNext_positive (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (b : Fin (m + 2) → q.Ω) (hA : 0 < s.A) : 0 < (phaseNext q ell m I g s b).A := by
  have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell hA
  unfold phaseNext
  split_ifs
  · change 0 < s.A + stepWeight q ell s.A
    positivity
  · exact hA

lemma phaseNext_eq_rawAdvance (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (hm : 0 < m) (I : Instance q) (g : q.E → q.Ω → Dual q)
    (s : State q m) (hs : Entry s) (hA : 0 < s.A) (ξ : ℕ → q.Ω) (call : ℕ) :
    phaseNext q ell m I g s (fun i => ξ (call + i.val)) =
      rawAdvance q ell m I g ξ (m + 2) call s := by
  have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell hA
  by_cases hactive : s.A < q.R ^ 2 / q.ε
  · have he : { s with stage := 0, received := 0, pilot := fun _ => 0 } = s := by
      rcases s with ⟨A, x, z, stage, received, pilot, center, direction⟩
      rcases hs with ⟨hs, hr, hp⟩
      dsimp only at hs hr hp
      subst stage
      subst received
      subst pilot
      rfl
    have h := GeneralizedMirrorBlocks.rawAdvance_block q ell m I g ξ s call hactive hm
    dsimp only at h
    rw [he] at h
    rw [h]
    simp [phaseNext, hA, hactive, guardedProx, ha, blockDirection, blockCenter, queryPoint]
  · rw [rawAdvance_frozen q ell m I g ξ (m + 2) call s (le_of_not_gt hactive)]
    simp [phaseNext, hactive]

noncomputable def liftedNext (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (n : ℕ) (s : State q m) (b : Fin n → q.Ω) : State q m :=
  if h : n = m + 2 then phaseNext q ell m I g s (fun i => b ⟨i.val, by omega⟩) else s

lemma liftedNext_full (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (b : Fin (m + 2) → q.Ω) :
    liftedNext q ell m I g (m + 2) s b = phaseNext q ell m I g s b := by
  simp [liftedNext]

lemma measurable_liftedNext (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (hp : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2)) (n : ℕ) :
    Measurable (Function.uncurry (liftedNext q ell m I g n)) := by
  by_cases hn : n = m + 2
  · subst n
    simpa only [Function.uncurry_def, liftedNext_full] using measurable_phaseNext q ell m I hg hp
  · simpa only [Function.uncurry_def, liftedNext, dite_eq_right hn] using
      (measurable_fst : Measurable (Prod.fst : State q m × (Fin n → q.Ω) → State q m))

noncomputable def trace (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (ξ : ℕ → q.Ω) (k : ℕ) :
    State q m × (ℕ → q.Ω) :=
  OracleTemplate.StochasticGeneralized.blockTrace (fun _ => m + 2) (liftedNext q ell m I g) s ξ k

lemma trace_succ (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (ξ : ℕ → q.Ω) (k : ℕ) :
    trace q ell m I g s ξ (k + 1) =
      (phaseNext q ell m I g (trace q ell m I g s ξ k).1
        (fun i => (trace q ell m I g s ξ k).2 i.val),
       fun i => (trace q ell m I g s ξ k).2 (m + 2 + i)) := by
  exact (OracleTemplate.StochasticGeneralized.blockTrace_succ _ _ _ _ _).trans (by
    simp only [OracleTemplate.StochasticGeneralized.blockAdvance, liftedNext_full]
    rfl)

lemma trace_tape (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (ξ : ℕ → q.Ω) (k : ℕ) :
    (trace q ell m I g s ξ k).2 = fun i => ξ (k * (m + 2) + i) := by
  induction k with
  | zero => simp [trace, OracleTemplate.StochasticGeneralized.blockTrace]
  | succ k ih =>
    rw [trace_succ]
    dsimp only
    rw [ih]
    funext i
    simp only [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma trace_entry_positive (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (s : State q m)
    (hs : Entry s) (hA : 0 < s.A) (ξ : ℕ → q.Ω) (k : ℕ) :
    Entry (trace q ell m I g s ξ k).1 ∧ 0 < (trace q ell m I g s ξ k).1.A := by
  induction k with
  | zero => exact ⟨hs, hA⟩
  | succ k ih =>
    have he : trace q ell m I g s ξ (k + 1) =
        OracleTemplate.StochasticGeneralized.blockAdvance (fun _ => m + 2)
          (liftedNext q ell m I g) (trace q ell m I g s ξ k) :=
      OracleTemplate.StochasticGeneralized.blockTrace_succ _ _ _ _ _
    rw [he]
    simp only [OracleTemplate.StochasticGeneralized.blockAdvance, liftedNext_full]
    exact ⟨phaseNext_entry q ell m I g _ _ ih.1,
      phaseNext_positive q hq hell m I g _ _ ih.2⟩

lemma trace_eq_rawAdvance (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (hm : 0 < m) (I : Instance q) (g : q.E → q.Ω → Dual q)
    (s : State q m) (hs : Entry s) (hA : 0 < s.A) (ξ : ℕ → q.Ω) (k : ℕ) :
    (trace q ell m I g s ξ k).1 = rawAdvance q ell m I g ξ (k * (m + 2)) 0 s := by
  induction k with
  | zero => simp [trace, OracleTemplate.StochasticGeneralized.blockTrace, rawAdvance, OracleTemplate.StochasticGradient.advance]
  | succ k ih =>
    have hinv := trace_entry_positive q hq hell m I g s hs hA ξ k
    rw [trace_succ]
    dsimp only
    rw [trace_tape]
    rw [phaseNext_eq_rawAdvance q hq hell m hm I g _ hinv.1 hinv.2 ξ (k * (m + 2)), ih]
    simpa only [Nat.succ_mul, Nat.zero_add] using
      (rawAdvance_add q ell m I g ξ (k * (m + 2)) (m + 2) 0 s).symm

lemma execute_eq_trace (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (hm : 0 < m) (I : Instance q) (g : q.E → q.Ω → Dual q)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (K : ℕ) (ξ : ℕ → q.Ω) :
    OracleTemplate.execute
      { Seed := fun _ => q.Ω, law := P,
        answer := fun _ (_, request) seed => oracleReply I g request seed }
      (algorithm q ell m) (fun _ => K * (m + 2)) () ξ =
      (trace q ell m I g (initialState q m) ξ K).1.x := by
  rw [execute_eq_rawAdvance]
  have hA := GeneralizedMirrorTuning.initialWeight_pos q hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.2.2.2.2.1
  rw [trace_eq_rawAdvance q hq hell m hm I g _ ⟨rfl, rfl, rfl⟩ hA]

lemma measurable_trace (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (hp : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2))
    (s : State q m) (k : ℕ) : Measurable (fun ξ => trace q ell m I g s ξ k) := by
  induction k with
  | zero => exact measurable_const.prodMk measurable_id
  | succ k ih =>
    have hb : Measurable (fun ξ => fun i : Fin (m + 2) => (trace q ell m I g s ξ k).2 i.val) := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply i.val).comp ih.snd
    have ht : Measurable (fun ξ => fun i : ℕ => (trace q ell m I g s ξ k).2 (m + 2 + i)) := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply (m + 2 + i)).comp ih.snd
    simpa only [trace_succ, Function.comp_def, Function.uncurry_apply_pair] using
      ((measurable_phaseNext q ell m I hg hp).comp (ih.fst.prodMk hb)).prodMk ht

end LongTails.Proofs.GeneralizedMirrorProcess
