import LongTails.Proofs.BirchNonEuclideanRennalaHistory

namespace LongTails.Proofs.BirchNonEuclideanRennalaHistoryLoop

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanRennalaCapture
open LongTails.Proofs.BirchNonEuclideanRennalaRecords
open LongTails.Proofs.BirchNonEuclideanRennalaAnchor
open LongTails.Proofs.BirchNonEuclideanRennalaBatch
open LongTails.Proofs.BirchNonEuclideanRennalaBatchAnchor
open LongTails.Proofs.BirchNonEuclideanRennalaMean
open LongTails.Proofs.BirchNonEuclideanRennalaHistory
open LongTails.Proofs.BirchNonEuclideanEvents (state_map_apply)

lemma relaunchCode_history {m : ℕ} (η : ℝ) (B k : ℕ) (w : Fin m) (regs : Registers m) (s : CodeState)
    (hh : History η B k regs s) :
    let z := relaunchCode w k regs s
    History η B k z.1 z.2 :=
  hh.quiet _ (relaunchCode_symbolic w k regs s _) rfl rfl rfl

lemma replyCode_history {m : ℕ} (K B : ℕ) (η : ℝ) (w : Fin m) (pub : State m) (regs : Registers m)
    (s : CodeState) (hv : CodeValid (m + 1) (canonicalTuning η B) s)
    (ho : Owned (canonicalTuning η B) pub regs s) (hc : Captured pub regs)
    (ha : ReadyAnchored (canonicalTuning η B) pub regs s) (hb : BatchShape B pub regs)
    (hba : BatchAnchored (canonicalTuning η B) pub regs s)
    (hh : History η B pub.round regs s) (he : (Event.reply w).Enabled pub) :
    let z := replyCode K B w pub regs s
    History η B (step K B pub (.reply w)).round z.1 z.2 := by
  let t := canonicalTuning η B
  let returned := (emit (.sendVector (w.val + 1) 0 (regs.reply w)) s).2
  let terms := regs.terms ++ [(Coefficient.constant (1 / (B : ℝ)), regs.reply w)]
  let next := (step K B pub (.reply w)).round
  have hn := codeValid_symbolic_next (m + 1) t s hv
  have hbound := codeValid_register_bound (m + 1) t s hv
  have hret := sendVector_valid (m + 1) t s hv (w.val + 1) 0 (regs.reply w)
    (by omega) (by omega) (ho.reply w he.2)
  have hor := ho.mono (retains_emit t (.sendVector (w.val + 1) 0 (regs.reply w)) s)
  have hsym : codeSymbolic t returned = { codeSymbolic t s with next := (codeSymbolic t s).next + 1 } := by
    rw [codeSymbolic_emit]
    rfl
  have hhist : History η B pub.round regs returned := hh.quiet _ hsym rfl rfl rfl
  have hraw : fresh pub w → ∀ term ∈ terms, RawRecord t returned term.2 (regs.points pub.round) := by
    intro hf term ht
    have hbefore : RawRecord t s term.2 (regs.points pub.round) := by
      rcases List.mem_append.mp ht with ht | ht
      · exact hba term ht
      · rw [List.mem_singleton.mp ht]
        have hr := ha w he.2
        rw [hc w he.1, hf] at hr
        exact hr
    exact hbefore.mono (codeExtends_emit s (.sendVector (w.val + 1) 0 (regs.reply w)))
      ((codeSymbolic_beforeNext t s).1 _ hbefore.query)
      (by rw [← hn]; exact hbound.1 _ _ (ho.points pub.round))
  have hcoef : ∀ term ∈ terms, term.1 = .constant (1 / (B : ℝ)) := by
    intro term ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hb.coefficients term ht
    · rw [List.mem_singleton.mp ht]
  have hdup : (terms.map Prod.snd).Nodup := by
    simp only [terms, List.map_append, List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨hb.distinct, by simp, ?_⟩
    intro a ha b hbm hab
    have hab' := hab.trans (List.mem_singleton.mp hbm)
    exact hb.pending_disjoint w he.2 (hab' ▸ ha)
  have htermsHist : History η B pub.round { regs with terms := terms } returned :=
    hhist.quiet (codeSymbolic t returned).next (by rfl) rfl rfl rfl
  by_cases hactive : pub.round < K
  · by_cases hf : fresh pub w
    · by_cases hcommit : commits B pub w
      · let committed := commitCode pub.round terms regs returned
        have hlen : terms.length = B := by
          simp only [terms, List.length_append, List.length_singleton, hb.length]
          exact hcommit.2
        have hcommitted := commitCode_history η B pub.round regs returned terms hret.1
          (fun j _ => hor.points j) hhist hlen hcoef hdup (hraw hf)
        have hnext : next = pub.round + 1 := by simp [next, step, hactive, hcommit]
        have hcom : History η B next committed.1 committed.2 := by rw [hnext]; exact hcommitted
        by_cases hl : next < K
        · have hlaunch := relaunchCode_history η B next w committed.1 committed.2 hcom
          simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
            hactive, hf, hcommit, hl, ite_true, next, returned, terms, committed] using hlaunch
        · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
            hactive, hf, hcommit, hl, ite_true, ite_false, next, returned, terms, committed] using hcom
      · have hnext : next = pub.round := by simp [next, step, hactive, hcommit]
        have hcom : History η B next { regs with terms := terms } returned := by
          rw [hnext]
          exact htermsHist
        by_cases hl : next < K
        · have hlaunch := relaunchCode_history η B next w { regs with terms := terms } returned hcom
          simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
            hactive, hf, hcommit, hl, ite_true, ite_false, next, returned, terms] using hlaunch
        · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
            hactive, hf, hcommit, hl, ite_true, ite_false, next, returned, terms] using hcom
    · have hcommit : ¬commits B pub w := fun hh => hf hh.1
      have hnext : next = pub.round := by simp [next, step, hactive, hcommit]
      have hcom : History η B next regs returned := by rw [hnext]; exact hhist
      by_cases hl : next < K
      · have hlaunch := relaunchCode_history η B next w regs returned hcom
        simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
          hactive, hf, hl, ite_true, ite_false, next, returned] using hlaunch
      · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
          hactive, hf, hl, ite_true, ite_false, next, returned] using hcom
  · have hnext : next = pub.round := by simp [next, step, hactive]
    have hcom : History η B next regs returned := by rw [hnext]; exact hhist
    simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply,
      hactive, ite_false, next, returned] using hcom

lemma eventCode_history {m : ℕ} (K B : ℕ) (η : ℝ) (e : Event m)
    (state : State m × Registers m) (s : CodeState)
    (hv : CodeValid (m + 1) (canonicalTuning η B) s)
    (ho : Owned (canonicalTuning η B) state.1 state.2 s) (hi : Invariant K B state.1)
    (hc : Captured state.1 state.2) (ha : ReadyAnchored (canonicalTuning η B) state.1 state.2 s)
    (hb : BatchShape B state.1 state.2) (hba : BatchAnchored (canonicalTuning η B) state.1 state.2 s)
    (hh : History η B state.1.round state.2 s) (he : e.Enabled state.1) :
    let z := eventCode K B e state s
    History η B z.1.1.round z.1.2 z.2 := by
  cases e with
  | reply w => exact replyCode_history K B η w state.1 state.2 s hv ho hc ha hb hba hh he
  | query w =>
      let t := canonicalTuning η B
      let out := (emit (.query (w.val + 1) (state.2.point w)) s).2
      have hn := codeValid_symbolic_next (m + 1) t s hv
      have hbound := codeValid_register_bound (m + 1) t s hv
      have hr := query_symbolic (w.val + 1) (state.2.point w) s t hn
      have hext := codeExtends_emit s (.query (w.val + 1) (state.2.point w))
      have hql : ∀ q ∈ (codeSymbolic t out).queries, ((codeSymbolic t out).queryPoints q).1 = 0 := by
        intro q hq
        rw [hr.2.2.1] at hq
        rcases Finset.mem_insert.mp hq with hq | hq
        · subst q
          rw [hr.2.1, hc w he.1]
          exact hh.main_linear (state.1.source w) (hi.source_le w)
        · rw [(codeExtends_symbolic t s out hext q ((codeSymbolic_beforeNext t s).1 q hq)).2.2.1]
          exact hh.queries_linear q hq
      exact hh.extend hext (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun j _ => by rw [← hn]; exact hbound.1 _ _ (ho.points j)) hr.2.2.2.1 hr.2.2.2.2.1 hql

lemma loop_history {m : ℕ} (K B : ℕ) (η : ℝ) (ht : (canonicalTuning η B).Valid) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState)
    (hv : CodeValid (m + 1) (canonicalTuning η B) s)
    (ho : Owned (canonicalTuning η B) state.1 state.2 s) (hi : Invariant K B state.1)
    (hc : Captured state.1 state.2) (ha : ReadyAnchored (canonicalTuning η B) state.1 state.2 s)
    (hb : BatchShape B state.1 state.2) (hba : BatchAnchored (canonicalTuning η B) state.1 state.2 s)
    (hh : History η B state.1.round state.2 s) (he : LegalFrom K B state.1 events) :
    let z := (forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s
    History η B z.1.1.round z.1.2 z.2 := by
  induction events generalizing state s with
  | nil => exact hh
  | cons e rest ih =>
      have hv' := eventCode_valid K B _ ht e state s hv ho he.1
      have hc' := eventCode_captured K B e state s hi hc
      have ha' := eventCode_anchored K B e state s _ hv ho ha
      have hb' := eventCode_batchShape K B e state s _ hv ho hb he.1
      have hba' := eventCode_batchAnchored K B e state s _ hv ho hc ha hba he.1
      have hh' := eventCode_history K B η e state s hv ho hi hc ha hb hba hh he.1
      have hi' : Invariant K B (eventCode K B e state s).1.1 := by
        rw [eventCode_public]
        exact step_invariant K B state.1 e hi he.1
      have hr : LegalFrom K B (eventCode K B e state s).1.1 rest := by
        rw [eventCode_public]
        exact he.2
      rw [state_forIn_cons]
      exact ih _ _ hv'.1 hv'.2.2 hi' hc' ha' hb' hba' hh' hr

lemma eventsStateCode_history {m : ℕ} (K B : ℕ) (η : ℝ) (ht : (canonicalTuning η B).Valid)
    (events : List (Event m)) (hK : 0 < K) (hB : 0 < B) (he : LegalFrom K B {} events) :
    let z := eventsStateCode K B events {}
    History η B z.1.1.round z.1.2 z.2 := by
  have hi := initialCode_valid m (canonicalTuning η B)
  rw [eventsStateCode_run]
  apply loop_history K B η ht events _ _ hi.1 hi.2 (invariant_initial K B hK hB) _ _ _ _
    (initialCode_history m B η) he
  · intro w _
    rw [initialCode_run]
  · intro w hw
    exact False.elim (Finset.notMem_empty w hw)
  · rw [initialCode_run]
    exact batchShape_initial m B
  · intro term ht
    rw [initialCode_run] at ht
    exact False.elim (List.not_mem_nil ht)

lemma completeTrace_history {m : ℕ} (K B : ℕ) (η : ℝ) (ht : (canonicalTuning η B).Valid)
    (events : List (Event m)) (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    let z := eventsStateCode K B events {}
    History η B K z.1.2 z.2 := by
  have hh := eventsStateCode_history K B η ht events hK hB he.1
  dsimp only at hh ⊢
  rw [eventsStateCode_public, he.2.1] at hh
  exact hh

end LongTails.Proofs.BirchNonEuclideanRennalaHistoryLoop
