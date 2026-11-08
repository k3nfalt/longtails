import LongTails.Proofs.BirchNonEuclideanRennalaCosts
import LongTails.Proofs.BirchNonEuclideanRennalaLabels

namespace LongTails.Proofs.BirchNonEuclideanRennalaLegality

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLabels (reply_ready)
open LongTails.Proofs.BirchNonEuclideanEvents (state_map_apply)

structure Owned {m : ℕ} (t : Tuning) (pub : State m) (regs : Registers m) (s : CodeState) : Prop where
  points : ∀ k, regs.points k ∈ (codeLayout t s).points 0
  point : ∀ w, regs.point w ∈ (codeLayout t s).points (w.val + 1)
  reply : ∀ w ∈ pub.ready, regs.reply w ∈ (codeLayout t s).vectors (w.val + 1)
  terms : ∀ term ∈ regs.terms, term.2 ∈ (codeLayout t s).vectors 0

lemma Owned.mono {m : ℕ} {t : Tuning} {pub : State m} {regs : Registers m} {s s' : CodeState}
    (ho : Owned t pub regs s) (hr : Retains t s s') : Owned t pub regs s' :=
  ⟨fun k => (hr 0).1 (ho.points k), fun w => (hr _).1 (ho.point w),
    fun w hw => (hr _).2 (ho.reply w hw), fun term ht => (hr 0).2 (ho.terms term ht)⟩

lemma Owned.weaken {m : ℕ} {t : Tuning} {pub pub' : State m} {regs : Registers m} {s : CodeState}
    (ho : Owned t pub regs s) (hr : pub'.ready ⊆ pub.ready) : Owned t pub' regs s :=
  ⟨ho.points, ho.point, fun w hw => ho.reply w (hr hw), ho.terms⟩

lemma Owned.replaceTerms {m : ℕ} {t : Tuning} {pub : State m} {regs : Registers m} {s : CodeState}
    (ho : Owned t pub regs s) (terms : List (Coefficient × ℕ))
    (ht : ∀ term ∈ terms, term.2 ∈ (codeLayout t s).vectors 0) :
    Owned t pub { regs with terms := terms } s := ⟨ho.points, ho.point, ho.reply, ht⟩

lemma commitCode_valid {m : ℕ} (k : ℕ) (terms : List (Coefficient × ℕ))
    (t : Tuning) (ht : t.Valid) (pub : State m) (regs : Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t pub regs s)
    (hv : ∀ term ∈ terms, term.2 ∈ (codeLayout t s).vectors 0) :
    let z := commitCode k terms regs s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t pub z.1 z.2 := by
  let s1 := (emit (.mix 0 terms) s).2
  let mean := (emit (.mix 0 terms) s).1
  let s2 := (emit (.sharp 0 mean) s1).2
  let d := (emit (.sharp 0 mean) s1).1
  let s3 := (emit (.move 0 (regs.points k) d (.step k)) s2).2
  let x := (emit (.move 0 (regs.points k) d (.step k)) s2).1
  have h1 := codeValid_emit (m + 1) t (.mix 0 terms) s hs (mix_legal _ _ _ _ _ (by omega) hv)
  have hm := mix_member (m + 1) t s hs 0 terms
  have h2 := codeValid_emit (m + 1) t (.sharp 0 mean) s1 h1 ⟨by omega, hm⟩
  have hd := sharp_member (m + 1) t s1 h1 0 mean
  have hr1 := retains_emit t (.mix 0 terms) s
  have hr2 := retains_trans t s s1 s2 hr1 (retains_emit t (.sharp 0 mean) s1)
  have h3 := codeValid_emit (m + 1) t (.move 0 (regs.points k) d (.step k)) s2 h2
    ⟨by omega, (hr2 0).1 (ho.points k), hd, ht.1 k⟩
  have hx := move_member (m + 1) t s2 h2 0 (regs.points k) d (.step k)
  have hr3 := retains_trans t s s2 s3 hr2 (retains_emit t (.move 0 (regs.points k) d (.step k)) s2)
  have ho3 := ho.mono hr3
  refine ⟨h3, hr3, ?_⟩
  refine ⟨?_, ho3.point, ho3.reply, by simp [commitCode, state_bind_apply, state_map_apply]⟩
  intro j
  by_cases hj : j = k + 1
  · simpa only [commitCode, state_bind_apply, state_pure_apply, hj, Function.update_self] using hx
  · simpa only [commitCode, state_bind_apply, state_pure_apply, Function.update_of_ne hj] using ho3.points j

lemma relaunchCode_valid {m : ℕ} (w : Fin m) (k : ℕ) (t : Tuning) (pub : State m)
    (regs : Registers m) (s : CodeState) (hs : CodeValid (m + 1) t s) (ho : Owned t pub regs s) :
    let z := relaunchCode w k regs s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t pub z.1 z.2 := by
  have hv := sendPoint_valid (m + 1) t s hs 0 (w.val + 1) (regs.points k) (by omega) (by omega) (ho.points k)
  have hr := retains_emit t (.sendPoint 0 (w.val + 1) (regs.points k)) s
  have ho' := ho.mono hr
  refine ⟨hv.1, hr, ho'.points, ?_, ho'.reply, ho'.terms⟩
  intro v
  by_cases h : v = w
  · subst v
    simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_self] using hv.2
  · simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_of_ne h] using ho'.point v

lemma replyCode_valid {m : ℕ} (K B : ℕ) (w : Fin m) (t : Tuning) (ht : t.Valid)
    (pub : State m) (regs : Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t pub regs s) (hw : w ∈ pub.ready) :
    let z := replyCode K B w pub regs s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t pub z.1 z.2 := by
  let returned := (emit (.sendVector (w.val + 1) 0 (regs.reply w)) s).2
  have hret := sendVector_valid (m + 1) t s hs (w.val + 1) 0 (regs.reply w)
    (by omega) (by omega) (ho.reply w hw)
  have hr := retains_emit t (.sendVector (w.val + 1) 0 (regs.reply w)) s
  have hor := ho.mono hr
  let terms := regs.terms ++ [(.constant (1 / (B : ℝ)), regs.reply w)]
  have hterms : ∀ term ∈ terms, term.2 ∈ (codeLayout t returned).vectors 0 := by
    intro term hterm
    rcases List.mem_append.mp hterm with hold | hnew
    · exact hor.terms term hold
    · have heq := List.mem_singleton.mp hnew
      subst term
      exact hret.2
  let next := (step K B pub (.reply w)).round
  by_cases ha : pub.round < K
  · by_cases hf : fresh pub w
    · by_cases hc : commits B pub w
      · let committed := commitCode pub.round terms regs returned
        have hcommit := commitCode_valid pub.round terms t ht pub regs returned hret.1 hor hterms
        have hrc := retains_trans t s returned committed.2 hr hcommit.2.1
        by_cases hn : next < K
        · have hl := relaunchCode_valid w next t pub committed.1 committed.2 hcommit.1 hcommit.2.2
          have hrl := retains_trans t s committed.2 _ hrc hl.2.1
          simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hf, hc, hn,
            ite_true, next, committed, returned, terms] using And.intro hl.1 (And.intro hrl hl.2.2)
        · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hf, hc, hn,
            ite_true, ite_false, next, committed, returned, terms] using And.intro hcommit.1 (And.intro hrc hcommit.2.2)
      · have hot := hor.replaceTerms terms hterms
        by_cases hn : next < K
        · have hl := relaunchCode_valid w next t pub { regs with terms := terms } returned hret.1 hot
          have hrl := retains_trans t s returned _ hr hl.2.1
          simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hf, hc, hn,
            ite_true, ite_false, next, returned, terms] using And.intro hl.1 (And.intro hrl hl.2.2)
        · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hf, hc, hn,
            ite_true, ite_false, next, returned, terms] using And.intro hret.1 (And.intro hr hot)
    · by_cases hn : next < K
      · have hl := relaunchCode_valid w next t pub regs returned hret.1 hor
        have hrl := retains_trans t s returned _ hr hl.2.1
        simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hf, hn,
          ite_true, ite_false, next, returned] using And.intro hl.1 (And.intro hrl hl.2.2)
      · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hf, hn,
          ite_true, ite_false, next, returned] using And.intro hret.1 (And.intro hr hor)
  · simpa only [replyCode, state_bind_apply, state_pure_apply, state_map_apply, ha, ite_false, returned]
      using And.intro hret.1 (And.intro hr hor)

lemma eventCode_valid {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid)
    (e : Event m) (state : State m × Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s) (he : e.Enabled state.1) :
    let z := eventCode K B e state s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t z.1.1 z.1.2 z.2 := by
  cases e with
  | query w =>
      have hv := codeValid_emit (m + 1) t (.query (w.val + 1) (state.2.point w)) s hs
        ⟨by omega, ho.point w⟩
      have hq := query_member (m + 1) t s hs (w.val + 1) (state.2.point w)
      have hr := retains_emit t (.query (w.val + 1) (state.2.point w)) s
      have ho' := ho.mono hr
      refine ⟨hv, hr, ho'.points, ho'.point, ?_, ho'.terms⟩
      intro v hmem
      change v ∈ insert w state.1.ready at hmem
      by_cases h : v = w
      · subst v
        simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, Function.update_self] using hq
      · have hm : v ∈ state.1.ready := (Finset.mem_insert.mp hmem).resolve_left h
        simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, Function.update_of_ne h] using ho'.reply v hm
  | reply w =>
      have hh := replyCode_valid K B w t ht state.1 state.2 s hs ho he.2
      refine ⟨hh.1, hh.2.1, ?_⟩
      have hw : (step K B state.1 (.reply w)).ready ⊆ state.1.ready := by
        rw [reply_ready]
        exact Finset.erase_subset _ _
      exact hh.2.2.weaken hw

lemma launchCode_valid (workers w : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (hw : w < workers) (hzero : 0 < workers)
    (hx : 0 ∈ (codeLayout t s).points 0) :
    let z := launchCode w s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧ 0 ∈ (codeLayout t z.2).points w := by
  have hh := sendPoint_valid workers t s hs 0 w 0 hzero hw hx
  exact ⟨hh.1, retains_emit t (.sendPoint 0 w 0) s, hh.2⟩

lemma launches_valid {m : ℕ} (ws : List (Fin m)) (t : Tuning) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (hx : 0 ∈ (codeLayout t s).points 0) :
    let z := (forIn ws () (fun w _ => ForInStep.yield <$> launchCode (w.val + 1)) :
      StateM CodeState Unit) s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧
      ∀ w ∈ ws, 0 ∈ (codeLayout t z.2).points (w.val + 1) := by
  induction ws generalizing s with
  | nil => exact ⟨hs, retains_refl t s, by simp⟩
  | cons w rest ih =>
      have h1 := launchCode_valid (m + 1) (w.val + 1) t s hs (by omega) (by omega) hx
      have h2 := ih (launchCode (w.val + 1) s).2 h1.1 ((h1.2.1 0).1 hx)
      rw [state_forIn_cons]
      refine ⟨h2.1, retains_trans t _ _ _ h1.2.1 h2.2.1, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact (h2.2.1 _).1 h1.2.2
      · exact h2.2.2 v hv

lemma initialCode_valid (m : ℕ) (t : Tuning) :
    let z := initialCode m {}
    CodeValid (m + 1) t z.2 ∧ Owned t ({} : State m) z.1 z.2 := by
  have hh := launches_valid (List.finRange m) t {} (codeValid_initial (m + 1) t) (by simp [codeLayout, codeInstructions, finalLayout])
  rw [initialCode_run]
  dsimp only
  refine ⟨hh.1, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (hh.2.1 0).1 (by simp [codeLayout, codeInstructions, finalLayout])
  · intro w
    exact hh.2.2 w (List.mem_finRange w)
  · simp
  · simp

lemma loop_public {m : ℕ} (K B : ℕ) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState) :
    ((forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s).1.1 = events.foldl (step K B) state.1 := by
  induction events generalizing state s with
  | nil => rfl
  | cons e rest ih =>
      rw [state_forIn_cons, ih, eventCode_public]
      rfl

lemma loop_valid {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t state.1 state.2 s) (he : LegalFrom K B state.1 events) :
    let z := (forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t z.1.1 z.1.2 z.2 := by
  induction events generalizing state s with
  | nil => exact ⟨hs, retains_refl t s, ho⟩
  | cons e rest ih =>
      have hv := eventCode_valid K B t ht e state s hs ho he.1
      have hr : LegalFrom K B (eventCode K B e state s).1.1 rest := by
        rw [eventCode_public]
        exact he.2
      have hh := ih (eventCode K B e state s).1 (eventCode K B e state s).2 hv.1 hv.2.2 hr
      rw [state_forIn_cons]
      exact ⟨hh.1, retains_trans t _ _ _ hv.2.1 hh.2.1, hh.2.2⟩

lemma eventsStateCode_public {m : ℕ} (K B : ℕ) (events : List (Event m)) (s : CodeState) :
    (eventsStateCode K B events s).1.1 = run K B events := by
  rw [eventsStateCode_run]
  exact loop_public K B events _ _

lemma eventsStateCode_valid {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid) (events : List (Event m))
    (he : LegalFrom K B {} events) :
    let z := eventsStateCode K B events {}
    CodeValid (m + 1) t z.2 ∧ Owned t z.1.1 z.1.2 z.2 := by
  have hi := initialCode_valid m t
  have hl := loop_valid K B t ht events ({}, (initialCode m {}).1) (initialCode m {}).2 hi.1 hi.2 he
  exact ⟨hl.1, hl.2.2⟩

lemma eventsProgram_legal {m : ℕ} (K B : ℕ) (t : Tuning) (ht : t.Valid) (events : List (Event m))
    (he : LegalFrom K B {} events) : (eventsProgram K B events t).Legal (m + 1) := by
  have hv := eventsStateCode_valid K B t ht events he
  exact ⟨hv.1.2, by change 0 < m + 1; omega, fun j => hv.2.points j.val⟩

end LongTails.Proofs.BirchNonEuclideanRennalaLegality
