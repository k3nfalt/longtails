import LongTails.Proofs.BirchNonEuclideanEvents

namespace LongTails.Proofs.BirchNonEuclideanEventLegality

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Algorithms.BirchNonEuclideanPhysical (packetCutoff)
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanEvents

structure Owned {m : ℕ} (t : Tuning) (regs : Registers m) (s : CodeState) : Prop where
  points : ∀ k, regs.points k ∈ (codeLayout t s).points 0
  momenta : ∀ k, regs.momenta k ∈ (codeLayout t s).vectors 0
  launchPoint : ∀ w, regs.launchPoint w ∈ (codeLayout t s).points (w.val + 1)
  launchMomentum : ∀ w, regs.launchMomentum w ∈ (codeLayout t s).vectors (w.val + 1)
  point : ∀ w, regs.point w ∈ (codeLayout t s).points (w.val + 1)
  momentum : ∀ w, regs.momentum w ∈ (codeLayout t s).vectors (w.val + 1)

lemma Owned.mono {m : ℕ} {t : Tuning} {regs : Registers m} {s s' : CodeState}
    (h : Owned t regs s) (hr : Retains t s s') : Owned t regs s' :=
  ⟨fun k => (hr 0).1 (h.points k), fun k => (hr 0).2 (h.momenta k),
    fun w => (hr _).1 (h.launchPoint w), fun w => (hr _).2 (h.launchMomentum w),
    fun w => (hr _).1 (h.point w), fun w => (hr _).2 (h.momentum w)⟩

lemma returnCode_valid (workers w x0 v0 x v : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (hw : w < workers) (hzero : 0 < workers)
    (hx0 : x0 ∈ (codeLayout t s).points w) (hv0 : v0 ∈ (codeLayout t s).vectors w)
    (hx : x ∈ (codeLayout t s).points w) (hv : v ∈ (codeLayout t s).vectors w) :
    let z := returnCode w x0 v0 x v s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      z.1.1 ∈ (codeLayout t z.2).vectors 0 ∧ z.1.2 ∈ (codeLayout t z.2).vectors 0 := by
  let s1 := (emit (.difference w x x0) s).2
  let dx := (emit (.difference w x x0) s).1
  let terms : List (Coefficient × ℕ) := [(.constant 1, v), (.constant (-1), v0)]
  let s2 := (emit (.mix w terms) s1).2
  let dm := (emit (.mix w terms) s1).1
  let s3 := (emit (.sendVector w 0 dx) s2).2
  let s4 := (emit (.sendVector w 0 dm) s3).2
  have h1 := difference_valid workers t s hs w x x0 hw hx hx0
  have hr1 := retains_emit t (.difference w x x0) s
  have ht : ∀ term ∈ terms, term.2 ∈ (codeLayout t s1).vectors w := by
    intro term hterm
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with rfl | rfl
    · exact (hr1 w).2 hv
    · exact (hr1 w).2 hv0
  have h2 := codeValid_emit workers t (.mix w terms) s1 h1.1 (mix_legal workers t s1 w terms hw ht)
  have hm2 := mix_member workers t s1 h1.1 w terms
  have hr2 := retains_trans t s s1 s2 hr1 (retains_emit t (.mix w terms) s1)
  have h3 := sendVector_valid workers t s2 h2 w 0 dx hw hzero
    (((retains_emit t (.mix w terms) s1) w).2 h1.2)
  have h4 := sendVector_valid workers t s3 h3.1 w 0 dm hw hzero
    (((retains_emit t (.sendVector w 0 dx) s2) w).2 hm2)
  have hr3 := retains_trans t s s2 s3 hr2 (retains_emit t (.sendVector w 0 dx) s2)
  exact ⟨h4.1, retains_trans t s s3 s4 hr3 (retains_emit t (.sendVector w 0 dm) s3),
    ((retains_emit t (.sendVector w 0 dm) s3) 0).2 h3.2, h4.2⟩

lemma commitCode_valid {m : ℕ} (k dx dm : ℕ) (t : Tuning) (regs : Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t regs s)
    (hx : dx ∈ (codeLayout t s).vectors 0) (hm : dm ∈ (codeLayout t s).vectors 0) :
    let z := commitCode k dx dm regs s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t z.1 z.2 := by
  let s1 := (emit (.move 0 (regs.points k) dx (.constant 1)) s).2
  let x := (emit (.move 0 (regs.points k) dx (.constant 1)) s).1
  let terms : List (Coefficient × ℕ) := [(.constant 1, regs.momenta k), (.constant 1, dm)]
  let s2 := (emit (.mix 0 terms) s1).2
  let v := (emit (.mix 0 terms) s1).1
  have h1 := codeValid_emit (m + 1) t (.move 0 (regs.points k) dx (.constant 1)) s hs
    ⟨by omega, ho.points k, hx, by norm_num [InstructionTemplate.instantiate, Coefficient.eval]⟩
  have hr1 := retains_emit t (.move 0 (regs.points k) dx (.constant 1)) s
  have hx1 := move_member (m + 1) t s hs 0 (regs.points k) dx (.constant 1)
  have ht : ∀ term ∈ terms, term.2 ∈ (codeLayout t s1).vectors 0 := by
    intro term hterm
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with rfl | rfl
    · exact (hr1 0).2 (ho.momenta k)
    · exact (hr1 0).2 hm
  have h2 := codeValid_emit (m + 1) t (.mix 0 terms) s1 h1 (mix_legal (m + 1) t s1 0 terms (by omega) ht)
  have hr2 := retains_trans t s s1 s2 hr1 (retains_emit t (.mix 0 terms) s1)
  have hv2 := mix_member (m + 1) t s1 h1 0 terms
  have hx2 := ((retains_emit t (.mix 0 terms) s1) 0).1 hx1
  have ho2 := ho.mono hr2
  refine ⟨h2, hr2, ?_⟩
  refine ⟨?_, ?_, ho2.launchPoint, ho2.launchMomentum, ho2.point, ho2.momentum⟩
  · intro j
    by_cases hj : j = k + 1
    · simpa only [commitCode, state_bind_apply, state_pure_apply, hj, Function.update_self] using hx2
    · simpa only [commitCode, state_bind_apply, state_pure_apply, Function.update_of_ne hj] using ho2.points j
  · intro j
    by_cases hj : j = k + 1
    · simpa only [commitCode, state_bind_apply, state_pure_apply, hj, Function.update_self] using hv2
    · simpa only [commitCode, state_bind_apply, state_pure_apply, Function.update_of_ne hj] using ho2.momenta j

lemma relaunchCode_valid {m : ℕ} (w : Fin m) (k : ℕ) (t : Tuning) (regs : Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t regs s) :
    let z := relaunchCode w k regs s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t z.1 z.2 := by
  let s1 := (emit (.sendPoint 0 (w.val + 1) (regs.points k)) s).2
  let s2 := (emit (.sendVector 0 (w.val + 1) (regs.momenta k)) s1).2
  have hw : w.val + 1 < m + 1 := by omega
  have h1 := sendPoint_valid (m + 1) t s hs 0 (w.val + 1) (regs.points k) (by omega) hw (ho.points k)
  have hr1 := retains_emit t (.sendPoint 0 (w.val + 1) (regs.points k)) s
  have h2 := sendVector_valid (m + 1) t s1 h1.1 0 (w.val + 1) (regs.momenta k) (by omega) hw
    ((hr1 0).2 (ho.momenta k))
  have hr2 := retains_trans t s s1 s2 hr1 (retains_emit t (.sendVector 0 (w.val + 1) (regs.momenta k)) s1)
  have hx2 := ((retains_emit t (.sendVector 0 (w.val + 1) (regs.momenta k)) s1) (w.val + 1)).1 h1.2
  have ho2 := ho.mono hr2
  refine ⟨h2.1, hr2, ?_⟩
  refine ⟨ho2.points, ho2.momenta, ?_, ?_, ?_, ?_⟩
  all_goals
    intro v
    by_cases hv : v = w
    · subst v
      first
      | simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_self] using hx2
      | simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_self] using h2.2
    · first
      | simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_of_ne hv] using ho2.launchPoint v
      | simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_of_ne hv] using ho2.launchMomentum v
      | simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_of_ne hv] using ho2.point v
      | simpa only [relaunchCode, state_bind_apply, state_pure_apply, Function.update_of_ne hv] using ho2.momentum v

lemma Owned.replacePrivate {m : ℕ} {t : Tuning} {regs : Registers m} {s : CodeState}
    (ho : Owned t regs s) (w : Fin m) (x v : ℕ)
    (hx : x ∈ (codeLayout t s).points (w.val + 1))
    (hv : v ∈ (codeLayout t s).vectors (w.val + 1)) :
    Owned t { regs with
      point := Function.update regs.point w x
      momentum := Function.update regs.momentum w v } s := by
  refine ⟨ho.points, ho.momenta, ho.launchPoint, ho.launchMomentum, ?_, ?_⟩
  · intro u
    by_cases hu : u = w
    · simpa only [hu, Function.update_self] using hx
    · simpa only [Function.update_of_ne hu] using ho.point u
  · intro u
    by_cases hu : u = w
    · simpa only [hu, Function.update_self] using hv
    · simpa only [Function.update_of_ne hu] using ho.momentum u

lemma eventCode_valid {m : ℕ} (H K R : ℕ) (t : Tuning) (ht : t.Valid)
    (e : Event m) (state : EventState m × Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t state.2 s) :
    let z := eventCode H K R e state s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧ Owned t z.1.2 z.2 := by
  cases e with
  | query w =>
      have hz := momentumStep_valid (m + 1) t ht (w.val + 1) H 0 (state.1.progress w)
        (state.2.point w, state.2.momentum w) s hs (by omega) (ho.point w) (ho.momentum w)
      rw [← privateStep_eq] at hz
      exact ⟨hz.1, hz.2.1, (ho.mono hz.2.1).replacePrivate w _ _ hz.2.2.1 hz.2.2.2⟩
  | complete w =>
      let returned := returnCode (w.val + 1) (state.2.launchPoint w) (state.2.launchMomentum w)
        (state.2.point w) (state.2.momentum w) s
      have hr := returnCode_valid (m + 1) (w.val + 1) _ _ _ _ t s hs (by omega) (by omega)
        (ho.launchPoint w) (ho.launchMomentum w) (ho.point w) (ho.momentum w)
      change CodeValid (m + 1) t returned.2 ∧ Retains t s returned.2 ∧
        returned.1.1 ∈ (codeLayout t returned.2).vectors 0 ∧
        returned.1.2 ∈ (codeLayout t returned.2).vectors 0 at hr
      have hor := ho.mono hr.2.1
      let next := eventStep K R state.1 (.complete w)
      by_cases ha : state.1.schedule.accepted.length < K
      · by_cases hg : state.1.schedule.accepted.length - state.1.schedule.source w ≤ R
        · let committed := commitCode state.1.schedule.accepted.length returned.1.1 returned.1.2 state.2 returned.2
          have hc := commitCode_valid state.1.schedule.accepted.length returned.1.1 returned.1.2 t state.2
            returned.2 hr.1 hor hr.2.2.1 hr.2.2.2
          have hrc := retains_trans t s returned.2 committed.2 hr.2.1 hc.2.1
          by_cases hn : next.schedule.accepted.length < K
          · have hl := relaunchCode_valid w next.schedule.accepted.length t committed.1 committed.2 hc.1 hc.2.2
            have hrl := retains_trans t s committed.2 _ hrc hl.2.1
            simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hg, hn,
              ite_true, next, committed, returned] using And.intro hl.1 (And.intro hrl hl.2.2)
          · simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hg, hn,
              ite_true, ite_false, next, committed, returned] using And.intro hc.1 (And.intro hrc hc.2.2)
        · by_cases hn : next.schedule.accepted.length < K
          · have hl := relaunchCode_valid w next.schedule.accepted.length t state.2 returned.2 hr.1 hor
            have hrl := retains_trans t s returned.2 _ hr.2.1 hl.2.1
            simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hg, hn,
              ite_true, ite_false, next, returned] using And.intro hl.1 (And.intro hrl hl.2.2)
          · simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, ha, hg, hn,
              ite_true, ite_false, next, returned] using And.intro hr.1 (And.intro hr.2.1 hor)
      · simpa only [eventCode, state_bind_apply, state_pure_apply, state_map_apply, ha,
          ite_false, returned] using And.intro hr.1 (And.intro hr.2.1 hor)

lemma launchCode_valid (workers w x v : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (hw : w < workers) (hzero : 0 < workers)
    (hx : x ∈ (codeLayout t s).points 0) (hv : v ∈ (codeLayout t s).vectors 0) :
    let z := launchCode w x v s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      x ∈ (codeLayout t z.2).points w ∧ v ∈ (codeLayout t z.2).vectors w := by
  let s1 := (emit (.sendPoint 0 w x) s).2
  have h1 := sendPoint_valid workers t s hs 0 w x hzero hw hx
  have hr1 := retains_emit t (.sendPoint 0 w x) s
  have h2 := sendVector_valid workers t s1 h1.1 0 w v hzero hw ((hr1 0).2 hv)
  exact ⟨h2.1, retains_trans t s s1 _ hr1 (retains_emit t (.sendVector 0 w v) s1),
    ((retains_emit t (.sendVector 0 w v) s1) w).1 h1.2, h2.2⟩

lemma launches_valid {m : ℕ} (ws : List (Fin m)) (x v : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid (m + 1) t s)
    (hx : x ∈ (codeLayout t s).points 0) (hv : v ∈ (codeLayout t s).vectors 0) :
    let z := (forIn ws () (fun w _ => ForInStep.yield <$> launchCode (w.val + 1) x v) :
      StateM CodeState Unit) s
    CodeValid (m + 1) t z.2 ∧ Retains t s z.2 ∧
      ∀ w ∈ ws, x ∈ (codeLayout t z.2).points (w.val + 1) ∧
        v ∈ (codeLayout t z.2).vectors (w.val + 1) := by
  induction ws generalizing s with
  | nil => exact ⟨hs, retains_refl t s, by simp⟩
  | cons w rest ih =>
      have h1 := launchCode_valid (m + 1) (w.val + 1) x v t s hs (by omega) (by omega) hx hv
      have h2 := ih (launchCode (w.val + 1) x v s).2 h1.1 ((h1.2.1 0).1 hx) ((h1.2.1 0).2 hv)
      rw [state_forIn_cons]
      change CodeValid (m + 1) t _ ∧ Retains t s _ ∧ ∀ u ∈ w :: rest, _
      refine ⟨h2.1, retains_trans t s _ _ h1.2.1 h2.2.1, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨(h2.2.1 _).1 h1.2.2.1, (h2.2.1 _).2 h1.2.2.2⟩
      · exact h2.2.2 u hu

lemma eventsStateCode_valid {m : ℕ} (H K B : ℕ) (events : List (Event m)) (t : Tuning) (ht : t.Valid) :
    let z := eventsStateCode H K B events {}
    CodeValid (m + 1) t z.2 ∧ Owned t z.1.2 z.2 := by
  have hx : 0 ∈ (codeLayout t {}).points 0 := by simp [codeLayout, codeInstructions, finalLayout]
  let initial := (localBatch 0 0 B).run {}
  have hi := localBatch_valid (m + 1) t 0 0 B {} (codeValid_initial (m + 1) t) (by omega) hx
  let sent := (forIn (List.finRange m) () (fun w _ => ForInStep.yield <$>
    launchCode (w.val + 1) 0 initial.1) : StateM CodeState Unit) initial.2
  have hl := launches_valid (List.finRange m) 0 initial.1 t initial.2 hi.1 ((hi.2.1 0).1 hx) hi.2.2
  let regs : Registers m := ⟨fun _ => 0, fun _ => initial.1, fun _ => 0,
    fun _ => initial.1, fun _ => 0, fun _ => initial.1⟩
  have ho : Owned t regs sent.2 := by
    refine ⟨fun _ => (hl.2.1 0).1 ((hi.2.1 0).1 hx), fun _ => (hl.2.1 0).2 hi.2.2, ?_, ?_, ?_, ?_⟩
    · intro w; exact (hl.2.2 w (List.mem_finRange w)).1
    · intro w; exact (hl.2.2 w (List.mem_finRange w)).2
    · intro w; exact (hl.2.2 w (List.mem_finRange w)).1
    · intro w; exact (hl.2.2 w (List.mem_finRange w)).2
  let Inv := fun (state : EventState m × Registers m) (s : CodeState) =>
    CodeValid (m + 1) t s ∧ Owned t state.2 s
  have hh := state_forIn_invariant (eventCode H K (packetCutoff H B)) events Inv
    (fun e _ state s h => by
      have he := eventCode_valid H K (packetCutoff H B) t ht e state s h.1 h.2
      exact ⟨he.1, he.2.2⟩) (({} : EventState m), regs) sent.2 ⟨hl.1, ho⟩
  exact hh

lemma eventsCode_valid {m : ℕ} (H K B : ℕ) (events : List (Event m)) (t : Tuning) (ht : t.Valid) :
    let z := (eventsCode H K B events).run {}
    CodeValid (m + 1) t z.2 ∧ ∀ k, z.1 k ∈ (codeLayout t z.2).points 0 := by
  have hh := eventsStateCode_valid H K B events t ht
  exact ⟨hh.1, hh.2.points⟩

lemma eventsProgram_legal {m : ℕ} (H K B : ℕ) (events : List (Event m)) (t : Tuning) (ht : t.Valid) :
    (eventsProgram H K B events t).Legal (m + 1) := by
  have hh := eventsCode_valid H K B events t ht
  exact ⟨hh.1.2, by change 0 < m + 1; omega, fun j => hh.2 j.val⟩

end LongTails.Proofs.BirchNonEuclideanEventLegality
