import LongTails.Proofs.BirchNonEuclideanEventCounter

namespace LongTails.Proofs.BirchNonEuclideanEventMeaning

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Algorithms.BirchNonEuclideanTrajectories
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanEvents
open LongTails.Proofs.BirchNonEuclideanReplay
open LongTails.Proofs.BirchNonEuclideanEventLegality
open LongTails.Proofs.BirchNonEuclideanEventCounter

def readValues {d m : ℕ} (mem : Memory d) (regs : Registers m) : Values d m :=
  ⟨fun k => mem.points (regs.points k), fun k => mem.vectors (regs.momenta k),
    fun w => mem.points (regs.launchPoint w), fun w => mem.vectors (regs.launchMomentum w),
    fun w => mem.points (regs.point w), fun w => mem.vectors (regs.momentum w)⟩

lemma readValues_old {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s s' : CodeState) (regs : Registers m)
    (hs : CodeValid (m + 1) t s) (ho : Owned t regs s) (he : CodeExtends s s') :
    readValues (codeMemory p lmo response t s') regs = readValues (codeMemory p lmo response t s) regs := by
  have hn : s.next = (codeMemory p lmo response t s).next := by
    rw [codeMemory_next, ← codeLayout_next t s]
    exact hs.1
  have hb := codeValid_register_bound (m + 1) t s hs
  apply Values.ext
  · funext k
    exact (codeMemory_old p lmo response t s s' he _ (hn ▸ hb.1 0 _ (ho.points k))).1
  · funext k
    exact (codeMemory_old p lmo response t s s' he _ (hn ▸ hb.2 0 _ (ho.momenta k))).2
  · funext w
    exact (codeMemory_old p lmo response t s s' he _ (hn ▸ hb.1 _ _ (ho.launchPoint w))).1
  · funext w
    exact (codeMemory_old p lmo response t s s' he _ (hn ▸ hb.2 _ _ (ho.launchMomentum w))).2
  · funext w
    exact (codeMemory_old p lmo response t s s' he _ (hn ▸ hb.1 _ _ (ho.point w))).1
  · funext w
    exact (codeMemory_old p lmo response t s s' he _ (hn ▸ hb.2 _ _ (ho.momentum w))).2

lemma readValues_private {d m : ℕ} (mem : Memory d) (regs : Registers m) (w : Fin m) (x v : ℕ) :
    readValues mem { regs with
      point := Function.update regs.point w x
      momentum := Function.update regs.momentum w v } =
    { readValues mem regs with
      point := Function.update (readValues mem regs).point w (mem.points x)
      momentum := Function.update (readValues mem regs).momentum w (mem.vectors v) } := by
  ext <;> simp [readValues, Function.update_apply, apply_ite]

lemma readValues_global {d m : ℕ} (mem : Memory d) (regs : Registers m) (k x v : ℕ) :
    readValues mem { regs with
      points := Function.update regs.points k x
      momenta := Function.update regs.momenta k v } =
    { readValues mem regs with
      points := Function.update (readValues mem regs).points k (mem.points x)
      momenta := Function.update (readValues mem regs).momenta k (mem.vectors v) } := by
  ext <;> simp [readValues, Function.update_apply, apply_ite]

lemma returnCode_extends (w x0 v0 x v : ℕ) : BuildExtends (returnCode w x0 v0 x v) := by
  unfold returnCode
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dx
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dm
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

lemma commitCode_extends {m : ℕ} (k dx dm : ℕ) (regs : Registers m) : BuildExtends (commitCode k dx dm regs) := by
  unfold commitCode
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro x
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro v
  exact buildExtends_pure _

lemma relaunchCode_extends {m : ℕ} (w : Fin m) (k : ℕ) (regs : Registers m) : BuildExtends (relaunchCode w k regs) := by
  unfold relaunchCode
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

lemma privateStep_values {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (η : ℝ) (B H h : ℕ)
    (w : Fin m) (regs : Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) (canonicalTuning η B) s) (ho : Owned (canonicalTuning η B) regs s) :
    let t := canonicalTuning η B
    let z := privateStep (w.val + 1) (regs.point w) (regs.momentum w) H h s
    let old := readValues (codeMemory p lmo response t s) regs
    let v := (1 / (B : ℝ)) • response (codeCalls s) (old.point w) + (1 - 1 / (B : ℝ)) • old.momentum w
    let x := old.point w + (1 / (H : ℝ) * η) • (dualNorm p.N v • lmo v)
    readValues (codeMemory p lmo response t z.2)
      { regs with
        point := Function.update regs.point w z.1.1
        momentum := Function.update regs.momentum w z.1.2 } =
      { old with
        point := Function.update old.point w x
        momentum := Function.update old.momentum w v } := by
  dsimp only
  rw [readValues_private]
  have he := momentumStep_extends (w.val + 1) H 0 h (regs.point w, regs.momentum w) s
  rw [← privateStep_eq] at he
  rw [readValues_old p lmo response (canonicalTuning η B) s _ regs hs ho he]
  have hn : s.next = 1 + s.instructions.length := hs.1.trans (codeLayout_next _ _)
  have hm := (codeValid_register_bound (m + 1) (canonicalTuning η B) s hs).2 _ _ (ho.momentum w)
  have hh := momentumStep_memory p lmo response (canonicalTuning η B) (w.val + 1) H 0 h
    (regs.point w, regs.momentum w) s hn hm
  rw [← privateStep_eq] at hh
  rw [hh.1, hh.2]
  rfl

lemma commitCode_values {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (k dx dm : ℕ) (regs : Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) t s) (ho : Owned t regs s) :
    let z := commitCode k dx dm regs s
    let mem := codeMemory p lmo response t s
    let old := readValues mem regs
    readValues (codeMemory p lmo response t z.2) z.1 =
      { old with
        points := Function.update old.points (k + 1) (old.points k + mem.vectors dx)
        momenta := Function.update old.momenta (k + 1) (old.momenta k + mem.vectors dm) } := by
  let z := commitCode k dx dm regs s
  let x := (emit (.move 0 (regs.points k) dx (.constant 1)) s).1
  let v := (emit (.mix 0 [(.constant 1, regs.momenta k), (.constant 1, dm)])
    (emit (.move 0 (regs.points k) dx (.constant 1)) s).2).1
  have hr : z.1 = { regs with
      points := Function.update regs.points (k + 1) x
      momenta := Function.update regs.momenta (k + 1) v } := rfl
  have hn : s.next = 1 + s.instructions.length := hs.1.trans (codeLayout_next _ _)
  have hm := commitCode_memory p lmo response t k dx dm regs s hn
  change (codeMemory p lmo response t z.2).points (z.1.points (k + 1)) = _ ∧
    (codeMemory p lmo response t z.2).vectors (z.1.momenta (k + 1)) = _ at hm
  rw [hr] at hm
  simp only [Function.update_self] at hm
  dsimp only
  change readValues (codeMemory p lmo response t z.2) z.1 = _
  rw [hr, readValues_global, readValues_old p lmo response t s z.2 regs hs ho (commitCode_extends k dx dm regs s)]
  rw [hm.1, hm.2]
  rfl

lemma relaunchCode_values {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (w : Fin m) (k : ℕ) (regs : Registers m) (s : CodeState) :
    let z := relaunchCode w k regs s
    let old := readValues (codeMemory p lmo response t s) regs
    readValues (codeMemory p lmo response t z.2) z.1 =
      { old with
        launchPoint := Function.update old.launchPoint w (old.points k)
        launchMomentum := Function.update old.launchMomentum w (old.momenta k)
        point := Function.update old.point w (old.points k)
        momentum := Function.update old.momentum w (old.momenta k) } := by
  have hm := relaunchCode_memory p lmo response t w k regs s
  have hr : (relaunchCode w k regs s).1 = { regs with
      launchPoint := Function.update regs.launchPoint w (regs.points k)
      launchMomentum := Function.update regs.launchMomentum w (regs.momenta k)
      point := Function.update regs.point w (regs.points k)
      momentum := Function.update regs.momentum w (regs.momenta k) } := rfl
  dsimp only at hm ⊢
  rw [hr]
  ext <;> simp only [readValues, hm.1, hm.2.1, Function.update_apply, apply_ite]

lemma eventCode_values {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K R : ℕ) (e : Event m) (state : EventState m × Registers m) (s : CodeState)
    (hs : CodeValid (m + 1) (canonicalTuning η B) s) (ho : Owned (canonicalTuning η B) state.2 s)
    (hr : ∀ w, e = .query w → ∀ x, response (codeCalls s) x =
      labelled (Sum.inr (w, state.1.schedule.serial w, state.1.progress w)) x) :
    let t := canonicalTuning η B
    let z := eventCode H K R e state s
    (z.1.1, readValues (codeMemory p lmo response t z.2) z.1.2) =
      eventValues p lmo labelled η B H K R e (state.1, readValues (codeMemory p lmo response t s) state.2) := by
  dsimp only
  apply Prod.ext
  · rw [eventCode_public]
    cases e <;> rfl
  · cases e with
    | query w =>
        have hh := privateStep_values p lmo response η B H (state.1.progress w) w state.2 s hs ho
        dsimp only at hh
        rw [hr w rfl] at hh
        simpa only [eventCode, eventValues, state_bind_apply, state_pure_apply] using hh
    | complete w =>
        let t := canonicalTuning η B
        let returned := returnCode (w.val + 1) (state.2.launchPoint w) (state.2.launchMomentum w)
          (state.2.point w) (state.2.momentum w) s
        have hret := returnCode_valid (m + 1) (w.val + 1) _ _ _ _ t s hs (by omega) (by omega)
          (ho.launchPoint w) (ho.launchMomentum w) (ho.point w) (ho.momentum w)
        change CodeValid (m + 1) t returned.2 ∧ Retains t s returned.2 ∧
          returned.1.1 ∈ (codeLayout t returned.2).vectors 0 ∧
          returned.1.2 ∈ (codeLayout t returned.2).vectors 0 at hret
        have hor := ho.mono hret.2.1
        have hread := readValues_old p lmo response t s returned.2 state.2 hs ho
          (returnCode_extends _ _ _ _ _ s)
        have hb := codeValid_register_bound (m + 1) t s hs
        have hv := returnCode_memory p lmo response t (w.val + 1) (state.2.launchPoint w)
          (state.2.launchMomentum w) (state.2.point w) (state.2.momentum w) s
          (hs.1.trans (codeLayout_next _ _))
          (hb.2 _ _ (ho.launchMomentum w)) (hb.2 _ _ (ho.momentum w))
        change (codeMemory p lmo response t returned.2).vectors returned.1.1 = _ ∧
          (codeMemory p lmo response t returned.2).vectors returned.1.2 = _ at hv
        let next := eventStep K R state.1 (.complete w)
        by_cases ha : state.1.schedule.accepted.length < K
        · by_cases hg : state.1.schedule.accepted.length - state.1.schedule.source w ≤ R
          · let committed := commitCode state.1.schedule.accepted.length returned.1.1 returned.1.2 state.2 returned.2
            have hcv := commitCode_values p lmo response t state.1.schedule.accepted.length returned.1.1 returned.1.2
              state.2 returned.2 hret.1 hor
            dsimp only at hcv
            rw [hread, hv.1, hv.2] at hcv
            by_cases hn : next.schedule.accepted.length < K
            · have hlv := relaunchCode_values p lmo response t w next.schedule.accepted.length committed.1 committed.2
              dsimp only at hlv
              change readValues (codeMemory p lmo response t committed.2) committed.1 = _ at hcv
              rw [hcv] at hlv
              simpa only [eventCode, eventValues, state_bind_apply, state_pure_apply, state_map_apply,
                ha, hg, hn, and_self, true_and, ite_true, next, committed, returned, readValues, t] using hlv
            · simpa only [eventCode, eventValues, state_bind_apply, state_pure_apply, state_map_apply,
                ha, hg, hn, and_self, true_and, ite_true, ite_false, next, committed, returned, readValues, t] using hcv
          · by_cases hn : next.schedule.accepted.length < K
            · have hlv := relaunchCode_values p lmo response t w next.schedule.accepted.length state.2 returned.2
              dsimp only at hlv
              rw [hread] at hlv
              simpa only [eventCode, eventValues, state_bind_apply, state_pure_apply, state_map_apply,
                ha, hg, hn, and_self, true_and, ite_true, ite_false, next, returned, readValues, t] using hlv
            · simpa only [eventCode, eventValues, state_bind_apply, state_pure_apply, state_map_apply,
                ha, hg, hn, and_self, true_and, ite_true, ite_false, next, returned, readValues, t] using hread
        · simpa only [eventCode, eventValues, state_bind_apply, state_pure_apply, state_map_apply,
            ha, false_and, ite_false, returned, readValues, t] using hread

lemma eventsStateCode_values_step {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (pre : List (Event m)) (e : Event m)
    (ht : (canonicalTuning η B).Valid)
    (hr : Labelled (queryLabels H K B (pre ++ [e])) response labelled) :
    let t := canonicalTuning η B
    let old := eventsStateCode H K B pre {}
    let z := eventsStateCode H K B (pre ++ [e]) {}
    (z.1.1, readValues (codeMemory p lmo response t z.2) z.1.2) =
      eventValues p lmo labelled η B H K (LongTails.Algorithms.BirchNonEuclideanPhysical.packetCutoff H B) e
        (old.1.1, readValues (codeMemory p lmo response t old.2) old.1.2) := by
  let old := eventsStateCode H K B pre {}
  have hv := eventsStateCode_valid H K B pre (canonicalTuning η B) ht
  have hh := eventCode_values p lmo response labelled η B H K
    (LongTails.Algorithms.BirchNonEuclideanPhysical.packetCutoff H B) e old.1 old.2 hv.1 hv.2 (by
      intro w he x
      subst e
      exact next_reply p response labelled H K B pre [] w hr x)
  dsimp only
  rw [eventsStateCode_append]
  exact hh

lemma eventsStateCode_values {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (labelled : QueryLabel m → Point p.d → Point p.d)
    (η : ℝ) (B H K : ℕ) (events : List (Event m))
    (ht : (canonicalTuning η B).Valid)
    (hr : Labelled (queryLabels H K B events) response labelled) :
    let t := canonicalTuning η B
    let start := initialCode m B {}
    let z := eventsStateCode H K B events {}
    (z.1.1, readValues (codeMemory p lmo response t z.2) z.1.2) =
      events.foldl (fun s e => eventValues p lmo labelled η B H K
        (LongTails.Algorithms.BirchNonEuclideanPhysical.packetCutoff H B) e s)
        ({}, readValues (codeMemory p lmo response t start.2) start.1) := by
  induction events using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre e ih =>
      have hp := hr.prefix (queryLabels_prefix H K B pre [e])
      have hh := eventsStateCode_values_step p lmo response labelled η B H K pre e ht hr
      dsimp only at ih hh ⊢
      rw [hh, ih hp, List.foldl_append]
      rfl

end LongTails.Proofs.BirchNonEuclideanEventMeaning
