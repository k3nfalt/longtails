import LongTails.Proofs.BirchNonEuclideanEventHistory
import LongTails.Proofs.BirchNonEuclideanPhysicalCertificate

namespace LongTails.Proofs.BirchNonEuclideanPairedReplay

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Algorithms.BirchNonEuclideanTrajectories
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanExecution
open LongTails.Proofs.BirchNonEuclideanCausality
open LongTails.Proofs.BirchNonEuclideanSymbolic
open LongTails.Proofs.BirchNonEuclideanDelta
open LongTails.Proofs.BirchNonEuclideanUnused
open LongTails.Proofs.BirchNonEuclideanReplay
open LongTails.Proofs.BirchNonEuclideanEventMeaning
open LongTails.Proofs.BirchNonEuclideanEventHistory

lemma batchPrefix_memory_points (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (w x B n : ℕ) (s : CodeState) :
    (codeMemory p lmo response t (batchPrefix w x B n s).2).points =
      (codeMemory p lmo response t s).points := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [batchPrefix_succ]
      change (codeMemory p lmo response t (emit (.query w x) (batchPrefix w x B n s).2).2).points = _
      rw [codeMemory_emit_query]
      exact ih

lemma localBatch_memory_points (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (w x B : ℕ) (s : CodeState) :
    (codeMemory p lmo response t (localBatch w x B s).2).points =
      (codeMemory p lmo response t s).points := by
  change (codeMemory p lmo response t ((localBatch w x B).run s).2).points = _
  rw [localBatch_prefix]
  dsimp only
  rw [codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl]
  exact batchPrefix_memory_points p lmo response t w x B B s

lemma launchCode_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (w x v : ℕ) (s : CodeState) :
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t (launchCode w x v s).2
    new.points = old.points ∧ new.vectors = old.vectors ∧ new.replies = old.replies := by
  dsimp only [launchCode, state_bind_apply, state_pure_apply]
  rw [codeMemory_emit_quiet p lmo response t _ (.sendVector _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.sendPoint _ _ _) rfl]
  exact ⟨rfl, rfl, rfl⟩

lemma launches_memory {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (ws : List (Fin m))
    (x v : ℕ) (s : CodeState) :
    let z := (forIn ws () (fun w _ => ForInStep.yield <$> launchCode (w.val + 1) x v) :
      StateM CodeState Unit) s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    new.points = old.points ∧ new.vectors = old.vectors ∧ new.replies = old.replies := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons w ws ih =>
      rw [state_forIn_cons]
      have hs := launchCode_memory p lmo response t (w.val + 1) x v s
      have hr := ih (launchCode (w.val + 1) x v s).2
      exact ⟨hr.1.trans hs.1, hr.2.1.trans hs.2.1, hr.2.2.trans hs.2.2⟩

lemma initialCode_values (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (m B : ℕ) :
    let init := localBatch 0 0 B {}
    let z := initialCode m B {}
    readValues (codeMemory p lmo response t z.2) z.1 =
      initialValues p ((codeMemory p lmo response t init.2).vectors init.1) := by
  let init := localBatch 0 0 B {}
  let tail := (forIn (List.finRange m) ()
    (fun w _ => ForInStep.yield <$> launchCode (w.val + 1) 0 init.1) : StateM CodeState Unit) init.2
  have hm := launches_memory p lmo response t (List.finRange m) 0 init.1 init.2
  change (codeMemory p lmo response t tail.2).points = (codeMemory p lmo response t init.2).points ∧
    (codeMemory p lmo response t tail.2).vectors = (codeMemory p lmo response t init.2).vectors ∧
    (codeMemory p lmo response t tail.2).replies = (codeMemory p lmo response t init.2).replies at hm
  have hr : (initialCode m B {}).1 =
      { points := fun _ => 0, momenta := fun _ => init.1,
        launchPoint := fun _ => 0, launchMomentum := fun _ => init.1,
        point := fun _ => 0, momentum := fun _ => init.1 } := rfl
  have hs : (initialCode m B {}).2 = tail.2 := rfl
  have hp : (codeMemory p lmo response t init.2).points = fun _ => p.x0 := by
    exact localBatch_memory_points p lmo response t 0 0 B {}
  dsimp only
  rw [hr, hs]
  ext i <;> simp only [readValues, initialValues, hm.1, hm.2.1, hp, init]

lemma codeMemory_response_congr (p : Params) (lmo : Point p.d → Point p.d)
    (response response' : ℕ → Point p.d → Point p.d) (t : Tuning) (s : CodeState)
    (hr : ∀ j < codeCalls s, response j = response' j) :
    codeMemory p lmo response t s = codeMemory p lmo response' t s := by
  apply interpret_sample_congr p lmo (fun x f => f x) (codeInstructions t s) (initialMemory p) response response'
  intro j hj
  apply hr j
  have hh := codeMemory_replies p lmo response t s
  simp only [codeMemory, interpret_replies] at hh
  omega

lemma batchPrefix_calls (w x B n : ℕ) (s : CodeState) :
    codeCalls (batchPrefix w x B n s).2 = codeCalls s + n := by
  induction n with
  | zero => simp [batchPrefix_zero]
  | succ n ih =>
      rw [batchPrefix_succ]
      change codeCalls ((emit (.query w x)).run (batchPrefix w x B n s).2).2 = _
      rw [emit_calls, ih]
      rfl

lemma batchPrefix_memory_records (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (w x B n : ℕ) (s : CodeState)
    (hn : s.next = 1 + s.instructions.length) :
    ∀ j < n, (codeMemory p lmo response t (batchPrefix w x B n s).2).vectors (s.next + j) =
      response (codeCalls s + j) ((codeMemory p lmo response t s).points x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ha := batchPrefix_aligned w x B n s t (by rw [codeSymbolic_next]; exact hn)
      have he : (codeMemory p lmo response t (batchPrefix w x B n s).2).next = s.next + n := by
        rw [codeMemory_next, ← codeSymbolic_next t, ← ha, batchPrefix_next]
      intro j hj
      rw [batchPrefix_succ]
      change (codeMemory p lmo response t (emit (.query w x) (batchPrefix w x B n s).2).2).vectors _ = _
      rw [codeMemory_emit_query]
      by_cases hjn : j = n
      · subst j
        simp [perform, storeVector, he, batchPrefix_calls, batchPrefix_memory_points]
      · have hne : s.next + j ≠ s.next + n := by omega
        simpa only [perform, storeVector, he, Function.update_of_ne hne] using ih j (by omega)

lemma localBatch_memory_mean (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (w x B : ℕ) (s : CodeState)
    (hn : s.next = 1 + s.instructions.length) :
    let z := localBatch w x B s
    (codeMemory p lmo response t z.2).vectors z.1 =
      (1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
        response (codeCalls s + j) ((codeMemory p lmo response t s).points x) := by
  change (codeMemory p lmo response t ((localBatch w x B).run s).2).vectors
    ((localBatch w x B).run s).1 = _
  rw [localBatch_prefix]
  dsimp only
  rw [codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl]
  have ha := batchPrefix_aligned w x B B s t (by rw [codeSymbolic_next]; exact hn)
  have he : (codeMemory p lmo response t (batchPrefix w x B B s).2).next =
      (batchPrefix w x B B s).2.next := by rw [ha, codeSymbolic_next, codeMemory_next]
  simp only [InstructionTemplate.instantiate, perform, storeVector, emit_apply, he, Function.update_self]
  rw [batchPrefix_terms]
  simp only [List.map_map, Function.comp_def, Coefficient.eval]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [batchPrefix_memory_records p lmo response t w x B B s hn j (Finset.mem_range.mp hj)]

lemma commitDifference_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (w x0 m0 xcur mcur xlocal mlocal : ℕ) (s : CodeState)
    (hn : s.next = 1 + s.instructions.length)
    (hm0 : m0 < s.next) (hmc : mcur < s.next) (hml : mlocal < s.next) :
    let z := ((do
      let dx ← emit (.difference w xlocal x0)
      let dm ← emit (.mix w [(.constant 1, mlocal), (.constant (-1), m0)])
      let _ ← emit (.sendVector w 0 dx)
      let _ ← emit (.sendVector w 0 dm)
      let x ← emit (.move 0 xcur dx (.constant 1))
      let v ← emit (.mix 0 [(.constant 1, mcur), (.constant 1, dm)])
      return (x, v)) : StateM CodeState (ℕ × ℕ)) s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    new.points z.1.1 = old.points xcur + (old.points xlocal - old.points x0) ∧
      new.vectors z.1.2 = old.vectors mcur + (old.vectors mlocal - old.vectors m0) := by
  have hn' : s.next = (codeMemory p lmo response t s).next := by rw [codeMemory_next, hn]
  have h0 : m0 ≠ (codeMemory p lmo response t s).next := by omega
  have hc : mcur ≠ (codeMemory p lmo response t s).next := by omega
  have hc1 : mcur ≠ (codeMemory p lmo response t s).next + 1 := by omega
  have hl : mlocal ≠ (codeMemory p lmo response t s).next := by omega
  dsimp only
  simp only [state_bind_apply, state_pure_apply]
  rw [codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.move _ _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.sendVector _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.sendVector _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.difference _ _ _) rfl]
  simp [InstructionTemplate.instantiate, Coefficient.eval, perform, storeVector,
    emit_apply, hn', h0, hc, hc1, hl, Nat.add_assoc, sub_eq_add_neg]

lemma deltaStep_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (H k : ℕ) (dispatch worker : ℕ → ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) (η : ℝ) (B : ℕ)
    (hn : s.next = 1 + s.instructions.length)
    (hm : ∀ j, state.2 j < s.next) (hx : ∀ j, state.1 j < s.next) :
    let t := canonicalTuning η B
    let z := deltaStep H dispatch worker k state s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    let packet := localValues p lmo (fun h => response (codeCalls s + h)) η B H
      (old.points (state.1 (dispatch k)), old.vectors (state.2 (dispatch k))) H
    new.points (z.1.1 (k + 1)) = old.points (state.1 k) +
      (packet.1 - old.points (state.1 (dispatch k))) ∧
      new.vectors (z.1.2 (k + 1)) = old.vectors (state.2 k) +
        (packet.2 - old.vectors (state.2 (dispatch k))) := by
  let t := canonicalTuning η B
  let w := worker k
  let src := dispatch k
  let s1 := (emit (.sendPoint 0 w (state.1 src)) s).2
  let s2 := (emit (.sendVector 0 w (state.2 src)) s1).2
  let packet := (localMomentum w (state.1 src) (state.2 src) H k).run s2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : (codeMemory p lmo response t s2).points = (codeMemory p lmo response t s).points ∧
      (codeMemory p lmo response t s2).vectors = (codeMemory p lmo response t s).vectors ∧
      (codeMemory p lmo response t s2).replies = (codeMemory p lmo response t s).replies :=
    launchCode_memory p lmo response t w (state.1 src) (state.2 src) s
  have hs2c : codeCalls s2 = codeCalls s := by
    simpa only [codeMemory_replies] using hs2.2.2
  have ha2 : s2.next = 1 + s2.instructions.length := by
    simp [s2, s1, emit_apply, hn, Nat.add_assoc]
  have hm2 : state.2 src < s2.next := by rw [hs2n]; have := hm src; omega
  have hp := localPrefix_memory p lmo response η B w H k H (state.1 src, state.2 src) s2 ha2 hm2
  have hp' : ((codeMemory p lmo response t packet.2).points packet.1.1,
      (codeMemory p lmo response t packet.2).vectors packet.1.2) =
      localValues p lmo (fun h => response (codeCalls s + h)) η B H
        ((codeMemory p lmo response t s).points (state.1 src),
          (codeMemory p lmo response t s).vectors (state.2 src)) H := by
    simpa only [packet, localMomentum_prefix, t, hs2c, hs2.1, hs2.2.1] using hp
  have hpn := localPrefix_next w H k H (state.1 src, state.2 src) s2
  have hpa := localPrefix_aligned w H k H (state.1 src, state.2 src) s2 t
    (by rw [codeSymbolic_next]; exact ha2)
  rw [codeSymbolic_next] at hpa
  have hpm := localPrefix_momentum_lt w H k H (state.1 src, state.2 src) s2 hm2
  have hglobal (j : ℕ) (hj : j < s.next) :
      (codeMemory p lmo response t packet.2).points j = (codeMemory p lmo response t s).points j ∧
        (codeMemory p lmo response t packet.2).vectors j = (codeMemory p lmo response t s).vectors j := by
    have hj2 : j < (codeMemory p lmo response t s2).next := by rw [codeMemory_next, ← ha2, hs2n]; omega
    have hh := codeMemory_old p lmo response t s2 packet.2
      (localPrefix_extends w H k H (state.1 src, state.2 src) s2) j hj2
    exact ⟨hh.1.trans (by rw [hs2.1]), hh.2.trans (by rw [hs2.2.1])⟩
  have hm0 : state.2 src < packet.2.next := by
    change state.2 src < (localPrefix w H k H (state.1 src, state.2 src) s2).2.next
    rw [hpn, hs2n]
    have := hm src
    omega
  have hmc : state.2 k < packet.2.next := by
    change state.2 k < (localPrefix w H k H (state.1 src, state.2 src) s2).2.next
    rw [hpn, hs2n]
    have := hm k
    omega
  have hc := commitDifference_memory p lmo response t w (state.1 src) (state.2 src)
    (state.1 k) (state.2 k) packet.1.1 packet.1.2 packet.2 hpa hm0 hmc hpm
  have hpx := congrArg Prod.fst hp'
  have hpv := congrArg Prod.snd hp'
  dsimp only at hpx hpv
  constructor
  · calc
      _ = (codeMemory p lmo response t packet.2).points (state.1 k) +
          ((codeMemory p lmo response t packet.2).points packet.1.1 -
            (codeMemory p lmo response t packet.2).points (state.1 src)) := by
        simpa only [deltaStep, state_bind_apply, state_pure_apply, Function.update_self,
          packet, s2, s1, w, src, t, StateT.run] using hc.1
      _ = _ := by rw [(hglobal (state.1 k) (hx k)).1, (hglobal (state.1 src) (hx src)).1, hpx]
  · calc
      _ = (codeMemory p lmo response t packet.2).vectors (state.2 k) +
          ((codeMemory p lmo response t packet.2).vectors packet.1.2 -
            (codeMemory p lmo response t packet.2).vectors (state.2 src)) := by
        simpa only [deltaStep, state_bind_apply, state_pure_apply, Function.update_self,
          packet, s2, s1, w, src, t, StateT.run] using hc.2
      _ = _ := by rw [(hglobal (state.2 k) (hm k)).2, (hglobal (state.2 src) (hm src)).2, hpv]

lemma deltaPrefix_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (workers H K B : ℕ)
    (dispatch worker : ℕ → ℕ) (η : ℝ) (ht : (canonicalTuning η B).Valid)
    (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) :
    let t := canonicalTuning η B
    let init := localBatch 0 0 B {}
    let z := deltaPrefix H dispatch worker K B
    let mem := codeMemory p lmo response t z.2
    (fun j => mem.points (z.1.1 j), fun j => mem.vectors (z.1.2 j)) =
      pairedValues p lmo (fun k h => response (B + k * H + h)) η B H dispatch
        ((codeMemory p lmo response t init.2).vectors init.1) K := by
  dsimp only
  induction K with
  | zero =>
      rw [deltaPrefix_zero, pairedValues]
      apply Prod.ext
      · funext j
        exact congrFun (localBatch_memory_points p lmo response (canonicalTuning η B) 0 0 B {}) 0
      · rfl
  | succ K ih =>
      let t := canonicalTuning η B
      let old := deltaPrefix H dispatch worker K B
      have hv := deltaPrefix_valid workers H K B dispatch worker t ht hw0 hw
      have hn : old.2.next = 1 + old.2.instructions.length := by
        rw [← codeLayout_next t old.2]
        exact hv.1.1
      have hb := codeValid_register_bound workers t old.2 hv.1
      have hx : ∀ j, old.1.1 j < old.2.next := fun j => hb.1 0 _ (hv.2.1 j)
      have hm : ∀ j, old.1.2 j < old.2.next := fun j => hb.2 0 _ (hv.2.2 j)
      have hc : codeCalls old.2 = B + K * H := by
        have hh := deltaCode_calls H dispatch worker K B {}
        change codeCalls old.2 = codeCalls {} + B + K * H at hh
        simpa [codeCalls] using hh
      have hs := deltaStep_memory p lmo response H K dispatch worker old.1 old.2 η B hn hm hx
      have he := buildExtends_deltaStep H K dispatch worker old.1 old.2
      have hmem (j : ℕ) (hj : j < old.2.next) :=
        codeMemory_old p lmo response t old.2 (deltaStep H dispatch worker K old.1 old.2).2
          he j (by rw [codeMemory_next, ← hn]; exact hj)
      rw [deltaPrefix_succ, pairedValues, ← ih]
      apply Prod.ext
      · funext j
        by_cases hj : j = K + 1
        · subst j
          simpa only [Function.update_self, hc, old, t] using hs.1
        · simp only [(deltaStep_registers H K dispatch worker (deltaPrefix H dispatch worker K B).1
            (deltaPrefix H dispatch worker K B).2).1, Function.update_of_ne hj]
          exact (hmem (old.1.1 j) (hx j)).1
      · funext j
        by_cases hj : j = K + 1
        · subst j
          simpa only [Function.update_self, hc, old, t] using hs.2
        · simp only [(deltaStep_registers H K dispatch worker (deltaPrefix H dispatch worker K B).1
            (deltaPrefix H dispatch worker K B).2).1, Function.update_of_ne hj]
          exact (hmem (old.1.2 j) (hm j)).2

end LongTails.Proofs.BirchNonEuclideanPairedReplay
