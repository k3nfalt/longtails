import LongTails.Algorithms.BirchNonEuclideanPhysical
import LongTails.Proofs.BirchNonEuclideanDeltaCertificate
import LongTails.Proofs.BirchNonEuclideanExtensions

namespace LongTails.Proofs.BirchNonEuclideanUnused

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta

structure Clean (s : SymbolicMemory) : Prop where
  units : s.units = ∅
  queries : ∀ q ∈ s.queries, (s.queryPoints q).1 = 0
  sharps : ∀ e ∈ s.sharps, (s.sharpInputs e).2 = 0 ∧ coefficientMass (s.sharpInputs e).1 = 1

lemma code_beforeNext (t : Tuning) (s : CodeState) :
    (∀ q ∈ (codeSymbolic t s).queries, q < (codeSymbolic t s).next) ∧
      (∀ e ∈ (codeSymbolic t s).sharps, e < (codeSymbolic t s).next) := by
  let a : Program := ⟨codeInstructions t s, 0, 0, fun _ => 0⟩
  have h := LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_beforeNext a
  exact ⟨h.1, fun e he => h.2 e (Finset.mem_union_left _ he)⟩

lemma localPrefix_clean (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hm : state.2 < s.next) (hc : Clean (codeSymbolic (canonicalTuning η B) s))
    (hx : ((codeSymbolic (canonicalTuning η B) s).points state.1).1 = 0)
    (hv : ((codeSymbolic (canonicalTuning η B) s).vectors state.2).2 = 0)
    (hmass : coefficientMass ((codeSymbolic (canonicalTuning η B) s).vectors state.2).1 = 1) :
    Clean (codeSymbolic (canonicalTuning η B) (localPrefix w H round n state s).2) := by
  let t := canonicalTuning η B
  have hs := localPrefix_sets w H round n state s t hn hm
  have hr := localPrefix_records w H round n state s η B hn hm
  have he := localPrefix_extends w H round n state s
  refine ⟨hs.2.2.trans hc.units, ?_, ?_⟩
  · intro q hq
    rw [hs.1] at hq
    rcases Finset.mem_union.mp hq with hq | hq
    · rw [(codeExtends_symbolic t s _ he q ((code_beforeNext t s).1 q hq)).2.2.1]
      exact hc.queries q hq
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      rw [(hr j (Finset.mem_range.mp hj)).1, localPath_raw]
      exact hx
  · intro e he'
    rw [hs.2.1] at he'
    rcases Finset.mem_union.mp he' with he' | he'
    · rw [(codeExtends_symbolic t s _ he e ((code_beforeNext t s).2 e he')).2.2.2]
      exact hc.sharps e he'
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he'
      rw [(hr j (Finset.mem_range.mp hj)).2]
      exact ⟨by rw [localRaw_direction, hv, smul_zero], localRaw_mass _ _ _ _ hmass⟩

def Quiet : InstructionTemplate → Prop
  | .query .. | .sharp .. | .lmo .. => False
  | _ => True

lemma quiet_clean (t : Tuning) (i : InstructionTemplate) (s : CodeState)
    (hi : Quiet i) (hc : Clean (codeSymbolic t s)) :
    Clean (codeSymbolic t (emit i s).2) := by
  rw [codeSymbolic_emit]
  cases i <;> simp only [Quiet] at hi
  all_goals exact ⟨hc.units, hc.queries, hc.sharps⟩

lemma unusedPacket_extends (w x v H round : ℕ) : BuildExtends (unusedPacket w x v H round) := by
  unfold unusedPacket
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_localMomentum _ _ _ _ _)
  intro packet
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dx
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dm
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

lemma unusedPacket_clean (w x v H round : ℕ) (s : CodeState) (η : ℝ) (B : ℕ)
    (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next) (hvlt : v < s.next)
    (hc : Clean (codeSymbolic (canonicalTuning η B) s))
    (hx : ((codeSymbolic (canonicalTuning η B) s).points x).1 = 0)
    (hv : ((codeSymbolic (canonicalTuning η B) s).vectors v).2 = 0)
    (hmass : coefficientMass ((codeSymbolic (canonicalTuning η B) s).vectors v).1 = 1) :
    Clean (codeSymbolic (canonicalTuning η B) (unusedPacket w x v H round s).2) := by
  let t := canonicalTuning η B
  let s1 := (emit (.sendPoint 0 w x) s).2
  let s2 := (emit (.sendVector 0 w v) s1).2
  have hc1 := quiet_clean t (.sendPoint 0 w x) s trivial hc
  have hc2 := quiet_clean t (.sendVector 0 w v) s1 trivial hc1
  have hn2 : s2.next = (codeSymbolic t s2).next := by
    dsimp only [s2, s1]
    rw [codeSymbolic_emit, codeSymbolic_emit]
    simp only [InstructionTemplate.instantiate, symbolicPerform, emit_apply]
    change s.next = (codeSymbolic t s).next at hn
    omega
  have hv2 : v < s2.next := by simp only [s2, s1, emit_apply]; omega
  have hpoints : (codeSymbolic t s2).points = (codeSymbolic t s).points := by
    simp only [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform]
  have hvectors : (codeSymbolic t s2).vectors = (codeSymbolic t s).vectors := by
    simp only [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform]
  dsimp only [t] at hpoints hvectors
  have hz := localPrefix_clean w H round H (x, v) s2 η B hn2 hv2 hc2
    (by simpa only [hpoints] using hx) (by simpa only [hvectors] using hv)
    (by simpa only [hvectors] using hmass)
  change Clean (codeSymbolic t ((localMomentum w x v H round).run s2).2) at hz
  simp only [unusedPacket, state_bind_apply, state_pure_apply]
  apply quiet_clean t (.sendVector _ _ _) _ trivial
  apply quiet_clean t (.sendVector _ _ _) _ trivial
  apply quiet_clean t (.mix _ _) _ trivial
  exact quiet_clean t (.difference _ _ _) _ trivial hz

lemma unusedPacket_valid (workers w x v H round : ℕ) (t : Tuning) (ht : t.Valid)
    (s : CodeState) (hs : CodeValid workers t s) (hw : w < workers)
    (hw0 : 0 < workers) (hx : x ∈ (codeLayout t s).points 0)
    (hv : v ∈ (codeLayout t s).vectors 0) :
    CodeValid workers t (unusedPacket w x v H round s).2 ∧
      Retains t s (unusedPacket w x v H round s).2 := by
  let s1 := (emit (.sendPoint 0 w x) s).2
  let s2 := (emit (.sendVector 0 w v) s1).2
  let z := (localMomentum w x v H round).run s2
  let dx := (emit (.difference w z.1.1 x) z.2).1
  let s3 := (emit (.difference w z.1.1 x) z.2).2
  let terms : List (Coefficient × ℕ) := [(.constant 1, z.1.2), (.constant (-1), v)]
  let dm := (emit (.mix w terms) s3).1
  let s4 := (emit (.mix w terms) s3).2
  let s5 := (emit (.sendVector w 0 dx) s4).2
  let s6 := (emit (.sendVector w 0 dm) s5).2
  have h1 := sendPoint_valid workers t s hs 0 w x hw0 hw hx
  have h2 := sendVector_valid workers t s1 h1.1 0 w v hw0 hw
    (((retains_emit t (.sendPoint 0 w x) s) 0).2 hv)
  have hx2 := ((retains_emit t (.sendVector 0 w v) s1) w).1 h1.2
  have hz := localMomentum_valid workers t ht w x v H round s2 h2.1 hw hx2 h2.2
  have h3 := difference_valid workers t z.2 hz.1 w z.1.1 x hw hz.2.2.1
    ((hz.2.1 w).1 hx2)
  have hr23 : Retains t s2 s3 := retains_trans t s2 z.2 s3 hz.2.1 (retains_emit t _ z.2)
  have hm3 : ∀ a ∈ terms, a.2 ∈ (codeLayout t s3).vectors w := by
    intro a ha
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ((retains_emit t (.difference w z.1.1 x) z.2) w).2 hz.2.2.2
    · exact (hr23 w).2 h2.2
  have h4 : CodeValid workers t s4 := codeValid_emit workers t _ s3 h3.1
    (mix_legal workers t s3 w terms hw hm3)
  have hdm : dm ∈ (codeLayout t s4).vectors w := mix_member workers t s3 h3.1 w terms
  have h5 := sendVector_valid workers t s4 h4 w 0 dx hw hw0
    (((retains_emit t (.mix w terms) s3) w).2 h3.2)
  have h6 := sendVector_valid workers t s5 h5.1 w 0 dm hw hw0
    (((retains_emit t (.sendVector w 0 dx) s4) w).2 hdm)
  have hr02 : Retains t s s2 := retains_trans t s s1 s2 (retains_emit t _ s) (retains_emit t _ s1)
  have hr04 : Retains t s s4 := retains_trans t s s3 s4
    (retains_trans t s s2 s3 hr02 hr23) (retains_emit t _ s3)
  have hr06 : Retains t s s6 := retains_trans t s s5 s6
    (retains_trans t s s4 s5 hr04 (retains_emit t _ s4)) (retains_emit t _ s5)
  exact ⟨h6.1, hr06⟩

lemma unusedPacket_calls (w x v H round : ℕ) (s : CodeState) :
    codeCalls (unusedPacket w x v H round s).2 = codeCalls s + H := by
  have h := localMomentum_calls w x v H round
    { instructions := s.instructions ++ [.sendPoint 0 w x, .sendVector 0 w v],
      next := s.next + 1 + 1 }
  simp only [unusedPacket, state_bind_apply, emit_apply, state_pure_apply]
  simpa [codeCalls, StateT.run, InstructionTemplate.instantiate, Instruction.oracleCost] using h

lemma pairedCode_prefix (H K B : ℕ) (dispatch worker : ℕ → ℕ) :
    (pairedCode H dispatch worker K B).run {} = deltaPrefix H dispatch worker K B := rfl

lemma pairedCode_state (H K B : ℕ) (dispatch worker : ℕ → ℕ) (s : CodeState) :
    ((pairedCode H dispatch worker K B).run s).2 =
      ((deltaCode H dispatch worker K B).run s).2 := rfl

lemma state_forIn_extends {α β : Type} (step : α → β → StateM CodeState β)
    (xs : List α) (b : β) (s : CodeState)
    (he : ∀ i ∈ xs, ∀ b, BuildExtends (step i b)) :
    CodeExtends s ((forIn xs b (fun i b => ForInStep.yield <$> step i b) :
      StateM CodeState β) s).2 := by
  induction xs generalizing b s with
  | nil => exact codeExtends_refl s
  | cons i xs ih =>
      rw [state_forIn_cons]
      exact codeExtends_trans s _ _ (he i (by simp) b s)
        (ih _ _ (fun j hj => he j (List.mem_cons_of_mem i hj)))

lemma physicalLocalCode_run {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) :
    (physicalLocalCode H K B word).run {} =
      let schedule := finalSchedule H K B word
      let z := deltaPrefix H (packetSource schedule.accepted) (packetWorker schedule.accepted) K B
      let tail := (forIn (ignored schedule) () (fun job _ => ForInStep.yield <$>
        unusedPacket (job.worker.val + 1) (z.1.1 job.source) (z.1.2 job.source) H 0) :
          StateM CodeState Unit) z.2
      (z.1.1, tail.2) := rfl

lemma physicalLocalCode_calls {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) :
    codeCalls ((physicalLocalCode H K B word).run {}).2 =
      B + H * (K + (ignored (finalSchedule H K B word)).length) := by
  rw [physicalLocalCode_run]
  dsimp only
  rw [state_forIn_cost codeCalls _ H (fun job _ s => unusedPacket_calls _ _ _ _ _ s)]
  have h := deltaCode_calls H (packetSource (finalSchedule H K B word).accepted)
    (packetWorker (finalSchedule H K B word).accepted) K B {}
  change codeCalls (deltaPrefix H _ _ K B).2 = codeCalls {} + B + K * H at h
  rw [h]
  have hz : codeCalls {} = 0 := rfl
  rw [hz]
  ring

lemma physicalLocalCode_points {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) :
    ((physicalLocalCode H K B word).run {}).1 =
      (deltaPrefix H (packetSource (finalSchedule H K B word).accepted)
        (packetWorker (finalSchedule H K B word).accepted) K B).1.1 := by
  rw [physicalLocalCode_run]

lemma physicalLocalFamily_calls {m : ℕ} (H K B : ℕ) (word : ℕ → ℕ → ℕ → Fin m) (t : Tuning) :
    ((physicalLocalFamily H word).instantiate K B t).oracleCalls = physicalLocalCalls H word K B := by
  rw [(family_tuning_cost (physicalLocalFamily H word) K B t (canonicalTuning 0 1)).1]
  exact physicalLocalCode_calls H K B (word K B)

lemma unusedPackets_properties {α : Type} (jobs : List α) (w x v : α → ℕ)
    (workers H : ℕ) (η : ℝ) (B : ℕ) (s : CodeState)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers)
    (hs : CodeValid workers (canonicalTuning η B) s)
    (hc : Clean (codeSymbolic (canonicalTuning η B) s))
    (hw : ∀ a ∈ jobs, w a < workers)
    (hx : ∀ a ∈ jobs, x a ∈ (codeLayout (canonicalTuning η B) s).points 0)
    (hv : ∀ a ∈ jobs, v a ∈ (codeLayout (canonicalTuning η B) s).vectors 0)
    (hxl : ∀ a ∈ jobs, ((codeSymbolic (canonicalTuning η B) s).points (x a)).1 = 0)
    (hvl : ∀ a ∈ jobs, ((codeSymbolic (canonicalTuning η B) s).vectors (v a)).2 = 0)
    (hvm : ∀ a ∈ jobs,
      coefficientMass ((codeSymbolic (canonicalTuning η B) s).vectors (v a)).1 = 1) :
    let r := (forIn jobs () (fun a _ => ForInStep.yield <$> unusedPacket (w a) (x a) (v a) H 0) :
      StateM CodeState Unit) s
    CodeValid workers (canonicalTuning η B) r.2 ∧ Retains (canonicalTuning η B) s r.2 ∧
      CodeExtends s r.2 ∧ Clean (codeSymbolic (canonicalTuning η B) r.2) := by
  let t := canonicalTuning η B
  let Inv := fun (_ : Unit) (r : CodeState) => CodeValid workers t r ∧ Retains t s r ∧
    CodeExtends s r ∧ Clean (codeSymbolic t r)
  apply state_forIn_invariant (fun a _ => unusedPacket (w a) (x a) (v a) H 0) jobs Inv
  · intro a ha _ r hr
    have hx' := (hr.2.1 0).1 (hx a ha)
    have hv' := (hr.2.1 0).2 (hv a ha)
    have hp := unusedPacket_valid workers (w a) (x a) (v a) H 0 t ht r hr.1 (hw a ha) hw0 hx' hv'
    have hb := codeValid_register_bound workers t s hs
    have hxs : x a < (codeSymbolic t s).next := by
      rw [← codeValid_symbolic_next workers t s hs]
      exact hb.1 0 _ (hx a ha)
    have hvs : v a < (codeSymbolic t s).next := by
      rw [← codeValid_symbolic_next workers t s hs]
      exact hb.2 0 _ (hv a ha)
    have hxv := (codeExtends_symbolic t s r hr.2.2.1 _ hxs).1
    have hvv := (codeExtends_symbolic t s r hr.2.2.1 _ hvs).2.1
    have hclean := unusedPacket_clean (w a) (x a) (v a) H 0 r η B
      (codeValid_symbolic_next workers t r hr.1)
      ((codeValid_register_bound workers t r hr.1).2 0 _ hv') hr.2.2.2
      (by change ((codeSymbolic t r).points (x a)).1 = 0; rw [hxv]; exact hxl a ha)
      (by change ((codeSymbolic t r).vectors (v a)).2 = 0; rw [hvv]; exact hvl a ha)
      (by change coefficientMass ((codeSymbolic t r).vectors (v a)).1 = 1; rw [hvv]; exact hvm a ha)
    exact ⟨hp.1, retains_trans t s r _ hr.2.1 hp.2,
      codeExtends_trans s r _ hr.2.2.1 (unusedPacket_extends _ _ _ _ _ r), hclean⟩
  · exact ⟨hs, retains_refl t s, codeExtends_refl s, hc⟩

lemma clean_append_extension (s r : CodeState) (t : Tuning) (a b : Program)
    (main : ℕ → ℕ) (K : ℕ) (ha : a.instructions = codeInstructions t s)
    (hb : b.instructions = codeInstructions t r) (he : CodeExtends s r)
    (hm : ∀ k ≤ K, main k < (codeSymbolic t s).next)
    (hc : Clean (codeSymbolic t r)) (hoc : b.outputCount = a.outputCount)
    (hop : ∀ j, b.outputPoint j = a.outputPoint (Fin.cast (congrArg (fun n => n + 1) hoc) j)) :
    LongTails.Proofs.BirchNonEuclideanExtensions.CertificateExtension a b main K := by
  obtain ⟨tail, htail⟩ := he
  have hcode : b.instructions = a.instructions ++ tail.map (InstructionTemplate.instantiate t) := by
    rw [ha, hb]
    simp only [codeInstructions, htail, List.map_append]
  have has : a.symbolic = codeSymbolic t s := by simp only [Program.symbolic, ha, codeSymbolic]
  have hbs : b.symbolic = codeSymbolic t r := by simp only [Program.symbolic, hb, codeSymbolic]
  apply LongTails.Proofs.BirchNonEuclideanExtensions.certificateExtension_of_append _ hcode
  · simpa only [has] using hm
  · simpa only [hbs] using hc.units
  · simpa only [hbs] using hc.queries
  · intro e he _
    rw [hbs] at he ⊢
    exact (hc.sharps e he).1
  · intro e he _
    rw [hbs] at he ⊢
    rw [← codeSymbolic_sharp_mass]
    exact (hc.sharps e he).2
  · exact hop
  · exact hoc

lemma output_agreement (a b : Program) (main : ℕ → ℕ) (K : ℕ)
    (ha : a.outputCount + 1 = K ∧ ∀ j, a.outputPoint j = main j.val)
    (hb : b.outputCount + 1 = K ∧ ∀ j, b.outputPoint j = main j.val) :
    ∃ hoc : b.outputCount = a.outputCount,
      ∀ j, b.outputPoint j = a.outputPoint (Fin.cast (congrArg (fun n => n + 1) hoc) j) := by
  have hoc : b.outputCount = a.outputCount := by have := ha.1; have := hb.1; omega
  refine ⟨hoc, ?_⟩
  intro j
  rw [hb.2, ha.2]
  rfl

end LongTails.Proofs.BirchNonEuclideanUnused
