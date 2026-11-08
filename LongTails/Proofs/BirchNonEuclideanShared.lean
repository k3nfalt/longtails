import LongTails.Proofs.BirchNonEuclideanDelta

namespace LongTails.Proofs.BirchNonEuclideanShared

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanDelta (localMomentum_next)

lemma sharedPacketStep_next (m H k x v i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState) :
    (sharedPacketStep m H k x v i terms s).2.next = s.next + (4 * H + 5) := by
  have hn := localMomentum_next (i + 1) x v H k
    { instructions := s.instructions ++ [.sendPoint 0 (i + 1) x,
        .sendVector 0 (i + 1) v], next := s.next + 1 + 1 }
  simp only [sharedPacketStep, state_bind_apply, emit_apply, state_pure_apply]
  simp only [StateT.run, List.append_assoc, List.singleton_append] at hn ⊢
  rw [hn]
  omega

lemma buildExtends_sharedPacketStep (m H k x v i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) :
    BuildExtends (sharedPacketStep m H k x v i terms) := by
  unfold sharedPacketStep
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_localMomentum _ _ _ _ _)
  intro packet
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro dx
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

noncomputable def packetPrefix (m H k x v n : ℕ) (s : CodeState) :=
  (forIn (List.range n) ([], [])
    (fun i ts => ForInStep.yield <$> sharedPacketStep m H k x v i ts) :
      StateM CodeState (List (Coefficient × ℕ) × List (Coefficient × ℕ))) s

lemma packetPrefix_zero (m H k x v : ℕ) (s : CodeState) :
    packetPrefix m H k x v 0 s = (([], []), s) := rfl

lemma packetPrefix_succ (m H k x v n : ℕ) (s : CodeState) :
    packetPrefix m H k x v (n + 1) s =
      let z := packetPrefix m H k x v n s
      sharedPacketStep m H k x v n z.1 z.2 := state_forIn_range_succ _ n _ _

lemma packetPrefix_next (m H k x v n : ℕ) (s : CodeState) :
    (packetPrefix m H k x v n s).2.next = s.next + n * (4 * H + 5) := by
  induction n with
  | zero => simp [packetPrefix_zero]
  | succ n ih =>
      rw [packetPrefix_succ]
      dsimp only
      rw [sharedPacketStep_next, ih, Nat.add_mul]
      omega

lemma packetPrefix_extends (m H k x v n : ℕ) (s : CodeState) :
    CodeExtends s (packetPrefix m H k x v n s).2 := by
  induction n with
  | zero => exact codeExtends_refl s
  | succ n ih =>
      rw [packetPrefix_succ]
      exact codeExtends_trans _ _ _ ih (buildExtends_sharedPacketStep m H k x v n _ _)

lemma sharedRoundStep_registers (m H k : ℕ) (state : (ℕ → ℕ) × ℕ) (s : CodeState) :
    (sharedRoundStep m H k state s).1 =
      (Function.update state.1 (k + 1) (s.next + m * (4 * H + 5) + 1),
        s.next + m * (4 * H + 5) + 2) ∧
      (sharedRoundStep m H k state s).2.next = s.next + m * (4 * H + 5) + 3 := by
  simp only [sharedRoundStep, state_bind_apply, emit_apply, state_pure_apply]
  change (_, _) = (_, _) ∧ _
  rw [show (forIn (List.range m) ([], [])
    (fun i ts => ForInStep.yield <$> sharedPacketStep m H k (state.1 k) state.2 i ts) :
      StateM CodeState (List (Coefficient × ℕ) × List (Coefficient × ℕ))) s =
        packetPrefix m H k (state.1 k) state.2 m s from rfl]
  rw [packetPrefix_next]
  exact ⟨rfl, rfl⟩

noncomputable def sharedPrefix (m H K B : ℕ) :=
  let init := (localBatch 0 0 (m * B)).run {}
  (forIn (List.range K) ((fun _ => 0), init.1)
    (fun k state => ForInStep.yield <$> sharedRoundStep m H k state) :
      StateM CodeState ((ℕ → ℕ) × ℕ)) init.2

lemma sharedPrefix_zero (m H B : ℕ) :
    sharedPrefix m H 0 B =
      let init := (localBatch 0 0 (m * B)).run {}
      (((fun _ => 0), init.1), init.2) := rfl

lemma sharedPrefix_succ (m H K B : ℕ) :
    sharedPrefix m H (K + 1) B =
      let z := sharedPrefix m H K B
      sharedRoundStep m H K z.1 z.2 := state_forIn_range_succ _ K _ _

lemma sharedCode_prefix (m H K B : ℕ) :
    (sharedCode m H K B).run {} = ((sharedPrefix m H K B).1.1, (sharedPrefix m H K B).2) := rfl

lemma sharedPrefix_next (m H K B : ℕ) :
    (sharedPrefix m H K B).2.next = m * B + 2 + K * (m * (4 * H + 5) + 3) := by
  induction K with
  | zero =>
      rw [sharedPrefix_zero]
      dsimp only
      rw [localBatch_next]
      simp
      omega
  | succ K ih =>
      rw [sharedPrefix_succ]
      dsimp only
      rw [(sharedRoundStep_registers m H K _ _).2, ih, Nat.add_mul]
      omega

noncomputable def termSum (t : Tuning) (s : CodeState) (terms : List (Coefficient × ℕ)) : LinearValue :=
  (terms.map (fun c => c.1.eval t • (codeSymbolic t s).vectors c.2)).sum

def TermsBefore (terms : List (Coefficient × ℕ)) (n : ℕ) : Prop :=
  ∀ c ∈ terms, c.2 < n

lemma termSum_append (t : Tuning) (s : CodeState) (left right : List (Coefficient × ℕ)) :
    termSum t s (left ++ right) = termSum t s left + termSum t s right := by
  simp [termSum]

lemma termSum_extends (t : Tuning) (s s' : CodeState) (terms : List (Coefficient × ℕ))
    (he : CodeExtends s s') (hn : s.next = (codeSymbolic t s).next)
    (hb : TermsBefore terms s.next) : termSum t s' terms = termSum t s terms := by
  unfold termSum
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [(codeExtends_symbolic t s s' he c.2 (by rw [← hn]; exact hb c hc)).2.1]

lemma sharedPacketStep_aligned (m H k x v i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    (sharedPacketStep m H k x v i terms s).2.next =
      (codeSymbolic t (sharedPacketStep m H k x v i terms s).2).next := by
  let s1 := (emit (.sendPoint 0 (i + 1) x) s).2
  let s2 := (emit (.sendVector 0 (i + 1) v) s1).2
  have ha : s2.next = (codeSymbolic t s2).next := by
    simp only [s2, s1, codeSymbolic_next, emit_apply, List.length_append, List.length_singleton]
    rw [codeSymbolic_next] at hn
    omega
  have hp := localPrefix_aligned (i + 1) H k H (x, v) s2 t ha
  change ((localMomentum (i + 1) x v H k).run s2).2.next =
    (codeSymbolic t ((localMomentum (i + 1) x v H k).run s2).2).next at hp
  simp only [sharedPacketStep, state_bind_apply, state_pure_apply]
  simp only [codeSymbolic_next, emit_apply, List.length_append, List.length_singleton]
  simp only [codeSymbolic_next, s2, s1, emit_apply, StateT.run] at hp
  omega

lemma sharedPacketStep_terms_before (m H k x v i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState)
    (hv : v < s.next) (hl : TermsBefore terms.1 s.next) (hr : TermsBefore terms.2 s.next) :
    let z := sharedPacketStep m H k x v i terms s
    TermsBefore z.1.1 z.2.next ∧ TermsBefore z.1.2 z.2.next := by
  let s1 := (emit (.sendPoint 0 (i + 1) x) s).2
  let s2 := (emit (.sendVector 0 (i + 1) v) s1).2
  let packet := (localMomentum (i + 1) x v H k).run s2
  have hpn : packet.2.next = s.next + 2 + 4 * H := by
    rw [localMomentum_next]
    simp [s2, s1, emit_apply, Nat.add_assoc]
  have hpm : packet.1.2 < packet.2.next :=
    localPrefix_momentum_lt (i + 1) H k H (x, v) s2 (by dsimp [s2, s1]; simp only [emit_apply]; omega)
  dsimp only [sharedPacketStep, state_bind_apply, state_pure_apply, TermsBefore]
  constructor <;> intro c hc
  · change c ∈ terms.1 ++ [(.constant (1 / (m : ℝ)), packet.2.next)] at hc
    change c.2 < packet.2.next + 1 + 1 + 1
    rcases List.mem_append.mp hc with hc | hc
    · have := hl c hc; omega
    · have := List.mem_singleton.mp hc; subst c; simp only; omega
  · change c ∈ terms.2 ++ [(.constant (1 / (m : ℝ)), packet.1.2)] at hc
    change c.2 < packet.2.next + 1 + 1 + 1
    rcases List.mem_append.mp hc with hc | hc
    · have := hr c hc; omega
    · have := List.mem_singleton.mp hc; subst c; simp only; omega

lemma sharedPacketStep_symbolic (m H k x v i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hv : v < s.next) (hx : x < s.next)
    (hl : TermsBefore terms.1 s.next) (hr : TermsBefore terms.2 s.next) :
    let t := canonicalTuning η B
    let z := sharedPacketStep m H k x v i terms s
    termSum t z.2 z.1.1 = termSum t s terms.1 + (1 / (m : ℝ)) •
      ((1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (s.next + 2 + 4 * h + 2) 1) : LinearValue)) ∧
      termSum t z.2 z.1.2 = termSum t s terms.2 + (1 / (m : ℝ)) •
        localRaw (1 / (B : ℝ)) (s.next + 2) ((codeSymbolic t s).vectors v) H := by
  let t := canonicalTuning η B
  let w := i + 1
  let s1 := (emit (.sendPoint 0 w x) s).2
  let s2 := (emit (.sendVector 0 w v) s1).2
  let packet := (localMomentum w x v H k).run s2
  let s3 := (emit (.difference w packet.1.1 x) packet.2).2
  let s4 := (emit (.sendVector w 0 packet.2.next) s3).2
  let s5 := (emit (.sendVector w 0 packet.1.2) s4).2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : codeSymbolic t s2 = { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
    simp [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, Nat.add_assoc]
  have ha : s2.next = (codeSymbolic t s2).next := by rw [hs2n, hs2, hn]
  have hv2 : v < s2.next := by rw [hs2n]; omega
  have hp := localPrefix_values w H k H (x, v) s2 η B ha hv2
  have hp' : (codeSymbolic t packet.2).vectors packet.1.2 =
      localRaw (1 / (B : ℝ)) s2.next ((codeSymbolic t s2).vectors v) H ∧
      (codeSymbolic t packet.2).points packet.1.1 =
        localPath (1 / (H : ℝ) * η) s2.next ((codeSymbolic t s2).points x) H := hp
  have hpa : packet.2.next = (codeSymbolic t packet.2).next := localPrefix_aligned w H k H (x, v) s2 t ha
  have hpm : packet.1.2 < packet.2.next := localPrefix_momentum_lt w H k H (x, v) s2 hv2
  have hpx : (codeSymbolic t packet.2).points x = (codeSymbolic t s).points x := by
    have hh := (codeExtends_symbolic t s2 packet.2 (localPrefix_extends w H k H (x, v) s2) x
      (by rw [← ha, hs2n]; omega)).1
    exact hh.trans (by rw [hs2])
  have hdx : (codeSymbolic t s5).vectors packet.2.next =
      (1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (s.next + 2 + 4 * h + 2) 1) : LinearValue) := by
    simp only [s5, s4, s3, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform,
      symbolicStore, ← hpa, Function.update_self]
    rw [hp'.2, hpx, localPath_closed, hs2, hs2n]
    abel
  have hmv : (codeSymbolic t s5).vectors packet.1.2 =
      localRaw (1 / (B : ℝ)) (s.next + 2) ((codeSymbolic t s).vectors v) H := by
    simp only [s5, s4, s3, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform,
      symbolicStore, ← hpa, Function.update_of_ne (Nat.ne_of_lt hpm)]
    rw [hp'.1, hs2, hs2n]
  have he : CodeExtends s s5 := buildExtends_sharedPacketStep m H k x v i terms s
  have hleft := termSum_extends t s s5 terms.1 he hn hl
  have hright := termSum_extends t s s5 terms.2 he hn hr
  change termSum t s5 (terms.1 ++ [(.constant (1 / (m : ℝ)), packet.2.next)]) = _ ∧
    termSum t s5 (terms.2 ++ [(.constant (1 / (m : ℝ)), packet.1.2)]) = _
  rw [termSum_append, termSum_append, hleft, hright]
  simp only [termSum, List.map_singleton, List.sum_singleton, Coefficient.eval, hdx, hmv]
  exact ⟨rfl, rfl⟩

lemma packetPrefix_aligned (m H k x v n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    (packetPrefix m H k x v n s).2.next =
      (codeSymbolic t (packetPrefix m H k x v n s).2).next := by
  induction n with
  | zero => exact hn
  | succ n ih =>
      rw [packetPrefix_succ]
      exact sharedPacketStep_aligned m H k x v n _ _ t ih

lemma packetPrefix_terms_before (m H k x v n : ℕ) (s : CodeState) (hv : v < s.next) :
    let z := packetPrefix m H k x v n s
    TermsBefore z.1.1 z.2.next ∧ TermsBefore z.1.2 z.2.next := by
  induction n with
  | zero => exact ⟨by simp [packetPrefix_zero, TermsBefore], by simp [packetPrefix_zero, TermsBefore]⟩
  | succ n ih =>
      rw [packetPrefix_succ]
      dsimp only
      exact sharedPacketStep_terms_before m H k x v n _ _
        (by rw [packetPrefix_next]; omega) ih.1 ih.2

lemma packetPrefix_symbolic (m H k x v n : ℕ) (s : CodeState) (η : ℝ) (B : ℕ)
    (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hv : v < s.next) (hx : x < s.next) :
    let t := canonicalTuning η B
    let z := packetPrefix m H k x v n s
    termSum t z.2 z.1.1 = ∑ i ∈ Finset.range n, (1 / (m : ℝ)) •
      ((1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (s.next + i * (4 * H + 5) + 2 + 4 * h + 2) 1) : LinearValue)) ∧
      termSum t z.2 z.1.2 = ∑ i ∈ Finset.range n, (1 / (m : ℝ)) •
        localRaw (1 / (B : ℝ)) (s.next + i * (4 * H + 5) + 2)
          ((codeSymbolic t s).vectors v) H := by
  let t := canonicalTuning η B
  induction n with
  | zero => simp [packetPrefix_zero, termSum]
  | succ n ih =>
      let z := packetPrefix m H k x v n s
      have ha := packetPrefix_aligned m H k x v n s t hn
      have hb := packetPrefix_terms_before m H k x v n s hv
      have hvn : v < z.2.next := by dsimp only [z]; rw [packetPrefix_next]; omega
      have hxn : x < z.2.next := by dsimp only [z]; rw [packetPrefix_next]; omega
      have hh := sharedPacketStep_symbolic m H k x v n z.1 z.2 η B ha hvn hxn hb.1 hb.2
      have hvo : (codeSymbolic t z.2).vectors v = (codeSymbolic t s).vectors v :=
        (codeExtends_symbolic t s z.2 (packetPrefix_extends m H k x v n s) v (by rw [← hn]; exact hv)).2.1
      rw [packetPrefix_succ]
      dsimp only at hh ⊢
      constructor
      · rw [hh.1, ih.1, Finset.sum_range_succ]
        simp only [z, packetPrefix_next]
      · rw [hh.2, ih.2, hvo, Finset.sum_range_succ]
        simp only [z, packetPrefix_next, t]

lemma sharedPacketStep_records (m H k x v i h : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hv : v < s.next) (hh : h < H) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (sharedPacketStep m H k x v i terms s).2
    new.queryPoints (s.next + 2 + 4 * h) = localPath (1 / (H : ℝ) * η) (s.next + 2)
      ((codeSymbolic t s).points x) h ∧
      new.sharpInputs (s.next + 2 + 4 * h + 2) = localRaw (1 / (B : ℝ)) (s.next + 2)
        ((codeSymbolic t s).vectors v) (h + 1) := by
  let t := canonicalTuning η B
  let w := i + 1
  let s1 := (emit (.sendPoint 0 w x) s).2
  let s2 := (emit (.sendVector 0 w v) s1).2
  let packet := (localMomentum w x v H k).run s2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : codeSymbolic t s2 = { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
    simp [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, Nat.add_assoc]
  have ha2 : s2.next = (codeSymbolic t s2).next := by rw [hs2n, hs2, hn]
  have hv2 : v < s2.next := by rw [hs2n]; omega
  have hr := localPrefix_records w H k H (x, v) s2 η B ha2 hv2 h hh
  have hr' : (codeSymbolic t packet.2).queryPoints (s.next + 2 + 4 * h) =
      localPath (1 / (H : ℝ) * η) (s.next + 2) ((codeSymbolic t s).points x) h ∧
      (codeSymbolic t packet.2).sharpInputs (s.next + 2 + 4 * h + 2) =
      localRaw (1 / (B : ℝ)) (s.next + 2) ((codeSymbolic t s).vectors v) (h + 1) := by
    have hs2' := hs2
    dsimp only [t] at hs2'
    simpa only [packet, localMomentum_prefix, t, hs2n, hs2'] using hr
  convert hr' using 1 <;>
    simp only [sharedPacketStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
      InstructionTemplate.instantiate, symbolicPerform, symbolicStore, packet, s2, s1, w, t, StateT.run]

lemma sharedPacketStep_sets (m H k x v i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) (hv : v < s.next) :
    let new := codeSymbolic t (sharedPacketStep m H k x v i terms s).2
    let old := codeSymbolic t s
    new.queries = old.queries ∪ (Finset.range H).image (fun h => s.next + 2 + 4 * h) ∧
      new.sharps = old.sharps ∪ (Finset.range H).image (fun h => s.next + 2 + 4 * h + 2) ∧
      new.units = old.units := by
  let w := i + 1
  let s1 := (emit (.sendPoint 0 w x) s).2
  let s2 := (emit (.sendVector 0 w v) s1).2
  let packet := (localMomentum w x v H k).run s2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : codeSymbolic t s2 = { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
    simp [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, Nat.add_assoc]
  have ha2 : s2.next = (codeSymbolic t s2).next := by rw [hs2n, hs2, hn]
  have hv2 : v < s2.next := by rw [hs2n]; omega
  have hr := localPrefix_sets w H k H (x, v) s2 t ha2 hv2
  have hr' : (codeSymbolic t packet.2).queries = (codeSymbolic t s).queries ∪
      (Finset.range H).image (fun h => s.next + 2 + 4 * h) ∧
      (codeSymbolic t packet.2).sharps = (codeSymbolic t s).sharps ∪
      (Finset.range H).image (fun h => s.next + 2 + 4 * h + 2) ∧
      (codeSymbolic t packet.2).units = (codeSymbolic t s).units := by
    simpa only [packet, localMomentum_prefix, hs2n, hs2] using hr
  convert hr' using 1 <;>
    simp only [sharedPacketStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
      InstructionTemplate.instantiate, symbolicPerform, symbolicStore, packet, s2, s1, w, StateT.run]

lemma packetPrefix_records (m H k x v n i h : ℕ) (s : CodeState) (η : ℝ) (B : ℕ)
    (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hv : v < s.next) (hx : x < s.next) (hi : i < n) (hh : h < H) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (packetPrefix m H k x v n s).2
    let first := s.next + i * (4 * H + 5) + 2
    new.queryPoints (first + 4 * h) = localPath (1 / (H : ℝ) * η) first ((codeSymbolic t s).points x) h ∧
      new.sharpInputs (first + 4 * h + 2) = localRaw (1 / (B : ℝ)) first
        ((codeSymbolic t s).vectors v) (h + 1) := by
  let t := canonicalTuning η B
  induction n with
  | zero => omega
  | succ n ih =>
      let z := packetPrefix m H k x v n s
      have ha := packetPrefix_aligned m H k x v n s t hn
      have he := buildExtends_sharedPacketStep m H k x v n z.1 z.2
      have hz : z.2.next = s.next + n * (4 * H + 5) := packetPrefix_next m H k x v n s
      rw [packetPrefix_succ]
      dsimp only
      by_cases hin : i = n
      · subst i
        have hr := sharedPacketStep_records m H k x v n h z.1 z.2 η B ha (by rw [hz]; omega) hh
        have hxo := (codeExtends_symbolic t s z.2 (packetPrefix_extends m H k x v n s) x
          (by rw [← hn]; exact hx)).1
        have hvo := (codeExtends_symbolic t s z.2 (packetPrefix_extends m H k x v n s) v
          (by rw [← hn]; exact hv)).2.1
        dsimp only at hr
        rw [hz, hxo, hvo] at hr
        exact hr
      · have hi' : i < n := by omega
        have hmul := Nat.mul_le_mul_right (4 * H + 5) (show i + 1 ≤ n by omega)
        have hq : s.next + i * (4 * H + 5) + 2 + 4 * h < (codeSymbolic t z.2).next := by
          rw [← ha, hz]
          rw [Nat.add_mul] at hmul
          omega
        have hs : s.next + i * (4 * H + 5) + 2 + 4 * h + 2 < (codeSymbolic t z.2).next := by
          rw [← ha, hz]
          rw [Nat.add_mul] at hmul
          omega
        exact ⟨(codeExtends_symbolic t z.2 _ he _ hq).2.2.1.trans (ih hi').1,
          (codeExtends_symbolic t z.2 _ he _ hs).2.2.2.trans (ih hi').2⟩

lemma packetPrefix_sets (m H k x v n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) (hv : v < s.next) :
    let new := codeSymbolic t (packetPrefix m H k x v n s).2
    let old := codeSymbolic t s
    new.queries = old.queries ∪ (Finset.range n).biUnion (fun i =>
      (Finset.range H).image (fun h => s.next + i * (4 * H + 5) + 2 + 4 * h)) ∧
      new.sharps = old.sharps ∪ (Finset.range n).biUnion (fun i =>
        (Finset.range H).image (fun h => s.next + i * (4 * H + 5) + 2 + 4 * h + 2)) ∧
      new.units = old.units := by
  induction n with
  | zero => simp [packetPrefix_zero]
  | succ n ih =>
      have ha := packetPrefix_aligned m H k x v n s t hn
      have hh := sharedPacketStep_sets m H k x v n (packetPrefix m H k x v n s).1
        (packetPrefix m H k x v n s).2 t ha (by rw [packetPrefix_next]; omega)
      rw [packetPrefix_succ]
      dsimp only at hh ⊢
      rw [hh.1, hh.2.1, hh.2.2, ih.1, ih.2.1, ih.2.2, packetPrefix_next]
      simp [Finset.range_add_one, Finset.union_comm, Finset.union_left_comm]

lemma mix_symbolic (w : ℕ) (terms : List (Coefficient × ℕ)) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    (codeSymbolic t (emit (.mix w terms) s).2).vectors (emit (.mix w terms) s).1 = termSum t s terms := by
  rw [codeSymbolic_emit]
  simp [InstructionTemplate.instantiate, symbolicPerform, symbolicStore,
    emit_apply, hn, termSum, List.map_map, Function.comp_def]

lemma mix_move_mix_symbolic (x : ℕ) (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ))
    (s : CodeState) (t : Tuning) (hn : s.next = (codeSymbolic t s).next)
    (hr : TermsBefore terms.2 s.next) :
    let z := ((do
      let dx ← emit (.mix 0 terms.1)
      let y ← emit (.move 0 x dx (.constant 1))
      let v ← emit (.mix 0 terms.2)
      return (y, v)) : StateM CodeState (ℕ × ℕ)) s
    (codeSymbolic t z.2).points z.1.1 = (codeSymbolic t s).points x + termSum t s terms.1 ∧
      (codeSymbolic t z.2).vectors z.1.2 = termSum t s terms.2 := by
  let s1 := (emit (.mix 0 terms.1) s).2
  let s2 := (emit (.move 0 x s.next (.constant 1)) s1).2
  let s3 := (emit (.mix 0 terms.2) s2).2
  have hn1 : s1.next = (codeSymbolic t s1).next := by
    simp only [s1, codeSymbolic_next, emit_apply, List.length_append, List.length_singleton]
    rw [codeSymbolic_next] at hn
    omega
  have hn2 : s2.next = (codeSymbolic t s2).next := by
    simp only [s2, codeSymbolic_next, emit_apply, List.length_append, List.length_singleton]
    rw [codeSymbolic_next] at hn1
    omega
  have hvec : (codeSymbolic t s1).vectors s.next = termSum t s terms.1 := mix_symbolic 0 terms.1 s t hn
  have hpt : (codeSymbolic t s1).points x = (codeSymbolic t s).points x := by
    simp [s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, symbolicStore]
  have hsum : termSum t s2 terms.2 = termSum t s terms.2 :=
    termSum_extends t s s2 terms.2
      (codeExtends_trans _ _ _ (codeExtends_emit s _) (codeExtends_emit s1 _)) hn hr
  constructor
  · change (codeSymbolic t s3).points s1.next = _
    simp only [s3, s2, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform,
      symbolicStore, ← hn1, Function.update_self, Coefficient.eval, one_smul]
    rw [hpt, hvec]
  · change (codeSymbolic t s3).vectors s2.next = _
    exact (mix_symbolic 0 terms.2 s2 t hn2).trans hsum

lemma sharedRoundStep_symbolic (m H k : ℕ) (state : (ℕ → ℕ) × ℕ) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hv : state.2 < s.next) (hx : state.1 k < s.next) :
    let t := canonicalTuning η B
    let z := sharedRoundStep m H k state s
    (codeSymbolic t z.2).points (z.1.1 (k + 1)) = (codeSymbolic t s).points (state.1 k) +
      ∑ i ∈ Finset.range m, (1 / (m : ℝ)) • ((1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (s.next + i * (4 * H + 5) + 2 + 4 * h + 2) 1) : LinearValue)) ∧
      (codeSymbolic t z.2).vectors z.1.2 = ∑ i ∈ Finset.range m, (1 / (m : ℝ)) •
        localRaw (1 / (B : ℝ)) (s.next + i * (4 * H + 5) + 2) ((codeSymbolic t s).vectors state.2) H := by
  let t := canonicalTuning η B
  let z := packetPrefix m H k (state.1 k) state.2 m s
  have ha := packetPrefix_aligned m H k (state.1 k) state.2 m s t hn
  have hb := packetPrefix_terms_before m H k (state.1 k) state.2 m s hv
  have hp := packetPrefix_symbolic m H k (state.1 k) state.2 m s η B hn hv hx
  have hxold := (codeExtends_symbolic t s z.2 (packetPrefix_extends m H k (state.1 k) state.2 m s)
    (state.1 k) (by rw [← hn]; exact hx)).1
  have hc := mix_move_mix_symbolic (state.1 k) z.1 z.2 t ha hb.2
  constructor
  · calc
      _ = (codeSymbolic t z.2).points (state.1 k) + termSum t z.2 z.1.1 := by
        simpa only [sharedRoundStep, state_bind_apply, state_pure_apply, z, packetPrefix,
          Function.update_self] using hc.1
      _ = _ := by rw [hxold, hp.1]
  · calc
      _ = termSum t z.2 z.1.2 := by
        simpa only [sharedRoundStep, state_bind_apply, state_pure_apply, z, packetPrefix] using hc.2
      _ = _ := hp.2

lemma buildExtends_sharedRoundStep (m H k : ℕ) (state : (ℕ → ℕ) × ℕ) :
    BuildExtends (sharedRoundStep m H k state) := by
  unfold sharedRoundStep
  apply buildExtends_bind
  · intro s
    exact packetPrefix_extends m H k (state.1 k) state.2 m s
  · intro terms
    apply buildExtends_bind _ _ (buildExtends_emit _)
    intro dx
    apply buildExtends_bind _ _ (buildExtends_emit _)
    intro x
    apply buildExtends_bind _ _ (buildExtends_emit _)
    intro v
    exact buildExtends_pure _

def mainIndex (m H B k : ℕ) : ℕ := if k = 0 then 0 else m * B + k * (m * (4 * H + 5) + 3)

def momentumIndex (m H B k : ℕ) : ℕ := m * B + k * (m * (4 * H + 5) + 3) + 1

def queryIndex (m H B k i h : ℕ) : ℕ :=
  m * B + 4 + k * (m * (4 * H + 5) + 3) + i * (4 * H + 5) + 4 * h

def sharpIndex (m H B k i h : ℕ) : ℕ := queryIndex m H B k i h + 2

lemma sharedPrefix_registers (m H K B : ℕ) :
    (∀ j ≤ K, (sharedPrefix m H K B).1.1 j = mainIndex m H B j) ∧
      (sharedPrefix m H K B).1.2 = momentumIndex m H B K := by
  induction K with
  | zero =>
      constructor
      · intro j hj
        have : j = 0 := by omega
        subst j
        rfl
      · rw [sharedPrefix_zero]
        dsimp only
        rw [localBatch_register]
        simp [momentumIndex, Nat.add_comm]
  | succ K ih =>
      rw [sharedPrefix_succ]
      dsimp only
      rw [(sharedRoundStep_registers m H K _ _).1]
      dsimp only
      constructor
      · intro j hj
        by_cases hjk : j = K + 1
        · subst j
          rw [Function.update_self, sharedPrefix_next]
          simp [mainIndex, Nat.add_mul]
          omega
        · rw [Function.update_of_ne hjk]
          exact ih.1 j (by omega)
      · rw [sharedPrefix_next]
        dsimp [momentumIndex]
        rw [Nat.add_mul]
        omega

lemma sharedPrefix_valid (workers m H K B : ℕ) (t : Tuning) (ht : t.Valid)
    (hw0 : 0 < workers) (hw : m < workers) :
    let z := sharedPrefix m H K B
    CodeValid workers t z.2 ∧ (∀ j, z.1.1 j ∈ (codeLayout t z.2).points 0) ∧
      z.1.2 ∈ (codeLayout t z.2).vectors 0 := by
  have hx : 0 ∈ (codeLayout t {}).points 0 := by simp [codeLayout, codeInstructions, finalLayout]
  have hi := localBatch_valid workers t 0 0 (m * B) {} (codeValid_initial workers t) hw0 hx
  let init := (localBatch 0 0 (m * B)).run {}
  let Inv := fun (state : (ℕ → ℕ) × ℕ) (s : CodeState) => CodeValid workers t s ∧
    (∀ j, state.1 j ∈ (codeLayout t s).points 0) ∧ state.2 ∈ (codeLayout t s).vectors 0
  apply state_forIn_invariant (sharedRoundStep m H) (List.range K) Inv
  · intro k _ state s h
    have hc := sharedRoundStep_valid workers m H k t ht state s h.1 hw0 hw h.2.1 h.2.2
    exact ⟨hc.1, hc.2.2⟩
  · exact ⟨hi.1, (fun _ => (hi.2.1 0).1 hx), hi.2.2⟩

lemma sharedPrefix_extends (m H K B j : ℕ) (hj : j ≤ K) :
    CodeExtends (sharedPrefix m H j B).2 (sharedPrefix m H K B).2 := by
  induction K with
  | zero =>
      have : j = 0 := by omega
      subst j
      exact codeExtends_refl _
  | succ K ih =>
      by_cases h : j ≤ K
      · rw [sharedPrefix_succ]
        exact codeExtends_trans _ _ _ (ih h) (buildExtends_sharedRoundStep m H K _ _)
      · have : j = K + 1 := by omega
        subst j
        exact codeExtends_refl _

lemma mainIndex_lt (m H B j K : ℕ) (hj : j ≤ K) :
    mainIndex m H B j < m * B + 2 + K * (m * (4 * H + 5) + 3) := by
  have hh := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) hj
  simp only [mainIndex]
  split_ifs <;> omega

lemma momentumIndex_lt (m H B j K : ℕ) (hj : j ≤ K) :
    momentumIndex m H B j < m * B + 2 + K * (m * (4 * H + 5) + 3) := by
  have hh := Nat.mul_le_mul_right (m * (4 * H + 5) + 3) hj
  dsimp [momentumIndex]
  omega

lemma sharedPrefix_old (workers m H K B j : ℕ) (t : Tuning) (ht : t.Valid)
    (hw0 : 0 < workers) (hw : m < workers) (hj : j ≤ K) :
    (codeSymbolic t (sharedPrefix m H K B).2).points (mainIndex m H B j) =
      (codeSymbolic t (sharedPrefix m H j B).2).points (mainIndex m H B j) ∧
    (codeSymbolic t (sharedPrefix m H K B).2).vectors (momentumIndex m H B j) =
      (codeSymbolic t (sharedPrefix m H j B).2).vectors (momentumIndex m H B j) := by
  have hv := (sharedPrefix_valid workers m H j B t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have he := sharedPrefix_extends m H K B j hj
  have hx : mainIndex m H B j < (codeSymbolic t (sharedPrefix m H j B).2).next := by
    rw [← hn, sharedPrefix_next]
    exact mainIndex_lt m H B j j le_rfl
  have hm : momentumIndex m H B j < (codeSymbolic t (sharedPrefix m H j B).2).next := by
    rw [← hn, sharedPrefix_next]
    exact momentumIndex_lt m H B j j le_rfl
  exact ⟨(codeExtends_symbolic t _ _ he _ hx).1, (codeExtends_symbolic t _ _ he _ hm).2.1⟩

noncomputable def mainValue (m H B : ℕ) (t : Tuning) (k : ℕ) : LinearValue :=
  (codeSymbolic t (sharedPrefix m H k B).2).points (mainIndex m H B k)

noncomputable def bufferValue (m H B : ℕ) (t : Tuning) (k : ℕ) : LinearValue :=
  (codeSymbolic t (sharedPrefix m H k B).2).vectors (momentumIndex m H B k)

lemma shared_recurrences (workers m H K B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers) :
    mainValue m H B (canonicalTuning η B) (K + 1) = mainValue m H B (canonicalTuning η B) K +
      ∑ i ∈ Finset.range m, (1 / (m : ℝ)) • ((1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (sharpIndex m H B K i h) 1) : LinearValue)) ∧
      bufferValue m H B (canonicalTuning η B) (K + 1) = ∑ i ∈ Finset.range m, (1 / (m : ℝ)) •
        localRaw (1 / (B : ℝ)) (queryIndex m H B K i 0) (bufferValue m H B (canonicalTuning η B) K) H := by
  let t := canonicalTuning η B
  let z := sharedPrefix m H K B
  have hv := sharedPrefix_valid workers m H K B t ht hw0 hw
  have hn := codeValid_symbolic_next workers t z.2 hv.1
  have hb := codeValid_register_bound workers t z.2 hv.1
  have hr := sharedRoundStep_symbolic m H K z.1 z.2 η B hn (hb.2 0 _ hv.2.2) (hb.1 0 _ (hv.2.1 K))
  have hregs := sharedPrefix_registers m H K B
  have hnextregs := sharedPrefix_registers m H (K + 1) B
  have hxn : (sharedRoundStep m H K z.1 z.2).1.1 (K + 1) = mainIndex m H B (K + 1) := by
    simpa only [sharedPrefix_succ] using hnextregs.1 (K + 1) le_rfl
  have hmn : (sharedRoundStep m H K z.1 z.2).1.2 = momentumIndex m H B (K + 1) := by
    simpa only [sharedPrefix_succ] using hnextregs.2
  dsimp only at hr
  rw [hxn, hmn, hregs.1 K le_rfl, hregs.2] at hr
  constructor
  · change (codeSymbolic t (sharedPrefix m H (K + 1) B).2).points _ = _
    rw [sharedPrefix_succ, hr.1]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    congr 2
    rw [show z.2.next = m * B + 2 + K * (m * (4 * H + 5) + 3) from sharedPrefix_next m H K B]
    dsimp [sharpIndex, queryIndex]
    omega
  · change (codeSymbolic t (sharedPrefix m H (K + 1) B).2).vectors _ = _
    rw [sharedPrefix_succ, hr.2]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    rw [show z.2.next = m * B + 2 + K * (m * (4 * H + 5) + 3) from sharedPrefix_next m H K B]
    simp [queryIndex]
    omega

lemma mainValue_zero (m H B : ℕ) (t : Tuning) : mainValue m H B t 0 = 0 := by
  dsimp only [mainValue]
  rw [sharedPrefix_zero]
  dsimp only
  rw [localBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  change (codeSymbolic t (batchPrefix 0 0 (m * B) (m * B) {}).2).points 0 = 0
  rw [batchPrefix_points]
  rfl

lemma bufferValue_zero (m H B : ℕ) (t : Tuning) :
    bufferValue m H B t 0 = (1 / ((m * B : ℕ) : ℝ)) •
      ∑ j ∈ Finset.range (m * B), ((Finsupp.single (1 + j) 1, 0) : LinearValue) := by
  have hh := localBatch_symbolic 0 0 (m * B) {} t rfl
  have hm := localBatch_register 0 0 (m * B) {}
  dsimp only [bufferValue]
  rw [sharedPrefix_zero]
  dsimp only
  rw [show momentumIndex m H B 0 = ((localBatch 0 0 (m * B)).run {}).1 by
    rw [hm]; simp [momentumIndex, Nat.add_comm]]
  exact hh

lemma sharedRoundStep_records (m H k i h : ℕ) (state : (ℕ → ℕ) × ℕ) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hv : state.2 < s.next) (hx : state.1 k < s.next) (hi : i < m) (hh : h < H) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (sharedRoundStep m H k state s).2
    let first := s.next + i * (4 * H + 5) + 2
    new.queryPoints (first + 4 * h) = localPath (1 / (H : ℝ) * η) first
      ((codeSymbolic t s).points (state.1 k)) h ∧
      new.sharpInputs (first + 4 * h + 2) = localRaw (1 / (B : ℝ)) first
        ((codeSymbolic t s).vectors state.2) (h + 1) := by
  have hr := packetPrefix_records m H k (state.1 k) state.2 m i h s η B hn hv hx hi hh
  convert hr using 1
  simp only [sharedRoundStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
      InstructionTemplate.instantiate, symbolicPerform, symbolicStore, packetPrefix]

lemma sharedRoundStep_sets (m H k : ℕ) (state : (ℕ → ℕ) × ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) (hv : state.2 < s.next) :
    let new := codeSymbolic t (sharedRoundStep m H k state s).2
    let old := codeSymbolic t s
    new.queries = old.queries ∪ (Finset.range m).biUnion (fun i =>
      (Finset.range H).image (fun h => s.next + i * (4 * H + 5) + 2 + 4 * h)) ∧
      new.sharps = old.sharps ∪ (Finset.range m).biUnion (fun i =>
        (Finset.range H).image (fun h => s.next + i * (4 * H + 5) + 2 + 4 * h + 2)) ∧
      new.units = old.units := by
  have hr := packetPrefix_sets m H k (state.1 k) state.2 m s t hn hv
  convert hr using 1
  simp only [sharedRoundStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
      InstructionTemplate.instantiate, symbolicPerform, symbolicStore, packetPrefix]

def roundQueries (m H B k : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion (fun i => (Finset.range H).image (queryIndex m H B k i))

def roundSharps (m H B k : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion (fun i => (Finset.range H).image (sharpIndex m H B k i))

def querySet (m H B K : ℕ) : Finset ℕ :=
  (Finset.range (m * B)).image (fun j => 1 + j) ∪ (Finset.range K).biUnion (roundQueries m H B)

def sharpSet (m H B K : ℕ) : Finset ℕ := (Finset.range K).biUnion (roundSharps m H B)

lemma querySet_succ (m H B K : ℕ) :
    querySet m H B (K + 1) = querySet m H B K ∪ roundQueries m H B K := by
  simp [querySet, Finset.range_add_one, Finset.union_assoc, Finset.union_comm]

lemma sharpSet_succ (m H B K : ℕ) :
    sharpSet m H B (K + 1) = sharpSet m H B K ∪ roundSharps m H B K := by
  simp [sharpSet, Finset.range_add_one, Finset.union_comm]

lemma sharedPrefix_sets (workers m H K B : ℕ) (t : Tuning) (ht : t.Valid)
    (hw0 : 0 < workers) (hw : m < workers) :
    let new := codeSymbolic t (sharedPrefix m H K B).2
    new.queries = querySet m H B K ∧ new.sharps = sharpSet m H B K ∧ new.units = ∅ := by
  induction K with
  | zero =>
      rw [sharedPrefix_zero]
      dsimp only
      rw [localBatch_prefix]
      dsimp only
      rw [codeSymbolic_emit]
      have hh := batchPrefix_sets 0 0 (m * B) (m * B) {} t rfl
      simpa only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, querySet, sharpSet,
        Finset.range_zero, Finset.biUnion_empty, Finset.union_empty, codeSymbolic, codeInstructions,
        List.map_nil, List.foldl_nil, Finset.empty_union] using hh
  | succ K ih =>
      let z := sharedPrefix m H K B
      have hv := sharedPrefix_valid workers m H K B t ht hw0 hw
      have hn := codeValid_symbolic_next workers t z.2 hv.1
      have hb := codeValid_register_bound workers t z.2 hv.1
      have hh := sharedRoundStep_sets m H K z.1 z.2 t hn (hb.2 0 _ hv.2.2)
      have hq (i : ℕ) : (fun h => z.2.next + i * (4 * H + 5) + 2 + 4 * h) = queryIndex m H B K i := by
        funext h
        rw [show z.2.next = m * B + 2 + K * (m * (4 * H + 5) + 3) from sharedPrefix_next m H K B]
        dsimp [queryIndex]
        omega
      have he (i : ℕ) : (fun h => z.2.next + i * (4 * H + 5) + 2 + 4 * h + 2) = sharpIndex m H B K i := by
        funext h
        change (fun h => z.2.next + i * (4 * H + 5) + 2 + 4 * h) h + 2 = _
        rw [hq]
        rfl
      dsimp only at hh
      simp only [hq, he] at hh
      rw [sharedPrefix_succ, querySet_succ, sharpSet_succ]
      exact ⟨hh.1.trans (congrArg (fun s => s ∪ roundQueries m H B K) ih.1),
        hh.2.1.trans (congrArg (fun s => s ∪ roundSharps m H B K) ih.2.1), hh.2.2.trans ih.2.2⟩

lemma sharedPrefix_new_records (workers m H k B i h : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hi : i < m) (hh : h < H) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (sharedPrefix m H (k + 1) B).2
    new.queryPoints (queryIndex m H B k i h) = localPath (1 / (H : ℝ) * η) (queryIndex m H B k i 0)
      (mainValue m H B t k) h ∧
      new.sharpInputs (sharpIndex m H B k i h) = localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0)
        (bufferValue m H B t k) (h + 1) := by
  let t := canonicalTuning η B
  let z := sharedPrefix m H k B
  have hv := sharedPrefix_valid workers m H k B t ht hw0 hw
  have hn := codeValid_symbolic_next workers t z.2 hv.1
  have hb := codeValid_register_bound workers t z.2 hv.1
  have hr := sharedRoundStep_records m H k i h z.1 z.2 η B hn
    (hb.2 0 _ hv.2.2) (hb.1 0 _ (hv.2.1 k)) hi hh
  have hregs := sharedPrefix_registers m H k B
  have hfirst : z.2.next + i * (4 * H + 5) + 2 = queryIndex m H B k i 0 := by
    rw [show z.2.next = m * B + 2 + k * (m * (4 * H + 5) + 3) from sharedPrefix_next m H k B]
    dsimp [queryIndex]
    omega
  have hq : z.2.next + i * (4 * H + 5) + 2 + 4 * h = queryIndex m H B k i h := by
    rw [hfirst]; simp [queryIndex, Nat.add_assoc]
  have he : z.2.next + i * (4 * H + 5) + 2 + 4 * h + 2 = sharpIndex m H B k i h := by rw [hq]; rfl
  dsimp only at hr
  rw [hregs.1 k le_rfl, hregs.2, he, hq, hfirst] at hr
  simpa only [mainValue, bufferValue, sharedPrefix_succ, z, t] using hr

lemma sharedPrefix_records (workers m H K B k i h : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hk : k < K) (hi : i < m) (hh : h < H) :
    let t := canonicalTuning η B
    let new := codeSymbolic t (sharedPrefix m H K B).2
    new.queryPoints (queryIndex m H B k i h) = localPath (1 / (H : ℝ) * η) (queryIndex m H B k i 0)
      (mainValue m H B t k) h ∧
      new.sharpInputs (sharpIndex m H B k i h) = localRaw (1 / (B : ℝ)) (queryIndex m H B k i 0)
        (bufferValue m H B t k) (h + 1) := by
  let t := canonicalTuning η B
  have hv := (sharedPrefix_valid workers m H (k + 1) B t ht hw0 hw).1
  have hn := codeValid_symbolic_next workers t _ hv
  have he := sharedPrefix_extends m H K B (k + 1) (by omega)
  have him := Nat.mul_le_mul_right (4 * H + 5) (show i + 1 ≤ m by omega)
  rw [Nat.add_mul] at him
  have hq : queryIndex m H B k i h < (codeSymbolic t (sharedPrefix m H (k + 1) B).2).next := by
    rw [← hn, sharedPrefix_next]
    dsimp [queryIndex]
    rw [Nat.add_mul]
    omega
  have hs : sharpIndex m H B k i h < (codeSymbolic t (sharedPrefix m H (k + 1) B).2).next := by
    rw [← hn, sharedPrefix_next]
    dsimp [sharpIndex, queryIndex]
    rw [Nat.add_mul]
    omega
  have hr := sharedPrefix_new_records workers m H k B i h η ht hw0 hw hi hh
  exact ⟨(codeExtends_symbolic t _ _ he _ hq).2.2.1.trans hr.1,
    (codeExtends_symbolic t _ _ he _ hs).2.2.2.trans hr.2⟩

end LongTails.Proofs.BirchNonEuclideanShared
