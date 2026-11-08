import LongTails.Algorithms.BirchCausalPackets
import LongTails.Proofs.BirchNonEuclideanCoefficients

namespace LongTails.Proofs.BirchCausalConstruction

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients

def PacketValid (workers : ℕ) (t : Tuning) (code : PacketCode) : Prop :=
  ∀ w x m s, CodeValid workers t s → w < workers →
    x ∈ (codeLayout t s).points w → m ∈ (codeLayout t s).vectors w →
    let z := code w x m s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      z.1.1 ∈ (codeLayout t z.2).points w ∧ z.1.2 ∈ (codeLayout t z.2).vectors w

lemma atom_valid (workers : ℕ) (t : Tuning) (ht : t.Valid) (H round index : ℕ) :
    PacketValid workers t (atom H round index) := by
  intro w x m s hs hw hx hm
  exact momentumStep_valid workers t ht w H round index (x, m) s hs hw hx hm

lemma sequence_valid (workers : ℕ) (t : Tuning) (left right : PacketCode)
    (hl : PacketValid workers t left) (hr : PacketValid workers t right) :
    PacketValid workers t (sequence left right) := by
  intro w x m s hs hw hx hm
  have hleft := hl w x m s hs hw hx hm
  have hright := hr w (left w x m s).1.1 (left w x m s).1.2
    (left w x m s).2 hleft.1 hw hleft.2.2.1 hleft.2.2.2
  exact ⟨hright.1, retains_trans t s _ _ hleft.2.1 hright.2.1, hright.2.2⟩

lemma join_valid (workers : ℕ) (t : Tuning) (w x m : ℕ)
    (left right : ℕ × ℕ) (s : CodeState) (hs : CodeValid workers t s)
    (hw : w < workers) (hx : x ∈ (codeLayout t s).points w)
    (hm : m ∈ (codeLayout t s).vectors w)
    (hlx : left.1 ∈ (codeLayout t s).points w)
    (hlm : left.2 ∈ (codeLayout t s).vectors w)
    (hrx : right.1 ∈ (codeLayout t s).points w)
    (hrm : right.2 ∈ (codeLayout t s).vectors w) :
    let z := join w x m left right s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      z.1.1 ∈ (codeLayout t z.2).points w ∧ z.1.2 ∈ (codeLayout t z.2).vectors w := by
  let z1 := emit (.difference w left.1 x) s
  let z2 := emit (.difference w right.1 x) z1.2
  let terms := [(Coefficient.constant 1, z1.1), (.constant 1, z2.1)]
  let z3 := emit (.mix w terms) z2.2
  let z4 := emit (.move w x z3.1 (.constant 1)) z3.2
  let momenta := [(Coefficient.constant 1, left.2), (.constant 1, right.2), (.constant (-1), m)]
  let z5 := emit (.mix w momenta) z4.2
  have h1 := difference_valid workers t s hs w left.1 x hw hlx hx
  have ret1 := retains_emit t (.difference w left.1 x) s
  have h2 := difference_valid workers t z1.2 h1.1 w right.1 x hw
    ((ret1 w).1 hrx) ((ret1 w).1 hx)
  have ret2 := retains_trans t s z1.2 z2.2 ret1 (retains_emit t _ z1.2)
  have hterms : ∀ v ∈ terms, v.2 ∈ (codeLayout t z2.2).vectors w := by
    intro v hv
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ((retains_emit t (.difference w right.1 x) z1.2) w).2 h1.2
    · exact h2.2
  have h3 := codeValid_emit workers t (.mix w terms) z2.2 h2.1
    (mix_legal workers t z2.2 w terms hw hterms)
  have hd := mix_member workers t z2.2 h2.1 w terms
  have ret3 := retains_trans t s z2.2 z3.2 ret2 (retains_emit t _ z2.2)
  have h4 := codeValid_emit workers t (.move w x z3.1 (.constant 1)) z3.2 h3
    ⟨hw, (ret3 w).1 hx, hd, by norm_num [Coefficient.eval]⟩
  have hy := move_member workers t z3.2 h3 w x z3.1 (.constant 1)
  have ret4 := retains_trans t s z3.2 z4.2 ret3 (retains_emit t _ z3.2)
  have hmomenta : ∀ v ∈ momenta, v.2 ∈ (codeLayout t z4.2).vectors w := by
    intro v hv
    simp only [momenta, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact (ret4 w).2 hlm
    · exact (ret4 w).2 hrm
    · exact (ret4 w).2 hm
  have h5 := codeValid_emit workers t (.mix w momenta) z4.2 h4
    (mix_legal workers t z4.2 w momenta hw hmomenta)
  have hv := mix_member workers t z4.2 h4 w momenta
  have ret5 := retains_trans t s z4.2 z5.2 ret4 (retains_emit t _ z4.2)
  exact ⟨h5, ret5, ((retains_emit t (.mix w momenta) z4.2) w).1 hy, hv⟩

lemma sendState_valid (workers : ℕ) (t : Tuning) (sender receiver x m : ℕ)
    (s : CodeState) (hs : CodeValid workers t s) (hfrom : sender < workers)
    (hto : receiver < workers) (hx : x ∈ (codeLayout t s).points sender)
    (hm : m ∈ (codeLayout t s).vectors sender) :
    let s' := (sendState sender receiver x m s).2
    CodeValid workers t s' ∧ Retains t s s' ∧
      x ∈ (codeLayout t s').points receiver ∧ m ∈ (codeLayout t s').vectors receiver := by
  let s1 := (emit (.sendPoint sender receiver x) s).2
  let s2 := (emit (.sendVector sender receiver m) s1).2
  have h1 := sendPoint_valid workers t s hs sender receiver x hfrom hto hx
  have r1 := retains_emit t (.sendPoint sender receiver x) s
  have h2 := sendVector_valid workers t s1 h1.1 sender receiver m hfrom hto ((r1 sender).2 hm)
  have r2 := retains_emit t (.sendVector sender receiver m) s1
  exact ⟨h2.1, retains_trans t s s1 s2 r1 r2, (r2 receiver).1 h1.2, h2.2⟩

lemma fork_valid (workers : ℕ) (t : Tuning) (leftWorker rightWorker : ℕ)
    (left right : PacketCode) (hlw : leftWorker < workers) (hrw : rightWorker < workers)
    (hl : PacketValid workers t left) (hr : PacketValid workers t right) :
    PacketValid workers t (fork leftWorker rightWorker left right) := by
  intro w x m s hs hw hx hm
  let s1 := (sendState w leftWorker x m s).2
  let l := left leftWorker x m s1
  let s2 := (sendState leftWorker w l.1.1 l.1.2 l.2).2
  let s3 := (sendState w rightWorker x m s2).2
  let r := right rightWorker x m s3
  let s4 := (sendState rightWorker w r.1.1 r.1.2 r.2).2
  have h1 := sendState_valid workers t w leftWorker x m s hs hw hlw hx hm
  have hleft := hl leftWorker x m s1 h1.1 hlw h1.2.2.1 h1.2.2.2
  have rleft := retains_trans t s s1 l.2 h1.2.1 hleft.2.1
  have h2 := sendState_valid workers t leftWorker w l.1.1 l.1.2 l.2
    hleft.1 hlw hw hleft.2.2.1 hleft.2.2.2
  have ret2 := retains_trans t s l.2 s2 rleft h2.2.1
  have h3 := sendState_valid workers t w rightWorker x m s2 h2.1 hw hrw
    ((ret2 w).1 hx) ((ret2 w).2 hm)
  have hright := hr rightWorker x m s3 h3.1 hrw h3.2.2.1 h3.2.2.2
  have h4 := sendState_valid workers t rightWorker w r.1.1 r.1.2 r.2
    hright.1 hrw hw hright.2.2.1 hright.2.2.2
  have ret24 := retains_trans t s2 s3 s4 h3.2.1
    (retains_trans t s3 r.2 s4 hright.2.1 h4.2.1)
  have ret4 := retains_trans t s s2 s4 ret2 ret24
  have hj := join_valid workers t w x m l.1 r.1 s4 h4.1 hw
    ((ret4 w).1 hx) ((ret4 w).2 hm)
    ((ret24 w).1 h2.2.2.1) ((ret24 w).2 h2.2.2.2) h4.2.2.1 h4.2.2.2
  exact ⟨hj.1, retains_trans t s s4 _ ret4 hj.2.1, hj.2.2⟩

lemma nestedPacket_valid (workers : ℕ) (t : Tuning) (ht : t.Valid)
    (H round leftWorker rightWorker : ℕ) (hlw : leftWorker < workers)
    (hrw : rightWorker < workers) :
    PacketValid workers t (nestedPacket H round leftWorker rightWorker) := by
  apply sequence_valid
  · exact atom_valid workers t ht H round 0
  · apply sequence_valid
    · apply fork_valid workers t leftWorker rightWorker _ _ hlw hrw
      · exact sequence_valid workers t _ _ (atom_valid workers t ht H round 1)
          (atom_valid workers t ht H round 2)
      · exact sequence_valid workers t _ _ (atom_valid workers t ht H round 3)
          (atom_valid workers t ht H round 4)
    · exact atom_valid workers t ht H round 5

lemma join_symbolic (t : Tuning) (w x m : ℕ) (left right : ℕ × ℕ) (s : CodeState)
    (hnext : (codeSymbolic t s).next = s.next)
    (hm : m < s.next) (hlm : left.2 < s.next) (hrm : right.2 < s.next) :
    let z := join w x m left right s
    (codeSymbolic t z.2).points z.1.1 =
      (codeSymbolic t s).points left.1 + (codeSymbolic t s).points right.1 -
        (codeSymbolic t s).points x ∧
    (codeSymbolic t z.2).vectors z.1.2 =
      (codeSymbolic t s).vectors left.2 + (codeSymbolic t s).vectors right.2 -
        (codeSymbolic t s).vectors m := by
  have hm' (i : ℕ) : m ≠ s.next + i := by omega
  have hlm' (i : ℕ) : left.2 ≠ s.next + i := by omega
  have hrm' (i : ℕ) : right.2 ≠ s.next + i := by omega
  dsimp only [join, state_bind_apply, emit_apply, state_pure_apply]
  simp only [codeSymbolic, codeInstructions] at hnext ⊢
  simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil, InstructionTemplate.instantiate, Coefficient.eval]
  simp [symbolicPerform, symbolicStore, hnext, Function.update_apply,
    hm', hlm', hrm', Nat.add_assoc, show m ≠ s.next by omega, show left.2 ≠ s.next by omega,
    show right.2 ≠ s.next by omega]
  constructor <;> module

def OwnedValid (workers : ℕ) (t : Tuning) (s : CodeState) (value : OwnedState) : Prop :=
  value.worker < workers ∧ value.point ∈ (codeLayout t s).points value.worker ∧
    value.momentum ∈ (codeLayout t s).vectors value.worker

lemma OwnedValid.retains (workers : ℕ) (t : Tuning) (s s' : CodeState)
    (value : OwnedState) (h : OwnedValid workers t s value) (hr : Retains t s s') :
    OwnedValid workers t s' value :=
  ⟨h.1, (hr value.worker).1 h.2.1, (hr value.worker).2 h.2.2⟩

lemma graphNodeCode_valid (workers H round : ℕ) (t : Tuning) (ht : t.Valid)
    (node : GraphNode) (state : GraphState) (s : CodeState)
    (hs : CodeValid workers t s) (hw : node.worker < workers)
    (howned : ∀ i, OwnedValid workers t s (state.states i)) :
    let z := graphNodeCode H round node state s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧ OwnedValid workers t z.2 z.1 := by
  cases node with
  | query worker source =>
      let root := state.states source
      let s1 := (sendState root.worker worker root.point root.momentum s).2
      have hroot := howned source
      have h1 := sendState_valid workers t root.worker worker root.point root.momentum
        s hs hroot.1 hw hroot.2.1 hroot.2.2
      have h2 := atom_valid workers t ht H round state.atoms worker root.point root.momentum
        s1 h1.1 hw h1.2.2.1 h1.2.2.2
      exact ⟨h2.1, retains_trans t s s1 _ h1.2.1 h2.2.1, hw, h2.2.2⟩
  | merge worker left right common =>
      let l := state.states left
      let r := state.states right
      let base := state.states common
      let s1 := (sendState l.worker worker l.point l.momentum s).2
      let s2 := (sendState r.worker worker r.point r.momentum s1).2
      let s3 := (sendState base.worker worker base.point base.momentum s2).2
      have hl := howned left
      have hr := howned right
      have hb := howned common
      have h1 := sendState_valid workers t l.worker worker l.point l.momentum s hs hl.1 hw hl.2.1 hl.2.2
      have hr1 := OwnedValid.retains workers t s s1 r hr h1.2.1
      have h2 := sendState_valid workers t r.worker worker r.point r.momentum s1
        h1.1 hr1.1 hw hr1.2.1 hr1.2.2
      have ret2 := retains_trans t s s1 s2 h1.2.1 h2.2.1
      have hb2 := OwnedValid.retains workers t s s2 base hb ret2
      have h3 := sendState_valid workers t base.worker worker base.point base.momentum s2
        h2.1 hb2.1 hw hb2.2.1 hb2.2.2
      have ret13 := retains_trans t s1 s2 s3 h2.2.1 h3.2.1
      have ret3 := retains_trans t s s2 s3 ret2 h3.2.1
      have hj := join_valid workers t worker base.point base.momentum
        (l.point, l.momentum) (r.point, r.momentum) s3 h3.1 hw h3.2.2.1 h3.2.2.2
        ((ret13 worker).1 h1.2.2.1) ((ret13 worker).2 h1.2.2.2)
        ((h3.2.1 worker).1 h2.2.2.1) ((h3.2.1 worker).2 h2.2.2.2)
      exact ⟨hj.1, retains_trans t s s3 _ ret3 hj.2.1, hw, hj.2.2⟩

lemma graphStep_valid (workers H round : ℕ) (t : Tuning) (ht : t.Valid)
    (node : GraphNode) (state : GraphState) (s : CodeState)
    (hs : CodeValid workers t s) (hw : node.worker < workers)
    (howned : ∀ i, OwnedValid workers t s (state.states i)) :
    let z := graphStep H round node state s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      ∀ i, OwnedValid workers t z.2 (z.1.states i) := by
  have h := graphNodeCode_valid workers H round t ht node state s hs hw howned
  refine ⟨h.1, h.2.1, ?_⟩
  intro i
  dsimp only [graphStep, state_bind_apply, state_pure_apply]
  by_cases hi : i = state.next
  · subst i
    rw [Function.update_self]
    exact h.2.2
  · rw [Function.update_of_ne hi]
    exact OwnedValid.retains workers t s _ (state.states i) (howned i) h.2.1

lemma graphCode_valid (workers H round output : ℕ) (t : Tuning) (ht : t.Valid)
    (nodes : List GraphNode) (hnodes : ∀ node ∈ nodes, node.worker < workers) :
    PacketValid workers t (graphCode H round nodes output) := by
  intro w x m s hs hw hx hm
  let initial : GraphState := ⟨fun _ => ⟨w, x, m⟩, 1, 0⟩
  let Inv := fun (state : GraphState) (s' : CodeState) =>
    CodeValid workers t s' ∧ Retains t s s' ∧
      ∀ i, OwnedValid workers t s' (state.states i)
  have hloop := state_forIn_invariant (graphStep H round) nodes Inv
    (fun node hnode state s' h => by
      have hh := graphStep_valid workers H round t ht node state s' h.1 (hnodes node hnode) h.2.2
      exact ⟨hh.1, retains_trans t s s' _ h.2.1 hh.2.1, hh.2.2⟩)
    initial s ⟨hs, retains_refl t s, fun _ => ⟨hw, hx, hm⟩⟩
  let z := (forIn nodes initial (fun node state => ForInStep.yield <$> graphStep H round node state) :
    StateM CodeState GraphState) s
  have hz : Inv z.1 z.2 := hloop
  let result := z.1.states output
  have ho := hz.2.2 output
  have hsend := sendState_valid workers t result.worker w result.point result.momentum
    z.2 hz.1 ho.1 hw ho.2.1 ho.2.2
  exact ⟨hsend.1, retains_trans t s z.2 _ hz.2.1 hsend.2.1, hsend.2.2⟩

lemma atom_extends (H round index worker x m : ℕ) : BuildExtends (atom H round index worker x m) :=
  momentumStep_extends worker H round index (x, m)

lemma sendState_extends (sender receiver x m : ℕ) : BuildExtends (sendState sender receiver x m) := by
  unfold sendState
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

lemma join_extends (w x m : ℕ) (left right : ℕ × ℕ) : BuildExtends (join w x m left right) := by
  unfold join
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

lemma graphNodeCode_extends (H round : ℕ) (node : GraphNode) (state : GraphState) :
    BuildExtends (graphNodeCode H round node state) := by
  cases node with
  | query worker source =>
      unfold graphNodeCode
      apply buildExtends_bind _ _ (sendState_extends _ _ _ _)
      intro _
      apply buildExtends_bind _ _ (atom_extends _ _ _ _ _ _)
      intro _
      exact buildExtends_pure _
  | merge worker left right common =>
      unfold graphNodeCode
      apply buildExtends_bind _ _ (sendState_extends _ _ _ _)
      intro _
      apply buildExtends_bind _ _ (sendState_extends _ _ _ _)
      intro _
      apply buildExtends_bind _ _ (sendState_extends _ _ _ _)
      intro _
      apply buildExtends_bind _ _ (join_extends _ _ _ _ _)
      intro _
      exact buildExtends_pure _

lemma graphStep_extends (H round : ℕ) (node : GraphNode) (state : GraphState) :
    BuildExtends (graphStep H round node state) := by
  unfold graphStep
  apply buildExtends_bind _ _ (graphNodeCode_extends _ _ _ _)
  intro _
  exact buildExtends_pure _

lemma sendState_symbolic (t : Tuning) (sender receiver x m : ℕ) (s : CodeState) :
    codeSymbolic t (sendState sender receiver x m s).2 =
      { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
  simp only [sendState, state_bind_apply, state_pure_apply, codeSymbolic_emit,
    InstructionTemplate.instantiate, symbolicPerform]

lemma sendState_next (sender receiver x m : ℕ) (s : CodeState) :
    (sendState sender receiver x m s).2.next = s.next + 2 := by
  simp only [sendState, state_bind_apply, state_pure_apply, emit_apply]

lemma graphQuery_symbolic (H round worker source : ℕ) (state : GraphState) (s : CodeState)
    (t : Tuning) (hn : s.next = (codeSymbolic t s).next)
    (hm : (state.states source).momentum < s.next) :
    let z := graphNodeCode H round (.query worker source) state s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    let α := t.momentum (round * H + state.atoms)
    let v := α • (Finsupp.single (s.next + 2) 1, 0) +
      (1 - α) • old.vectors (state.states source).momentum
    new.vectors z.1.momentum = v ∧
      new.points z.1.point = old.points (state.states source).point +
        (1 / (H : ℝ) * t.step round) • (0, Finsupp.single (s.next + 4) 1) ∧
      new.queryPoints (s.next + 2) = old.points (state.states source).point ∧
      new.sharpInputs (s.next + 4) = v ∧
      new.queries = insert (s.next + 2) old.queries ∧
      new.sharps = insert (s.next + 4) old.sharps ∧ new.units = old.units := by
  let root := state.states source
  let s1 := (sendState root.worker worker root.point root.momentum s).2
  have hn1 : s1.next = (codeSymbolic t s1).next := by
    rw [sendState_next, sendState_symbolic, hn]
  have hm1 : root.momentum < s1.next := by
    simp only [s1, sendState_next, root]
    omega
  have h := momentumStep_symbolic worker H round state.atoms (root.point, root.momentum)
    s1 t hn1 hm1
  simpa only [s1, sendState_next, sendState_symbolic, Nat.add_assoc, Nat.reduceAdd,
    root, graphNodeCode, state_bind_apply, state_pure_apply, atom, momentumStep] using h

lemma graphMerge_symbolic (H round worker left right common : ℕ) (state : GraphState)
    (s : CodeState) (t : Tuning) (hn : s.next = (codeSymbolic t s).next)
    (hl : (state.states left).momentum < s.next)
    (hr : (state.states right).momentum < s.next)
    (hc : (state.states common).momentum < s.next) :
    let z := graphNodeCode H round (.merge worker left right common) state s
    (codeSymbolic t z.2).points z.1.point =
      (codeSymbolic t s).points (state.states left).point +
        (codeSymbolic t s).points (state.states right).point -
          (codeSymbolic t s).points (state.states common).point ∧
    (codeSymbolic t z.2).vectors z.1.momentum =
      (codeSymbolic t s).vectors (state.states left).momentum +
        (codeSymbolic t s).vectors (state.states right).momentum -
          (codeSymbolic t s).vectors (state.states common).momentum := by
  let l := state.states left
  let r := state.states right
  let base := state.states common
  let s1 := (sendState l.worker worker l.point l.momentum s).2
  let s2 := (sendState r.worker worker r.point r.momentum s1).2
  let s3 := (sendState base.worker worker base.point base.momentum s2).2
  have hn3 : (codeSymbolic t s3).next = s3.next := by
    simp only [s3, s2, s1, sendState_next, sendState_symbolic, hn]
  have hlo : l.momentum < s3.next := by
    simp only [s3, s2, s1, sendState_next, l, r, base]
    omega
  have hro : r.momentum < s3.next := by
    simp only [s3, s2, s1, sendState_next, l, r, base]
    omega
  have hco : base.momentum < s3.next := by
    simp only [s3, s2, s1, sendState_next, l, r, base]
    omega
  have h := join_symbolic t worker base.point base.momentum
    (l.point, l.momentum) (r.point, r.momentum) s3 hn3 hco hlo hro
  simpa only [s3, s2, s1, sendState_symbolic, l, r, base, graphNodeCode,
    state_bind_apply, state_pure_apply] using h

def nodeLength : GraphNode → ℕ
  | .query _ _ => 6
  | .merge _ _ _ _ => 11

lemma graphNodeCode_next (H round : ℕ) (node : GraphNode) (state : GraphState) (s : CodeState) :
    (graphNodeCode H round node state s).2.next = s.next + nodeLength node := by
  cases node <;> simp only [graphNodeCode, sendState, atom, join, state_bind_apply,
    state_pure_apply, emit_apply, nodeLength, Nat.add_assoc, Nat.reduceAdd]

lemma graphStep_meta (H round : ℕ) (node : GraphNode) (state : GraphState) (s : CodeState) :
    (graphStep H round node state s).1.next = state.next + 1 ∧
      (graphStep H round node state s).1.atoms = state.atoms + node.calls ∧
        (graphStep H round node state s).2.next = s.next + nodeLength node := by
  refine ⟨rfl, ?_, graphNodeCode_next H round node state s⟩
  cases node <;> rfl

lemma graphQuery_registers (H round worker source : ℕ) (state : GraphState) (s : CodeState) :
    (graphNodeCode H round (.query worker source) state s).1 =
      ⟨worker, s.next + 5, s.next + 3⟩ := by
  simp only [graphNodeCode, sendState, atom, state_bind_apply, state_pure_apply, emit_apply, Nat.add_assoc, Nat.reduceAdd]

lemma graphMerge_registers (H round worker left right common : ℕ) (state : GraphState) (s : CodeState) :
    (graphNodeCode H round (.merge worker left right common) state s).1 =
      ⟨worker, s.next + 9, s.next + 10⟩ := by
  simp only [graphNodeCode, sendState, join, state_bind_apply, state_pure_apply, emit_apply, Nat.add_assoc, Nat.reduceAdd]

end LongTails.Proofs.BirchCausalConstruction
