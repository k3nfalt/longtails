import LongTails.Proofs.BirchCausalMerges

namespace LongTails.Proofs.BirchCausalControllers

open Finset
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchCausalMerges

lemma historyStep_next (node : GraphNode) (state : HistoryState) :
    (historyStep node state).next = state.next + 1 := by
  cases node <;> rfl

lemma historyFold_next (nodes : List GraphNode) (state : HistoryState) :
    (nodes.foldl (flip historyStep) state).next = state.next + nodes.length := by
  induction nodes generalizing state with
  | nil => simp
  | cons node rest ih =>
      rw [List.foldl_cons, ih]
      dsimp only [flip]
      rw [historyStep_next]
      simp only [List.length_cons]
      omega

lemma historyStep_old (node : GraphNode) (state : HistoryState) (i : ℕ) (hi : i < state.next) :
    (historyStep node state).states i = state.states i := by
  cases node <;> simp [historyStep, ne_of_lt hi]

lemma historyFold_old (nodes : List GraphNode) (state : HistoryState) (i : ℕ) (hi : i < state.next) :
    (nodes.foldl (flip historyStep) state).states i = state.states i := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      rw [List.foldl_cons]
      dsimp only [flip]
      rw [ih (historyStep node state) (by rw [historyStep_next]; omega), historyStep_old node state i hi]

lemma graphValid_append (workers : ℕ) (state : HistoryState) (left right : List GraphNode) :
    GraphValidFrom workers state (left ++ right) ↔ GraphValidFrom workers state left ∧
      GraphValidFrom workers (left.foldl (flip historyStep) state) right := by
  induction left generalizing state with
  | nil => simp [GraphValidFrom]
  | cons node rest ih => simp [GraphValidFrom, ih, and_assoc, flip]

lemma compile_calls (expr : PacketExpr) (root next : ℕ) :
    ((expr.compile root next).nodes.map GraphNode.calls).sum = expr.calls := by
  induction expr generalizing root next with
  | atom worker => rfl
  | sequence left right ihl ihr => simp only [PacketExpr.compile, List.map_append, List.sum_append,
      ihl, ihr, PacketExpr.calls]
  | fork owner left right ihl ihr => simp [PacketExpr.compile, PacketExpr.calls, ihl, ihr, GraphNode.calls]
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      simp [PacketExpr.compile, PacketExpr.calls, ihl, ihr, iha, ihb, GraphNode.calls, Nat.add_assoc]

lemma compile_next (expr : PacketExpr) (root next : ℕ) :
    (expr.compile root next).next = next + (expr.compile root next).nodes.length := by
  induction expr generalizing root next with
  | atom worker => rfl
  | sequence left right ihl ihr =>
      simp only [PacketExpr.compile, List.length_append]
      rw [ihr, ihl]
      omega
  | fork owner left right ihl ihr =>
      simp only [PacketExpr.compile, List.length_append, List.length_singleton]
      rw [ihr, ihl]
      omega
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      simp only [PacketExpr.compile, List.length_append, List.length_singleton]
      rw [ihb, iha, ihr, ihl]
      omega

lemma compile_next_le (expr : PacketExpr) (root next : ℕ) :
    next ≤ (expr.compile root next).next := by
  rw [compile_next]
  omega

lemma compile_output_lt (expr : PacketExpr) (root next : ℕ) :
    (expr.compile root next).output < (expr.compile root next).next := by
  induction expr generalizing root next with
  | atom worker => exact Nat.lt_succ_self _
  | sequence left right ihl ihr => exact ihr _ _
  | fork owner left right ihl ihr => exact Nat.lt_succ_self _
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb => exact Nat.lt_succ_self _

lemma compile_workers (workers : ℕ) (expr : PacketExpr) (hv : expr.Valid workers) (root next : ℕ) :
    ∀ node ∈ (expr.compile root next).nodes, node.worker < workers := by
  induction expr generalizing root next with
  | atom worker => simpa [PacketExpr.compile, PacketExpr.Valid, GraphNode.worker] using hv
  | sequence left right ihl ihr =>
      intro node hn
      simp only [PacketExpr.compile, List.mem_append] at hn
      rcases hn with hn | hn
      · exact ihl hv.1 _ _ node hn
      · exact ihr hv.2 _ _ node hn
  | fork owner left right ihl ihr =>
      intro node hn
      simp only [PacketExpr.compile, List.mem_append, List.mem_singleton] at hn
      rcases hn with (hn | hn) | rfl
      · exact ihl hv.2.1 _ _ node hn
      · exact ihr hv.2.2 _ _ node hn
      · exact hv.1
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      intro node hn
      simp only [PacketExpr.compile, List.mem_append, List.mem_singleton] at hn
      rcases hn with ((((hn | hn) | rfl) | hn) | hn) | rfl
      · exact ihl hv.2.1 _ _ node hn
      · exact ihr hv.2.2.1 _ _ node hn
      · exact hv.1
      · exact iha hv.2.2.2.1 _ _ node hn
      · exact ihb hv.2.2.2.2 _ _ node hn
      · exact hv.1

lemma interval_attach (base : Finset ℕ) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    (base ∪ Ico a b) ∪ Ico b c = base ∪ Ico a c := by
  ext i
  simp only [mem_union, mem_Ico]
  constructor
  · intro h
    rcases h with (hi | hi) | hi
    · exact Or.inl hi
    · exact Or.inr ⟨hi.1, hi.2.trans_le hbc⟩
    · exact Or.inr ⟨hab.trans hi.1, hi.2⟩
  · intro h
    rcases h with hi | hi
    · exact Or.inl (Or.inl hi)
    · by_cases hib : i < b
      · exact Or.inl (Or.inr ⟨hi.1, hib⟩)
      · exact Or.inr ⟨by omega, hi.2⟩

lemma interval_meet (base : Finset ℕ) (a b c : ℕ) :
    (base ∪ Ico a b) ∩ (base ∪ Ico b c) = base := by
  ext i
  simp only [mem_inter, mem_union, mem_Ico]
  constructor
  · intro h
    rcases h.1 with hi | hi
    · exact hi
    · rcases h.2 with hj | hj
      · exact hj
      · omega
  · intro hi
    exact ⟨Or.inl hi, Or.inl hi⟩

lemma union_reuse (base left right : Finset ℕ) :
    (base ∪ left) ∪ (base ∪ right) = (base ∪ left) ∪ right := by
  ext i
  simp only [mem_union]
  tauto

structure BlockMeaning (workers : ℕ) (state : HistoryState) (root : ℕ)
    (block : GraphBlock) (calls : ℕ) : Prop where
  valid : GraphValidFrom workers state block.nodes
  next : (block.nodes.foldl (flip historyStep) state).next = block.next
  atoms : (block.nodes.foldl (flip historyStep) state).atoms = state.atoms + calls
  output_lt : block.output < block.next
  output : (block.nodes.foldl (flip historyStep) state).states block.output =
    state.states root ∪ Ico state.atoms (state.atoms + calls)

lemma BlockMeaning.next_le {workers root calls : ℕ} {state : HistoryState} {block : GraphBlock}
    (h : BlockMeaning workers state root block calls) : state.next ≤ block.next := by
  rw [← h.next, historyFold_next]
  omega

lemma block_atom (workers worker root : ℕ) (state : HistoryState)
    (hw : worker < workers) (hr : root < state.next) :
    BlockMeaning workers state root ⟨[.query worker root], state.next, state.next + 1⟩ 1 := by
  refine ⟨⟨⟨hw, hr⟩, trivial⟩, rfl, rfl, Nat.lt_succ_self _, ?_⟩
  simp only [List.foldl_cons, List.foldl_nil, flip, historyStep, Function.update_self]
  simp

lemma block_sequence (workers root a b : ℕ) (state : HistoryState) (left right : GraphBlock)
    (hl : BlockMeaning workers state root left a)
    (hr : BlockMeaning workers (left.nodes.foldl (flip historyStep) state) left.output right b) :
    BlockMeaning workers state root ⟨left.nodes ++ right.nodes, right.output, right.next⟩ (a + b) := by
  refine ⟨(graphValid_append workers state left.nodes right.nodes).2 ⟨hl.valid, hr.valid⟩,
    ?_, ?_, hr.output_lt, ?_⟩
  · simpa only [List.foldl_append] using hr.next
  · simpa only [List.foldl_append, hl.atoms, Nat.add_assoc] using hr.atoms
  · simp only [List.foldl_append]
    rw [hr.output, hl.output, hl.atoms]
    rw [interval_attach _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _)]
    rw [Nat.add_assoc]

lemma block_fork (workers owner root a b : ℕ) (state : HistoryState) (left right : GraphBlock)
    (hw : owner < workers) (hroot : root < state.next)
    (hl : BlockMeaning workers state root left a)
    (hr : BlockMeaning workers (left.nodes.foldl (flip historyStep) state) root right b) :
    BlockMeaning workers state root
      ⟨left.nodes ++ right.nodes ++ [GraphNode.merge owner left.output right.output root], right.next, right.next + 1⟩
      (a + b) := by
  let first := left.nodes.foldl (flip historyStep) state
  let second := right.nodes.foldl (flip historyStep) first
  have hroot1 : root < first.next := by rw [hl.next]; exact hroot.trans_le hl.next_le
  have hroot2 : root < second.next := by rw [hr.next]; exact hroot1.trans_le hr.next_le
  have hleft : second.states left.output = state.states root ∪ Ico state.atoms (state.atoms + a) := by
    rw [historyFold_old right.nodes first left.output (by rw [hl.next]; exact hl.output_lt), hl.output]
  have hbase : first.states root = state.states root := historyFold_old left.nodes state root hroot
  have hcommon : second.states root = state.states root :=
    (historyFold_old right.nodes first root hroot1).trans hbase
  have hright : second.states right.output = state.states root ∪
      Ico (state.atoms + a) (state.atoms + a + b) := by
    rw [hr.output, hbase, hl.atoms]
  have hmeet : second.states root = second.states left.output ∩ second.states right.output := by
    rw [hcommon, hleft, hright, interval_meet]
  have hmerge : (GraphNode.merge owner left.output right.output root).Valid workers second :=
    ⟨hw, by rw [hr.next]; exact hl.output_lt.trans_le (by simpa only [hl.next] using hr.next_le),
      by rw [hr.next]; exact hr.output_lt, hroot2, hmeet⟩
  refine ⟨?_, ?_, ?_, Nat.lt_succ_self _, ?_⟩
  · rw [graphValid_append, graphValid_append]
    exact ⟨⟨hl.valid, hr.valid⟩, by simpa only [List.foldl_append] using hmerge, trivial⟩
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, flip,
      historyStep_next, hr.next]
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, flip,
      historyStep, hr.atoms, hl.atoms, Nat.add_assoc]
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, flip]
    change (historyStep (.merge owner left.output right.output root) second).states right.next = _
    have hn2 : second.next = right.next := hr.next
    simp only [historyStep, hn2, Function.update_self]
    rw [hleft, hright, union_reuse, interval_attach _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _), Nat.add_assoc]

lemma overlap_meet (base : Finset ℕ) (a b c d e : ℕ) (hab : a ≤ b) (hcd : c ≤ d) :
    (base ∪ Ico a d) ∩ ((base ∪ Ico b c) ∪ Ico d e) = base ∪ Ico b c := by
  ext i
  simp only [mem_inter, mem_union, mem_Ico]
  constructor
  · intro h
    rcases h.1 with hi | hi
    · exact Or.inl hi
    · rcases h.2 with hj | hj
      · exact hj
      · exact (not_lt_of_ge hj.1 hi.2).elim
  · intro h
    refine ⟨?_, Or.inl h⟩
    rcases h with hi | hi
    · exact Or.inl hi
    · exact Or.inr ⟨hab.trans hi.1, hi.2.trans_le hcd⟩

lemma overlap_union (base : Finset ℕ) (a b c d e : ℕ)
    (hab : a ≤ b) (hcd : c ≤ d) (hde : d ≤ e) (had : a ≤ d) :
    (base ∪ Ico a d) ∪ ((base ∪ Ico b c) ∪ Ico d e) = base ∪ Ico a e := by
  have hsub : base ∪ Ico b c ⊆ base ∪ Ico a d := by
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact mem_union_left _ hi
    · have h := mem_Ico.mp hi
      exact mem_union_right _ (mem_Ico.mpr ⟨hab.trans h.1, h.2.trans_le hcd⟩)
  rw [← union_assoc, union_eq_left.mpr hsub, interval_attach base a d e had hde]

lemma block_finish (workers owner root calls next left right common : ℕ)
    (state : HistoryState) (nodes : List GraphNode)
    (hv : GraphValidFrom workers state nodes)
    (hn : (nodes.foldl (flip historyStep) state).next = next)
    (ha : (nodes.foldl (flip historyStep) state).atoms = state.atoms + calls)
    (hw : owner < workers) (hl : left < next) (hr : right < next) (hc : common < next)
    (hm : (nodes.foldl (flip historyStep) state).states common =
      (nodes.foldl (flip historyStep) state).states left ∩
        (nodes.foldl (flip historyStep) state).states right)
    (hu : (nodes.foldl (flip historyStep) state).states left ∪
      (nodes.foldl (flip historyStep) state).states right =
        state.states root ∪ Ico state.atoms (state.atoms + calls)) :
    BlockMeaning workers state root
      ⟨nodes ++ [GraphNode.merge owner left right common], next, next + 1⟩ calls := by
  refine ⟨?_, ?_, ?_, Nat.lt_succ_self _, ?_⟩
  · rw [graphValid_append]
    exact ⟨hv, ⟨hw, by rwa [hn], by rwa [hn], by rwa [hn], hm⟩, trivial⟩
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, flip, historyStep_next, hn]
  · simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, flip, historyStep] using ha
  · simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, flip, historyStep, hn,
      Function.update_self] using hu

lemma block_overlap (workers owner root a b c d : ℕ) (state : HistoryState)
    (left right afterBoth afterRight : GraphBlock)
    (hw : owner < workers) (hroot : root < state.next)
    (hl : BlockMeaning workers state root left a)
    (hr : BlockMeaning workers (left.nodes.foldl (flip historyStep) state) root right b)
    (ha : BlockMeaning workers
      ((left.nodes ++ right.nodes ++ [GraphNode.merge owner left.output right.output root]).foldl
        (flip historyStep) state) right.next afterBoth c)
    (hb : BlockMeaning workers
      ((left.nodes ++ right.nodes ++ [GraphNode.merge owner left.output right.output root] ++ afterBoth.nodes).foldl
        (flip historyStep) state) right.output afterRight d) :
    BlockMeaning workers state root
      ⟨left.nodes ++ right.nodes ++ [GraphNode.merge owner left.output right.output root] ++
        afterBoth.nodes ++ afterRight.nodes ++ [GraphNode.merge owner afterBoth.output afterRight.output right.output],
        afterRight.next, afterRight.next + 1⟩ (a + b + c + d) := by
  let forked : GraphBlock :=
    ⟨left.nodes ++ right.nodes ++ [GraphNode.merge owner left.output right.output root], right.next, right.next + 1⟩
  let prefixBlock : GraphBlock := ⟨forked.nodes ++ afterBoth.nodes, afterBoth.output, afterBoth.next⟩
  let f := forked.nodes.foldl (flip historyStep) state
  let p := prefixBlock.nodes.foldl (flip historyStep) state
  let q := afterRight.nodes.foldl (flip historyStep) p
  have hf : BlockMeaning workers state root forked (a + b) :=
    block_fork workers owner root a b state left right hw hroot hl hr
  have hp : BlockMeaning workers state root prefixBlock (a + b + c) :=
    block_sequence workers root (a + b) c state forked afterBoth hf ha
  have hfnext : f.next = right.next + 1 := hf.next
  have hpnext : p.next = afterBoth.next := hp.next
  have hqnext : q.next = afterRight.next := hb.next
  have hrightf : right.output < f.next := by rw [hfnext]; exact hr.output_lt.trans_le (Nat.le_succ _)
  have hrightp : right.output < p.next := by
    rw [hpnext]
    exact hrightf.trans_le ha.next_le
  have hrightq : right.output < q.next := by rw [hqnext]; exact hrightp.trans_le hb.next_le
  have hrf : f.states right.output = state.states root ∪
      Ico (state.atoms + a) (state.atoms + (a + b)) := by
    have hlt : right.output < (right.nodes.foldl (flip historyStep)
        (left.nodes.foldl (flip historyStep) state)).next := by rw [hr.next]; exact hr.output_lt
    dsimp only [f, forked]
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, flip]
    rw [historyStep_old _ _ _ (by simpa only [List.foldl_append] using hlt)]
    rw [List.foldl_append, hr.output, historyFold_old left.nodes state root hroot, hl.atoms,
      Nat.add_assoc]
  have hrp : p.states right.output = state.states root ∪
      Ico (state.atoms + a) (state.atoms + (a + b)) := by
    change ((forked.nodes ++ afterBoth.nodes).foldl (flip historyStep) state).states _ = _
    rw [List.foldl_append, historyFold_old afterBoth.nodes f right.output hrightf, hrf]
  have hrq : q.states right.output = state.states root ∪
      Ico (state.atoms + a) (state.atoms + (a + b)) :=
    (historyFold_old afterRight.nodes p right.output hrightp).trans hrp
  have hap : afterBoth.output < p.next := by rw [hpnext]; exact ha.output_lt
  have haq : afterBoth.output < q.next := by rw [hqnext]; exact hap.trans_le hb.next_le
  have haqstate : q.states afterBoth.output = state.states root ∪
      Ico state.atoms (state.atoms + (a + b + c)) := by
    rw [historyFold_old afterRight.nodes p afterBoth.output hap]
    exact hp.output
  have hbqstate : q.states afterRight.output =
      (state.states root ∪ Ico (state.atoms + a) (state.atoms + (a + b))) ∪
        Ico (state.atoms + (a + b + c)) (state.atoms + (a + b + c) + d) := by
    rw [hb.output, hrp, hp.atoms]
  apply block_finish workers owner root (a + b + c + d) afterRight.next afterBoth.output
    afterRight.output right.output state (prefixBlock.nodes ++ afterRight.nodes)
  · exact (graphValid_append workers state prefixBlock.nodes afterRight.nodes).2 ⟨hp.valid, hb.valid⟩
  · simpa only [List.foldl_append] using hqnext
  · rw [List.foldl_append]
    change q.atoms = _
    have hqa : q.atoms = p.atoms + d := hb.atoms
    have hpa : p.atoms = state.atoms + (a + b + c) := hp.atoms
    rw [hqa, hpa, Nat.add_assoc]
  · exact hw
  · rwa [hqnext] at haq
  · exact hb.output_lt
  · rwa [hqnext] at hrightq
  · rw [List.foldl_append]
    change q.states right.output = q.states afterBoth.output ∩ q.states afterRight.output
    rw [hrq, haqstate, hbqstate, overlap_meet _ _ _ _ _ _ (by omega) (by omega)]
  · rw [List.foldl_append]
    change q.states afterBoth.output ∪ q.states afterRight.output = _
    rw [haqstate, hbqstate, overlap_union _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    rw [Nat.add_assoc]

lemma compile_meaning (workers : ℕ) (expr : PacketExpr) (hv : expr.Valid workers)
    (state : HistoryState) (root : ℕ) (hroot : root < state.next) :
    BlockMeaning workers state root (expr.compile root state.next) expr.calls := by
  induction expr generalizing state root with
  | atom worker => exact block_atom workers worker root state hv hroot
  | sequence left right ihl ihr =>
      let l := left.compile root state.next
      let first := l.nodes.foldl (flip historyStep) state
      have hl : BlockMeaning workers state root l left.calls := ihl hv.1 state root hroot
      have hr : BlockMeaning workers first l.output (right.compile l.output l.next) right.calls := by
        have hsource : l.output < first.next := by rw [hl.next]; exact hl.output_lt
        have hh := ihr hv.2 first l.output hsource
        have hln : first.next = l.next := hl.next
        simpa only [hln] using hh
      exact block_sequence workers root left.calls right.calls state l _ hl hr
  | fork owner left right ihl ihr =>
      let l := left.compile root state.next
      let first := l.nodes.foldl (flip historyStep) state
      have hl : BlockMeaning workers state root l left.calls := ihl hv.2.1 state root hroot
      have hr : BlockMeaning workers first root (right.compile root l.next) right.calls := by
        have hsource : root < first.next := by rw [hl.next]; exact hroot.trans_le hl.next_le
        have hh := ihr hv.2.2 first root hsource
        have hln : first.next = l.next := hl.next
        simpa only [hln] using hh
      exact block_fork workers owner root left.calls right.calls state l _ hv.1 hroot hl hr
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      let l := left.compile root state.next
      let first := l.nodes.foldl (flip historyStep) state
      let r := right.compile root l.next
      let forked : GraphBlock :=
        ⟨l.nodes ++ r.nodes ++ [GraphNode.merge owner l.output r.output root], r.next, r.next + 1⟩
      let f := forked.nodes.foldl (flip historyStep) state
      let a := afterBoth.compile r.next (r.next + 1)
      let p := (forked.nodes ++ a.nodes).foldl (flip historyStep) state
      have hl : BlockMeaning workers state root l left.calls := ihl hv.2.1 state root hroot
      have hr : BlockMeaning workers first root r right.calls := by
        have hsource : root < first.next := by rw [hl.next]; exact hroot.trans_le hl.next_le
        have hh := ihr hv.2.2.1 first root hsource
        have hln : first.next = l.next := hl.next
        simpa only [hln] using hh
      have hf : BlockMeaning workers state root forked (left.calls + right.calls) :=
        block_fork workers owner root left.calls right.calls state l r hv.1 hroot hl hr
      have hfn : f.next = r.next + 1 := hf.next
      have ha : BlockMeaning workers f r.next a afterBoth.calls := by
        have hh := iha hv.2.2.2.1 f r.next (by rw [hfn]; omega)
        simpa only [hfn] using hh
      have hp := block_sequence workers root (left.calls + right.calls) afterBoth.calls
        state forked a hf ha
      have hpn : p.next = a.next := hp.next
      have hb : BlockMeaning workers p r.output (afterRight.compile r.output a.next) afterRight.calls := by
        have hrf : r.output < f.next := by rw [hfn]; exact hr.output_lt.trans_le (Nat.le_succ _)
        have hrp : r.output < p.next := by rw [hpn]; exact hrf.trans_le ha.next_le
        have hh := ihb hv.2.2.2.2 p r.output hrp
        simpa only [hpn] using hh
      exact block_overlap workers owner root left.calls right.calls afterBoth.calls afterRight.calls
        state l r a _ hv.1 hroot hl hr ha hb

lemma calls_positive (expr : PacketExpr) : 0 < expr.calls := by
  induction expr with
  | atom worker => exact Nat.zero_lt_one
  | sequence left right ihl ihr => exact Nat.add_pos_left ihl _
  | fork owner left right ihl ihr => exact Nat.add_pos_left ihl _
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      exact Nat.add_pos_left (Nat.add_pos_left (Nat.add_pos_left ihl _) _) _

lemma joins_bound (expr : PacketExpr) : expr.joins + 1 ≤ expr.calls := by
  induction expr with
  | atom worker => rfl
  | sequence left right ihl ihr => dsimp [PacketExpr.joins, PacketExpr.calls]; omega
  | fork owner left right ihl ihr => dsimp [PacketExpr.joins, PacketExpr.calls]; omega
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      dsimp [PacketExpr.joins, PacketExpr.calls]; omega

lemma compile_length (expr : PacketExpr) (root next : ℕ) :
    (expr.compile root next).nodes.length = expr.calls + expr.joins := by
  induction expr generalizing root next with
  | atom worker => rfl
  | sequence left right ihl ihr =>
      simp only [PacketExpr.compile, List.length_append, ihl, ihr, PacketExpr.calls, PacketExpr.joins]
      omega
  | fork owner left right ihl ihr =>
      simp only [PacketExpr.compile, List.length_append, List.length_singleton,
        ihl, ihr, PacketExpr.calls, PacketExpr.joins]
      omega
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      simp only [PacketExpr.compile, List.length_append, List.length_singleton,
        ihl, ihr, iha, ihb, PacketExpr.calls, PacketExpr.joins]
      omega

lemma nestedComb_counts (queryWorker mergeWorker : ℕ → ℕ) (depth : ℕ) :
    (nestedComb queryWorker mergeWorker depth).calls = 3 * depth + 1 ∧
      (nestedComb queryWorker mergeWorker depth).joins = 2 * depth := by
  induction depth with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth ih =>
      simp only [nestedComb, PacketExpr.calls, PacketExpr.joins, ih.1, ih.2]
      constructor <;> omega

lemma nestedBalanced_calls (queryWorker mergeWorker : ℕ → ℕ) (depth : ℕ) :
    (nestedBalanced queryWorker mergeWorker depth).calls = 4 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [nestedBalanced, PacketExpr.calls, ih, pow_succ]
      omega

lemma nestedComb_valid (workers : ℕ) (queryWorker mergeWorker : ℕ → ℕ) (depth : ℕ)
    (hq : ∀ i < 3 * depth + 1, queryWorker i < workers)
    (hm : ∀ i < depth, mergeWorker i < workers) :
    (nestedComb queryWorker mergeWorker depth).Valid workers := by
  induction depth with
  | zero => exact hq 0 (by omega)
  | succ depth ih =>
      exact ⟨hm depth (by omega), ih (fun i hi => hq i (by omega))
        (fun i hi => hm i (by omega)), hq _ (by omega), hq _ (by omega), hq _ (by omega)⟩

lemma compiled_calls (H round output worker x m : ℕ) (expr : PacketExpr)
    (root next : ℕ) (s : LongTails.Algorithms.BirchNonEuclideanFamilies.CodeState) :
    LongTails.Proofs.BirchNonEuclideanFamilies.codeCalls
      (graphCode H round (expr.compile root next).nodes output worker x m s).2 =
        LongTails.Proofs.BirchNonEuclideanFamilies.codeCalls s + expr.calls := by
  rw [graphCode_calls, compile_calls]

lemma historyStep_old_queries (node : GraphNode) (state : HistoryState) (i : ℕ)
    (hi : i < state.atoms) :
    (historyStep node state).queryHistory i = state.queryHistory i := by
  cases node <;> simp [historyStep, ne_of_lt hi]

lemma historyFold_old_queries (nodes : List GraphNode) (state : HistoryState) (i : ℕ)
    (hi : i < state.atoms) :
    (nodes.foldl (flip historyStep) state).queryHistory i = state.queryHistory i := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      rw [List.foldl_cons]
      dsimp only [flip]
      rw [ih (historyStep node state) (by rw [historyStep_atoms]; omega),
        historyStep_old_queries node state i hi]

def RootedQueries (base : Finset ℕ) (state : HistoryState) (nodes : List GraphNode) : Prop :=
  ∀ i, state.atoms ≤ i → i < (nodes.foldl (flip historyStep) state).atoms →
    base ⊆ (nodes.foldl (flip historyStep) state).queryHistory i

lemma rootedQueries_mono (base larger : Finset ℕ) (state : HistoryState) (nodes : List GraphNode)
    (hbase : base ⊆ larger) (h : RootedQueries larger state nodes) : RootedQueries base state nodes :=
  fun i hi hj => hbase.trans (h i hi hj)

lemma rootedQueries_query (state : HistoryState) (worker source : ℕ) :
    RootedQueries (state.states source) state [.query worker source] := by
  intro i hi hj
  change i < state.atoms + 1 at hj
  have he : i = state.atoms := by omega
  subst i
  simp only [List.foldl_cons, List.foldl_nil, flip, historyStep, Function.update_self]
  exact Subset.rfl

lemma rootedQueries_merge (base : Finset ℕ) (state : HistoryState) (owner left right common : ℕ) :
    RootedQueries base state [.merge owner left right common] := by
  intro i hi hj
  change i < state.atoms at hj
  omega

lemma rootedQueries_append (base : Finset ℕ) (state : HistoryState) (left right : List GraphNode)
    (hl : RootedQueries base state left)
    (hr : RootedQueries base (left.foldl (flip historyStep) state) right) :
    RootedQueries base state (left ++ right) := by
  intro i hi hj
  rw [List.foldl_append] at hj ⊢
  by_cases hm : i < (left.foldl (flip historyStep) state).atoms
  · rw [historyFold_old_queries right _ i hm]
    exact hl i hi hm
  · exact hr i (by omega) hj

lemma compile_rooted (workers : ℕ) (expr : PacketExpr) (hv : expr.Valid workers)
    (state : HistoryState) (root : ℕ) (hroot : root < state.next) :
    RootedQueries (state.states root) state (expr.compile root state.next).nodes := by
  induction expr generalizing state root with
  | atom worker => exact rootedQueries_query state worker root
  | sequence left right ihl ihr =>
      let l := left.compile root state.next
      let first := l.nodes.foldl (flip historyStep) state
      have hl : BlockMeaning workers state root l left.calls := compile_meaning workers left hv.1 state root hroot
      have hn : first.next = l.next := hl.next
      have hsource : l.output < first.next := by rw [hn]; exact hl.output_lt
      apply rootedQueries_append _ _ l.nodes
      · exact ihl hv.1 state root hroot
      · apply rootedQueries_mono _ (first.states l.output)
        · rw [hl.output]; exact subset_union_left
        · simpa only [hn] using ihr hv.2 first l.output hsource
  | fork owner left right ihl ihr =>
      let l := left.compile root state.next
      let first := l.nodes.foldl (flip historyStep) state
      have hl : BlockMeaning workers state root l left.calls := compile_meaning workers left hv.2.1 state root hroot
      have hn : first.next = l.next := hl.next
      have hsource : root < first.next := by rw [hn]; exact hroot.trans_le hl.next_le
      apply rootedQueries_append
      · apply rootedQueries_append
        · exact ihl hv.2.1 state root hroot
        · have hh := ihr hv.2.2 first root hsource
          have hbase : first.states root = state.states root := historyFold_old l.nodes state root hroot
          simpa only [hn, hbase] using hh
      · exact rootedQueries_merge _ _ _ _ _ _
  | overlap owner left right afterBoth afterRight ihl ihr iha ihb =>
      let l := left.compile root state.next
      let first := l.nodes.foldl (flip historyStep) state
      let r := right.compile root l.next
      let forked : GraphBlock :=
        ⟨l.nodes ++ r.nodes ++ [GraphNode.merge owner l.output r.output root], r.next, r.next + 1⟩
      let f := forked.nodes.foldl (flip historyStep) state
      let a := afterBoth.compile r.next (r.next + 1)
      let p := (forked.nodes ++ a.nodes).foldl (flip historyStep) state
      have hl : BlockMeaning workers state root l left.calls := compile_meaning workers left hv.2.1 state root hroot
      have hn : first.next = l.next := hl.next
      have hsource : root < first.next := by rw [hn]; exact hroot.trans_le hl.next_le
      have hr : BlockMeaning workers first root r right.calls := by
        simpa only [hn] using compile_meaning workers right hv.2.2.1 first root hsource
      have hf : BlockMeaning workers state root forked (left.calls + right.calls) :=
        block_fork workers owner root left.calls right.calls state l r hv.1 hroot hl hr
      have hfn : f.next = r.next + 1 := hf.next
      have ha : BlockMeaning workers f r.next a afterBoth.calls := by
        simpa only [hfn] using compile_meaning workers afterBoth hv.2.2.2.1 f r.next (by rw [hfn]; omega)
      have hp := block_sequence workers root (left.calls + right.calls) afterBoth.calls state forked a hf ha
      have hpn : p.next = a.next := hp.next
      have hrf : r.output < f.next := by rw [hfn]; exact hr.output_lt.trans_le (Nat.le_succ _)
      have hrp : r.output < p.next := by rw [hpn]; exact hrf.trans_le ha.next_le
      have hcommon : state.states root ⊆ p.states r.output := by
        change state.states root ⊆ ((forked.nodes ++ a.nodes).foldl (flip historyStep) state).states r.output
        rw [List.foldl_append, historyFold_old a.nodes f r.output hrf]
        dsimp only [f, forked]
        rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, flip]
        rw [historyStep_old _ _ _ (by rw [List.foldl_append, hr.next]; exact hr.output_lt),
          List.foldl_append, hr.output, historyFold_old l.nodes state root hroot]
        exact subset_union_left
      apply rootedQueries_append
      · apply rootedQueries_append
        · apply rootedQueries_append
          · apply rootedQueries_append
            · apply rootedQueries_append
              · exact ihl hv.2.1 state root hroot
              · have hbase : first.states root = state.states root := historyFold_old l.nodes state root hroot
                simpa only [hn, hbase] using ihr hv.2.2.1 first root hsource
            · exact rootedQueries_merge _ _ _ _ _ _
          · apply rootedQueries_mono _ (f.states r.next)
            · rw [hf.output]; exact subset_union_left
            · simpa only [hfn] using iha hv.2.2.2.1 f r.next (by rw [hfn]; omega)
        · apply rootedQueries_mono _ (p.states r.output) _ _ hcommon
          simpa only [hpn] using ihb hv.2.2.2.2 p r.output hrp
      · exact rootedQueries_merge _ _ _ _ _ _

end LongTails.Proofs.BirchCausalControllers
