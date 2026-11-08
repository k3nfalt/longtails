import LongTails.Proofs.BirchCollectionNestedReset

namespace LongTails.Proofs.BirchCollectionNestedRun

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Proofs.BirchCollectionGroupReady
open LongTails.Proofs.BirchCollectionNestedShape
open LongTails.Proofs.BirchCollectionNestedCollect
open LongTails.Proofs.BirchCollectionNestedReset
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionLocalPublish (abortOne)
open LongTails.Proofs.BirchCollectionBatches (RetiredPast)

local notation "groupStep" => LongTails.Algorithms.BirchCollectionLocalAsync.advance
local notation "groupEnabled" => LongTails.Algorithms.BirchCollectionLocal.Enabled

structure Data {m : ℕ} (layout : Layout m) (s : State m) (start B : ℕ) (move : ℝ) : Prop where
  ready : Ready layout.group s.outer start B move
  shape : Shape layout s start B move

lemma frame_extends {m : ℕ} {s t : Round m} (h : CaptureFrame s t) : Extends s.trace t.trace :=
  ⟨h.stateCount.ge, h.directionCount.ge, fun i _ => congrFun h.states i,
    fun i _ => congrFun h.directions i, h.rawCount⟩

def launch {m : ℕ} (layout : Layout m) (B : ℕ) (move : ℝ) (s : State m) (ws : List (Fin m)) :
    State m :=
  {s with outer := ws.foldl (fun t w => groupStep layout.group B move t (.query w)) s.outer}

lemma launch_data {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m) (ws : List (Fin m))
    (hs : Data layout s start B move) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    let out := launch layout B move s ws
    Data layout out start B move ∧ CaptureFrame s.outer out.outer ∧
      ∀ w, (out.outer.pending w).isSome ↔ w ∈ ws ∨ (s.outer.pending w).isSome := by
  induction ws generalizing s with
  | nil => exact ⟨hs, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl⟩, by simp [launch]⟩
  | cons w ws ih =>
    let t : State m := {s with outer := groupStep layout.group B move s.outer (.query w)}
    obtain ⟨hr, hf⟩ := ready_query layout.group s.outer w hs.ready hs.shape.heads hB hm0 hm1
    have ht : Data layout t start B move := ⟨hr, shape_frame hs.shape hf (fun _ => rfl)⟩
    obtain ⟨hd, hframe, hready⟩ := ih t ht
    refine ⟨hd, hf.trans hframe, ?_⟩
    intro v
    change ((launch layout B move t ws).outer.pending v).isSome ↔ _
    rw [hready v]
    by_cases hv : v = w
    · subst v
      simp [t, LongTails.Algorithms.BirchCollectionLocalAsync.advance]
    · simp [t, LongTails.Algorithms.BirchCollectionLocalAsync.advance, hv]

lemma start_data {m start B : ℕ} {move : ℝ} (layout : Layout m) (trace : TraceState)
    (events : List Event) (hr : run events = trace) (hv : ValidFrom (m + 1) {} events)
    (hret : RetiredPast trace) (hc : trace.nextDirection = start)
    (hb : trace.markers.getLast?.getD 0 < trace.nextState)
    (hh : (trace.states (trace.markers.getLast?.getD 0)).history = Finset.range start)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    let s := LongTails.Algorithms.BirchCollectionNested.start layout B move trace events
    Data layout s start B move ∧
      Extends trace s.outer.trace ∧ s.outer.completed = 0 ∧ s.outer.trace.markers = trace.markers ∧
      ∀ w, (s.outer.pending w).isSome := by
  let s : State m := ⟨Round.initial m trace events, fun _ => ⟨trace.markers.getLast?.getD 0, 0⟩⟩
  have hready : Ready layout.group s.outer start B move :=
    ⟨hr, hv, hret, by simp [s, Round.initial], by simp [s, Round.initial], by simp [s, Round.initial]⟩
  have hd : Data layout s start B move := ⟨hready, shape_initial layout trace events hc hb hh⟩
  obtain ⟨ht, hf, hp⟩ := launch_data layout s (List.finRange m) hd hB hm0 hm1
  exact ⟨ht, (frame_extends hf), hf.completed, hf.markers, fun w => (hp w).2 (Or.inl (by simp))⟩

lemma synchronize_data {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m) (i : Fin m)
    (hs : Data layout s start B move)
    (hready : ∀ w, layout.cluster (layout.group w) ≠ i → (s.outer.pending w).isSome)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    let out := synchronize layout B move s i
    Data layout out start B move ∧ Extends s.outer.trace out.outer.trace ∧
      out.outer.completed = s.outer.completed ∧ out.outer.trace.markers = s.outer.trace.markers ∧
      ∀ w, (out.outer.pending w).isSome := by
  let t : State m := {s with outer := abortCluster layout B s.outer i}
  obtain ⟨hr, hf, hpend⟩ := abort_fold_ready layout.group s.outer (workers layout i) hs.ready
  have ht : Data layout t start B move := ⟨hr, shape_frame hs.shape hf (fun _ => rfl)⟩
  let pair := collectCluster layout t.outer i (t.cluster i).point
  have hc : Collected layout t i pair (groups layout i) start B move := collect_data layout t i ht.shape ht.ready
  let reset := resetCluster layout t i pair
  have hstate : Shape layout reset start B move := reset_shape ht.shape hc
  have hsaved : Ready layout.group reset.outer start B move := by
    apply ready_change_heads pair.1 _ hc.ready
    intro w j hj
    have h' : (layout.cluster (layout.group w)) ≠ i := by
      intro h
      have hw := (worker_member layout i w).2 h
      have hp := hpend w
      rw [ite_eq_left hw] at hp
      change pair.1.pending w = some j at hj
      rw [hc.frame.pending, show t.outer.pending w = none from hp] at hj
      contradiction
    change (if layout.cluster (layout.group w) = i then pair.2 else pair.1.head (layout.group w)) = _
    rw [ite_eq_right h']
  obtain ⟨hd, hfr, hready'⟩ := launch_data layout reset (workers layout i) ⟨hsaved, hstate⟩ hB hm0 hm1
  have hx' := frame_extends hfr
  have hpass : Extends pair.1.trace (launch layout B move reset (workers layout i)).outer.trace := hx'
  refine ⟨hd, (frame_extends hf).trans (hc.frame.trace.trans hpass), ?_, ?_, ?_⟩
  · exact hfr.completed.trans (hc.frame.completed.trans hf.completed)
  · exact hfr.markers.trans (hc.frame.markers.trans hf.markers)
  · intro w
    apply (hready' w).2
    by_cases hw : w ∈ workers layout i
    · exact Or.inl hw
    · right
      change (pair.1.pending w).isSome
      rw [hc.frame.pending, show t.outer.pending w = s.outer.pending w from (hpend w).trans (ite_eq_right hw)]
      exact hready w (fun h => hw ((worker_member layout i w).2 h))

lemma reply_extends {m B : ℕ} (layout : Layout m) (move : ℝ) (s : State m) (w : Fin m) :
    Extends s.outer.trace (groupStep layout.group B move s.outer (.reply w)).trace := by
  cases h : s.outer.pending w with
  | none => simpa only [LongTails.Algorithms.BirchCollectionLocalAsync.advance, h] using
      extends_refl s.outer.trace
  | some j =>
    simp only [LongTails.Algorithms.BirchCollectionLocalAsync.advance, h]
    exact extends_fold _ _

lemma advance_data {m start Q B : ℕ} {move : ℝ} (layout : Layout m) (s : State m) (w : Fin m)
    (hs : Data layout s start B move) (hlt : s.outer.completed < Q)
    (hp : ∀ v, (s.outer.pending v).isSome)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    let out := advance layout Q B move s w
    Data layout out start B move ∧ Extends s.outer.trace out.outer.trace ∧
      out.outer.completed = s.outer.completed + 1 ∧ out.outer.trace.markers = s.outer.trace.markers ∧
      (out.outer.completed < Q → ∀ v, (out.outer.pending v).isSome) := by
  let i := layout.cluster (layout.group w)
  let t := groupStep layout.group B move s.outer (.reply w)
  let completed := (s.cluster i).completed + 1
  let u : State m := {outer := t, cluster := Function.update s.cluster i {(s.cluster i) with completed}}
  have hen : groupEnabled Q s.outer (.reply w) := ⟨hlt, hp w⟩
  obtain ⟨hr, hf⟩ := ready_reply layout.group s.outer w hs.ready hs.shape.heads hen
  have hs' : Shape layout u start B move := by
    apply shape_reply (layout.group w) hs.shape hf
    intro c
    change (Function.update s.cluster i {(s.cluster i) with completed} c).point = _
    by_cases h : c = i
    · subst c
      simp
    · simp [h]
  have hdata : Data layout u start B move := ⟨hr, hs'⟩
  have hframe : Extends s.outer.trace u.outer.trace := reply_extends layout move s w
  have hothers (v : Fin m) (hv : v ≠ w) : (u.outer.pending v).isSome := by
    cases h : s.outer.pending w with
    | none =>
      have hh := hp w
      simp [h] at hh
    | some j =>
      change (t.pending v).isSome
      simpa [t, LongTails.Algorithms.BirchCollectionLocalAsync.advance, h, hv] using hp v
  by_cases hstop : t.completed = Q
  · have hout : advance layout Q B move s w = u := by
      change (if t.completed = Q then u else _) = u
      rw [ite_eq_left hstop]
    rw [hout]
    exact ⟨hdata, hframe, hf.completed, hf.markers, fun hl => (Nat.lt_irrefl Q (hstop ▸ hl)).elim⟩
  · by_cases hsync : layout.quota i = some completed
    · have hout : advance layout Q B move s w = synchronize layout B move u i := by
        change (if t.completed = Q then u else if layout.quota i = some completed then _ else _) = _
        rw [ite_eq_right hstop, ite_eq_left hsync]
      obtain ⟨hd, he, hc, hm, hp'⟩ := synchronize_data layout u i hdata
        (fun v hv => hothers v (fun he => hv (he ▸ rfl))) hB hm0 hm1
      rw [hout]
      exact ⟨hd, hframe.trans he, hc.trans hf.completed, hm.trans hf.markers, fun _ => hp'⟩
    · have hout : advance layout Q B move s w = launch layout B move u [w] := by
        change (if t.completed = Q then u else if layout.quota i = some completed then _ else _) = _
        rw [ite_eq_right hstop, ite_eq_right hsync]
        rfl
      obtain ⟨hd, he, hp'⟩ := launch_data layout u [w] hdata hB hm0 hm1
      rw [hout]
      refine ⟨hd, hframe.trans (frame_extends he), he.completed.trans hf.completed,
        he.markers.trans hf.markers, ?_⟩
      intro _ v
      apply (hp' v).2
      by_cases hv : v = w
      · exact Or.inl (by simp [hv])
      · exact Or.inr (hothers v hv)

end LongTails.Proofs.BirchCollectionNestedRun
