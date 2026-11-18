import LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
import LongTails.Proofs.DistributedExecution

namespace LongTails.Proofs.LeonNetwork

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex

lemma compute_ready (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (i : Fin p.n) (s : ComputeState p) (t : Time) :
    ((computation p g).answer i s t).isSome ↔ ∃ q ∈ s.pending, q.1 ≤ t := by
  cases h : s.pending with
  | none => simp [computation, h]
  | some entry =>
    rcases entry with ⟨finish, x, m⟩
    by_cases ht : finish ≤ t <;> simp [computation, h, ht]

lemma mail_ready (p : Params) (s : Mail p) (t : Time) :
    ((communication p).answer s t).isSome ↔ ∃ edge, ∃ m ∈ (s edge).head?, m.1 ≤ t := by
  classical
  simp [communication, Option.isSome_iff_exists]

lemma mail_answer (p : Params) (s s' : Mail p) (t : Time)
    (i j : Fin p.n) (bits : List Bool)
    (h : (communication p).answer s t = some ((j, i, bits), s')) :
    ∃ finish rest, s (i, j) = (finish, bits) :: rest ∧ finish ≤ t ∧
      s' = Function.update s (i, j) rest := by
  classical
  unfold communication at h
  dsimp only at h
  split_ifs at h with ready
  · let e := ready.choose
    let m := ready.choose_spec.choose
    have hm : m ∈ (s e).head? ∧ m.1 ≤ t := ready.choose_spec.choose_spec
    cases hp : s e with
    | nil => simp [hp] at hm
    | cons v rest =>
      have hv : v = m := by simpa [hp] using hm.1
      have hreply : ((e.2, (e.1, m.2)), Function.update s e (s e).tail) =
          ((j, (i, bits)), s') := Option.some.inj h
      have hfst := congrArg (fun z => z.1.1) hreply
      have hsnd := congrArg (fun z => z.1.2.1) hreply
      have hb := congrArg (fun z => z.1.2.2) hreply
      have hstate := congrArg Prod.snd hreply
      have he : e = (i, j) := Prod.ext hsnd hfst
      refine ⟨m.1, rest, ?_, hm.2, ?_⟩
      · rw [← he, hp, hv]
        have hb' : m.2 = bits := hb
        rw [← hb']
      · simpa [hp, ← he] using hstate.symm

lemma next_exists (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (A : Algorithm (ComputeQuery p) (ComputeReply p)
      (CommReply p) (Point p) p.n) (c : ExecutionState (system p g P) A)
    (hc : c.time ≤ c.deadline) :
    ∃ t, IsLeast {t | c.time ≤ t ∧ t ≤ c.deadline ∧
      (t = c.deadline ∨ (event (system p g P) A c t).isSome)} t := by
  classical
  let wake := Finset.univ.image c.wakeTime
  let comp := Finset.univ.biUnion fun i => ((c.oracle.computation i).pending.toFinset).image Prod.fst
  let mail := Finset.univ.biUnion fun e => ((c.oracle.communication e).head?.toFinset).image Prod.fst
  apply DistributedExecution.nextTime_exists_of_thresholds _ (wake ∪ comp ∪ mail) _ _ hc
  intro t
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready]
  change ((∃ i, ((computation p g).answer i (c.oracle.computation i) t).isSome) ∨
    ((communication p).answer c.oracle.communication t).isSome) ∨ (∃ i, c.wakeTime i ≤ t) ↔ _
  refine Iff.trans (((exists_congr (fun i => compute_ready p g i (c.oracle.computation i) t)).or
    (mail_ready p c.oracle.communication t)).or Iff.rfl) ?_
  simp only [wake, comp, mail, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Option.mem_toFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ((⟨i, q, hq, ht⟩ | ⟨e, m, hm, ht⟩) | ⟨i, ht⟩)
    · exact ⟨q.1, Or.inl (Or.inr ⟨i, q, hq, rfl⟩), ht⟩
    · exact ⟨m.1, Or.inr ⟨e, m, hm, rfl⟩, ht⟩
    · exact ⟨_, Or.inl (Or.inl ⟨i, rfl⟩), ht⟩
  · rintro ⟨r, ((⟨i, rfl⟩ | ⟨i, q, hq, rfl⟩) | ⟨e, m, hm, rfl⟩), ht⟩
    · exact Or.inr ⟨i, ht⟩
    · exact Or.inl (Or.inl ⟨i, q, hq, ht⟩)
    · exact Or.inl (Or.inr ⟨e, m, hm, ht⟩)

end LongTails.Proofs.LeonNetwork

namespace LongTails.Proofs.LeonNetworkWork

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex

lemma update_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] (f : ι → α) (g : ι → α → ℕ)
    (i : ι) (v : α) :
    (∑ j, g j (Function.update f i v j)) + g i (f i) = (∑ j, g j (f j)) + g i v := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun j => g j (f j)) (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i, g j (Function.update f i v j)) =
      ∑ j ∈ Finset.univ.erase i, g j (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, Function.update_self]
  omega

def queued {p : Params} (s : Mail p) : ℕ := ∑ e, (s e).length

def pending {p : Params} (states : Fin p.n → ComputeState p) : ℕ :=
  ∑ i, ((states i).pending.toList).length

lemma post_work (p : Params) (s : Mail p) (t : Time) (i : Fin p.n) (q : Fin p.n × List Bool) :
    queued ((communication p).submit s t i q) = queued s + 1 := by
  unfold communication queued
  dsimp only
  have he := update_sum s (fun _ msgs => msgs.length) (i, q.1)
    (s (i, q.1) ++ [(max t (((s (i, q.1)).getLast?.map Prod.fst).getD 0) +
      p.l + p.b * q.2.length, q.2)])
  simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at he
  omega

lemma deliver_work (p : Params) (s s' : Mail p) (t : Time) (i j : Fin p.n) (bits : List Bool)
    (h : (communication p).answer s t = some ((j, i, bits), s')) :
    queued s' + 1 = queued s := by
  obtain ⟨time, rest, he, _, rfl⟩ := LeonNetwork.mail_answer p s s' t i j bits h
  have hh := update_sum s (fun _ msgs => msgs.length) (i, j) rest
  rw [he, List.length_cons] at hh
  unfold queued
  omega

lemma compute_work (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (states : Fin p.n → ComputeState p) (i : Fin p.n) (t : Time) (q : ComputeQuery p) :
    pending (Function.update states i ((computation p g).submit i (states i) t q)) ≤
      pending states + 1 := by
  have he := update_sum states (fun _ s => s.pending.toList.length) i
    ((computation p g).submit i (states i) t q)
  cases hs : (states i).pending <;> simp [computation, hs, pending] at he ⊢
  omega

lemma answer_work (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (states : Fin p.n → ComputeState p) (s' : ComputeState p) (i : Fin p.n) (t : Time)
    (vals : ComputeReply p) (h : (computation p g).answer i (states i) t = some (vals, s')) :
    pending (Function.update states i s') + 1 = pending states := by
  cases hs : (states i).pending with
  | none => simp [computation, hs] at h
  | some entry =>
    rcases entry with ⟨finish, x, m⟩
    by_cases ht : finish ≤ t
    · simp [computation, hs, ht] at h
      have he := update_sum states (fun _ s => s.pending.toList.length) i s'
      rw [← h.2] at he ⊢
      simp only [hs, Option.toList_some, List.length_cons, List.length_nil,
        Option.toList_none, Nat.add_zero, Nat.zero_add] at he
      exact he
    · simp [computation, hs, ht] at h

end LongTails.Proofs.LeonNetworkWork
