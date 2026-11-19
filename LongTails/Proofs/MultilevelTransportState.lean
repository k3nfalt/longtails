import LongTails.Proofs.MultilevelTimetable
import LongTails.Proofs.MultilevelClock

namespace LongTails.Proofs.MultilevelTransportState

open DistributedTemplate MeasureTheory
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTimetable

inductive Phase
  | idle
  | down (job : ℕ) (atTime : Time)
  | work (job : ℕ) (atTime : Time)
  | up (job : ℕ) (atTime : Time)


def Phase.job : Phase → Option ℕ
  | .idle => none
  | .down j _ | .work j _ | .up j _ => some j

def Phase.unused : Phase → ℕ
  | .down _ _ | .work _ _ => 1
  | _ => 0

def Phase.remaining : Phase → ℕ
  | .idle => 0
  | .down _ _ => 3
  | .work _ _ => 2
  | .up _ _ => 1

structure Book (p : Params) where
  issued : ℕ := 0
  pending : Fin p.n → Phase := fun _ => .idle
  done : Finset ℕ := ∅
  memory : Fin p.n → Bits := fun _ => []

def count {p : Params} (t : Script p) (i : Fin p.n) (k : ℕ) :=
  ((Finset.range k).filter (fun j => t.worker j = i)).card

lemma count_succ {p : Params} (t : Script p) (i : Fin p.n) (k : ℕ) :
    count t i (k+1) = count t i k + if t.worker k = i then 1 else 0 := by
  by_cases h : t.worker k = i <;> simp [count, Finset.range_add_one, h, Finset.filter_insert]

def Valid {p : Params} (t : Script p) (b : Book p) : Prop :=
  b.issued ≤ t.count ∧ (∀ j ∈ b.done, j < b.issued) ∧
  (∀ i j, (b.pending i).job = some j →
    j < b.issued ∧ t.worker j = i ∧ j ∉ b.done ∧ count t i b.issued = ordinal t j + 1) ∧
  ∀ j < b.issued, j ∈ b.done ∨ (b.pending (t.worker j)).job = some j

def launch {p : Params} (t : Script p) (b : Book p) (now : Time) : Book p :=
  {b with
    issued := b.issued+1
    pending := Function.update b.pending (t.worker b.issued) (.down b.issued now)}

def startWork {p : Params} (b : Book p) (i : Fin p.n) (j : ℕ) (now : Time) (bs : Bits) : Book p :=
  {b with pending := Function.update b.pending i (.work j now), memory := Function.update b.memory i bs}

def startReply {p : Params} (b : Book p) (i : Fin p.n) (j : ℕ) (now : Time) : Book p :=
  {b with pending := Function.update b.pending i (.up j now)}

def collect {p : Params} (b : Book p) (i : Fin p.n) (j : ℕ) : Book p :=
  {b with pending := Function.update b.pending i .idle, done := insert j b.done}

lemma initial_valid {p : Params} (t : Script p) : Valid t ({} : Book p) := by
  simp [Valid, Phase.job]

lemma launch_valid {p : Params} (t : Script p) (b : Book p) (τ : Time)
    (hb : Valid t b) (hj : b.issued < t.count) (hfree : (b.pending (t.worker b.issued)).job = none) :
    Valid t (launch t b τ) := by
  rcases hb with ⟨_,hd,hp,he⟩
  refine ⟨hj, fun j h => (hd j h).trans (Nat.lt_succ_self _), ?_, ?_⟩
  · intro i j h
    by_cases hi : i = t.worker b.issued
    · subst i
      simp [launch, Phase.job] at h
      subst j
      refine ⟨Nat.lt_succ_self _, rfl, fun h => (hd _ h).false, ?_⟩
      change count t _ (b.issued+1) = count t _ b.issued + 1
      simp [count_succ]
    · have ho : (b.pending i).job = some j := by simpa [launch, hi] using h
      obtain ⟨hlt,hw,hj,hc⟩ := hp i j ho
      exact ⟨by simpa [launch] using hlt.trans (Nat.lt_succ_self _), hw, hj,
        by simp [launch, count_succ, Ne.symm hi, hc]⟩
  · intro j hj
    by_cases h : j = b.issued
    · subst j; exact Or.inr (by simp [launch, Phase.job])
    have hl : j < b.issued := by change j < b.issued+1 at hj; omega
    rcases he j hl with hd | hbusy
    · exact Or.inl hd
    · have hn : t.worker j ≠ t.worker b.issued := by
        intro eq
        rw [eq, hfree] at hbusy
        contradiction
      exact Or.inr (by simpa [launch, hn] using hbusy)

lemma same_jobs_valid {p : Params} (t : Script p) (b c : Book p) (hb : Valid t b)
    (hissued : c.issued = b.issued) (hdone : c.done = b.done)
    (hjob : ∀ i, (c.pending i).job = (b.pending i).job) : Valid t c := by
  simpa only [Valid, hissued, hdone, hjob] using hb

lemma collect_valid {p : Params} (t : Script p) (b : Book p) (i : Fin p.n) (j : ℕ)
    (hb : Valid t b) (hj : (b.pending i).job = some j) : Valid t (collect b i j) := by
  rcases hb with ⟨hc,hd,hp,he⟩
  obtain ⟨hlt,hw,_,_⟩ := hp _ _ hj
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | h
    · exact hlt
    · exact hd _ h
  · intro v a ha
    by_cases h : v = i
    · simp [collect, h, Phase.job] at ha
    · have h₀ : (b.pending v).job = some a := by simpa [collect,h] using ha
      obtain ⟨hlt',hw',hd',hc'⟩ := hp _ _ h₀
      exact ⟨hlt', hw', by simp [collect, hd', show a ≠ j from fun eq => h (hw'.symm.trans (eq ▸ hw))], hc'⟩
  · intro a ha
    rcases he _ ha with hd | hbusy
    · exact Or.inl (Finset.mem_insert_of_mem hd)
    · by_cases h : t.worker a = i
      · rw [h,hj] at hbusy
        exact Or.inl (by simp [collect, Option.some.inj hbusy])
      · exact Or.inr (by simpa [collect,h] using hbusy)

def frame (bs : Bits) := bs ++ List.replicate clockBits false

lemma unframe_frame (bs : Bits) : unframe (frame bs) = bs := by simp [unframe, frame]

noncomputable def payload {p : Params} (t : Script p) (out : ℕ → Bits) (k : ℕ) : Bits :=
  t.request k fun j => if j < k ∧ t.finish j ≤ t.start k then out j else []

lemma reply_eq {p : Params} (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p)
    (xs : Samples p) (k : ℕ) :
    let v := reply t g xs
    let bs := payload t v k
    let i := t.worker k
    let z := t.decode bs
    let sample := xs i (ordinal t k)
    v k = t.encode bs (g i z.1 sample, g i z.2 sample) := by
  dsimp only
  conv_lhs => unfold reply
  rfl

noncomputable def root {p : Params} (b : Book p) (seed : Selection p) (out : ℕ → Bits) : State p :=
  {seed, next := b.issued, pending := fun i => (b.pending i).job,
   answers := fun j => if j ∈ b.done then some (out j) else none}

noncomputable def worker {p : Params} (b : Book p) (seed : Selection p) (i : Fin p.n) : State p :=
  {seed, input := b.memory i}

lemma visible_ready {p : Params} (t : Script p) (b : Book p) (seed : Selection p) (out : ℕ → Bits)
    (hr : ready t (root b seed out)) :
    t.request b.issued (visible t b.issued (root b seed out).answers) = payload t out b.issued := by
  apply congrArg
  funext j
  by_cases h : j < b.issued ∧ t.finish j ≤ t.start b.issued
  · have hs := hr.2.2 j (h.1.trans hr.1) h.2
    simp [root] at hs
    simp [visible, h, root, hs]
  · simp [visible, h]

end LongTails.Proofs.MultilevelTransportState
