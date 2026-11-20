import LongTails.Proofs.GraceScheduleBlocks
import LongTails.Proofs.GraceRouting

namespace LongTails.Proofs.GraceExchangeBlock

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LeonReservations (Frame sends receives used usedCount posted consumed due)
open LeonTranscript (wire Op)
open GraceReservations (duration)
open GraceScheduleBlocks (Block locate)

variable {p : Params}

abbrev Packets (p : Params) := Fin p.n → Fin p.n → Option (List Bool)

def sendRow (M : Packets p) (a b : Time) (j : Fin p.n) : Frame p.base :=
  ⟨fun i => match M i j with
    | some bits => .send j bits
    | none => .send i [], a, a, b⟩

def readRow (M : Packets p) (b : Time) (i : Fin p.n) : Frame p.base :=
  ⟨fun j => match M i j with
    | some bits => .receive i (wire bits)
    | none => .send j [], b, b, b⟩

def rows (M : Packets p) (a b : Time) :=
  (List.finRange p.n).map (sendRow M a b) ++ (List.finRange p.n).map (readRow M b)

def message (b : Time) (packet : Option (List Bool)) :=
  packet.toList.map fun bits => (b,wire bits)

lemma sent (M : Packets p) (a b : Time) (ids : List (Fin p.n)) (hn : ids.Nodup)
    (i j : Fin p.n) (hne : i ≠ j) :
    posted (ids.map (sendRow M a b)) i j = if j ∈ ids then message b (M i j) else [] := by
  induction ids with
  | nil => simp [posted]
  | cons k ks ih =>
    obtain ⟨hk,hks⟩ := List.nodup_cons.mp hn
    change sends (sendRow M a b k) i j ++ posted (ks.map (sendRow M a b)) i j = _
    rw [ih hks]
    by_cases he : j = k
    · subst k
      cases hm : M i j <;> simp [sends, sendRow, hm, message, hk, hne]
    · cases hm : M i k <;> simp [sends, sendRow, hm, hne, he, Ne.symm he]

lemma read (M : Packets p) (b : Time) (ids : List (Fin p.n)) (hn : ids.Nodup)
    (i j : Fin p.n) :
    consumed (ids.map (readRow M b)) i j = if i ∈ ids then message b (M i j) else [] := by
  induction ids with
  | nil => simp [consumed]
  | cons k ks ih =>
    obtain ⟨hk,hks⟩ := List.nodup_cons.mp hn
    change receives (readRow M b k) i j ++ consumed (ks.map (readRow M b)) i j = _
    rw [ih hks]
    by_cases he : i = k
    · subst k
      cases hm : M i j <;> simp [receives, readRow, hm, message, hk]
    · cases hm : M k j <;> simp [receives, readRow, hm, he, Ne.symm he]

lemma send_effect (M : Packets p) (a b : Time) (ids : List (Fin p.n)) (i j : Fin p.n) :
    consumed (ids.map (sendRow M a b)) i j = [] ∧ usedCount (ids.map (sendRow M a b)) i = 0 := by
  induction ids with
  | nil => exact ⟨rfl,rfl⟩
  | cons k ks ih =>
    change receives (sendRow M a b k) i j ++ consumed (ks.map (sendRow M a b)) i j = [] ∧
      used (sendRow M a b k) i + usedCount (ks.map (sendRow M a b)) i = 0
    rw [ih.1, ih.2]
    cases h : M i k <;> cases h' : M j k <;> simp [receives, used, sendRow, h, h']

lemma read_effect (M : Packets p) (b : Time) (ids : List (Fin p.n)) (i j : Fin p.n)
    (hne : i ≠ j) : posted (ids.map (readRow M b)) i j = [] := by
  induction ids with
  | nil => rfl
  | cons k ks ih =>
    change sends (readRow M b k) i j ++ posted (ks.map (readRow M b)) i j = []
    rw [ih]
    cases h : M k i <;> simp [sends,readRow,h,hne]

lemma used_read (M : Packets p) (b : Time) (ids : List (Fin p.n)) (i : Fin p.n) :
    usedCount (ids.map (readRow M b)) i = 0 := by
  induction ids with
  | nil => rfl
  | cons k ks ih =>
    change used (readRow M b k) i + usedCount (ks.map (readRow M b)) i = 0
    rw [ih]
    cases h : M k i <;> simp [used,readRow,h]

lemma zero_samples (M : Packets p) (a b : Time) (i : Fin p.n) :
    usedCount (rows M a b) i = 0 := by
  rw [rows, GraceScheduleBlocks.used_append, (send_effect M a b _ i i).2, used_read, add_zero]

lemma map_location {α β : Type*} (f : α → β) (xs : List α) (pre : List β)
    (c : β) (rest : List β) (he : xs.map f = pre ++ c :: rest) :
    ∃ l k r, xs = l ++ k :: r ∧ pre = l.map f ∧ c = f k ∧ rest = r.map f := by
  induction xs generalizing pre with
  | nil => simp at he
  | cons x xs ih =>
    cases pre with
    | nil =>
      obtain ⟨hc, hr⟩ := List.cons.inj he
      exact ⟨[],x,xs,rfl,rfl,hc.symm,hr.symm⟩
    | cons v pre =>
      obtain ⟨hv, hh⟩ := List.cons.inj he
      obtain ⟨l,k,r,hx,hp,hc,hr⟩ := ih pre hh
      exact ⟨x::l,k,r,by simp [hx],by simp [hp,hv],hc,hr⟩

lemma location (M : Packets p) (a b : Time) (pre : List (Frame p.base)) (c : Frame p.base)
    (rest : List (Frame p.base)) (he : rows M a b = pre ++ c :: rest) :
    (∃ l k r, List.finRange p.n = l ++ k :: r ∧ pre = l.map (sendRow M a b) ∧
      c = sendRow M a b k ∧ rest = r.map (sendRow M a b) ++ (List.finRange p.n).map (readRow M b)) ∨
    (∃ l k r, List.finRange p.n = l ++ k :: r ∧
      pre = (List.finRange p.n).map (sendRow M a b) ++ l.map (readRow M b) ∧
      c = readRow M b k ∧ rest = r.map (readRow M b)) := by
  obtain ⟨tail,h₁,hr⟩ | ⟨mid,h₂,hp⟩ := locate _ _ _ _ _ he
  · obtain ⟨l,k,r,hl,hp,hc,ht⟩ := map_location _ _ _ _ _ h₁
    exact Or.inl ⟨l,k,r,hl,hp,hc,by rw [hr,ht]⟩
  · obtain ⟨l,k,r,hl,hm,hc,ht⟩ := map_location _ _ _ _ _ h₂
    exact Or.inr ⟨l,k,r,hl,by rw [hp,hm],hc,ht⟩

lemma before {l r : List (Fin p.n)} {k : Fin p.n} (he : List.finRange p.n = l ++ k :: r) :
    l.Nodup ∧ k ∉ l := by
  have hn := List.nodup_finRange p.n
  rw [he, List.nodup_append] at hn
  exact ⟨hn.1,fun hk => hn.2.2 _ hk _ (by simp) rfl⟩

lemma times (M : Packets p) (a b : Time) (hab : a ≤ b) (c : Frame p.base)
    (hc : c ∈ rows M a b) : a ≤ c.start ∧ c.finish ≤ b ∧ c.delivery = b := by
  obtain ⟨pre,rest,he⟩ := List.append_of_mem hc
  rcases location M a b pre c rest he with ⟨_,_,_,_,_,rfl,_⟩ | ⟨_,_,_,_,_,rfl,_⟩
  · exact ⟨le_rfl,hab,rfl⟩
  · exact ⟨hab,le_rfl,rfl⟩

lemma prior_due (M : Packets p) (a b : Time) (hab : a ≤ b) {pre : List (Frame p.base)}
    {c rest} (he : rows M a b = pre ++ c :: rest) (i j : Fin p.n) (m) (hm : m ∈ posted pre i j) :
    m.1 = b := by
  obtain ⟨f,hf,hh⟩ := List.mem_flatMap.mp hm
  unfold sends at hh
  cases ho : f.op i <;> simp [ho] at hh
  rw [hh.2]
  exact (times M a b hab f (by simp [he,hf])).2.2

lemma block (g : Point p → p.Ω → Point p) (s : Samples p) (M : Packets p) (a b : Time)
    (hab : a ≤ b) (diag : ∀ i, M i i = none)
    (cap : ∀ i j bits, M i j = some bits → p.G.Adj i j ∧ a + duration p i j bits ≤ b) :
    Block g s a b (rows M a b) := by
  have due_read (ids : List (Fin p.n)) : due b (ids.map (readRow M b)) false = b := by
    cases ids <;> rfl
  have dummy {pre c rest} (he : rows M a b = pre ++ c :: rest) (i : Fin p.n)
      (t : Time) (ht : t ≤ b) :
      (i = i ∨ p.G.Adj i i) ∧ t + duration p i i [] ≤ b ∧
        ∀ m ∈ posted pre i i, m.1 + duration p i i [] ≤ b := by
    have hd : duration p i i [] = 0 := by simp [duration]
    rw [hd]
    exact ⟨Or.inl rfl, by simpa using ht, fun m hm => by simpa using (prior_due M a b hab he i i m hm).le⟩
  constructor
  · constructor
    · intro pre c rest he
      rcases location M a b pre c rest he with ⟨l,k,r,_,_,rfl,rfl⟩ | ⟨l,k,r,_,_,rfl,rfl⟩
      · refine ⟨le_rfl,?_⟩
        cases r with
        | nil => simpa only [List.map_nil,List.nil_append,due_read,sendRow] using hab
        | cons => exact le_rfl
      · exact ⟨le_rfl,(due_read r).ge⟩
    · exact fun c hc => (times M a b hab c hc).2.1
    · intro pre c rest he i q vals ho
      rcases location M a b pre c rest he with ⟨_,k,_,_,_,rfl,_⟩ | ⟨_,k,_,_,_,rfl,_⟩
      · cases hm : M i k <;> simp [sendRow,hm] at ho
      · cases hm : M k i <;> simp [readRow,hm] at ho
    · intro pre c rest he i j bits ho
      rcases location M a b pre c rest he with ⟨l,k,r,hl,hp,rfl,_⟩ | ⟨l,k,r,hl,hp,rfl,_⟩
      · cases hm : M i k with
        | none =>
          simp [sendRow,hm] at ho
          obtain ⟨rfl,rfl⟩ := ho
          exact dummy he i a hab
        | some bs =>
          simp [sendRow,hm] at ho
          obtain ⟨rfl,rfl⟩ := ho
          obtain ⟨ha,ht⟩ := cap i k bs hm
          refine ⟨Or.inr ha,ht,?_⟩
          rw [hp,sent M a b l (before hl).1 i k ha.ne, ite_eq_right_iff.mpr (fun h => False.elim ((before hl).2 h))]
          simp
      · cases hm : M k i with
        | none =>
          simp [readRow,hm] at ho
          obtain ⟨rfl,rfl⟩ := ho
          exact dummy he i b le_rfl
        | some bs => simp [readRow,hm] at ho
    · intro pre c rest he j i bits ho
      rcases location M a b pre c rest he with ⟨_,k,_,_,_,rfl,_⟩ | ⟨l,k,r,hl,hp,rfl,_⟩
      · cases hm : M j k <;> simp [sendRow,hm] at ho
      · cases hm : M k j with
        | none => simp [readRow,hm] at ho
        | some bs =>
          simp [readRow,hm] at ho
          obtain ⟨rfl,rfl⟩ := ho
          have hne := (cap k j bs hm).1.ne
          refine ⟨le_rfl,?_⟩
          rw [hp]
          simp only [consumed,posted,List.flatMap_append]
          change (consumed _ k j ++ consumed _ k j) ++ _ <+: posted _ k j ++ posted _ k j
          rw [(send_effect M a b _ k j).1, read M b l (before hl).1,
            sent M a b _ (List.nodup_finRange _) k j hne, read_effect M b l k j hne]
          simp [hm,message,(before hl).2,readRow]
  · exact hab
  · exact fun c hc => (times M a b hab c hc).1
  · exact fun c hc => (times M a b hab c hc).2.2.le
  · intro c hc i bits ho
    obtain ⟨pre,rest,he⟩ := List.append_of_mem hc
    rcases location M a b pre c rest he with ⟨_,k,_,_,_,rfl,_⟩ | ⟨_,k,_,_,_,rfl,_⟩
    · cases hm : M i k <;> simp [sendRow,hm] at ho
    · by_cases hk : k = i
      · subst k; simp [readRow,diag] at ho
      · cases hm : M k i <;> simp [readRow,hm,hk] at ho
  · intro i j hne
    simp only [rows, posted, consumed, List.flatMap_append]
    change posted _ i j ++ posted _ i j = consumed _ i j ++ consumed _ i j
    rw [sent M a b _ (List.nodup_finRange _) i j hne,read_effect M b _ i j hne,
      (send_effect M a b _ i j).1, read M b _ (List.nodup_finRange _) i j]
    simp

open LongTails.Algorithms.GraceRouting
open LongTails.Algorithms.LeonProtocol (Program)
open LeonTranscript (Trace)

variable {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r)

noncomputable def packets (D q : ℕ) (phase : Phase) (k : ℕ) (values : Fin p.n → Values) :
    Packets p := fun i j =>
  let xs := A.items D phase k i j
  if xs.isEmpty then none else some (pack q xs (values i))

lemma routed_block (g : Point p → p.Ω → Point p) (s : Samples p) (a : Time)
    (D q : ℕ) (phase : Phase) (k : ℕ) (values : Fin p.n → Values)
    (hs : ∀ i j, p.G.Adj i j → p.b i j = p.b j i) :
    Block g s a (a + A.frameTime q)
      (rows (packets A D q phase k values) a (a + A.frameTime q)) := by
  apply block _ _ _ _ _ le_self_add
  · intro i
    have he : A.items D phase k i i = [] := by
      by_contra hn
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hn
      exact (GraceRouting.sends_edge A (List.mem_filter.mp hx).2).ne rfl
    simp [packets,he]
  · intro i j bits ho
    unfold packets at ho
    dsimp only at ho
    split at ho
    · contradiction
    · rename_i h
      obtain rfl := Option.some.inj ho
      have hn : A.items D phase k i j ≠ [] := by simpa using h
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ hn
      have ha := GraceRouting.sends_edge A (List.mem_filter.mp hx).2
      refine ⟨ha,add_le_add_right ?_ _⟩
      simpa [duration,ha.ne,wire] using GraceRouting.wire_time A D q phase k i j (values i) hn (hs i j ha)

lemma send_trace (D q : ℕ) (phase : Phase) (k : ℕ) (v : Fin p.n → Values) (a b : Time)
    (i : Fin p.n) (next : Program p.base) (ids : List (Fin p.n)) {ops x}
    (h : Trace next ops x) :
    Trace (A.sendFrame D q phase k i (v i) next ids)
      ((ids.map fun j => (sendRow (packets A D q phase k v) a b j).op i) ++ ops) x := by
  induction ids with
  | nil => exact h
  | cons j js ih =>
    cases he : (A.items D phase k i j).isEmpty <;>
      simpa only [Routes.sendFrame,List.map_cons,List.cons_append,sendRow,packets,he,Bool.false_eq_true,↓reduceIte] using
        (Trace.send (i := if (A.items D phase k i j).isEmpty then i else j)
          (bits := if (A.items D phase k i j).isEmpty then [] else pack q (A.items D phase k i j) (v i)) ih)

noncomputable def afterReads (D q : ℕ) (phase : Phase) (k : ℕ) (v : Fin p.n → Values)
    (i : Fin p.n) : List (Fin p.n) → Values → Values
  | [], acc => acc
  | j :: js, acc =>
    let xs := A.items D phase k j i
    let next := if xs.isEmpty then acc else unpack phase q xs (wire (pack q xs (v j))) acc
    afterReads D q phase k v i js next

lemma receive_trace (D q : ℕ) (phase : Phase) (k : ℕ) (v : Fin p.n → Values) (b : Time)
    (i : Fin p.n) (next : Values → Program p.base) (ids : List (Fin p.n)) (acc : Values)
    {ops x} (h : Trace (next (afterReads A D q phase k v i ids acc)) ops x) :
    Trace (A.receiveFrame D q phase k i next ids acc)
      ((ids.map fun j => (readRow (packets A D q phase k v) b j).op i) ++ ops) x := by
  induction ids generalizing acc with
  | nil => exact h
  | cons j js ih =>
    cases he : (A.items D phase k j i).isEmpty
    · simp only [afterReads,he,Bool.false_eq_true,↓reduceIte] at h
      simpa only [Routes.receiveFrame,List.map_cons,List.cons_append,readRow,packets,he,Bool.false_eq_true,↓reduceIte] using
        (Trace.receive (i := j) (bits := wire (pack q (A.items D phase k j i) (v j)))
          (f := fun bits => A.receiveFrame D q phase k i next js
            (unpack phase q (A.items D phase k j i) bits acc)) (ih _ h))
    · simp only [afterReads,he,↓reduceIte] at h
      simpa only [Routes.receiveFrame,List.map_cons,List.cons_append,readRow,packets,he,Bool.false_eq_true,↓reduceIte] using
        (Trace.send (i := i) (bits := []) (ih _ h))

end LongTails.Proofs.GraceExchangeBlock
