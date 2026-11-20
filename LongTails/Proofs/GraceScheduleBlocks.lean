import LongTails.Proofs.GraceScheduledExecution

namespace LongTails.Proofs.GraceScheduleBlocks

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LeonReservations (Frame due usedCount posted consumed)
open GraceReservations (Certified)

variable {p : Params}

def shift (s : Samples p) (offset : Fin p.n → ℕ) : Samples p :=
  fun i k => s i (offset i + k)

structure Block (g : Point p → p.Ω → Point p) (s : Samples p)
    (a b : Time) (rows : List (Frame p.base)) : Prop extends Certified g s b rows where
  span : a ≤ b
  start : ∀ c ∈ rows, a ≤ c.start
  delivery : ∀ c ∈ rows, c.delivery ≤ b
  noLocalReads : ∀ c ∈ rows, ∀ i bits, c.op i ≠ .receive i bits
  matched : ∀ i j, i ≠ j → posted rows i j = consumed rows i j

lemma locate {α : Type*} (xs ys pre : List α) (c : α) (rest : List α)
    (h : xs ++ ys = pre ++ c :: rest) :
    (∃ tail, xs = pre ++ c :: tail ∧ rest = tail ++ ys) ∨
      (∃ mid, ys = mid ++ c :: rest ∧ pre = xs ++ mid) := by
  induction xs generalizing pre with
  | nil => exact Or.inr ⟨pre, h, rfl⟩
  | cons x xs ih =>
    cases pre with
    | nil =>
      obtain ⟨hx, hr⟩ := List.cons.inj h
      exact Or.inl ⟨xs, by simp [hx], hr.symm⟩
    | cons v pre =>
      obtain ⟨rfl, ht⟩ := List.cons.inj h
      obtain ⟨tail, he, hr⟩ | ⟨mid, he, hp⟩ := ih pre ht
      · exact Or.inl ⟨tail, by simp [he], hr⟩
      · exact Or.inr ⟨mid, he, by simp [hp]⟩

lemma used_append (xs ys : List (Frame p.base)) (i : Fin p.n) :
    usedCount (xs ++ ys) i = usedCount xs i + usedCount ys i := by simp [usedCount]

lemma posted_deadline {g : Point p → p.Ω → Point p} {s : Samples p} {a b : Time}
    {xs : List (Frame p.base)} (hx : Block g s a b xs) (i j : Fin p.n) (msg)
    (hm : msg ∈ posted xs i j) : msg.1 ≤ b := by
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp hm
  unfold LeonReservations.sends at he
  cases ho : c.op i <;> simp [ho] at he
  rw [he.2]
  exact hx.delivery c hc

lemma append {g : Point p → p.Ω → Point p} {s : Samples p} {a b d : Time}
    {xs ys : List (Frame p.base)} (h₁ : Block g s a b xs)
    (h₂ : Block g (shift s (usedCount xs)) b d ys) : Block g s a d (xs ++ ys) := by
  have mem (pre : List (Frame p.base)) (c : Frame p.base) (tail : List (Frame p.base)) :
      c ∈ pre ++ c :: tail := by simp
  have hb : b ≤ due d ys false := by
    cases he : ys with
    | nil => exact h₂.span
    | cons c rest => exact h₂.start c (by simp [he])
  constructor
  · constructor
    · intro pre c rest he
      obtain ⟨tail, hx, rfl⟩ | ⟨mid,hy,_⟩ := locate _ _ _ _ _ he
      · obtain ⟨hs,hf⟩ := h₁.ordered _ _ _ hx
        refine ⟨hs,hf.trans ?_⟩
        cases tail with
        | nil => exact hb
        | cons => rfl
      · exact h₂.ordered _ _ _ hy
    · intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact (h₁.bounded c h).trans h₂.span
      · exact h₂.bounded c h
    · intro pre c rest he i q vals ho
      obtain ⟨tail, hx, _⟩ | ⟨mid,hy,rfl⟩ := locate _ _ _ _ _ he
      · exact h₁.sample _ _ _ hx i q vals ho
      · simpa [shift, used_append, Nat.add_assoc] using h₂.sample _ _ _ hy i q vals ho
    · intro pre c rest he i j bits ho
      obtain ⟨tail,hx,_⟩ | ⟨mid,hy,rfl⟩ := locate _ _ _ _ _ he
      · exact h₁.send _ _ _ hx i j bits ho
      · obtain ⟨hadj,hstart,hprevious⟩ := h₂.send _ _ _ hy i j bits ho
        refine ⟨hadj,hstart,?_⟩
        intro msg hm
        rw [posted, List.flatMap_append] at hm
        obtain hm | hm := List.mem_append.mp hm
        · have htime := (posted_deadline h₁ i j msg hm).trans (h₂.start c (hy ▸ mem ..))
          exact (add_le_add_left htime _).trans hstart
        · exact hprevious msg hm
    · intro pre c rest he j i bits ho
      obtain ⟨tail,hx,_⟩ | ⟨mid,hy,rfl⟩ := locate _ _ _ _ _ he
      · exact h₁.receive _ _ _ hx j i bits ho
      · obtain ⟨ht,more,hm⟩ := h₂.receive _ _ _ hy j i bits ho
        refine ⟨ht,more,?_⟩
        have hne : i ≠ j := by intro he; subst i; exact h₂.noLocalReads c (hy ▸ mem ..) j bits ho
        simp only [posted, consumed, List.flatMap_append, List.append_assoc] at hm ⊢
        change consumed xs i j ++ _ = posted xs i j ++ _
        rw [h₁.matched i j hne]
        simp_all [consumed]
  · exact h₁.span.trans h₂.span
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact h₁.start c h
    · exact h₁.span.trans (h₂.start c h)
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact (h₁.delivery c h).trans h₂.span
    · exact h₂.delivery c h
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact h₁.noLocalReads c h
    · exact h₂.noLocalReads c h
  · intro i j hne
    simp only [posted, consumed, List.flatMap_append]
    change (posted xs i j ++ posted ys i j) = (consumed xs i j ++ consumed ys i j)
    rw [h₁.matched i j hne, h₂.matched i j hne]

end LongTails.Proofs.GraceScheduleBlocks
