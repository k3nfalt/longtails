import LongTails.Algorithms.AuxiliaryPlan
import LongTails.Algorithms.GuardedMetricAcceleration

namespace LongTails.Algorithms.AuxiliarySimilarity

open scoped RealInnerProductSpace
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.GuardedMetricAcceleration

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Tuning where
  α : ℝ
  db : ℝ
  M : ℝ
  a : ℝ
  ε : ℝ
  η : ℝ
  N : ℕ
  J : ℕ
  T : ℕ
  K : ℕ

abbrev Plan (E : Type) (β : Type) := TwoPlan E (ℝ × E) β

abbrev Rec (E : Type) := E × ℝ × E

noncomputable def psiRec (t : Tuning) (y v z : E) (r : ℝ × E) : Rec E :=
  (z, r.1 + t.α * ‖z - y‖ ^ 2 + t.db * ‖z - v‖ ^ 2 + t.db * ‖z‖ ^ 2,
    r.2 + (2 * t.α) • (z - y) + (2 * t.db) • (z - v) + (2 * t.db) • z)

noncomputable def tRec (t : Tuning) (y v x : E) (r : ℝ × E) : Rec E :=
  (x, r.1 + t.α * ‖x - y‖ ^ 2 + t.db * ‖x - v‖ ^ 2,
    r.2 + (2 * t.α) • (x - y) + (2 * t.db) • (x - v))

noncomputable def gRec (t : Tuning) (v : E) (q : Rec E) : Rec E :=
  (q.1, q.2.1 - t.db * ‖q.1 - v‖ ^ 2, q.2.2 - (2 * t.db) • (q.1 - v))

noncomputable def recBreg (w u : Rec E) : ℝ := w.2.1 - u.2.1 - ⟪u.2.2, w.1 - u.1⟫

noncomputable def firstBad (n : ℕ) (bad : ℕ → Prop) : Option ℕ := by
  classical
  exact if h : ∃ i, i < n ∧ bad i then some (Nat.find h) else none

structure Book (E : Type) where
  best : E × ℝ
  cert : Option (E × E)

noncomputable def Book.note (bk : Book E) (x : E) (fx : ℝ) : Book E :=
  { bk with best := if fx < bk.best.2 then (x, fx) else bk.best }

def Book.flag (bk : Book E) (c : Option (E × E)) : Book E :=
  { bk with cert := match bk.cert with | some c₀ => some c₀ | none => c }

structure CheapState (E : Type) where
  k : ℕ
  recs : ℕ → Rec E

noncomputable def cheapStep (t : Tuning) (y v b : E) (r0 : Rec E) (st : CheapState E) :
    Plan E (CheapState E) := do
  let z := (st.recs st.k).1
  let z' := z - (1 / t.M) • (b + (st.recs st.k).2.2 - r0.2.2)
  let r ← TwoPlan.call 1 z'
  pure { k := st.k + 1, recs := Function.update st.recs (st.k + 1) (psiRec t y v z' r) }

noncomputable def cheapGD (t : Tuning) (y v xbar b : E) :
    Plan E (E × Option (E × E) × Rec E) := do
  let r ← TwoPlan.call 1 xbar
  let r0 := psiRec t y v xbar r
  let st ← TwoPlan.loop t.N (cheapStep t y v b r0) ⟨0, fun _ => r0⟩
  let w := st.recs t.N
  let bad := fun i => recBreg w (st.recs i) < 3 * t.db / 2 * ‖w.1 - (st.recs i).1‖ ^ 2
  pure ((st.recs (t.N - 1)).1, (firstBad t.N bad).map (fun i => (w.1, (st.recs i).1)), r0)

structure DaneState (E : Type) where
  k : ℕ
  recs : ℕ → Rec E
  prec : ℕ → Rec E
  book : Book E

noncomputable def daneStep (t : Tuning) (y v : E) (st : DaneState E) : Plan E (DaneState E) := do
  let cur := st.recs st.k
  let out ← cheapGD t y v cur.1 cur.2.2
  let r ← TwoPlan.call 0 out.1
  pure { k := st.k + 1,
         recs := Function.update st.recs (st.k + 1) (tRec t y v out.1 r),
         prec := Function.update st.prec st.k out.2.2,
         book := (st.book.flag out.2.1).note out.1 r.1 }

noncomputable def dane (t : Tuning) (y v s : E) (bk : Book E) : Plan E (Rec E × Book E) := do
  let r ← TwoPlan.call 0 s
  let r0 := tRec t y v s r
  let st ← TwoPlan.loop (t.J + 1) (daneStep t y v) ⟨0, fun _ => r0, fun _ => r0, bk.note s r.1⟩
  let wq ← TwoPlan.call 1 (st.recs (t.J + 1)).1
  let pw := psiRec t y v (st.recs (t.J + 1)).1 wq
  let bad := fun j => recBreg (st.recs (t.J + 1)) (st.recs j) < 2 / 5 * recBreg pw (st.prec j)
  let c := (firstBad (t.J + 1) bad).map (fun j => ((st.recs (t.J + 1)).1, (st.recs j).1))
  pure (st.recs t.J, st.book.flag c)

structure EpochState (E : Type) where
  k : ℕ
  x : E
  z : E
  recs : ℕ → Rec E
  book : Book E

noncomputable def guardPair (t : Tuning) (w u : Rec E) : Option (E × E) := by
  classical
  exact if recBreg w u < t.α / 2 * ‖w.1 - u.1‖ ^ 2 then some (w.1, u.1) else none

noncomputable def appaStep (t : Tuning) (y : E) (gy : Rec E) (st : EpochState E) :
    Plan E (EpochState E) := do
  let v := extrapolate t.a st.x st.z
  let out ← dane t y v st.x st.book
  let rg := gRec t v out.1
  let G := (2 * t.db) • (v - rg.1)
  let c1 := guardPair t (st.recs st.k) rg
  let c2 := guardPair t gy rg
  pure { k := st.k + 1, x := rg.1, z := centerStep t.a (t.α / 2) v st.z G,
         recs := Function.update st.recs (st.k + 1) rg, book := (out.2.flag c1).flag c2 }

noncomputable def exploit (t : Tuning) (y : E) (bk : Book E) : Plan E (Book E) :=
  match bk.cert with
  | none => pure bk
  | some (u, w) => do
      let ru ← TwoPlan.call 0 u
      let rw ← TwoPlan.call 0 w
      let d := ‖u - w‖⁻¹ • (u - w)
      let r1 ← TwoPlan.call 0 (y + t.η • d)
      let r2 ← TwoPlan.call 0 (y - t.η • d)
      pure ((((bk.note u ru.1).note w rw.1).note (y + t.η • d) r1.1).note (y - t.η • d) r2.1)

noncomputable def epoch (t : Tuning) (y : E) : Plan E E := do
  let r ← TwoPlan.call 0 y
  if ‖r.2‖ ≤ t.ε then pure y else do
    let gy : Rec E := (y, r.1, r.2)
    let st ← TwoPlan.loop t.T (appaStep t y gy)
      ⟨0, y, y, fun _ => gy, { best := (y, r.1), cert := none }⟩
    let out ← dane t y st.x st.x st.book
    let rf := gRec t st.x out.1
    let bad := fun i => recBreg rf (st.recs (i + 1)) < t.α / 2 * ‖rf.1 - (st.recs (i + 1)).1‖ ^ 2
    let c := (firstBad t.T bad).map (fun i => (rf.1, (st.recs (i + 1)).1))
    let r' ← TwoPlan.call 0 rf.1
    if ‖r'.2‖ ≤ t.ε then pure rf.1 else do
      let bk ← exploit t y (out.2.flag c)
      pure bk.best.1

noncomputable def method (t : Tuning) (x0 : E) : Plan E E :=
  TwoPlan.loop t.K (epoch t) x0

noncomputable def tuning (L δ ρ Δ ε : ℝ) : Tuning where
  α := Real.sqrt (ρ * ε) / 8
  db := max δ (Real.sqrt (ρ * ε) / 8)
  M := L + 2 * (Real.sqrt (ρ * ε) / 8) + 4 * max δ (Real.sqrt (ρ * ε) / 8)
  a := Real.sqrt (Real.sqrt (ρ * ε) / 8 / (4 * max δ (Real.sqrt (ρ * ε) / 8)))
  ε := ε
  η := Real.sqrt (ρ * ε) / 8 / (8 * ρ)
  N := ⌈(L / δ + 6) * Real.log (2 ^ 110 * (1 + (L + δ) / Real.sqrt (ρ * ε)) ^ 10 *
    (1 + Δ * Real.sqrt (ρ * ε) / ε ^ 2))⌉₊ + 2
  J := ⌈15 * Real.log (400 * (1 + (L + δ) / Real.sqrt (ρ * ε)))⌉₊
  T := ⌈6 * Real.sqrt (1 + δ / Real.sqrt (ρ * ε)) * Real.log (8 + 8 * δ / Real.sqrt (ρ * ε))⌉₊
  K := ⌈2 ^ 19 * Δ * Real.sqrt (ρ * ε) / ε ^ 2⌉₊ + 1

end LongTails.Algorithms.AuxiliarySimilarity
