import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.ArrowHurwicz

universe u v

structure AHState (E : Type u) (F : Type v) where
  phase : ℕ
  x : E
  y : F
  v : E
  w : F
  sx : E
  sy : F
  n : ℕ

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def arrowHurwicz (η : ℝ) (x0 : E) (y0 : F) :
    Algorithm ((F ⊕ E) ⊕ ((E × ℝ) ⊕ (F × ℝ))) (E ⊕ F) (E × F) where
  State := AHState E F
  initial := fun _ => ⟨0, x0, y0, 0, 0, 0, 0, 0⟩
  query :=  fun st => (0,
    if st.phase = 0 then Sum.inl (Sum.inl st.y)
    else if st.phase = 1 then Sum.inr (Sum.inl (st.x - η • st.v, η))
    else if st.phase = 2 then Sum.inl (Sum.inr st.x)
    else Sum.inr (Sum.inr (st.y + η • st.w, η)))
  update := fun st r =>
    if st.phase = 0 then ⟨1, st.x, st.y, Sum.elim id (fun _ => 0) r, st.w, st.sx, st.sy, st.n⟩
    else if st.phase = 1 then ⟨2, Sum.elim id (fun _ => 0) r, st.y, st.v, st.w, st.sx, st.sy, st.n⟩
    else if st.phase = 2 then ⟨3, st.x, st.y, st.v, Sum.elim (fun _ => 0) id r, st.sx, st.sy, st.n⟩
    else ⟨0, st.x, Sum.elim (fun _ => 0) id r, st.v, st.w, st.sx + st.x,
      st.sy + Sum.elim (fun _ => 0) id r, st.n + 1⟩
  output := fun st =>
    if st.n = 0 then (st.x, st.y) else (((st.n : ℝ))⁻¹ • st.sx, ((st.n : ℝ))⁻¹ • st.sy)

end OracleTemplate.ArrowHurwicz
