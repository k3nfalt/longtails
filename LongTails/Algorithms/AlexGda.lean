import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.BlockSaddle

universe u v

structure AlexState (E : Type u) (F : Type v) where
  phase : Bool
  n : ℕ
  x : E
  y : F
  v : F
  g : E
  best : E × F
  bestVal : ℝ

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def alexGda (γ δ α β : ℝ) (x0 : E) (y0 : F) :
    Algorithm ((E × F) ⊕ (E × F)) (E ⊕ F) (E × F) where
  State := AlexState E F
  initial := fun _ => ⟨false, 0, x0, y0, 0, 0, (x0, y0), 0⟩
  query :=  fun st => (0,
    if st.phase then Sum.inr (st.x - (γ * α) • st.g, st.y)
    else Sum.inl (st.x, st.y + ((δ - 1) * β) • st.v))
  update := fun st r =>
    if st.phase then
      ⟨false, st.n + 1, st.x - α • st.g, st.y + β • Sum.elim (fun _ => (0 : F)) id r,
        Sum.elim (fun _ => (0 : F)) id r, 0,
        if st.n = 0 ∨
            ‖st.g‖ ^ 2 + ‖Sum.elim (fun _ => (0 : F)) id r‖ ^ 2 + ‖st.v‖ ^ 2 < st.bestVal then
          (st.x, st.y) else st.best,
        if st.n = 0 ∨
            ‖st.g‖ ^ 2 + ‖Sum.elim (fun _ => (0 : F)) id r‖ ^ 2 + ‖st.v‖ ^ 2 < st.bestVal then
          ‖st.g‖ ^ 2 + ‖Sum.elim (fun _ => (0 : F)) id r‖ ^ 2 + ‖st.v‖ ^ 2 else st.bestVal⟩
    else ⟨true, st.n, st.x, st.y, st.v, Sum.elim id (fun _ => (0 : E)) r, st.best, st.bestVal⟩
  output := fun st => st.best

end OracleTemplate.BlockSaddle
