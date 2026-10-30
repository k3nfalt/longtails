import LongTails.Setups.ScheduledMomentumComparison

namespace LongTails.Algorithms.ScheduledMomentum

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar

structure Progress (m n : ℕ) where
  step : ℕ
  slot : ℕ
  point : Space m n
  momentum : Space m n
  acc : Space m n
  saved : Space m n

noncomputable def advanceProgress {m n : ℕ} (direction : Space m n → Space m n) (β : ℝ)
    (η : ℕ → ℝ) (B : ℕ) (selected : ℕ) (st : Progress m n) (g : Space m n) : Progress m n :=
  if st.slot + 1 < B then
    { st with slot := st.slot + 1, acc := st.acc + g }
  else
    let M := β • st.momentum + (1 - β) • ((1 / (B : ℝ)) • (st.acc + g))
    let x := st.point - η st.step • direction M
    ⟨st.step + 1, 0, x, M, 0, if st.step + 1 = selected then x else st.saved⟩

noncomputable def method {m n : ℕ} (direction : Space m n → Space m n) (β : ℝ) (η : ℕ → ℝ)
    (B T : ℕ) (x0 : Space m n) : Algorithm (Space m n) (Space m n) (Space m n) where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := Fin (T + 1) × Progress m n
  initial k := (k, ⟨0, 0, x0, 0, 0, x0⟩)
  query state := (0, state.2.point)
  update state g := (state.1, advanceProgress direction β η B state.1.val state.2 g)
  output state := state.2.saved

noncomputable def sgdMomentum {m n : ℕ} (β : ℝ) (η : ℕ → ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  method LongTails.Setups.ScheduledMomentumComparison.sgdDirection β η B T x0

noncomputable def nsgdMomentum {m n : ℕ} (β : ℝ) (η : ℕ → ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  method LongTails.Setups.ScheduledMomentumComparison.nsgdDirection β η B T x0

end LongTails.Algorithms.ScheduledMomentum
