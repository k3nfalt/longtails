import LongTails.Setups.BatchedSpectralSmooth

namespace LongTails.Algorithms.BatchedDirection

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar

structure Progress (m n : ℕ) where
  step : ℕ
  slot : ℕ
  point : Space m n
  acc : Space m n
  saved : Space m n

noncomputable def advanceProgress {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) (B : ℕ)
    (selected : ℕ) (st : Progress m n) (g : Space m n) : Progress m n :=
  if st.slot + 1 < B then
    { st with slot := st.slot + 1, acc := st.acc + g }
  else
    let x := st.point - η • direction ((1 / (B : ℝ)) • (st.acc + g))
    ⟨st.step + 1, 0, x, 0, if st.step + 1 = selected then x else st.saved⟩

noncomputable def method {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) (B T : ℕ)
    (x0 : Space m n) : Algorithm (Space m n) (Space m n) (Space m n) where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := Fin (T + 1) × Progress m n
  initial k := (k, ⟨0, 0, x0, 0, x0⟩)
  query state := (0, state.2.point)
  update state g := (state.1, advanceProgress direction η B state.1.val state.2 g)
  output state := state.2.saved

noncomputable def frobeniusNormalize {m n : ℕ} (X : Space m n) : Space m n := ‖X‖⁻¹ • X

noncomputable def muon {m n : ℕ} (η : ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  method polar η B T x0

noncomputable def sgd {m n : ℕ} (η : ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  method id η B T x0

noncomputable def nsgd {m n : ℕ} (η : ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  method frobeniusNormalize η B T x0

end LongTails.Algorithms.BatchedDirection
