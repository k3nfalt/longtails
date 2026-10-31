import LongTails.Setups.MomentumSpectralSmooth

namespace LongTails.Algorithms.MomentumDirection

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar

structure MomentumProgress (m n : ℕ) where
  step : ℕ
  slot : ℕ
  point : Space m n
  momentum : Space m n
  acc : Space m n
  saved : Space m n

noncomputable def advanceMomentum {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ)
    (B : ℕ) (selected : ℕ) (st : MomentumProgress m n) (g : Space m n) : MomentumProgress m n :=
  if st.slot + 1 < B then
    { st with slot := st.slot + 1, acc := st.acc + g }
  else
    let M := β • st.momentum + (1 - β) • ((1 / (B : ℝ)) • (st.acc + g))
    let x := st.point - η • direction M
    ⟨st.step + 1, 0, x, M, 0, if st.step + 1 = selected then x else st.saved⟩

noncomputable def momentumMethod {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ)
    (B T : ℕ) (x0 : Space m n) : Algorithm (Space m n) (Space m n) (Space m n) where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := Fin (T + 1) × MomentumProgress m n
  initial k := (k, ⟨0, 0, x0, 0, 0, x0⟩)
  query state := (0, state.2.point)
  update state g := (state.1, advanceMomentum direction β η B state.1.val state.2 g)
  output state := state.2.saved

noncomputable def muonMomentum {m n : ℕ} (β η : ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  momentumMethod polar β η B T x0

noncomputable def sgdMomentum {m n : ℕ} (β η : ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  momentumMethod id β η B T x0

noncomputable def nsgdMomentum {m n : ℕ} (β η : ℝ) (B T : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  momentumMethod LongTails.Setups.MomentumSpectralSmooth.frobeniusNormalize β η B T x0

end LongTails.Algorithms.MomentumDirection
