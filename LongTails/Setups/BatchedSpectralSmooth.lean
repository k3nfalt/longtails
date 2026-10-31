import LongTails.Setups.FiniteVarianceSpectralSmooth

namespace LongTails.Setups.BatchedSpectralSmooth

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar

structure Public where
  m : ℕ
  n : ℕ
  L : ℝ
  Δ : ℝ
  s : ℝ
  ε : ℝ
  x0 : Space m n

noncomputable def batchMean {m n : ℕ} (B : ℕ) (reply : ℕ → Space m n) (t : ℕ) : Space m n :=
  (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, reply (B * t + j)

noncomputable def batchedIterate {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) (B : ℕ)
    (x0 : Space m n) (reply : ℕ → Space m n) : ℕ → Space m n
  | 0 => x0
  | t + 1 => batchedIterate direction η B x0 reply t - η • direction (batchMean B reply t)

def FollowsBatched {m n : ℕ} (direction : Space m n → Space m n) (η : ℝ) (B T : ℕ)
    (x0 : Space m n) (A : Algorithm (Space m n) (Space m n) (Space m n)) : Prop :=
  ∃ draw : A.Seed → Fin (T + 1), Measurable draw ∧
    Measure.map draw (A.law : Measure _) = (PMF.uniformOfFintype (Fin (T + 1))).toMeasure ∧
    ∀ seed reply,
      let state := LongTails.Setups.FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = batchedIterate direction η B x0 reply t) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        batchedIterate direction η B x0 reply (draw seed)

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := Space p.m p.n → ℝ
  Query p := Space p.m p.n
  Reply p := Space p.m p.n
  Output p := Space p.m p.n
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.s ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ p.L * spectralNorm (x - y)) ∧
    (∃ fmin : ℝ, (∀ x, fmin ≤ f x) ∧ f p.x0 - fmin ≤ p.Δ) ∧
    ∃ (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f p.s)
      (P : ProbabilityMeasure (ℕ → model.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure model.Ω) (P : Measure _) ∧
      O = { Seed := fun _ => model.Ω
            law := P
            answer := fun _ (_, x) ω => model.sample x ω }
  successful p f output P :=
    Measurable output ∧
      Integrable (fun ω => nuclearNorm (gradient f (output ω))) (P : Measure _) ∧
      (∫ ω, nuclearNorm (gradient f (output ω)) ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm p A :=
    ∃ (η : ℝ) (B T : ℕ), 0 < η ∧ 0 < B ∧ FollowsBatched polar η B T p.x0 A

end LongTails.Setups.BatchedSpectralSmooth
