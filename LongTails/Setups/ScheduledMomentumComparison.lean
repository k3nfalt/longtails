import LongTails.Setups.BatchedSpectralSmooth

namespace LongTails.Setups.ScheduledMomentumComparison

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar

abbrev Public := BatchedSpectralSmooth.Public

noncomputable def sgdDirection {m n : ℕ} (X : Space m n) : Space m n := X

noncomputable def nsgdDirection {m n : ℕ} (X : Space m n) : Space m n := ‖X‖⁻¹ • X

noncomputable def momentumIterate {m n : ℕ} (direction : Space m n → Space m n) (β : ℝ)
    (η : ℕ → ℝ) (B : ℕ) (x0 : Space m n) (reply : ℕ → Space m n) : ℕ → Space m n × Space m n
  | 0 => (x0, 0)
  | t + 1 =>
      let M := β • (momentumIterate direction β η B x0 reply t).2 +
        (1 - β) • BatchedSpectralSmooth.batchMean B reply t
      ((momentumIterate direction β η B x0 reply t).1 - η t • direction M, M)

def FollowsScheduledMomentum {m n : ℕ} (direction : Space m n → Space m n) (β : ℝ)
    (η : ℕ → ℝ) (B T : ℕ) (x0 : Space m n)
    (A : Algorithm (Space m n) (Space m n) (Space m n)) : Prop :=
  ∃ draw : A.Seed → Fin (T + 1), Measurable draw ∧
    Measure.map draw (A.law : Measure _) = (PMF.uniformOfFintype (Fin (T + 1))).toMeasure ∧
    ∀ seed reply,
      let state := FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = (momentumIterate direction β η B x0 reply t).1) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        (momentumIterate direction β η B x0 reply (draw seed)).1

def SgdMomentumLower (p : Public) : Prop :=
  ∀ (β : ℝ), 0 ≤ β → β < 1 → ∀ (η : ℕ → ℝ) (B T : ℕ), 0 < B →
    ∀ (A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)),
      FollowsScheduledMomentum sgdDirection β η B T p.x0 A →
      ∃ (f : Space p.m p.n → ℝ) (O : Oracle (Space p.m p.n) (Space p.m p.n)),
        BatchedSpectralSmooth.spec.admissible p f O ∧
        (BatchedSpectralSmooth.spec.successful p f
          (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => B * (T + 1)) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
          (1 - β) * (min p.m p.n - 1 : ℕ) * p.L * p.Δ * p.s ≤ 81 * p.ε ^ 3 * (B * (T + 1)))

def NsgdMomentumLower (p : Public) : Prop :=
  ∀ (β : ℝ), 0 ≤ β → β < 1 → ∀ (η : ℕ → ℝ) (B T : ℕ), 0 < B →
    ∀ (A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)),
      FollowsScheduledMomentum nsgdDirection β η B T p.x0 A →
      ∃ (f : Space p.m p.n → ℝ) (O : Oracle (Space p.m p.n) (Space p.m p.n)),
        BatchedSpectralSmooth.spec.admissible p f O ∧
        (BatchedSpectralSmooth.spec.successful p f
          (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => B * (T + 1)) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
          (1 - β) * (min p.m p.n - 1 : ℕ) * p.L * p.Δ * p.s ≤
              288 * p.ε ^ 3 * (2 + Real.log (1 + p.s * Real.sqrt (min p.m p.n) / p.ε)) *
                (B * (T + 1)) ∨
            (1 - β) ^ 2 * (min p.m p.n - 1 : ℕ) * p.s ^ 2 ≤ 24 * p.ε ^ 2 * (B * (T + 1)))

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := Space p.m p.n → ℝ
  Query p := Space p.m p.n
  Reply p := Space p.m p.n
  Output p := Space p.m p.n
  publicInput p := p
  valid p := 2 ≤ min p.m p.n ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.s ∧ 0 < p.ε ∧ 72 * p.ε ^ 2 ≤ p.L * p.Δ
  admissible p f O := BatchedSpectralSmooth.spec.admissible p f O
  successful p f output P :=
    BatchedSpectralSmooth.spec.successful p f output P ∧ SgdMomentumLower p ∧ NsgdMomentumLower p
  allowedAlgorithm p A := BatchedSpectralSmooth.spec.allowedAlgorithm p A

end LongTails.Setups.ScheduledMomentumComparison
