import LongTails.Setups.BatchedSpectralSmooth

namespace LongTails.Setups.MomentumSpectralSmooth

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar

structure Public where
  m : ℕ
  n : ℕ
  L : ℝ
  Δ : ℝ
  s : ℝ
  ε : ℝ
  β : ℝ
  x0 : Space m n

def Public.toBase (p : Public) : BatchedSpectralSmooth.Public :=
  ⟨p.m, p.n, p.L, p.Δ, p.s, p.ε, p.x0⟩

noncomputable def momentumIterate {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ) (B : ℕ)
    (x0 : Space m n) (reply : ℕ → Space m n) : ℕ → Space m n × Space m n
  | 0 => (x0, 0)
  | t + 1 =>
      let M := β • (momentumIterate direction β η B x0 reply t).2 +
        (1 - β) • BatchedSpectralSmooth.batchMean B reply t
      ((momentumIterate direction β η B x0 reply t).1 - η • direction M, M)

def FollowsMomentum {m n : ℕ} (direction : Space m n → Space m n) (β η : ℝ) (B T : ℕ)
    (x0 : Space m n) (A : Algorithm (Space m n) (Space m n) (Space m n)) : Prop :=
  ∃ draw : A.Seed → Fin (T + 1), Measurable draw ∧
    Measure.map draw (A.law : Measure _) = (PMF.uniformOfFintype (Fin (T + 1))).toMeasure ∧
    ∀ seed reply,
      let state := FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = (momentumIterate direction β η B x0 reply t).1) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        (momentumIterate direction β η B x0 reply (draw seed)).1

noncomputable def frobeniusNormalize {m n : ℕ} (X : Space m n) : Space m n := ‖X‖⁻¹ • X

def MomentumLower (p : Public) (direction : Space p.m p.n → Space p.m p.n) (q : ℕ) (C : ℝ) :
    Prop :=
  2 ≤ min p.m p.n → 1024 * p.ε ^ 2 ≤ p.L * p.Δ →
  ∀ (η : ℝ), 0 < η → ∀ (B T : ℕ), 0 < B →
    ∀ (A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)),
      FollowsMomentum direction p.β η B T p.x0 A →
      ∃ (f : Space p.m p.n → ℝ) (O : Oracle (Space p.m p.n) (Space p.m p.n)),
        BatchedSpectralSmooth.spec.admissible p.toBase f O ∧
        (BatchedSpectralSmooth.spec.successful p.toBase f
          (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => B * (T + 1)) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
          ((p.n - min p.m p.n + 1 : ℕ) : ℝ) ≤ 4 * (B * (T + 1) : ℝ) ^ 2 ∨
            (min p.m p.n - 1 : ℕ) * p.L * p.Δ * p.s ^ 2 * (1 - p.β) ^ q ≤
              C * p.ε ^ 4 * (B * (T + 1)))

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := Space p.m p.n → ℝ
  Query p := Space p.m p.n
  Reply p := Space p.m p.n
  Output p := Space p.m p.n
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.s ∧ 0 < p.ε ∧ 0 ≤ p.β ∧ p.β < 1
  admissible p f O := BatchedSpectralSmooth.spec.admissible p.toBase f O
  successful p f output P :=
    BatchedSpectralSmooth.spec.successful p.toBase f output P ∧
      MomentumLower p id 3 (2 ^ 21) ∧ MomentumLower p frobeniusNormalize 3 (2 ^ 21)
  allowedAlgorithm p A :=
    ∃ (η : ℝ) (B T : ℕ), 0 < η ∧ 0 < B ∧ FollowsMomentum polar p.β η B T p.x0 A

end LongTails.Setups.MomentumSpectralSmooth
