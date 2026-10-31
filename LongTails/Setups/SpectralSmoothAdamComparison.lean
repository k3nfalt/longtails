import LongTails.Setups.BatchedSpectralSmooth

namespace LongTails.Setups.SpectralSmoothAdamComparison

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar

structure Public where
  r : ℕ
  L : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space r r

def Public.toBase (p : Public) : BatchedSpectralSmooth.Public :=
  ⟨p.r, p.r, p.L, p.Δ, p.ε, p.ε, p.x0⟩

structure AdamTuning where
  η : ℝ
  β₁ : ℝ
  β₂ : ℝ
  τ : ℝ

def AdamTuning.Valid (a : AdamTuning) : Prop :=
  0 < a.η ∧ 0 ≤ a.β₁ ∧ a.β₁ < 1 ∧ 0 ≤ a.β₂ ∧ a.β₂ < 1 ∧
    a.β₁ ^ 2 ≤ a.β₂ ∧ 0 ≤ a.τ

noncomputable def firstMoment {r : ℕ} (β : ℝ) (B : ℕ)
    (reply : ℕ → Space r r) : ℕ → Space r r
  | 0 => 0
  | t + 1 => β • firstMoment β B reply t +
      (1 - β) • BatchedSpectralSmooth.batchMean B reply t

noncomputable def secondMoment {r : ℕ} (β : ℝ) (B : ℕ)
    (reply : ℕ → Space r r) : ℕ → Space r r
  | 0 => 0
  | t + 1 => β • secondMoment β B reply t +
      (1 - β) • (WithLp.toLp 2 (fun i => (BatchedSpectralSmooth.batchMean B reply t i) ^ 2))

noncomputable def adamDirection {r : ℕ} (a : AdamTuning) (B : ℕ)
    (reply : ℕ → Space r r) (t : ℕ) : Space r r := WithLp.toLp 2 fun i =>
  (firstMoment a.β₁ B reply (t + 1) i / (1 - a.β₁ ^ (t + 1))) /
    (Real.sqrt (secondMoment a.β₂ B reply (t + 1) i / (1 - a.β₂ ^ (t + 1))) + a.τ)

noncomputable def adamIterate {r : ℕ} (a : AdamTuning) (B : ℕ)
    (x0 : Space r r) (reply : ℕ → Space r r) : ℕ → Space r r
  | 0 => x0
  | t + 1 => adamIterate a B x0 reply t - a.η • adamDirection a B reply t

def FollowsAdam {r : ℕ} (a : AdamTuning) (B T : ℕ) (x0 : Space r r)
    (A : Algorithm (Space r r) (Space r r) (Space r r)) : Prop :=
  ∃ draw : A.Seed → Fin (T + 1), Measurable draw ∧
    Measure.map draw (A.law : Measure _) = (PMF.uniformOfFintype (Fin (T + 1))).toMeasure ∧
    ∀ seed reply,
      let state := FiniteVarianceSpectralSmooth.replyState A seed reply
      (∀ t j, t ≤ T → j < B →
        (A.query (state (B * t + j))).2 = adamIterate a B x0 reply t) ∧
      ∀ extra, A.output (state (B * (T + 1) + extra)) =
        adamIterate a B x0 reply (draw seed)

def AdamLower (p : Public) : Prop :=
  ∀ (a : AdamTuning), a.Valid → ∀ (B T : ℕ), 0 < B →
    ∀ (A : Algorithm (Space p.r p.r) (Space p.r p.r) (Space p.r p.r)),
      FollowsAdam a B T p.x0 A →
      ∃ (f : Space p.r p.r → ℝ) (O : Oracle (Space p.r p.r) (Space p.r p.r)),
        BatchedSpectralSmooth.spec.admissible p.toBase f O ∧
        (BatchedSpectralSmooth.spec.successful p.toBase f
          (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => B * (T + 1)) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
          (p.r - 1 : ℕ) ≤ 64 * (B * (T + 1) : ℝ) ^ 2 ∨
            (p.r - 1 : ℕ) * p.L * p.Δ ≤ 4096 * p.ε ^ 2 * (B * (T + 1) : ℝ) ^ 3)

def SgdLower (p : Public) : Prop :=
  ∀ (η : ℝ), 0 < η → ∀ (B T : ℕ), 0 < B →
    ∀ (A : Algorithm (Space p.r p.r) (Space p.r p.r) (Space p.r p.r)),
      BatchedSpectralSmooth.FollowsBatched id η B T p.x0 A →
      ∃ (f : Space p.r p.r → ℝ) (O : Oracle (Space p.r p.r) (Space p.r p.r)),
        BatchedSpectralSmooth.spec.admissible p.toBase f O ∧
        (BatchedSpectralSmooth.spec.successful p.toBase f
          (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => B * (T + 1)) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
          (p.r - 1 : ℕ) * p.L * p.Δ ≤ 1728 * p.ε ^ 2 * (B * (T + 1)))

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := Space p.r p.r → ℝ
  Query p := Space p.r p.r
  Reply p := Space p.r p.r
  Output p := Space p.r p.r
  publicInput p := p
  valid p := 4 ≤ p.r ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 < p.ε ∧
    128 * p.ε ^ 2 ≤ p.L * p.Δ
  admissible p f O := BatchedSpectralSmooth.spec.admissible p.toBase f O
  successful p f output P :=
    BatchedSpectralSmooth.spec.successful p.toBase f output P ∧ AdamLower p ∧ SgdLower p
  allowedAlgorithm p A := BatchedSpectralSmooth.spec.allowedAlgorithm p.toBase A

end LongTails.Setups.SpectralSmoothAdamComparison
