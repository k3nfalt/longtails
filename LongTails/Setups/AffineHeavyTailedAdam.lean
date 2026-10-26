import LongTails.Setups.HeavyTailedAdam

open MeasureTheory

namespace LongTails.Setups.AffineHeavyTailedAdam

open OracleTemplate

abbrev Point (d : ℕ) := Adam.Point d

noncomputable def sumNorm {d : ℕ} (x : Point d) : ℝ := ∑ i, |x i|

noncomputable def maxNorm {d : ℕ} (x : Point d) : ℝ := ‖WithLp.ofLp x‖

structure Config where
  β₁ : ℝ
  β₂ : ℝ
  η : ℝ
  δ : ℝ
  batchSize : ℕ
  lastIndex : ℕ

structure State (d : ℕ) where
  count : ℕ
  total : Point d
  core : Adam.State d

noncomputable def coreStep {d : ℕ} (cfg : Config) (s : Adam.State d)
    (g : Point d) : Adam.State d :=
  let m := cfg.β₁ • s.momentum + (1 - cfg.β₁) • g
  let v := Adam.secondMomentStep (1 - cfg.β₂) s.secondMoment g
  let mhat := (1 - cfg.β₁ ^ (s.time + 1))⁻¹ • m
  let vhat := (1 - cfg.β₂ ^ (s.time + 1))⁻¹ • v
  { selected := s.selected
    time := s.time + 1
    point := s.point - cfg.η • Adam.direction cfg.δ mhat vhat
    momentum := m
    secondMoment := v
    saved := if s.time = s.selected then s.point else s.saved }

noncomputable def step {d : ℕ} (cfg : Config) (s : State d) (g : Point d) : State d :=
  if s.count + 1 < cfg.batchSize then
    { count := s.count + 1, total := s.total + g, core := s.core }
  else
    { count := 0, total := 0
      core := coreStep cfg s.core ((cfg.batchSize : ℝ)⁻¹ • (s.total + g)) }

noncomputable def method {d : ℕ} (cfg : Config) (x0 : Point d) :
    Algorithm (Point d) (Point d) (Point d) where
  Seed := Fin (cfg.lastIndex + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (cfg.lastIndex + 1))).toMeasure, inferInstance⟩
  State := State d
  initial k := ⟨0, 0, ⟨k.val, 0, x0, 0, 0, x0⟩⟩
  query s := (0, s.core.point)
  update := step cfg
  output s := s.core.saved

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L0 : ℝ
  L1 : ℝ
  σ0 : Fin d → ℝ
  σ1 : ℝ
  p : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Point d

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Point q.d → ℝ
  Query q := Point q.d
  Reply q := Point q.d
  Output q := Point q.d
  publicInput q := q
  valid q := 0 ≤ q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.L0 + q.L1 ∧
    (∀ i, 0 ≤ q.σ0 i) ∧ 0 ≤ q.σ1 ∧ 1 < q.p ∧ q.p ≤ 2 ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : Point q.d → q.Ω → Point q.d)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, q.L1 * maxNorm (y - x) ≤ 1 →
        sumNorm (gradient f y - gradient f x) ≤
          (q.L0 + q.L1 * sumNorm (gradient f x)) * maxNorm (y - x)) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x i, Integrable (fun ω => |(g x ω - gradient f x) i| ^ q.p) p) ∧
      (∀ x i, ∫ ω, |(g x ω - gradient f x) i| ^ q.p ∂p ≤
        q.σ0 i ^ q.p + q.σ1 ^ q.p * |gradient f x i| ^ q.p)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => sumNorm (gradient f (output ω))) (P : Measure _) ∧
      (∫ ω, sumNorm (gradient f (output ω)) ∂(P : Measure _)) ≤ q.ε
  allowedAlgorithm q A :=
    ∃ cfg : Config, 0 ≤ cfg.β₁ ∧ cfg.β₁ < 1 ∧ 0 ≤ cfg.β₂ ∧ cfg.β₂ < 1 ∧
      0 < cfg.η ∧ 0 < cfg.δ ∧ 0 < cfg.batchSize ∧ A = method cfg q.x0

end LongTails.Setups.AffineHeavyTailedAdam
