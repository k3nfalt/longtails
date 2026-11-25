import LongTails.Proofs.CenteredLogisticSteps
import LongTails.Proofs.CenteredLogisticSlowDrift

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticSlowDynamics

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin direction)
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space)
open CenteredLogisticGeometry CenteredLogisticDynamics CenteredLogisticSteps
open TwoSampleQuadraticPerceptronEmbedding

variable {p : Params} {D : Data p} {μ : ℝ}

structure Cloud (p : Params) (D : Data p) (μ : ℝ) where
  e : Features p.d
  A : Fin p.n → ℝ
  u : Fin p.n → Features p.d
  unit : ‖e‖ = 1
  fixed : shift e = e
  orthogonal : ∀ i, ⟪e, u i⟫ = 0
  residual : ∀ i, ‖u i‖ ≤ 1
  levels : ∀ i, |A i| ≤ 9 / 8
  mean : (𝔼 i, A i) = -μ / 2
  energy_lo : 3 / 4 ≤ 𝔼 i, A i ^ 2
  energy_hi : (𝔼 i, A i ^ 2) ≤ 3 / 2
  pos_row : ∃ i, 3 / 4 ≤ A i
  rows : ∀ i, D i = A i • e + μ • u i

structure Split (d : ℕ) where
  a : ℝ
  b : ℝ
  q : ℝ
  z : Features d

variable (F : Cloud p D μ) (s : Split p.d)

noncomputable def point : Space p.d := ((s.a,s.b), s.q • F.e + s.z)

noncomputable def detail (i : Fin p.n) : ℝ :=
  μ * (s.a * ⟪F.u i,s.z⟫ + s.b * ⟪shift (F.u i),s.z⟫)

noncomputable def weight (i : Fin p.n) : ℝ :=
  Real.sigmoid (-margin .conv p.d (D i) (point F s))

noncomputable def background : ℝ := 𝔼 i, F.A i * weight F s i

noncomputable def residualForce : Features p.d := 𝔼 i, weight F s i • F.u i

noncomputable def advance (η : ℝ) : Split p.d :=
  let k := background F s
  let U := residualForce F s
  ⟨s.a + η * (k * s.q + μ * ⟪U,s.z⟫), s.b + η * (k * s.q + μ * ⟪shift U,s.z⟫),
    s.q + η * (s.a + s.b) * k, s.z + (η * μ) • (s.a • U + s.b • shift U)⟩

lemma shifted_inner (v : Features p.d) : ⟪F.e,shift v⟫ = ⟪F.e,v⟫ := by
  simpa only [F.fixed] using inner_shift_shift F.e v

lemma inner_decomp {a q : ℝ} {u z : Features p.d} (hu : ⟪F.e,u⟫ = 0) (hz : ⟪F.e,z⟫ = 0) :
    ⟪a • F.e + μ • u,q • F.e + z⟫ = a * q + μ * ⟪u,z⟫ := by
  have hue : ⟪u,F.e⟫ = 0 := by rw [real_inner_comm]; exact hu
  simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hue, hz, F.unit, mul_comm]

lemma margin_eq (hz : ⟪F.e,s.z⟫ = 0) (i : Fin p.n) :
    margin .conv p.d (D i) (point F s) =
      F.A i * (s.a + s.b) * s.q + detail F s i := by
  simp only [point, margin, F.rows, shift_add, shift_smul, F.fixed]
  rw [inner_decomp F (F.orthogonal i) hz, inner_decomp F ((shifted_inner F _).trans (F.orthogonal i)) hz]
  dsimp only [detail]
  ring

lemma force_orthogonal : ⟪F.e,residualForce F s⟫ = 0 := by
  unfold residualForce
  rw [← mean_inner]
  simp only [real_inner_smul_right, F.orthogonal, mul_zero, Finset.expect_const_zero]

lemma force_norm : ‖residualForce F s‖ ≤ 1 := by
  apply mean_norm_le
  intro i
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ weight F s i from Real.sigmoid_nonneg _)]
  exact (mul_le_mul (Real.sigmoid_le_one _) (F.residual i) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

lemma advance_centered (η : ℝ) (hz : ⟪F.e,s.z⟫ = 0) : ⟪F.e,(advance F s η).z⟫ = 0 := by
  simp [advance, inner_add_right, real_inner_smul_right, hz, shifted_inner, force_orthogonal]

lemma step_eq (η : ℝ) (hz : ⟪F.e,s.z⟫ = 0) :
    step D η (point F s) = point F (advance F s η) := by
  let v := s.q • F.e + s.z
  let g := 𝔼 i, weight F s i • D i
  have hg : g = background F s • F.e + μ • residualForce F s := by
    dsimp only [g, background, residualForce]
    simp_rw [F.rows, smul_add, smul_smul (weight F s _) (F.A _), mul_comm (weight F s _) (F.A _),
      smul_comm (weight F s _) μ, Finset.expect_add_distrib, mean_varying_smul, ← Finset.smul_expect]
  have hM (B : Fin p.n → Features p.d) :
      (𝔼 i, weight F s i * ⟪B i,v⟫) = ⟪𝔼 i, weight F s i • B i,v⟫ := by
    conv_rhs => rw [real_inner_comm]
    rw [← mean_inner]
    apply Finset.expect_congr rfl
    intro i _
    rw [real_inner_smul_right, real_inner_comm v (B i)]
  have hS : (𝔼 i, weight F s i • shift (D i)) = shift g := by
    simp_rw [← shift_smul, mean_shift]
    rfl
  have hZ : (𝔼 i, weight F s i • (s.a • D i + s.b • shift (D i))) = s.a • g + s.b • shift g := by
    simp_rw [smul_add, smul_comm (weight F s _) s.a, smul_comm (weight F s _) s.b,
      Finset.expect_add_distrib, ← Finset.smul_expect, hS]
    rfl
  unfold step
  rw [mean_parts]
  change ((s.a + η * (𝔼 i, weight F s i * ⟪D i,v⟫),
    s.b + η * (𝔼 i, weight F s i * ⟪shift (D i),v⟫)),
    v + η • (𝔼 i, weight F s i • (s.a • D i + s.b • shift (D i)))) = _
  rw [hM, hM, hS, hZ]
  change ((s.a + η * ⟪g,v⟫, s.b + η * ⟪shift g,v⟫), v + η • (s.a • g + s.b • shift g)) = _
  rw [hg, shift_add, shift_smul, shift_smul, F.fixed]
  dsimp only [v, point, advance]
  rw [inner_decomp F (force_orthogonal F s) hz,
    inner_decomp F ((shifted_inner F _).trans (force_orthogonal F s)) hz]
  congr 1
  module

end LongTails.Proofs.CenteredLogisticSlowDynamics
