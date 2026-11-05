import LongTails.Proofs.FiniteSumNondualProxSolver

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteSumNondualOuterGeometry

open FiniteSumNondualProxGeometry
open RecursiveEnvelopeGeometry (Model)
open LongTails.Algorithms.FiniteSumNondualProx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Certified (C : Set E) (g : E → E) (μ ρ : ℝ) (c : E) (out : Certificate E) : Prop :=
  out.point ∈ C ∧ out.gradient = g out.point ∧
    ∃ v, Normal C out.point v ∧ regularizedGradient g μ c out.point + v = out.error ∧ ‖out.error‖ ≤ ρ

lemma certified_gradient_error {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L μ ρ : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) (c : E) (out : Certificate E)
    (hc : Certified C g μ ρ c out) :
    ‖μ • (c - out.point) - envelopeSlope C f μ c‖ ≤ ρ := by
  obtain ⟨hw, _, v, hv, he, hr⟩ := hc
  have hp := proximalPoint_spec hne hco hcont μ c
  exact residual_envelope_gradient_error hcv hf hμ c _ out.point v hp.1 hw hp.2 hv (by rwa [he])

lemma certified_value_error {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    {L μ ρ : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) (c : E) (out : Certificate E)
    (hc : Certified C g μ ρ c out) :
    regularized f μ c out.point - envelope C f μ c ≤ ρ ^ 2 / (2 * μ) := by
  obtain ⟨_, _, v, hv, he, hr⟩ := hc
  have hp := proximalPoint_spec hne hco hcont μ c
  exact residual_value_error hf hμ c _ out.point v hp.1 hv (by rwa [he])

omit [InnerProductSpace ℝ E] in
lemma envelope_le_objective {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    {f : E → ℝ} (hcont : Continuous f) (μ : ℝ) (y : E) (hy : y ∈ C) :
    envelope C f μ y ≤ f y := by
  have hh := (proximalPoint_spec hne hco hcont μ y).2 hy
  change envelope C f μ y ≤ regularized f μ y y at hh
  simpa only [regularized, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hh

lemma certified_descent {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    {L μ ρ η : ℝ} {f : E → ℝ} {g : E → E}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) (c y : E) (hy : y ∈ C)
    (out : Certificate E) (hc : Certified C g μ ρ c out)
    (hline : envelope C f μ c ≤ envelope C f μ y + η)
    (hρ : ρ ^ 2 / (2 * μ) ≤ η / 2) :
    f out.point ≤ f y + 3 * η / 2 - μ / 2 * ‖c - out.point‖ ^ 2 := by
  have hv := certified_value_error hne hco hf hcont hμ c out hc
  have hy' := envelope_le_objective hne hco hcont μ y hy
  unfold regularized at hv
  rw [norm_sub_rev out.point c] at hv
  linarith

lemma certified_cut_movement {C : Set E} {μ ρ D δ : ℝ} {g : E → E}
    (hμ : 0 ≤ μ) (c z z' : E) (hz' : z' ∈ C) (out : Certificate E)
    (hc : Certified C g μ ρ c out) (hdist : ‖out.point - z'‖ ≤ D)
    (hline : ⟪μ • (c - out.point), c - z⟫ ≤ 0)
    (hcut : δ ≤ ⟪out.gradient, out.point - z'⟫) :
    δ ≤ ρ * D + μ * ‖c - out.point‖ * ‖z - z'‖ := by
  obtain ⟨_, hg, v, hv, he, hr⟩ := hc
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hr
  have hn := hv z' hz'
  have hnormal : 0 ≤ ⟪v, out.point - z'⟫ := by
    rw [← neg_sub out.point z', inner_neg_right] at hn
    linarith
  have hgrad : out.gradient = μ • (c - out.point) + out.error - v := by
    rw [hg]
    unfold regularizedGradient at he
    rw [← he]
    module
  have hs : out.point - z' = (out.point - c) + (c - z) + (z - z') := by module
  have hneg : ⟪μ • (c - out.point), out.point - c⟫ = -μ * ‖c - out.point‖ ^ 2 := by
    rw [show out.point - c = -(c - out.point) by module, inner_neg_right,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hmove := real_inner_le_norm (μ • (c - out.point)) (z - z')
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at hmove
  have herr := (real_inner_le_norm out.error (out.point - z')).trans
    ((mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hdist hρ))
  rw [hgrad, inner_sub_left, inner_add_left] at hcut
  rw [hs, inner_add_right, inner_add_right, hneg, ← hs] at hcut
  nlinarith [mul_nonneg hμ (sq_nonneg ‖c - out.point‖)]

end LongTails.Proofs.FiniteSumNondualOuterGeometry
