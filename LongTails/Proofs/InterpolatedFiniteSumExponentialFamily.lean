import LongTails.Proofs.InterpolatedFiniteSumExponential
import LongTails.Proofs.InterpolatedFiniteSumPairs
import LongTails.Proofs.InterpolatedFiniteSumHiddenComponent

open scoped RealInnerProductSpace BigOperators
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumExponentialFamily

open InterpolatedFiniteSumExponential InterpolatedFiniteSumPairs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def signed (v : E) (s : Fin 2) : E := if s = 0 then v else -v

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma signed_norm (v : E) (s : Fin 2) : ‖signed v s‖ = ‖v‖ := by
  unfold signed
  split <;> simp

omit [CompleteSpace E] in
lemma signed_inner_zero (v z : E) (hz : ⟪v, z⟫ = 0) (s : Fin 2) :
    ⟪signed v s, z⟫ = 0 := by
  unfold signed
  split <;> simp [hz]

noncomputable def components {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) : Fin n → E → ℝ :=
  paired h (fun a => centeredValue (m a.1) (signed v a.2) C)

noncomputable def fields {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (dm : Fin g → E → E) (v : E) (C : ℝ) : Fin n → E → E :=
  paired h (fun a => centeredField (m a.1) (dm a.1) (signed v a.2) C)

lemma components_gradient {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (dm : Fin g → E → E) (v : E) (C : ℝ)
    (hm : ∀ i x, HasGradientAt (m i) (dm i x) x) (i : Fin n) (x : E) :
    HasGradientAt (components h m v C i) (fields h m dm v C i x) x := by
  rcases index_or_outside h i with ⟨a, rfl⟩ | hi
  · simp only [components, fields, paired_at_index]
    exact centeredValue_gradient _ _ _ _ _ (hm a.1 x)
  · simp only [components, fields, paired_outside h _ i hi]
    exact hasGradientAt_const x 0

lemma components_gradient_eq {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (dm : Fin g → E → E) (v : E) (C : ℝ)
    (hm : ∀ i x, HasGradientAt (m i) (dm i x) x) (i : Fin n) :
    gradient (components h m v C i) = fields h m dm v C i :=
  funext (fun x => (components_gradient h m dm v C hm i x).gradient)

omit [CompleteSpace E] in
lemma components_convex {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ i, ConvexOn ℝ Set.univ (m i)) (i : Fin n) :
    ConvexOn ℝ Set.univ (components h m v C i) := by
  apply paired_property h _ (fun f => ConvexOn ℝ Set.univ f)
  · exact convexOn_const 0 convex_univ
  · intro a
    exact centeredValue_convex _ _ _ hC (hm a.1)

lemma fields_differentiable {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (dm : Fin g → E → E) (v : E) (C : ℝ)
    (hm : ∀ i x, HasGradientAt (m i) (dm i x) x)
    (hdm : ∀ i, Differentiable ℝ (dm i)) (i : Fin n) :
    Differentiable ℝ (fields h m dm v C i) := by
  apply paired_property h _ (fun f => Differentiable ℝ f)
  · exact differentiable_const 0
  · intro a
    exact centeredField_differentiable _ _ _ _ (hm a.1) (hdm a.1)

omit [CompleteSpace E] in
lemma components_nonnegative {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ i x, 0 ≤ m i x) (i : Fin n) (x : E) :
    0 ≤ components h m v C i x := by
  apply paired_property h (fun a => centeredValue (m a.1) (signed v a.2) C) (fun f : E → ℝ => 0 ≤ f x)
  · exact le_rfl
  · intro a
    exact centeredValue_nonnegative _ _ _ hC x (hm a.1 x)

omit [CompleteSpace E] in
lemma components_minimizer_value {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) (z : E) (hm : ∀ i, m i z = 0) (hv : ⟪v, z⟫ = 0) (i : Fin n) :
    components h m v C i z = 0 := by
  apply paired_property h (fun a => centeredValue (m a.1) (signed v a.2) C) (fun f : E → ℝ => f z = 0)
  · rfl
  · intro a
    exact centeredValue_at_minimizer _ _ _ _ (hm a.1) (signed_inner_zero v z hv a.2)

lemma fields_curvature {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (dm : Fin g → E → E) (v : E) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hm : ∀ i x, HasGradientAt (m i) (dm i x) x)
    (hdm : ∀ i, Differentiable ℝ (dm i))
    (hgn : ∀ i x, ‖dm i x‖ ≤ L / 7) (hv : ‖v‖ = 2 * L / 7)
    (hgc : ∀ i x, ‖fderiv ℝ (dm i) x‖ ≤ 4 * L ^ 2 / 49) (i : Fin n) (x : E) :
    ‖fderiv ℝ (fields h m dm v C i) x‖ ≤
      2 * C * L ^ 2 / 7 + L * ‖fields h m dm v C i x‖ := by
  rcases index_or_outside h i with ⟨a, rfl⟩ | hi
  · simp only [fields, paired_at_index]
    exact centeredField_curvature _ _ _ _ _ hC hL x (hm a.1 x) (hdm a.1 x)
      (hgn a.1 x) ((signed_norm v a.2).trans hv) (hgc a.1 x)
  · simp only [fields, paired_outside h _ i hi]
    change ‖fderiv ℝ (fun _ : E => (0 : E)) x‖ ≤ 2 * C * L ^ 2 / 7 + L * ‖(0 : E)‖
    rw [(hasFDerivAt_const (c := (0 : E)) x).fderiv]
    simp only [norm_zero, mul_zero, add_zero]
    positivity

omit [CompleteSpace E] in
lemma components_sum {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) (x : E) :
    (∑ i : Fin n, components h m v C i x) =
      ∑ j : Fin g, (centeredValue (m j) v C x + centeredValue (m j) (-v) C x) := by
  have hh := congrArg (fun f : E → ℝ => f x)
    (paired_sum h (fun a => centeredValue (m a.1) (signed v a.2) C))
  simp only [Finset.sum_apply, Fintype.sum_prod_type] at hh
  simpa [components, Fin.sum_univ_two, signed] using hh

omit [CompleteSpace E] in
lemma components_sum_lower {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) (hC : 0 ≤ C) (x : E) :
    2 * C * (∑ j : Fin g, (Real.exp (m j x) - 1)) ≤
      ∑ i : Fin n, components h m v C i x := by
  rw [components_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => centered_pair_lower (m j) v C hC x)

omit [CompleteSpace E] in
lemma components_sum_zero {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C : ℝ) :
    (∑ i : Fin n, components h m v C i 0) =
      2 * C * (∑ j : Fin g, (Real.exp (m j 0) - 1)) := by
  rw [components_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact centered_pair_zero_carrier (m j) v C 0 (by simp)

omit [CompleteSpace E] in
lemma components_sum_tangent {n g : ℕ} (h : 2 * g ≤ n) (m : Fin g → E → ℝ)
    (v : E) (C η D F : ℝ) (hC : 0 ≤ C) (a : Fin g → ℝ) (x : E)
    (hm : ∀ i, η - D - F * a i ≤ m i x) :
    2 * C * g * (Real.exp η - 1) - 2 * C * Real.exp η * (g * D + F * ∑ i, a i) ≤
      ∑ i : Fin n, components h m v C i x := by
  have he (i : Fin g) : Real.exp η - 1 - Real.exp η * (D + F * a i) ≤
      Real.exp (m i x) - 1 := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (m i x - η)) (Real.exp_pos η).le
    have hid : Real.exp η * Real.exp (m i x - η) = Real.exp (m i x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hid] at hh
    have hl := mul_le_mul_of_nonneg_left (hm i) (Real.exp_pos η).le
    nlinarith only [hh, hl]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * C)
  have hb := components_sum_lower h m v C hC x
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hb
  nlinarith only [hh, hb]

lemma admissible (p : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Params)
    (hp : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.valid p)
    {g : ℕ} (h : 2 * g ≤ p.n)
    (m : Fin g → LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Point p → ℝ)
    (dm : Fin g → LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Point p →
      LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Point p)
    (v z : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Point p) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ i x, HasGradientAt (m i) (dm i x) x)
    (hdm : ∀ i, Differentiable ℝ (dm i)) (hconv : ∀ i, ConvexOn ℝ Set.univ (m i))
    (hgn : ∀ i x, ‖dm i x‖ ≤ p.L1 / 7) (hv : ‖v‖ = 2 * p.L1 / 7)
    (hgc : ∀ i x, ‖fderiv ℝ (dm i) x‖ ≤ 4 * p.L1 ^ 2 / 49)
    (hadd : 2 * C * p.L1 ^ 2 / 7 ≤ p.L0) (hnonneg : ∀ i x, 0 ≤ m i x)
    (hmz : ∀ i, m i z = 0) (hvz : ⟪v, z⟫ = 0) (hz : ‖z‖ ≤ p.R)
    (hgap : (p.n : ℝ)⁻¹ * (2 * C * ∑ j : Fin g, (Real.exp (m j 0) - 1)) ≤ p.Δ) :
    LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.admissible p
      (components h m v C)
      (InterpolatedFiniteSumHiddenComponent.exactOracle p (components h m v C) (fields h m dm v C)) := by
  refine ⟨components_convex h m v C hC hconv, ?_, ?_, ?_, ?_, z, ?_, hz, ?_⟩
  · intro i x
    rw [components_gradient_eq h m dm v C hm]
    exact components_gradient h m dm v C hm i x
  · intro i
    rw [components_gradient_eq h m dm v C hm]
    exact fields_differentiable h m dm v C hm hdm i
  · intro i x
    rw [components_gradient_eq h m dm v C hm]
    have hh := fields_curvature h m dm v C p.L1 hC hp.2.1 hm hdm hgn hv hgc i x
    linarith only [hh, hadd]
  · intro history seed i x
    simp only [InterpolatedFiniteSumHiddenComponent.exactOracle,
      components_gradient_eq h m dm v C hm]
  · intro i x _
    change components h m v C i z ≤ components h m v C i x
    rw [components_minimizer_value h m v C z hmz hvz]
    exact components_nonnegative h m v C hC hnonneg i x
  · simpa only [id_eq, LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.objective,
      components_minimizer_value h m v C z hmz hvz, Finset.sum_const_zero,
      mul_zero, sub_zero, components_sum_zero] using hgap

end LongTails.Proofs.InterpolatedFiniteSumExponentialFamily
