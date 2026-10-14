import LongTails.Setups.QuadraticFiniteSum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.QuadraticFiniteSum

open LongTails.Setups.QuadraticFiniteSum

variable {q : Params} (f : Instance q)

lemma component_hasGradientAt (i : Fin q.n) (hs : (f.A i).toLinearMap.IsSymmetric)
    (x : q.E) :
    HasGradientAt (fun y => ⟪y, f.A i y⟫ / 2 + ⟪f.b i, y⟫) (f.A i x + f.b i) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (((hasFDerivAt_id x).inner ℝ (f.A i).hasFDerivAt).const_smul (1 / 2 : ℝ)).add
    ((hasFDerivAt_const (f.b i) x).inner ℝ (hasFDerivAt_id x))
  convert hd using 1
  · funext y
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, id_eq]
    ring
  · ext v
    have hh : ⟪f.A i x, v⟫ = ⟪x, f.A i v⟫ := hs x v
    have hh' : ⟪v, f.A i x⟫ = ⟪x, f.A i v⟫ := (real_inner_comm _ _).trans hh
    simp [fderivInnerCLM_apply, hh, hh']
    ring

lemma component_gap (i : Fin q.n) (hs : (f.A i).toLinearMap.IsSymmetric) (x u : q.E) :
    (⟪x, f.A i x⟫ / 2 + ⟪f.b i, x⟫) -
        (⟪u, f.A i u⟫ / 2 + ⟪f.b i, u⟫) =
      ⟪x - u, f.A i (x - u)⟫ / 2 + ⟪f.A i u + f.b i, x - u⟫ := by
  have hsym : ⟪f.A i u, x⟫ = ⟪u, f.A i x⟫ := hs u x
  have hsym' : ⟪x, f.A i u⟫ = ⟪u, f.A i x⟫ := by rw [real_inner_comm, hsym]
  simp only [map_sub, inner_sub_left, inner_sub_right, inner_add_left, hsym, hsym']
  rw [real_inner_comm (f.A i u) u]
  ring

lemma objective_gap (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric)
    {u : q.E} (hu : (∑ i, (f.A i u + f.b i)) = 0) (x : q.E) :
    objective f x - objective f u = (q.n : ℝ)⁻¹ * (∑ i, ⟪x - u, f.A i (x - u)⟫) / 2 := by
  unfold objective
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [component_gap f _ (hs _)]
  rw [Finset.sum_add_distrib, ← sum_inner, hu, inner_zero_left, add_zero,
    ← Finset.sum_div]
  ring

lemma objective_upper {L : ℝ} (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric)
    (hA : ∀ i, ‖f.A i‖ ≤ L) {u : q.E}
    (hu : (∑ i, (f.A i u + f.b i)) = 0) (x : q.E) :
    objective f x - objective f u ≤ L * ‖x - u‖ ^ 2 / 2 := by
  rw [objective_gap f hs hu]
  have hn : (q.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q.n
  have hsum : (∑ i, ⟪x - u, f.A i (x - u)⟫) ≤ (q.n : ℝ) * (L * ‖x - u‖ ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin q.n, L * ‖x - u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ ‖x - u‖ * ‖f.A i (x - u)‖ := real_inner_le_norm _ _
          _ ≤ ‖x - u‖ * (L * ‖x - u‖) := mul_le_mul_of_nonneg_left
            (((f.A i).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q.n : (0 : ℝ) ≤ _))
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul] at hh
  linarith

lemma stationary_minimizer {μ : ℝ} (hμ : 0 ≤ μ)
    (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric)
    (hp : ∀ x, μ * ‖x‖ ^ 2 ≤ (q.n : ℝ)⁻¹ * ∑ i, ⟪x, f.A i x⟫)
    {u : q.E} (hu : (∑ i, (f.A i u + f.b i)) = 0) :
    IsMinOn (objective f) Set.univ u := by
  intro x hx
  change objective f u ≤ objective f x
  have hg := objective_gap f hs hu x
  have hn := hp (x - u)
  have hz := mul_nonneg hμ (sq_nonneg ‖x - u‖)
  linarith

lemma continuous_objective : Continuous (objective f) := by
  unfold objective
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i hi
  exact (continuous_id.inner (f.A i).continuous).div_const 2 |>.add
    (continuous_const.inner continuous_id)

end OracleTemplate.QuadraticFiniteSum
