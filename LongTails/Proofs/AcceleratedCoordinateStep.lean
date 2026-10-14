import LongTails.Algorithms.AcceleratedCoordinate
import Mathlib.Tactic

open InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

lemma mirror_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c : ℝ} (hc : 0 ≤ c) (z x a u : E) :
    let next := (1 / (1 + c)) • (z + c • x - a)
    ⟪a, z - u⟫ - c / 2 * ‖x - u‖ ^ 2 ≤
      ‖a‖ ^ 2 / 2 + ‖z - u‖ ^ 2 / 2 - (1 + c) / 2 * ‖next - u‖ ^ 2 := by
  let next := (1 / (1 + c)) • (z + c • x - a)
  have hden : 0 < 1 + c := by linarith
  have hid : (1 + c) • (next - u) = (z - u - a) + c • (x - u) := by
    dsimp [next]
    match_scalars
    all_goals field_simp <;> ring
  have heq := congrArg (fun v => ‖v‖ ^ 2) hid
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real,
    inner_smul_right] at heq
  have hnonneg := mul_nonneg hc (sq_nonneg ‖(z - u - a) - (x - u)‖)
  rw [norm_sub_sq_real] at hnonneg
  have hsq : (1 + c) * ((1 + c) * ‖next - u‖ ^ 2) ≤
      (1 + c) * (‖z - u - a‖ ^ 2 + c * ‖x - u‖ ^ 2) := by nlinarith
  have h := (mul_le_mul_iff_right₀ hden).mp hsq
  rw [norm_sub_sq_real (z - u) a, real_inner_comm a (z - u)] at h
  dsimp only
  change _ ≤ _ + _ - _ * ‖next - u‖ ^ 2
  nlinarith

lemma coordinate_descent {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {L : Fin d → ℝ} {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hmodel : ∀ x i t, f (x + EuclideanSpace.single i t) ≤
      f x + t * g x i + L i / 2 * t ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (hL : 0 < L i) :
    f (x - EuclideanSpace.single i (g x i / L i)) ≤ f x - (g x i) ^ 2 / (2 * L i) := by
  have h := hmodel x i (-(g x i / L i))
  have heq : x + EuclideanSpace.single i (-(g x i / L i)) =
      x - EuclideanSpace.single i (g x i / L i) := by
    ext j
    by_cases hj : j = i <;> simp [hj]; ring
  rw [heq] at h
  convert h using 1; field_simp; ring

end OracleTemplate.AcceleratedCoordinate
