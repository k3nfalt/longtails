import LongTails.Proofs.AcceleratedCoordinateEnergy
import LongTails.Proofs.AcceleratedCoordinateExecution
import LongTails.Proofs.RecursiveGradientEnergy

open InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

noncomputable def energy (p : Params) (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (u : EuclideanSpace ℝ (Fin p.d))
    (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) : ℝ :=
  f s.1 - f u + p.μ / 2 * ‖s.2 - u‖ ^ 2

lemma energy_step (p : Params) (hμ : 0 < p.μ) (hL : ∀ i, p.μ ≤ p.L i)
    {f : EuclideanSpace ℝ (Fin p.d) → ℝ}
    (hmodel : ∀ x i t, f (x + EuclideanSpace.single i t) ≤
      f x + t * gradient f x i + p.L i / 2 * t ^ 2)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
    (u : EuclideanSpace ℝ (Fin p.d)) :
    (𝔼 choice : CoordinateChoice p,
      energy p f u (step p s choice.1 (gradient f (extrapolate p s) choice.1))) ≤
        (1 - tau p) * energy p f u s := by
  let x := extrapolate p s
  let next := fun choice : CoordinateChoice p => step p s choice.1 (gradient f x choice.1)
  rcases tuning p hμ with ⟨hτ, hτ1, hη, hrel, hcoef⟩
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (choice : CoordinateChoice p) _ => coordinate_mirror p hμ hL hmodel s u choice.1)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    ← Finset.expect_div, Fintype.expect_const] at hm
  rw [importance_unbiased p (fun i => gradient f (extrapolate p s) i * (s.2 - u) i)] at hm
  have hi : (∑ i, gradient f x i * (s.2 - u) i) = ⟪gradient f x, s.2 - u⟫ := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  change eta p * (∑ i, gradient f x i * (s.2 - u) i) -
      eta p * p.μ / 2 * ‖x - u‖ ^ 2 ≤
      (eta p) ^ 2 * p.μ * (totalWeight p : ℝ) ^ 2 *
        (f x - (𝔼 choice, f (next choice).1)) + ‖s.2 - u‖ ^ 2 / 2 -
        (1 + eta p * p.μ) / 2 * (𝔼 choice, ‖(next choice).2 - u‖ ^ 2) at hm
  rw [hi] at hm
  have hd : (𝔼 choice : CoordinateChoice p, f (next choice).1) ≤ f x := by
    have h := Finset.expect_le_expect (s := Finset.univ) (fun (choice : CoordinateChoice p) _ =>
      coordinate_descent hmodel x choice.1 (hμ.trans_le (hL choice.1)))
    have hh := Finset.expect_nonneg (s := Finset.univ) (fun (choice : CoordinateChoice p) _ =>
      div_nonneg (sq_nonneg (gradient f x choice.1))
        (show 0 ≤ 2 * p.L choice.1 by have := hμ.trans_le (hL choice.1); positivity))
    simp only [Finset.expect_sub_distrib, Fintype.expect_const] at h
    dsimp only [next, step]
    linarith
  have hA : (eta p) ^ 2 * p.μ * (totalWeight p : ℝ) ^ 2 ≤ eta p / tau p := by
    apply (le_div_iff₀ hτ).mpr
    have h := mul_le_mul_of_nonneg_left hcoef hη.le
    nlinarith only [h]
  have hc := convex_coupling hμ.le hτ hτ1.le hη.le hs s.1 s.2 u
  have hp := potential_algebra hη hτ hrel hA hd hm hc
  simpa only [energy, Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const, next, x] using hp

lemma run_energy (p : Params) (hμ : 0 < p.μ) (hL : ∀ i, p.μ ≤ p.L i)
    {f : EuclideanSpace ℝ (Fin p.d) → ℝ}
    (hmodel : ∀ x i t, f (x + EuclideanSpace.single i t) ≤
      f x + t * gradient f x i + p.L i / 2 * t ^ 2)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : EuclideanSpace ℝ (Fin p.d)) (K : ℕ)
    (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) :
    (𝔼 seed : Fin K → CoordinateChoice p,
      energy p f u (run p (fun q => gradient f q.2 q.1) s (List.ofFn seed))) ≤
        (1 - tau p) ^ K * energy p f u s := by
  have hq : 0 ≤ 1 - tau p := (sub_pos.mpr (tuning p hμ).2.1).le
  induction K generalizing s with
  | zero => simp [run]
  | succ K ih =>
      rw [NonconvexFiniteSum.expect_function_succ]
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, run]
      have h := Finset.expect_le_expect (s := Finset.univ)
        (fun (choice : CoordinateChoice p) _ =>
          ih (step p s choice.1 (gradient f (extrapolate p s) choice.1)))
      simp only [← Finset.mul_expect] at h
      have hh := mul_le_mul_of_nonneg_left (energy_step p hμ hL hmodel hs s u) (pow_nonneg hq K)
      exact h.trans (by simpa only [pow_succ, mul_assoc] using hh)

lemma initial_energy (p : Params) {f : EuclideanSpace ℝ (Fin p.d) → ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : EuclideanSpace ℝ (Fin p.d)) (hmin : IsMinOn f Set.univ u)
    (hgap : f p.x0 - f u ≤ p.Δ) : energy p f u (p.x0, p.x0) ≤ 2 * p.Δ := by
  have hzero : gradient f u = 0 := by
    apply (toDual ℝ (EuclideanSpace ℝ (Fin p.d))).injective
    simpa using (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero (hg u).hasFDerivAt
  have h := hs u p.x0
  rw [hzero, inner_zero_left, add_zero] at h
  dsimp [energy]
  linarith

lemma run_rate (p : Params) (hμ : 0 < p.μ) (hL : ∀ i, p.μ ≤ p.L i)
    {f : EuclideanSpace ℝ (Fin p.d) → ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hmodel : ∀ x i t, f (x + EuclideanSpace.single i t) ≤
      f x + t * gradient f x i + p.L i / 2 * t ^ 2)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : EuclideanSpace ℝ (Fin p.d)) (hmin : IsMinOn f Set.univ u)
    (hgap : f p.x0 - f u ≤ p.Δ) (K : ℕ) :
    (𝔼 seed : Seeds p K,
      (f (run p (fun q => gradient f q.2 q.1) (p.x0, p.x0) (List.ofFn seed)).1 - f u)) ≤
        (1 - tau p) ^ K * (2 * p.Δ) := by
  have hq : 0 ≤ 1 - tau p := (sub_pos.mpr (tuning p hμ).2.1).le
  have hi := initial_energy p hg hs u hmin hgap
  have he := run_energy p hμ hL hmodel hs u K (p.x0, p.x0)
  have hpoint (seed : Fin K → CoordinateChoice p) :
      f (run p (fun q => gradient f q.2 q.1) (p.x0, p.x0) (List.ofFn seed)).1 - f u ≤
        energy p f u (run p (fun q => gradient f q.2 q.1) (p.x0, p.x0) (List.ofFn seed)) := by
    unfold energy
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have h := Finset.expect_le_expect (s := Finset.univ) (fun seed _ => hpoint seed)
  exact h.trans (he.trans (mul_le_mul_of_nonneg_left hi (pow_nonneg hq K)))

end OracleTemplate.AcceleratedCoordinate
