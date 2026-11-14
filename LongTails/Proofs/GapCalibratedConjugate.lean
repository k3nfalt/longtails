import LongTails.Proofs.GapCalibratedWeights

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.GapCalibratedConjugate

open CompactConjugate GeneralizedSmoothHardDual GeneralizedSmoothHardDualSegments
open GeneralizedSmoothHardTransfer GeneralizedSmoothHardChain

noncomputable def constantVector (m : ℕ) (a : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ => a)

noncomputable def objective {m : ℕ} (L₀ L₁ B A : ℝ) (G : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  value (feasible G) (dual L₀ L₁) (x + constantVector m A + shift L₀ L₁ B G)

noncomputable def field {m : ℕ} (L₀ L₁ B A : ℝ) (G : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  maximizer (feasible G) (dual L₀ L₁) (x + constantVector m A + shift L₀ L₁ B G)

variable {m : ℕ} (hm : 0 < m) (L₀ L₁ B A : ℝ)
  (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ) (hG : ∀ i, 0 < G i)
  (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B)

include hm hL₀ hL₁ hG hB hGB

lemma objective_nonnegative (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective L₀ L₁ B A G x :=
  conjugate_nonnegative hm L₀ L₁ B hL₀ hL₁ G hG hB hGB _

lemma objective_zero (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, x i + A + shiftCoordinate L₀ L₁ B G i ≤ 0) :
    objective L₀ L₁ B A G x = 0 := by
  apply conjugate_zero_of_nonpositive hm L₀ L₁ B hL₀ hL₁ G hG hB hGB
  exact hx

lemma objective_vertex_bound (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    G i * (x i + A + 2 / L₁) ≤ objective L₀ L₁ B A G x := by
  have hu := maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G)
    (x + constantVector m A + shift L₀ L₁ B G)
  exact (shifted_vertex_bound hm L₀ L₁ B hL₀ hL₁ G hG i (hGB i)
    (x + constantVector m A)).trans (hu.2 (vertex_feasible G hG i))

lemma objective_upper (x : EuclideanSpace ℝ (Fin m)) (D : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i, G i * (x i + A + shiftCoordinate L₀ L₁ B G i) ≤ D) :
    objective L₀ L₁ B A G x ≤ D := by
  let z := field L₀ L₁ B A G x
  have hz : z ∈ feasible G := (maximizer_spec (feasible_compact G B hG hB hGB)
    ⟨0, feasible_zero G⟩ (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G)
    (x + constantVector m A + shift L₀ L₁ B G)).1
  have hd := (dual_bound hm L₀ L₁ hL₀ hL₁ z hz.1).1
  have hi (i : Fin m) :
      (x i + A + shiftCoordinate L₀ L₁ B G i) * z i ≤ D * (z i / G i) := by
    have hh := mul_le_mul_of_nonneg_right (hx i) (div_nonneg (hz.1 i) (hG i).le)
    have he : G i * (x i + A + shiftCoordinate L₀ L₁ B G i) * (z i / G i) =
        (x i + A + shiftCoordinate L₀ L₁ B G i) * z i := by
      field_simp [(hG i).ne']
    rwa [he] at hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [← Finset.mul_sum] at hs
  have hb := hs.trans ((mul_le_mul_of_nonneg_left hz.2 hD).trans_eq (mul_one D))
  have he : ⟪x + constantVector m A + shift L₀ L₁ B G, z⟫ =
      ∑ i, (x i + A + shiftCoordinate L₀ L₁ B G i) * z i := by
    simp [PiLp.inner_apply, constantVector, shift, mul_comm]
  change ⟪x + constantVector m A + shift L₀ L₁ B G, z⟫ - dual L₀ L₁ z ≤ D
  rw [he]
  linarith

lemma field_tail_zero (hA : 0 ≤ A) (τ : ℝ) (j l : Fin m) (hjl : j < l)
    (horder : G l ≤ G j) (x : EuclideanSpace ℝ (Fin m))
    (hxj : -τ ≤ x j) (hxl : x l ≤ τ)
    (hgap : τ * (G j + G l) < 2 * (G j - G l) / L₁) :
    field L₀ L₁ B A G x l = 0 := by
  have hu := maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G)
    (x + constantVector m A + shift L₀ L₁ B G)
  apply optimizer_coordinate_zero hm L₀ L₁ B hL₀ hL₁ G hG hB hGB j l
    (ne_of_lt hjl) horder _ _ hu.1 hu.2
  have hs := shifted_score hm L₀ L₁ B τ hL₁ G hG j l hjl (x j) (x l) hxj hxl hgap
  have ha := mul_nonneg (sub_nonneg.mpr horder) hA
  change (G j - G l) * (2 * (Real.log (1 + L₁ * B / L₀) / L₁)) +
    G j * (4 / L₁ * Real.log (1 + 1 / (1 / Real.sqrt m))) <
      G j * (x j + A + shiftCoordinate L₀ L₁ B G j) -
        G l * (x l + A + shiftCoordinate L₀ L₁ B G l)
  nlinarith only [hs, ha]

lemma objective_hasGradientAt (x : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (objective L₀ L₁ B A G) (field L₀ L₁ B A G x) x := by
  have hh := conjugate_hasGradientAt hm L₀ L₁ B hL₀ hL₁ G hG hB hGB
    (x + constantVector m A + shift L₀ L₁ B G)
  rw [hasGradientAt_iff_hasFDerivAt]
  have ht := hh.hasFDerivAt.comp x (((hasFDerivAt_id x).add_const
    (constantVector m A)).add_const (shift L₀ L₁ B G))
  convert ht using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, field]

lemma field_pair (x y : EuclideanSpace ℝ (Fin m)) :
    ‖field L₀ L₁ B A G x - field L₀ L₁ B A G y‖ ≤
      (L₀ + L₁ * max ‖field L₀ L₁ B A G x‖ ‖field L₀ L₁ B A G y‖) * ‖x - y‖ := by
  have hh := conjugate_field_pair hm L₀ L₁ B hL₀ hL₁ G hG hB hGB
    (x + constantVector m A + shift L₀ L₁ B G)
    (y + constantVector m A + shift L₀ L₁ B G)
  simpa only [field, add_sub_add_right_eq_sub] using hh

lemma field_norm_bound (x : EuclideanSpace ℝ (Fin m)) : ‖field L₀ L₁ B A G x‖ ≤ B := by
  exact feasible_norm_bound G B hG hB hGB _
    (maximizer_spec (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
      (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G) _).1

lemma objective_convex : ConvexOn ℝ univ (objective L₀ L₁ B A G) := by
  let σ := constantVector m A + shift L₀ L₁ B G
  have hc := value_convex (feasible_compact G B hG hB hGB) ⟨0, feasible_zero G⟩
    (dual_continuousOn_feasible hm L₀ L₁ hL₀ hL₁ G)
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := hc.2 (mem_univ (x + σ)) (mem_univ (y + σ)) ha hb hab
  have he : a • (x + σ) + b • (y + σ) = (a • x + b • y) + σ := by
    calc
      _ = (a • x + b • y) + (a + b) • σ := by simp only [smul_add, add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  rw [he] at hh
  simpa only [objective, σ, add_assoc] using hh

lemma field_lipschitz (x y : EuclideanSpace ℝ (Fin m)) :
    ‖field L₀ L₁ B A G x - field L₀ L₁ B A G y‖ ≤ (L₀ + L₁ * B) * ‖x - y‖ := by
  apply (field_pair hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB x y).trans
  gcongr
  exact max_le (field_norm_bound hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB x)
    (field_norm_bound hm L₀ L₁ B A hL₀ hL₁ G hG hB hGB y)

end LongTails.Proofs.GapCalibratedConjugate
