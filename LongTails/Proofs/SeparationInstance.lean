import LongTails.Proofs.DiagonalSpectral
import LongTails.Proofs.MuonProcess
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.MeanValue

namespace LongTails.Proofs.SeparationInstance

open MeasureTheory ProbabilityTheory
open LongTails.Algorithms.MatrixPolar LongTails.Proofs.DiagonalSpectral

variable {m n : ℕ}

noncomputable def valley (w D u : ℝ) : ℝ := Real.sqrt (w ^ 2 + (u - D) ^ 2)

noncomputable def valleySlope (w D u : ℝ) : ℝ := (u - D) / Real.sqrt (w ^ 2 + (u - D) ^ 2)

lemma valley_pos {w : ℝ} (hw : 0 < w) (D u : ℝ) : 0 < w ^ 2 + (u - D) ^ 2 := by positivity

lemma hasDerivAt_valley {w : ℝ} (hw : 0 < w) (D u : ℝ) :
    HasDerivAt (valley w D) (valleySlope w D u) u := by
  have h1 := HasDerivAt.sub_const D (hasDerivAt_id u)
  have h2 := HasDerivAt.const_add (w ^ 2) (HasDerivAt.pow h1 2)
  have hs := HasDerivAt.sqrt h2 (valley_pos hw D u).ne'
  convert hs using 1
  · funext y
    simp [valley]
  · have hp : 0 < Real.sqrt (w ^ 2 + (u - D) ^ 2) := Real.sqrt_pos.mpr (valley_pos hw D u)
    simp only [valleySlope, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      mul_one]
    field_simp

lemma abs_valleySlope_le (w D u : ℝ) : |valleySlope w D u| ≤ 1 := by
  unfold valleySlope
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg w])

lemma valleySlope_far {w D u : ℝ} (hw : 0 < w) (hu : u ≤ D - w) :
    valleySlope w D u ≤ -(1 / 2) := by
  unfold valleySlope
  have hpos : 0 < Real.sqrt (w ^ 2 + (u - D) ^ 2) := Real.sqrt_pos.mpr (valley_pos hw D u)
  rw [div_le_iff₀ hpos]
  have hs : Real.sqrt (w ^ 2 + (u - D) ^ 2) ≤ 2 * (D - u) := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  linarith

lemma valleySlope_lipschitz {w : ℝ} (hw : 0 < w) (D u v : ℝ) :
    |valleySlope w D u - valleySlope w D v| ≤ |u - v| / w := by
  let h : ℝ → ℝ := fun x => x / Real.sqrt (w ^ 2 + x ^ 2)
  let h' : ℝ → ℝ := fun x => w ^ 2 / (Real.sqrt (w ^ 2 + x ^ 2) ^ 3)
  have hd (x : ℝ) : HasDerivAt h (h' x) x := by
    have hp : 0 < w ^ 2 + x ^ 2 := by positivity
    have hs := HasDerivAt.sqrt (HasDerivAt.const_add (w ^ 2) ((hasDerivAt_id x).pow 2)) hp.ne'
    have hq := HasDerivAt.div (hasDerivAt_id x) hs (Real.sqrt_pos.mpr hp).ne'
    convert hq using 1
    · funext y
      simp only [h, Pi.div_apply, Pi.pow_apply, id_eq]
    · have hsq : Real.sqrt (w ^ 2 + x ^ 2) ^ 2 = w ^ 2 + x ^ 2 := Real.sq_sqrt hp.le
      have hsp : 0 < Real.sqrt (w ^ 2 + x ^ 2) := Real.sqrt_pos.mpr hp
      simp only [h', Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one,
        one_mul]
      rw [show Real.sqrt (w ^ 2 + x ^ 2) ^ 3 = Real.sqrt (w ^ 2 + x ^ 2) *
        Real.sqrt (w ^ 2 + x ^ 2) ^ 2 by ring, hsq]
      field_simp
      rw [hsq]
      ring
  have hb (x : ℝ) : ‖h' x‖ ≤ 1 / w := by
    have hp : 0 < w ^ 2 + x ^ 2 := by positivity
    have hs : w ≤ Real.sqrt (w ^ 2 + x ^ 2) := by
      rw [Real.le_sqrt hw.le hp.le]; nlinarith [sq_nonneg x]
    have hspos : 0 < Real.sqrt (w ^ 2 + x ^ 2) := hw.trans_le hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (by positivity) hw]
    have h3 : w ^ 3 ≤ Real.sqrt (w ^ 2 + x ^ 2) ^ 3 := pow_le_pow_left₀ hw.le hs 3
    nlinarith
  have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := h) (f' := h') (s := Set.univ) (C := 1 / w)
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) convex_univ
    (Set.mem_univ (v - D)) (Set.mem_univ (u - D))
  simp only [Real.norm_eq_abs] at hl
  have he : u - D - (v - D) = u - v := by ring
  rw [he] at hl
  simpa [valleySlope, h, div_eq_mul_inv, mul_comm] using hl

structure FlatShape where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  lip : ℝ
  deriv : ∀ u, HasDerivAt value (slope u) u
  lip_nonneg : 0 ≤ lip
  lip_spec : ∀ u v, |slope u - slope v| ≤ lip * |u - v|
  nonneg : ∀ u, 0 ≤ value u
  bounded : ∀ u, |slope u| ≤ 1

lemma FlatShape.continuous_slope (φ : FlatShape) : Continuous φ.slope := by
  apply continuous_iff_continuousAt.mpr
  intro u
  refine Metric.continuousAt_iff.mpr fun e he => ⟨e / (φ.lip + 1), by
    have : 0 < φ.lip + 1 := by linarith [φ.lip_nonneg]
    positivity, fun {v} hv => ?_⟩
  rw [Real.dist_eq] at hv ⊢
  have : 0 < φ.lip + 1 := by linarith [φ.lip_nonneg]
  calc |φ.slope v - φ.slope u| ≤ φ.lip * |v - u| := φ.lip_spec v u
    _ ≤ (φ.lip + 1) * |v - u| := by nlinarith [abs_nonneg (v - u)]
    _ < (φ.lip + 1) * (e / (φ.lip + 1)) := mul_lt_mul_of_pos_left hv this
    _ = e := by field_simp

noncomputable def valleyShape {w : ℝ} (hw : 0 < w) (D : ℝ) : FlatShape where
  value := valley w D
  slope := valleySlope w D
  lip := 1 / w
  deriv := hasDerivAt_valley hw D
  lip_nonneg := by positivity
  lip_spec u v := by
    have h := valleySlope_lipschitz hw D u v
    rw [div_eq_mul_inv] at h
    rw [one_div]
    linarith [mul_comm |u - v| w⁻¹]
  nonneg u := Real.sqrt_nonneg _
  bounded := abs_valleySlope_le w D

def stiff (i : Fin (min m n)) : Prop := i.val = 0

instance (i : Fin (min m n)) : Decidable (stiff i) := inferInstanceAs (Decidable (i.val = 0))

noncomputable def offset (x0 X : Space m n) (i : Fin (min m n)) : ℝ := X (dg i) - x0 (dg i)

noncomputable def objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) : ℝ :=
  ∑ i, if stiff i then ℓ / 2 * offset x0 X i ^ 2 else c * φ.value (offset x0 X i)

noncomputable def coefficients (ℓ c : ℝ) (φ : FlatShape) (u : Fin (min m n) → ℝ) :
    Fin (min m n) → ℝ :=
  fun i => if stiff i then ℓ * u i else c * φ.slope (u i)

lemma hasGradientAt_objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    HasGradientAt (objective ℓ c φ x0)
      (diagMat (coefficients ℓ c φ (offset x0 X))) X := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcoord (i : Fin (min m n)) : HasFDerivAt (fun Y : Space m n => offset x0 Y i)
      (EuclideanSpace.proj (dg i) : Space m n →L[ℝ] ℝ) X := by
    unfold offset
    exact (EuclideanSpace.proj (dg i) : Space m n →L[ℝ] ℝ).hasFDerivAt.sub_const _
  have hterm (i : Fin (min m n)) : HasFDerivAt (fun Y : Space m n =>
      if stiff i then ℓ / 2 * offset x0 Y i ^ 2 else c * φ.value (offset x0 Y i))
      (coefficients ℓ c φ (offset x0 X) i • (EuclideanSpace.proj (dg i) : Space m n →L[ℝ] ℝ))
      X := by
    by_cases hs : stiff i
    · simp only [hs, ↓reduceIte, coefficients]
      have hq : HasDerivAt (fun u : ℝ => ℓ / 2 * u ^ 2) (ℓ * offset x0 X i) (offset x0 X i) := by
        convert HasDerivAt.const_mul (ℓ / 2) ((hasDerivAt_id (offset x0 X i)).pow 2) using 1
        all_goals (try funext u)
        all_goals (try simp)
        all_goals (try ring)
      exact HasDerivAt.comp_hasFDerivAt (h₂ := fun u => ℓ / 2 * u ^ 2) X hq (hcoord i)
    · simp only [hs, ↓reduceIte, coefficients]
      exact HasDerivAt.comp_hasFDerivAt (h₂ := fun u => c * φ.value u) X
        ((φ.deriv (offset x0 X i)).const_mul c) (hcoord i)
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
  convert hsum using 1
  · funext Y
    simp [objective]
  · ext Y
    rw [InnerProductSpace.toDual_apply_apply, inner_diagMat]
    simp

lemma gradient_objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    gradient (objective ℓ c φ x0) X = diagMat (coefficients ℓ c φ (offset x0 X)) :=
  (hasGradientAt_objective ℓ c φ x0 X).gradient

lemma nuclear_gradient_objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    nuclearNorm (gradient (objective ℓ c φ x0) X) =
      ∑ i, |coefficients ℓ c φ (offset x0 X) i| := by
  rw [gradient_objective, nuclearNorm_diagMat]

lemma lipschitz_objective {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (φ : FlatShape)
    (x0 X Y : Space m n) :
    nuclearNorm (gradient (objective ℓ c φ x0) X - gradient (objective ℓ c φ x0) Y) ≤
      (∑ i : Fin (min m n), if stiff i then ℓ else c * φ.lip) * spectralNorm (X - Y) := by
  rw [gradient_objective, gradient_objective, ← diagMat_sub, nuclearNorm_diagMat,
    Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hd : |offset x0 X i - offset x0 Y i| ≤ spectralNorm (X - Y) := by
    have h := abs_apply_le_spectralNorm (X - Y) (dg i)
    simpa [offset, PiLp.sub_apply, sub_sub_sub_cancel_right] using h
  by_cases hs : stiff i
  · simp only [Pi.sub_apply, coefficients, hs, ↓reduceIte]
    rw [← mul_sub, abs_mul, abs_of_nonneg hℓ]
    exact mul_le_mul_of_nonneg_left hd hℓ
  · simp only [Pi.sub_apply, coefficients, hs, ↓reduceIte]
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    have hl := φ.lip_spec (offset x0 X i) (offset x0 Y i)
    calc c * |φ.slope (offset x0 X i) - φ.slope (offset x0 Y i)| ≤
          c * (φ.lip * |offset x0 X i - offset x0 Y i|) := mul_le_mul_of_nonneg_left hl hc
      _ ≤ c * φ.lip * spectralNorm (X - Y) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd φ.lip_nonneg) hc

lemma objective_nonneg {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (φ : FlatShape) (x0 X : Space m n) :
    0 ≤ objective ℓ c φ x0 X := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · positivity
  · exact mul_nonneg hc (φ.nonneg _)

lemma objective_start (ℓ c : ℝ) (φ : FlatShape) (x0 : Space m n) :
    objective ℓ c φ x0 x0 = ∑ i : Fin (min m n), if stiff i then 0 else c * φ.value 0 := by
  unfold objective offset
  apply Finset.sum_congr rfl
  intro i _
  simp

end LongTails.Proofs.SeparationInstance
