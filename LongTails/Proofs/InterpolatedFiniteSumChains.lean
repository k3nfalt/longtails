import LongTails.Proofs.InterpolatedFiniteSumProfiles
import LongTails.Proofs.FiniteSumNondualLowerComponents
import LongTails.Proofs.CompactConjugate
import LongTails.Proofs.InterpolatedFiniteSumCentering
import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.InterpolatedFiniteSumChains

open InterpolatedFiniteSumProfiles FiniteSumNondualLowerComponents

noncomputable def energy {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) : ℝ :=
  separableEnergy (fun _ => profile) x

noncomputable def field {ι : Type*} (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  separableSlope (fun _ => profileSlope) x

lemma energy_model {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    0 ≤ energy y - energy x - ⟪field x, y - x⟫ ∧
      energy y - energy x - ⟪field x, y - x⟫ ≤ 3 / 2 * ‖y - x‖ ^ 2 := by
  have he : energy y - energy x - ⟪field x, y - x⟫ =
      ∑ j, (profile (y j) - profile (x j) - profileSlope (x j) * (y j - x j)) := by
    simp [energy, field, separableEnergy, separableSlope, PiLp.inner_apply,
      RCLike.inner_apply, Finset.sum_sub_distrib, mul_comm]
  rw [he, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact ⟨Finset.sum_nonneg (fun j _ => (profile_remainder (x j) (y j)).1),
    Finset.sum_le_sum (fun j _ => (profile_remainder (x j) (y j)).2)⟩

lemma energy_hasGradientAt {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    HasGradientAt energy (field x) x :=
  CompactConjugate.hasGradientAt_of_quadratic_remainder energy x (field x) (3 / 2)
    (energy_model x)

lemma field_differentiable {ι : Type*} [Fintype ι] :
    Differentiable ℝ (field : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
  have hd : Differentiable ℝ (fun x : EuclideanSpace ℝ ι => fun i => profileSlope (x i)) := by
    apply differentiable_pi.mpr
    intro i
    have hs : Differentiable ℝ profileSlope := fun t => (profileSlope_hasDerivAt t).differentiableAt
    exact hs.comp
      (PiLp.proj 2 (fun _ : ι => ℝ) i).differentiable
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.differentiable.comp hd

lemma field_lipschitz {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ‖field x - field y‖ ≤ 3 * ‖x - y‖ := by
  have hs : ‖field x - field y‖ ^ 2 ≤ 9 * ‖x - y‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change (profileSlope (x j) - profileSlope (y j)) ^ 2 ≤ 9 * (x j - y j) ^ 2
    have hh := pow_le_pow_left₀ (abs_nonneg _) (profileSlope_lipschitz (x j) (y j)) 2
    norm_num [sq_abs, mul_pow] at hh ⊢
    exact hh
  nlinarith [norm_nonneg (field x - field y), norm_nonneg (x - y)]

lemma field_curvature {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (field : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤ 3 := by
  apply norm_fderiv_le_of_lipschitz ℝ (C := (3 : NNReal))
  exact LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using field_lipschitz x y)

lemma field_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖field x‖ ≤ Real.sqrt (Fintype.card ι) := by
  have hs : ‖field x‖ ^ 2 ≤ Fintype.card ι := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun j _ => by
        change profileSlope (x j) ^ 2 ≤ 1
        obtain ⟨hl, hu⟩ := abs_le.mp (profileSlope_bound (x j))
        nlinarith)
      _ = _ := by simp
  exact Real.le_sqrt_of_sq_le hs

lemma energy_nonnegative {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    0 ≤ energy x := Finset.sum_nonneg (fun i _ => profile_nonnegative (x i))

lemma energy_convex {ι : Type*} [Fintype ι] :
    ConvexOn ℝ Set.univ (energy : EuclideanSpace ℝ ι → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change ∑ i, profile (a * x i + b * y i) ≤ a * ∑ i, profile (x i) + b * ∑ i, profile (y i)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => profile_convex.2 (Set.mem_univ _) (Set.mem_univ _)
    ha hb hab)

lemma mapped_gradient {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y => energy (A y)) (A.adjoint (field (A x))) x := by
  have hd := (energy_hasGradientAt (A x)).hasFDerivAt.comp x A.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    exact A.adjoint_inner_left v (field (A x))

lemma mapped_differentiable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) :
    Differentiable ℝ (fun x => A.adjoint (field (A x))) :=
  A.adjoint.differentiable.comp (field_differentiable.comp A.differentiable)

lemma mapped_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (x y : EuclideanSpace ℝ ι) :
    ‖A.adjoint (field (A x)) - A.adjoint (field (A y))‖ ≤ 3 * ‖A‖ ^ 2 * ‖x - y‖ := by
  rw [← map_sub]
  calc
    _ ≤ ‖A.adjoint‖ * ‖field (A x) - field (A y)‖ := A.adjoint.le_opNorm _
    _ = ‖A‖ * ‖field (A x) - field (A y)‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖A‖ * (3 * ‖A x - A y‖) :=
      mul_le_mul_of_nonneg_left (field_lipschitz (A x) (A y)) (norm_nonneg _)
    _ ≤ ‖A‖ * (3 * (‖A‖ * ‖x - y‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← map_sub]
      exact A.le_opNorm _
    _ = _ := by ring

lemma mapped_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (x : EuclideanSpace ℝ ι) :
    ‖A.adjoint (field (A x))‖ ≤ ‖A‖ * Real.sqrt (Fintype.card κ) := by
  have h := A.adjoint.le_opNorm (field (A x))
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_left (field_norm _) (norm_nonneg _))

noncomputable def chainValue {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ)
    (v x : EuclideanSpace ℝ ι) : ℝ := c * energy (A x) - ⟪v, x⟫

noncomputable def chainField {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ)
    (v x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι := c • A.adjoint (field (A x)) - v

lemma chainValue_hasGradientAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ)
    (v x : EuclideanSpace ℝ ι) : HasGradientAt (chainValue A c v) (chainField A c v x) x := by
  apply InterpolatedFiniteSumCentering.centered_gradient
    (fun y => c * energy (A y)) (fun y => c • A.adjoint (field (A y))) v x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (mapped_gradient A x).hasFDerivAt.const_mul c using 1
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, smul_apply,
      smul_eq_mul]

lemma chainField_differentiable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ) (v : EuclideanSpace ℝ ι) :
    Differentiable ℝ (chainField A c v) :=
  ((mapped_differentiable A).const_smul c).sub_const v

lemma chainField_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ) (hc : 0 ≤ c)
    (v x y : EuclideanSpace ℝ ι) :
    ‖chainField A c v x - chainField A c v y‖ ≤ 3 * c * ‖A‖ ^ 2 * ‖x - y‖ := by
  simp only [chainField, sub_sub_sub_cancel_right, ← smul_sub, norm_smul, Real.norm_of_nonneg hc]
  have h := mul_le_mul_of_nonneg_left (mapped_lipschitz A x y) hc
  convert h using 1
  ring

lemma chainField_curvature {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ) (hc : 0 ≤ c)
    (v x : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (chainField A c v) x‖ ≤ 3 * c * ‖A‖ ^ 2 := by
  apply norm_fderiv_le_of_lipschitz ℝ (C := ⟨3 * c * ‖A‖ ^ 2, by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖chainField A c v x - chainField A c v y‖ ≤ 3 * c * ‖A‖ ^ 2 * ‖x - y‖
  exact chainField_lipschitz A c hc v x y

lemma chainField_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ) (hc : 0 ≤ c)
    (v x : EuclideanSpace ℝ ι) :
    ‖chainField A c v x‖ ≤ c * ‖A‖ * Real.sqrt (Fintype.card κ) + ‖v‖ := by
  have h := norm_sub_le (c • A.adjoint (field (A x))) v
  rw [norm_smul, Real.norm_of_nonneg hc] at h
  have h' := mul_le_mul_of_nonneg_left (mapped_norm A x) hc
  dsimp [chainField]
  nlinarith

lemma chainValue_convex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (c : ℝ) (hc : 0 ≤ c)
    (v : EuclideanSpace ℝ ι) : ConvexOn ℝ Set.univ (chainValue A c v) := by
  apply InterpolatedFiniteSumCentering.centered_convex (fun x => c * energy (A x)) v
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (energy_convex (ι := κ)).2 (Set.mem_univ (A x)) (Set.mem_univ (A y)) ha hb hab
  have hh := mul_le_mul_of_nonneg_left h hc
  simpa only [map_add, map_smul, smul_eq_mul, mul_add, mul_left_comm] using hh

lemma profile_support_one (t : ℝ) : t - 1 / 2 ≤ profile t := by
  have hp := ramp_two_above_linear (2 * t - 1 / 2)
  have hn := AdaptivePolynomialHinge.ramp_nonnegative 2 (by omega) (-2 * t - 1 / 2)
  dsimp [profile]
  linarith

noncomputable def sequenceValue (c σ : ℝ) (T : ℕ) (y : ℕ → ℝ) : ℝ :=
  -(c / σ) * y 0 + ∑ j ∈ Finset.range T, c * profile ((y j - y (j + 1)) / σ)

lemma sequence_prefix (c σ : ℝ) (hc : 0 ≤ c) (T p : ℕ) (hp : p ≤ T) (y : ℕ → ℝ) :
    -(c / σ) * y p - p * c / 2 ≤ sequenceValue c σ T y := by
  have h₁ := Finset.sum_le_sum (s := Finset.range p) (fun j _ =>
    mul_le_mul_of_nonneg_left (profile_support_one ((y j - y (j + 1)) / σ)) hc)
  have h₂ : (∑ j ∈ Finset.range p, c * profile ((y j - y (j + 1)) / σ)) ≤
      ∑ j ∈ Finset.range T, c * profile ((y j - y (j + 1)) / σ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
      (fun j _ _ => mul_nonneg hc (profile_nonnegative _))
  have he : (∑ j ∈ Finset.range p, c * ((y j - y (j + 1)) / σ - 1 / 2)) =
      (c / σ) * (y 0 - y p) - p * c / 2 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_range_sub']
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [he] at h₁
  dsimp [sequenceValue]
  linarith

lemma sequence_minimum (c σ : ℝ) (hc : 0 ≤ c) (T : ℕ) (y : ℕ → ℝ) (hy : y T = 0) :
    -(T : ℝ) * c / 2 ≤ sequenceValue c σ T y := by
  have h := sequence_prefix c σ hc T T le_rfl y
  rw [hy, mul_zero] at h
  linarith

lemma sequence_minimizer (c σ : ℝ) (hσ : σ ≠ 0) (T : ℕ) :
    sequenceValue c σ T (fun j => ((T : ℝ) - j) * σ) = -(T : ℝ) * c / 2 := by
  have he (j : ℕ) : (((T : ℝ) - j) * σ - ((T : ℝ) - (j + 1 : ℕ)) * σ) / σ = 1 := by
    push_cast
    field_simp
    ring
  simp only [sequenceValue, Nat.cast_zero, sub_zero, he,
    (profile_linear 1 (by norm_num)).1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

noncomputable def tailMap (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Fin.lastCases (x (Fin.last k))
        (fun j => x j.castSucc - x j.succ))
      map_add' := by
        intro x y
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp
        · simp; ring
      map_smul' := by
        intro a x
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp
        · simp; ring }

lemma tailMap_apply_last (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    tailMap k x (Fin.last k) = x (Fin.last k) := by simp [tailMap]

lemma tailMap_apply_castSucc (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin k) :
    tailMap k x j.castSucc = x j.castSucc - x j.succ := by simp [tailMap]

lemma tailMap_norm (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ‖tailMap k x‖ ≤ 2 * ‖x‖ := by
  have he : ‖tailMap k x‖ ^ 2 = (∑ j : Fin k, (x j.castSucc - x j.succ) ^ 2) +
      x (Fin.last k) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    simp only [tailMap_apply_castSucc, tailMap_apply_last]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) (_ : j ∈ Finset.univ) =>
    show (x j.castSucc - x j.succ) ^ 2 ≤ 2 * x j.castSucc ^ 2 + 2 * x j.succ ^ 2 by
      nlinarith [sq_nonneg (x j.castSucc + x j.succ)])
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hb
  have hl : (∑ j : Fin k, x j.castSucc ^ 2) + x (Fin.last k) ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  have hr : x 0 ^ 2 + (∑ j : Fin k, x j.succ ^ 2) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  nlinarith [norm_nonneg (tailMap k x), norm_nonneg x, sq_nonneg (x 0),
    sq_nonneg (x (Fin.last k))]

noncomputable def selectedTail {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (tailMap k).comp (coordinateMap π)

lemma selectedTail_opNorm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) :
    ‖selectedTail π‖ ≤ 2 := by
  apply (selectedTail π).opNorm_le_bound (by norm_num)
  intro x
  exact (tailMap_norm k (coordinateMap π x)).trans
    (mul_le_mul_of_nonneg_left (coordinateMap_norm π x) (by norm_num))

noncomputable def extended {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) (j : ℕ) : ℝ :=
  if h : j < k + 1 then x ⟨j, h⟩ else 0

lemma extended_fin {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin (k + 1)) :
    extended x j = x j := by simp [extended, j.isLt]

lemma extended_terminal {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) :
    extended x (k + 1) = 0 := by simp [extended]

lemma tailMap_sequence {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin (k + 1)) :
    tailMap k x j = extended x j - extended x (j + 1) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [tailMap_apply_last, Fin.val_last, extended_terminal, sub_zero]
    exact (extended_fin x (Fin.last k)).symm
  · rw [tailMap_apply_castSucc, extended_fin]
    have he : (i.castSucc : ℕ) + 1 = (i.succ : ℕ) := rfl
    rw [he, extended_fin]

lemma energy_sequence {k : ℕ} (σ : ℝ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    energy (σ⁻¹ • tailMap k x) =
      ∑ j ∈ Finset.range (k + 1), profile ((extended x j - extended x (j + 1)) / σ) := by
  change (∑ j : Fin (k + 1), profile (σ⁻¹ * tailMap k x j)) = _
  simp_rw [tailMap_sequence, ← div_eq_inv_mul]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    profile ((extended x j - extended x (j + 1)) / σ)) (k + 1)

lemma selected_sequence {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    chainValue (σ⁻¹ • selectedTail π) c (PiLp.single 2 (π 0) (c / σ)) x =
      sequenceValue c σ (k + 1) (extended (coordinateMap π x)) := by
  have h0 : extended (coordinateMap π x) 0 = x (π 0) := by
    simp [extended, coordinateMap]
  simp only [chainValue, selectedTail, smul_apply,
    ContinuousLinearMap.comp_apply, energy_sequence, sequenceValue,
    ← Finset.mul_sum, h0]
  rw [EuclideanSpace.inner_single_left]
  simp only [starRingEnd_apply, star_trivial]
  ring


lemma coordinateMap_opNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (π : κ ↪ ι) :
    ‖coordinateMap π‖ ≤ 1 := by
  apply (coordinateMap π).opNorm_le_bound (by norm_num)
  intro x
  simpa only [one_mul] using coordinateMap_norm π x

lemma coordinateMap_single {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (π : κ ↪ ι) (j : κ) :
    coordinateMap π (PiLp.single 2 (π j) (1 : ℝ)) = PiLp.single 2 j 1 := by
  ext i
  change (PiLp.single 2 (π j) (1 : ℝ) : EuclideanSpace ℝ ι) (π i) =
    (PiLp.single 2 j (1 : ℝ) : EuclideanSpace ℝ κ) i
  simp only [PiLp.single_apply, π.injective.eq_iff]

lemma coordinateMap_adjoint_coordinate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (π : κ ↪ ι) (y : EuclideanSpace ℝ κ) (j : κ) :
    (coordinateMap π).adjoint y (π j) = y j := by
  classical
  have h := (coordinateMap π).adjoint_inner_left (PiLp.single 2 (π j) (1 : ℝ)) y
  rw [coordinateMap_single] at h
  simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using h

lemma coordinateMap_adjoint_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (π : κ ↪ ι) (y : EuclideanSpace ℝ κ) : coordinateMap π ((coordinateMap π).adjoint y) = y := by
  ext j
  exact coordinateMap_adjoint_coordinate π y j

lemma coordinateMap_adjoint_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (π : κ ↪ ι) (y : EuclideanSpace ℝ κ) : ‖(coordinateMap π).adjoint y‖ ≤ ‖y‖ := by
  have h := (coordinateMap π).adjoint.le_opNorm y
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (by nlinarith [coordinateMap_opNorm π, norm_nonneg y])

noncomputable def descendingVector (k : ℕ) (σ : ℝ) : EuclideanSpace ℝ (Fin (k + 1)) :=
  WithLp.toLp 2 (fun j => ((k + 1 : ℕ) - (j : ℝ)) * σ)

lemma descendingVector_norm (k : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) :
    ‖descendingVector k σ‖ ≤ (k + 1 : ℕ) * σ * Real.sqrt (k + 1 : ℕ) := by
  have hs : ‖descendingVector k σ‖ ^ 2 ≤ (k + 1 : ℕ) * ((k + 1 : ℕ) * σ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin (k + 1), (((k + 1 : ℕ) : ℝ) * σ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        change (((k + 1 : ℕ) - (j : ℝ)) * σ) ^ 2 ≤ _
        have hj : (j : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast j.isLt.le
        have hj0 : (0 : ℝ) ≤ j := by positivity
        have h₁ := mul_le_mul_of_nonneg_right (sub_le_self ((k + 1 : ℕ) : ℝ) hj0) hσ
        have h₂ := mul_nonneg (sub_nonneg.mpr hj) hσ
        nlinarith
      _ = _ := by simp
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℕ) by positivity)
  have hn : 0 ≤ (((k + 1 : ℕ) : ℝ) * σ * Real.sqrt (k + 1 : ℕ)) := by positivity
  nlinarith [norm_nonneg (descendingVector k σ)]

lemma sequence_prefix_gap (c σ : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (T r : ℕ)
    (hr : r ≤ T) (y : ℕ → ℝ) (α : ℝ) (hy : y r ≤ α) :
    ((T : ℝ) - r) * c / 2 - c * α / σ ≤ sequenceValue c σ T y + T * c / 2 := by
  have h := sequence_prefix c σ hc T r hr y
  have h' := mul_le_mul_of_nonneg_left hy (div_nonneg hc hσ.le)
  simp only [div_eq_mul_inv] at h h' ⊢
  nlinarith only [h, h']

lemma sequence_congr (c σ : ℝ) (T : ℕ) (x y : ℕ → ℝ)
    (h : ∀ j, j ≤ T → x j = y j) : sequenceValue c σ T x = sequenceValue c σ T y := by
  unfold sequenceValue
  rw [h 0 (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [h j (by omega), h (j + 1) (by omega)]

lemma descendingVector_sequence (k : ℕ) (σ : ℝ) (j : ℕ) (hj : j ≤ k + 1) :
    extended (descendingVector k σ) j = ((k + 1 : ℕ) - (j : ℝ)) * σ := by
  by_cases h : j < k + 1
  · simp [extended, h, descendingVector]
  · have he : j = k + 1 := by omega
    subst j
    simp [extended_terminal]

noncomputable def rawChain {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  chainValue (σ⁻¹ • selectedTail π) c (PiLp.single 2 (π 0) (c / σ))

noncomputable def rawField {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  chainField (σ⁻¹ • selectedTail π) c (PiLp.single 2 (π 0) (c / σ))

noncomputable def chainMinimizer {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (σ : ℝ) :
    EuclideanSpace ℝ (Fin d) := (coordinateMap π).adjoint (descendingVector k σ)

lemma rawChain_gradient {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (rawChain π c σ) (rawField π c σ x) x :=
  chainValue_hasGradientAt _ _ _ _

lemma rawField_differentiable {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) :
    Differentiable ℝ (rawField π c σ) := chainField_differentiable _ _ _

lemma rawChain_convex {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) (hc : 0 ≤ c) :
    ConvexOn ℝ Set.univ (rawChain π c σ) := chainValue_convex _ _ hc _

lemma rawChain_lower {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) (hc : 0 ≤ c)
    (x : EuclideanSpace ℝ (Fin d)) : -((k + 1 : ℕ) : ℝ) * c / 2 ≤ rawChain π c σ x := by
  rw [rawChain, selected_sequence]
  exact sequence_minimum c σ hc (k + 1) _ (extended_terminal _)

lemma rawChain_minimum {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) (hσ : σ ≠ 0) :
    rawChain π c σ (chainMinimizer π σ) = -((k + 1 : ℕ) : ℝ) * c / 2 := by
  rw [rawChain, selected_sequence, chainMinimizer, coordinateMap_adjoint_right]
  rw [sequence_congr c σ (k + 1) _ _ (descendingVector_sequence k σ)]
  exact sequence_minimizer c σ hσ (k + 1)

lemma rawChain_zero {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ) :
    rawChain π c σ 0 = 0 := by
  simp [rawChain, chainValue, energy, separableEnergy, profile, AdaptivePolynomialHinge.ramp]

lemma chainMinimizer_norm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (σ : ℝ) (hσ : 0 ≤ σ) :
    ‖chainMinimizer π σ‖ ≤ (k + 1 : ℕ) * σ * Real.sqrt (k + 1 : ℕ) :=
  (coordinateMap_adjoint_norm π _).trans (descendingVector_norm k σ hσ)

lemma scaledTail_opNorm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (σ : ℝ) (hσ : 0 < σ) :
    ‖σ⁻¹ • selectedTail π‖ ≤ 2 / σ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hσ.le)]
  have h := mul_le_mul_of_nonneg_left (selectedTail_opNorm π) (inv_nonneg.mpr hσ.le)
  simpa only [div_eq_inv_mul] using h

lemma rawField_norm {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖rawField π c σ x‖ ≤ (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) := by
  have h := chainField_norm (σ⁻¹ • selectedTail π) c hc (PiLp.single 2 (π 0) (c / σ)) x
  rw [PiLp.norm_single, Real.norm_of_nonneg (div_nonneg hc hσ.le), Fintype.card_fin] at h
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (scaledTail_opNorm π σ hσ) hc) (Real.sqrt_nonneg (k + 1 : ℕ))
  change ‖chainField _ _ _ x‖ ≤ _
  simp only [div_eq_mul_inv] at h hh ⊢
  nlinarith only [h, hh]

lemma rawField_curvature {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (hc : 0 ≤ c) (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (rawField π c σ) x‖ ≤ 12 * c / σ ^ 2 := by
  have h := chainField_curvature (σ⁻¹ • selectedTail π) c hc (PiLp.single 2 (π 0) (c / σ)) x
  have hs := pow_le_pow_left₀ (norm_nonneg _) (scaledTail_opNorm π σ hσ) 2
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 * c by positivity)
  change ‖fderiv ℝ (chainField _ _ _) x‖ ≤ _
  simp only [div_pow] at hh
  calc
    _ ≤ 3 * c * ‖σ⁻¹ • selectedTail π‖ ^ 2 := h
    _ ≤ 3 * c * (2 ^ 2 / σ ^ 2) := hh
    _ = _ := by ring

lemma coordinateMap_adjoint_outside {ι κ : Type*} [Fintype ι] [Fintype κ]
    (π : κ ↪ ι) (y : EuclideanSpace ℝ κ) (j : ι) (hj : ∀ i, π i ≠ j) :
    (coordinateMap π).adjoint y j = 0 := by
  classical
  have hs : coordinateMap π (PiLp.single 2 j (1 : ℝ)) = 0 := by
    ext i
    change (PiLp.single 2 j (1 : ℝ) : EuclideanSpace ℝ ι) (π i) = 0
    simp only [PiLp.single_apply, ite_eq_right (hj i)]
  have hh := (coordinateMap π).adjoint_inner_left (PiLp.single 2 j (1 : ℝ)) y
  rw [hs, inner_zero_right, EuclideanSpace.inner_single_right] at hh
  simpa only [RCLike.conj_to_real, one_mul] using hh

end LongTails.Proofs.InterpolatedFiniteSumChains
