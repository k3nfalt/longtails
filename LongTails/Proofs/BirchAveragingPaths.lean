import LongTails.Setups.BirchNonIID
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import LongTails.Proofs.BirchSgdConvergence

namespace LongTails.Setups.BirchNonIID

/-- The population Hessian assumption supplies the correction-field Lipschitz bound.
This is a supporting mean-value lemma, not a new optimization result. -/
theorem gradientDifferenceSimilarity_of_secondOrderSimilarity
    {workers d : ℕ} {I : Instance workers d} {δ : ℝ}
    (h : SecondOrderSimilarity I δ) : GradientDifferenceSimilarity I δ := by
  intro i x y
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (𝕜 := ℝ)
    (fun z _ => (h.1 i z).sub (h.2.1 z))
    (fun z _ => ?_) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [fderiv_sub (h.1 i z) (h.2.1 z)] using h.2.2 i z

end LongTails.Setups.BirchNonIID

namespace BirchNonIIDResearch

/-- Scalar absorption estimate for the proposed averaging argument. -/
theorem exponential_dispersion_absorption {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hrt : r * t ≤ 1 / 8) (hexp : Real.exp (2 * t) ≤ 1 + 1 / r) :
    r ^ 2 * t * (Real.exp t - 1) ^ 2 ≤ 1 / 8 := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp ht
  have he2 : (Real.exp t) ^ 2 ≤ 1 + 1 / r := by
    simpa only [two_mul, Real.exp_add, pow_two] using hexp
  have hsq : (Real.exp t - 1) ^ 2 ≤ 1 / r := by nlinarith
  calc
    r ^ 2 * t * (Real.exp t - 1) ^ 2 ≤ r ^ 2 * t * (1 / r) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg r) ht)
    _ = r * t := by field_simp
    _ ≤ 1 / 8 := hrt

/-- The logarithmic round length controls both correction drift and dispersion. -/
theorem logarithmic_horizon_absorption {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (horizon : t ≤ Real.log (1 + 1 / r) / 8) :
    r * t ≤ 1 / 8 ∧ r ^ 2 * t * (Real.exp t - 1) ^ 2 ≤ 1 / 8 := by
  have hp : 0 < 1 + 1 / r := by positivity
  have hlog : Real.log (1 + 1 / r) ≤ 1 / r := by
    simpa using Real.log_le_sub_one_of_pos hp
  have ht' : t ≤ (1 / r) / 8 :=
    horizon.trans (div_le_div_of_nonneg_right hlog (by norm_num))
  have hrt : r * t ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left ht' hr.le
    convert h using 1; field_simp
  refine ⟨hrt, exponential_dispersion_absorption hr ht hrt ?_⟩
  have h2 : 2 * t ≤ Real.log (1 + 1 / r) := by linarith
  calc
    Real.exp (2 * t) ≤ Real.exp (Real.log (1 + 1 / r)) := Real.exp_le_exp.mpr h2
    _ = 1 + 1 / r := Real.exp_log hp

end BirchNonIIDResearch

open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

noncomputable def correctedDirection {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor x : Point d) : Point d :=
  gradient (I.localObjective i) x - gradient (I.localObjective i) anchor +
    gradient (objective I) anchor

theorem correctedDirection_at_anchor {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor : Point d) :
    correctedDirection I i anchor anchor = gradient (objective I) anchor := by
  simp [correctedDirection]

theorem correctedDirection_error {workers d : ℕ} {I : Instance workers d} {δ : ℝ}
    (h : GradientDifferenceSimilarity I δ) (i : Fin workers) (anchor x : Point d) :
    ‖correctedDirection I i anchor x - gradient (objective I) x‖ ≤ δ * ‖x - anchor‖ := by
  convert h i x anchor using 1
  congr 1
  unfold correctedDirection
  abel

noncomputable def localPath {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor : Point d) (η : ℝ) : ℕ → Point d
  | 0 => anchor
  | k + 1 => localPath I i anchor η k -
      η • correctedDirection I i anchor (localPath I i anchor η k)

noncomputable def centralPath {workers d : ℕ} (I : Instance workers d)
    (anchor : Point d) (η : ℝ) : ℕ → Point d
  | 0 => anchor
  | k + 1 => centralPath I anchor η k - η • gradient (objective I) (centralPath I anchor η k)

theorem localPath_first {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor : Point d) (η : ℝ) :
    localPath I i anchor η 1 = centralPath I anchor η 1 := by
  simp [localPath, centralPath, correctedDirection_at_anchor]

theorem correctedStep_deviation {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hη : 0 ≤ η) (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (i : Fin workers) (anchor y z : Point d) :
    ‖(y - η • correctedDirection I i anchor y) -
      (z - η • gradient (objective I) z)‖ ≤
        (1 + η * L) * ‖y - z‖ + η * δ * ‖y - anchor‖ := by
  let g := gradient (objective I)
  let v := correctedDirection I i anchor y
  have herr := correctedDirection_error hd i anchor y
  have hgrad := hs.2 y z
  change ‖(y - η • v) - (z - η • g z)‖ ≤ _
  calc
    ‖(y - η • v) - (z - η • g z)‖ =
        ‖(y - z) - η • (g y - g z) - η • (v - g y)‖ := by
      congr 1
      module
    _ ≤ ‖(y - z) - η • (g y - g z)‖ + ‖η • (v - g y)‖ := norm_sub_le _ _
    _ ≤ (‖y - z‖ + ‖η • (g y - g z)‖) + ‖η • (v - g y)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = ‖y - z‖ + η * ‖g y - g z‖ + η * ‖v - g y‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    _ ≤ (1 + η * L) * ‖y - z‖ + η * δ * ‖y - anchor‖ := by
      have h1 := mul_le_mul_of_nonneg_left hgrad hη
      have h2 := mul_le_mul_of_nonneg_left herr hη
      dsimp [g, v] at *
      nlinarith

theorem localPath_deviation_recurrence {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hη : 0 ≤ η) (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (i : Fin workers) (anchor : Point d) (k : ℕ) :
    ‖localPath I i anchor η (k + 1) - centralPath I anchor η (k + 1)‖ ≤
      (1 + η * L) * ‖localPath I i anchor η k - centralPath I anchor η k‖ +
        η * δ * ‖localPath I i anchor η k - anchor‖ := by
  exact correctedStep_deviation hη hs hd i anchor _ _

/-- An explicit finite-horizon bound for the scalar comparison recurrence. -/
theorem geometric_comparison {a : ℕ → ℝ} {η L δ D : ℝ}
    (hη : 0 ≤ η) (hL : 0 < L) (ha : a 0 = 0) :
    ∀ k, (∀ j < k, a (j + 1) ≤ (1 + η * L) * a j + η * δ * D) →
      a k ≤ δ / L * ((1 + η * L) ^ k - 1) * D := by
  intro k
  induction k with
  | zero => intro _; simp [ha]
  | succ k ih =>
    intro hstep
    have ih' := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    calc
      a (k + 1) ≤ (1 + η * L) * a k + η * δ * D := hstep k (Nat.lt_succ_self k)
      _ ≤ (1 + η * L) * (δ / L * ((1 + η * L) ^ k - 1) * D) + η * δ * D := by
        exact add_le_add (mul_le_mul_of_nonneg_left ih'
          (show 0 ≤ 1 + η * L by positivity)) le_rfl
      _ = δ / L * ((1 + η * L) ^ (k + 1) - 1) * D := by
        rw [pow_succ]
        field_simp; ring

/-- Finite local trajectories stay close to a centralized trajectory when their excursion is bounded. -/
theorem localPath_deviation_bound {workers d : ℕ} {I : Instance workers d} {L δ η D : ℝ}
    (hη : 0 ≤ η) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (i : Fin workers) (anchor : Point d) (K : ℕ)
    (hD : ∀ k < K, ‖localPath I i anchor η k - anchor‖ ≤ D) :
    ‖localPath I i anchor η K - centralPath I anchor η K‖ ≤
      δ / L * ((1 + η * L) ^ K - 1) * D := by
  apply geometric_comparison hη hL (by simp [localPath, centralPath]) K
  intro k hk
  exact (localPath_deviation_recurrence hη hs hd i anchor k).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hD k hk) (mul_nonneg hη hδ)))

theorem localPath_eq_sum {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor : Point d) (η : ℝ) (k : ℕ) :
    localPath I i anchor η k = anchor - η •
      ∑ j ∈ Finset.range k, correctedDirection I i anchor (localPath I i anchor η j) := by
  induction k with
  | zero => simp [localPath]
  | succ k ih =>
    change localPath I i anchor η k -
      η • correctedDirection I i anchor (localPath I i anchor η k) = _
    calc
      _ = (anchor - η • ∑ j ∈ Finset.range k,
          correctedDirection I i anchor (localPath I i anchor η j)) -
          η • correctedDirection I i anchor (localPath I i anchor η k) :=
        congrArg (fun z => z - η • correctedDirection I i anchor (localPath I i anchor η k)) ih
      _ = _ := by rw [Finset.sum_range_succ, smul_add]; abel

theorem localPath_excursion_energy {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor : Point d) {η : ℝ} (hη : 0 ≤ η) (k : ℕ) :
    ‖localPath I i anchor η k - anchor‖ ^ 2 ≤ η ^ 2 * (k : ℝ) *
      ∑ j ∈ Finset.range k, ‖correctedDirection I i anchor (localPath I i anchor η j)‖ ^ 2 := by
  let v := fun j => correctedDirection I i anchor (localPath I i anchor η j)
  have hn : ‖localPath I i anchor η k - anchor‖ ≤ η * ∑ j ∈ Finset.range k, ‖v j‖ := by
    rw [localPath_eq_sum]
    change ‖anchor - η • ∑ j ∈ Finset.range k, v j - anchor‖ ≤ _
    have he : anchor - η • ∑ j ∈ Finset.range k, v j - anchor =
        -(η • ∑ j ∈ Finset.range k, v j) := by abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hη
  have hsum : 0 ≤ ∑ j ∈ Finset.range k, ‖v j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq : ‖localPath I i anchor η k - anchor‖ ^ 2 ≤
      η ^ 2 * (∑ j ∈ Finset.range k, ‖v j‖) ^ 2 := by
    have hmul := mul_nonneg hη hsum
    have hnorm := norm_nonneg (localPath I i anchor η k - anchor)
    nlinarith
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := fun j => ‖v j‖)
  simp only [Finset.card_range] at hc
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg η)
  dsimp [v] at *
  nlinarith

theorem localPath_excursion_totalEnergy {workers d : ℕ} (I : Instance workers d)
    (i : Fin workers) (anchor : Point d) {η : ℝ} (hη : 0 ≤ η) {k K : ℕ} (hk : k ≤ K) :
    ‖localPath I i anchor η k - anchor‖ ^ 2 ≤ η ^ 2 * (K : ℝ) *
      ∑ j ∈ Finset.range K, ‖correctedDirection I i anchor (localPath I i anchor η j)‖ ^ 2 := by
  have hs : (∑ j ∈ Finset.range k,
      ‖correctedDirection I i anchor (localPath I i anchor η j)‖ ^ 2) ≤
      ∑ j ∈ Finset.range K, ‖correctedDirection I i anchor (localPath I i anchor η j)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => sq_nonneg _)
  have hn : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk
  have hm := mul_le_mul hn hs
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg K)
  have hmul := mul_le_mul_of_nonneg_left hm (sq_nonneg η)
  have he := localPath_excursion_energy I i anchor hη k
  nlinarith

/-- The endpoint deviation is controlled by the energy of the actual local updates. -/
theorem localPath_endpoint_energy {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hη : 0 ≤ η) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (i : Fin workers) (anchor : Point d) (K : ℕ) :
    ‖localPath I i anchor η K - centralPath I anchor η K‖ ^ 2 ≤
      (δ / L) ^ 2 * ((1 + η * L) ^ K - 1) ^ 2 * η ^ 2 * (K : ℝ) *
        ∑ k ∈ Finset.range K, ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2 := by
  let A := η ^ 2 * (K : ℝ) *
    ∑ k ∈ Finset.range K, ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD (k : ℕ) (hk : k < K) :
      ‖localPath I i anchor η k - anchor‖ ≤ Real.sqrt A := by
    have he := localPath_excursion_totalEnergy I i anchor hη hk.le
    have hroot := Real.sq_sqrt hA
    have hroot0 := Real.sqrt_nonneg A
    change ‖localPath I i anchor η k - anchor‖ ^ 2 ≤ A at he
    nlinarith [norm_nonneg (localPath I i anchor η k - anchor)]
  have hn := localPath_deviation_bound hη hL hδ hs hd i anchor K hD
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow, Real.sq_sqrt hA] at hsq
  dsimp [A] at hsq
  nlinarith

end LongTails.Setups.BirchNonIID

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

/-- Smooth descent with the exact squared correction error retained. -/
theorem direction_descent {d : ℕ} {f : Point d → ℝ} {L η : ℝ}
    (hs : LongTails.Setups.BirchSgd.SmoothObjective f L) (x v : Point d) :
    f (x - η • v) ≤ f x - η / 2 * ‖gradient f x‖ ^ 2 -
      η / 2 * (1 - L * η) * ‖v‖ ^ 2 + η / 2 * ‖gradient f x - v‖ ^ 2 := by
  have h := (OracleTemplate.Rennala.smooth_growth f L hs.1 hs.2).1 x (x - η • v)
  have he : x - η • v - x = -(η • v) := by abel
  rw [he, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hi : inner ℝ (gradient f x) v =
      (‖gradient f x‖ ^ 2 + ‖v‖ ^ 2 - ‖gradient f x - v‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]
    ring
  rw [hi] at h
  nlinarith

theorem localPath_descent_sum {workers d : ℕ} {I : Instance workers d} {L η : ℝ}
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (i : Fin workers) (anchor : Point d) (K : ℕ) :
    objective I (localPath I i anchor η K) ≤ objective I anchor -
      η / 2 * (∑ k ∈ Finset.range K, ‖gradient (objective I) (localPath I i anchor η k)‖ ^ 2) -
      η / 2 * (1 - L * η) * (∑ k ∈ Finset.range K,
        ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) +
      η / 2 * (∑ k ∈ Finset.range K,
        ‖gradient (objective I) (localPath I i anchor η k) -
          correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) := by
  induction K with
  | zero => simp [localPath]
  | succ K ih =>
    have hstep := direction_descent hs (localPath I i anchor η K)
      (correctedDirection I i anchor (localPath I i anchor η K)) (η := η)
    change objective I (localPath I i anchor η K -
      η • correctedDirection I i anchor (localPath I i anchor η K)) ≤ _
    simp only [Finset.sum_range_succ]
    nlinarith

theorem localPath_correction_energy {workers d : ℕ} {I : Instance workers d} {δ η : ℝ}
    (hd : GradientDifferenceSimilarity I δ) (hη : 0 ≤ η)
    (i : Fin workers) (anchor : Point d) (K : ℕ) :
    (∑ k ∈ Finset.range K,
      ‖gradient (objective I) (localPath I i anchor η k) -
        correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) ≤
      δ ^ 2 * η ^ 2 * (K : ℝ) ^ 2 * (∑ k ∈ Finset.range K,
        ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) := by
  let E := ∑ k ∈ Finset.range K, ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2
  have hpoint (k : ℕ) (hk : k ∈ Finset.range K) :
      ‖gradient (objective I) (localPath I i anchor η k) -
        correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2 ≤
      δ ^ 2 * η ^ 2 * (K : ℝ) * E := by
    have h := correctedDirection_error hd i anchor (localPath I i anchor η k)
    rw [norm_sub_rev] at h
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow] at hsq
    have he := localPath_excursion_totalEnergy I i anchor hη (Finset.mem_range.mp hk).le
    have hm := mul_le_mul_of_nonneg_left he (sq_nonneg δ)
    dsimp [E]
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  dsimp [E] at hsum
  nlinarith

end LongTails.Setups.BirchNonIID

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

theorem smooth_lower_taylor {d : ℕ} {f : Point d → ℝ} {L : ℝ}
    (hs : LongTails.Setups.BirchSgd.SmoothObjective f L) (x y : Point d) :
    f x + inner ℝ (gradient f x) (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hn : ∀ y, HasGradientAt (fun z => -f z) (-gradient f y) y :=
    fun y => by
      rw [hasGradientAt_iff_hasFDerivAt, map_neg]
      convert! (hs.1 y).hasFDerivAt.neg using 1
  have hnlip : ∀ y z, ‖-gradient f y - -gradient f z‖ ≤ L * ‖y - z‖ := by
    intro y z
    simpa only [neg_sub_neg, norm_sub_rev] using hs.2 y z
  have h := OracleTemplate.Gradient.smooth_upper_bound hn hnlip x y
  simp only [inner_neg_left] at h
  linarith

/-- The averaging defect requires only global smoothness and exact centering. -/
theorem centered_jensen_defect {n d : ℕ} {f : Point d → ℝ} {L : ℝ}
    (hs : LongTails.Setups.BirchSgd.SmoothObjective f L)
    (y : Fin n → Point d) (x : Point d) (hc : ∑ i, (y i - x) = 0) :
    (n : ℝ) * f x ≤ (∑ i, f (y i)) + L / 2 * ∑ i, ‖y i - x‖ ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => smooth_lower_taylor hs x (y i))
  have hi : (∑ i, inner ℝ (gradient f x) (y i - x)) = 0 := by
    rw [← inner_sum, hc, inner_zero_right]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hi] at h
  linarith

/-- A centered point minimizes the sum of squared distances. -/
theorem centered_variance_le {n d : ℕ} (y : Fin n → Point d) (x z : Point d)
    (hc : ∑ i, (y i - x) = 0) :
    (∑ i, ‖y i - x‖ ^ 2) ≤ ∑ i, ‖y i - z‖ ^ 2 := by
  have hi : (∑ i, inner ℝ (y i - x) (x - z)) = 0 := by
    rw [← sum_inner, hc, inner_zero_left]
  have he (i : Fin n) : ‖y i - z‖ ^ 2 =
      ‖y i - x‖ ^ 2 + ‖x - z‖ ^ 2 + 2 * inner ℝ (y i - x) (x - z) := by
    have hv : y i - z = (y i - x) + (x - z) := by abel
    rw [hv, norm_add_sq_real]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hi, mul_zero, add_zero]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))

noncomputable def pointMean {n d : ℕ} (y : Fin n → Point d) : Point d :=
  (n : ℝ)⁻¹ • ∑ i, y i

theorem pointMean_centered {n d : ℕ} (hn : 0 < n) (y : Fin n → Point d) :
    ∑ i, (y i - pointMean y) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, pointMean]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn', one_smul, sub_self]

/-- Compare the nonconvex mean objective with any common reference point. -/
theorem pointMean_jensen_comparator {n d : ℕ} {f : Point d → ℝ} {L : ℝ}
    (hn : 0 < n) (hL : 0 ≤ L)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective f L)
    (y : Fin n → Point d) (z : Point d) :
    (n : ℝ) * f (pointMean y) ≤
      (∑ i, f (y i)) + L / 2 * ∑ i, ‖y i - z‖ ^ 2 := by
  have hc := pointMean_centered hn y
  have hj := centered_jensen_defect hs y (pointMean y) hc
  have hv := centered_variance_le y (pointMean y) z hc
  exact hj.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (by positivity)))

/-- Averaging the actual local endpoints costs only their deviation energy. -/
theorem localPath_mean_objective {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hw : 0 < workers) (hη : 0 ≤ η) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (anchor : Point d) (K : ℕ) :
    (workers : ℝ) * objective I (pointMean (fun i => localPath I i anchor η K)) ≤
      (∑ i, objective I (localPath I i anchor η K)) +
      L / 2 * ((δ / L) ^ 2 * ((1 + η * L) ^ K - 1) ^ 2 * η ^ 2 * (K : ℝ)) *
        ∑ i, ∑ k ∈ Finset.range K,
          ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2 := by
  have hj := pointMean_jensen_comparator hw hL.le hs
    (fun i => localPath I i anchor η K) (centralPath I anchor η K)
  have he := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => localPath_endpoint_energy hη hL hδ hs hd i anchor K)
  rw [← Finset.mul_sum] at he
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ L / 2 by positivity)
  exact hj.trans (by nlinarith)

end LongTails.Setups.BirchNonIID

open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

/-- One actual averaging round, retaining both sources of energy loss. -/
theorem localPath_round_descent {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hw : 0 < workers) (hη : 0 ≤ η) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (anchor : Point d) (K : ℕ) :
    (workers : ℝ) * objective I (pointMean (fun i => localPath I i anchor η K)) ≤
      (workers : ℝ) * objective I anchor -
      η / 2 * (∑ i, ∑ k ∈ Finset.range K,
        ‖gradient (objective I) (localPath I i anchor η k)‖ ^ 2) -
      (η / 2 * (1 - L * η) - η / 2 * (δ ^ 2 * η ^ 2 * (K : ℝ) ^ 2) -
        L / 2 * ((δ / L) ^ 2 * ((1 + η * L) ^ K - 1) ^ 2 * η ^ 2 * (K : ℝ))) *
        (∑ i, ∑ k ∈ Finset.range K,
          ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) := by
  have hj := localPath_mean_objective hw hη hL hδ hs hd anchor K
  have hsummed := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => localPath_descent_sum hs i anchor K (η := η))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsummed
  have he := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => localPath_correction_energy hd hη i anchor K)
  rw [← Finset.mul_sum] at he
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ η / 2 by positivity)
  nlinarith

theorem logarithmic_round_coefficient {L δ η : ℝ} (K : ℕ)
    (hL : 0 < L) (hδ : 0 < δ) (hη : 0 ≤ η) (hstep : η * L ≤ 1 / 4)
    (hh : η * L * (K : ℝ) ≤ Real.log (1 + L / δ) / 8) :
    39 * η / 128 ≤ η / 2 * (1 - L * η) -
      η / 2 * (δ ^ 2 * η ^ 2 * (K : ℝ) ^ 2) -
      L / 2 * ((δ / L) ^ 2 * ((1 + η * L) ^ K - 1) ^ 2 * η ^ 2 * (K : ℝ)) := by
  let r := δ / L
  let t := η * L * (K : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hh' : t ≤ Real.log (1 + 1 / r) / 8 := by
    simpa [t, r, one_div_div] using hh
  obtain ⟨hrt, hexp⟩ := BirchNonIIDResearch.logarithmic_horizon_absorption hr ht hh'
  have hid : r * t = δ * η * (K : ℝ) := by
    dsimp [r, t]
    field_simp
  have hsmall : δ ^ 2 * η ^ 2 * (K : ℝ) ^ 2 ≤ 1 / 64 := by
    have hnon : 0 ≤ r * t := mul_nonneg hr.le ht
    have hsq := pow_le_pow_left₀ hnon hrt 2
    rw [hid] at hsq
    nlinarith
  have hb : 1 ≤ 1 + η * L := by linarith [mul_nonneg hη hL.le]
  have hq0 : 0 ≤ (1 + η * L) ^ K - 1 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hb K
    simpa using sub_nonneg.mpr h
  have hq : (1 + η * L) ^ K ≤ Real.exp t := by
    have he : 1 + η * L ≤ Real.exp (η * L) := by
      linarith [Real.add_one_le_exp (η * L)]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + η * L) he K
    simpa [← Real.exp_nat_mul, t, mul_comm, mul_left_comm, mul_assoc] using hp
  have hsq := pow_le_pow_left₀ hq0 (sub_le_sub_right hq 1) 2
  have hdisp : r ^ 2 * t * ((1 + η * L) ^ K - 1) ^ 2 ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hsq (by positivity)).trans hexp
  have hmul := mul_le_mul_of_nonneg_left hdisp (show 0 ≤ η / 2 by positivity)
  have heq : L / 2 * (r ^ 2 * ((1 + η * L) ^ K - 1) ^ 2 * η ^ 2 * (K : ℝ)) =
      η / 2 * (r ^ 2 * t * ((1 + η * L) ^ K - 1) ^ 2) := by dsimp [t]; ring
  have hcor := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ η / 2 by positivity)
  have hsteps := mul_le_mul_of_nonneg_left hstep hη
  change 39 * η / 128 ≤ η / 2 * (1 - L * η) -
    η / 2 * (δ ^ 2 * η ^ 2 * (K : ℝ) ^ 2) -
    L / 2 * (r ^ 2 * ((1 + η * L) ^ K - 1) ^ 2 * η ^ 2 * (K : ℝ))
  rw [heq]
  nlinarith

/-- A logarithmically safe round decreases the objective by its true gradient energy. -/
theorem logarithmic_round_descent {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hw : 0 < workers) (hη : 0 ≤ η) (hL : 0 < L) (hδ : 0 < δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (anchor : Point d) (K : ℕ)
    (hstep : η * L ≤ 1 / 4)
    (hh : η * L * (K : ℝ) ≤ Real.log (1 + L / δ) / 8) :
    (workers : ℝ) * objective I (pointMean (fun i => localPath I i anchor η K)) ≤
      (workers : ℝ) * objective I anchor -
      η / 2 * (∑ i, ∑ k ∈ Finset.range K,
        ‖gradient (objective I) (localPath I i anchor η k)‖ ^ 2) -
      39 * η / 128 * (∑ i, ∑ k ∈ Finset.range K,
        ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2) := by
  have hb := localPath_round_descent hw hη hL hδ.le hs hd anchor K
  have hc := logarithmic_round_coefficient K hL hδ hη hstep hh
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ ∑ i, ∑ k ∈ Finset.range K,
      ‖correctedDirection I i anchor (localPath I i anchor η k)‖ ^ 2 from
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  linarith

end LongTails.Setups.BirchNonIID

open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

noncomputable def serverPath {workers d : ℕ} (I : Instance workers d)
    (x0 : Point d) (η : ℝ) (K : ℕ) : ℕ → Point d
  | 0 => x0
  | r + 1 => pointMean (fun i => localPath I i (serverPath I x0 η K r) η K)

noncomputable def roundGradientEnergy {workers d : ℕ} (I : Instance workers d)
    (x : Point d) (η : ℝ) (K : ℕ) : ℝ :=
  ∑ i, ∑ k ∈ Finset.range K, ‖gradient (objective I) (localPath I i x η k)‖ ^ 2

theorem serverPath_energy_descent {workers d : ℕ} {I : Instance workers d} {L δ η : ℝ}
    (hw : 0 < workers) (hη : 0 ≤ η) (hL : 0 < L) (hδ : 0 < δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (x0 : Point d) (K R : ℕ)
    (hstep : η * L ≤ 1 / 4)
    (hh : η * L * (K : ℝ) ≤ Real.log (1 + L / δ) / 8) :
    (workers : ℝ) * objective I (serverPath I x0 η K R) ≤
      (workers : ℝ) * objective I x0 - η / 2 *
        ∑ r ∈ Finset.range R, roundGradientEnergy I (serverPath I x0 η K r) η K := by
  induction R with
  | zero => simp [serverPath]
  | succ R ih =>
    have hb := logarithmic_round_descent hw hη hL hδ hs hd
      (serverPath I x0 η K R) K hstep hh
    have he : 0 ≤ 39 * η / 128 * (∑ i, ∑ k ∈ Finset.range K,
        ‖correctedDirection I i (serverPath I x0 η K R)
          (localPath I i (serverPath I x0 η K R) η k)‖ ^ 2) := by positivity
    simp only [serverPath, Finset.sum_range_succ]
    change (workers : ℝ) * objective I
      (pointMean (fun i => localPath I i (serverPath I x0 η K R) η K)) ≤ _
    dsimp [roundGradientEnergy] at *
    linarith

/-- The finite trajectory guarantee; connecting it to randomized oracle execution is separate. -/
theorem serverPath_gradient_energy {workers d : ℕ} {I : Instance workers d} {L δ η Δ : ℝ}
    (hw : 0 < workers) (hη : 0 < η) (hL : 0 < L) (hδ : 0 < δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (x0 : Point d) (K R : ℕ)
    (hstep : η * L ≤ 1 / 4)
    (hh : η * L * (K : ℝ) ≤ Real.log (1 + L / δ) / 8)
    (hlower : ∀ x, I.lower ≤ objective I x)
    (hgap : objective I x0 - I.lower ≤ Δ) :
    (∑ r ∈ Finset.range R, roundGradientEnergy I (serverPath I x0 η K r) η K) ≤
      2 * (workers : ℝ) * Δ / η := by
  have hb := serverPath_energy_descent hw hη.le hL hδ hs hd x0 K R hstep hh
  have hl := mul_le_mul_of_nonneg_left (hlower (serverPath I x0 η K R))
    (Nat.cast_nonneg workers : (0 : ℝ) ≤ workers)
  have hg := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg workers : (0 : ℝ) ≤ workers)
  apply (le_div_iff₀ hη).mpr
  nlinarith

noncomputable def logarithmicStep (L δ : ℝ) (K : ℕ) : ℝ :=
  min (1 / (4 * L)) (Real.log (1 + L / δ) / (8 * L * (K : ℝ)))

theorem logarithmicStep_bounds {L δ : ℝ} {K : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hK : 0 < K) :
    0 < logarithmicStep L δ K ∧
    logarithmicStep L δ K * L ≤ 1 / 4 ∧
    logarithmicStep L δ K * L * (K : ℝ) ≤ Real.log (1 + L / δ) / 8 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : 0 < Real.log (1 + L / δ) := Real.log_pos (by
    have h := div_pos hL hδ
    linarith)
  have hpos : 0 < logarithmicStep L δ K := by
    dsimp [logarithmicStep]
    apply lt_min <;> positivity
  refine ⟨hpos, ?_, ?_⟩
  · have h := min_le_left (1 / (4 * L)) (Real.log (1 + L / δ) / (8 * L * (K : ℝ)))
    have hm := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp h
    change logarithmicStep L δ K * (4 * L) ≤ 1 at hm
    nlinarith
  · have h := min_le_right (1 / (4 * L)) (Real.log (1 + L / δ) / (8 * L * (K : ℝ)))
    have hm := (le_div_iff₀ (show 0 < 8 * L * (K : ℝ) by positivity)).mp h
    change logarithmicStep L δ K * (8 * L * (K : ℝ)) ≤ Real.log (1 + L / δ) at hm
    nlinarith

end LongTails.Setups.BirchNonIID
