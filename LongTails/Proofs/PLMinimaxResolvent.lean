import LongTails.Algorithms.PLMinimaxCubic
import LongTails.Proofs.PLMinimaxGeometry

open InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_square_energy (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) (t : ℝ) (b : E) :
    ⟪K (K b) + t • b, b⟫ = ‖K b‖ ^ 2 + t * ‖b‖ ^ 2 := by
  rw [inner_add_left, real_inner_smul_left, hs, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

lemma regularized_square_bound (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (_ht : 0 < t) (b : E) :
    t * ‖b‖ ≤ ‖K (K b) + t • b‖ := by
  have he := regularized_square_energy K hs t b
  have hi := real_inner_le_norm (K (K b) + t • b) b
  by_cases hb : ‖b‖ = 0
  · simp [hb]
  · have hb' : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb)
    nlinarith [sq_nonneg ‖K b‖]

lemma regularized_square_image_bound (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (_ht : 0 ≤ t) (b : E) :
    4 * t * ‖K b‖ ^ 2 ≤ ‖K (K b) + t • b‖ ^ 2 := by
  have he : ⟪K (K b), b⟫ = ‖K b‖ ^ 2 := by
    rw [hs, real_inner_self_eq_norm_sq]
  have hm := norm_sub_sq_real (K (K b)) (t • b)
  have hp := norm_add_sq_real (K (K b)) (t • b)
  rw [inner_smul_right, he] at hm hp
  nlinarith [sq_nonneg ‖K (K b) - t • b‖]

lemma regularized_square_injective (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) :
    Function.Injective (K.comp K + t • ContinuousLinearMap.id ℝ E) := by
  intro a b hab
  have hzero : K (K (a - b)) + t • (a - b) = 0 := by
    change K (K a) + t • a = K (K b) + t • b at hab
    calc K (K (a - b)) + t • (a - b)
        = (K (K a) + t • a) - (K (K b) + t • b) := by
          simp only [map_sub, smul_sub]
          abel
      _ = 0 := sub_eq_zero.mpr hab
  have hb := regularized_square_bound K hs ht (a - b)
  rw [hzero, norm_zero] at hb
  have hn : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma regularized_square_surjective [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) :
    Function.Surjective (K.comp K + t • ContinuousLinearMap.id ℝ E) :=
  LinearMap.injective_iff_surjective.mp (regularized_square_injective K hs ht)

lemma kernel_primal_component (H : E →L[ℝ] E) {L : ℝ} (hL : 0 < L)
    (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (a b : E)
    (hab : ⟪a, b⟫ = 0) (hbound : ‖H a‖ ≤ L * ‖a‖)
    (hdual : ⟪H b, b⟫ ≤ 0) (hzero : H (a + b) + (2 * L) • a = 0) : a = 0 := by
  have hz := congrArg (fun v => ⟪v, a - b⟫) hzero
  simp only [map_add, inner_add_left, inner_sub_right, real_inner_smul_left,
    inner_zero_left, hab, sub_zero, real_inner_self_eq_norm_sq] at hz
  have hc : ⟪H b, a⟫ = ⟪H a, b⟫ := (hs b a).trans (real_inner_comm (H a) b)
  rw [hc] at hz
  have hi := (abs_le.mp (abs_real_inner_le_norm (H a) a)).1
  have hn := mul_le_mul_of_nonneg_right hbound (norm_nonneg a)
  have hp : L * ‖a‖ ^ 2 ≤ 0 := by nlinarith
  have hsq : ‖a‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hL).mp (by simpa using hp)
  have ha : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
  exact norm_eq_zero.mp ha

lemma squaredRegularization_invertible [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) :
    (squaredRegularization K t).IsInvertible := by
  let e := (LinearEquiv.ofBijective (squaredRegularization K t).toLinearMap
    ⟨regularized_square_injective K hs ht, regularized_square_surjective K hs ht⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

lemma squaredRegularization_inverse_bound [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (v : E) :
    t * ‖(squaredRegularization K t).inverse v‖ ≤ ‖v‖ := by
  have hh := regularized_square_bound K hs ht ((squaredRegularization K t).inverse v)
  have he := (squaredRegularization_invertible K hs ht).self_apply_inverse v
  change K (K ((squaredRegularization K t).inverse v)) +
    t • (squaredRegularization K t).inverse v = v at he
  rwa [he] at hh

lemma tikhonovResponse_bound [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (v : E) :
    4 * t * ‖tikhonovResponse K t v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hh := regularized_square_image_bound K hs ht.le ((squaredRegularization K t).inverse v)
  have he := (squaredRegularization_invertible K hs ht).self_apply_inverse v
  change K (K ((squaredRegularization K t).inverse v)) +
    t • (squaredRegularization K t).inverse v = v at he
  rwa [he] at hh

lemma squaredRegularization_symmetric (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) (t : ℝ) (u v : E) :
    ⟪squaredRegularization K t u, v⟫ = ⟪u, squaredRegularization K t v⟫ := by
  change ⟪K (K u) + t • u, v⟫ = ⟪u, K (K v) + t • v⟫
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
  rw [hs, hs]

lemma inverse_symmetric (A : E →L[ℝ] E) (hi : A.IsInvertible)
    (hs : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫) (u v : E) :
    ⟪A.inverse u, v⟫ = ⟪u, A.inverse v⟫ := by
  calc
    ⟪A.inverse u, v⟫ = ⟪A.inverse u, A (A.inverse v)⟫ := by rw [hi.self_apply_inverse]
    _ = ⟪A (A.inverse u), A.inverse v⟫ := (hs _ _).symm
    _ = ⟪u, A.inverse v⟫ := by rw [hi.self_apply_inverse]

lemma squaredRegularization_inverse_commute [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (v : E) :
    K ((squaredRegularization K t).inverse v) = (squaredRegularization K t).inverse (K v) := by
  have hi := squaredRegularization_invertible K hs ht
  apply hi.bijective.1
  rw [hi.self_apply_inverse]
  have hc : ∀ u, squaredRegularization K t (K u) = K (squaredRegularization K t u) := by
    intro u
    simp [squaredRegularization, map_add, map_smul]
  rw [hc, hi.self_apply_inverse]

lemma tikhonovResponse_symmetric [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (u v : E) :
    ⟪tikhonovResponse K t u, v⟫ = ⟪u, tikhonovResponse K t v⟫ := by
  change ⟪K ((squaredRegularization K t).inverse u), v⟫ =
    ⟪u, K ((squaredRegularization K t).inverse v)⟫
  rw [hs, inverse_symmetric _ (squaredRegularization_invertible K hs ht)
    (squaredRegularization_symmetric K hs t), squaredRegularization_inverse_commute K hs ht]

lemma tikhonovResponse_bias_identity [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (v : E) :
    tikhonovResponse K t (K v) - v = -t • (squaredRegularization K t).inverse v := by
  change K ((squaredRegularization K t).inverse (K v)) - v = _
  rw [← squaredRegularization_inverse_commute K hs ht]
  have he := (squaredRegularization_invertible K hs ht).self_apply_inverse v
  change K (K ((squaredRegularization K t).inverse v)) +
    t • (squaredRegularization K t).inverse v = v at he
  have hh := eq_sub_of_add_eq he
  rw [hh]
  simp [neg_smul]

lemma tikhonovResponse_bias_bound [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (v : E) :
    ‖tikhonovResponse K t (K v) - v‖ ≤ ‖v‖ := by
  rw [tikhonovResponse_bias_identity K hs ht, norm_smul, norm_neg, Real.norm_of_nonneg ht.le]
  exact squaredRegularization_inverse_bound K hs ht v

lemma tikhonovResponse_bias_residual [FiniteDimensional ℝ E] (K : E →L[ℝ] E)
    (hs : ∀ u v, ⟪K u, v⟫ = ⟪u, K v⟫) {t : ℝ} (ht : 0 < t) (v : E) :
    4 * ‖K (tikhonovResponse K t (K v) - v)‖ ^ 2 ≤ t * ‖v‖ ^ 2 := by
  rw [tikhonovResponse_bias_identity K hs ht, map_smul, norm_smul, norm_neg,
    Real.norm_of_nonneg ht.le]
  have hh := mul_le_mul_of_nonneg_left (tikhonovResponse_bound K hs ht v) ht.le
  change t * (4 * t * ‖K ((squaredRegularization K t).inverse v)‖ ^ 2) ≤ _ at hh
  nlinarith

lemma primal_component_energy (H : E →L[ℝ] E) {L : ℝ}
    (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (a b : E)
    (hab : ⟪a, b⟫ = 0) (hbound : ‖H a‖ ≤ L * ‖a‖) (hdual : ⟪H b, b⟫ ≤ 0) :
    L * ‖a‖ ^ 2 ≤ ‖H (a + b) + (2 * L) • a‖ * ‖a + b‖ := by
  have he : ‖a - b‖ = ‖a + b‖ := by
    have h₁ := norm_sub_sq_real a b
    have h₂ := norm_add_sq_real a b
    rw [hab] at h₁ h₂
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]
  have hi := real_inner_le_norm (H (a + b) + (2 * L) • a) (a - b)
  rw [he] at hi
  simp only [map_add, inner_add_left, inner_sub_right, real_inner_smul_left,
    hab, real_inner_self_eq_norm_sq] at hi
  have hc : ⟪H b, a⟫ = ⟪H a, b⟫ := (hs b a).trans (real_inner_comm (H a) b)
  rw [hc] at hi
  have hlo := (abs_le.mp (abs_real_inner_le_norm (H a) a)).1
  have hn := mul_le_mul_of_nonneg_right hbound (norm_nonneg a)
  simp only [map_add]
  nlinarith

lemma inverse_quadratic_lower (Q R : E →L[ℝ] E) {b : ℝ} (hb : 0 < b)
    (hs : ∀ u v, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hpos : ∀ u, 0 ≤ ⟪Q u, u⟫) (hupper : ∀ u, ⟪Q u, u⟫ ≤ b * ‖u‖ ^ 2)
    (hQR : ∀ u, Q (R u) = u) (v : E) : b⁻¹ * ‖v‖ ^ 2 ≤ ⟪R v, v⟫ := by
  have hp := hpos (R v - b⁻¹ • v)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_smul_right, hQR] at hp
  have hc : ⟪Q v, R v⟫ = ‖v‖ ^ 2 := by rw [hs, hQR, real_inner_self_eq_norm_sq]
  rw [hc, real_inner_self_eq_norm_sq, real_inner_comm (R v) v] at hp
  have hu : b⁻¹ ^ 2 * ⟪Q v, v⟫ ≤ b⁻¹ * ‖v‖ ^ 2 := by
    calc
      b⁻¹ ^ 2 * ⟪Q v, v⟫ ≤ b⁻¹ ^ 2 * (b * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hupper v) (sq_nonneg _)
      _ = b⁻¹ * ‖v‖ ^ 2 := by field_simp
  nlinarith

lemma primal_component_inner_energy (H : E →L[ℝ] E) {L : ℝ}
    (hs : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (a b : E)
    (hab : ⟪a, b⟫ = 0) (hbound : ‖H a‖ ≤ L * ‖a‖) (hdual : ⟪H b, b⟫ ≤ 0) :
    L * ‖a‖ ^ 2 ≤ ⟪H (a + b) + (2 * L) • a, a - b⟫ := by
  simp only [map_add, inner_add_left, inner_sub_right, real_inner_smul_left,
    hab, real_inner_self_eq_norm_sq]
  have hc : ⟪H b, a⟫ = ⟪H a, b⟫ := (hs b a).trans (real_inner_comm (H a) b)
  rw [hc]
  have hlo := (abs_le.mp (abs_real_inner_le_norm (H a) a)).1
  have hn := mul_le_mul_of_nonneg_right hbound (norm_nonneg a)
  nlinarith

lemma inverse_difference_apply (A B : E →L[ℝ] E)
    (hA : A.IsInvertible) (hB : B.IsInvertible) (v : E) :
    A.inverse v - B.inverse v = A.inverse ((B - A) (B.inverse v)) := by
  rw [sub_apply, map_sub, hB.self_apply_inverse, hA.inverse_apply_self]

lemma inverse_difference_bound (A B : E →L[ℝ] E)
    (hA : A.IsInvertible) (hB : B.IsInvertible) {a b : ℝ}
    (ha : 0 ≤ a)
    (hAb : ∀ v, ‖A.inverse v‖ ≤ a * ‖v‖)
    (hBb : ∀ v, ‖B.inverse v‖ ≤ b * ‖v‖) (v : E) :
    ‖A.inverse v - B.inverse v‖ ≤ a * ‖B - A‖ * b * ‖v‖ := by
  rw [inverse_difference_apply A B hA hB]
  calc
    _ ≤ a * ‖(B - A) (B.inverse v)‖ := hAb _
    _ ≤ a * (‖B - A‖ * ‖B.inverse v‖) :=
      mul_le_mul_of_nonneg_left ((B - A).le_opNorm _) ha
    _ ≤ a * (‖B - A‖ * (b * ‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hBb v) (norm_nonneg _)) ha
    _ = _ := by ring

lemma squaredRegularization_difference_bound (A B : E →L[ℝ] E) (t : ℝ) :
    ‖squaredRegularization B t - squaredRegularization A t‖ ≤
      (‖A‖ + ‖B‖) * ‖B - A‖ := by
  have he : squaredRegularization B t - squaredRegularization A t =
      B.comp (B - A) + (B - A).comp A := by
    ext v
    simp only [squaredRegularization, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
      map_sub, smul_apply, ContinuousLinearMap.id_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖B.comp (B - A)‖ + ‖(B - A).comp A‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖B - A‖ + ‖B - A‖ * ‖A‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ = _ := by ring

lemma tikhonovResponse_difference_bound [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) {t : ℝ} (ht : 0 < t)
    (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hB : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (v : E) :
    ‖tikhonovResponse A t v - tikhonovResponse B t v‖ ≤
      (t⁻¹ + ‖A‖ * t⁻¹ * (‖A‖ + ‖B‖) * t⁻¹) * ‖B - A‖ * ‖v‖ := by
  let IA := (squaredRegularization A t).inverse
  let IB := (squaredRegularization B t).inverse
  have hab : ∀ u, ‖IA u‖ ≤ t⁻¹ * ‖u‖ := by
    intro u
    have hh := squaredRegularization_inverse_bound A hA ht u
    exact (le_inv_mul_iff₀ ht).mpr hh
  have hbb : ∀ u, ‖IB u‖ ≤ t⁻¹ * ‖u‖ := by
    intro u
    have hh := squaredRegularization_inverse_bound B hB ht u
    exact (le_inv_mul_iff₀ ht).mpr hh
  have hd := inverse_difference_bound (squaredRegularization A t) (squaredRegularization B t)
    (squaredRegularization_invertible A hA ht) (squaredRegularization_invertible B hB ht)
    (inv_nonneg.mpr ht.le) hab hbb v
  have hs := squaredRegularization_difference_bound A B t
  have hd' : ‖IA v - IB v‖ ≤
      t⁻¹ * ((‖A‖ + ‖B‖) * ‖B - A‖) * t⁻¹ * ‖v‖ := by
    apply hd.trans
    gcongr
  have he : tikhonovResponse A t v - tikhonovResponse B t v =
      A (IA v - IB v) + (A - B) (IB v) := by
    simp only [tikhonovResponse, ContinuousLinearMap.comp_apply, map_sub, sub_apply, IA, IB]
    abel
  rw [he]
  calc
    _ ≤ ‖A (IA v - IB v)‖ + ‖(A - B) (IB v)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖IA v - IB v‖ + ‖A - B‖ * ‖IB v‖ :=
      add_le_add (A.le_opNorm _) ((A - B).le_opNorm _)
    _ ≤ ‖A‖ * (t⁻¹ * ((‖A‖ + ‖B‖) * ‖B - A‖) * t⁻¹ * ‖v‖) +
        ‖A - B‖ * (t⁻¹ * ‖v‖) := by gcongr; exact hbb v
    _ = _ := by rw [norm_sub_rev A B]; ring

lemma inverse_curvature_transfer (Q R : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hs : ∀ u v, ⟪Q u, v⟫ = ⟪u, Q v⟫) (hpos : ∀ u, 0 ≤ ⟪Q u, u⟫)
    (hQR : ∀ u, Q (R u) = u)
    (hcurv : ∀ u, -η * ‖u‖ ^ 2 ≤ (2 * L) * (‖u‖ ^ 2 - ⟪Q u, u⟫)) (v : E) :
    -η * ‖v‖ ^ 2 ≤ (2 * L) * (⟪R v, v⟫ - ‖v‖ ^ 2) := by
  let b := 1 + η / (2 * L)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbe : (2 * L) * b = 2 * L + η := by dsimp [b]; field_simp
  have hu : ∀ u, ⟪Q u, u⟫ ≤ b * ‖u‖ ^ 2 := by
    intro u
    have hh := hcurv u
    have he := congrArg (fun a : ℝ => a * ‖u‖ ^ 2) hbe
    nlinarith
  have hi := inverse_quadratic_lower Q R hb hs hpos hu hQR v
  have hinv : b * b⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
  have hcoeff : -η ≤ (2 * L) * (b⁻¹ - 1) := by
    apply (mul_le_mul_iff_right₀ hb).mp
    have he := congrArg (fun a : ℝ => a * b⁻¹) hbe
    have hb1 : 1 ≤ b := by
      dsimp [b]
      linarith [div_nonneg hη (show 0 ≤ 2 * L by positivity)]
    have hηb := mul_le_mul_of_nonneg_left hb1 hη
    have heq := congrArg (fun a : ℝ => (2 * L) * a) hinv
    nlinarith
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * L by positivity)
  have hc := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖v‖)
  nlinarith

end OracleTemplate.PLMinimax
