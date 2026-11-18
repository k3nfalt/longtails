import LongTails.Proofs.RelativeHessianExposure

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RelativeHessianAveraging

open scoped BigOperators
open Classical RelativeHessianSimulation RelativeHessianExposure
open FiniteSumNondualLowerExposure FiniteSumNondualLowerHiding FiniteSumNondualLowerAveraging

variable {d m : ℕ} {S : Type*}

lemma embedding_indicator_sum {k : ℕ} (P : (Fin (k + 1) ↪ Fin d) → Prop) [DecidablePred P] :
    (∑ w : CoordinateWords d k, if P (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter
        (fun w => ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w ∧ P π)).card : ℝ) := by
  classical
  have he (w : CoordinateWords d k) : P (coordinateEmbedding w) ↔
      ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧ P π := by
    constructor
    · intro h; exact ⟨coordinateEmbedding w, coordinateEmbedding_labels w, h⟩
    · rintro ⟨π, hπ, h⟩
      have he : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro j
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) j
      simpa [he] using h
  calc
    _ = ∑ w : CoordinateWords d k, if ∃ π : Fin (k + 1) ↪ Fin d,
        List.ofFn π = w.val ∧ P π then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : P (coordinateEmbedding w)
      · simp only [hw, (he w).mp hw, ↓reduceIte]
      · have hn := mt (he w).mpr hw
        simp only [hw, hn, ↓reduceIte]
    _ = _ := subtype_indicator_sum (distinctWords (k + 1) (Finset.univ : Finset (Fin d)))
      (fun w => ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w ∧ P π)

lemma bad_fraction (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (hT : T < m) (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D) :
    4 * (∑ w : CoordinateWords d m,
      if bad query output update initial T (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords d m) := by
  have h := bad_count query output update initial T hT D hD.le hd
  have he : ((distinctWords (m + 1) (Finset.univ : Finset (Fin d))).filter
      (fun w => ∃ j : Fin (T + 1), ∃ π : Fin (m + 1) ↪ Fin d, List.ofFn π = w ∧
        0 < hits (SmoothConvexFiniteHiding.largeSet (2 * RelativeHessianLocalized.radius m) (1 / 20)
          (observe query output update initial T j π)) (w.drop (j.val + 1)))) =
      ((distinctWords (m + 1) (Finset.univ : Finset (Fin d))).filter
        (fun w => ∃ π : Fin (m + 1) ↪ Fin d, List.ofFn π = w ∧ bad query output update initial T π)) := by
    apply Finset.filter_congr
    intro w _
    constructor
    · rintro ⟨j, π, hπ, hj⟩
      exact ⟨π, hπ, j, by simpa only [hπ] using hj⟩
    · rintro ⟨π, hπ, j, hj⟩
      exact ⟨j, π, hπ, by simpa only [hπ] using hj⟩
  rw [he, ← embedding_indicator_sum (bad query output update initial T)] at h
  have ht : 0 ≤ ((distinctWords (m + 1) (Finset.univ : Finset (Fin d))).card : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hsize ht
  simp only [CoordinateWords, Fintype.card_coe]
  apply (mul_le_mul_iff_left₀ hD).mp
  nlinarith

lemma gradient_average (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) (hT : T < m) (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D) :
    (Fintype.card (CoordinateWords d m) : ℝ) ≤
      2 * ∑ w : CoordinateWords d m, ‖gradient (RelativeHessianLocalized.value (axes (coordinateEmbedding w)))
        (output (actual (coordinateEmbedding w) query update initial T))‖ := by
  have hb := bad_fraction query output update initial T hT D hD hd hsize
  have hp (w : CoordinateWords d m) :
      (7 / 10 : ℝ) * (1 - if bad query output update initial T (coordinateEmbedding w) then 1 else 0) ≤
      ‖gradient (RelativeHessianLocalized.value (axes (coordinateEmbedding w)))
        (output (actual (coordinateEmbedding w) query update initial T))‖ := by
    by_cases hw : bad query output update initial T (coordinateEmbedding w)
    · simpa only [hw, ite_true, sub_self, mul_zero] using norm_nonneg
        (gradient (RelativeHessianLocalized.value (axes (coordinateEmbedding w)))
          (output (actual (coordinateEmbedding w) query update initial T)))
    · simpa only [hw, ite_false, sub_zero, mul_one] using
        good_gradient query output update initial T hT (coordinateEmbedding w) hw
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords d m))) => hp w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hc : (0 : ℝ) ≤ Fintype.card (CoordinateWords d m) := by positivity
  nlinarith

end LongTails.Proofs.RelativeHessianAveraging
