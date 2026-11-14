import LongTails.Proofs.LocalizedMonotoneSimulation
import LongTails.Proofs.SmoothConvexFiniteAveraging

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical
open scoped BigOperators

namespace LongTails.Proofs.LocalizedMonotoneAveraging

open LocalizedMonotoneSimulation SmoothConvexFiniteHiding
open FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure FiniteSumNondualLowerAveraging

lemma bad_sum_bound {d n k : ℕ} {S : Type*} (a b c γ B D : ℝ)
    (hB : 0 ≤ B) (ha : 0 < a) (hk : k ≤ n) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → Reply d → S) (initial : S) :
    D * (∑ w : CoordinateWords d n, if coordinateBad (k := k) a b c γ B query output update initial
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (k + 1 : ℕ) * (n + 1 : ℕ) * (B ^ 2 / a ^ 2) * Fintype.card (CoordinateWords d n) := by
  classical
  let bad := fun π : Fin (n + 1) ↪ Fin d => coordinateBad (k := k) a b c γ B query output update initial π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ t : Fin (k + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet B a
          (observation a b c γ query output update initial t π)) (w.val.drop t.val) := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using ht⟩
    · rintro ⟨t, π, hπ, ht⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro j
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) j
      exact ⟨t, by simpa only [hp, ← coordinateEmbedding_labels w] using ht⟩
  let P := fun w : List (Fin d) => ∃ t : Fin (k + 1), ∃ π : Fin (n + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet B a
      (observation a b c γ query output update initial t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) B a D
    hB ha hD hDs (fun t : Fin (k + 1) => t.val)
    (fun t => by have := t.isLt; omega) (observation a b c γ query output update initial)
    (observation_prefix a b c γ query output update initial)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe, pow_two, mul_assoc] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma execution_average_residual {d n k : ℕ} {S : Type*} (a b c γ B η D : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (hk : k ≤ n)
    (hB : 3 * b / 2 ≤ B) (hbB : b ≤ B)
    (hcoerce : Real.sqrt (n + 1) * c + (2 * (n + 1) + 1) * η ≤ b)
    (hgap : Real.sqrt (n + 1) * η ≤ c - a - n * (3 * a / 2))
    (hD : 0 < D) (hDs : D + (n + 1 : ℕ) ≤ d)
    (hsize : 2 * (k + 1 : ℕ) * (n + 1 : ℕ) * (B ^ 2 / a ^ 2) ≤ D)
    (query output : S → Space d) (update : S → Reply d → S) (initial : S) :
    (γ * η) * Fintype.card (CoordinateWords d n) ≤
      2 * ∑ w : CoordinateWords d n, ‖LocalizedMonotoneInstance.field a b c γ (coordinateEmbedding w)
        (output ((fun s => update s
          (LocalizedMonotoneInstance.field a b c γ (coordinateEmbedding w) (query s),
           LocalizedMonotoneInstance.jacobian a b γ (coordinateEmbedding w) (query s)))^[k] initial))‖ := by
  classical
  let bad := fun w : CoordinateWords d n =>
    coordinateBad (k := k) a b c γ B query output update initial (coordinateEmbedding w)
  have hB0 : 0 ≤ B := hb.le.trans hbB
  have hb' := bad_sum_bound a b c γ B D hB0 ha hk hD.le hDs query output update initial
  have hhalf : 2 * (∑ w, if bad w then (1 : ℝ) else 0) ≤ Fintype.card (CoordinateWords d n) := by
    have hs := mul_le_mul_of_nonneg_right hsize
      (Nat.cast_nonneg (Fintype.card (CoordinateWords d n)) : (0 : ℝ) ≤ _)
    nlinarith
  exact SmoothConvexFiniteAveraging.finite_good_average bad _ _ (mul_nonneg hγ hη)
    (fun _ => norm_nonneg _)
    (fun w hw => good_execution_residual a b c γ B η ha hb hc hγ hk hB hbB hcoerce hgap
      query output update initial (coordinateEmbedding w) hw) hhalf

end LongTails.Proofs.LocalizedMonotoneAveraging
