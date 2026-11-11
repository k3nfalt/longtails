import LongTails.Proofs.SmoothConvexFiniteSimulation
import LongTails.Proofs.SmoothConvexFiniteHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical
open scoped BigOperators

namespace LongTails.Proofs.SmoothConvexFiniteAveraging

open SmoothConvexFiniteSimulation SmoothConvexFiniteHiding SmoothConvexFiniteWall
open FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure FiniteSumNondualLowerAveraging

noncomputable def observation {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  let s := simulatedState L R δ a π query update initial t.val
  if t.val < k then query s else output s

lemma observation_prefix {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (t : Fin (k + 1)) (π ρ : Fin (k + 1) ↪ Fin d)
    (h : ∀ j : Fin (k + 1), j.val < t.val → π j = ρ j) :
    observation L R δ a query output update initial t π =
      observation L R δ a query output update initial t ρ := by
  unfold observation
  rw [simulatedState_prefix L R δ a π ρ query update initial t.val h]

def coordinateBad {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (k + 1), 0 < hits
    (largeSet (3 * R) (δ / 4) (observation L R δ a query output update initial t π))
    ((List.ofFn π).drop t.val)

lemma good_observation_small {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) (hgood : ¬ coordinateBad L R δ a query output update initial π)
    (t j : Fin (k + 1)) (hj : t.val ≤ j.val)
    (ht : ‖observation L R δ a query output update initial t π‖ ≤ 3 * R) :
    |observation L R δ a query output update initial t π (π j)| ≤ δ / 4 := by
  apply not_largeSet_small _ _ _ ht
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ j hj h⟩

lemma objective_far_gap {d k : ℕ} (L R δ a : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (hx : 3 * R ≤ ‖x‖) :
    L * a ^ 2 ≤ 8192 * ((k : ℝ) + 1) * objective L R δ a π x := by
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * R) hx 2
  have ha' : a ^ 2 ≤ R ^ 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg a)]
  have hw : a ^ 2 ≤ 16 * wall R x := by dsimp [wall]; nlinarith [sq_nonneg R]
  have hf : L / 512 * wall R x ≤ objective L R δ a π x :=
    mul_le_mul_of_nonneg_left ((le_max_right _ _).trans
      (SmoothConvexFiniteGeometry.smoothMax_ge _ _ _ (sq_pos_of_pos hR))) (by positivity)
  have hLw := mul_le_mul_of_nonneg_left hw hL
  have hn := objective_nonneg L R δ a hL hR π x
  nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hn]

lemma good_execution_gap {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hrad : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) (hgood : ¬ coordinateBad L R δ a query output update initial π) :
    L * a ^ 2 / (8192 * ((k : ℝ) + 1)) ≤
      objective L R δ a π (output ((fun s => update s (field L R δ a π (query s)))^[k] initial)) := by
  have he := simulatedState_coupling L R δ a hR hδ π hrad query update initial k
    (fun t ht hx j hj => by
      have h := good_observation_small L R δ a query output update initial π hgood
        ⟨t, by omega⟩ j hj (by simpa only [observation, ht, ↓reduceIte] using hx.le)
      simpa only [observation, ht, ↓reduceIte] using h)
  rw [← he]
  apply (div_le_iff₀ (by positivity : 0 < 8192 * ((k : ℝ) + 1))).mpr
  rw [mul_comm (objective L R δ a π _) (8192 * ((k : ℝ) + 1))]
  by_cases hx : ‖output (simulatedState L R δ a π query update initial k)‖ ≤ 3 * R
  · apply objective_gap L R δ a hL hR hδ ha π _ hscale
    have h := good_observation_small L R δ a query output update initial π hgood
      (Fin.last k) (Fin.last k) le_rfl (by simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using hx)
    simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using h
  · exact objective_far_gap L R δ a hL hR π hrad _ (le_of_not_ge hx)

lemma bad_sum_bound {d k : ℕ} {S : Type*} (L R δ a D : ℝ)
    (hR : 0 ≤ R) (hδ : 0 < δ) (hD : 0 ≤ D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) :
    D * (∑ w : CoordinateWords d k, if coordinateBad L R δ a query output update initial
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (k + 1 : ℕ) ^ 2 * ((3 * R) ^ 2 / (δ / 4) ^ 2) * Fintype.card (CoordinateWords d k) := by
  classical
  let bad := fun π : Fin (k + 1) ↪ Fin d => coordinateBad L R δ a query output update initial π
  have he (w : CoordinateWords d k) : bad (coordinateEmbedding w) ↔
      ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (3 * R) (δ / 4)
          (observation L R δ a query output update initial t π)) (w.val.drop t.val) := by
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
  let P := fun w : List (Fin d) => ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (3 * R) (δ / 4)
      (observation L R δ a query output update initial t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) (3 * R) (δ / 4) D
    (by positivity) (by positivity) hD hDs (fun t : Fin (k + 1) => t.val)
    (fun t => t.isLt.le) (observation L R δ a query output update initial)
    (observation_prefix L R δ a query output update initial)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe, pow_two, mul_assoc] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma finite_good_average {W : Type*} [Fintype W] (bad : W → Prop) [DecidablePred bad]
    (loss : W → ℝ) (g : ℝ) (hg : 0 ≤ g) (hn : ∀ w, 0 ≤ loss w)
    (hl : ∀ w, ¬ bad w → g ≤ loss w)
    (hb : 2 * (∑ w, if bad w then (1 : ℝ) else 0) ≤ Fintype.card W) :
    g * Fintype.card W ≤ 2 * ∑ w, loss w := by
  have h (w : W) : g * (1 - if bad w then (1 : ℝ) else 0) ≤ loss w := by
    by_cases hw : bad w
    · simpa only [hw, ↓reduceIte, sub_self, mul_zero] using hn w
    · simpa only [hw, ↓reduceIte, sub_zero, mul_one] using hl w hw
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => h w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  nlinarith [mul_le_mul_of_nonneg_left hb hg]

lemma execution_average_gap {d k : ℕ} {S : Type*} (L R δ a D : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hrad : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (hsize : 2 * (k + 1 : ℕ) ^ 2 * ((3 * R) ^ 2 / (δ / 4) ^ 2) ≤ D)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) :
    (L * a ^ 2 / (8192 * ((k : ℝ) + 1))) * Fintype.card (CoordinateWords d k) ≤
      2 * ∑ w : CoordinateWords d k, objective L R δ a (coordinateEmbedding w)
        (output ((fun s => update s (field L R δ a (coordinateEmbedding w) (query s)))^[k] initial)) := by
  classical
  let bad := fun w : CoordinateWords d k =>
    coordinateBad L R δ a query output update initial (coordinateEmbedding w)
  have hb := bad_sum_bound L R δ a D hR.le hδ hD.le hDs query output update initial
  have hb' : 2 * (∑ w, if bad w then (1 : ℝ) else 0) ≤ Fintype.card (CoordinateWords d k) := by
    have hs := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg (Fintype.card (CoordinateWords d k)) :
      (0 : ℝ) ≤ Fintype.card (CoordinateWords d k))
    nlinarith
  exact finite_good_average bad _ _ (by positivity)
    (fun w => objective_nonneg L R δ a hL hR (coordinateEmbedding w) _)
    (fun w hw => good_execution_gap L R δ a hL hR hδ.le ha hrad hscale
      query output update initial (coordinateEmbedding w) hw) hb'

end LongTails.Proofs.SmoothConvexFiniteAveraging
