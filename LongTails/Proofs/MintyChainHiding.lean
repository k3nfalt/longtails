import LongTails.Proofs.MintyChainGeometry
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.MintyChainHiding

open MintyChainGeometry SmoothConvexFiniteHiding
open FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure FiniteSumNondualLowerAveraging

variable {d k : ℕ} {S : Type*}

noncomputable def simulatedState (κ r B : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → EuclideanSpace ℝ (Fin d) → S)
    (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let s := simulatedState κ r B π query update initial t
    update s (partialField κ r B π t (query s))

lemma simulatedState_prefix (κ r B : ℝ) (π ρ : Fin (k + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → EuclideanSpace ℝ (Fin d) → S)
    (initial : S) (t : ℕ) (h : ∀ j : Fin (k + 1), j.val < t → π j = ρ j) :
    simulatedState κ r B π query update initial t =
      simulatedState κ r B ρ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => h j (by omega))
    simp only [simulatedState, he]
    rw [partialField_prefix κ r B π ρ t (fun j hj => h j (by omega))]

lemma simulatedState_coupling (κ r B : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d)) (update : S → EuclideanSpace ℝ (Fin d) → S)
    (initial : S) (T : ℕ)
    (hgood : ∀ t < T, ∀ j : Fin (k + 1), t ≤ j.val →
      |ball B (query (simulatedState κ r B π query update initial t)) (π j)| ≤ r / 4) :
    simulatedState κ r B π query update initial T =
      (fun s => update s (field κ r B π (query s)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (fun t ht => hgood t (by omega))
    rw [simulatedState, ← field_eq_partial κ r B hr π T _ (hgood T (by omega)), he,
      Function.iterate_succ_apply']

noncomputable def observation (κ r B : ℝ) (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  let s := simulatedState κ r B π query update initial t.val
  ball B (if t.val < k then query s else output s)

lemma observation_prefix (κ r B : ℝ) (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (t : Fin (k + 1)) (π ρ : Fin (k + 1) ↪ Fin d)
    (h : ∀ j : Fin (k + 1), j.val < t.val → π j = ρ j) :
    observation κ r B query output update initial t π =
      observation κ r B query output update initial t ρ := by
  unfold observation
  rw [simulatedState_prefix κ r B π ρ query update initial t.val h]

def coordinateBad (κ r B : ℝ) (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (k + 1), 0 < hits
    (largeSet B (r / 4) (observation κ r B query output update initial t π))
    ((List.ofFn π).drop t.val)

lemma good_observation_small (κ r B : ℝ) (hB : 0 ≤ B)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad κ r B query output update initial π)
    (t j : Fin (k + 1)) (hj : t.val ≤ j.val) :
    |observation κ r B query output update initial t π (π j)| ≤ r / 4 := by
  apply not_largeSet_small _ _ _ (ball_norm_le B hB _)
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ j hj h⟩

lemma good_execution_lower (κ r B : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hB : 0 < B)
    (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad κ r B query output update initial π) :
    3 * κ ^ 2 * r ^ 2 / 16 ≤ ‖field κ r B π
      (output ((fun s => update s (field κ r B π (query s)))^[k] initial))‖ ^ 2 := by
  have he := simulatedState_coupling κ r B hr π query update initial k
    (fun t ht j hj => by
      have h := good_observation_small κ r B hB.le query output update initial π hgood
        ⟨t, by omega⟩ j hj
      simpa only [observation, ht, ↓reduceIte] using h)
  rw [← he]
  apply field_lower κ r B hκ hr hB π hrad
  refine ⟨Fin.last k, ?_⟩
  have h := good_observation_small κ r B hB.le query output update initial π hgood
    (Fin.last k) (Fin.last k) le_rfl
  simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
  have h2 := le_abs_self (ball B (output (simulatedState κ r B π query update initial k))
    (π (Fin.last k)))
  linarith

lemma bad_sum_bound (κ r B D : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hD : 0 ≤ D)
    (hDs : D + (k + 1 : ℕ) ≤ d)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) :
    D * (∑ w : CoordinateWords d k, if coordinateBad κ r B query output update initial
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (k + 1 : ℕ) ^ 2 * (B ^ 2 / (r / 4) ^ 2) * Fintype.card (CoordinateWords d k) := by
  let bad := fun π : Fin (k + 1) ↪ Fin d => coordinateBad κ r B query output update initial π
  have he (w : CoordinateWords d k) : bad (coordinateEmbedding w) ↔
      ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet B (r / 4)
          (observation κ r B query output update initial t π)) (w.val.drop t.val) := by
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
    List.ofFn π = w ∧ 0 < hits (largeSet B (r / 4)
      (observation κ r B query output update initial t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) B (r / 4) D
    hB (by positivity) hD hDs (fun t : Fin (k + 1) => t.val)
    (fun t => t.isLt.le) (observation κ r B query output update initial)
    (observation_prefix κ r B query output update initial)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe, pow_two, mul_assoc] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma execution_average (κ r B D ε : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hB : 0 < B)
    (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2) (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (hsize : 4 * ((k + 1 : ℕ) ^ 2 * (B ^ 2 / (r / 4) ^ 2)) ≤ D)
    (hε : 0 ≤ ε) (hgap : 4 * ε ^ 2 ≤ 3 * κ ^ 2 * r ^ 2 / 16)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) :
    3 * ε * Fintype.card (CoordinateWords d k) ≤
      2 * ∑ w : CoordinateWords d k, ‖field κ r B (coordinateEmbedding w)
        (output ((fun s => update s (field κ r B (coordinateEmbedding w) (query s)))^[k]
          initial))‖ := by
  let bad := fun w : CoordinateWords d k =>
    coordinateBad κ r B query output update initial (coordinateEmbedding w)
  let nb : ℝ := ∑ w, if bad w then (1 : ℝ) else 0
  have hb := bad_sum_bound κ r B D hB.le hr hD.le hDs query output update initial
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords d k) := Nat.cast_nonneg _
  have hnb : 4 * nb ≤ Fintype.card (CoordinateWords d k) := by
    have h1 : D * (4 * nb) ≤ D * Fintype.card (CoordinateWords d k) := by
      have h2 := mul_le_mul_of_nonneg_right hsize hcard
      change D * nb ≤ _ at hb
      nlinarith
    exact le_of_mul_le_mul_left h1 hD
  have hloss (w : CoordinateWords d k) : 2 * ε * (1 - if bad w then (1 : ℝ) else 0) ≤
      ‖field κ r B (coordinateEmbedding w)
        (output ((fun s => update s (field κ r B (coordinateEmbedding w) (query s)))^[k]
          initial))‖ := by
    by_cases hw : bad w
    · simp only [hw, ↓reduceIte, sub_self, mul_zero]
      exact norm_nonneg _
    · simp only [hw, ↓reduceIte, sub_zero, mul_one]
      have h := good_execution_lower κ r B hκ hr hB hrad query output update initial
        (coordinateEmbedding w) hw
      have h2 : (2 * ε) ^ 2 ≤ ‖field κ r B (coordinateEmbedding w)
          (output ((fun s => update s (field κ r B (coordinateEmbedding w) (query s)))^[k]
            initial))‖ ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords d k))) =>
    hloss w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  change 2 * ε * (Fintype.card (CoordinateWords d k) - nb) ≤ _ at hs
  nlinarith [mul_le_mul_of_nonneg_left hnb hε]

lemma exists_failure {Ω : Type*} [MeasurableSpace Ω] (κ r B D ε : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hB : 0 < B)
    (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2) (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (hsize : 4 * ((k + 1 : ℕ) ^ 2 * (B ^ 2 / (r / 4) ^ 2)) ≤ D)
    (hε : 0 < ε) (hgap : 4 * ε ^ 2 ≤ 3 * κ ^ 2 * r ^ 2 / 16)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (k + 1) ↪ Fin d,
      let loss := fun ω => ‖field κ r B π
        (output ((fun s => update s (field κ r B π (query s)))^[k] (initial ω)))‖
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  by_contra h
  push Not at h
  let loss := fun (w : CoordinateWords d k) (ω : Ω) =>
    ‖field κ r B (coordinateEmbedding w)
      (output ((fun s => update s (field κ r B (coordinateEmbedding w) (query s)))^[k]
        (initial ω)))‖
  have hi (w : CoordinateWords d k) : Integrable (loss w) (P : Measure Ω) :=
    (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d k) : (∫ ω, loss w ω ∂(P : Measure Ω)) ≤ ε :=
    (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, loss w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hp := integral_mono (integrable_const
    (3 * ε * Fintype.card (CoordinateWords d k)))
    (hs.const_mul 2) (fun ω => execution_average κ r B D ε hκ hr hB hrad hD hDs hsize
      hε.le hgap query output update (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hp
  have hb : (∑ w : CoordinateWords d k, ∫ ω, loss w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d k) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d k, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : k + 1 ≤ d := by
    have hh : ((k + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d k) := by
    exact_mod_cast FiniteSumNondualLowerBound.coordinateWords_card_pos d k hd
  change _ ≤ 2 * ∑ w : CoordinateWords d k, ∫ ω, loss w ω ∂(P : Measure Ω) at hp
  nlinarith [mul_pos hε hc]

end LongTails.Proofs.MintyChainHiding
