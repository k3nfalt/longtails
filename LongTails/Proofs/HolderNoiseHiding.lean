import LongTails.Proofs.FrontierChainSimulation
import LongTails.Proofs.QuasarHardHiding

namespace LongTails.Proofs.HolderNoiseHiding

open FrontierChainSimulation FrontierChainOracle FrontierChainWall SoftRadialProjection
open Classical

variable {d k : ℕ} {S : Type*}

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def exposure (β : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => exposure β t + if β t then 1 else 0

lemma exposure_mono (β : ℕ → Bool) : Monotone (exposure β) := by
  apply monotone_nat_of_le_succ
  intro t
  simp only [exposure]
  omega

structure QueryData (S : Type*) (d : ℕ) where
  query : S → Point d × Point d
  output : S → Point d
  update : S → Point d × Point d → S
  normalize : Point d → Point d
  response : Point d → Point d
  init : S

noncomputable def partialPair (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (r : ℕ) (s : S) (b : Bool) : Point d × Point d :=
  (H.response (partialOracle π p r (H.normalize (H.query s).1) b),
    H.response (partialOracle π p r (H.normalize (H.query s).2) b))

noncomputable def actualPair (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (s : S) (b : Bool) : Point d × Point d :=
  (H.response (canonicalOracle π p (H.normalize (H.query s).1) b),
    H.response (canonicalOracle π p (H.normalize (H.query s).2) b))

noncomputable def simState (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) : ℕ → S
  | 0 => H.init
  | t + 1 => let s := simState H π p β t
    H.update s (partialPair H π p (exposure β t) s (β t))

noncomputable def actualState (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) : ℕ → S
  | 0 => H.init
  | t + 1 => let s := actualState H π p β t
    H.update s (actualPair H π p s (β t))

lemma simState_prefix (H : QueryData S d) (π π' : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (t : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val < exposure β t → π j = π' j) :
    simState H π p β t = simState H π' p β t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => hπ j (hj.trans_le (exposure_mono β (Nat.le_succ t))))
    simp only [simState, he]
    congr 1
    unfold partialPair
    cases hb : β t
    · have hp : ∀ j : Fin (k + 1), j.val < exposure β t → π j = π' j := by
        intro j hj
        apply hπ j
        simpa only [exposure, hb, Bool.false_eq_true, ite_false, add_zero] using hj
      rw [partialOracle_false_prefix π π' p _ _ hp, partialOracle_false_prefix π π' p _ _ hp]
    · have hp : ∀ j : Fin (k + 1), j.val ≤ exposure β t → π j = π' j := by
        intro j hj
        apply hπ j
        simpa only [exposure, hb, ite_true] using Nat.lt_succ_of_le hj
      rw [partialOracle_true_prefix π π' p _ _ hp, partialOracle_true_prefix π π' p _ _ hp]

noncomputable def observation (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (t : ℕ) (i : Fin 3) : Point d :=
  let s := simState H π p β t
  project (radius k) (H.normalize (if i = 0 then (H.query s).1 else if i = 1 then (H.query s).2 else H.output s))

lemma observation_prefix (H : QueryData S d) (π π' : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (t : ℕ) (i : Fin 3)
    (hπ : ∀ j : Fin (k + 1), j.val < exposure β t → π j = π' j) :
    observation H π p β t i = observation H π' p β t i := by
  unfold observation
  rw [simState_prefix H π π' p β t hπ]

lemma observation_norm (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (t : ℕ) (i : Fin 3) :
    ‖observation H π p β t i‖ ≤ radius k := by
  exact norm_project_le (radius_pos k) _

lemma simState_coupling (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (N : ℕ)
    (hgood : ∀ t < N, ∀ i : Fin 3, ∀ j : Fin (k + 1), exposure β t ≤ j.val →
      |observation H π p β t i (π j)| ≤ 1 / 4) :
    simState H π p β N = actualState H π p β N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hgood t (by omega))
    simp only [simState, actualState, ← he]
    congr 1
    unfold partialPair actualPair
    have h0 := fun j hj => hgood N (by omega) 0 j hj
    have h1 := fun j hj => hgood N (by omega) 1 j hj
    simp only [observation, ite_true] at h0
    simp only [observation, show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true] at h1
    rw [partialOracle_eq π p _ _ _ h0, partialOracle_eq π p _ _ _ h1]

open SmoothConvexFiniteHiding FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure
open FiniteSumNondualLowerAveraging

noncomputable def isBad (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (N : ℕ) : Prop :=
  ∃ j : Fin (N + 1) × Fin 3, 0 < hits
    (largeSet (radius k) (1 / 4) (observation H π p β j.1.val j.2))
      ((List.ofFn π).drop (exposure β j.1.val))

lemma good_coordinate (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (N : ℕ) (hgood : ¬ isBad H π p β N)
    (t : ℕ) (ht : t ≤ N) (i : Fin 3) (j : Fin (k + 1)) (hj : exposure β t ≤ j.val) :
    |observation H π p β t i (π j)| ≤ 1 / 4 := by
  apply not_largeSet_small (radius k) (1 / 4) _ (observation_norm H π p β t i)
  intro hm
  apply hgood
  refine ⟨(⟨t, by omega⟩, i), ?_⟩
  exact hits_drop_positive π (exposure β t) _ j hj hm

lemma bad_count (H : QueryData S d) (p : ℝ) (β : ℕ → Bool) (N : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hDs : D + (k + 1 : ℕ) ≤ d) (hN : exposure β N ≤ k + 1) :
    D * (∑ w : CoordinateWords d k,
      if isBad H (coordinateEmbedding w) p β N then (1 : ℝ) else 0) ≤
      (3 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * (radius k ^ 2 / (1 / 4) ^ 2) *
        Fintype.card (CoordinateWords d k) := by
  have he (w : CoordinateWords d k) :
      isBad H (coordinateEmbedding w) p β N ↔
      ∃ j : Fin (N + 1) × Fin 3, ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (radius k) (1 / 4) (observation H π p β j.1.val j.2))
          (w.val.drop (exposure β j.1.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro i
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) i
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1) × Fin 3, ∃ π : Fin (k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (radius k) (1 / 4)
      (observation H π p β j.1.val j.2)) (w.drop (exposure β j.1.val))
  have hs : (∑ w : CoordinateWords d k,
      if isBad H (coordinateEmbedding w) p β N then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) (radius k) (1 / 4) D
    (radius_pos k).le (by norm_num) hD hDs
    (fun j : Fin (N + 1) × Fin 3 => exposure β j.1.val)
    (fun j => (exposure_mono β (by have := j.1.isLt; omega)).trans hN)
    (fun j π => observation H π p β j.1.val j.2)
    (fun j π ρ hπ => observation_prefix H π ρ p β j.1.val j.2 hπ)
  have hJ : (Fintype.card (Fin (N + 1) × Fin 3) : ℝ) = 3 * ((N : ℝ) + 1) := by
    simp [Fintype.card_prod]
    ring
  rw [hJ] at h
  simp only [CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1

lemma good_gradient (H : QueryData S d) (π : Fin (k + 1) ↪ Fin d)
    (p : ℝ) (β : ℕ → Bool) (N : ℕ) (hgood : ¬ isBad H π p β N)
    (hN : exposure β N ≤ k) :
    1 / 2 ≤ ‖wallField π (radius k) (1 / 5) (H.normalize (H.output (actualState H π p β N)))‖ := by
  have hc := simState_coupling H π p β N (fun t ht i j hj =>
    good_coordinate H π p β N hgood t (by omega) i j hj)
  have ho := good_coordinate H π p β N hgood N le_rfl 2 (Fin.last k) hN
  simp only [observation, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ite_false, hc] at ho
  exact canonical_gradient_lower π _ (by linarith)

lemma gradient_sum_lower (H : QueryData S d) (p : ℝ) (β : ℕ → Bool) (N : ℕ)
    (D : ℝ) (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d) (hN : exposure β N ≤ k)
    (hsize : 4 * ((3 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * (radius k ^ 2 / (1 / 4) ^ 2)) ≤ D) :
    (3 / 8 : ℝ) * Fintype.card (CoordinateWords d k) ≤
      ∑ w : CoordinateWords d k,
        ‖wallField (coordinateEmbedding w) (radius k) (1 / 5)
          (H.normalize (H.output (actualState H (coordinateEmbedding w) p β N)))‖ := by
  have hb := bad_count H p β N D hD.le hDs (by omega : exposure β N ≤ k + 1)
  have hb4 : 4 * (∑ w : CoordinateWords d k,
      if isBad H (coordinateEmbedding w) p β N then (1 : ℝ) else 0) ≤ Fintype.card (CoordinateWords d k) := by
    apply (mul_le_mul_iff_left₀ hD).mp
    have ht := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg (Fintype.card (CoordinateWords d k)))
    nlinarith
  have hp (w : CoordinateWords d k) :
      (1 / 2 : ℝ) * (1 - if isBad H (coordinateEmbedding w) p β N then 1 else 0) ≤
      ‖wallField (coordinateEmbedding w) (radius k) (1 / 5)
        (H.normalize (H.output (actualState H (coordinateEmbedding w) p β N)))‖ := by
    by_cases hw : isBad H (coordinateEmbedding w) p β N
    · simp only [hw, ite_true, sub_self, mul_zero]
      exact norm_nonneg _
    · simp only [hw, ite_false, sub_zero, mul_one]
      exact good_gradient H (coordinateEmbedding w) p β N hw hN
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords d k))) => hp w)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, mul_one] at hs
  linarith

lemma gradient_sum_exposure (H : QueryData S d) (p : ℝ) (β : ℕ → Bool) (N : ℕ)
    (D : ℝ) (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (hsize : 4 * ((3 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * (radius k ^ 2 / (1 / 4) ^ 2)) ≤ D) :
    (3 / 8 : ℝ) * Fintype.card (CoordinateWords d k) * (1 - (exposure β N : ℝ) / (k + 1)) ≤
      ∑ w : CoordinateWords d k,
        ‖wallField (coordinateEmbedding w) (radius k) (1 / 5)
          (H.normalize (H.output (actualState H (coordinateEmbedding w) p β N)))‖ := by
  by_cases hN : exposure β N ≤ k
  · have h := gradient_sum_lower H p β N D hD hDs hN hsize
    have hf : 1 - (exposure β N : ℝ) / (k + 1) ≤ 1 := by
      have hq : 0 ≤ (exposure β N : ℝ) / (k + 1) := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans (by simpa using h)
  · have hf : 1 - (exposure β N : ℝ) / (k + 1) ≤ 0 := by
      have hn : (k : ℝ) + 1 ≤ exposure β N := by exact_mod_cast (show k + 1 ≤ exposure β N by omega)
      rw [sub_nonpos, le_div_iff₀ (by positivity)]
      simpa using hn
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hf).trans
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

end LongTails.Proofs.HolderNoiseHiding
