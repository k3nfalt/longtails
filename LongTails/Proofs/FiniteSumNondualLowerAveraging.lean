import LongTails.Proofs.FiniteSumNondualLowerExposure
import LongTails.Proofs.FiniteSumNondualLowerPolicy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.FiniteSumNondualLowerAveraging

open FiniteSumNondualLowerExposure FiniteSumNondualLowerHiding Classical

lemma prefix_family_bad_count_bound {ι J : Type*} [DecidableEq ι] [Fintype J] {K : ℕ} {C : ℝ}
    (F : J → (Fin K ↪ ι) → ℕ × Finset ι)
    (hB : ∀ j π, ((F j π).2.card : ℝ) ≤ C) (hC : 0 ≤ C)
    (hK : ∀ j π, (F j π).1 ≤ K)
    (hF : ∀ j π ρ, (∀ z : Fin K, z.val < (F j π).1 → π z = ρ z) → F j π = F j ρ)
    (s : Finset ι) (D : ℝ) (hD : 0 ≤ D) (hDs : D + K ≤ s.card) :
    D * (((distinctWords K s).filter (fun w => ∃ j : J, ∃ π : Fin K ↪ ι,
      List.ofFn π = w ∧ 0 < hits (F j π).2 (w.drop (F j π).1))).card : ℝ) ≤
      (Fintype.card J : ℝ) * K * C * (distinctWords K s).card := by
  classical
  let tree := fun j => prefixTree (F j) (hB j) hC K []
  have he : (distinctWords K s).filter (fun w => ∃ j : J, ∃ π : Fin K ↪ ι,
      List.ofFn π = w ∧ 0 < hits (F j π).2 (w.drop (F j π).1)) =
      (distinctWords K s).filter (fun w => ∃ j, exposedBad (tree j) w = true) := by
    apply Finset.filter_congr
    intro w hw
    constructor
    · rintro ⟨j, π, rfl, hπ⟩
      refine ⟨j, ?_⟩
      rw [show tree j = prefixTree (F j) (hB j) hC K [] from rfl,
        prefixTree_empty_correct (F j) (hB j) hC (hK j) (hF j) π]
      simpa using hπ
    · rintro ⟨j, h⟩
      have hm := (mem_distinctWords K s w).mp hw
      let π := wordEmbedding w hm.1 hm.2.1
      have hπ : List.ofFn π = w := wordEmbedding_ofFn w hm.1 hm.2.1
      refine ⟨j, π, hπ, ?_⟩
      rw [← hπ, show tree j = prefixTree (F j) (hB j) hC K [] from rfl,
        prefixTree_empty_correct (F j) (hB j) hC (hK j) (hF j) π] at h
      simpa [hπ] using h
  rw [he]
  exact tree_family_bad_bound tree hC K s D hD hDs

lemma scaled_bad_fraction {D b total A : ℝ} (hD : 0 < D) (ht : 0 ≤ total)
    (hb : D * b ≤ A * total) (hA : 32 * A ≤ D) : 32 * b ≤ total := by
  apply (mul_le_mul_iff_left₀ hD).mp
  have hs := mul_le_mul_of_nonneg_right hA ht
  nlinarith

lemma finite_gap_average {U V : Type*} (u : Finset U) (v : Finset V)
    (badOwner badCoordinate : U → V → Prop)
    [∀ x y, Decidable (badOwner x y)] [∀ x y, Decidable (badCoordinate x y)]
    (gap : U → V → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hgap : ∀ x ∈ u, ∀ y ∈ v, 0 ≤ gap x y)
    (hgood : ∀ x ∈ u, ∀ y ∈ v, ¬ badOwner x y → ¬ badCoordinate x y → g ≤ gap x y)
    (hOwner : ∀ y ∈ v, 4 * (∑ x ∈ u, if badOwner x y then (1 : ℝ) else 0) ≤ u.card)
    (hCoordinate : ∀ x ∈ u,
      32 * (∑ y ∈ v, if badCoordinate x y then (1 : ℝ) else 0) ≤ v.card) :
    23 * g * u.card * v.card ≤ 32 * ∑ x ∈ u, ∑ y ∈ v, gap x y := by
  have hp (x : U) (hx : x ∈ u) (y : V) (hy : y ∈ v) :
      g * (1 - (if badOwner x y then (1 : ℝ) else 0) -
        (if badCoordinate x y then (1 : ℝ) else 0)) ≤ gap x y := by
    by_cases ho : badOwner x y <;> by_cases hc : badCoordinate x y
    · simp only [ho, hc, ↓reduceIte]; linarith [hgap x hx y hy]
    · simpa only [ho, hc, ↓reduceIte, sub_self, sub_zero, mul_zero] using hgap x hx y hy
    · simpa only [ho, hc, ↓reduceIte, sub_zero, sub_self, mul_zero] using hgap x hx y hy
    · simpa only [ho, hc, ↓reduceIte, sub_zero, mul_one] using hgood x hx y hy ho hc
  have hs := Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hp x hx y hy))
  have ho := Finset.sum_le_sum (fun y hy => hOwner y hy)
  have hc := Finset.sum_le_sum (fun x hx => hCoordinate x hx)
  simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at ho hc
  rw [Finset.sum_comm] at ho
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hgo := mul_le_mul_of_nonneg_left ho hg
  have hgc := mul_le_mul_of_nonneg_left hc hg
  nlinarith

open FiniteSumNondualLowerSimulation FiniteSumNondualLowerComponents
open FiniteSumNondualLowerPolicy FiniteSumNondualLowerSearch
open LongTails.Setups.FiniteSumNondualSmoothConvex OracleTemplate

noncomputable def executionObservation {p : Params}
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p)) (T : ℕ)
    (t : Fin (T + 1)) (s : A.State) : Point p :=
  if t.val < T then (A.query s).2.2.val else (A.output s).val

lemma executionObservation_mem {p : Params}
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p)) (T : ℕ)
    (t : Fin (T + 1)) (s : A.State) : ∑ i, |executionObservation A T t s i| ≤ p.R := by
  unfold executionObservation
  split
  · exact (A.query s).2.2.property
  · exact (A.output s).property

noncomputable def coordinateBad {p : Params} {k : ℕ} (δ a : ℝ)
    (owner : Fin (k + 1) → Fin p.n)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (π : Fin (k + 1) ↪ Fin p.d) : Prop :=
  ∃ t : Fin (T + 1),
    let F := observedPrefix p.L δ a (δ / 4) owner
      (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed)
      (executionObservation A T t) t.val
    0 < hits (F π).2 ((List.ofFn π).drop (F π).1)

lemma coordinate_bad_fraction {p : Params} {k : ℕ} (δ a D : ℝ) (hδ : 0 < δ)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ p.d)
    (owner : Fin (k + 1) → Fin p.n)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed)
    (hsize : 32 * (T + 1 : ℕ) * (k + 1 : ℕ) * (p.R / (δ / 4)) ≤ D) :
    32 * (((distinctWords (k + 1) (Finset.univ : Finset (Fin p.d))).filter
      (fun w => ∃ π : Fin (k + 1) ↪ Fin p.d,
        List.ofFn π = w ∧ coordinateBad δ a owner A T seed π)).card : ℝ) ≤
      (distinctWords (k + 1) (Finset.univ : Finset (Fin p.d))).card := by
  classical
  let q := fun s => ((A.query s).2.1, (A.query s).2.2.val)
  let F := fun t : Fin (T + 1) => observedPrefix p.L δ a (δ / 4) owner q A.update
    (A.initial seed) (executionObservation A T t) t.val
  have hθ : 0 < δ / 4 := by positivity
  have hb : ∀ t π, ((F t π).2.card : ℝ) ≤ p.R / (δ / 4) := fun t =>
    observedPrefix_bound p.L δ a (δ / 4) p.R hθ owner q A.update (A.initial seed)
      (executionObservation A T t) (executionObservation_mem A T t) t.val
  have hk : ∀ t π, (F t π).1 ≤ k + 1 := fun t =>
    observedPrefix_count p.L δ a (δ / 4) owner q A.update (A.initial seed)
      (executionObservation A T t) t.val
  have hf : ∀ t π ρ, (∀ z : Fin (k + 1), z.val < (F t π).1 → π z = ρ z) →
      F t π = F t ρ := fun t =>
    observedPrefix_determined p.L δ a (δ / 4) owner q A.update (A.initial seed)
      (executionObservation A T t) t.val
  have hd : D + (k + 1 : ℕ) ≤ ((Finset.univ : Finset (Fin p.d)).card : ℝ) := by
    simpa using hDs
  have bound := prefix_family_bad_count_bound F hb (div_nonneg p.hR hθ.le) hk hf
    Finset.univ D hD.le hd
  have hs : 32 * ((Fintype.card (Fin (T + 1)) : ℝ) * (k + 1 : ℕ) *
      (p.R / (δ / 4))) ≤ D := by simpa [mul_assoc] using hsize
  have result := scaled_bad_fraction hD (by positivity) bound hs
  convert result using 1
  apply congrArg (fun s : Finset (List (Fin p.d)) => (32 : ℝ) * s.card)
  ext w
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hw, π, hπ, t, ht⟩
    exact ⟨hw, t, π, hπ, by simpa only [hπ] using ht⟩
  · rintro ⟨hw, t, π, hπ, ht⟩
    exact ⟨hw, π, hπ, t, by simpa only [hπ] using ht⟩

lemma execution_gap_of_good {p : Params} {k : ℕ} (δ a : ℝ)
    (hL : 0 ≤ p.L) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (π : Fin (k + 1) ↪ Fin p.d) (owner : Fin (k + 1) → Fin p.n)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit)
    (hgood : ∀ t : Fin (T + 1),
      let F := observedPrefix p.L δ a (δ / 4) owner
        (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed)
        (executionObservation A T t) t.val
      ¬ 0 < hits (F π).2 ((List.ofFn π).drop (F π).1))
    (hincomplete : (simulatedState p.L δ a π owner
      (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed) T).2 < k) :
    p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n) ≤
      objective (hardComponent p.L δ a π owner)
        (execute (hardOracle p δ a π owner) A (fun _ => T) seed ξ).val := by
  let q := fun s => ((A.query s).2.1, (A.query s).2.2.val)
  have hs := simulatedState_coupling p.L δ a hδ π owner q A.update (A.initial seed) T
    (fun t ht j hj => by
      have h := observed_not_bad_small p.L δ a (δ / 4) owner q A.update (A.initial seed)
        (executionObservation A T ⟨t, by omega⟩) t π (hgood ⟨t, by omega⟩) j hj
      simpa only [executionObservation, ht, ↓reduceIte] using h)
  rw [execute_hard, ← hs]
  let r := (simulatedState p.L δ a π owner q A.update (A.initial seed) T).2
  have hr : r + 1 ≤ k := by dsimp [r, q]; omega
  apply hard_objective_gap p δ a hL hδ ha π owner _ (r + 1) hr hscale
  have h := observed_not_bad_small p.L δ a (δ / 4) owner q A.update (A.initial seed)
    (executionObservation A T (Fin.last T)) T π (hgood (Fin.last T))
    ⟨r + 1, by omega⟩ (by change r < r + 1; omega)
  simpa only [executionObservation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using h

abbrev OwnerWords (n k : ℕ) := ↥(words n k)
abbrev CoordinateWords (d k : ℕ) := ↥(distinctWords (k + 1) (Finset.univ : Finset (Fin d)))

def coordinateEmbedding {d k : ℕ} (w : CoordinateWords d k) : Fin (k + 1) ↪ Fin d :=
  wordEmbedding w.val ((mem_distinctWords _ _ _).mp w.property).1
    ((mem_distinctWords _ _ _).mp w.property).2.1

lemma coordinateEmbedding_labels {d k : ℕ} (w : CoordinateWords d k) :
    List.ofFn (coordinateEmbedding w) = w.val := wordEmbedding_ofFn _ _ _

lemma subtype_indicator_sum {U : Type*} (s : Finset U) (P : U → Prop) [DecidablePred P] :
    (∑ x : s, if P x.val then (1 : ℝ) else 0) = (s.filter P).card := by
  rw [Finset.sum_coe_sort s (fun x : U => if P x then (1 : ℝ) else 0), ← Finset.sum_filter]
  simp

lemma owner_bad_sum {p : Params} {k : ℕ} (δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin p.d)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (hk : 0 < k) (hT : 8 * T ≤ p.n * k) :
    4 * (∑ w : OwnerWords p.n k, if k ≤
      (simulatedState p.L δ a π (wordOwner 0 w.val)
        (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed) T).2
      then (1 : ℝ) else 0) ≤ Fintype.card (OwnerWords p.n k) := by
  have h := simulated_completion_fraction p.L δ a π
    (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed) 0 T
    (NeZero.pos p.n) hk hT
  rw [subtype_indicator_sum (words p.n k) (fun w => k ≤
    (simulatedState p.L δ a π (wordOwner 0 w)
      (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed) T).2)]
  simpa [OwnerWords, Fintype.card_coe, words_card] using h

lemma coordinate_bad_sum {p : Params} {k : ℕ} (δ a D : ℝ) (hδ : 0 < δ)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ p.d)
    (owner : Fin (k + 1) → Fin p.n)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed)
    (hsize : 32 * (T + 1 : ℕ) * (k + 1 : ℕ) * (p.R / (δ / 4)) ≤ D) :
    32 * (∑ w : CoordinateWords p.d k,
      if coordinateBad δ a owner A T seed (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords p.d k) := by
  classical
  have he (w : CoordinateWords p.d k) : coordinateBad δ a owner A T seed (coordinateEmbedding w) ↔
      ∃ π : Fin (k + 1) ↪ Fin p.d, List.ofFn π = w.val ∧ coordinateBad δ a owner A T seed π := by
    constructor
    · intro h; exact ⟨coordinateEmbedding w, coordinateEmbedding_labels w, h⟩
    · rintro ⟨π, hπ, h⟩
      have he : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro j
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) j
      simpa [he] using h
  have hs : (∑ w : CoordinateWords p.d k,
      if coordinateBad δ a owner A T seed (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin p.d))).filter
        (fun w => ∃ π : Fin (k + 1) ↪ Fin p.d,
          List.ofFn π = w ∧ coordinateBad δ a owner A T seed π)).card : ℝ) := by
    calc
      _ = ∑ w : CoordinateWords p.d k, if ∃ π : Fin (k + 1) ↪ Fin p.d,
          List.ofFn π = w.val ∧ coordinateBad δ a owner A T seed π then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : coordinateBad δ a owner A T seed (coordinateEmbedding w)
        · simp only [h, (he w).mp h, ↓reduceIte]
        · have hn := mt (he w).mpr h
          simp only [h, hn, ↓reduceIte]
      _ = _ := subtype_indicator_sum
        (distinctWords (k + 1) (Finset.univ : Finset (Fin p.d)))
        (fun w => ∃ π : Fin (k + 1) ↪ Fin p.d,
          List.ofFn π = w ∧ coordinateBad δ a owner A T seed π)
  rw [hs]
  simpa [CoordinateWords, Fintype.card_coe] using
    coordinate_bad_fraction δ a D hδ hD hDs owner A T seed hsize

noncomputable def executionGap {p : Params} {k : ℕ} (δ a : ℝ)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit)
    (u : OwnerWords p.n k) (v : CoordinateWords p.d k) : ℝ :=
  objective (hardComponent p.L δ a (coordinateEmbedding v) (wordOwner 0 u.val))
    (execute (hardOracle p δ a (coordinateEmbedding v) (wordOwner 0 u.val))
      A (fun _ => T) seed ξ).val

lemma execution_joint_gap {p : Params} {k : ℕ} (δ a D : ℝ)
    (hL : 0 ≤ p.L) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ p.d)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (hk : 0 < k) (hT : 8 * T ≤ p.n * k)
    (hsize : 32 * (T + 1 : ℕ) * (k + 1 : ℕ) * (p.R / (δ / 4)) ≤ D) :
    23 * (p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n)) *
      Fintype.card (OwnerWords p.n k) * Fintype.card (CoordinateWords p.d k) ≤
      32 * ∑ u : OwnerWords p.n k, ∑ v : CoordinateWords p.d k, executionGap δ a A T seed ξ u v := by
  classical
  let badOwner := fun (u : OwnerWords p.n k) (v : CoordinateWords p.d k) => k ≤
    (simulatedState p.L δ a (coordinateEmbedding v) (wordOwner 0 u.val)
      (fun s => ((A.query s).2.1, (A.query s).2.2.val)) A.update (A.initial seed) T).2
  let badCoord := fun (u : OwnerWords p.n k) (v : CoordinateWords p.d k) =>
    coordinateBad δ a (wordOwner 0 u.val) A T seed (coordinateEmbedding v)
  have hgap (u : OwnerWords p.n k) (v : CoordinateWords p.d k) :
      0 ≤ executionGap δ a A T seed ξ u v :=
    hard_objective_nonneg p δ a hL _ _ _
  have hgood (u : OwnerWords p.n k) (v : CoordinateWords p.d k)
      (ho : ¬ badOwner u v) (hc : ¬ badCoord u v) :
      p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n) ≤ executionGap δ a A T seed ξ u v := by
    apply execution_gap_of_good δ a hL hδ.le ha hscale
    · intro t
      dsimp only
      intro ht
      exact hc ⟨t, ht⟩
    · exact Nat.lt_of_not_ge ho
  have ho (v : CoordinateWords p.d k) := owner_bad_sum δ a (coordinateEmbedding v) A T seed hk hT
  have hc (u : OwnerWords p.n k) :=
    coordinate_bad_sum δ a D hδ hD hDs (wordOwner 0 u.val) A T seed hsize
  have hg : 0 ≤ p.L * a ^ 2 / (16 * ((k : ℝ) + 1) * p.n) := by positivity
  have h := finite_gap_average Finset.univ Finset.univ badOwner badCoord
    (executionGap δ a A T seed ξ) _ hg
    (fun u _ v _ => hgap u v) (fun u _ v _ => hgood u v)
    (fun v _ => ho v) (fun u _ => hc u)
  simpa only [Finset.card_univ] using h

end LongTails.Proofs.FiniteSumNondualLowerAveraging
