import LongTails.Proofs.SmoothConvexFiniteAveraging

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical

namespace LongTails.Proofs.FinitePrefixSimulation

open SmoothConvexFiniteHiding FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure

variable {d k : ℕ} {S : Type*}

noncomputable def state
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (π : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 => let s := state partialReply π query update initial t
             update s (partialReply π t (query s))

lemma state_prefix
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hp : ∀ π ρ r x, (∀ i, i.val ≤ r → π i = ρ i) → partialReply π r x = partialReply ρ r x)
    (π ρ : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (t : ℕ)
    (h : ∀ i, i.val < t → π i = ρ i) :
    state partialReply π query update initial t = state partialReply ρ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun i hi => h i (by omega))
    simp only [state, he]
    rw [hp π ρ t _ (fun i hi => h i (by omega))]

noncomputable def observation
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  let s := state partialReply π query update initial t.val
  if t.val < k then query s else output s

lemma observation_prefix
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hp : ∀ π ρ r x, (∀ i, i.val ≤ r → π i = ρ i) → partialReply π r x = partialReply ρ r x)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (t : Fin (k + 1)) (π ρ : Fin (k + 1) ↪ Fin d)
    (h : ∀ i, i.val < t.val → π i = ρ i) :
    observation partialReply query output update initial t π = observation partialReply query output update initial t ρ := by
  unfold observation
  rw [state_prefix partialReply hp π ρ query update initial t.val h]

def bad (B θ : ℝ)
    (observe : Fin (k + 1) → (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d))
    (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (k + 1), 0 < hits (largeSet B θ (observe t π)) ((List.ofFn π).drop t.val)

lemma good_small (B θ : ℝ)
    (observe : Fin (k + 1) → (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d))
    (π : Fin (k + 1) ↪ Fin d) (hgood : ¬ bad B θ observe π)
    (t j : Fin (k + 1)) (hj : t.val ≤ j.val) (ht : ‖observe t π‖ ≤ B) : |observe t π (π j)| ≤ θ := by
  apply not_largeSet_small B θ _ ht
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ j hj h⟩

lemma state_coupling (B θ : ℝ)
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (reply : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (heq : ∀ π r x, r < k → (‖x‖ < B → ∀ i, r ≤ i.val → |x (π i)| ≤ θ) → partialReply π r x = reply π x)
    (π : Fin (k + 1) ↪ Fin d) (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (hgood : ¬ bad B θ (observation partialReply query output update initial) π) :
    state partialReply π query update initial k = (fun s => update s (reply π (query s)))^[k] initial := by
  have hc (T : ℕ) (hT : T ≤ k) : state partialReply π query update initial T =
      (fun s => update s (reply π (query s)))^[T] initial := by
    induction T with
    | zero => rfl
    | succ T ih =>
      have ht : T < k := by omega
      have he := heq π T (query (state partialReply π query update initial T)) ht (by
        intro hx i hi
        have hs := good_small B θ _ π hgood ⟨T, by omega⟩ i hi
          (by simpa only [observation, ht, ↓reduceIte] using hx.le)
        simpa only [observation, ht, ↓reduceIte] using hs)
      rw [state, he, ih (by omega), Function.iterate_succ_apply']
  exact hc k le_rfl

lemma good_loss (B θ gap : ℝ)
    (partialReply : (Fin (k + 1) ↪ Fin d) → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (reply : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (loss : (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (heq : ∀ π r x, r < k → (‖x‖ < B → ∀ i, r ≤ i.val → |x (π i)| ≤ θ) → partialReply π r x = reply π x)
    (hnear : ∀ π x, |x (π (Fin.last k))| ≤ θ → gap ≤ loss π x)
    (hfar : ∀ π x, B ≤ ‖x‖ → gap ≤ loss π x)
    (π : Fin (k + 1) ↪ Fin d) (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (hgood : ¬ bad B θ (observation partialReply query output update initial) π) :
    gap ≤ loss π (output ((fun s => update s (reply π (query s)))^[k] initial)) := by
  rw [← state_coupling B θ partialReply reply heq π query output update initial hgood]
  by_cases hx : ‖output (state partialReply π query update initial k)‖ ≤ B
  · apply hnear
    have hs := good_small B θ _ π hgood (Fin.last k) (Fin.last k) le_rfl
      (by simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using hx)
    simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using hs
  · exact hfar π _ (le_of_not_ge hx)

open FiniteSumNondualLowerAveraging
open scoped BigOperators

lemma bad_sum_bound (B θ D : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (hD : 0 ≤ D)
    (hDs : D + (k + 1 : ℕ) ≤ d)
    (observe : Fin (k + 1) → (Fin (k + 1) ↪ Fin d) → EuclideanSpace ℝ (Fin d))
    (hp : ∀ t π ρ, (∀ i, i.val < t.val → π i = ρ i) → observe t π = observe t ρ) :
    D * (∑ w : CoordinateWords d k, if bad B θ observe (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (k + 1 : ℕ) ^ 2 * (B ^ 2 / θ ^ 2) * Fintype.card (CoordinateWords d k) := by
  classical
  have he (w : CoordinateWords d k) : bad B θ observe (coordinateEmbedding w) ↔
      ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet B θ (observe t π)) (w.val.drop t.val) := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using ht⟩
    · rintro ⟨t, π, hπ, ht⟩
      have hpe : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro j
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) j
      exact ⟨t, by simpa only [hpe, ← coordinateEmbedding_labels w] using ht⟩
  let P := fun w : List (Fin d) => ∃ t : Fin (k + 1), ∃ π : Fin (k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet B θ (observe t π)) (w.drop t.val)
  have hs : (∑ w : CoordinateWords d k, if bad B θ observe (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) B θ D hB hθ hD hDs
    (fun t : Fin (k + 1) => t.val) (fun t => t.isLt.le) observe hp
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe, pow_two, mul_assoc] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

end LongTails.Proofs.FinitePrefixSimulation
