import LongTails.Proofs.StochasticMintyOracle
import LongTails.Proofs.AbcHardExecution
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StochasticMintyHiding

open Classical
open LongTails.Proofs.MintyChainGeometry LongTails.Proofs.StochasticMintyOracle
open LongTails.Proofs.AbcHardExecution (coinCount level level_mono level_le)
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging

variable {d k : ℕ} {St : Type*}

noncomputable def simState (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState κ r B q π query update initial ω t
    update s (simReply κ r B q π (level k q ω (t + 1)) (query s) (ω t))

noncomputable def trueState (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := trueState κ r B q π query update initial ω t
    update s (reply κ r B q π (query s) (ω t))

lemma simState_prefix (κ r B q : ℝ) (π ρ : Fin (k + 1) ↪ Fin d)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (ω : ℕ → ℝ) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val < level k q ω t → π j = ρ j) :
    simState κ r B q π query update initial ω t = simState κ r B q ρ query update initial ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := level_mono k q ω (Nat.le_add_right t 1)
    have he := ih (fun j hj => h j (by omega))
    simp only [simState]
    rw [he, simReply_prefix κ r B q π ρ _ _ _ h]

lemma level_coin (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) (h : level k q ω (t + 1) = level k q ω t) :
    k + 1 ≤ level k q ω t ∨ q < ω t := by
  by_cases hc : ω t ≤ q
  · left
    have h1 : level k q ω (t + 1) = min (k + 1) (coinCount q ω t + 1) := by
      simp [level, coinCount, hc]
    have h2 : level k q ω t = min (k + 1) (coinCount q ω t) := rfl
    omega
  · exact Or.inr (not_le.mp hc)

lemma coupling (κ r B q : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (query : St → EuclideanSpace ℝ (Fin d)) (update : St → EuclideanSpace ℝ (Fin d) → St)
    (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N, ∀ j : Fin (k + 1), level k q ω t ≤ j.val →
      |ball B (query (simState κ r B q π query update initial ω t)) (π j)| ≤ r / 4) :
    simState κ r B q π query update initial ω N = trueState κ r B q π query update initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hmono := level_mono k q ω (Nat.le_add_right N 1)
    have he := ih (fun t ht => hhit t (by omega))
    simp only [simState, trueState]
    rw [← he, reply_eq_simReply κ r B q hr π _ (level k q ω N) (level k q ω (N + 1)) hmono (ω N)
      (hhit N (by omega)) (fun hlev => level_coin q ω N hlev)]

noncomputable def observation (κ r B q : ℝ) (query output : St → EuclideanSpace ℝ (Fin d))
    (update : St → EuclideanSpace ℝ (Fin d) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (j : Fin (N + 1)) (π : Fin (k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  let s := simState κ r B q π query update initial ω j.val
  ball B (if j.val < N then query s else output s)

lemma observation_prefix (κ r B q : ℝ) (query output : St → EuclideanSpace ℝ (Fin d))
    (update : St → EuclideanSpace ℝ (Fin d) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (j : Fin (N + 1)) (π ρ : Fin (k + 1) ↪ Fin d)
    (h : ∀ i : Fin (k + 1), i.val < level k q ω j.val → π i = ρ i) :
    observation κ r B q query output update initial ω N j π =
      observation κ r B q query output update initial ω N j ρ := by
  unfold observation
  rw [simState_prefix κ r B q π ρ query update initial ω j.val h]

def coordinateBad (κ r B q : ℝ) (query output : St → EuclideanSpace ℝ (Fin d))
    (update : St → EuclideanSpace ℝ (Fin d) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits
    (largeSet B (r / 4) (observation κ r B q query output update initial ω N j π))
    ((List.ofFn π).drop (level k q ω j.val))

lemma good_small (κ r B q : ℝ) (hB : 0 ≤ B) (query output : St → EuclideanSpace ℝ (Fin d))
    (update : St → EuclideanSpace ℝ (Fin d) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad κ r B q query output update initial ω N π)
    (j : Fin (N + 1)) (i : Fin (k + 1)) (hi : level k q ω j.val ≤ i.val) :
    |observation κ r B q query output update initial ω N j π (π i)| ≤ r / 4 := by
  apply not_largeSet_small _ _ _ (ball_norm_le B hB _)
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ i hi h⟩

lemma bad_sum_bound (κ r B q : ℝ) (hB : 0 ≤ B) (hr : 0 < r)
    (query output : St → EuclideanSpace ℝ (Fin d))
    (update : St → EuclideanSpace ℝ (Fin d) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hDs : D + (k + 1 : ℕ) ≤ d) :
    D * (∑ w : CoordinateWords d k, if coordinateBad κ r B q query output update initial ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (k + 1 : ℕ) * (B ^ 2 / (r / 4) ^ 2) *
        Fintype.card (CoordinateWords d k) := by
  let bad := fun π : Fin (k + 1) ↪ Fin d =>
    coordinateBad κ r B q query output update initial ω N π
  have he (w : CoordinateWords d k) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet B (r / 4)
          (observation κ r B q query output update initial ω N j π))
          (w.val.drop (level k q ω j.val)) := by
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
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1), ∃ π : Fin (k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet B (r / 4)
      (observation κ r B q query output update initial ω N j π))
      (w.drop (level k q ω j.val))
  have hs : (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := k + 1) B (r / 4) D
    hB (by positivity) hD hDs
    (fun j : Fin (N + 1) => level k q ω j.val) (fun j => level_le k q ω j.val)
    (observation κ r B q query output update initial ω N)
    (observation_prefix κ r B q query output update initial ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma good_floor (κ r B q : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hB : 0 < B)
    (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2)
    (query output : St → EuclideanSpace ℝ (Fin d))
    (update : St → EuclideanSpace ℝ (Fin d) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad κ r B q query output update initial ω N π)
    (hlev : level k q ω N < k + 1) :
    3 * κ ^ 2 * r ^ 2 / 16 ≤
      ‖field κ r B π (output (trueState κ r B q π query update initial ω N))‖ ^ 2 := by
  have hhit : ∀ t < N, ∀ j : Fin (k + 1), level k q ω t ≤ j.val →
      |ball B (query (simState κ r B q π query update initial ω t)) (π j)| ≤ r / 4 := by
    intro t ht j hj
    have h := good_small κ r B q hB.le query output update initial ω N π hgood ⟨t, by omega⟩ j hj
    simpa only [observation, ht, ↓reduceIte] using h
  rw [← coupling κ r B q hr π query update initial ω N hhit]
  apply field_lower κ r B hκ hr hB π hrad
  refine ⟨Fin.last k, ?_⟩
  have h := good_small κ r B q hB.le query output update initial ω N π hgood (Fin.last N)
    (Fin.last k) (by simp only [Fin.val_last]; omega)
  simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
  have h2 := le_abs_self (ball B (output (simState κ r B q π query update initial ω N))
    (π (Fin.last k)))
  linarith

end LongTails.Proofs.StochasticMintyHiding
