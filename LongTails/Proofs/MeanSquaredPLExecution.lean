import LongTails.Proofs.MeanSquaredPLOracle
import LongTails.Proofs.ThirdOrderMaskedExecution
import LongTails.Proofs.HessianPLLocalized

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MeanSquaredPLExecution

open Classical
open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.MeanSquaredPLMask
open LongTails.Proofs.MeanSquaredPLSecret LongTails.Proofs.MeanSquaredPLOracle
open LongTails.Proofs.ThirdOrderMaskedExecution (lvl lvl_mono lvl_le lvl_pos)
open LongTails.Proofs.RelativeHessianSimulation (axes axes_inner axes_orthonormal)
open LongTails.Proofs.RelativeHessianLocalized (radius radius_pos)
open LongTails.Proofs.AbcHardOracle (coin Scale toUnit)
open LongTails.Proofs.AbcHardExecution (coinCount coinCount_mono)
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging

variable {d n : ℕ} {St : Type*}

lemma plSim_prefix (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (R : ℕ) (hR : 1 ≤ R)
    (x0 x : Space d) (ω : ℝ) (h : ∀ k : Fin (n + 1), k.val < R → π k = ρ k) :
    plSim S q π R x0 x ω = plSim S q ρ R x0 x ω := by
  unfold plSim
  rw [unitSim_prefix R hR π ρ _ _ h]

noncomputable def simState (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState S q π x0 query update initial ω t
    update s (plSim S q π (lvl n q ω (t + 1)) x0 (query s).1 (ω t),
      plSim S q π (lvl n q ω (t + 1)) x0 (query s).2 (ω t))

noncomputable def trueState (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := trueState S q π x0 query update initial ω t
    update s (plReply S q π x0 (query s).1 (ω t), plReply S q π x0 (query s).2 (ω t))

lemma simState_prefix (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (t : ℕ) (h : ∀ k : Fin (n + 1), k.val < lvl n q ω t → π k = ρ k) :
    simState S q π x0 query update initial ω t = simState S q ρ x0 query update initial ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := lvl_mono n q ω (Nat.le_add_right t 1)
    have he := ih (fun k hk => h k (by omega))
    simp only [simState]
    rw [he, plSim_prefix S q π ρ _ (lvl_pos n q ω (t + 1)) x0 _ _ h,
      plSim_prefix S q π ρ _ (lvl_pos n q ω (t + 1)) x0 _ _ h]

lemma reply_eq_sim (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℕ → ℝ) (t : ℕ)
    (hhit : ‖toUnit S x0 x‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), lvl n q ω t ≤ i.val → |toUnit S x0 x (π i)| ≤ 1 / 40) :
    plReply S q π x0 x (ω t) = plSim S q π (lvl n q ω (t + 1)) x0 x (ω t) := by
  unfold plReply plSim
  congr 1
  have hle := lvl_le n q ω t
  by_cases hfull : lvl n q ω t = n + 1
  · have hnext : lvl n q ω (t + 1) = n + 1 :=
      le_antisymm (lvl_le n q ω (t + 1)) (hfull ▸ lvl_mono n q ω (Nat.le_add_right t 1))
    rw [hnext]
    exact reply_eq_sim_full π _ _
  · have hr : lvl n q ω t ≤ n := by omega
    have hcc : lvl n q ω t = coinCount q ω t + 1 := by
      unfold lvl at hfull hr ⊢
      omega
    by_cases hc : ω t ≤ q
    · have hnext : lvl n q ω (t + 1) = lvl n q ω t + 1 := by
        have h1 : lvl n q ω (t + 1) = min (n + 1) (coinCount q ω t + 1 + 1) := by
          simp [lvl, coinCount, hc]
        omega
      rw [hnext]
      exact reply_eq_sim_succ _ hr π _ _ hhit
    · have hnext : lvl n q ω (t + 1) = lvl n q ω t := by
        simp [lvl, coinCount, hc]
      have hc0 : coin q (ω t) = 0 := by
        unfold coin
        rw [ite_eq_right hc]
      rw [hnext, hc0]
      exact reply_eq_sim_zero _ hr π _ hhit

lemma coupling (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N, ∀ x : Space d,
      (x = (query (simState S q π x0 query update initial ω t)).1 ∨
        x = (query (simState S q π x0 query update initial ω t)).2) →
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), lvl n q ω t ≤ i.val → |toUnit S x0 x (π i)| ≤ 1 / 40) :
    simState S q π x0 query update initial ω N = trueState S q π x0 query update initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hhit t (by omega))
    simp only [simState, trueState]
    rw [← he, reply_eq_sim S q π x0 _ ω N (hhit N (by omega) _ (Or.inl rfl)),
      reply_eq_sim S q π x0 _ ω N (hhit N (by omega) _ (Or.inr rfl))]

noncomputable def observation (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1) × Bool) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  if j.1.val < N then
    toUnit S x0 (if j.2 then (query (simState S q π x0 query update initial ω j.1.val)).1
      else (query (simState S q π x0 query update initial ω j.1.val)).2)
  else toUnit S x0 (output (simState S q π x0 query update initial ω j.1.val))

lemma observation_prefix (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1) × Bool) (π ρ : Fin (n + 1) ↪ Fin d)
    (h : ∀ k : Fin (n + 1), k.val < lvl n q ω j.1.val → π k = ρ k) :
    observation S q x0 query output update initial ω N j π =
      observation S q x0 query output update initial ω N j ρ := by
  unfold observation
  rw [simState_prefix S q π ρ x0 query update initial ω j.1.val h]

lemma observation_fst (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N t : ℕ) (ht : t < N) (π : Fin (n + 1) ↪ Fin d) :
    observation S q x0 query output update initial ω N (⟨t, by omega⟩, true) π =
      toUnit S x0 (query (simState S q π x0 query update initial ω t)).1 := by
  simp [observation, ht]

lemma observation_snd (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N t : ℕ) (ht : t < N) (π : Fin (n + 1) ↪ Fin d) :
    observation S q x0 query output update initial ω N (⟨t, by omega⟩, false) π =
      toUnit S x0 (query (simState S q π x0 query update initial ω t)).2 := by
  simp [observation, ht]

lemma observation_last (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d) :
    observation S q x0 query output update initial ω N (Fin.last N, true) π =
      toUnit S x0 (output (simState S q π x0 query update initial ω N)) := by
  simp [observation]

def coordinateBad (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1) × Bool, 0 < hits
    (largeSet (2 * radius n) (1 / 40)
      (observation S q x0 query output update initial ω N j π))
    ((List.ofFn π).drop (lvl n q ω j.1.val))

lemma good_small (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S q x0 query output update initial ω N π)
    (j : Fin (N + 1) × Bool)
    (hj : ‖observation S q x0 query output update initial ω N j π‖ ≤ 2 * radius n)
    (i : Fin (n + 1)) (hi : lvl n q ω j.1.val ≤ i.val) :
    |observation S q x0 query output update initial ω N j π (π i)| ≤ 1 / 40 := by
  apply not_largeSet_small _ _ _ hj
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ i hi h⟩

lemma bad_sum_bound (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d) :
    D * (∑ w : CoordinateWords d n, if coordinateBad S q x0 query output update initial ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (2 * (N + 1 : ℕ) : ℕ) * (n + 1 : ℕ) * ((2 * radius n) ^ 2 / (1 / 40) ^ 2) *
        Fintype.card (CoordinateWords d n) := by
  let bad := fun π : Fin (n + 1) ↪ Fin d =>
    coordinateBad S q x0 query output update initial ω N π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1) × Bool, ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (2 * radius n) (1 / 40)
          (observation S q x0 query output update initial ω N j π))
          (w.val.drop (lvl n q ω j.1.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro k
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) k
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1) × Bool, ∃ π : Fin (n + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (2 * radius n) (1 / 40)
      (observation S q x0 query output update initial ω N j π))
      (w.drop (lvl n q ω j.1.val))
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) (2 * radius n) (1 / 40) D
    (by have := radius_pos n; positivity) (by norm_num) hD hDs
    (fun j : Fin (N + 1) × Bool => lvl n q ω j.1.val) (fun j => lvl_le n q ω j.1.val)
    (observation S q x0 query output update initial ω N)
    (observation_prefix S q x0 query output update initial ω N)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, CoordinateWords,
    Fintype.card_coe] at h ⊢
  have hcard : (((N + 1) * 2 : ℕ) : ℝ) = ((2 * (N + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcard] at h
  convert h using 1

lemma good_gap (S : Scale) (q : ℝ) (x0 : Space d)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S q x0 query output update initial ω N π) :
    S.a * ((n : ℝ) - lvl n q ω N) ≤
      objective S π x0 (output (trueState S q π x0 query update initial ω N)) -
        S.a * ((n + 1 : ℕ) * HessianPLWell.bottom) := by
  have hhit : ∀ t < N, ∀ x : Space d,
      (x = (query (simState S q π x0 query update initial ω t)).1 ∨
        x = (query (simState S q π x0 query update initial ω t)).2) →
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), lvl n q ω t ≤ i.val → |toUnit S x0 x (π i)| ≤ 1 / 40 := by
    intro t ht x hx hnorm i hi
    rcases hx with hx | hx
    · have h := good_small S q x0 query output update initial ω N π hgood (⟨t, by omega⟩, true)
      rw [observation_fst S q x0 query output update initial ω N t ht π] at h
      rw [hx]
      exact h (by rw [← hx]; exact hnorm) i hi
    · have h := good_small S q x0 query output update initial ω N π hgood (⟨t, by omega⟩, false)
      rw [observation_snd S q x0 query output update initial ω N t ht π] at h
      rw [hx]
      exact h (by rw [← hx]; exact hnorm) i hi
  rw [← coupling S q π x0 query update initial ω N hhit]
  have h := good_small S q x0 query output update initial ω N π hgood (Fin.last N, true)
  rw [observation_last S q x0 query output update initial ω N π] at h
  simp only [Fin.val_last] at h
  have hR := RelativeHessianLocalized.radius_large n
  have hun := HessianPLLocalized.value_unfinished (axes_orthonormal π)
    (toUnit S x0 (output (simState S q π x0 query update initial ω N))) (lvl n q ω N)
    (fun hx j hj => by
      rw [axes_inner]
      have := h (by linarith [radius_pos n]) j hj
      linarith)
  have ha := S.ha
  unfold objective hardValue
  have := mul_le_mul_of_nonneg_left hun ha.le
  linarith

end LongTails.Proofs.MeanSquaredPLExecution
