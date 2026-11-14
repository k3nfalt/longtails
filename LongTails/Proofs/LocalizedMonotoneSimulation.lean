import LongTails.Proofs.LocalizedMonotoneJets
import LongTails.Proofs.SmoothConvexFiniteHiding

namespace LongTails.Proofs.LocalizedMonotoneSimulation

open LocalizedMonotoneJets LocalizedMonotoneInstance LocalizedMonotoneRadial
open SmoothConvexFiniteHiding FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Reply (d : ℕ) := Space d × (Space d →L[ℝ] Space d)

noncomputable def simulatedState {d n : ℕ} {S : Type*} (a b c γ : ℝ)
    (π : Fin (n + 1) ↪ Fin d) (query : S → Space d)
    (update : S → Reply d → S) (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let s := simulatedState a b c γ π query update initial t
    update s (partialReply a b c γ t π (query s))

lemma simulatedState_prefix {d n : ℕ} {S : Type*} (a b c γ : ℝ)
    (π τ : Fin (n + 1) ↪ Fin d) (query : S → Space d)
    (update : S → Reply d → S) (initial : S) (t : ℕ)
    (h : ∀ i : Fin (n + 1), i.val < t → π i = τ i) :
    simulatedState a b c γ π query update initial t =
      simulatedState a b c γ τ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun i hi => h i (by omega))
    simp only [simulatedState, he]
    rw [partialReply_prefix a b c γ π τ _ h]

lemma simulatedState_coupling {d n : ℕ} {S : Type*} (a b c γ : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (query : S → Space d)
    (update : S → Reply d → S) (initial : S) (T : ℕ) (hT : T ≤ n)
    (hgood : ∀ t < T, ∀ i : Fin (n + 1), t ≤ i.val →
      |radial b (query (simulatedState a b c γ π query update initial t)) (π i)| ≤ a) :
    simulatedState a b c γ π query update initial T =
      (fun s => update s (field a b c γ π (query s), jacobian a b γ π (query s)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (by omega) (fun t ht => hgood t (by omega))
    rw [simulatedState, ← fullReply_eq_partial a b c γ ha (by omega) π _ (hgood T (by omega)),
      he, Function.iterate_succ_apply']

noncomputable def observation {d n k : ℕ} {S : Type*} (a b c γ : ℝ)
    (query output : S → Space d) (update : S → Reply d → S) (initial : S)
    (t : Fin (k + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  let s := simulatedState a b c γ π query update initial t.val
  if t.val < k then radial b (query s) else output s

lemma observation_prefix {d n k : ℕ} {S : Type*} (a b c γ : ℝ)
    (query output : S → Space d) (update : S → Reply d → S) (initial : S)
    (t : Fin (k + 1)) (π τ : Fin (n + 1) ↪ Fin d)
    (h : ∀ i : Fin (n + 1), i.val < t.val → π i = τ i) :
    observation a b c γ query output update initial t π =
      observation a b c γ query output update initial t τ := by
  unfold observation
  rw [simulatedState_prefix a b c γ π τ query update initial t.val h]

def coordinateBad {d n k : ℕ} {S : Type*} (a b c γ B : ℝ)
    (query output : S → Space d) (update : S → Reply d → S) (initial : S)
    (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ t : Fin (k + 1), 0 < hits
    (largeSet B a (observation a b c γ query output update initial t π))
    ((List.ofFn π).drop t.val)

lemma good_observation_small {d n k : ℕ} {S : Type*} (a b c γ B : ℝ)
    (query output : S → Space d) (update : S → Reply d → S) (initial : S)
    (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad (k := k) a b c γ B query output update initial π)
    (t : Fin (k + 1)) (i : Fin (n + 1)) (hi : t.val ≤ i.val)
    (ht : ‖observation a b c γ query output update initial t π‖ ≤ B) :
    |observation a b c γ query output update initial t π (π i)| ≤ a := by
  apply not_largeSet_small _ _ _ ht
  intro h
  exact hgood ⟨t, hits_drop_positive π t.val _ i hi h⟩

lemma good_execution_residual {d n k : ℕ} {S : Type*} (a b c γ B η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hk : k ≤ n)
    (hB : 3 * b / 2 ≤ B) (hbB : b ≤ B)
    (hcoerce : Real.sqrt (n + 1) * c + (2 * (n + 1) + 1) * η ≤ b)
    (hgap : Real.sqrt (n + 1) * η ≤ c - a - n * (3 * a / 2))
    (query output : S → Space d) (update : S → Reply d → S) (initial : S)
    (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad (k := k) a b c γ B query output update initial π) :
    γ * η ≤ ‖field a b c γ π
      (output ((fun s => update s (field a b c γ π (query s), jacobian a b γ π (query s)))^[k] initial))‖ := by
  have he := simulatedState_coupling a b c γ ha π query update initial k hk
    (fun t ht i hi => by
      have ho : ‖observation a b c γ query output update initial (⟨t, by omega⟩ : Fin (k + 1)) π‖ ≤ B := by
        simp only [observation, ht, ↓reduceIte]
        exact (radial_bounded b hb _).trans hB
      have h := good_observation_small a b c γ B query output update initial π hgood
        (⟨t, by omega⟩ : Fin (k + 1)) i hi ho
      simpa only [observation, ht, ↓reduceIte] using h)
  rw [← he, field_norm a b c γ hγ]
  apply mul_le_mul_of_nonneg_left _ hγ
  apply LocalizedMonotoneCoercivity.localized_residual_lower a b c η ha hb hc π _ hcoerce hgap
  intro hx
  have ho : ‖observation a b c γ query output update initial (Fin.last k) π‖ ≤ B := by
    simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using hx.trans hbB
  have h := good_observation_small a b c γ B query output update initial π hgood
    (Fin.last k) (Fin.last n) hk ho
  simpa only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] using h

end LongTails.Proofs.LocalizedMonotoneSimulation
