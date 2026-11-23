import LongTails.Algorithms.HighProbabilityStationarity
import LongTails.Proofs.HighProbabilityRounds
import LongTails.Proofs.HighProbabilityTest

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityRoundStep

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate

section Deterministic

variable {β : Type*}

lemma passers_eq {K : ℕ} (e : ℕ → Option β) (pass : Fin K → Bool) (j : ℕ)
    (hj : j < (Finset.univ.filter (fun i => pass i = true)).card) :
    passers e pass j = e ((Finset.univ.filter (fun i => pass i = true)).orderEmbOfFin rfl ⟨j, hj⟩) := by
  simp only [passers, dite_eq_left hj]

lemma round_deterministic {K K' : ℕ} (e : ℕ → Option β) (pass : Fin K → Bool)
    (solid good : β → Prop) (acc : Fin K → Prop)
    [DecidablePred fun i : Fin K => ∃ y, e i = some y ∧ ¬ solid y]
    [DecidablePred fun i : Fin K => ¬ acc i]
    [DecidablePred fun j : Fin K' => ∃ y, passers e pass j = some y ∧ ¬ good y]
    (hsome : ∀ i : Fin K, ∃ y, e i = some y)
    (hpass_some : ∀ i : Fin K, pass i = true → ∃ y, e i = some y)
    (hpass : ∀ i : Fin K, ∀ y, e i = some y → solid y → acc i → pass i = true)
    (hgood : ∀ i : Fin K, ∀ y, e i = some y → pass i = true → acc i → good y)
    (hsolid : 3 * (Finset.univ.filter (fun i : Fin K => ∃ y, e i = some y ∧ ¬ solid y)).card ≤ K)
    (hacc : 6 * (Finset.univ.filter (fun i : Fin K => ¬ acc i)).card ≤ K)
    (hK : 2 * K' = K ∨ (K = 1 ∧ K' = 1)) :
    (∀ j < K', ∃ y, passers e pass j = some y) ∧
      3 * (Finset.univ.filter (fun j : Fin K' => ∃ y, passers e pass j = some y ∧ ¬ good y)).card ≤
        K' := by
  classical
  set S := Finset.univ.filter (fun i : Fin K => pass i = true) with hS
  set Bs := Finset.univ.filter (fun i : Fin K => ∃ y, e i = some y ∧ ¬ solid y)
  set Ba := Finset.univ.filter (fun i : Fin K => ¬ acc i)
  have hcover : (Finset.univ : Finset (Fin K)) ⊆ S ∪ Bs ∪ Ba := by
    intro i _
    by_cases hp : pass i = true
    · simp [S, hp]
    · obtain ⟨y, hy⟩ := hsome i
      by_cases hs : solid y
      · have : ¬ acc i := fun ha => hp (hpass i y hy hs ha)
        simp [Ba, this]
      · simp only [Finset.mem_union]
        left; right
        simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hy, hs⟩
  have hcard : K ≤ S.card + Bs.card + Ba.card := by
    have h1 := Finset.card_le_card hcover
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_union_le (S ∪ Bs) Ba
    have h3 := Finset.card_union_le S Bs
    omega
  have hSK : K' ≤ S.card := by
    rcases hK with h | ⟨h1, h2⟩
    · omega
    · omega
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [passers_eq e pass j (lt_of_lt_of_le hj hSK)]
    exact hpass_some _ (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem S rfl ⟨j, by omega⟩)).2
  · let φ : Fin K' → Fin K := fun j => S.orderEmbOfFin rfl ⟨j, by omega⟩
    have hφinj : Function.Injective φ := by
      intro a b hab
      have := (S.orderEmbOfFin rfl).injective hab
      exact Fin.ext (by simpa using congrArg Fin.val this)
    have hmap : (Finset.univ.filter (fun j : Fin K' => ∃ y, passers e pass j = some y ∧ ¬ good y)).map
        ⟨φ, hφinj⟩ ⊆ Ba := by
      intro i hi
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk] at hi
      obtain ⟨j, ⟨y, hy, hng⟩, rfl⟩ := hi
      rw [passers_eq e pass j (lt_of_lt_of_le j.isLt hSK)] at hy
      have hmem : φ j ∈ S := Finset.orderEmbOfFin_mem S rfl _
      have hp : pass (φ j) = true := (Finset.mem_filter.mp hmem).2
      simp only [Ba, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ha
      exact hng (hgood (φ j) y hy hp ha)
    have hle := Finset.card_le_card hmap
    rw [Finset.card_map] at hle
    rcases hK with h | ⟨h1, h2⟩
    · omega
    · omega

end Deterministic

end LongTails.Proofs.HighProbabilityRoundStep
