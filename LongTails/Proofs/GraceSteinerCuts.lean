import Mathlib.Tactic

namespace LongTails.Proofs.GraceSteinerCuts

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

structure Endpoints (V E : Type*) where
  left : E → V
  right : E → V

def Splits (S C : Finset V) := (∃ i ∈ S, i ∈ C) ∧ (∃ j ∈ S, j ∉ C)

def Crosses (a : Endpoints V E) (C : Finset V) (e : E) : Prop :=
  ¬ (a.left e ∈ C ↔ a.right e ∈ C)

instance (a : Endpoints V E) (C : Finset V) (e : E) : Decidable (Crosses a C e) :=
  inferInstanceAs (Decidable (¬ (_ ↔ _)))

def cut (a : Endpoints V E) (b : E → ℝ) (C : Finset V) :=
  ∑ e, if Crosses a C e then b e else 0

def Connects (a : Endpoints V E) (S : Finset V) (F : Finset E) :=
  ∀ C, Splits S C → ∃ e ∈ F, Crosses a C e

def merge (u v i : V) := if i = u then v else i

def Endpoints.contract (a : Endpoints V E) (u v : V) : Endpoints V E :=
  ⟨fun e => merge u v (a.left e), fun e => merge u v (a.right e)⟩

def preimage (u v : V) (C : Finset V) := Finset.univ.filter (fun i => merge u v i ∈ C)

omit [Fintype E] [DecidableEq E] in
lemma split_image_iff (S C : Finset V) (u v : V) :
    Splits (S.image (merge u v)) C ↔ Splits S (preimage u v C) := by
  simp [Splits, preimage]

omit [DecidableEq E] in
lemma contracted_cut (a : Endpoints V E) (b : E → ℝ) (C : Finset V) (u v : V) :
    cut (a.contract u v) b C = cut a b (preimage u v C) := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : merge u v (a.left e) ∈ C ↔ merge u v (a.right e) ∈ C <;>
    simp [Crosses, Endpoints.contract, preimage, he]

omit [DecidableEq E] in
lemma contraction_preserves_mincut (a : Endpoints V E) (b : E → ℝ) (S : Finset V)
    (rate : ℝ) (hcut : ∀ C, Splits S C → rate ≤ cut a b C) (u v : V) :
    ∀ C, Splits (S.image (merge u v)) C → rate ≤ cut (a.contract u v) b C := by
  intro C hC
  rw [contracted_cut]
  exact hcut _ ((split_image_iff ..).mp hC)

omit [Fintype E] in
lemma lift_connector (a : Endpoints V E) (S : Finset V) (e₀ : E) (F : Finset E)
    (h : Connects (a.contract (a.left e₀) (a.right e₀))
      (S.image (merge (a.left e₀) (a.right e₀))) F) : Connects a S (insert e₀ F) := by
  intro C hC
  by_cases hc : Crosses a C e₀
  · exact ⟨_, Finset.mem_insert_self .., hc⟩
  · have he : a.left e₀ ∈ C ↔ a.right e₀ ∈ C := Classical.not_not.mp hc
    have hm (i : V) : merge (a.left e₀) (a.right e₀) i ∈ C ↔ i ∈ C := by
      by_cases hi : i = a.left e₀
      · simpa [merge, hi] using he.symm
      · simp [merge, hi]
    have hpre : preimage (a.left e₀) (a.right e₀) C = C := by ext; simp [preimage, hm]
    obtain ⟨e, hmem, hcross⟩ := h C ((split_image_iff ..).mpr (hpre.symm ▸ hC))
    exact ⟨e, Finset.mem_insert_of_mem hmem, by simpa [Crosses, Endpoints.contract, hm] using hcross⟩

def incidence (a : Endpoints V E) (S : Finset V) (e : E) : ℕ :=
  ∑ i ∈ S, if Crosses a {i} e then 1 else 0

omit [Fintype V] [DecidableEq E] in
lemma incidence_cost (a : Endpoints V E) (S : Finset V) (b : E → ℝ) :
    ∑ e, b e * incidence a S e = ∑ i ∈ S, cut a b {i} := by
  classical
  unfold cut incidence
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

omit [Fintype V] [DecidableEq E] in
lemma incidence_capacity (a : Endpoints V E) (S : Finset V) (b : E → ℝ) (rate : ℝ)
    (hS : 1 < S.card) (hcut : ∀ C, Splits S C → rate ≤ cut a b C) :
    (S.card : ℝ) * rate ≤ ∑ e, b e * incidence a S e := by
  rw [incidence_cost]
  calc
    _ = ∑ _ ∈ S, rate := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hS i
      exact hcut _ ⟨⟨i, hi, by simp⟩, ⟨j, hj, by simpa using hji⟩⟩

end LongTails.Proofs.GraceSteinerCuts
