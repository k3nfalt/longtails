import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic

namespace LongTails.Proofs.GraceFractionalPacking

lemma packing_of_price_bound {E T : Type*} [Fintype E] [Fintype T]
    (load : T → E → ℝ) (capacity : E → ℝ)
    (hprice : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ t, ∑ e, load t e * c e ≤ ∑ e, capacity e * c e) :
    ∃ (m : ℕ+) (trees : Fin m → T) (w : Fin m → ℝ), m ≤ Fintype.card E + 1 ∧
      (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∀ e, ∑ i, w i * load (trees i) e ≤ capacity e := by
  classical
  let K := convexHull ℝ (Set.range load)
  have hit : ¬ Disjoint (Set.Iic capacity) K := by
    intro hdis
    obtain ⟨f, u, v, hu, huv, hv⟩ := geometric_hahn_banach_closed_compact
      (convex_Iic (𝕜 := ℝ) capacity) isClosed_Iic (convex_convexHull ℝ _)
      ((Set.finite_range load).isCompact_convexHull ℝ) hdis
    let c (e : E) := f (Pi.single e (1 : ℝ))
    have hb := hu capacity (le_refl capacity)
    have hnon (e : E) : 0 ≤ c e := by
      by_contra! he
      let a := (u - f capacity + 1) / (-c e)
      have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (by linarith) (by linarith)
      have hx : capacity - a • Pi.single e (1 : ℝ) ∈ Set.Iic capacity := by
        intro j
        by_cases hj : e = j
        · subst j; simpa using sub_le_self (capacity e) ha
        · simp [Pi.single_eq_of_ne (Ne.symm hj)]
      have h := hu _ hx
      rw [map_sub, map_smul, smul_eq_mul] at h
      change f capacity - a * c e < u at h
      have heq : a * (-c e) = u - f capacity + 1 := div_mul_cancel₀ _ (by linarith)
      linarith
    have eval (x : E → ℝ) : f x = ∑ e, x e * c e := by
      conv_lhs => arg 2; rw [pi_eq_sum_univ' x]
      simp [c, map_sum]
    obtain ⟨t, ht⟩ := hprice c hnon
    have h := hv (load t) (subset_convexHull ℝ _ (Set.mem_range_self t))
    rw [← eval, ← eval] at ht
    linarith
  obtain ⟨x, hx, hK⟩ := Set.not_disjoint_iff.mp hit
  unfold K at hK
  obtain ⟨ι, hι, z, w, hz, hind, hpos, hone, hmean⟩ := eq_pos_convex_span_of_mem_convexHull hK
  have : Nonempty ι := by
    by_contra! h
    simp at hone
  let m : ℕ+ := ⟨Fintype.card ι, Fintype.card_pos⟩
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  choose trees hrep using fun i => hz (Set.mem_range_self i)
  refine ⟨m, fun j => trees (e j), fun j => w (e j), ?_, fun j => hpos _, ?_, ?_⟩
  · change Fintype.card ι ≤ Fintype.card E + 1
    rw [← hind.finrank_vectorSpan_add_one]
    apply Nat.add_le_add_right
    simpa using Submodule.finrank_le (vectorSpan ℝ (Set.range z))
  · exact (e.sum_comp w).trans hone
  · intro a
    rw [e.sum_comp (fun i => w i * load (trees i) a)]
    simp only [hrep]
    have hm := congrFun hmean a
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm.le.trans (hx a)

end LongTails.Proofs.GraceFractionalPacking
