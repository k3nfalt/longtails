import LongTails.Proofs.SlidingWireConvex
import LongTails.Proofs.SmoothConvexFiniteHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWirePartial

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireLocal FrontierChainProfiles FrontierChain FrontierChainGeometry
open SmoothConvexFiniteGeometry SmoothConvexFiniteWall
open Classical

variable {d k : ℕ}

noncomputable def pobj (r : ℕ) (δ : ℝ) (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d) : ℝ :=
  (if 0 < V then -potential (u (π 0)) else 0) +
    ∑ i : Fin k, if i.val + 1 < V then link r δ i.val (u (π i.castSucc)) (u (π i.succ)) else 0

noncomputable def pfield (r : ℕ) (δ : ℝ) (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d) :
    Point d :=
  (if 0 < V then -(potentialSlope (u (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) else 0) +
    ∑ i : Fin k, if i.val + 1 < V then lfield r δ i.val (π i.castSucc) (π i.succ) u else 0

def Good (θ : ℝ) (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d) : Prop :=
  ∀ j : Fin (k + 1), V ≤ j.val → |u (π j)| ≤ θ

lemma pobj_congr (r : ℕ) (δ : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d)
    (h : ∀ j : Fin (k + 1), j.val < V → π j = ρ j) : pobj r δ π V u = pobj r δ ρ V u := by
  unfold pobj
  congr 1
  · split_ifs with hV
    · rw [h 0 hV]
    · rfl
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [h i.castSucc (by simp; omega), h i.succ (by simp; omega)]
    · rfl

lemma pfield_congr (r : ℕ) (δ : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d)
    (h : ∀ j : Fin (k + 1), j.val < V → π j = ρ j) : pfield r δ π V u = pfield r δ ρ V u := by
  unfold pfield
  congr 1
  · split_ifs with hV
    · rw [h 0 hV]
    · rfl
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [h i.castSucc (by simp; omega), h i.succ (by simp; omega)]
    · rfl

lemma link_flat (r : ℕ) {δ θ : ℝ} (hθ : 2 * ((r : ℝ) ^ 2 + 7) * θ ≤ δ)
    (hθ2 : θ ≤ 1 / 2) (l : ℕ) {s t : ℝ} (hs : |s| ≤ θ) (ht : |t| ≤ θ) :
    link r δ l s t = 0 ∧ linkL r δ l s t = 0 ∧ linkR r δ l s t = 0 := by
  unfold link linkL linkR
  split_ifs
  · exact edge_flat (by linarith)
  · have hc := coef_bounds r l
    have he : |stretch r l s t| ≤ δ := by
      unfold stretch
      calc _ ≤ |cA r l * s| + |cB r l * t| := abs_add_le _ _
        _ = |cA r l| * |s| + |cB r l| * |t| := by rw [abs_mul, abs_mul]
        _ ≤ ((r : ℝ) ^ 2 + 7) * θ + ((r : ℝ) ^ 2 + 7) * θ := by
            gcongr
            · exact hc.1
            · exact hc.2
        _ ≤ δ := by linarith
    have := sp_flat he
    simp [this.1, this.2]

lemma partial_eq (r : ℕ) {δ θ : ℝ} (hθ : 2 * ((r : ℝ) ^ 2 + 7) * θ ≤ δ)
    (hθ2 : θ ≤ 1 / 2) (π : Fin (k + 1) ↪ Fin d) (V V' : ℕ) (u : Point d) (hV0 : 0 < V')
    (hcond : ∀ i : ℕ, i < k → V' ≤ i + 1 → V ≤ i) (hg : Good θ π V u) :
    pobj r δ π V' u = obj r δ π u ∧ pfield r δ π V' u = field r δ π u := by
  have hflat : ∀ i : Fin k, ¬ (i.val + 1 < V') →
      link r δ i.val (u (π i.castSucc)) (u (π i.succ)) = 0 ∧
        lfield r δ i.val (π i.castSucc) (π i.succ) u = 0 := by
    intro i hi
    have hVi := hcond i.val i.isLt (by omega)
    have h1 := hg i.castSucc (by simp; omega)
    have h2 := hg i.succ (by simp; omega)
    have hf := link_flat r hθ hθ2 i.val h1 h2
    refine ⟨hf.1, ?_⟩
    unfold lfield
    rw [hf.2.1, hf.2.2]
    simp
  constructor
  · unfold pobj obj
    rw [ite_eq_left hV0]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · exact (hflat i hi).1.symm
  · unfold pfield SlidingWireChain.field
    rw [ite_eq_left hV0]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · exact (hflat i hi).2.symm

end LongTails.Proofs.SlidingWirePartial
