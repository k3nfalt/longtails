import LongTails.Proofs.LocalizedClippedExecution
import LongTails.Proofs.LocalizedClippedDrift

open MeasureTheory OracleTemplate OracleTemplate.ContinuizedSimilarQuasar
open LongTails.Setups.TerminalClippingConvex
open LongTails.Algorithms.LocalizedClippedSubgradient
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.LocalizedClippedSubgradient

variable {Ω : Type}

noncomputable def path (p : Public) (g : Vector p.d → Ω → Vector p.d)
    (proj : Vector p.d → Vector p.d) (ξ : ℕ → Ω) : ℕ → Vector p.d
  | 0 => p.x0
  | n+1 => next p g proj (path p g proj ξ n) (ξ n)

lemma path_good (p : Public) (g : Vector p.d → Ω → Vector p.d) (proj : Vector p.d → Vector p.d)
    (ξ : ℕ → Ω) {X : Set (Vector p.d)} (hR : 0 ≤ p.R) (hx0 : p.x0 ∈ X)
    (hpX : ∀ y, proj y ∈ X) (hp : ∀ y, ∀ u ∈ X, ⟪y - proj y, u - proj y⟫ ≤ 0) (n : ℕ) :
    path p g proj ξ n ∈ X ∧ ‖path p g proj ξ n - p.x0‖ ≤ p.R := by
  cases n with
  | zero => exact ⟨hx0, by simpa [path] using hR⟩
  | succ k =>
    refine ⟨hpX _, ?_⟩
    apply le_trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (TerminalClipping.projection_distance (hp _ _ hx0)))
    exact localize_radius p hR _

lemma iterate_path (p : Public) (g : Vector p.d → Ω → Vector p.d) (proj : Vector p.d → Vector p.d)
    (ξ : ℕ → Ω) (n : ℕ) :
    iterateSamples (transition p g proj) n (p.x0, 0) (fun i => ξ i) =
      (path p g proj ξ n, ∑ i ∈ Finset.range n, path p g proj ξ i) := by
  induction n with
  | zero => simp [iterateSamples, path]
  | succ n ih =>
    rw [GapStrongGrowth.iterateSamples_succ_last]
    simp only [Fin.val_castSucc, ih, Fin.val_last, transition, Finset.sum_range_succ, path]

lemma stopped_path (p : Public) (g : Vector p.d → Ω → Vector p.d) (proj : Vector p.d → Vector p.d)
    (ξ : ℕ → Ω) (F : Vector p.d → ℝ) (good : Vector p.d → Prop)
    (hpath : ∀ i, good (path p g proj ξ i)) (n : ℕ) :
    iterateSamples (TerminalClipping.stopUnless (fun s : Vector p.d × ℝ => good s.1)
      (fun s ω => (next p g proj s.1 ω, s.2 + F s.1))) n (p.x0, 0) (fun i => ξ i) =
      (path p g proj ξ n, ∑ i ∈ Finset.range n, F (path p g proj ξ i)) := by
  classical
  induction n with
  | zero => simp [iterateSamples, path]
  | succ n ih =>
    rw [GapStrongGrowth.iterateSamples_succ_last]
    simp only [Fin.val_castSucc, ih, Fin.val_last, TerminalClipping.stopUnless, hpath,
      ↓reduceIte, Finset.sum_range_succ, path]

lemma average_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} {f : E → ℝ} (hf : ConvexOn ℝ X f) {n : ℕ} (hn : 0 < n)
    (x : ℕ → E) (hx : ∀ i, x i ∈ X) (u : E) :
    let a := ((n : ℝ)⁻¹) • ∑ i ∈ Finset.range n, x i
    a ∈ X ∧ n * (f a - f u) ≤ ∑ i ∈ Finset.range n, (f (x i) - f u) := by
  classical
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : ∑ _i ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by simp [hn.ne']
  have hm := hf.1.sum_mem (fun _ _ => inv_nonneg.mpr hnr.le) hw (fun i _ => hx i)
  have hj := hf.map_sum_le (fun _ _ => inv_nonneg.mpr hnr.le) hw (fun i _ => hx i)
  rw [← Finset.smul_sum] at hm hj
  refine ⟨hm, ?_⟩
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    _ = n * f (((n : ℝ)⁻¹) • ∑ i ∈ Finset.range n, x i) - n * f u := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hj hnr.le
      rwa [← mul_assoc, mul_inv_cancel₀ hnr.ne', one_mul, ← sub_le_sub_iff_right (n * f u)] at hh

end LongTails.Proofs.LocalizedClippedSubgradient
