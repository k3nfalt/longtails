import LongTails.Setups.SmoothConvexConcave
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

open scoped BigOperators
open scoped RealInnerProductSpace

namespace OracleTemplate.SaddlePoint

open LongTails.Setups.SmoothConvexConcave

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma convex_support_on {X : Set E} {f : E → ℝ} {v x y : E}
    (hc : ConvexOn ℝ X f) (hx : x ∈ X) (hy : y ∈ X)
    (hg : HasGradientAt f v x) : ⟪v, y - x⟫ ≤ f y - f x := by
  have hconv := hc.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) v)
      ((AffineMap.lineMap x y) (0 : ℝ)) := by simpa using hg.hasFDerivAt
  have hline : HasDerivAt (f ∘ AffineMap.lineMap x y) ⟪v, y - x⟫ (0 : ℝ) := by
    simpa using hd.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have h := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa using hx) (by simpa using hy) (by norm_num) hline
  simpa [slope_def_field] using h

lemma saddle_difference_le {X : Set E} {Y : Set F} {φ : E → F → ℝ}
    (hc : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (ha : ∀ x ∈ X, ConcaveOn ℝ Y (φ x))
    {z u v : E × F} (hz : z ∈ X ×ˢ Y) (hu : u ∈ X ×ˢ Y)
    (hgx : HasGradientAt (fun x => φ x z.2) v.1 z.1)
    (hgy : HasGradientAt (φ z.1) (-v.2) z.2) :
    φ z.1 u.2 - φ u.1 z.2 ≤
      ⟪v.1, z.1 - u.1⟫ + ⟪v.2, z.2 - u.2⟫ := by
  have h1 := convex_support_on (hc z.2 hz.2) hz.1 hu.1 hgx
  have hgneg : HasGradientAt (-φ z.1) v.2 z.2 := by
    simpa [hasGradientAt_iff_hasFDerivAt, map_neg] using hgy.hasFDerivAt.neg
  have h2 := convex_support_on (ha z.1 hz.1).neg hz.2 hu.2 hgneg
  simp only [Pi.neg_apply] at h2
  have hx : ⟪v.1, u.1 - z.1⟫ = -⟪v.1, z.1 - u.1⟫ := by
    rw [← inner_neg_right]
    congr 1
    abel
  have hy : ⟪v.2, u.2 - z.2⟫ = -⟪v.2, z.2 - u.2⟫ := by
    rw [← inner_neg_right]
    congr 1
    abel
  rw [hx] at h1
  rw [hy] at h2
  linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma gap_le_of_pairwise {X : Set E} {Y : Set F} {φ : E → F → ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (z : E × F) (B : ℝ)
    (h : ∀ x ∈ X, ∀ y ∈ Y, φ z.1 y - φ x z.2 ≤ B) :
    gap E F X Y φ z ≤ B := by
  have hi : ∀ y ∈ Y, φ z.1 y - B ≤ sInf ((fun x => φ x z.2) '' X) := by
    intro y hy
    apply le_csInf (hX.image _)
    rintro _ ⟨x, hx, rfl⟩
    linarith [h x hx y hy]
  have hs : sSup ((fun y => φ z.1 y) '' Y) ≤
      B + sInf ((fun x => φ x z.2) '' X) := by
    apply csSup_le (hY.image _)
    rintro _ ⟨y, hy, rfl⟩
    linarith [hi y hy]
  unfold gap
  linarith

omit [CompleteSpace E] in
lemma average_mem {X : Set E} (hX : Convex ℝ X) (x : ℕ → E)
    {n : ℕ} (hn : 0 < n) (hx : ∀ k < n, x k ∈ X) :
    (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x k) ∈ X := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hw : ∑ _k ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by
    simp [hn0]
  simpa only [Finset.smul_sum] using hX.sum_mem
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)) hw
    (fun k hk => hx k (Finset.mem_range.mp hk))

omit [CompleteSpace E] [CompleteSpace F] in
lemma average_gap_le {X : Set E} {Y : Set F} {φ : E → F → ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hc : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (ha : ∀ x ∈ X, ConcaveOn ℝ Y (φ x))
    (z : ℕ → E × F) {n : ℕ} (hn : 0 < n)
    (hz : ∀ k < n, z k ∈ X ×ˢ Y) (B : ℝ)
    (hregret : ∀ x ∈ X, ∀ y ∈ Y,
      (∑ k ∈ Finset.range n, (φ (z k).1 y - φ x (z k).2)) ≤ B) :
    gap E F X Y φ
      ((n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (z k).1),
       (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (z k).2)) ≤ B / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hw : ∑ _k ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by simp [hn0]
  have hw0 : ∀ k ∈ Finset.range n, 0 ≤ (n : ℝ)⁻¹ :=
    fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)
  apply gap_le_of_pairwise hX hY
  intro x hx y hy
  have hcx := (hc y hy).map_sum_le hw0 hw
    (fun k hk => (hz k (Finset.mem_range.mp hk)).1)
  have hay := (ha x hx).le_map_sum hw0 hw
    (fun k hk => (hz k (Finset.mem_range.mp hk)).2)
  simp only [← Finset.smul_sum, smul_eq_mul, ← Finset.mul_sum] at hcx hay
  have hr := mul_le_mul_of_nonneg_left (hregret x hx y hy)
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  rw [Finset.sum_sub_distrib] at hr
  dsimp only
  rw [div_eq_mul_inv]
  nlinarith

lemma average_gap_le_of_regret {X : Set E} {Y : Set F} {φ : E → F → ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hc : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (ha : ∀ x ∈ X, ConcaveOn ℝ Y (φ x))
    (g : E × F → E × F)
    (hg : ∀ z, HasGradientAt (fun x => φ x z.2) (g z).1 z.1 ∧
      HasGradientAt (φ z.1) (-(g z).2) z.2)
    (z : ℕ → E × F) {n : ℕ} (hn : 0 < n)
    (hz : ∀ k < n, z k ∈ X ×ˢ Y) (B : ℝ)
    (hregret : ∀ u ∈ X ×ˢ Y,
      (∑ k ∈ Finset.range n, (⟪(g (z k)).1, (z k).1 - u.1⟫ +
        ⟪(g (z k)).2, (z k).2 - u.2⟫)) ≤ B) :
    gap E F X Y φ ((n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, z k)) ≤ B / n := by
  have hp : (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, z k) =
      ((n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (z k).1),
       (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (z k).2)) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [hp]
  apply average_gap_le hX hY hc ha z hn hz B
  intro x hx y hy
  apply (Finset.sum_le_sum (fun k hk =>
    saddle_difference_le hc ha (hz k (Finset.mem_range.mp hk))
      (show (x, y) ∈ X ×ˢ Y from ⟨hx, hy⟩) (hg (z k)).1 (hg (z k)).2)).trans
  exact hregret (x, y) ⟨hx, hy⟩

end OracleTemplate.SaddlePoint
