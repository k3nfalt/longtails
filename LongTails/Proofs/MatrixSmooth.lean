import LongTails.Proofs.MatrixPolarGeometry
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.MatrixSmooth

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Algorithms.MatrixPolar

lemma spectralNorm_smul {m n : ℕ} (t : ℝ) (X : Space m n) :
    spectralNorm (t • X) = |t| * spectralNorm X := by
  simp [spectralNorm, norm_smul, Real.norm_eq_abs]

lemma smooth_upper {m n : ℕ} {f : Space m n → ℝ} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (x y : Space m n) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * spectralNorm (y - x) ^ 2 := by
  let v := y - x
  let F := fun t : ℝ => f (x + t • v)
  let F' := fun t : ℝ => ⟪gradient f (x + t • v), v⟫
  have hF (t : ℝ) : HasDerivAt F (F' t) t := by
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const v |>.const_add x)
    simpa only [F, F', Function.comp_def, id_eq, one_smul, toDual_apply_apply] using h
  let B := fun t : ℝ => f x + t * ⟪gradient f x, v⟫ +
    t ^ 2 * (L / 2 * spectralNorm v ^ 2)
  have hB (t : ℝ) : HasDerivAt B
      (⟪gradient f x, v⟫ + L * spectralNorm v ^ 2 * t) t := by
    convert ((hasDerivAt_id t).mul_const ⟪gradient f x, v⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * spectralNorm v ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1,
      F' t ≤ ⟪gradient f x, v⟫ + L * spectralNorm v ^ 2 * t := by
    intro t ht
    have hp := (le_abs_self ⟪gradient f (x + t • v) - gradient f x, v⟫).trans
      (inner_le_nuclear_mul_spectral _ _)
    have hs := mul_le_mul_of_nonneg_right (hlip (x + t • v) x)
      (show 0 ≤ spectralNorm v from norm_nonneg _)
    simp only [add_sub_cancel_left, spectralNorm_smul, abs_of_nonneg ht.1] at hs
    rw [inner_sub_left] at hp
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, v] using h

lemma polar_descent {m n : ℕ} {f : Space m n → ℝ} {L η : ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hL : 0 ≤ L) (hη : 0 ≤ η) (x M : Space m n) :
    f (x - η • polar M) ≤ f x - η * ⟪gradient f x, polar M⟫ + L / 2 * η ^ 2 := by
  have hs := smooth_upper hg hlip x (x - η • polar M)
  have he : x - η • polar M - x = (-η) • polar M := by module
  rw [he, inner_smul_right, spectralNorm_smul, abs_neg, abs_of_nonneg hη] at hs
  have hp : spectralNorm (polar M) ≤ 1 := polar_mem M
  have hn : 0 ≤ spectralNorm (polar M) := norm_nonneg _
  have hb : (η * spectralNorm (polar M)) ^ 2 ≤ η ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg hη hn) (by nlinarith) 2
  nlinarith [mul_le_mul_of_nonneg_left hb hL]

lemma gradient_self_bound {m n : ℕ} {f : Space m n → ℝ} {L fmin : ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hL : 0 < L) (hmin : ∀ x, fmin ≤ f x) (x : Space m n) :
    nuclearNorm (gradient f x) ^ 2 ≤ 2 * L * (f x - fmin) := by
  have hn : 0 ≤ nuclearNorm (gradient f x) := by unfold nuclearNorm; positivity
  have hd := polar_descent hg hlip hL.le (div_nonneg hn hL.le) x (gradient f x)
  rw [polar_pairing_eq_nuclear] at hd
  have hm := hmin (x - (nuclearNorm (gradient f x) / L) • polar (gradient f x))
  field_simp at hd
  nlinarith

lemma polar_alignment_deficit {m n : ℕ} (G M : Space m n) :
    0 ≤ nuclearNorm G - ⟪G, polar M⟫ ∧
      nuclearNorm G - ⟪G, polar M⟫ ≤ 2 * nuclearNorm G ∧
      nuclearNorm G - ⟪G, polar M⟫ ≤ 2 * nuclearNorm (M - G) := by
  have hab (X Y : Space m n) : |⟪X, polar Y⟫| ≤ nuclearNorm X := by
    exact (inner_le_nuclear_mul_spectral X (polar Y)).trans
      (by simpa using mul_le_mul_of_nonneg_left (polar_mem Y) (nuclearNorm_nonneg X))
  have hgm := abs_le.mp (hab G M)
  have hem := abs_le.mp (hab (M - G) M)
  have ht := nuclearNorm_add_le (G - M) M
  have he : nuclearNorm (G - M) = nuclearNorm (M - G) := by
    rw [← neg_sub M G, nuclearNorm_neg]
  rw [sub_add_cancel, he] at ht
  rw [inner_sub_left, polar_pairing_eq_nuclear] at hem
  constructor
  · linarith [hgm.2]
  constructor
  · linarith [hgm.1]
  · linarith [hem.2]

lemma gradient_self_bound_nonnegative {m n : ℕ} {f : Space m n → ℝ} {L fmin : ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hL : 0 ≤ L) (hmin : ∀ x, fmin ≤ f x) (x : Space m n) :
    nuclearNorm (gradient f x) ^ 2 ≤ 2 * L * (f x - fmin) := by
  rcases hL.eq_or_lt with he | hp
  · subst L
    by_cases hz : nuclearNorm (gradient f x) = 0
    · simp [hz]
    have hq : 0 < nuclearNorm (gradient f x) :=
      lt_of_le_of_ne (nuclearNorm_nonneg _) (Ne.symm hz)
    let η := (f x - fmin + 1) / nuclearNorm (gradient f x)
    have hη : 0 ≤ η := div_nonneg (by linarith [hmin x]) hq.le
    have hd := polar_descent hg hlip le_rfl hη x (gradient f x)
    rw [polar_pairing_eq_nuclear] at hd
    have hm := hmin (x - η • polar (gradient f x))
    have hmul : η * nuclearNorm (gradient f x) = f x - fmin + 1 := by
      exact div_mul_cancel₀ _ hz
    nlinarith
  · exact gradient_self_bound hg hlip hp hmin x

end LongTails.Proofs.MatrixSmooth
