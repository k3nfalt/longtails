import LongTails.Proofs.AcceleratedMarkovStep
import LongTails.Proofs.NearZeroSumCalculus
import LongTails.Proofs.NearZeroSumProjection

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.HiddenDecompositionEnergy

open HeavyTailedMarkovGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma bounded_error_step {f : E → ℝ} {L D R b : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x0 x z u g : E) (hz : ‖z - x0‖ ≤ R) (hu : ‖u - x0‖ ≤ R)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a) (haB : a ^ 2 ≤ A + a)
    (he : ‖gradient f ((A / (A + a)) • x + (a / (A + a)) • z) - g‖ ≤ b) :
    let next := x0 + clip R (z - (a / D) • g - x0)
    let out := (A / (A + a)) • x + (a / (A + a)) • next
    (A + a) * (f out - f u) + D / 2 * ‖next - u‖ ^ 2 ≤
      A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2 + 4 * R * a * b := by
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  let e := gradient f y - g
  have he' : ‖e‖ ≤ b := he
  have hzu : ‖z - u‖ ≤ 2 * R := by
    have hh := norm_sub_le_norm_sub_add_norm_sub z x0 u
    rw [norm_sub_rev x0 u] at hh
    linarith
  have hei : ⟪e, z - u⟫ ≤ 2 * R * b := by
    calc
      _ ≤ ‖e‖ * ‖z - u‖ := real_inner_le_norm _ _
      _ ≤ b * (2 * R) := mul_le_mul he' hzu (norm_nonneg _) (le_trans (norm_nonneg _) he')
      _ = _ := by ring
  have hs := accelerated_projected_step hL hD hLD hR
    (p := 2) (by norm_num) (by norm_num) hc hg hlip x0 x z u g hz hu hA ha hB haB
  have hm := min_le_right ((a * ‖e‖) ^ (2 : ℝ) * (2 * R) ^ ((2 : ℝ) - 2) /
    (D / 4) ^ ((2 : ℝ) - 1)) (2 * R * a * ‖e‖)
  have hb := mul_le_mul_of_nonneg_left he' (show 0 ≤ 2 * R * a by positivity)
  have hi := mul_le_mul_of_nonneg_left hei ha
  dsimp only at hs ⊢
  change _ ≤ _ + a * ⟪e, z - u⟫ + _ at hs
  linarith

lemma radius_contraction {μ R d b gap : ℝ} (hμ : 0 < μ) (hR : 0 ≤ R)
    (hd : 0 ≤ d) (hb : b ≤ μ * R / 256)
    (hlower : μ / 2 * d ^ 2 - b * d ≤ gap)
    (hupper : gap ≤ μ * R ^ 2 / 32) :
    d ≤ R / 2 := by
  have he := mul_le_mul_of_nonneg_right hb hd
  have hs : μ * (d ^ 2 / 2) ≤ μ * (R ^ 2 / 32 + R * d / 256) := by
    nlinarith
  have hc := (mul_le_mul_iff_of_pos_left hμ).mp hs
  by_contra h
  have hlt : R / 2 < d := lt_of_not_ge h
  have hprod := mul_nonneg (sub_nonneg.mpr hlt.le) hR
  nlinarith [sq_nonneg (d - R / 2)]

omit [CompleteSpace E] in
lemma regularized_curvature (F G S : E → E) (μ β s : ℝ)
    (hdecomp : ∀ x, F x = G x + S x)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hresidual : ∀ x y, ‖S x - S y‖ ≤ s * ‖x - y‖)
    (a x y : E) :
    (μ + β - s) * ‖x - y‖ ^ 2 ≤
      ⟪(G x + β • (x - a)) - (G y + β • (y - a)), x - y⟫ := by
  have he : ⟪S x - S y, x - y⟫ ≤ s * ‖x - y‖ ^ 2 := by
    calc
      _ ≤ ‖S x - S y‖ * ‖x - y‖ := real_inner_le_norm _ _
      _ ≤ (s * ‖x - y‖) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (hresidual x y) (norm_nonneg _)
      _ = _ := by ring
  have hf := hstrong x y
  rw [hdecomp x, hdecomp y] at hf
  have hid : (G x + β • (x - a)) - (G y + β • (y - a)) =
      (G x - G y) + β • (x - y) := by module
  rw [hid, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_add_left] at hf he ⊢
  nlinarith

lemma strongly_monotone_gradient_support {f : E → ℝ} {G : E → E} {m : ℝ}
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫) (x y : E) :
    f x + ⟪G x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let F' := fun t : ℝ => ⟪G (x + t • d), d⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    simp only [id_eq, one_smul, InnerProductSpace.toDual_apply_apply] at h
    exact h
  let B := fun t : ℝ => f x + t * ⟪G x, d⟫ + t ^ 2 * (m / 2 * ‖d‖ ^ 2)
  have hB : ∀ t, HasDerivAt B (⟪G x, d⟫ + m * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪G x, d⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (m / 2 * ‖d‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, ⟪G x, d⟫ + m * ‖d‖ ^ 2 * t ≤ F' t := by
    intro t ht
    by_cases hz : t = 0
    · subst t
      simp [F']
    have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    have h := hm (x + t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, inner_smul_right, inner_sub_left, mul_pow] at h
    have hh : t * (m * ‖d‖ ^ 2 * t) ≤ t * (⟪G (x + t • d), d⟫ - ⟪G x, d⟫) := by
      nlinarith [h]
    have := (mul_le_mul_iff_of_pos_left hpos).mp hh
    dsimp [F']
    linarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (show B 0 ≤ F 0 by simp [F, B])
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

omit [CompleteSpace E] in
lemma convex_of_gradient_support {f : E → ℝ} {G : E → E}
    (hs : ∀ x y, f x + ⟪G x, y - x⟫ ≤ f y) :
    ConvexOn ℝ univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hs z x) ha
  have hy := mul_le_mul_of_nonneg_left (hs z y) hb
  have hz : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = a • x + b • y - (a + b) • z := by module
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi : a * ⟪G z, x - z⟫ + b * ⟪G z, y - z⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hz, inner_zero_right]
  change f z ≤ a * f x + b * f y
  have he : a * f z + b * f z = f z := by rw [← add_mul, hab, one_mul]
  linarith

lemma strongly_monotone_gradient_convex {f : E → ℝ} {G : E → E} {m : ℝ}
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hm : ∀ x y, m * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    (hm0 : 0 ≤ m) :
    ConvexOn ℝ univ f := by
  apply convex_of_gradient_support (G := G)
  intro x y
  have h := strongly_monotone_gradient_support hg hm x y
  have hn : 0 ≤ m / 2 * ‖y - x‖ ^ 2 := by positivity
  linarith

lemma regularized_potential_gradient {φ : E → ℝ} {G : E → E}
    (hg : ∀ x, HasGradientAt φ (G x) x) (β : ℝ) (anchor v x : E) :
    HasGradientAt (fun y => φ y + β / 2 * ‖y - anchor‖ ^ 2 + ⟪v, y⟫)
      (G x + β • (x - anchor) + v) x := by
  have hq := hasGradientWithinAt_univ.mp
    (NearZeroSum.gradient_translated_quadratic β anchor x univ)
  have hv : HasFDerivAt (fun y => ⟪v, y⟫) (InnerProductSpace.toDual ℝ E v) x :=
    (InnerProductSpace.toDual ℝ E v).hasFDerivAt
  change HasFDerivAt _ (InnerProductSpace.toDual ℝ E (G x + β • (x - anchor) + v)) x
  convert (hg x).hasFDerivAt.add hq.hasFDerivAt |>.add hv using 1
  simp [map_add]

omit [CompleteSpace E] in
lemma proximal_root_distance (F : E → E) {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (anchor u xstar : E) (hu : F u + β • (u - anchor) = 0) (hx : F xstar = 0) :
    ‖u - xstar‖ ≤ β / (μ + β) * ‖anchor - xstar‖ := by
  have hm : 0 < μ + β := by positivity
  have hf : F u = β • (anchor - u) := by
    have he := eq_neg_of_add_eq_zero_left hu
    rw [he]
    module
  have h := hstrong u xstar
  rw [hx, sub_zero, hf, real_inner_smul_left] at h
  have he : anchor - u = (anchor - xstar) - (u - xstar) := by abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq] at h
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm (anchor - xstar) (u - xstar)) hβ
  by_cases hz : ‖u - xstar‖ = 0
  · rw [hz]
    positivity
  have hd : 0 < ‖u - xstar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hh : (μ + β) * ‖u - xstar‖ ≤ β * ‖anchor - xstar‖ := by
    apply (mul_le_mul_iff_of_pos_right hd).mp
    nlinarith
  have hr : ‖u - xstar‖ ≤ β * ‖anchor - xstar‖ / (μ + β) :=
    (le_div_iff₀ hm).mpr (by nlinarith [hh])
  simpa only [div_mul_eq_mul_div] using hr

omit [CompleteSpace E] in
lemma proximal_displacement (F : E → E) {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (anchor u xstar : E) (hu : F u + β • (u - anchor) = 0) (hx : F xstar = 0) :
    ‖u - anchor‖ ≤ ‖anchor - xstar‖ := by
  by_cases hz : β = 0
  · have h := proximal_root_distance F hμ hβ hstrong anchor u xstar hu hx
    simp only [hz, zero_div, zero_mul] at h
    have he : u = xstar := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    rw [he, norm_sub_rev]
  have hb : 0 < β := lt_of_le_of_ne hβ (Ne.symm hz)
  have hf : F u = β • (anchor - u) := by
    rw [eq_neg_of_add_eq_zero_left hu]
    module
  have h := hstrong u xstar
  rw [hx, sub_zero, hf, real_inner_smul_left] at h
  have hi : 0 ≤ ⟪anchor - u, u - xstar⟫ := by
    have hh : 0 ≤ β * ⟪anchor - u, u - xstar⟫ :=
      (mul_nonneg hμ.le (sq_nonneg _)).trans h
    exact (mul_nonneg_iff_of_pos_left hb).mp hh
  have he : anchor - xstar = (anchor - u) + (u - xstar) := by abel
  have hn : ‖anchor - xstar‖ ^ 2 =
      ‖anchor - u‖ ^ 2 + 2 * ⟪anchor - u, u - xstar⟫ + ‖u - xstar‖ ^ 2 := by
    rw [he, norm_add_sq_real]
  rw [norm_sub_rev u anchor]
  nlinarith [norm_nonneg (anchor - u), norm_nonneg (anchor - xstar), sq_nonneg ‖u - xstar‖]

lemma strongly_monotone_root_exists (F : E → E) {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) :
    ∃ u, F u = 0 := by
  have hP : ConstrainedMonotone.Proj (univ : Set E) id := by
    constructor
    · simp
    · intro z w _
      simp
  obtain ⟨u, _, hu⟩ := NearZeroSum.strongly_monotone_vi_exists
    (C := univ) (P := id) (A := F) (ρ := μ) (L := μ + L)
    isComplete_univ (Set.univ_nonempty) hP hμ (by linarith)
    (by intro x _ y _; exact hstrong x y)
    (by
      intro x _ y _
      exact (hlip x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
  have h := hu (u - F u) (mem_univ _)
  have he : u - F u - u = -F u := by abel
  rw [he, real_inner_self_eq_norm_sq, norm_neg] at h
  exact ⟨u, norm_eq_zero.mp (by nlinarith [norm_nonneg (F u)])⟩

lemma regularized_root_exists (F : E → E) {μ L β : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (anchor : E) :
    ∃ u, F u + β • (u - anchor) = 0 := by
  apply strongly_monotone_root_exists (μ := μ + β) (L := L + β) _
    (by positivity) (add_nonneg hL hβ)
  · intro x y
    have he : (F x + β • (x - anchor)) - (F y + β • (y - anchor)) =
        (F x - F y) + β • (x - y) := by module
    rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [hstrong x y]
  · intro x y
    have he : (F x + β • (x - anchor)) - (F y + β • (y - anchor)) =
        (F x - F y) + β • (x - y) := by module
    rw [he]
    have hn := norm_add_le (F x - F y) (β • (x - y))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ] at hn
    nlinarith [hlip x y]

end OracleTemplate.HiddenDecompositionEnergy
