import LongTails.Proofs.GradientDiversityProfile
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace LongTails.Proofs.StrongGrowthAlignment

open LongTails.Setups.DistributedGradientDiversity LongTails.Algorithms.GradientDiversityDesign

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma alignment {p : Params} (hp : spec.valid p) (v : Fin p.n → E) (g : E)
    (hmean : ∑ i, v i = (p.n : ℝ) • g)
    (hg : ∑ i, ‖v i‖ ^ 2 ≤ (p.n : ℝ) * p.ρ * ‖g‖ ^ 2) :
    information p * ‖g‖ ^ 2 ≤ ⟪∑ i, weight p i • v i, g⟫ := by
  by_cases hz : g = 0
  · simp [hz]
  let z := fun i => ⟪v i, g⟫ / ‖g‖^2
  have hpos := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hs : ∑ i, z i = (p.n : ℝ) := by
    unfold z
    rw [← Finset.sum_div, ← sum_inner, hmean, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [hpos.ne']
  have hb : ∑ i, z i ^ 2 ≤ (p.n : ℝ) * p.ρ := by
    have h (i : Fin p.n) : z i ^ 2 ≤ ‖v i‖ ^ 2 / ‖g‖ ^ 2 := by
      have hi := mul_self_le_mul_self (abs_nonneg _) (abs_real_inner_le_norm (v i) g)
      rw [← sq, sq_abs] at hi
      unfold z
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hpos) hpos]
      nlinarith only [mul_le_mul_of_nonneg_right hi hpos.le]
    have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => h i
    rw [← Finset.sum_div] at hh
    exact hh.trans ((div_le_iff₀ hpos).mpr hg)
  have h := (GradientDiversityProfile.support hp z hs hb)
  simp only [z, mul_div_assoc', ← Finset.sum_div] at h
  rw [sum_inner]
  simp only [real_inner_smul_left]
  exact (le_div_iff₀ hpos).mp h

lemma individual_bound {p : Params} (hp : spec.valid p) (v : Fin p.n → E) (g : E)
    (hmean : ∑ i, v i = (p.n : ℝ) • g)
    (hg : ∑ i, ‖v i‖ ^ 2 ≤ (p.n : ℝ) * p.ρ * ‖g‖ ^ 2) (i : Fin p.n) :
    ‖v i‖ ≤ (1 + Real.sqrt (p.n * (p.ρ - 1))) * ‖g‖ := by
  have hs : ∑ j, ‖v j - g‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 - p.n * ‖g‖ ^ 2 := by
    simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← sum_inner, hmean, real_inner_smul_left, real_inner_self_eq_norm_sq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hb := Finset.single_le_sum (fun j _ => sq_nonneg ‖v j - g‖) (Finset.mem_univ i)
  rw [hs] at hb
  have hρ := sub_nonneg.mpr hp.2.2.2.1
  have hsq := Real.sq_sqrt (mul_nonneg (show 0 ≤ (p.n : ℝ) by positivity) hρ)
  have h : ‖v i - g‖ ≤ Real.sqrt (p.n * (p.ρ - 1)) * ‖g‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, hsq]
    nlinarith only [hb, hg]
  linarith only [h, norm_le_norm_sub_add (v i) g]

lemma gradient_sq_of_upper {F : E → ℝ} {v : E → E} {B : ℝ} (hB : 0 < B)
    (hu : ∀ x y, F y ≤ F x + ⟪v x, y-x⟫ + B/2 * ‖y-x‖^2)
    {z : E} (hz : ∀ y, F z ≤ F y) (x : E) :
    ‖v x‖^2 ≤ 2*B*(F x - F z) := by
  let y := x - B⁻¹ • v x
  have he : y - x = -B⁻¹ • v x := by dsimp [y]; module
  have h := (hz y).trans (hu x y)
  rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_pos (inv_pos.mpr hB)] at h
  field_simp [hB.ne',hB] at h
  linarith

variable [CompleteSpace E]

lemma gap_transfer {F G : E → ℝ} {g v : E → E} {L B I : ℝ} {z : E}
    (hL : 0 < L) (hI : 0 < I)
    (hc : ConvexOn ℝ Set.univ F) (hd : ∀ x, HasGradientAt F (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hu : ∀ x y, G y ≤ G x + ⟪v x, y - x⟫ + B / 2 * ‖y - x‖ ^ 2)
    (ha : ∀ x, I * ‖g x‖ ^ 2 ≤ ⟪v x, g x⟫)
    (hz : ∀ x, G z ≤ G x) (x : E) :
    I / 2 * (F x - F z) ≤ G x - G z := by
  let M := max L (B / I)
  have hM : 0 < M := hL.trans_le (le_max_left _ _)
  have hBM : B ≤ I * M := by
    have h := (div_le_iff₀ hI).mp (show B / I ≤ M from le_max_right _ _)
    linarith
  let T := fun y => y - (1 / M) • g y
  have hstep (y : E) : I / 2 * (F y - F (T y)) ≤ G y - G (T y) := by
    have he : T y - y = -(1 / M) • g y := by dsimp [T]; module
    have hs := OracleTemplate.Gradient.convex_support hc hd y (T y)
    have hy := hu y (T y)
    rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq] at hs
    rw [he, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (one_div_pos.mpr hM)] at hy
    have h1 := mul_le_mul_of_nonneg_left (ha y) (one_div_pos.mpr hM).le
    have h2 := mul_le_mul_of_nonneg_right hBM (sq_nonneg ((1 / M) * ‖g y‖))
    have h3 := mul_le_mul_of_nonneg_left hs hI.le
    field_simp [hM.ne', hM] at hy h1 h2 h3
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hM)).mp
    nlinarith only [hy, h2, mul_le_mul_of_nonneg_right h1 hM.le,
      mul_le_mul_of_nonneg_right h3 (mul_nonneg hM.le hI.le)]
  have htel (k : ℕ) : I / 2 * (F x - F (T^[k] x)) ≤ G x - G (T^[k] x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      linarith only [ih, hstep (T^[k] x)]
  by_contra! hbad
  let e := (I / 2 * (F x - F z) - (G x - G z)) / I
  have he : 0 < e := div_pos (sub_pos.mpr hbad) hI
  let K := max 1 ⌈M * ‖x - z‖ ^ 2 / (2 * e)⌉₊
  have hh := OracleTemplate.Gradient.gd_accuracy F g M ‖x-z‖ e x z hM
    (norm_nonneg _) he hc hd (fun a b => (hl a b).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) le_rfl K le_rfl
  rw [OracleTemplate.Gradient.execute_gd] at hh
  change F (T^[K] x) - F z ≤ e at hh
  have hh' := mul_le_mul_of_nonneg_left hh hI.le
  have heq : I * e = I / 2 * (F x - F z) - (G x - G z) := by dsimp [e]; field_simp
  linarith only [htel K, hz (T^[K] x), hh', heq, hbad]

end LongTails.Proofs.StrongGrowthAlignment
