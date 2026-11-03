import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open scoped NNReal RealInnerProductSpace

namespace LongTails.Proofs.TailObliviousAnchoring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma anchored_inverse_bound (F : E → E) (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (a : ℝ) (b x u : E) (hu : F u + a • u - b = 0) :
    a * ‖x - u‖ ≤ ‖F x + a • x - b‖ := by
  have hid : F x + a • x - b = (F x - F u) + a • (x - u) := by
    have hb : b = F u + a • u := (sub_eq_zero.mp hu).symm
    rw [hb, smul_sub]
    abel
  have hin : a * ‖x - u‖ ^ 2 ≤ ⟪F x + a • x - b, x - u⟫ := by
    rw [hid, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    linarith [hF x u]
  have hcs := real_inner_le_norm (F x + a • x - b) (x - u)
  rcases (norm_nonneg (x - u)).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have : a * ‖x - u‖ * ‖x - u‖ ≤ ‖F x + a • x - b‖ * ‖x - u‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma anchored_roots_bound (F : E → E) (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (a : ℝ) (b c u v : E) (hu : F u + a • u - b = 0)
    (hv : F v + a • v - c = 0) :
    a * ‖u - v‖ ≤ ‖b - c‖ := by
  have hb : F u + a • u = b := sub_eq_zero.mp hu
  simpa only [hb] using anchored_inverse_bound F hF a c u v hv

lemma doubled_anchor_root_movement (F : E → E) (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (a : ℝ) (ha : 0 < a) (b z u v : E) (hu : F u + a • u - b = 0)
    (hv : F v + (2 * a) • v - (b + a • z) = 0) :
    ‖u - v‖ ≤ ‖z - u‖ / 2 := by
  have hid : F u + (2 * a) • u - (b + a • z) = a • (u - z) := by
    have hb : F u + a • u = b := sub_eq_zero.mp hu
    rw [← hb]
    module
  have h := anchored_inverse_bound F hF (2 * a) (b + a • z) u v hv
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_sub_rev u z] at h
  nlinarith

lemma regularized_contraction (F : E → E) (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (L : ℝ) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (a : ℝ) (ha : 0 < a) (hL0 : 0 ≤ L)
    (b x y : E) :
    ‖(x - (a / (L + a) ^ 2) • (F x + a • x - b)) -
      (y - (a / (L + a) ^ 2) • (F y + a • y - b))‖ ^ 2 ≤
      (1 - (a / (L + a)) ^ 2) * ‖x - y‖ ^ 2 := by
  set γ := a / (L + a) ^ 2 with hγ
  have hLa : 0 < L + a := by linarith
  have hid : (x - γ • (F x + a • x - b)) - (y - γ • (F y + a • y - b)) =
      (x - y) - γ • ((F x - F y) + a • (x - y)) := by
    simp only [smul_sub, smul_add]
    abel
  rw [hid, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ γ)]
  have hinner : ⟪x - y, (F x - F y) + a • (x - y)⟫ ≥ a * ‖x - y‖ ^ 2 := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
    linarith [hF x y]
  have hnorm : ‖(F x - F y) + a • (x - y)‖ ≤ (L + a) * ‖x - y‖ := by
    calc _ ≤ ‖F x - F y‖ + ‖a • (x - y)‖ := norm_add_le _ _
      _ ≤ L * ‖x - y‖ + a * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        linarith [hL x y]
      _ = _ := by ring
  have hn2 : ‖(F x - F y) + a • (x - y)‖ ^ 2 ≤ (L + a) ^ 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rwa [mul_pow] at this
  have hγ0 : 0 ≤ γ := by positivity
  have hγL : γ * (L + a) ^ 2 = a := by
    rw [hγ]; field_simp
  have hθ : (a / (L + a)) ^ 2 = γ * a := by
    rw [hγ]; field_simp
  rw [hθ]
  nlinarith [mul_le_mul_of_nonneg_left hn2 (sq_nonneg γ),
    mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ 2 * γ)]

lemma exists_anchored_root [CompleteSpace E] (F : E → E)
    (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (L : ℝ) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L)
    (a : ℝ) (ha : 0 < a) (b : E) :
    ∃ u, F u + a • u - b = 0 := by
  set γ := a / (L + a) ^ 2 with hγ
  have hLa : 0 < L + a := by linarith
  have hθ0 : 0 ≤ 1 - (a / (L + a)) ^ 2 := by
    have h1 : a / (L + a) ≤ 1 := (div_le_one hLa).mpr (by linarith)
    have h0 : 0 ≤ a / (L + a) := by positivity
    nlinarith
  have hθ1 : 1 - (a / (L + a)) ^ 2 < 1 := by
    have : 0 < a / (L + a) := by positivity
    nlinarith
  let k : ℝ≥0 := ⟨Real.sqrt (1 - (a / (L + a)) ^ 2), Real.sqrt_nonneg _⟩
  let f : E → E := fun x => x - γ • (F x + a • x - b)
  have hk : k < 1 := by
    change Real.sqrt (1 - (a / (L + a)) ^ 2) < 1
    rw [Real.sqrt_lt' one_pos]
    simpa using hθ1
  have hf : ContractingWith k f := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖f x - f y‖ ≤ Real.sqrt (1 - (a / (L + a)) ^ 2) * ‖x - y‖
    have h := regularized_contraction F hF L hL a ha hL0 b x y
    have hs : ‖f x - f y‖ ≤ Real.sqrt ((1 - (a / (L + a)) ^ 2) * ‖x - y‖ ^ 2) :=
      Real.le_sqrt_of_sq_le h
    rwa [Real.sqrt_mul hθ0, Real.sqrt_sq (norm_nonneg _)] at hs
  let u := hf.fixedPoint f
  have hu : f u = u := hf.fixedPoint_isFixedPt
  have hγp : 0 < γ := by positivity
  refine ⟨u, ?_⟩
  have h0 : γ • (F u + a • u - b) = 0 := by
    have := congrArg (fun z => u - z) hu
    simp only [f, sub_sub_cancel, sub_self] at this
    exact this
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd h hγp.ne'
  · exact h

noncomputable def anchoredRoot [CompleteSpace E] (F : E → E)
    (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (L : ℝ) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L)
    (a : ℝ) (ha : 0 < a) (b : E) : E :=
  Classical.choose (exists_anchored_root F hF L hL hL0 a ha b)

lemma anchoredRoot_equation [CompleteSpace E] (F : E → E)
    (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (L : ℝ) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L)
    (a : ℝ) (ha : 0 < a) (b : E) :
    F (anchoredRoot F hF L hL hL0 a ha b) + a • anchoredRoot F hF L hL hL0 a ha b - b = 0 :=
  Classical.choose_spec (exists_anchored_root F hF L hL hL0 a ha b)

lemma anchoredRoot_lipschitz [CompleteSpace E] (F : E → E)
    (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (L : ℝ) (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L)
    (a : ℝ) (ha : 0 < a) :
    LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ (anchoredRoot F hF L hL hL0 a ha) := by
  apply LipschitzWith.of_dist_le_mul
  intro b c
  simp only [dist_eq_norm]
  have h := anchored_roots_bound F hF a b c
    (anchoredRoot F hF L hL hL0 a ha b) (anchoredRoot F hF L hL hL0 a ha c)
    (anchoredRoot_equation F hF L hL hL0 a ha b) (anchoredRoot_equation F hF L hL hL0 a ha c)
  change ‖anchoredRoot F hF L hL hL0 a ha b - anchoredRoot F hF L hL hL0 a ha c‖ ≤
    a⁻¹ * ‖b - c‖
  rw [← div_eq_inv_mul, le_div_iff₀ ha]
  nlinarith

lemma initial_root_distance (F : E → E) (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (a R : ℝ) (ha : 0 < a) (x0 xstar u : E) (hstar : F xstar = 0) (hR : ‖x0 - xstar‖ ≤ R)
    (hu : F u + a • u - a • x0 = 0) : ‖u - x0‖ ≤ 2 * R := by
  have hid : F xstar + a • xstar - a • x0 = a • (xstar - x0) := by
    rw [hstar]
    module
  have h := anchored_inverse_bound F hF a (a • x0) xstar u hu
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h
  have hd : ‖xstar - u‖ ≤ ‖xstar - x0‖ := (mul_le_mul_iff_right₀ ha).mp h
  have ht := norm_sub_le_norm_sub_add_norm_sub u xstar x0
  rw [norm_sub_rev u xstar] at ht
  rw [norm_sub_rev xstar x0] at hd ht
  linarith

lemma remove_initial_anchor (F : E → E) (hF : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (a R : ℝ) (ha : 0 ≤ a) (x0 u x : E) (hu : F u + a • u - a • x0 = 0)
    (hR : ‖u - x0‖ ≤ 2 * R) :
    ‖F x‖ ≤ 2 * ‖F x + a • x - a • x0‖ + 2 * a * R := by
  have hid : F x = (F x + a • x - a • x0) - a • (x - x0) := by
    module
  have hn := norm_sub_le (F x + a • x - a • x0) (a • (x - x0))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at hn
  rw [← hid] at hn
  have ht := norm_sub_le_norm_sub_add_norm_sub x u x0
  have hi := anchored_inverse_bound F hF a (a • x0) x u hu
  nlinarith [mul_le_mul_of_nonneg_left ht ha, mul_le_mul_of_nonneg_left hR ha]

omit [InnerProductSpace ℝ E] in
lemma correction_step_bound [NormedSpace ℝ E] (a a0 : ℝ) (ha0 : 0 ≤ a0) (ha : a0 ≤ a)
    (b b0 u v z : E) (hm : ‖u - v‖ ≤ ‖z - u‖ / 2) :
    ‖(2 * a - a0) • v - (b + a • z - b0)‖ ≤
      ‖(a - a0) • u - (b - b0)‖ + 2 * a * ‖z - u‖ := by
  have hid : (2 * a - a0) • v - (b + a • z - b0) =
      ((a - a0) • u - (b - b0)) +
        (2 * a - a0) • (v - u) + a • (u - z) := by module
  rw [hid]
  have hnorm := (norm_add_le (((a - a0) • u - (b - b0)) +
    (2 * a - a0) • (v - u)) (a • (u - z))).trans
    (add_le_add (norm_add_le ((a - a0) • u - (b - b0))
      ((2 * a - a0) • (v - u))) (le_refl _))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 2 * a - a0), abs_of_nonneg (by linarith : 0 ≤ a),
    norm_sub_rev v u, norm_sub_rev u z] at hnorm
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 2 * a - a0)
  nlinarith [mul_nonneg ha0 (norm_nonneg (z - u))]

omit [InnerProductSpace ℝ E] in
lemma correction_sum_bound [NormedSpace ℝ E] (a : ℕ → ℝ) (b u z : ℕ → E)
    (ha0 : 0 ≤ a 0) (ha : ∀ j, a 0 ≤ a j)
    (had : ∀ j, a (j + 1) = 2 * a j)
    (hb : ∀ j, b (j + 1) = b j + a j • z j)
    (hm : ∀ j, ‖u j - u (j + 1)‖ ≤ ‖z j - u j‖ / 2) (n : ℕ) :
    ‖(a n - a 0) • u n - (b n - b 0)‖ ≤
      2 * ∑ j ∈ Finset.range n, a j * ‖z j - u j‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [had, hb]
    calc
      _ ≤ ‖(a n - a 0) • u n - (b n - b 0)‖ + 2 * a n * ‖z n - u n‖ :=
        correction_step_bound (a n) (a 0) ha0 (ha n) (b n) (b 0) (u n) (u (n + 1)) (z n) (hm n)
      _ ≤ 2 * ∑ j ∈ Finset.range n, a j * ‖z j - u j‖ + 2 * a n * ‖z n - u n‖ :=
        add_le_add ih (le_refl _)
      _ = _ := by rw [Finset.sum_range_succ]; ring

omit [InnerProductSpace ℝ E] in
lemma anchored_residual_lipschitz [NormedSpace ℝ E] (F : E → E) (L : ℝ)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (a : ℝ) (ha : 0 ≤ a) (b x y : E) :
    ‖(F x + a • x - b) - (F y + a • y - b)‖ ≤ (L + a) * ‖x - y‖ := by
  have hid : (F x + a • x - b) - (F y + a • y - b) = (F x - F y) + a • (x - y) := by
    simp only [smul_sub]
    abel
  rw [hid]
  calc _ ≤ ‖F x - F y‖ + ‖a • (x - y)‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ + a * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      linarith [hL x y]
    _ = _ := by ring

omit [InnerProductSpace ℝ E] in
lemma residual_from_correction [NormedSpace ℝ E] (F : E → E) (L : ℝ)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (a a0 : ℝ) (ha0 : 0 ≤ a0)
    (b b0 u z : E) (hu : F u + a • u - b = 0) :
    ‖F z + a0 • z - b0‖ ≤ (L + a0) * ‖z - u‖ + ‖(a - a0) • u - (b - b0)‖ := by
  have he : F u + a0 • u - b0 = -((a - a0) • u - (b - b0)) := by
    have hb : F u + a • u = b := sub_eq_zero.mp hu
    rw [← hb]
    module
  have hn := norm_sub_le_norm_sub_add_norm_sub (F z + a0 • z - b0) (F u + a0 • u - b0) 0
  simp only [sub_zero] at hn
  have hl := anchored_residual_lipschitz F L hL a0 ha0 b0 z u
  rw [he, norm_neg] at hn
  rw [he] at hl
  linarith

end LongTails.Proofs.TailObliviousAnchoring
