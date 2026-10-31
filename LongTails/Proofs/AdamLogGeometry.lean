import LongTails.Proofs.NearestSetLocal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamLogGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma gradient_continuous {g : E → E} {L0 L1 : ℝ} (hL1 : 0 ≤ L1)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖) : Continuous g := by
  apply continuous_iff_continuousAt.2
  intro x
  apply continuousAt_of_locally_lipschitz (r := 1 / (1 + L1)) (by positivity)
    (L0 + L1 * ‖g x‖)
  intro y hy
  simp only [dist_eq_norm] at hy ⊢
  apply hs x y
  have hh := (lt_div_iff₀ (show 0 < 1 + L1 by positivity)).1 hy
  nlinarith [norm_nonneg (y - x)]

lemma local_upper {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (x y : E) (hxy : L1 * ‖y - x‖ ≤ 1) :
    f y ≤ f x + ⟪g x, y - x⟫ + (L0 + L1 * ‖g x‖) / 2 * ‖y - x‖ ^ 2 := by
  apply OracleTemplate.NearestSet.segment_upper_bound hf x y
  intro t ht
  have hn : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have ht1 : t ≤ 1 := ht.2.le
  have hsmall : L1 * ‖x + t • (y - x) - x‖ ≤ 1 := by
    rw [hn]
    calc L1 * (t * ‖y - x‖) ≤ L1 * ‖y - x‖ := by
          nlinarith [mul_nonneg hL1 (norm_nonneg (y - x))]
      _ ≤ 1 := hxy
  have h := hs x (x + t • (y - x)) hsmall
  rw [hn] at h
  convert h using 1; ring

lemma local_remainder {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (x y : E) (hxy : L1 * ‖y - x‖ ≤ 1) :
    |f y - f x - ⟪g x, y - x⟫| ≤ (L0 + L1 * ‖g x‖) / 2 * ‖y - x‖ ^ 2 := by
  have hu := local_upper hL1 hf hs x y hxy
  have hn : ∀ z, HasGradientAt (fun w => -f w) (-g z) z := by
    intro z
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hf z).hasFDerivAt.neg
  have hs' : ∀ u v, L1 * ‖v - u‖ ≤ 1 →
      ‖(-g v) - (-g u)‖ ≤ (L0 + L1 * ‖-g u‖) * ‖v - u‖ := by
    intro u v h
    simpa only [neg_sub_neg, norm_sub_rev, norm_neg] using hs u v h
  have hl := local_upper hL1 hn hs' x y hxy
  simp only [norm_neg, inner_neg_left] at hl
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma gradient_gap_square {f : E → ℝ} {g : E → E} {L0 L1 lower : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hlower : ∀ x, lower ≤ f x) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * (1 + L0 + L1 * ‖g x‖) * (f x - lower) := by
  let C := 1 + L0 + L1 * ‖g x‖
  have hC : 0 < C := by dsimp [C]; positivity
  let y := x - (1 / C) • g x
  have hy : y - x = -(1 / C) • g x := by dsimp [y]; module
  have hn : ‖y - x‖ = ‖g x‖ / C := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.2 hC)]
    ring
  have hsmall : L1 * ‖y - x‖ ≤ 1 := by
    rw [hn, ← mul_div_assoc]
    apply (div_le_one hC).2
    dsimp [C]
    linarith
  have hu := local_upper hL1 hf hs x y hsmall
  rw [hy, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.2 hC)] at hu
  have hlo := hlower y
  have hrel : L0 + L1 * ‖g x‖ ≤ C := by dsimp [C]; linarith
  have hbound : (L0 + L1 * ‖g x‖) / 2 * ((1 / C) * ‖g x‖) ^ 2 ≤
      ‖g x‖ ^ 2 / (2 * C) := by
    calc _ ≤ C / 2 * ((1 / C) * ‖g x‖) ^ 2 := by gcongr
      _ = _ := by field_simp
  have hg : ‖g x‖ ^ 2 / (2 * C) ≤ f x - lower := by
    have he : -(1 / C) * ‖g x‖ ^ 2 = -2 * (‖g x‖ ^ 2 / (2 * C)) := by field_simp
    rw [he] at hu
    linarith
  exact (div_le_iff₀ (by positivity : 0 < 2 * C)).1 hg |>.trans_eq (by ring)

lemma gradient_gap_linear {f : E → ℝ} {g : E → E} {L0 L1 lower : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hlower : ∀ x, lower ≤ f x) (x : E) :
    ‖g x‖ ≤ 4 * (1 + L0 + L1) * (1 + f x - lower) := by
  have h := gradient_gap_square hL0 hL1 hf hs hlower x
  have hD : 0 ≤ f x - lower := sub_nonneg.2 (hlower x)
  have hH : 0 ≤ ‖g x‖ := norm_nonneg _
  by_contra hn
  have hlarge : 4 * (1 + L0 + L1) * (1 + f x - lower) < ‖g x‖ := lt_of_not_ge hn
  have h1 : 4 * L1 * (f x - lower) < ‖g x‖ := by
    nlinarith [mul_nonneg hL0 hD, mul_nonneg hL1 hD]
  have h2 : 4 * (1 + L0) * (f x - lower) < ‖g x‖ := by
    nlinarith [mul_nonneg hL1 hD]
  have h3 : 1 < ‖g x‖ := by
    nlinarith [mul_nonneg hL0 hD, mul_nonneg hL1 hD]
  have h4 := mul_lt_mul_of_pos_right h1 (lt_trans zero_lt_one h3)
  nlinarith [sq_nonneg (‖g x‖ - 1)]

lemma log_gradient {f : E → ℝ} {g : E → E} {lower : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x) (x : E) :
    HasGradientAt (fun y => Real.log (1 + f y - lower))
      ((1 + f x - lower)⁻¹ • g x) x := by
  have hpos : 0 < 1 + f x - lower := by linarith [hlower x]
  have hh := (((hf x).hasFDerivAt.const_add 1).sub_const lower).log hpos.ne'
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hh using 1
  simp only [map_smul]

lemma log_lipschitz {f : E → ℝ} {g : E → E} {lower K : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower)) (x y : E) :
    |Real.log (1 + f y - lower) - Real.log (1 + f x - lower)| ≤ K * ‖y - x‖ := by
  have hnorm (z : E) : ‖InnerProductSpace.toDual ℝ E ((1 + f z - lower)⁻¹ • g z)‖ ≤ K := by
    have hp : 0 < 1 + f z - lower := by linarith [hlower z]
    rw [(InnerProductSpace.toDual ℝ E).norm_map, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (by linarith [hlower z]))]
    have hh := hbound z
    calc (1 + f z - lower)⁻¹ * ‖g z‖ ≤ (1 + f z - lower)⁻¹ * (K * (1 + f z - lower)) := by
          exact mul_le_mul_of_nonneg_left hh (inv_nonneg.2 hp.le)
      _ = K := by field_simp
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := Set.univ)
      (fun z _ => (log_gradient hf hlower z).hasFDerivAt.hasFDerivWithinAt)
      (fun z _ => hnorm z) (convex_univ : Convex ℝ (Set.univ : Set E))
      (Set.mem_univ x) (Set.mem_univ y)

omit [CompleteSpace E] in
lemma normalized_sub_le {a b K C J r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hJ : 0 ≤ J) (hr : 0 ≤ r) (u v : E)
    (hv : ‖v‖ ≤ K * b) (hd : ‖v - u‖ ≤ C * a * r)
    (hab : |a - b| ≤ J * a * r) :
    ‖b⁻¹ • v - a⁻¹ • u‖ ≤ (C + K * J) * r := by
  have hid : b⁻¹ = a⁻¹ + (a - b) / (a * b) := by field_simp; ring
  have he : b⁻¹ • v - a⁻¹ • u =
      a⁻¹ • (v - u) + ((a - b) / (a * b)) • v := by
    rw [hid, add_smul, smul_sub]
    module
  have h1 : ‖a⁻¹ • (v - u)‖ ≤ C * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
    calc a⁻¹ * ‖v - u‖ ≤ a⁻¹ * (C * a * r) :=
          mul_le_mul_of_nonneg_left hd (inv_nonneg.2 ha.le)
      _ = _ := by field_simp
  have h2 : ‖((a - b) / (a * b)) • v‖ ≤ K * J * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ha hb)]
    calc |a - b| / (a * b) * ‖v‖ ≤ (J * a * r) / (a * b) * (K * b) := by gcongr
      _ = _ := by field_simp
  rw [he]
  exact (norm_add_le _ _).trans (by nlinarith [h1, h2])

lemma local_value_difference {f : E → ℝ} {g : E → E} {L0 L1 lower K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower))
    (hC : L0 + L1 * K ≤ K ^ 2) (x y : E)
    (hxy : L1 * ‖y - x‖ ≤ 1) (hshort : K * ‖y - x‖ ≤ 1) :
    |f y - f x| ≤ (2 * K) * (1 + f x - lower) * ‖y - x‖ := by
  let φ := 1 + f x - lower
  let r := ‖y - x‖
  have hφ : 1 ≤ φ := by dsimp [φ]; linarith [hlower x]
  have hr : 0 ≤ r := norm_nonneg _
  have hc : L0 + L1 * ‖g x‖ ≤ K ^ 2 * φ := by
    have hh := mul_le_mul_of_nonneg_left (hbound x) hL1
    have h0 := mul_le_mul_of_nonneg_left hφ hL0
    have h1 := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ φ)
    change L1 * ‖g x‖ ≤ L1 * (K * φ) at hh
    nlinarith
  have ht := local_remainder hL1 hf hs x y hxy
  have hi := abs_real_inner_le_norm (g x) (y - x)
  have hv : |f y - f x| ≤ ‖g x‖ * r + (L0 + L1 * ‖g x‖) / 2 * r ^ 2 := by
    have hh := abs_add_le (f y - f x - ⟪g x, y - x⟫) ⟪g x, y - x⟫
    simp only [sub_add_cancel] at hh
    linarith
  have hmain := mul_le_mul_of_nonneg_right (hbound x) hr
  have hquad := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
  have hshort' := mul_le_mul_of_nonneg_right hshort (mul_nonneg (mul_nonneg hK (by positivity : 0 ≤ φ)) hr)
  change |f y - f x| ≤ (2 * K) * φ * r
  change K * r ≤ 1 at hshort
  change ‖g x‖ * r ≤ K * φ * r at hmain
  dsimp [r] at hshort'
  dsimp [r] at hv hquad hmain ⊢
  nlinarith

lemma log_gradient_local {f : E → ℝ} {g : E → E} {L0 L1 lower K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower))
    (hC : L0 + L1 * K ≤ K ^ 2) (x y : E)
    (hxy : L1 * ‖y - x‖ ≤ 1) (hshort : K * ‖y - x‖ ≤ 1) :
    ‖(1 + f y - lower)⁻¹ • g y - (1 + f x - lower)⁻¹ • g x‖ ≤
      3 * K ^ 2 * ‖y - x‖ := by
  have hx : 0 < 1 + f x - lower := by linarith [hlower x]
  have hy : 0 < 1 + f y - lower := by linarith [hlower y]
  have hc : L0 + L1 * ‖g x‖ ≤ (L0 + L1 * K) * (1 + f x - lower) := by
    have h0 := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + f x - lower by linarith [hlower x]) hL0
    have h1 := mul_le_mul_of_nonneg_left (hbound x) hL1
    nlinarith
  have hd : ‖g y - g x‖ ≤ (L0 + L1 * K) * (1 + f x - lower) * ‖y - x‖ :=
    (hs x y hxy).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hv := local_value_difference hL0 hL1 hK hf hlower hs hbound hC x y hxy hshort
  have hab : |(1 + f x - lower) - (1 + f y - lower)| ≤
      (2 * K) * (1 + f x - lower) * ‖y - x‖ := by
    have he : (1 + f x - lower) - (1 + f y - lower) = -(f y - f x) := by ring
    simpa only [he, abs_neg] using hv
  have hn := normalized_sub_le hx hy (by positivity : 0 ≤ 2 * K)
    (norm_nonneg (y - x)) (g x) (g y) (hbound y) hd hab
  exact hn.trans (by nlinarith [mul_le_mul_of_nonneg_right hC (norm_nonneg (y - x))])

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma global_of_local {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ E]
    {g : E → F} {r C : ℝ} (hr : 0 < r)
    (hlocal : ∀ x y, ‖y - x‖ ≤ r → ‖g y - g x‖ ≤ C * ‖y - x‖) (x y : E) :
    ‖g y - g x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖y - x‖ / r)
  have hN0 : 0 < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
  let v := (1 / (N : ℝ)) • (y - x)
  have hv : ‖v‖ = ‖y - x‖ / N := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hN0)]
    ring
  have hvr : ‖v‖ ≤ r := by
    rw [hv]
    apply (div_le_iff₀ hN0).2
    have hh := (div_lt_iff₀ hr).1 hN
    nlinarith
  have hstep (i : ℕ) : ‖g (x + (i + 1 : ℕ) • v) - g (x + i • v)‖ ≤ C * ‖v‖ := by
    have he : (x + (i + 1 : ℕ) • v) - (x + i • v) = v := by
      rw [add_nsmul, one_nsmul]
      abel
    simpa only [he] using hlocal (x + i • v) (x + (i + 1 : ℕ) • v) (by simpa only [he] using hvr)
  have hsum (i : ℕ) : ‖g (x + i • v) - g x‖ ≤ (i : ℝ) * C * ‖v‖ := by
    induction i with
    | zero => simp
    | succ i ih =>
        have ht := norm_sub_le_norm_sub_add_norm_sub (g (x + (i + 1 : ℕ) • v)) (g (x + i • v)) (g x)
        have hh := hstep i
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith
  have hend : x + N • v = y := by
    dsimp [v]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have he : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp
    rw [he, one_smul, add_sub_cancel]
  have hh := hsum N
  rw [hend, hv] at hh
  convert hh using 1
  field_simp

lemma log_gradient_lipschitz {f : E → ℝ} {g : E → E} {L0 L1 lower K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 →
      ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower))
    (hC : L0 + L1 * K ≤ K ^ 2) (x y : E) :
    ‖(1 + f y - lower)⁻¹ • g y - (1 + f x - lower)⁻¹ • g x‖ ≤
      3 * K ^ 2 * ‖y - x‖ := by
  apply global_of_local (r := 1 / (1 + L1 + K)) (by positivity)
    (fun u v hdist => ?_) x y
  have hp : 0 < 1 + L1 + K := by positivity
  have hd := (le_div_iff₀ hp).1 hdist
  apply log_gradient_local hL0 hL1 hK hf hlower hs hbound hC u v
  · nlinarith [mul_nonneg hK (norm_nonneg (v - u)), norm_nonneg (v - u)]
  · nlinarith [mul_nonneg hL1 (norm_nonneg (v - u)), norm_nonneg (v - u)]

lemma close_value_bound {f : E → ℝ} {g : E → E} {lower K : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower)) (x y : E)
    (hnear : K * ‖y - x‖ ≤ 1 / 2) :
    1 + f y - lower ≤ 2 * (1 + f x - lower) := by
  have hx : 0 < 1 + f x - lower := by linarith [hlower x]
  have hy : 0 < 1 + f y - lower := by linarith [hlower y]
  have hl := (abs_le.mp (log_lipschitz hf hlower hbound x y)).2
  have he : Real.exp (1 / 2) ≤ 2 := by
    rw [Real.exp_half]
    nlinarith [Real.sq_sqrt (Real.exp_pos 1).le, Real.sqrt_nonneg (Real.exp 1),
      Real.exp_one_lt_three]
  have hh := Real.exp_le_exp.mpr (show Real.log (1 + f y - lower) ≤
      Real.log (1 + f x - lower) + 1 / 2 by linarith)
  rw [Real.exp_log hy, Real.exp_add, Real.exp_log hx] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left he hx.le])

lemma local_value_lipschitz {f : E → ℝ} {g : E → E} {lower K r : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower)) (x y z : E)
    (hr : K * r ≤ 1 / 2) (hy : ‖y - x‖ ≤ r) (hz : ‖z - x‖ ≤ r) :
    |f y - f z| ≤ 2 * K * (1 + f x - lower) * ‖y - z‖ := by
  have hgrad (w : E) (hw : w ∈ Metric.closedBall x r) :
      ‖InnerProductSpace.toDual ℝ E (g w)‖ ≤ 2 * K * (1 + f x - lower) := by
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    have hd : ‖w - x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hn : K * ‖w - x‖ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hd hK).trans hr
    have hv := mul_le_mul_of_nonneg_left (close_value_bound hf hlower hbound x w hn) hK
    exact (hbound w).trans (by nlinarith)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (s := Metric.closedBall x r) (fun w _ => (hf w).hasFDerivAt.hasFDerivWithinAt)
    hgrad (convex_closedBall x r)
    (show z ∈ Metric.closedBall x r by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
    (show y ∈ Metric.closedBall x r by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
  simpa only [Real.norm_eq_abs] using h

end LongTails.Proofs.AdamLogGeometry
