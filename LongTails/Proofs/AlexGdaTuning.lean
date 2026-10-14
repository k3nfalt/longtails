import LongTails.Proofs.AlexGdaRun
import LongTails.Proofs.SmoothConvexConcaveGap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

open scoped RealInnerProductSpace

namespace OracleTemplate.BlockSaddle

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma params_of_kappa {γ δ Lx Ly Lxy α β κ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ)
    (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly) (hLxy : 0 ≤ Lxy) (hα : 0 < α) (hβ : 0 < β)
    (hA : (Lx + Lxy) * α = κ) (hB : (Ly + Lxy) * β = κ)
    (hκ : κ * (4 * γ ^ 2 * δ ^ 2) = γ - 1) :
    Lx * γ ^ 2 * α ≤ (γ - 1) / 4 ∧ γ * δ ^ 2 * Ly * β ≤ (γ - 1) / 4 ∧
      γ ^ 2 * δ ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16 ∧ (Lx + Lxy) * α ≤ 1 / 16 ∧
      (Ly + Lxy) * β ≤ 1 / 16 ∧
      Lxy * ((δ - 1) * β) ^ 2 ≤ ((2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8) * β ∧
      Lxy * ((δ - 1) * β) ≤ 1 / 16 ∧ Lxy * (γ * α) ≤ 1 / 8 := by
  have hγ0 : 0 < γ := by linarith
  have hδ0 : 0 < δ := by linarith
  have hc : 0 ≤ γ - 1 := by linarith
  have hd : 0 ≤ δ - 1 := by linarith
  have hκ0 : 0 ≤ κ := by rw [← hA]; exact mul_nonneg (add_nonneg hLx hLxy) hα.le
  have a1 : Lx * α ≤ κ := by linarith only [hA, mul_nonneg hLxy hα.le]
  have a2 : Lxy * α ≤ κ := by linarith only [hA, mul_nonneg hLx hα.le]
  have b1 : Ly * β ≤ κ := by linarith only [hB, mul_nonneg hLxy hβ.le]
  have b2 : Lxy * β ≤ κ := by linarith only [hB, mul_nonneg hLy hβ.le]
  have hγsq : 1 ≤ γ ^ 2 := one_le_pow₀ hγ.le
  have hδsq : 1 ≤ δ ^ 2 := one_le_pow₀ hδ
  have hq : κ * γ ^ 2 * δ ^ 2 = (γ - 1) / 4 := by linarith only [hκ]
  have k1 : κ * γ ^ 2 * 1 ≤ κ * γ ^ 2 * δ ^ 2 :=
    mul_le_mul_of_nonneg_left hδsq (mul_nonneg hκ0 (sq_nonneg γ))
  have hsq : 4 * (γ - 1) ≤ γ ^ 2 := by linarith only [sq_nonneg (γ - 2)]
  have kd : κ * δ ^ 2 ≤ 1 / 16 := by
    have h : κ * δ ^ 2 * (4 * γ ^ 2) ≤ 1 / 16 * (4 * γ ^ 2) := by linarith only [hκ, hsq]
    exact le_of_mul_le_mul_right h (by positivity)
  have kle : κ ≤ 1 / 16 := by
    have h : κ * 1 ≤ κ * δ ^ 2 := mul_le_mul_of_nonneg_left hδsq hκ0
    linarith only [h, kd]
  have kd2 : κ * δ ^ 2 ≤ (γ - 1) / 4 := by
    have h : κ * δ ^ 2 * 1 ≤ κ * δ ^ 2 * γ ^ 2 :=
      mul_le_mul_of_nonneg_left hγsq (mul_nonneg hκ0 (sq_nonneg δ))
    linarith only [h, hq]
  have kg : κ * γ ≤ 1 / 8 := by
    have h1 : γ * 1 ≤ γ * δ ^ 2 := mul_le_mul_of_nonneg_left hδsq hγ0.le
    have h : κ * γ * (4 * γ * δ ^ 2) ≤ 1 / 8 * (4 * γ * δ ^ 2) := by
      linarith only [hκ, h1, hγ2]
    exact le_of_mul_le_mul_right h (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left a1 (sq_nonneg γ)
    linarith only [h, k1, hq]
  · have h := mul_le_mul_of_nonneg_left b1 (mul_nonneg hγ0.le (sq_nonneg δ))
    have h2 : 0 ≤ (γ - 1) * (γ * δ ^ 2 * κ) :=
      mul_nonneg hc (mul_nonneg (mul_nonneg hγ0.le (sq_nonneg δ)) hκ0)
    linarith only [h, h2, hq]
  · have h := mul_le_mul a2 b2 (mul_nonneg hLxy hβ.le) hκ0
    have h2 := mul_le_mul_of_nonneg_left h (mul_nonneg (sq_nonneg γ) (sq_nonneg δ))
    have e : γ ^ 2 * δ ^ 2 * (κ * κ) = κ * ((γ - 1) / 4) := by rw [← hq]; ring
    have h3 : κ * ((γ - 1) / 4) ≤ 1 / 16 * (1 / 4) :=
      mul_le_mul kle (by linarith only [hγ2]) (by linarith only [hc]) (by norm_num)
    linarith only [h2, e, h3]
  · rw [hA]; exact kle
  · rw [hB]; exact kle
  · have s1 : (δ - 1) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hd (by linarith only [hd]) 2
    have s2 := mul_le_mul b2 s1 (sq_nonneg (δ - 1)) hκ0
    have s3 := mul_le_mul_of_nonneg_right (le_trans s2 kd2) hβ.le
    have p1 : 0 ≤ (2 - γ) * (δ - 1) * β :=
      mul_nonneg (mul_nonneg (by linarith only [hγ2]) hd) hβ.le
    have p2 : 0 ≤ (γ - 1) * β := mul_nonneg hc hβ.le
    linarith only [s3, p1, p2]
  · have h := mul_le_mul_of_nonneg_right b2 hd
    have h2 : 0 ≤ δ * (δ - 1) := mul_nonneg hδ0.le hd
    have h3 : κ * (δ - 1) ≤ κ * δ ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [h2]) hκ0
    linarith only [h, h3, kd]
  · have h := mul_le_mul_of_nonneg_right a2 hγ0.le
    linarith only [h, kg]

lemma concave_support {φ : F → ℝ} {w y y' : F} (hc : ConcaveOn ℝ Set.univ φ)
    (hg : HasGradientAt φ w y) : φ y' - φ y ≤ ⟪w, y' - y⟫ := by
  have hd : HasGradientAt (fun z => -φ z) (-w) y := by
    have h1 : HasFDerivAt (fun z => -φ z) (-(InnerProductSpace.toDual ℝ F) w) y :=
      hg.hasFDerivAt.neg
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact h1
  have h := SaddlePoint.convex_support_on (X := Set.univ) (f := fun z => -φ z) (v := -w)
    (x := y) (y := y') hc.neg (Set.mem_univ y) (Set.mem_univ y') hd
  have h' : -⟪w, y' - y⟫ ≤ -φ y' - -φ y := by
    rw [← inner_neg_left]; exact h
  linarith only [h']

lemma hyp_of_admissible {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F} {Lx Ly Lxy : ℝ}
    {xs : E} {ys : F}
    (hgx : ∀ z : E × F, HasGradientAt (fun x => f x z.2) (gx z) z.1)
    (hgy : ∀ z : E × F, HasGradientAt (fun y => f z.1 y) (gy z) z.2)
    (hcv : ∀ y, ConvexOn ℝ Set.univ (fun x => f x y))
    (hcc : ∀ x, ConcaveOn ℝ Set.univ (fun y => f x y))
    (lxx : ∀ x x' y, ‖gx (x, y) - gx (x', y)‖ ≤ Lx * ‖x - x'‖)
    (lxy : ∀ x y y', ‖gx (x, y) - gx (x, y')‖ ≤ Lxy * ‖y - y'‖)
    (lyy : ∀ x y y', ‖gy (x, y) - gy (x, y')‖ ≤ Ly * ‖y - y'‖)
    (lyx : ∀ x x' y, ‖gy (x, y) - gy (x', y)‖ ≤ Lxy * ‖x - x'‖)
    (hs : ∀ x y, f xs y ≤ f xs ys ∧ f xs ys ≤ f x ys) :
    Hyp f gx gy Lx Ly Lxy xs ys where
  cvx := fun x x' y =>
    SaddlePoint.convex_support_on (hcv y) (Set.mem_univ x) (Set.mem_univ x') (hgx (x, y))
  ccv := fun x y y' => concave_support (hcc x) (hgy (x, y))
  lxx := lxx
  lxy := lxy
  lyy := lyy
  lyx := lyx
  sx := by
    have hmin : IsLocalMin (fun x => f x ys) xs :=
      Filter.Eventually.of_forall (fun x => (hs x ys).2)
    have h := hmin.hasFDerivAt_eq_zero (hgx (xs, ys)).hasFDerivAt
    exact (LinearIsometryEquiv.map_eq_zero_iff _).mp h
  sy := by
    have hmax : IsLocalMax (fun y => f xs y) ys :=
      Filter.Eventually.of_forall (fun y => (hs xs y).1)
    have h := hmax.hasFDerivAt_eq_zero (hgy (xs, ys)).hasFDerivAt
    exact (LinearIsometryEquiv.map_eq_zero_iff _).mp h

omit [CompleteSpace E] [CompleteSpace F] in
theorem alex_guarantee {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F} {Lx Ly Lxy : ℝ}
    {xs : E} {ys : F} {γ δ R ε : ℝ} {x0 : E} {y0 : F} (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly) (hLxy : 0 ≤ Lxy) (hx : 0 < Lx + Lxy) (hy : 0 < Ly + Lxy)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ) (hε : 0 < ε)
    (hdist : ‖x0 - xs‖ ^ 2 + ‖y0 - ys‖ ^ 2 ≤ R ^ 2) (K : ℕ)
    (hK : 180 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2 * R ^ 2 / ((γ - 1) ^ 3 * ε ^ 2) ≤ K) :
    ‖gx (record gx gy γ δ ((γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (Lx + Lxy)))
        ((γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (Ly + Lxy))) x0 y0 K).1‖ ^ 2 +
      ‖gy (record gx gy γ δ ((γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (Lx + Lxy)))
        ((γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (Ly + Lxy))) x0 y0 K).1‖ ^ 2 ≤ ε ^ 2 := by
  have hγ0 : 0 < γ := by linarith
  have hδ0 : 0 < δ := by linarith
  have hc : 0 < γ - 1 := by linarith
  have hΛx : Lx + Lxy ≤ max Lx Ly + Lxy := by linarith only [le_max_left Lx Ly]
  have hΛy : Ly + Lxy ≤ max Lx Ly + Lxy := by linarith only [le_max_right Lx Ly]
  have hΛ : 0 < max Lx Ly + Lxy := lt_of_lt_of_le hx hΛx
  have hden : 0 < 4 * γ ^ 2 * δ ^ 2 := by positivity
  have hc3 : 0 < (γ - 1) ^ 3 * ε ^ 2 := by positivity
  have hK' : 180 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2 * R ^ 2 ≤ K * ((γ - 1) ^ 3 * ε ^ 2) :=
    (div_le_iff₀ hc3).mp hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have hR : R ^ 2 ≤ 0 := by
      have hpos : 0 < 180 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2 := by positivity
      have h : 180 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2 * R ^ 2 ≤ 0 := by
        simpa using hK'
      by_contra hne
      have := mul_pos hpos (lt_of_not_ge hne)
      linarith only [h, this]
    have h1 : ‖x0 - xs‖ ^ 2 ≤ 0 := by linarith only [hdist, hR, sq_nonneg ‖y0 - ys‖]
    have h2 : ‖y0 - ys‖ ^ 2 ≤ 0 := by linarith only [hdist, hR, sq_nonneg ‖x0 - xs‖]
    have ex : x0 = xs := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h1 (sq_nonneg _))
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    have ey : y0 = ys := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h2 (sq_nonneg _))
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    show ‖gx (x0, y0)‖ ^ 2 + ‖gy (x0, y0)‖ ^ 2 ≤ ε ^ 2
    rw [ex, ey, H.sx, H.sy, norm_zero, norm_zero]
    nlinarith only [sq_nonneg ε]
  · set α := (γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (Lx + Lxy)) with hαdef
    set β := (γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (Ly + Lxy)) with hβdef
    set m0 := (γ - 1) / (4 * γ ^ 2 * δ ^ 2 * (max Lx Ly + Lxy)) with hm0def
    have hα : 0 < α := div_pos hc (mul_pos hden hx)
    have hβ : 0 < β := div_pos hc (mul_pos hden hy)
    have hm0 : 0 < m0 := div_pos hc (mul_pos hden hΛ)
    have hmα : m0 ≤ α :=
      div_le_div_of_nonneg_left hc.le (mul_pos hden hx) (mul_le_mul_of_nonneg_left hΛx hden.le)
    have hmβ : m0 ≤ β :=
      div_le_div_of_nonneg_left hc.le (mul_pos hden hy) (mul_le_mul_of_nonneg_left hΛy hden.le)
    have hA : (Lx + Lxy) * α = (γ - 1) / (4 * γ ^ 2 * δ ^ 2) := by
      rw [hαdef, mul_comm (Lx + Lxy), div_mul_eq_mul_div, mul_div_mul_right _ _ hx.ne']
    have hB : (Ly + Lxy) * β = (γ - 1) / (4 * γ ^ 2 * δ ^ 2) := by
      rw [hβdef, mul_comm (Ly + Lxy), div_mul_eq_mul_div, mul_div_mul_right _ _ hy.ne']
    have hκ : (γ - 1) / (4 * γ ^ 2 * δ ^ 2) * (4 * γ ^ 2 * δ ^ 2) = γ - 1 :=
      div_mul_cancel₀ _ hden.ne'
    obtain ⟨c1, c2, c3, e1, e2, e3, r1, r2⟩ :=
      params_of_kappa hγ hγ2 hδ hLx hLy hLxy hα hβ hA hB hκ
    have hb := best_bound (x0 := x0) (y0 := y0) H hγ hγ2 hδ hα hβ hLx hLy hLxy c1 c2 c3 e1 e2 e3
      r1 r2 hm0 hmα hmβ K hKpos
    set res := ‖gx (record gx gy γ δ α β x0 y0 K).1‖ ^ 2 +
      ‖gy (record gx gy γ δ α β x0 y0 K).1‖ ^ 2 with hres
    have hm : m0 * (4 * γ ^ 2 * δ ^ 2 * (max Lx Ly + Lxy)) = γ - 1 := by
      rw [hm0def]; exact div_mul_cancel₀ _ (mul_pos hden hΛ).ne'
    have hm2 : m0 ^ 2 * (16 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2) = (γ - 1) ^ 2 := by
      rw [← hm]; ring
    have h2 := mul_le_mul_of_nonneg_right hb
      (show 0 ≤ 16 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2 by positivity)
    have e : (γ - 1) * m0 ^ 2 * K * res * (16 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2) =
        (γ - 1) ^ 3 * K * res := by
      calc (γ - 1) * m0 ^ 2 * K * res * (16 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2)
          = (γ - 1) * K * res * (m0 ^ 2 * (16 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2)) := by
            ring
        _ = (γ - 1) * K * res * (γ - 1) ^ 2 := by rw [hm2]
        _ = (γ - 1) ^ 3 * K * res := by ring
    rw [e] at h2
    have h3 := mul_le_mul_of_nonneg_left hdist
      (show 0 ≤ 180 * γ ^ 4 * δ ^ 4 * (max Lx Ly + Lxy) ^ 2 by positivity)
    have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
    have hpos : 0 < (γ - 1) ^ 3 * K := by positivity
    have h4 : (γ - 1) ^ 3 * K * res ≤ (γ - 1) ^ 3 * K * ε ^ 2 := by
      linarith only [h2, h3, hK']
    exact le_of_mul_le_mul_left h4 hpos

end OracleTemplate.BlockSaddle
