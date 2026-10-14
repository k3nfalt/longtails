import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.BlockSaddle

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

structure Hyp (f : E → F → ℝ) (gx : E × F → E) (gy : E × F → F) (Lx Ly Lxy : ℝ)
    (xs : E) (ys : F) : Prop where
  cvx : ∀ x x' y, ⟪gx (x, y), x' - x⟫ ≤ f x' y - f x y
  ccv : ∀ x y y', f x y' - f x y ≤ ⟪gy (x, y), y' - y⟫
  lxx : ∀ x x' y, ‖gx (x, y) - gx (x', y)‖ ≤ Lx * ‖x - x'‖
  lxy : ∀ x y y', ‖gx (x, y) - gx (x, y')‖ ≤ Lxy * ‖y - y'‖
  lyy : ∀ x y y', ‖gy (x, y) - gy (x, y')‖ ≤ Ly * ‖y - y'‖
  lyx : ∀ x x' y, ‖gy (x, y) - gy (x', y)‖ ≤ Lxy * ‖x - x'‖
  sx : gx (xs, ys) = 0
  sy : gy (xs, ys) = 0

lemma inner_lower {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (a b : G) (r : ℝ) (h : ‖a - b‖ ≤ r) : ‖b‖ ^ 2 - r * ‖b‖ ≤ ⟪a, b⟫ := by
  have h1 : ⟪a, b⟫ = ‖b‖ ^ 2 + ⟪a - b, b⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
  have h2 := abs_real_inner_le_norm (a - b) b
  have h3 := neg_abs_le ⟪a - b, b⟫
  have h4 := mul_le_mul_of_nonneg_right h (norm_nonneg b)
  linarith

lemma dist_drop_x (x xs g : E) {α : ℝ} (hα : 0 < α) :
    ‖x - xs‖ ^ 2 / α - ‖x - α • g - xs‖ ^ 2 / α = 2 * ⟪x - xs, g⟫ - α * ‖g‖ ^ 2 := by
  have e : x - α • g - xs = (x - xs) - α • g := by abel
  rw [e, norm_sub_sq_real (x - xs) (α • g), inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp
  ring

lemma dist_drop_y (y ys h : F) {β : ℝ} (hβ : 0 < β) :
    ‖y - ys‖ ^ 2 / β - ‖y + β • h - ys‖ ^ 2 / β = -(2 * ⟪h, y - ys⟫) - β * ‖h‖ ^ 2 := by
  have e : y + β • h - ys = (y - ys) + β • h := by abel
  rw [e, norm_add_sq_real (y - ys) (β • h), inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm h (y - ys)]
  field_simp
  ring

lemma cross_bound {k a b u : ℝ} (hk : k ≤ 1 / 16) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (he : u ^ 2 = k * (a * b)) : u ≤ (a + b) / 8 := by
  have hv0 : 0 ≤ (a + b) / 8 := by positivity
  refine (sq_le_sq₀ hu hv0).mp ?_
  rw [he]
  have h1 := mul_le_mul_of_nonneg_right hk (mul_nonneg ha hb)
  have h2 := sq_nonneg (a - b)
  have e : ((a + b) / 8) ^ 2 = 1 / 16 * (a * b) + (a - b) ^ 2 / 64 := by ring
  rw [e]
  linarith only [h1, h2]

lemma coef_q3 {γ δ Ly β : ℝ} (hγ : 1 < γ) (hδ : 1 ≤ δ) (hLy : 0 ≤ Ly) (hβ : 0 < β)
    (c2 : γ * δ ^ 2 * Ly * β ≤ (γ - 1) / 4) :
    (2 - γ) * (δ - 1) ^ 2 * (Ly * β) ≤ (γ - 1) / 4 := by
  have h1 : (δ - 1) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h0 : 0 ≤ (δ - 1) ^ 2 := sq_nonneg _
  have h2 : (2 - γ) * (δ - 1) ^ 2 ≤ 1 * (δ - 1) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  have h3 : δ ^ 2 ≤ γ * δ ^ 2 := le_mul_of_one_le_left (sq_nonneg δ) hγ.le
  have h4 : (2 - γ) * (δ - 1) ^ 2 ≤ γ * δ ^ 2 := by linarith only [h1, h2, h3]
  have h5 := mul_le_mul_of_nonneg_right h4 (mul_nonneg hLy hβ.le)
  linarith only [h5, c2]

lemma coef_k5 {γ δ α β Lxy : ℝ} (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (c3 : γ ^ 2 * δ ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16) :
    γ ^ 2 * (δ - 1) ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16 := by
  have h1 : (δ - 1) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : 0 ≤ γ ^ 2 * Lxy ^ 2 * (α * β) := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  linarith only [h3, c3]

set_option maxHeartbeats 1000000 in
lemma arith_core {γ δ α β Lx Ly Lxy G H N S1 S2 S3 S4 hv : ℝ}
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (hLy : 0 ≤ Ly) (hLxy : 0 ≤ Lxy) (hG : 0 ≤ G) (hH : 0 ≤ H) (hN : 0 ≤ N)
    (c1 : Lx * γ ^ 2 * α ≤ (γ - 1) / 4)
    (c2 : γ * δ ^ 2 * Ly * β ≤ (γ - 1) / 4)
    (c3 : γ ^ 2 * δ ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16)
    (b1 : (1 - Lx * (γ * α)) * G ^ 2 ≤ S1)
    (b2 : hv - Ly * ((δ - 1) * β) * N ^ 2 ≤ S2)
    (bhv : -(H ^ 2 + N ^ 2) / 2 ≤ hv)
    (b3 : G ^ 2 - (Lx * (γ * α) * G + Lxy * ((δ - 1) * β) * N) * G ≤ S3)
    (b4 : H ^ 2 - (Ly * (δ * β) * H + Lxy * ((γ - 1) * α) * G) * H ≤ S4) :
    (γ - 1) / 4 * (α * G ^ 2 + β * H ^ 2) ≤
      (2 - γ) * (γ * α * S1 + (δ - 1) * β * S2) + γ * ((γ - 1) * α * S3 + δ * β * S4)
        - α * G ^ 2 - β * H ^ 2
        + ((2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8) * β * (N ^ 2 - H ^ 2) := by
  have hc : 0 ≤ γ - 1 := by linarith
  have hd : 0 ≤ δ - 1 := by linarith
  have h2γ : 0 ≤ 2 - γ := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hG2 : 0 ≤ α * G ^ 2 := mul_nonneg hα.le (sq_nonneg G)
  have hH2 : 0 ≤ β * H ^ 2 := mul_nonneg hβ.le (sq_nonneg H)
  have hN2 : 0 ≤ β * N ^ 2 := mul_nonneg hβ.le (sq_nonneg N)
  have P1 := mul_le_mul_of_nonneg_left b1 (mul_nonneg h2γ (mul_nonneg hγ0 hα.le))
  have P2 := mul_le_mul_of_nonneg_left b2 (mul_nonneg h2γ (mul_nonneg hd hβ.le))
  have P2' := mul_le_mul_of_nonneg_left bhv (mul_nonneg h2γ (mul_nonneg hd hβ.le))
  have P3 := mul_le_mul_of_nonneg_left b3 (mul_nonneg hγ0 (mul_nonneg hc hα.le))
  have P4 := mul_le_mul_of_nonneg_left b4 (mul_nonneg hγ0 (mul_nonneg hδ0 hβ.le))
  have Q1 := mul_le_mul_of_nonneg_right c1 hG2
  have Q2 := mul_le_mul_of_nonneg_right c2 hH2
  have Q3 := mul_le_mul_of_nonneg_right (coef_q3 hγ hδ hLy hβ c2) hN2
  have hu4 : γ * δ * Lxy * (α * β) * (G * H) ≤ (α * G ^ 2 + β * H ^ 2) / 8 :=
    cross_bound c3 hG2 hH2
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hγ0 hδ0) hLxy) (mul_nonneg hα.le hβ.le))
        (mul_nonneg hG hH)) (by ring)
  have hu5 : γ * (δ - 1) * Lxy * (α * β) * (N * G) ≤ (α * G ^ 2 + β * N ^ 2) / 8 :=
    cross_bound (coef_k5 hδ hα hβ c3) hG2 hN2
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hγ0 hd) hLxy) (mul_nonneg hα.le hβ.le))
        (mul_nonneg hN hG)) (by ring)
  have Q4 := mul_le_mul_of_nonneg_left hu4 hc
  have Q5 := mul_le_mul_of_nonneg_left hu5 hc
  have R1 : 0 ≤ (γ - 1) * (α * G ^ 2) := mul_nonneg hc hG2
  have R2 : 0 ≤ (γ - 1) * (δ - 1) * (β * H ^ 2) := mul_nonneg (mul_nonneg hc hd) hH2
  linarith only [P1, P2, P2', P3, P4, Q1, Q2, Q3, Q4, Q5, R1, R2]

section Points

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F} {Lx Ly Lxy : ℝ} {xs : E} {ys : F}

lemma Hyp.saddle_x (H : Hyp f gx gy Lx Ly Lxy xs ys) (x : E) : f xs ys ≤ f x ys := by
  have h := H.cvx xs x ys
  rw [H.sx, inner_zero_left] at h
  linarith only [h]

lemma Hyp.saddle_y (H : Hyp f gx gy Lx Ly Lxy xs ys) (y : F) : f xs y ≤ f xs ys := by
  have h := H.ccv xs ys y
  rw [H.sy, inner_zero_left] at h
  linarith only [h]

lemma energy_drop_points (H : Hyp f gx gy Lx Ly Lxy xs ys) {γ δ α β θ : ℝ}
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hα : 0 < α) (hβ : 0 < β)
    (x : E) (y v q : F) (g p : E) (h : F) (x1 : E) (y1 q1 : F) (g1 : E)
    (hq : q = y + ((δ - 1) * β) • v) (hg : g = gx (x, q)) (hp : p = x - (γ * α) • g)
    (hh : h = gy (p, y)) (hx1 : x1 = x - α • g) (hy1 : y1 = y + β • h)
    (hq1 : q1 = y1 + ((δ - 1) * β) • h) (hg1 : g1 = gx (x1, q1)) :
    (2 - γ) * (γ * α * ⟪gx (p, q), g⟫ + (δ - 1) * β * ⟪gy (p, q), v⟫)
        + γ * ((γ - 1) * α * ⟪gx (p, y), g⟫ + δ * β * ⟪gy (x1, q1), h⟫)
        - α * ‖g‖ ^ 2 - β * ‖h‖ ^ 2 + θ * β * (‖v‖ ^ 2 - ‖h‖ ^ 2) ≤
      (‖x - xs‖ ^ 2 / α + ‖y - ys‖ ^ 2 / β - ⟪x - xs, g⟫ - (γ - 1) * (f x q - f xs ys)
          + θ * β * ‖v‖ ^ 2)
        - (‖x1 - xs‖ ^ 2 / α + ‖y1 - ys‖ ^ 2 / β - ⟪x1 - xs, g1⟫
          - (γ - 1) * (f x1 q1 - f xs ys) + θ * β * ‖h‖ ^ 2) := by
  have d1 : ‖x - xs‖ ^ 2 / α - ‖x1 - xs‖ ^ 2 / α = 2 * ⟪x - xs, g⟫ - α * ‖g‖ ^ 2 := by
    rw [hx1]; exact dist_drop_x x xs g hα
  have d2 : ‖y - ys‖ ^ 2 / β - ‖y1 - ys‖ ^ 2 / β = -(2 * ⟪h, y - ys⟫) - β * ‖h‖ ^ 2 := by
    rw [hy1]; exact dist_drop_y y ys h hβ
  have i1 : -⟪x - xs, g⟫ ≤ f xs q - f x q := by
    have t := H.cvx x xs q
    rw [← hg, ← neg_sub x xs, inner_neg_right, real_inner_comm] at t
    exact t
  have i2 : -⟪x1 - xs, g1⟫ ≤ f xs q1 - f x1 q1 := by
    have t := H.cvx x1 xs q1
    rw [← hg1, ← neg_sub x1 xs, inner_neg_right, real_inner_comm] at t
    exact t
  have i3 : f p ys - f p y ≤ -⟪h, y - ys⟫ := by
    have t := H.ccv p y ys
    rw [← hh, ← neg_sub y ys, inner_neg_right] at t
    exact t
  have i4 : f xs ys ≤ f p ys := H.saddle_x p
  have i5 : f xs q ≤ f xs ys := H.saddle_y q
  have i6 : f xs q1 ≤ f xs ys := H.saddle_y q1
  have i7 : γ * α * ⟪gx (p, q), g⟫ ≤ f x q - f p q := by
    have t := H.cvx p x q
    have e : x - p = (γ * α) • g := by rw [hp]; module
    rw [e, inner_smul_right] at t
    exact t
  have i8 : (δ - 1) * β * ⟪gy (p, q), v⟫ ≤ f p q - f p y := by
    have t := H.ccv p q y
    have e : y - q = -(((δ - 1) * β) • v) := by rw [hq]; module
    rw [e, inner_neg_right, inner_smul_right] at t
    linarith only [t]
  have i9 : (γ - 1) * α * ⟪gx (p, y), g⟫ ≤ f x1 y - f p y := by
    have t := H.cvx p x1 y
    have e : x1 - p = ((γ - 1) * α) • g := by rw [hx1, hp]; module
    rw [e, inner_smul_right] at t
    exact t
  have i10 : δ * β * ⟪gy (x1, q1), h⟫ ≤ f x1 q1 - f x1 y := by
    have t := H.ccv x1 q1 y
    have e : y - q1 = -((δ * β) • h) := by rw [hq1, hy1]; module
    rw [e, inner_neg_right, inner_smul_right] at t
    linarith only [t]
  have A1 := mul_le_mul_of_nonneg_left (add_le_add i7 i8) (show (0 : ℝ) ≤ 2 - γ by linarith)
  have A2 := mul_le_mul_of_nonneg_left (add_le_add i9 i10) (show (0 : ℝ) ≤ γ by linarith)
  linarith only [A1, A2, d1, d2, i1, i2, i3, i4, i5, i6]

lemma inner_bounds_points (H : Hyp f gx gy Lx Ly Lxy xs ys) {γ δ α β : ℝ}
    (hγ : 1 < γ) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (x : E) (y v q : F) (g p : E) (h : F) (x1 : E) (y1 q1 : F)
    (hq : q = y + ((δ - 1) * β) • v) (hg : g = gx (x, q)) (hp : p = x - (γ * α) • g)
    (hh : h = gy (p, y)) (hx1 : x1 = x - α • g) (hy1 : y1 = y + β • h)
    (hq1 : q1 = y1 + ((δ - 1) * β) • h) :
    (1 - Lx * (γ * α)) * ‖g‖ ^ 2 ≤ ⟪gx (p, q), g⟫ ∧
    ⟪h, v⟫ - Ly * ((δ - 1) * β) * ‖v‖ ^ 2 ≤ ⟪gy (p, q), v⟫ ∧
    -(‖h‖ ^ 2 + ‖v‖ ^ 2) / 2 ≤ ⟪h, v⟫ ∧
    ‖g‖ ^ 2 - (Lx * (γ * α) * ‖g‖ + Lxy * ((δ - 1) * β) * ‖v‖) * ‖g‖ ≤ ⟪gx (p, y), g⟫ ∧
    ‖h‖ ^ 2 - (Ly * (δ * β) * ‖h‖ + Lxy * ((γ - 1) * α) * ‖g‖) * ‖h‖ ≤ ⟪gy (x1, q1), h⟫ := by
  have hγα : 0 < γ * α := mul_pos (by linarith) hα
  have hdβ : 0 ≤ (δ - 1) * β := mul_nonneg (by linarith) hβ.le
  have hcα : 0 ≤ (γ - 1) * α := mul_nonneg (by linarith) hα.le
  have hδβ : 0 ≤ δ * β := mul_nonneg (by linarith) hβ.le
  have npx : ‖p - x‖ = γ * α * ‖g‖ := by
    have e : p - x = -((γ * α) • g) := by rw [hp]; module
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγα]
  have nqy : ‖q - y‖ = (δ - 1) * β * ‖v‖ := by
    have e : q - y = ((δ - 1) * β) • v := by rw [hq]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hdβ]
  have nyq : ‖y - q‖ = (δ - 1) * β * ‖v‖ := by rw [norm_sub_rev, nqy]
  have nx1p : ‖x1 - p‖ = (γ - 1) * α * ‖g‖ := by
    have e : x1 - p = ((γ - 1) * α) • g := by rw [hx1, hp]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcα]
  have nq1y : ‖q1 - y‖ = δ * β * ‖h‖ := by
    have e : q1 - y = (δ * β) • h := by rw [hq1, hy1]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδβ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have t : ‖gx (p, q) - g‖ ≤ Lx * (γ * α * ‖g‖) := by
      have t0 := H.lxx p x q
      rw [← hg, npx] at t0
      exact t0
    have s := inner_lower (gx (p, q)) g _ t
    linarith only [s]
  · have t : ‖gy (p, q) - h‖ ≤ Ly * ((δ - 1) * β * ‖v‖) := by
      have t0 := H.lyy p q y
      rw [← hh, nqy] at t0
      exact t0
    have e : ⟪gy (p, q), v⟫ = ⟪h, v⟫ + ⟪gy (p, q) - h, v⟫ := by
      rw [inner_sub_left]; ring
    have a1 := abs_real_inner_le_norm (gy (p, q) - h) v
    have a2 := neg_abs_le ⟪gy (p, q) - h, v⟫
    have a3 := mul_le_mul_of_nonneg_right t (norm_nonneg v)
    rw [e]
    linarith only [a1, a2, a3]
  · have t := norm_add_sq_real h v
    have t0 := sq_nonneg ‖h + v‖
    linarith only [t, t0]
  · have t : ‖gx (p, y) - g‖ ≤ Lx * (γ * α) * ‖g‖ + Lxy * ((δ - 1) * β) * ‖v‖ := by
      have t1 := H.lxy p y q
      have t2 := H.lxx p x q
      rw [nyq] at t1
      rw [← hg, npx] at t2
      calc ‖gx (p, y) - g‖ = ‖(gx (p, y) - gx (p, q)) + (gx (p, q) - g)‖ := by
            congr 1; abel
        _ ≤ ‖gx (p, y) - gx (p, q)‖ + ‖gx (p, q) - g‖ := norm_add_le _ _
        _ ≤ Lx * (γ * α) * ‖g‖ + Lxy * ((δ - 1) * β) * ‖v‖ := by linarith only [t1, t2]
    exact inner_lower (gx (p, y)) g _ t
  · have t : ‖gy (x1, q1) - h‖ ≤ Ly * (δ * β) * ‖h‖ + Lxy * ((γ - 1) * α) * ‖g‖ := by
      have t1 := H.lyy x1 q1 y
      have t2 := H.lyx x1 p y
      rw [nq1y] at t1
      rw [← hh, nx1p] at t2
      calc ‖gy (x1, q1) - h‖ = ‖(gy (x1, q1) - gy (x1, y)) + (gy (x1, y) - h)‖ := by
            congr 1; abel
        _ ≤ ‖gy (x1, q1) - gy (x1, y)‖ + ‖gy (x1, y) - h‖ := norm_add_le _ _
        _ ≤ Ly * (δ * β) * ‖h‖ + Lxy * ((γ - 1) * α) * ‖g‖ := by linarith only [t1, t2]
    exact inner_lower (gy (x1, q1)) h _ t

lemma lower_arith {X Y N A B I Fq D gn γ α β θ Lx Lxy : ℝ}
    (hX : X ^ 2 = α * A) (hY : Y ^ 2 = β * B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX0 : 0 ≤ X) (hgn : 0 ≤ gn) (hLxy : 0 ≤ Lxy)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2)
    (k0 : gn ≤ Lx * X + Lxy * (Y + D * N)) (k1 : I ≤ X * gn) (k4 : Fq ≤ I)
    (e1 : (Lx + Lxy) * α ≤ 1 / 16) (e2 : Lxy * β ≤ 1 / 16) (e3 : Lxy * D ^ 2 ≤ θ * β) :
    (A + B) / 2 ≤ A + B - I - (γ - 1) * Fq + θ * β * N ^ 2 := by
  have m1 := mul_le_mul_of_nonneg_left k4 (show (0 : ℝ) ≤ γ - 1 by linarith)
  have m2a := mul_le_mul_of_nonneg_left k1 (show (0 : ℝ) ≤ γ by linarith)
  have m2b : 0 ≤ (2 - γ) * (X * gn) := mul_nonneg (by linarith) (mul_nonneg hX0 hgn)
  have m3 := mul_le_mul_of_nonneg_left k0 hX0
  have m4 := mul_nonneg hLxy (sq_nonneg (X - Y))
  have m5 := mul_nonneg hLxy (sq_nonneg (X - D * N))
  have m6 := mul_le_mul_of_nonneg_right e1 hA
  have m7 := mul_le_mul_of_nonneg_right e2 hB
  have m8 := mul_le_mul_of_nonneg_right e3 (sq_nonneg N)
  have hX' : (2 * Lx + 2 * Lxy) * X ^ 2 = (2 * Lx + 2 * Lxy) * (α * A) := by rw [hX]
  have hY' : Lxy * Y ^ 2 = Lxy * (β * B) := by rw [hY]
  linarith only [m1, m2a, m2b, m3, m4, m5, m6, m7, m8, hX', hY', hA, hB]

lemma upper_arith {X Y A B I F0 gn γ α β Lx Ly Lxy : ℝ}
    (hX : X ^ 2 = α * A) (hY : Y ^ 2 = β * B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hY0 : 0 ≤ Y) (hgn : 0 ≤ gn) (hLx : 0 ≤ Lx) (hLxy : 0 ≤ Lxy)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2)
    (u1 : F0 ≤ I) (u2 : -F0 ≤ Y * gn) (u3 : gn ≤ Lxy * X + Ly * Y)
    (e1 : (Lx + Lxy) * α ≤ 1 / 16) (e2 : (Ly + Lxy) * β ≤ 1 / 16) :
    A + B - I - (γ - 1) * F0 ≤ 9 / 8 * (A + B) := by
  have m1 := mul_le_mul_of_nonneg_left u2 (show (0 : ℝ) ≤ γ by linarith)
  have m2 : 0 ≤ (2 - γ) * (Y * gn) := mul_nonneg (by linarith) (mul_nonneg hY0 hgn)
  have m3 := mul_le_mul_of_nonneg_left u3 hY0
  have m4 := mul_nonneg hLxy (sq_nonneg (X - Y))
  have m6 := mul_le_mul_of_nonneg_right e1 hA
  have m7 := mul_le_mul_of_nonneg_right e2 hB
  have m8 : 0 ≤ Lx * (α * A) := by rw [← hX]; exact mul_nonneg hLx (sq_nonneg X)
  have hX' : Lxy * X ^ 2 = Lxy * (α * A) := by rw [hX]
  have hY' : (2 * Ly + Lxy) * Y ^ 2 = (2 * Ly + Lxy) * (β * B) := by rw [hY]
  have m9 : 0 ≤ Lxy * (β * B) := by rw [← hY]; exact mul_nonneg hLxy (sq_nonneg Y)
  linarith only [m1, m2, m3, m4, m6, m7, m8, m9, hX', hY', hA, hB, u1]

end Points

section Machine

variable (f : E → F → ℝ) (gx : E × F → E) (gy : E × F → F) (γ δ α β : ℝ) (xs : E) (ys : F)

noncomputable def extra (s : E × F × F) : F := s.2.1 + ((δ - 1) * β) • s.2.2

noncomputable def gradX (s : E × F × F) : E := gx (s.1, extra δ β s)

noncomputable def predict (s : E × F × F) : E := s.1 - (γ * α) • gradX gx δ β s

noncomputable def gradY (s : E × F × F) : F := gy (predict gx γ δ α β s, s.2.1)

noncomputable def next (s : E × F × F) : E × F × F :=
  (s.1 - α • gradX gx δ β s, s.2.1 + β • gradY gx gy γ δ α β s, gradY gx gy γ δ α β s)

noncomputable def energy (s : E × F × F) : ℝ :=
  ‖s.1 - xs‖ ^ 2 / α + ‖s.2.1 - ys‖ ^ 2 / β - ⟪s.1 - xs, gradX gx δ β s⟫
    - (γ - 1) * (f s.1 (extra δ β s) - f xs ys)
    + ((2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8) * β * ‖s.2.2‖ ^ 2

noncomputable def progress (s : E × F × F) : ℝ :=
  ‖gradX gx δ β s‖ ^ 2 + ‖gradY gx gy γ δ α β s‖ ^ 2 + ‖s.2.2‖ ^ 2

end Machine

section Bounds

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F} {Lx Ly Lxy : ℝ} {xs : E} {ys : F}
  {γ δ α β : ℝ}

theorem step_decrease (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (hLy : 0 ≤ Ly) (hLxy : 0 ≤ Lxy)
    (c1 : Lx * γ ^ 2 * α ≤ (γ - 1) / 4) (c2 : γ * δ ^ 2 * Ly * β ≤ (γ - 1) / 4)
    (c3 : γ ^ 2 * δ ^ 2 * Lxy ^ 2 * (α * β) ≤ 1 / 16) (s : E × F × F) :
    (γ - 1) / 4 * (α * ‖gradX gx δ β s‖ ^ 2 + β * ‖gradY gx gy γ δ α β s‖ ^ 2) ≤
      energy f gx γ δ α β xs ys s - energy f gx γ δ α β xs ys (next gx gy γ δ α β s) := by
  have hd := energy_drop_points H hγ hγ2 hα hβ (θ := (2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8)
    s.1 s.2.1 s.2.2 (extra δ β s) (gradX gx δ β s) (predict gx γ δ α β s)
    (gradY gx gy γ δ α β s) (next gx gy γ δ α β s).1 (next gx gy γ δ α β s).2.1
    (extra δ β (next gx gy γ δ α β s)) (gradX gx δ β (next gx gy γ δ α β s))
    rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨b1, b2, bhv, b3, b4⟩ := inner_bounds_points H hγ hδ hα hβ
    s.1 s.2.1 s.2.2 (extra δ β s) (gradX gx δ β s) (predict gx γ δ α β s)
    (gradY gx gy γ δ α β s) (next gx gy γ δ α β s).1 (next gx gy γ δ α β s).2.1
    (extra δ β (next gx gy γ δ α β s)) rfl rfl rfl rfl rfl rfl rfl
  have ha := arith_core hγ hγ2 hδ hα hβ hLy hLxy (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    c1 c2 c3 b1 b2 bhv b3 b4
  exact le_trans ha hd

theorem energy_lower (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (hLxy : 0 ≤ Lxy)
    (e1 : (Lx + Lxy) * α ≤ 1 / 16) (e2 : Lxy * β ≤ 1 / 16)
    (e3 : Lxy * ((δ - 1) * β) ^ 2 ≤ ((2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8) * β)
    (s : E × F × F) :
    (‖s.1 - xs‖ ^ 2 / α + ‖s.2.1 - ys‖ ^ 2 / β) / 2 ≤ energy f gx γ δ α β xs ys s := by
  have hX : ‖s.1 - xs‖ ^ 2 = α * (‖s.1 - xs‖ ^ 2 / α) := by field_simp
  have hY : ‖s.2.1 - ys‖ ^ 2 = β * (‖s.2.1 - ys‖ ^ 2 / β) := by field_simp
  have hA : 0 ≤ ‖s.1 - xs‖ ^ 2 / α := by positivity
  have hB : 0 ≤ ‖s.2.1 - ys‖ ^ 2 / β := by positivity
  have hD : 0 ≤ (δ - 1) * β := mul_nonneg (by linarith) hβ.le
  have k0 : ‖gradX gx δ β s‖ ≤
      Lx * ‖s.1 - xs‖ + Lxy * (‖s.2.1 - ys‖ + (δ - 1) * β * ‖s.2.2‖) := by
    have t1 : ‖gradX gx δ β s - gx (xs, extra δ β s)‖ ≤ Lx * ‖s.1 - xs‖ :=
      H.lxx s.1 xs (extra δ β s)
    have t2 := H.lxy xs (extra δ β s) ys
    rw [H.sx, sub_zero] at t2
    have e : extra δ β s - ys = (s.2.1 - ys) + ((δ - 1) * β) • s.2.2 := by
      unfold extra; abel
    have e2 : ‖((δ - 1) * β) • s.2.2‖ = (δ - 1) * β * ‖s.2.2‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hD]
    have t3 := norm_add_le (s.2.1 - ys) (((δ - 1) * β) • s.2.2)
    rw [← e, e2] at t3
    have t4 := mul_le_mul_of_nonneg_left t3 hLxy
    have t5 := norm_add_le (gradX gx δ β s - gx (xs, extra δ β s)) (gx (xs, extra δ β s))
    rw [sub_add_cancel] at t5
    linarith only [t1, t2, t4, t5]
  have k1 : ⟪s.1 - xs, gradX gx δ β s⟫ ≤ ‖s.1 - xs‖ * ‖gradX gx δ β s‖ :=
    real_inner_le_norm _ _
  have k4 : f s.1 (extra δ β s) - f xs ys ≤ ⟪s.1 - xs, gradX gx δ β s⟫ := by
    have t : ⟪gradX gx δ β s, xs - s.1⟫ ≤ f xs (extra δ β s) - f s.1 (extra δ β s) :=
      H.cvx s.1 xs (extra δ β s)
    rw [← neg_sub s.1 xs, inner_neg_right, real_inner_comm] at t
    have t2 := H.saddle_y (extra δ β s)
    linarith only [t, t2]
  exact lower_arith hX hY hA hB (norm_nonneg _) (norm_nonneg _) hLxy hγ hγ2 k0 k1 k4 e1 e2 e3

theorem energy_init (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hα : 0 < α) (hβ : 0 < β)
    (hLx : 0 ≤ Lx) (hLxy : 0 ≤ Lxy)
    (e1 : (Lx + Lxy) * α ≤ 1 / 16) (e2 : (Ly + Lxy) * β ≤ 1 / 16) (x0 : E) (y0 : F) :
    energy f gx γ δ α β xs ys (x0, y0, 0) ≤
      9 / 8 * (‖x0 - xs‖ ^ 2 / α + ‖y0 - ys‖ ^ 2 / β) := by
  have hq : extra δ β (x0, y0, (0 : F)) = y0 := by simp [extra]
  have hX : ‖x0 - xs‖ ^ 2 = α * (‖x0 - xs‖ ^ 2 / α) := by field_simp
  have hY : ‖y0 - ys‖ ^ 2 = β * (‖y0 - ys‖ ^ 2 / β) := by field_simp
  have hA : 0 ≤ ‖x0 - xs‖ ^ 2 / α := by positivity
  have hB : 0 ≤ ‖y0 - ys‖ ^ 2 / β := by positivity
  have u1 : f x0 y0 - f xs ys ≤ ⟪x0 - xs, gx (x0, y0)⟫ := by
    have t := H.cvx x0 xs y0
    rw [← neg_sub x0 xs, inner_neg_right, real_inner_comm] at t
    have t2 := H.saddle_y y0
    linarith only [t, t2]
  have u2 : -(f x0 y0 - f xs ys) ≤ ‖y0 - ys‖ * ‖gy (x0, y0)‖ := by
    have t := H.ccv x0 y0 ys
    have t2 := H.saddle_x x0
    have t3 := real_inner_le_norm (gy (x0, y0)) (ys - y0)
    rw [norm_sub_rev ys y0] at t3
    linarith only [t, t2, t3]
  have u3 : ‖gy (x0, y0)‖ ≤ Lxy * ‖x0 - xs‖ + Ly * ‖y0 - ys‖ := by
    have t1 := H.lyx x0 xs y0
    have t2 := H.lyy xs y0 ys
    rw [H.sy, sub_zero] at t2
    have t5 := norm_add_le (gy (x0, y0) - gy (xs, y0)) (gy (xs, y0))
    rw [sub_add_cancel] at t5
    linarith only [t1, t2, t5]
  have key := upper_arith hX hY hA hB (norm_nonneg _) (norm_nonneg _) hLx hLxy hγ hγ2
    u1 u2 u3 e1 e2
  show ‖x0 - xs‖ ^ 2 / α + ‖y0 - ys‖ ^ 2 / β
      - ⟪x0 - xs, gx (x0, extra δ β (x0, y0, (0 : F)))⟫
      - (γ - 1) * (f x0 (extra δ β (x0, y0, (0 : F))) - f xs ys)
      + ((2 - γ) * (δ - 1) / 2 + 3 * (γ - 1) / 8) * β * ‖(0 : F)‖ ^ 2 ≤ _
  rw [hq, norm_zero]
  linarith only [key]

theorem residual_le (H : Hyp f gx gy Lx Ly Lxy xs ys)
    (hγ : 1 < γ) (hδ : 1 ≤ δ) (hα : 0 < α) (hβ : 0 < β)
    (r1 : Lxy * ((δ - 1) * β) ≤ 1 / 16) (r2 : Lxy * (γ * α) ≤ 1 / 8) (s : E × F × F) :
    ‖gx (s.1, s.2.1)‖ ^ 2 + ‖gy (s.1, s.2.1)‖ ^ 2 ≤ 5 / 4 * progress gx gy γ δ α β s := by
  have hD : 0 ≤ (δ - 1) * β := mul_nonneg (by linarith) hβ.le
  have hγα : 0 < γ * α := mul_pos (by linarith) hα
  have a1 : ‖gx (s.1, s.2.1)‖ ≤ ‖gradX gx δ β s‖ + ‖s.2.2‖ / 16 := by
    have t := H.lxy s.1 s.2.1 (extra δ β s)
    have e : s.2.1 - extra δ β s = -(((δ - 1) * β) • s.2.2) := by unfold extra; abel
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hD] at t
    have t' : ‖gx (s.1, s.2.1) - gradX gx δ β s‖ ≤ Lxy * ((δ - 1) * β * ‖s.2.2‖) := t
    have t2 := norm_add_le (gx (s.1, s.2.1) - gradX gx δ β s) (gradX gx δ β s)
    rw [sub_add_cancel] at t2
    have t3 := mul_le_mul_of_nonneg_right r1 (norm_nonneg s.2.2)
    linarith only [t', t2, t3]
  have a2 : ‖gy (s.1, s.2.1)‖ ≤ ‖gradY gx gy γ δ α β s‖ + ‖gradX gx δ β s‖ / 8 := by
    have t := H.lyx s.1 (predict gx γ δ α β s) s.2.1
    have e : s.1 - predict gx γ δ α β s = (γ * α) • gradX gx δ β s := by unfold predict; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hγα] at t
    have t' : ‖gy (s.1, s.2.1) - gradY gx gy γ δ α β s‖ ≤
        Lxy * (γ * α * ‖gradX gx δ β s‖) := t
    have t2 := norm_add_le (gy (s.1, s.2.1) - gradY gx gy γ δ α β s) (gradY gx gy γ δ α β s)
    rw [sub_add_cancel] at t2
    have t3 := mul_le_mul_of_nonneg_right r2 (norm_nonneg (gradX gx δ β s))
    linarith only [t', t2, t3]
  have b1 := pow_le_pow_left₀ (norm_nonneg _) a1 2
  have b2 := pow_le_pow_left₀ (norm_nonneg _) a2 2
  have c1 := sq_nonneg (‖gradX gx δ β s‖ - ‖s.2.2‖)
  have c2 := sq_nonneg (‖gradY gx gy γ δ α β s‖ - ‖gradX gx δ β s‖)
  have c3 := sq_nonneg ‖s.2.2‖
  have c4 := sq_nonneg ‖gradX gx δ β s‖
  have c5 := sq_nonneg ‖gradY gx gy γ δ α β s‖
  unfold progress
  linarith only [b1, b2, c1, c2, c3, c4, c5]

end Bounds

end OracleTemplate.BlockSaddle
