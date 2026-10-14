import LongTails.Proofs.TwoSidedPLEnvelope

open Set InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.TwoSidedPL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def potential (f : E → F → ℝ) (L : ℝ) (z x : E) (y : F) : ℝ :=
  fhat f L z x y - 2 * psi f L y z + 2 * envelope f L z

def xgrad (gx : E → F → E) (L : ℝ) (z x : E) (y : F) : E := gx x y + (2 * L) • (x - z)

lemma step_scalar {L τ μy A B G Q k n1 n2 W X Y m Vd : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hs : 3 * L * τ ≤ 1) (hμ : 0 < μy) (hμL : μy ≤ L) (hG0 : 0 ≤ G) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W)
    (hbase : (τ - 3 * L / 2 * τ ^ 2) * A ^ 2 + m - 3 * L / 2 * τ ^ 2 * n1 ^ 2 + τ / 32 * B ^ 2 -
      τ / 32 * G ^ 2 - 5 * L / 2 * (τ ^ 2 / 1024) * (Q ^ 2 + n2 ^ 2) +
      L * (2 * (τ * μy / 6144) - (τ * μy / 6144) ^ 2) * k ^ 2 -
      4 * L * (τ * μy / 6144) * k * W ≤ Vd)
    (hW : W ≤ X + Y + 2 * (τ * μy / 6144) * k) (hX : L * μy * X ^ 2 ≤ 2 * B ^ 2)
    (hY : Y ^ 2 ≤ 2 * (τ / 32) ^ 2 * (Q ^ 2 + n2 ^ 2)) (hQ : Q ≤ B + G)
    (hG : G ≤ 4 / 3 * A + L * τ * n1) :
    τ / 3 * A ^ 2 + τ / 64 * B ^ 2 + L * τ * μy / 24576 * k ^ 2 + m -
      2 * L * τ ^ 2 * (n1 ^ 2 + n2 ^ 2) ≤ Vd := by
  set β := τ * μy / 6144 with hβdef
  have hβ : 0 < β := by positivity
  have hτμ : τ * μy ≤ 1 / 3 := by
    have := mul_le_mul_of_nonneg_left hμL hτ.le
    linarith
  have hβs : β ≤ 1 / 18432 := by rw [hβdef]; linarith
  have hLβ : 0 < L * β := by positivity
  have s1 : 4 * L * β * k * W ≤ L * β / 2 * k ^ 2 + 8 * L * β * W ^ 2 := by
    linarith [mul_nonneg hLβ.le (sq_nonneg (k - 4 * W))]
  have s2 : W ^ 2 ≤ 3 * X ^ 2 + 3 * Y ^ 2 + 12 * β ^ 2 * k ^ 2 := by
    have h0 : W ^ 2 ≤ (X + Y + 2 * β * k) ^ 2 := pow_le_pow_left₀ hW0 hW 2
    linarith [sq_nonneg (X - Y), sq_nonneg (X - 2 * β * k), sq_nonneg (Y - 2 * β * k)]
  have s3 : 8 * L * β * W ^ 2 ≤ 8 * L * β * (3 * X ^ 2 + 3 * Y ^ 2 + 12 * β ^ 2 * k ^ 2) :=
    mul_le_mul_of_nonneg_left s2 (by positivity)
  have s4 : 24 * L * β * X ^ 2 ≤ τ / 128 * B ^ 2 := by
    have e : 24 * L * β * X ^ 2 = τ / 256 * (L * μy * X ^ 2) := by rw [hβdef]; ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ τ / 256)]
  have s5 : 24 * L * β * Y ^ 2 ≤ L * τ ^ 2 / 100000 * (Q ^ 2 + n2 ^ 2) := by
    have h1 : 24 * L * β * Y ^ 2 ≤ 24 * L * β * (2 * (τ / 32) ^ 2 * (Q ^ 2 + n2 ^ 2)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    have hLt : 0 ≤ L * τ ^ 2 := by positivity
    have h2 : (L * τ ^ 2) * (48 * β / 1024) ≤ (L * τ ^ 2) * (1 / 100000) :=
      mul_le_mul_of_nonneg_left (by linarith) hLt
    have e : 24 * L * β * (2 * (τ / 32) ^ 2 * (Q ^ 2 + n2 ^ 2)) =
        (L * τ ^ 2) * (48 * β / 1024) * (Q ^ 2 + n2 ^ 2) := by ring
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ Q ^ 2 + n2 ^ 2)
    rw [e] at h1
    linarith
  have s6 : Q ^ 2 ≤ 2 * B ^ 2 + 2 * G ^ 2 := by
    have := pow_le_pow_left₀ hQ0 hQ 2
    linarith [sq_nonneg (B - G)]
  have s7 : G ^ 2 ≤ 32 / 9 * A ^ 2 + 2 * L ^ 2 * τ ^ 2 * n1 ^ 2 := by
    have := pow_le_pow_left₀ hG0 hG 2
    linarith [sq_nonneg (4 / 3 * A - L * τ * n1)]
  have hcτ : 5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000 ≤ τ / 1024 := by
    have e : 5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000 = (L * τ) * (τ * (5 / 2048 + 1 / 100000)) := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_right (by linarith : L * τ ≤ 1 / 3)
      (by positivity : (0 : ℝ) ≤ τ * (5 / 2048 + 1 / 100000))
    linarith
  have hc0 : 0 ≤ 5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000 := by positivity
  have hcn : 5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000 ≤ 2 * L * τ ^ 2 := by
    have : 0 ≤ L * τ ^ 2 := by positivity
    linarith
  have p1 : (5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000) * Q ^ 2 ≤
      (5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000) * (2 * B ^ 2 + 2 * G ^ 2) :=
    mul_le_mul_of_nonneg_left s6 hc0
  have p2 : (5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000) * (2 * B ^ 2 + 2 * G ^ 2) ≤
      τ / 1024 * (2 * B ^ 2 + 2 * G ^ 2) :=
    mul_le_mul_of_nonneg_right hcτ (by positivity)
  have p3 : 17 * τ / 512 * G ^ 2 ≤ 17 * τ / 512 * (32 / 9 * A ^ 2 + 2 * L ^ 2 * τ ^ 2 * n1 ^ 2) :=
    mul_le_mul_of_nonneg_left s7 (by positivity)
  have p4 : L * τ ^ 2 * A ^ 2 ≤ 1 / 3 * (τ * A ^ 2) := by
    have : L * τ ^ 2 * A ^ 2 = (L * τ) * (τ * A ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p5 : L ^ 2 * τ ^ 3 * n1 ^ 2 ≤ 1 / 3 * (L * τ ^ 2 * n1 ^ 2) := by
    have : L ^ 2 * τ ^ 3 * n1 ^ 2 = (L * τ) * (L * τ ^ 2 * n1 ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p6 : (5 * L / 2 * (τ ^ 2 / 1024) + L * τ ^ 2 / 100000) * n2 ^ 2 ≤ 2 * L * τ ^ 2 * n2 ^ 2 :=
    mul_le_mul_of_nonneg_right hcn (sq_nonneg _)
  have p7 : L * β ^ 2 * k ^ 2 ≤ 1 / 18432 * (L * β * k ^ 2) := by
    have : L * β ^ 2 * k ^ 2 = β * (L * β * k ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hβs (by positivity)
  have p8 : L * β ^ 3 * k ^ 2 ≤ 1 / 18432 * (L * β ^ 2 * k ^ 2) := by
    have : L * β ^ 3 * k ^ 2 = β * (L * β ^ 2 * k ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hβs (by positivity)
  have hT : L * τ * μy / 24576 = L * β / 4 := by rw [hβdef]; ring
  rw [hT]
  have q1 : 0 ≤ τ * A ^ 2 := by positivity
  have q2 : 0 ≤ τ * B ^ 2 := by positivity
  have q3 : 0 ≤ L * τ ^ 2 * n1 ^ 2 := by positivity
  have q4 : 0 ≤ L * τ ^ 2 * n2 ^ 2 := by positivity
  have q5 : 0 ≤ L * β * k ^ 2 := by positivity
  have q6 : 0 ≤ L * β ^ 2 * k ^ 2 := by positivity
  have q7 : 0 ≤ τ * G ^ 2 := by positivity
  linarith

lemma Hyp.dist_next [ProperSpace E] {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F}
    {L μx μy : ℝ} (H : Hyp f gx gy L μx μy) {τ : ℝ} (hτ : 0 < τ) (hs : 3 * L * τ ≤ 1)
    (x z e1 x' : E) (y : F) (hx' : x' = x - τ • (xgrad gx L z x y + e1)) :
    L * ‖xhat f L y z - x'‖ ≤ 4 / 3 * ‖xgrad gx L z x y‖ + L * τ * ‖e1‖ := by
  have hd : L * ‖x - xhat f L y z‖ ≤ ‖xgrad gx L z x y‖ := H.dist_xhat z x y
  have hL := H.hL
  have e : xhat f L y z - x' = -(x - xhat f L y z) + τ • xgrad gx L z x y + τ • e1 := by
    rw [hx']; simp only [smul_add]; abel
  have hn : ‖xhat f L y z - x'‖ ≤ ‖x - xhat f L y z‖ + τ * ‖xgrad gx L z x y‖ + τ * ‖e1‖ := by
    rw [e]
    have : ‖-(x - xhat f L y z) + τ • xgrad gx L z x y + τ • e1‖ ≤
        ‖-(x - xhat f L y z)‖ + ‖τ • xgrad gx L z x y‖ + ‖τ • e1‖ := norm_add₃_le
    simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hτ] using this
  have hA : L * τ * ‖xgrad gx L z x y‖ ≤ 1 / 3 * ‖xgrad gx L z x y‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have := mul_le_mul_of_nonneg_left hn hL.le
  linarith

set_option maxHeartbeats 2000000 in
lemma Hyp.step [ProperSpace E] {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F}
    {L μx μy : ℝ} (H : Hyp f gx gy L μx μy) {τ : ℝ} (hτ : 0 < τ) (hs : 3 * L * τ ≤ 1)
    (x z e1 x' z' : E) (y e2 y' : F) (hx' : x' = x - τ • (xgrad gx L z x y + e1))
    (hy' : y' = y + (τ / 32) • (gy x' y + e2)) (hz' : z' = z + (τ * μy / 6144) • (x' - z)) :
    τ / 3 * ‖xgrad gx L z x y‖ ^ 2 + τ / 64 * ‖gy (xhat f L y z) y‖ ^ 2 +
        L * τ * μy / 24576 * ‖x' - z‖ ^ 2 +
      ((τ - 3 * L * τ ^ 2) * ⟪xgrad gx L z x y, e1⟫ +
        ⟪(τ / 16) • gy (xhat f L y z) y - (τ / 32 + 5 * L * τ ^ 2 / 1024) • gy x' y, e2⟫) -
      2 * L * τ ^ 2 * (‖e1‖ ^ 2 + ‖e2‖ ^ 2) ≤
      potential f L z x y - potential f L z' x' y' := by
  have hL := H.hL
  have hμ := H.hμy
  have hμL := H.hμyL
  have hτμ : τ * μy ≤ 1 / 3 := by
    have := mul_le_mul_of_nonneg_left hμL hτ.le
    linarith
  simp only [potential, psi, envelope, phat, fhat]
  set h := xgrad gx L z x y with hh
  set g := gy (xhat f L y z) y with hg
  set q := gy x' y with hq
  set β := τ * μy / 6144 with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have dx : x' - x = -(τ • (h + e1)) := by rw [hx']; abel
  have dy : y' - y = (τ / 32) • (q + e2) := by rw [hy']; abel
  have dz : z' - z = β • (x' - z) := by rw [hz']; abel
  have dxz : x' - z' = (1 - β) • (x' - z) := by rw [hz']; module
  have hA := H.fhat_upper z x x' y
  have hgx : gx x y + (2 * L) • (x - z) = h := rfl
  rw [hgx, dx] at hA
  have iA : ⟪h, -(τ • (h + e1))⟫ = -τ * ‖h‖ ^ 2 - τ * ⟪h, e1⟫ := by
    rw [inner_neg_right, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]; ring
  have nA : ‖-(τ • (h + e1))‖ ^ 2 = τ ^ 2 * (‖h‖ ^ 2 + 2 * ⟪h, e1⟫ + ‖e1‖ ^ 2) := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real]
  rw [iA, nA] at hA
  simp only [fhat] at hA
  have hB := H.upper_y x' y y'
  rw [dy] at hB
  have iB : ⟪q, (τ / 32) • (q + e2)⟫ = τ / 32 * (‖q‖ ^ 2 + ⟪q, e2⟫) := by
    rw [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
  have nB : ‖(τ / 32) • (q + e2)‖ ^ 2 = (τ / 32) ^ 2 * (‖q‖ ^ 2 + 2 * ⟪q, e2⟫ + ‖e2‖ ^ 2) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real]
  rw [iB, nB] at hB
  have hC : L * ‖x' - z'‖ ^ 2 = L * ((1 - β) ^ 2 * ‖x' - z‖ ^ 2) := by
    rw [dxz, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hD := H.psi_lower y y' z
  rw [dy] at hD
  have iD : ⟪g, (τ / 32) • (q + e2)⟫ = τ / 32 * (⟪g, q⟫ + ⟪g, e2⟫) := by
    rw [inner_smul_right, inner_add_right]
  rw [iD, nB] at hD
  simp only [psi, fhat] at hD
  have hE := H.xhat_min y' z (xhat f L y' z')
  simp only [psi, fhat] at hE
  have hF := H.xbar_min z' (xbar f L z)
  simp only [envelope, phat] at hF
  have nz : ‖z' - z‖ = β * ‖x' - z‖ := by rw [dz, norm_smul, Real.norm_eq_abs, abs_of_pos hβ0]
  have c1 : L * ‖xhat f L y' z' - z'‖ ^ 2 = L * (‖xhat f L y' z' - z‖ ^ 2 -
      2 * ⟪xhat f L y' z' - z, z' - z⟫ + (β * ‖x' - z‖) ^ 2) := by
    have : xhat f L y' z' - z' = (xhat f L y' z' - z) - (z' - z) := by abel
    rw [this, norm_sub_sq_real, nz]
  have c2 : L * ‖xbar f L z - z'‖ ^ 2 = L * (‖xbar f L z - z‖ ^ 2 -
      2 * ⟪xbar f L z - z, z' - z⟫ + (β * ‖x' - z‖) ^ 2) := by
    have : xbar f L z - z' = (xbar f L z - z) - (z' - z) := by abel
    rw [this, norm_sub_sq_real, nz]
  have cross : 4 * L * ⟪xhat f L y' z' - z, z' - z⟫ - 4 * L * ⟪xbar f L z - z, z' - z⟫ =
      4 * L * ⟪xhat f L y' z' - xbar f L z, z' - z⟫ := by
    rw [← mul_sub, ← inner_sub_left]; congr 2; abel
  have hcs : 4 * L * ⟪xhat f L y' z' - xbar f L z, z' - z⟫ ≤
      4 * L * (‖xbar f L z - xhat f L y' z'‖ * (β * ‖x' - z‖)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← nz, norm_sub_rev]; exact real_inner_le_norm _ _
  have gsq : τ / 32 * ‖g - q‖ ^ 2 = τ / 32 * (‖g‖ ^ 2 - 2 * ⟪g, q⟫ + ‖q‖ ^ 2) := by
    rw [norm_sub_sq_real g q]
  have hgap : ‖g - q‖ ≤ L * ‖xhat f L y z - x'‖ := by
    have := H.lipy (xhat f L y z) x' y y
    simpa using this
  have hdn := H.dist_next hτ hs x z e1 x' y hx'
  have hG : ‖g - q‖ ≤ 4 / 3 * ‖h‖ + L * τ * ‖e1‖ := hgap.trans hdn
  have hQ : ‖q‖ ≤ ‖g‖ + ‖g - q‖ := by
    have := norm_sub_le g (g - q)
    simpa using this
  have hXl := H.xhat_sub_xbar y z
  have hWb : ‖xbar f L z - xhat f L y' z'‖ ≤
      ‖xhat f L y z - xbar f L z‖ + ‖y' - y‖ + 2 * β * ‖x' - z‖ := by
    have h1 := H.xhat_lip y y' z z'
    have e : xbar f L z - xhat f L y' z' =
        (xbar f L z - xhat f L y z) + (xhat f L y z - xhat f L y' z') := by abel
    have h2 := norm_add_le (xbar f L z - xhat f L y z) (xhat f L y z - xhat f L y' z')
    have h3 : ‖xbar f L z - xhat f L y z‖ = ‖xhat f L y z - xbar f L z‖ := norm_sub_rev _ _
    have h4 : ‖y - y'‖ = ‖y' - y‖ := norm_sub_rev _ _
    have h5 : ‖z - z'‖ = β * ‖x' - z‖ := by rw [norm_sub_rev, nz]
    rw [e]
    linarith
  have hYb : ‖y' - y‖ ^ 2 ≤ 2 * (τ / 32) ^ 2 * (‖q‖ ^ 2 + ‖e2‖ ^ 2) := by
    rw [dy, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le q e2) 2
    have h2 : ‖q + e2‖ ^ 2 ≤ 2 * (‖q‖ ^ 2 + ‖e2‖ ^ 2) := by
      linarith [sq_nonneg (‖q‖ - ‖e2‖)]
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (τ / 32))
    linarith
  have im : ⟪(τ / 16) • g - (τ / 32 + 5 * L * τ ^ 2 / 1024) • q, e2⟫ =
      τ / 16 * ⟪g, e2⟫ - (τ / 32 + 5 * L * τ ^ 2 / 1024) * ⟪q, e2⟫ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  rw [im]
  have hbase : (τ - 3 * L / 2 * τ ^ 2) * ‖h‖ ^ 2 +
      ((τ - 3 * L * τ ^ 2) * ⟪h, e1⟫ +
        (τ / 16 * ⟪g, e2⟫ - (τ / 32 + 5 * L * τ ^ 2 / 1024) * ⟪q, e2⟫)) -
      3 * L / 2 * τ ^ 2 * ‖e1‖ ^ 2 + τ / 32 * ‖g‖ ^ 2 - τ / 32 * ‖g - q‖ ^ 2 -
      5 * L / 2 * (τ ^ 2 / 1024) * (‖q‖ ^ 2 + ‖e2‖ ^ 2) +
      L * (2 * β - β ^ 2) * ‖x' - z‖ ^ 2 -
      4 * L * β * ‖x' - z‖ * ‖xbar f L z - xhat f L y' z'‖ ≤
      f x y + L * ‖x - z‖ ^ 2 - 2 * (f (xhat f L y z) y + L * ‖xhat f L y z - z‖ ^ 2) +
        2 * (maxValue f (xbar f L z) + L * ‖xbar f L z - z‖ ^ 2) -
      (f x' y' + L * ‖x' - z'‖ ^ 2 - 2 * (f (xhat f L y' z') y' + L * ‖xhat f L y' z' - z'‖ ^ 2) +
        2 * (maxValue f (xbar f L z') + L * ‖xbar f L z' - z'‖ ^ 2)) := by
    linarith
  linarith [step_scalar (Vd := f x y + L * ‖x - z‖ ^ 2 - 2 * (f (xhat f L y z) y + L * ‖xhat f L y z - z‖ ^ 2) +
        2 * (maxValue f (xbar f L z) + L * ‖xbar f L z - z‖ ^ 2) -
      (f x' y' + L * ‖x' - z'‖ ^ 2 - 2 * (f (xhat f L y' z') y' + L * ‖xhat f L y' z' - z'‖ ^ 2) +
        2 * (maxValue f (xbar f L z') + L * ‖xbar f L z' - z'‖ ^ 2)))
    hL hτ hs hμ hμL (norm_nonneg _) (norm_nonneg q) (norm_nonneg _) hbase hWb hXl hYb hQ hG]

end OracleTemplate.TwoSidedPL
