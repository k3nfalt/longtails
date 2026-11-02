import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.ComparisonTrustBounds

structure Abs where
  L : ℝ
  ρ : ℝ
  ε : ℝ
  G : ℝ
  γ : ℝ
  r : ℝ
  n : ℝ
  B0 : ℝ

structure Abs.OK (A : Abs) : Prop where
  hL : 0 < A.L
  hρ : 0 < A.ρ
  hε : 0 < A.ε
  hG : 0 ≤ A.G
  hγ : 0 < A.γ
  hr : 0 < A.r
  hρr : A.ρ * A.r = A.γ / 4
  hγr : A.γ * A.r = A.ε / 4
  hn : 0 ≤ A.n
  hB0 : A.B0 = 2 + A.n + A.L / A.γ + A.G / A.ε

namespace Abs

variable {A : Abs}

noncomputable def LA (A : Abs) : ℝ := 2 * A.L + 4 * A.γ
noncomputable def a (A : Abs) : ℝ := Real.sqrt (A.γ / A.LA)
noncomputable def Rad (A : Abs) : ℝ := 4 * A.G / A.γ + A.r
noncomputable def σ (A : Abs) : ℝ := A.a * A.ε ^ 2 / (576000 * A.LA * A.Rad)
noncomputable def K (A : Abs) : ℝ := A.σ / (8 * A.Rad)
noncomputable def τ0 (A : Abs) : ℝ := A.K * A.ε / (6 * (A.L ^ 2 + A.γ ^ 2))
noncomputable def δ (A : Abs) : ℝ := 1 / (4 * 10 ^ 20 * A.B0 ^ 11)
noncomputable def τ (A : Abs) : ℝ := 4 * A.r / (10 ^ 12 * A.B0 ^ 6)

lemma κ_le (h : A.OK) : A.L / A.γ ≤ A.B0 := by
  rw [h.hB0]
  have := div_nonneg h.hG h.hε.le
  linarith [h.hn]

lemma g_le (h : A.OK) : A.G / A.ε ≤ A.B0 := by
  rw [h.hB0]
  have := div_nonneg h.hL.le h.hγ.le
  linarith [h.hn]

lemma n_le (h : A.OK) : A.n ≤ A.B0 := by
  rw [h.hB0]
  have := div_nonneg h.hL.le h.hγ.le
  have := div_nonneg h.hG h.hε.le
  linarith

lemma two_le (h : A.OK) : 2 ≤ A.B0 := by
  rw [h.hB0]
  have := div_nonneg h.hL.le h.hγ.le
  have := div_nonneg h.hG h.hε.le
  linarith [h.hn]

lemma B0_pos (h : A.OK) : 0 < A.B0 := by linarith [two_le h]

lemma LA_pos (h : A.OK) : 0 < A.LA := by unfold LA; linarith [h.hL, h.hγ]

lemma γ_le_LA (h : A.OK) : 4 * A.γ ≤ A.LA := by unfold LA; linarith [h.hL]

lemma LA_le (h : A.OK) : A.LA ≤ 4 * A.B0 * A.γ := by
  unfold LA
  have hk := κ_le h
  have h2 := two_le h
  have : A.L ≤ A.B0 * A.γ := by rwa [div_le_iff₀ h.hγ] at hk
  nlinarith [h.hγ]

lemma a_sq (h : A.OK) : A.a ^ 2 = A.γ / A.LA := by
  unfold a
  rw [Real.sq_sqrt (div_nonneg h.hγ.le (LA_pos h).le)]

lemma a_pos (h : A.OK) : 0 < A.a := Real.sqrt_pos.mpr (div_pos h.hγ (LA_pos h))

lemma a_le_one (h : A.OK) : A.a ≤ 1 := by
  unfold a
  rw [Real.sqrt_le_one]
  rw [div_le_one (LA_pos h)]
  linarith [γ_le_LA h, h.hγ]

lemma a_lower (h : A.OK) : 1 / (2 * A.B0) ≤ A.a := by
  have h2 := two_le h
  have hL4 : A.LA ≤ (2 * A.B0) ^ 2 * A.γ := by
    have := LA_le h
    have : 4 * A.B0 * A.γ ≤ 4 * A.B0 ^ 2 * A.γ := by
      nlinarith [mul_nonneg (mul_nonneg (B0_pos h).le h.hγ.le) (show (0:ℝ) ≤ A.B0 - 1 by linarith)]
    nlinarith
  have hsq : (1 / (2 * A.B0)) ^ 2 ≤ A.a ^ 2 := by
    rw [a_sq h, div_pow, one_pow, div_le_div_iff₀ (by positivity) (LA_pos h)]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (a_pos h).le (by norm_num)).mp hsq

lemma Rad_pos (h : A.OK) : 0 < A.Rad := by
  unfold Rad
  have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) h.hG) h.hγ.le
  linarith [h.hr]

lemma r_le_Rad (h : A.OK) : A.r ≤ A.Rad := by
  unfold Rad
  have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) h.hG) h.hγ.le
  linarith

lemma ε_eq (h : A.OK) : A.ε = 4 * A.γ * A.r := by linarith [h.hγr]

lemma Rad_le (h : A.OK) : A.Rad ≤ 17 * A.B0 * A.r := by
  unfold Rad
  have hg := g_le h
  have : A.G ≤ A.B0 * A.ε := by rwa [div_le_iff₀ h.hε] at hg
  have hε := ε_eq h
  have : 4 * A.G / A.γ ≤ 16 * A.B0 * A.r := by
    rw [div_le_iff₀ h.hγ]
    rw [hε] at this
    nlinarith
  have : A.r ≤ A.B0 * A.r := by nlinarith [h.hr, two_le h]
  linarith

lemma G_le_Rad (h : A.OK) : A.G / A.γ ≤ A.Rad / 4 := by
  unfold Rad
  have : A.G / A.γ = (4 * A.G / A.γ) / 4 := by ring
  linarith [h.hr]

lemma LARad_ge (h : A.OK) : A.ε ≤ A.LA * A.Rad := by
  have h1 := γ_le_LA h
  have h2 := r_le_Rad h
  have := ε_eq h
  have : 4 * A.γ * A.r ≤ A.LA * A.Rad := mul_le_mul h1 h2 h.hr.le (LA_pos h).le
  linarith

lemma σ_pos (h : A.OK) : 0 < A.σ := by
  unfold σ
  have := a_pos h; have := LA_pos h; have := Rad_pos h; have := h.hε
  positivity

lemma σ_le (h : A.OK) : A.σ ≤ A.ε / 576000 := by
  unfold σ
  have ha := a_le_one h
  have hl := LARad_ge h
  rw [div_le_div_iff₀ (by have := LA_pos h; have := Rad_pos h; positivity) (by norm_num)]
  have : 0 ≤ A.ε ^ 2 := sq_nonneg _
  have : A.a * A.ε ^ 2 ≤ A.ε ^ 2 := by nlinarith [a_pos h]
  have : A.ε ^ 2 * 576000 ≤ A.ε * (576000 * A.LA * A.Rad) := by nlinarith [h.hε]
  nlinarith

lemma K_pos (h : A.OK) : 0 < A.K := by
  unfold K; have := σ_pos h; have := Rad_pos h; positivity

lemma K_le (h : A.OK) : A.K ≤ A.γ / 80 := by
  unfold K
  rw [div_le_div_iff₀ (by have := Rad_pos h; positivity) (by norm_num)]
  have h1 := σ_le h
  have h2 := r_le_Rad h
  have := ε_eq h
  have : A.ε / 576000 * 80 ≤ A.γ * (8 * A.Rad) := by
    rw [this]
    nlinarith [h.hγ, h.hr]
  nlinarith

lemma K_lower (h : A.OK) : A.γ / (10 ^ 9 * A.B0 ^ 4) ≤ A.K := by
  unfold K σ
  have ha := a_lower h
  have hLA := LA_le h
  have hRad := Rad_le h
  have h2 := two_le h
  have hε := ε_eq h
  have hγ := h.hγ
  have hr := h.hr
  have hB := B0_pos h
  have hRp := Rad_pos h
  have hLAp := LA_pos h
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hε]
  have e1 : A.γ * (576000 * A.LA * A.Rad * (8 * A.Rad)) ≤
      A.γ * (576000 * (4 * A.B0 * A.γ) * (17 * A.B0 * A.r) * (8 * (17 * A.B0 * A.r))) := by
    gcongr
  have e2 : 1 / (2 * A.B0) * (4 * A.γ * A.r) ^ 2 * (10 ^ 9 * A.B0 ^ 4) ≤
      A.a * (4 * A.γ * A.r) ^ 2 * (10 ^ 9 * A.B0 ^ 4) := by gcongr
  have e3 : A.γ * (576000 * (4 * A.B0 * A.γ) * (17 * A.B0 * A.r) * (8 * (17 * A.B0 * A.r))) ≤
      1 / (2 * A.B0) * (4 * A.γ * A.r) ^ 2 * (10 ^ 9 * A.B0 ^ 4) := by
    field_simp
    ring_nf
    nlinarith [pow_pos hB 3, pow_pos hγ 2, pow_pos hr 2, mul_pos (pow_pos hγ 2) (pow_pos hr 2),
      mul_pos (mul_pos (pow_pos hγ 2) (pow_pos hr 2)) (pow_pos hB 3)]
  linarith

noncomputable def Λ (A : Abs) : ℝ := Real.log A.B0
noncomputable def m (A : Abs) : ℕ := ⌈18 * A.Λ⌉₊ + 72
noncomputable def N (A : Abs) : ℕ := ⌈Real.sqrt (2 * A.L / A.γ + 4) * (8 * A.Λ + 40)⌉₊

lemma Λ_pos (h : A.OK) : 0 < A.Λ := Real.log_pos (by linarith [two_le h])

lemma Λ_ge (h : A.OK) : Real.log 2 ≤ A.Λ := Real.log_le_log (by norm_num) (two_le h)

lemma pow_m (h : A.OK) : 2 ^ 72 * A.B0 ^ 12 ≤ (2 : ℝ) ^ A.m := by
  have hB := two_le h
  have hΛ := Λ_pos h
  have hm : 18 * A.Λ + 72 ≤ (A.m : ℝ) := by
    unfold m
    push_cast
    linarith [Nat.le_ceil (18 * A.Λ)]
  have h1 : (2 : ℝ) ^ (18 * A.Λ + 72) ≤ (2 : ℝ) ^ (A.m : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hm
  rw [Real.rpow_natCast] at h1
  have h2 : (2 : ℝ) ^ (18 * A.Λ + 72) = A.B0 ^ (18 * Real.log 2) * 2 ^ (72 : ℝ) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by linarith : (0 : ℝ) < A.B0)]
    unfold Λ
    ring_nf
  have h3 : A.B0 ^ (12 : ℝ) ≤ A.B0 ^ (18 * Real.log 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Real.log_two_gt_d9])
  rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h3
  have h72 : (2 : ℝ) ^ (72 : ℝ) = 2 ^ (72 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
  rw [h72] at h2
  have : (2 : ℝ) ^ 72 * A.B0 ^ 12 ≤ A.B0 ^ (18 * Real.log 2) * 2 ^ 72 := by
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) 72]
  linarith

lemma pow_q (h : A.OK) : (2 / 3 : ℝ) ^ A.m ≤ 1 / (2 ^ 36 * A.B0 ^ 6) := by
  have hm := pow_m h
  have hB := B0_pos h
  have hsq : ((3 / 2 : ℝ) ^ A.m) ^ 2 ≥ (2 : ℝ) ^ A.m := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hge : 2 ^ 36 * A.B0 ^ 6 ≤ (3 / 2 : ℝ) ^ A.m := by
    have : (2 ^ 36 * A.B0 ^ 6) ^ 2 ≤ ((3 / 2 : ℝ) ^ A.m) ^ 2 := by
      have : (2 ^ 36 * A.B0 ^ 6 : ℝ) ^ 2 = 2 ^ 72 * A.B0 ^ 12 := by ring
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
  rw [div_pow, show (2 : ℝ) ^ A.m / 3 ^ A.m = 1 / (3 / 2) ^ A.m by
    rw [div_pow]; field_simp]
  exact one_div_le_one_div_of_le (by positivity) hge

lemma decay_N (h : A.OK) : (1 - A.a) ^ A.N ≤ Real.exp (-40) / A.B0 ^ 8 := by
  have ha := a_pos h
  have ha1 := a_le_one h
  have hB := B0_pos h
  have hΛ := Λ_pos h
  have hprod : A.a * Real.sqrt (2 * A.L / A.γ + 4) = 1 := by
    have : 2 * A.L / A.γ + 4 = A.LA / A.γ := by unfold LA; field_simp [h.hγ.ne']
    rw [this]
    unfold a
    rw [← Real.sqrt_mul (div_nonneg h.hγ.le (LA_pos h).le), div_mul_div_comm, mul_comm A.γ,
      div_self (by have := LA_pos h; have := h.hγ; positivity), Real.sqrt_one]
  have hN : 8 * A.Λ + 40 ≤ A.a * A.N := by
    have := Nat.le_ceil (Real.sqrt (2 * A.L / A.γ + 4) * (8 * A.Λ + 40))
    have h2 := mul_le_mul_of_nonneg_left this ha.le
    unfold N
    rw [← mul_assoc, hprod, one_mul] at h2
    exact h2
  have h1 : (1 - A.a) ^ A.N ≤ Real.exp (-A.a) ^ A.N :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-A.a)]) _
  rw [← Real.exp_nat_mul] at h1
  refine h1.trans ?_
  have : Real.exp (A.N * -A.a) ≤ Real.exp (-(8 * A.Λ + 40)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  refine this.trans (le_of_eq ?_)
  have hE : Real.exp (8 * A.Λ) = A.B0 ^ 8 := by
    unfold Λ
    rw [show (8 : ℝ) * Real.log A.B0 = Real.log (A.B0 ^ 8) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [show -(8 * A.Λ + 40) = -40 - 8 * A.Λ by ring, Real.exp_sub, hE]

lemma τ0_pos (h : A.OK) : 0 < A.τ0 := by
  unfold τ0; have := K_pos h; have := h.hε; have := h.hγ; positivity

lemma Lτ0 (h : A.OK) : A.L * A.τ0 ≤ A.ε / 4 := by
  unfold τ0
  have hK := K_le h
  have hKp := K_pos h
  have hγ := h.hγ
  have hL := h.hL
  have hε := h.hε
  rw [show A.L * (A.K * A.ε / (6 * (A.L ^ 2 + A.γ ^ 2))) =
    A.ε * (A.L * A.K / (6 * (A.L ^ 2 + A.γ ^ 2))) by ring]
  have : A.L * A.K / (6 * (A.L ^ 2 + A.γ ^ 2)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (A.L - A.γ)]
  nlinarith

lemma δ_pos (h : A.OK) : 0 < A.δ := by unfold δ; have := B0_pos h; positivity

lemma δ_le (h : A.OK) : A.δ ≤ 1 / (300 * A.B0) := by
  unfold δ
  have hB := two_le h
  apply one_div_le_one_div_of_le (by positivity)
  have : A.B0 ≤ A.B0 ^ 11 := by
    calc A.B0 = A.B0 ^ 1 := (pow_one _).symm
      _ ≤ A.B0 ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
  nlinarith

lemma δ_half (h : A.OK) : A.δ ≤ 1 / 2 := by
  have := δ_le h
  have hB := two_le h
  have : 1 / (300 * A.B0) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  linarith

lemma ρτsq (h : A.OK) : A.ρ * A.τ ^ 2 = A.ε / (10 ^ 24 * A.B0 ^ 12) := by
  unfold τ
  have hB := B0_pos h
  have h1 : A.ρ * A.r ^ 2 = A.ε / 16 := by
    have : A.ρ * A.r ^ 2 = (A.ρ * A.r) * A.r := by ring
    rw [this, h.hρr]; linarith [h.hγr]
  rw [div_pow, mul_pow, show (10 ^ 12 * A.B0 ^ 6 : ℝ) ^ 2 = 10 ^ 24 * A.B0 ^ 12 by ring]
  rw [show A.ρ * (4 ^ 2 * A.r ^ 2 / (10 ^ 24 * A.B0 ^ 12)) =
    16 * (A.ρ * A.r ^ 2) / (10 ^ 24 * A.B0 ^ 12) by ring, h1]
  ring

lemma sqrt_n_le (h : A.OK) (hn1 : 1 ≤ A.n) : Real.sqrt A.n ≤ A.B0 := by
  have hn := n_le h
  have h1 := hn1
  calc Real.sqrt A.n ≤ A.n := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
    _ ≤ A.B0 := hn

lemma sqrt_n_pos (hn1 : 1 ≤ A.n) : 0 < Real.sqrt A.n := Real.sqrt_pos.mpr (by linarith)

lemma hζ (h : A.OK) (hn1 : 1 ≤ A.n) : (A.n + 2) * (9 * A.ρ * A.τ ^ 2 / 2) ≤
    A.ε / 2 / (2 * Real.sqrt A.n) := by
  have hρτ := ρτsq h
  have hB := two_le h
  have hs := sqrt_n_le h hn1
  have hsp := sqrt_n_pos hn1
  have hn2 : A.n + 2 ≤ 2 * A.B0 := by linarith [n_le h]
  rw [show 9 * A.ρ * A.τ ^ 2 / 2 = 9 / 2 * (A.ρ * A.τ ^ 2) by ring, hρτ,
    le_div_iff₀ (by positivity)]
  have hε := h.hε
  have hB12 : A.B0 ^ 2 ≤ A.B0 ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
  rw [show (A.n + 2) * (9 / 2 * (A.ε / (10 ^ 24 * A.B0 ^ 12))) * (2 * Real.sqrt A.n) =
    A.ε * ((A.n + 2) * Real.sqrt A.n * 9 / (10 ^ 24 * A.B0 ^ 12)) by field_simp]
  have : (A.n + 2) * Real.sqrt A.n * 9 / (10 ^ 24 * A.B0 ^ 12) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (A.n + 2) * Real.sqrt A.n ≤ 2 * A.B0 * A.B0 :=
      mul_le_mul hn2 hs hsp.le (by linarith)
    nlinarith
  nlinarith

lemma hδ (h : A.OK) (hn1 : 1 ≤ A.n) : 2 * Real.sqrt A.n * (2 / 2 ^ A.m +
    2 * Real.sqrt A.n * (9 * A.ρ * A.τ ^ 2 / 2) / (A.ε / 2)) ≤ A.δ := by
  have hρτ := ρτsq h
  have hB := two_le h
  have hs := sqrt_n_le h hn1
  have hsp := sqrt_n_pos hn1
  have hm := pow_m h
  have hε := h.hε
  have hB12 : A.B0 ^ 11 ≤ A.B0 ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h1 : 2 * Real.sqrt A.n * (2 / 2 ^ A.m) ≤ A.δ / 2 := by
    unfold δ
    rw [show 2 * Real.sqrt A.n * (2 / 2 ^ A.m) = 4 * Real.sqrt A.n / 2 ^ A.m by ring,
      div_le_iff₀ (by positivity)]
    have : 4 * Real.sqrt A.n ≤ 4 * A.B0 := by linarith
    have : 1 / (4 * 10 ^ 20 * A.B0 ^ 11) / 2 * (2 ^ 72 * A.B0 ^ 12) ≤
        1 / (4 * 10 ^ 20 * A.B0 ^ 11) / 2 * 2 ^ A.m := by gcongr
    have : 4 * A.B0 ≤ 1 / (4 * 10 ^ 20 * A.B0 ^ 11) / 2 * (2 ^ 72 * A.B0 ^ 12) := by
      rw [show 1 / (4 * 10 ^ 20 * A.B0 ^ 11) / 2 * (2 ^ 72 * A.B0 ^ 12) =
        2 ^ 72 / (8 * 10 ^ 20) * (A.B0 ^ 12 / A.B0 ^ 11) by field_simp; norm_num]
      rw [show A.B0 ^ 12 / A.B0 ^ 11 = A.B0 by field_simp]
      nlinarith
    linarith
  have h2 : 2 * Real.sqrt A.n * (2 * Real.sqrt A.n * (9 * A.ρ * A.τ ^ 2 / 2) / (A.ε / 2)) ≤
      A.δ / 2 := by
    unfold δ
    rw [show 9 * A.ρ * A.τ ^ 2 / 2 = 9 / 2 * (A.ρ * A.τ ^ 2) by ring, hρτ]
    rw [show 2 * Real.sqrt A.n * (2 * Real.sqrt A.n * (9 / 2 * (A.ε / (10 ^ 24 * A.B0 ^ 12))) /
      (A.ε / 2)) = 36 * (Real.sqrt A.n) ^ 2 / (10 ^ 24 * A.B0 ^ 12) by field_simp; ring]
    rw [Real.sq_sqrt (by linarith [h.hn])]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hn := n_le h
    have : 36 * A.n * (4 * 10 ^ 20 * A.B0 ^ 11 * 2) ≤ 36 * A.B0 * (8 * 10 ^ 20 * A.B0 ^ 11) := by
      have : 0 ≤ A.B0 ^ 11 := by positivity
      nlinarith
    have e : 1 / (4 * 10 ^ 20 * A.B0 ^ 11) * (10 ^ 24 * A.B0 ^ 12) = 2500 * A.B0 := by
      field_simp; ring
    rw [e]
    nlinarith
  linarith

lemma hK (h : A.OK) : 2 * A.L ^ 2 * A.τ0 / A.ε + 3 * A.G * A.δ / A.τ0 + A.ρ * A.τ0 ≤ A.K := by
  have hKp := K_pos h
  have hKl := K_lower h
  have hτ0 := τ0_pos h
  have hγ := h.hγ
  have hε := h.hε
  have hL := h.hL
  have hB := two_le h
  have hden : 0 < A.L ^ 2 + A.γ ^ 2 := by positivity
  have e1 : 2 * A.L ^ 2 * A.τ0 / A.ε ≤ A.K / 3 := by
    unfold τ0
    rw [div_le_iff₀ hε]
    rw [show 2 * A.L ^ 2 * (A.K * A.ε / (6 * (A.L ^ 2 + A.γ ^ 2))) =
      A.K * A.ε / 3 * (A.L ^ 2 / (A.L ^ 2 + A.γ ^ 2)) by field_simp; ring]
    have : A.L ^ 2 / (A.L ^ 2 + A.γ ^ 2) ≤ 1 := by
      rw [div_le_one hden]; nlinarith
    have : 0 ≤ A.K * A.ε / 3 := by positivity
    nlinarith
  have e3 : A.ρ * A.τ0 ≤ A.K / 6 := by
    unfold τ0
    have hργ : A.ρ * A.ε = A.γ ^ 2 := by
      have : A.ε = 4 * A.γ * A.r := ε_eq h
      rw [this]
      have : A.ρ * A.r = A.γ / 4 := h.hρr
      nlinarith
    rw [show A.ρ * (A.K * A.ε / (6 * (A.L ^ 2 + A.γ ^ 2))) =
      A.K / 6 * (A.ρ * A.ε / (A.L ^ 2 + A.γ ^ 2)) by field_simp, hργ]
    have : A.γ ^ 2 / (A.L ^ 2 + A.γ ^ 2) ≤ 1 := by
      rw [div_le_one hden]; nlinarith
    nlinarith
  have e2 : 3 * A.G * A.δ / A.τ0 ≤ A.K / 3 := by
    rw [div_le_iff₀ hτ0]
    unfold τ0 δ
    have hg := g_le h
    have hG : A.G ≤ A.B0 * A.ε := by rwa [div_le_iff₀ hε] at hg
    have hk := κ_le h
    have hLγ : A.L ≤ A.B0 * A.γ := by rwa [div_le_iff₀ hγ] at hk
    have hLsq : A.L ^ 2 + A.γ ^ 2 ≤ 2 * A.B0 ^ 2 * A.γ ^ 2 := by
      have h1 : A.L ^ 2 ≤ (A.B0 * A.γ) ^ 2 := pow_le_pow_left₀ hL.le hLγ 2
      have h2 : 1 ≤ A.B0 ^ 2 := by nlinarith
      have h3 : A.γ ^ 2 ≤ A.B0 ^ 2 * A.γ ^ 2 := by nlinarith [sq_nonneg A.γ]
      nlinarith
    have hK2 : (A.γ / (10 ^ 9 * A.B0 ^ 4)) ^ 2 ≤ A.K ^ 2 :=
      pow_le_pow_left₀ (by positivity) hKl 2
    rw [show A.K / 3 * (A.K * A.ε / (6 * (A.L ^ 2 + A.γ ^ 2))) =
      A.K ^ 2 * A.ε / (18 * (A.L ^ 2 + A.γ ^ 2)) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    have lhs : 3 * A.G * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) * (18 * (A.L ^ 2 + A.γ ^ 2)) ≤
        3 * (A.B0 * A.ε) * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) * (18 * (2 * A.B0 ^ 2 * A.γ ^ 2)) := by
      gcongr
    have rhs : (A.γ / (10 ^ 9 * A.B0 ^ 4)) ^ 2 * A.ε ≤ A.K ^ 2 * A.ε :=
      mul_le_mul_of_nonneg_right hK2 hε.le
    have mid : 3 * (A.B0 * A.ε) * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) * (18 * (2 * A.B0 ^ 2 * A.γ ^ 2)) ≤
        (A.γ / (10 ^ 9 * A.B0 ^ 4)) ^ 2 * A.ε := by
      rw [show 3 * (A.B0 * A.ε) * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) * (18 * (2 * A.B0 ^ 2 * A.γ ^ 2)) =
        A.γ ^ 2 * A.ε * (108 / (4 * 10 ^ 20 * A.B0 ^ 8)) by field_simp; norm_num]
      rw [show (A.γ / (10 ^ 9 * A.B0 ^ 4)) ^ 2 * A.ε = A.γ ^ 2 * A.ε * (1 / (10 ^ 18 * A.B0 ^ 8)) by
        field_simp]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (B0_pos h) 8]
    linarith
  linarith

lemma hrad (h : A.OK) : A.δ ^ 2 * (2 * A.L + A.ρ * A.r) / 2 +
    A.L * (A.r * (2 / 3) ^ A.m) * (2 * A.L + A.ρ * A.r) / A.ε +
    A.ρ * (16 / 63 * A.r + A.r * (2 / 3) ^ A.m) / 2 ≤ A.γ / 16 := by
  have hγ := h.hγ
  have hε := h.hε
  have hr := h.hr
  have hB := two_le h
  have hq := pow_q h
  have hq0 : 0 ≤ (2 / 3 : ℝ) ^ A.m := by positivity
  have hδ := δ_le h
  have hδ0 := δ_pos h
  have hk := κ_le h
  have hLγ : A.L ≤ A.B0 * A.γ := by rwa [div_le_iff₀ hγ] at hk
  have hρr := h.hρr
  have hεe := ε_eq h
  have hden : 2 * A.L + A.ρ * A.r ≤ 3 * A.B0 * A.γ := by rw [hρr]; nlinarith
  have t1 : A.δ ^ 2 * (2 * A.L + A.ρ * A.r) / 2 ≤ A.γ / 200 := by
    have hδ1 : A.δ ≤ 1 := by linarith [δ_half h]
    have : A.δ ^ 2 ≤ A.δ := by nlinarith
    have : A.δ * (3 * A.B0 * A.γ) ≤ A.γ / 100 := by
      have : A.δ * A.B0 ≤ 1 / 300 := by
        rw [le_div_iff₀ (by positivity)] at hδ
        calc A.δ * A.B0 = A.δ * (300 * A.B0) / 300 := by ring
          _ ≤ 1 / 300 := by rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
      nlinarith
    have : 0 ≤ 2 * A.L + A.ρ * A.r := by rw [hρr]; linarith [h.hL]
    nlinarith
  have hqB : (2 / 3 : ℝ) ^ A.m * A.B0 ^ 2 ≤ 1 / 2 ^ 36 := by
    have hB6 : A.B0 ^ 2 ≤ A.B0 ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have := mul_le_mul_of_nonneg_left hB6 hq0
    have : (2 / 3 : ℝ) ^ A.m * A.B0 ^ 6 ≤ 1 / 2 ^ 36 := by
      rw [le_div_iff₀ (by positivity)] at hq
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pow_pos (B0_pos h) 6]
    linarith
  have t2 : A.L * (A.r * (2 / 3) ^ A.m) * (2 * A.L + A.ρ * A.r) / A.ε ≤ A.γ / 200 := by
    rw [div_le_iff₀ hε, hεe]
    have hL0 := h.hL.le
    have : A.L * (2 * A.L + A.ρ * A.r) ≤ 3 * A.B0 ^ 2 * A.γ ^ 2 := by
      calc A.L * (2 * A.L + A.ρ * A.r) ≤ (A.B0 * A.γ) * (3 * A.B0 * A.γ) :=
            mul_le_mul hLγ hden (by rw [hρr]; linarith) (by positivity)
        _ = 3 * A.B0 ^ 2 * A.γ ^ 2 := by ring
    have : A.L * (A.r * (2 / 3) ^ A.m) * (2 * A.L + A.ρ * A.r) ≤
        A.r * (2 / 3) ^ A.m * (3 * A.B0 ^ 2 * A.γ ^ 2) := by
      have : A.L * (A.r * (2 / 3) ^ A.m) * (2 * A.L + A.ρ * A.r) =
          A.r * (2 / 3) ^ A.m * (A.L * (2 * A.L + A.ρ * A.r)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by assumption) (by positivity)
    have : A.r * (2 / 3) ^ A.m * (3 * A.B0 ^ 2 * A.γ ^ 2) ≤ A.γ / 200 * (4 * A.γ * A.r) := by
      have : (2 / 3 : ℝ) ^ A.m * A.B0 ^ 2 * 3 ≤ 4 / 200 := by
        have : (1 : ℝ) / 2 ^ 36 * 3 ≤ 4 / 200 := by norm_num
        nlinarith
      nlinarith [mul_pos hr (pow_pos hγ 2)]
    linarith
  have t3 : A.ρ * (16 / 63 * A.r + A.r * (2 / 3) ^ A.m) / 2 ≤ A.γ * (8 / 252 + 1 / 2 ^ 39) := by
    have : (2 / 3 : ℝ) ^ A.m ≤ 1 / 2 ^ 36 := by
      have : (2 / 3 : ℝ) ^ A.m * 1 ≤ (2 / 3 : ℝ) ^ A.m * A.B0 ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) hq0
      linarith
    rw [show A.ρ * (16 / 63 * A.r + A.r * (2 / 3) ^ A.m) / 2 =
      (A.ρ * A.r) * (16 / 63 + (2 / 3) ^ A.m) / 2 by ring, hρr]
    nlinarith
  have : A.γ / 200 + A.γ / 200 + A.γ * (8 / 252 + 1 / 2 ^ 39) ≤ A.γ / 16 := by
    have : (1 : ℝ) / 200 + 1 / 200 + (8 / 252 + 1 / 2 ^ 39) ≤ 1 / 16 := by norm_num
    nlinarith
  linarith

noncomputable def sR (A : Abs) : ℝ := 4 * A.K * A.Rad + 2 * A.G * A.δ
noncomputable def gm (A : Abs) : ℝ := 2 * A.G + A.LA * A.Rad + A.sR
noncomputable def sl (A : Abs) : ℝ := A.sR * (4 * A.Rad + 2 * A.gm / A.LA)
noncomputable def W (A : Abs) : ℝ := A.Rad + A.gm / A.LA

lemma σ_lower (h : A.OK) : A.ε / (2 * 10 ^ 9 * A.B0 ^ 4) ≤ A.σ := by
  have hK := K_lower h
  have hRad := r_le_Rad h
  have : A.σ = 8 * A.Rad * A.K := by unfold K; field_simp [(Rad_pos h).ne']
  rw [this, ε_eq h]
  have hB := B0_pos h
  have := h.hγ; have := h.hr
  calc 4 * A.γ * A.r / (2 * 10 ^ 9 * A.B0 ^ 4) = 8 * A.r * (A.γ / (10 ^ 9 * A.B0 ^ 4)) / 4 := by
        field_simp; ring
    _ ≤ 8 * A.r * (A.γ / (10 ^ 9 * A.B0 ^ 4)) := by
        have : 0 ≤ 8 * A.r * (A.γ / (10 ^ 9 * A.B0 ^ 4)) := by positivity
        linarith
    _ ≤ 8 * A.Rad * A.K := by
        have : 8 * A.r ≤ 8 * A.Rad := by linarith
        exact mul_le_mul this hK (by positivity) (by linarith [Rad_pos h])

lemma sR_le (h : A.OK) : A.sR ≤ A.σ := by
  unfold sR
  have h1 : 4 * A.K * A.Rad = A.σ / 2 := by unfold K; field_simp [(Rad_pos h).ne']; ring
  have hσ := σ_lower h
  have hg := g_le h
  have hG : A.G ≤ A.B0 * A.ε := by rwa [div_le_iff₀ h.hε] at hg
  have hB := two_le h
  have h2 : 2 * A.G * A.δ ≤ A.σ / 2 := by
    unfold δ
    have : 2 * A.G * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) ≤ 2 * (A.B0 * A.ε) * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) := by
      gcongr
    have : 2 * (A.B0 * A.ε) * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) ≤ A.ε / (2 * 10 ^ 9 * A.B0 ^ 4) / 2 := by
      rw [show 2 * (A.B0 * A.ε) * (1 / (4 * 10 ^ 20 * A.B0 ^ 11)) = A.ε * (1 / (2 * 10 ^ 20 * A.B0 ^ 10)) by
        field_simp; ring]
      rw [show A.ε / (2 * 10 ^ 9 * A.B0 ^ 4) / 2 = A.ε * (1 / (4 * 10 ^ 9 * A.B0 ^ 4)) by
        field_simp; ring]
      apply mul_le_mul_of_nonneg_left _ h.hε.le
      apply one_div_le_one_div_of_le (by positivity)
      have : A.B0 ^ 4 ≤ A.B0 ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith [pow_pos (B0_pos h) 4]
    linarith
  linarith

lemma sR_nonneg (h : A.OK) : 0 ≤ A.sR := by
  unfold sR; have := K_pos h; have := Rad_pos h; have := δ_pos h; have := h.hG; positivity

lemma gm_le (h : A.OK) : A.gm / A.LA ≤ 3 / 2 * A.Rad := by
  unfold gm
  have hLA := LA_pos h
  have hRp := Rad_pos h
  rw [div_le_iff₀ hLA]
  have h1 : 2 * A.G ≤ A.LA * A.Rad / 8 := by
    have := G_le_Rad h
    rw [div_le_iff₀ h.hγ] at this
    have := γ_le_LA h
    have : A.γ * A.Rad ≤ A.LA * A.Rad / 4 := by nlinarith
    linarith
  have h2 : A.sR ≤ A.LA * A.Rad / 4 := by
    have := sR_le h; have := σ_le h; have := LARad_ge h
    have := h.hε
    linarith
  nlinarith

lemma sl_le (h : A.OK) : A.sl ≤ 7 * A.σ * A.Rad := by
  unfold sl
  have := gm_le h
  have hsR := sR_le h
  have h0 := sR_nonneg h
  have hR := Rad_pos h
  have : 4 * A.Rad + 2 * A.gm / A.LA ≤ 7 * A.Rad := by
    have : 2 * A.gm / A.LA = 2 * (A.gm / A.LA) := by ring
    linarith
  have hgm0 : 0 ≤ 4 * A.Rad + 2 * A.gm / A.LA := by
    have : 0 ≤ A.gm := by unfold gm; have := h.hG; have := LA_pos h; positivity
    have := LA_pos h
    have : 0 ≤ 2 * A.gm / A.LA := by positivity
    linarith
  calc A.sR * (4 * A.Rad + 2 * A.gm / A.LA) ≤ A.σ * (7 * A.Rad) :=
        mul_le_mul hsR this hgm0 (σ_pos h).le
    _ = 7 * A.σ * A.Rad := by ring

lemma σRad (h : A.OK) : A.σ * A.Rad = A.a * A.ε ^ 2 / (576000 * A.LA) := by
  unfold σ; field_simp [(Rad_pos h).ne', (LA_pos h).ne']

lemma hslack (h : A.OK) : 8 * A.sl ≤ A.a * A.γ * A.r ^ 2 := by
  have h1 := sl_le h
  have h2 := σRad h
  have hε := ε_eq h
  have hLA := γ_le_LA h
  have ha := a_pos h
  have hLAp := LA_pos h
  have : 56 * (A.a * A.ε ^ 2 / (576000 * A.LA)) ≤ A.a * A.γ * A.r ^ 2 := by
    rw [hε, show 56 * (A.a * (4 * A.γ * A.r) ^ 2 / (576000 * A.LA)) =
      A.a * A.γ * A.r ^ 2 * (A.γ / (4500 / 7 * A.LA)) by field_simp; ring]
    have h3 : A.γ / (4500 / 7 * A.LA) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [h.hγ]
    have h4 : 0 ≤ A.a * A.γ * A.r ^ 2 := by have := h.hγ; positivity
    have := mul_le_mul_of_nonneg_left h3 h4
    linarith
  have h5 : 8 * A.sl ≤ 56 * (A.σ * A.Rad) := by linarith
  rw [h2] at h5
  linarith

lemma hfin2 (h : A.OK) : 5 * A.sl / A.a ≤ (A.ε / 20) ^ 2 / (32 * A.LA) := by
  have h1 := sl_le h
  have h2 := σRad h
  have ha := a_pos h
  have hLA := LA_pos h
  rw [div_le_iff₀ ha]
  have : 5 * A.sl ≤ 35 * (A.a * A.ε ^ 2 / (576000 * A.LA)) := by nlinarith
  have : 35 * (A.a * A.ε ^ 2 / (576000 * A.LA)) ≤ (A.ε / 20) ^ 2 / (32 * A.LA) * A.a := by
    rw [show 35 * (A.a * A.ε ^ 2 / (576000 * A.LA)) = (A.ε / 20) ^ 2 / (32 * A.LA) * A.a * (7 / 9) by
      field_simp; ring]
    have : 0 ≤ (A.ε / 20) ^ 2 / (32 * A.LA) * A.a := by positivity
    nlinarith
  linarith

lemma hfin3 (h : A.OK) : A.sR ≤ A.ε / 20 / 2 := by
  have := sR_le h; have := σ_le h; have := h.hε; linarith

lemma W_le (h : A.OK) : A.W ≤ 4 * A.Rad := by unfold W; linarith [gm_le h, Rad_pos h]

lemma hfin1 (h : A.OK) : (1 - A.a) ^ A.N * (2 * A.G * A.W + (A.LA + A.γ) / 2 * A.W ^ 2) ≤
    (A.ε / 20) ^ 2 / (32 * A.LA) := by
  have hd := decay_N h
  have hW := W_le h
  have hW0 : 0 ≤ A.W := by
    unfold W; have := Rad_pos h; have := LA_pos h
    have : 0 ≤ A.gm := by unfold gm; have := h.hG; have := sR_nonneg h; positivity
    positivity
  have hR := Rad_le h
  have hRp := Rad_pos h
  have hLA := LA_le h
  have hLAp := LA_pos h
  have hg := g_le h
  have hG : A.G ≤ A.B0 * A.ε := by rwa [div_le_iff₀ h.hε] at hg
  have hε := ε_eq h
  have hB := two_le h
  have hγ := h.hγ
  have hr := h.hr
  have hγLA : A.γ ≤ A.LA := by linarith [γ_le_LA h]
  have hC : 2 * A.G * A.W + (A.LA + A.γ) / 2 * A.W ^ 2 ≤ 8 * A.G * A.Rad + 16 * A.LA * A.Rad ^ 2 := by
    have : A.W ^ 2 ≤ 16 * A.Rad ^ 2 := by nlinarith
    have : (A.LA + A.γ) / 2 ≤ A.LA := by linarith
    nlinarith [h.hG]
  have hLR : A.LA * A.Rad ≤ 68 * A.B0 ^ 2 * A.γ * A.r := by
    calc A.LA * A.Rad ≤ (4 * A.B0 * A.γ) * (17 * A.B0 * A.r) := mul_le_mul hLA hR hRp.le (by positivity)
      _ = 68 * A.B0 ^ 2 * A.γ * A.r := by ring
  have hpow : 0 ≤ (1 - A.a) ^ A.N := pow_nonneg (by linarith [a_le_one h]) _
  have hbig : (8 * A.G * A.Rad + 16 * A.LA * A.Rad ^ 2) * (32 * A.LA) ≤
      (A.ε / 20) ^ 2 * (Real.exp 40 * A.B0 ^ 8) := by
    have e1 : A.G * A.Rad * A.LA ≤ A.B0 * (4 * A.γ * A.r) * (68 * A.B0 ^ 2 * A.γ * A.r) := by
      rw [← hε]
      have : A.G * A.Rad * A.LA = A.G * (A.LA * A.Rad) := by ring
      rw [this]
      exact mul_le_mul hG hLR (mul_pos (LA_pos h) (Rad_pos h)).le
        (mul_nonneg (B0_pos h).le h.hε.le)
    have e2 : (A.LA * A.Rad) ^ 2 ≤ (68 * A.B0 ^ 2 * A.γ * A.r) ^ 2 :=
      pow_le_pow_left₀ (mul_pos (LA_pos h) (Rad_pos h)).le hLR 2
    have hexp : (10 : ℝ) ^ 17 ≤ Real.exp 40 := by
      have := Real.add_one_le_exp 40
      have h2 : Real.exp 40 = Real.exp 4 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (54 : ℝ) ≤ Real.exp 4 := by
        have := Real.exp_one_gt_d9
        have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        nlinarith [pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 4]
      rw [h2]
      calc (10 : ℝ) ^ 17 ≤ 54 ^ 10 := by norm_num
        _ ≤ Real.exp 4 ^ 10 := pow_le_pow_left₀ (by norm_num) h3 10
    have hB8 : A.B0 ^ 4 ≤ A.B0 ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hε]
    have : (8 * A.G * A.Rad + 16 * A.LA * A.Rad ^ 2) * (32 * A.LA) =
        256 * (A.G * A.Rad * A.LA) + 512 * (A.LA * A.Rad) ^ 2 := by ring
    rw [this]
    have hγr2 : 0 < A.γ ^ 2 * A.r ^ 2 := by positivity
    have : 256 * (A.B0 * (4 * A.γ * A.r) * (68 * A.B0 ^ 2 * A.γ * A.r)) +
        512 * (68 * A.B0 ^ 2 * A.γ * A.r) ^ 2 ≤ (4 * A.γ * A.r / 20) ^ 2 * (10 ^ 17 * A.B0 ^ 4) := by
      have hB3 : A.B0 ^ 3 ≤ A.B0 ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have : 256 * (A.B0 * (4 * A.γ * A.r) * (68 * A.B0 ^ 2 * A.γ * A.r)) +
          512 * (68 * A.B0 ^ 2 * A.γ * A.r) ^ 2 =
          A.γ ^ 2 * A.r ^ 2 * (69632 * A.B0 ^ 3 + 2367488 * A.B0 ^ 4) := by ring
      rw [this]
      have : (4 * A.γ * A.r / 20) ^ 2 * (10 ^ 17 * A.B0 ^ 4) =
          A.γ ^ 2 * A.r ^ 2 * (4 * 10 ^ 15 * A.B0 ^ 4) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ hγr2.le
      nlinarith [pow_pos (B0_pos h) 4]
    have : (4 * A.γ * A.r / 20) ^ 2 * (10 ^ 17 * A.B0 ^ 4) ≤
        (4 * A.γ * A.r / 20) ^ 2 * (Real.exp 40 * A.B0 ^ 8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hexp hB8 (by positivity) (by positivity)
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc (1 - A.a) ^ A.N * (2 * A.G * A.W + (A.LA + A.γ) / 2 * A.W ^ 2) * (32 * A.LA)
      ≤ (1 - A.a) ^ A.N * ((8 * A.G * A.Rad + 16 * A.LA * A.Rad ^ 2) * (32 * A.LA)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (by positivity)) hpow
    _ ≤ Real.exp (-40) / A.B0 ^ 8 * ((A.ε / 20) ^ 2 * (Real.exp 40 * A.B0 ^ 8)) := by
        have h0 : 0 ≤ (8 * A.G * A.Rad + 16 * A.LA * A.Rad ^ 2) * (32 * A.LA) := by
          have := h.hG; have := Rad_pos h; have := LA_pos h
          exact mul_nonneg (add_nonneg (by positivity) (by positivity)) (by positivity)
        exact mul_le_mul hd hbig h0 (by positivity)
    _ = (A.ε / 20) ^ 2 := by
        rw [Real.exp_neg]
        field_simp

lemma hθ2 (h : A.OK) : A.ε * A.r / 100 ≤ (3 / 32 - A.δ ^ 2 / 16) * A.ε * A.r - A.ρ * A.r ^ 3 / 3072 := by
  have hδ := δ_half h
  have hδ0 := δ_pos h
  have h1 : A.ρ * A.r ^ 3 = A.ε * A.r / 16 := by
    have : A.ρ * A.r ^ 3 = (A.ρ * A.r) * A.r ^ 2 := by ring
    rw [this, h.hρr, ε_eq h]; ring
  rw [h1]
  have : 0 < A.ε * A.r := mul_pos h.hε h.hr
  have : A.δ ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith

lemma hθ1 (h : A.OK) : A.ε * A.r / 100 ≤ A.γ * A.r ^ 2 / 25 := by
  rw [ε_eq h]; apply le_of_eq; ring

end Abs

end LongTails.Proofs.ComparisonTrustBounds
