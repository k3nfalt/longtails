import LongTails.Setups.RhoSmoothConvexFull
import LongTails.Proofs.RhoSmoothHardChain
import LongTails.Proofs.RhoSmoothHardDual
import LongTails.Proofs.AdaptiveLocalizationBounds

namespace LongTails.Proofs.RhoSmoothHardParameters

open LongTails.Setups.RhoSmoothConvexFull RhoSmoothLocal RhoSmoothHardChain

noncomputable def scale (p : Params) : ℝ := (p.L0 / p.L1) ^ (1 / p.ρ)

noncomputable def cap (p : Params) : ℝ := 1024 * scale p / ((p.ρ - 1) * p.L0)

noncomputable def last (p : Params) : ℝ := p.ε / cap p

noncomputable def links (p : Params) : ℕ := ⌊(p.R / (13 * cap p)) ^ 2⌋₊

noncomputable def lip (p : Params) (m : ℕ) : ℝ :=
  curv (p.L0 / 512) (p.L1 / 512) p.ρ (peak m (last p))

noncomputable def kernelRadius (p : Params) (m : ℕ) : ℝ :=
  min (cap p / 2) (scale p / (4 * lip p m))

noncomputable def degree (p : Params) : ℕ := 4 * links p + 80

noncomputable def width (p : Params) : ℝ :=
  16 * p.R + 1632 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * scale p / p.L0

noncomputable def coefficient (p : Params) (m : ℕ) : ℝ :=
  peak m (last p) / width p + p.L0 / 1000

noncomputable def quad (p : Params) : ℝ := (p.L0 * p.R / scale p) ^ 2

section

variable (p : Params) (hp : spec.valid p)
include hp

lemma L0_pos : 0 < p.L0 := hp.1
lemma L1_pos : 0 < p.L1 := hp.2.1
lemma ρ_gt : 1 < p.ρ := hp.2.2.1
lemma ρ_le : p.ρ ≤ 2 := hp.2.2.2.1
lemma R_pos : 0 < p.R := hp.2.2.2.2.1
lemma ε_pos : 0 < p.ε := hp.2.2.2.2.2.1
lemma accuracy_le : 16 * p.ε ≤ p.L0 * p.R ^ 2 := by
  have := hp.2.2.2.2.2.2.1
  linarith
lemma dim_ge : ⌈17592186044416 * (1 + quad p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 6⌉₊ ≤ p.d :=
  hp.2.2.2.2.2.2.2

lemma scale_pos : 0 < scale p := by
  unfold scale
  have := L0_pos p hp
  have := L1_pos p hp
  positivity

lemma scale_rpow : scale p ^ p.ρ * p.L1 = p.L0 := by
  unfold scale
  have h0 : 0 ≤ p.L0 / p.L1 := by have := L0_pos p hp; have := L1_pos p hp; positivity
  rw [← Real.rpow_mul h0, one_div, inv_mul_cancel₀ (by linarith [ρ_gt p hp]), Real.rpow_one]
  field_simp [(L1_pos p hp).ne']

lemma scale_rpow_internal : scale p ^ p.ρ * (p.L1 / 512) = p.L0 / 512 := by
  have := scale_rpow p hp
  linarith

lemma cap_pos : 0 < cap p := by
  unfold cap
  have := scale_pos p hp
  have := L0_pos p hp
  have : 0 < p.ρ - 1 := by linarith [ρ_gt p hp]
  positivity

lemma cap_relation : cap p * (p.ρ - 1) = 2 * scale p / (p.L0 / 512) := by
  unfold cap
  have := L0_pos p hp
  have : 0 < p.ρ - 1 := by linarith [ρ_gt p hp]
  field_simp
  ring

lemma last_pos : 0 < last p := by
  unfold last
  have := ε_pos p hp
  have := cap_pos p hp
  positivity

lemma ratio_sq : (p.R / cap p) ^ 2 ≤ quad p / 1048576 := by
  unfold cap quad
  have hL := L0_pos p hp
  have hs := scale_pos p hp
  have hρ1 : 0 < p.ρ - 1 := by linarith [ρ_gt p hp]
  have hρ2 : p.ρ - 1 ≤ 1 := by linarith [ρ_le p hp]
  have e : (p.R / (1024 * scale p / ((p.ρ - 1) * p.L0))) ^ 2 =
      (p.ρ - 1) ^ 2 * (p.L0 * p.R / scale p) ^ 2 / 1048576 := by
    field_simp
    ring
  rw [e]
  have hq : 0 ≤ (p.L0 * p.R / scale p) ^ 2 := sq_nonneg _
  have hsq : (p.ρ - 1) ^ 2 ≤ 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right hsq hq
  linarith

lemma ratio_sq_eq : (p.R / (13 * cap p)) ^ 2 =
    (p.ρ - 1) ^ 2 * quad p / 177209344 := by
  unfold cap quad
  have hL := L0_pos p hp
  have hs := scale_pos p hp
  have hρ1 : 0 < p.ρ - 1 := by linarith [ρ_gt p hp]
  field_simp
  ring

omit hp in
lemma links_le : (links p : ℝ) ≤ (p.R / (13 * cap p)) ^ 2 :=
  Nat.floor_le (sq_nonneg _)

lemma links_le_quad : (links p : ℝ) ≤ quad p := by
  have h1 := links_le p
  have h2 := ratio_sq_eq p hp
  have hq : 0 ≤ quad p := sq_nonneg _
  have hρ2 : (p.ρ - 1) ^ 2 ≤ 1 := by
    have : 0 < p.ρ - 1 := by linarith [ρ_gt p hp]
    have : p.ρ - 1 ≤ 1 := by linarith [ρ_le p hp]
    nlinarith
  have := mul_le_mul_of_nonneg_right hρ2 hq
  rw [h2] at h1
  linarith

lemma ratio_le : p.R / cap p ≤ 13 * ((links p : ℝ) + 1) := by
  have hc := cap_pos p hp
  have hR := R_pos p hp
  have hl := Nat.lt_floor_add_one ((p.R / (13 * cap p)) ^ 2)
  change (p.R / (13 * cap p)) ^ 2 < (links p : ℝ) + 1 at hl
  have hx : 0 ≤ p.R / (13 * cap p) := by positivity
  have h1 : p.R / (13 * cap p) ≤ (links p : ℝ) + 1 := by
    by_contra h
    push Not at h
    have hl1 : (1 : ℝ) ≤ (links p : ℝ) + 1 := by have := (links p).cast_nonneg (α := ℝ); linarith
    nlinarith
  have e : p.R / cap p = 13 * (p.R / (13 * cap p)) := by field_simp
  rw [e]
  linarith

lemma center_bound (m : ℕ) (hm : m ≤ links p) :
    Real.sqrt m * (6 * cap p + cap p / 2) ≤ p.R / 2 := by
  have hc := cap_pos p hp
  have hR := R_pos p hp
  have h1 : (m : ℝ) ≤ (p.R / (13 * cap p)) ^ 2 :=
    (Nat.cast_le.mpr hm).trans (links_le p)
  have h2 : Real.sqrt m ≤ p.R / (13 * cap p) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact h1
  have e : p.R / (13 * cap p) * (6 * cap p + cap p / 2) = p.R / 2 := by
    field_simp
    ring
  rw [← e]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

lemma lip_pos (m : ℕ) : 0 < lip p m :=
  curv_pos (by have := L0_pos p hp; positivity) (by have := L1_pos p hp; positivity)
    (peak_pos (m := m) (last_pos p hp)).le

lemma kernelRadius_pos (m : ℕ) : 0 < kernelRadius p m := by
  unfold kernelRadius
  have := cap_pos p hp
  have := scale_pos p hp
  have := lip_pos p hp m
  apply lt_min <;> positivity

omit hp in
lemma kernel_margin (m : ℕ) : 2 * kernelRadius p m ≤ cap p := by
  have := min_le_left (cap p / 2) (scale p / (4 * lip p m))
  unfold kernelRadius
  linarith

lemma kernel_lip (m : ℕ) : lip p m * (4 * kernelRadius p m) ≤ scale p := by
  have h := min_le_right (cap p / 2) (scale p / (4 * lip p m))
  have hl := lip_pos p hp m
  unfold kernelRadius
  have := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * lip p m by positivity)
  rw [mul_div_cancel₀ _ (by positivity)] at this
  linarith

lemma internal_curvature (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    curv (p.L0 / 512) (p.L1 / 512) p.ρ (a + lip p m * (4 * kernelRadius p m)) ≤
      (p.L0 + p.L1 * a ^ p.ρ) / 64 := by
  have hs := scale_pos p hp
  have hL0 := L0_pos p hp
  have hL1 := L1_pos p hp
  have hρ1 := ρ_gt p hp
  have hk := kernel_lip p hp m
  have hkn : 0 ≤ lip p m * (4 * kernelRadius p m) := by
    have := lip_pos p hp m
    have := kernelRadius_pos p hp m
    positivity
  have hmono : (a + lip p m * (4 * kernelRadius p m)) ^ p.ρ ≤ (a + scale p) ^ p.ρ :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hsum : (a + scale p) ^ p.ρ ≤ 2 * (a ^ p.ρ + scale p ^ p.ρ) := by
    have h := RhoSmoothHardDual.power_sum_le p.ρ (a / scale p) hρ1.le (ρ_le p hp) (by positivity)
    have e1 : (a + scale p) ^ p.ρ = scale p ^ p.ρ * (1 + a / scale p) ^ p.ρ := by
      rw [← Real.mul_rpow hs.le (by positivity)]
      congr 1
      field_simp
      ring
    have e2 : (a / scale p) ^ p.ρ = a ^ p.ρ / scale p ^ p.ρ := Real.div_rpow ha hs.le _
    have hsρ : 0 < scale p ^ p.ρ := Real.rpow_pos_of_pos hs _
    rw [e1]
    rw [e2] at h
    have := mul_le_mul_of_nonneg_left h hsρ.le
    have e3 : scale p ^ p.ρ * (2 * (1 + a ^ p.ρ / scale p ^ p.ρ)) =
        2 * (a ^ p.ρ + scale p ^ p.ρ) := by
      field_simp
      ring
    linarith
  have hGL := scale_rpow p hp
  unfold curv
  have h1 := mul_le_mul_of_nonneg_left (hmono.trans hsum) (show 0 ≤ p.L1 / 512 by positivity)
  have haρ : 0 ≤ a ^ p.ρ := Real.rpow_nonneg ha _
  nlinarith

omit hp in
lemma degree_valid : 2 ≤ degree p := by
  unfold degree
  omega

lemma width_pos : 0 < width p := by
  unfold width
  have := R_pos p hp
  have := scale_pos p hp
  have := L0_pos p hp
  positivity

lemma width_radius : 16 * p.R ≤ width p := by
  unfold width
  have := scale_pos p hp
  have := L0_pos p hp
  have : 0 ≤ 1632 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * scale p / p.L0 := by positivity
  linarith

lemma width_valid :
    1632 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * scale p ≤ p.L0 * width p := by
  unfold width
  have hL := L0_pos p hp
  have hR := R_pos p hp
  have e : p.L0 * (16 * p.R + 1632 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * scale p / p.L0) =
      16 * p.L0 * p.R + 1632 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * scale p := by
    field_simp
  rw [e]
  have : 0 ≤ 16 * p.L0 * p.R := by positivity
  linarith

lemma coefficient_pos (m : ℕ) : 0 < coefficient p m := by
  unfold coefficient
  have := peak_pos (m := m) (last_pos p hp)
  have := width_pos p hp
  have := L0_pos p hp
  positivity

lemma coefficient_tuning (m : ℕ) :
    coefficient p m * width p = peak m (last p) + p.L0 * width p / 1000 := by
  have hB := (width_pos p hp).ne'
  unfold coefficient
  field_simp

lemma far_large (m : ℕ) : 3 * p.ε ≤ 6 * coefficient p m * width p ^ 2 := by
  have hc : p.L0 / 1000 ≤ coefficient p m := by
    unfold coefficient
    have := peak_pos (m := m) (last_pos p hp)
    have := width_pos p hp
    have : 0 ≤ peak m (last p) / width p := by positivity
    linarith
  have hw := width_radius p hp
  have hR := R_pos p hp
  have hw2 : 256 * p.R ^ 2 ≤ width p ^ 2 := by nlinarith
  have hacc := accuracy_le p hp
  have hL := L0_pos p hp
  have h1 := mul_le_mul hc hw2 (by positivity) (by linarith)
  nlinarith

lemma peak_ratio (m : ℕ) (hm : m ≤ links p) :
    peak m (last p) / width p ≤ p.L0 * (((links p : ℝ) + 2) * 2 ^ links p) := by
  have hR := R_pos p hp
  have hc := cap_pos p hp
  have hL := L0_pos p hp
  have hε := ε_pos p hp
  have hw := width_radius p hp
  have hwp := width_pos p hp
  have hacc := accuracy_le p hp
  have hrat := ratio_le p hp
  unfold peak last
  have h2 : (2 : ℝ) ^ (m - 1) ≤ 2 ^ links p := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : p.ε / cap p ≤ p.L0 * p.R * (13 * ((links p : ℝ) + 1)) / 16 := by
    have : p.ε ≤ p.L0 * p.R ^ 2 / 16 := by linarith
    have hh : p.R / cap p * (p.L0 * p.R / 16) ≤ 13 * ((links p : ℝ) + 1) * (p.L0 * p.R / 16) :=
      mul_le_mul_of_nonneg_right hrat (by positivity)
    have e : p.ε / cap p ≤ p.R / cap p * (p.L0 * p.R / 16) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
      nlinarith
    nlinarith
  have hpow : 0 < (2 : ℝ) ^ links p := by positivity
  rw [div_le_iff₀ hwp]
  have h4 : p.ε / cap p * 2 ^ (m - 1) ≤ p.L0 * p.R * (13 * ((links p : ℝ) + 1)) / 16 * 2 ^ links p :=
    mul_le_mul h3 h2 (by positivity) (by positivity)
  have hl0 : (0 : ℝ) ≤ links p := Nat.cast_nonneg _
  have h5 : p.L0 * p.R * (13 * ((links p : ℝ) + 1)) / 16 * 2 ^ links p ≤
      p.L0 * (((links p : ℝ) + 2) * 2 ^ links p) * width p := by
    have : p.R * (13 * ((links p : ℝ) + 1)) / 16 ≤ ((links p : ℝ) + 2) * width p := by
      nlinarith
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ p.L0 * 2 ^ links p by positivity)
    nlinarith
  linarith

lemma leak (m : ℕ) (hm : m ≤ links p) :
    50 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * coefficient p m * (1 / 2 : ℝ) ^ degree p ≤
      p.L0 / 4 := by
  set L := links p
  have hL0 := L0_pos p hp
  have hk := AdaptiveLocalizationBounds.degree_le_geometric (2 * L + 40) (by omega)
  have hd : (degree p : ℝ) * (degree p + 1 : ℕ) ≤ 6 * 2 ^ (2 * L + 40) := by
    have e : degree p = 2 * (2 * L + 40) := by unfold degree; omega
    rw [e]
    push_cast at hk ⊢
    nlinarith
  have hcoef : coefficient p m ≤ p.L0 * (((L : ℝ) + 2) * 2 ^ L + 1) := by
    have := peak_ratio p hp m hm
    unfold coefficient
    nlinarith
  have hLpow : ((L : ℝ) + 2) * 2 ^ L + 1 ≤ 2 ^ (2 * L + 2) := by
    have h1 : (L : ℝ) + 2 ≤ 2 ^ (L + 1) := by
      have : L + 2 ≤ 2 ^ (L + 1) := by
        induction L with
        | zero => norm_num
        | succ k ih => rw [pow_succ]; omega
      exact_mod_cast this
    have h2 : (2 : ℝ) ^ (2 * L + 2) = 2 ^ (L + 1) * 2 ^ L * 2 := by
      rw [← pow_add]; rw [show 2 * L + 2 = L + 1 + L + 1 by ring, pow_succ]
    have h3 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
    rw [h2]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (L + 1)]
  have hhalf : (1 / 2 : ℝ) ^ degree p = 1 / 2 ^ (4 * L + 80) := by
    unfold degree
    rw [div_pow, one_pow]
  rw [hhalf]
  have hpos : (0 : ℝ) < 2 ^ (4 * L + 80) := by positivity
  have hprod : (degree p : ℝ) * (degree p + 1 : ℕ) * coefficient p m ≤
      6 * 2 ^ (2 * L + 40) * (p.L0 * 2 ^ (2 * L + 2)) := by
    have hn : (0 : ℝ) ≤ (degree p : ℝ) * (degree p + 1 : ℕ) := by positivity
    have hc := coefficient_pos p hp m
    calc
      _ ≤ 6 * 2 ^ (2 * L + 40) * coefficient p m := mul_le_mul_of_nonneg_right hd hc.le
      _ ≤ 6 * 2 ^ (2 * L + 40) * (p.L0 * (((L : ℝ) + 2) * 2 ^ L + 1)) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hLpow hL0.le
  have he : (2 : ℝ) ^ (4 * L + 80) = 2 ^ (2 * L + 40) * 2 ^ (2 * L + 2) * 2 ^ 38 := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [he]
  have hp1 : (0 : ℝ) < 2 ^ (2 * L + 40) := by positivity
  have hp2 : (0 : ℝ) < 2 ^ (2 * L + 2) := by positivity
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  nlinarith

lemma dimension_sufficient (m : ℕ) (hm : m ≤ links p) :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * ((4 * width p) ^ 2 / (cap p / 2) ^ 2) ≤ p.d := by
  set L := links p
  have hc := cap_pos p hp
  have hR := R_pos p hp
  have hL0 := L0_pos p hp
  have hs := scale_pos p hp
  have hρ1 : 0 < p.ρ - 1 := by linarith [ρ_gt p hp]
  have hρ2 : p.ρ - 1 ≤ 1 := by linarith [ρ_le p hp]
  have hmL : (m : ℝ) ≤ L := Nat.cast_le.mpr hm
  have hL0' : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hn : (degree p : ℝ) * (degree p + 1 : ℕ) ≤ 6561 * ((L : ℝ) + 1) ^ 2 := by
    have e : ((degree p : ℕ) : ℝ) = 4 * L + 80 := by unfold degree; push_cast; ring
    have e2 : ((degree p + 1 : ℕ) : ℝ) = 4 * L + 81 := by push_cast [e]; ring
    rw [e, e2]
    nlinarith
  have hsc : scale p / p.L0 / cap p ≤ 1 / 1024 := by
    unfold cap
    rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    field_simp
    nlinarith
  have hwA : width p / cap p ≤ 16384 * ((L : ℝ) + 1) ^ 2 := by
    have hrat := ratio_le p hp
    have e : width p / cap p = 16 * (p.R / cap p) +
        1632 * ((degree p : ℝ) * (degree p + 1 : ℕ)) * (scale p / p.L0 / cap p) := by
      unfold width
      field_simp
    rw [e]
    have h1 := mul_le_mul hn hsc (by positivity) (by positivity)
    nlinarith
  have hratio : (4 * width p) ^ 2 / (cap p / 2) ^ 2 = 64 * (width p / cap p) ^ 2 := by
    field_simp
    ring
  rw [hratio]
  have hw0 : 0 ≤ width p / cap p := by have := width_pos p hp; positivity
  have hwsq : (width p / cap p) ^ 2 ≤ (16384 * ((L : ℝ) + 1) ^ 2) ^ 2 :=
    pow_le_pow_left₀ hw0 hwA 2
  have hm2 : (m : ℝ) ^ 2 ≤ ((L : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
  have hbound : (m : ℝ) + 2 * (m : ℝ) ^ 2 * (64 * (width p / cap p) ^ 2) ≤
      68719476736 * ((L : ℝ) + 1) ^ 6 := by
    have h1 : 2 * (m : ℝ) ^ 2 * (64 * (width p / cap p) ^ 2) ≤
        2 * ((L : ℝ) + 1) ^ 2 * (64 * (16384 * ((L : ℝ) + 1) ^ 2) ^ 2) := by
      apply mul_le_mul _ (by nlinarith) (by positivity) (by positivity)
      linarith
    have h2 : (m : ℝ) ≤ ((L : ℝ) + 1) ^ 6 := by
      have : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith
      have h6 : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) ^ 6 := by
        calc (L : ℝ) + 1 = ((L : ℝ) + 1) ^ 1 := by ring
          _ ≤ ((L : ℝ) + 1) ^ 6 := pow_le_pow_right₀ this (by norm_num)
      linarith
    nlinarith
  have hq := links_le_quad p hp
  have hsq : 0 ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := Real.sqrt_nonneg _
  have hbase : ((L : ℝ) + 1) ^ 6 ≤ (1 + quad p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 6 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 6
  have hd := (Nat.le_ceil _).trans (Nat.cast_le.mpr (dim_ge p hp))
  nlinarith

end

end LongTails.Proofs.RhoSmoothHardParameters
