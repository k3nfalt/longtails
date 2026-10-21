import LongTails.Proofs.LoraWarmup
import LongTails.Proofs.SilverCertificate
import LongTails.Algorithms.LoraSilver

namespace LongTails.Proofs.LoraSilverTuning

open LongTails.Algorithms.LoraGd LongTails.Setups.LocalSmoothStronglyConvexLora
open LongTails.Proofs.LoraModel LongTails.Proofs.SilverCertificate
open LongTails.Algorithms.LoraSilver LongTails.Algorithms.SilverSchedule

lemma pow_ceil_log {a b : ℝ} (ha : 1 < a) (hb : 0 < b) :
    b ≤ a ^ ⌈Real.log b / Real.log a⌉₊ := by
  apply (Real.log_le_log_iff hb (pow_pos (by linarith : 0 < a) _)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ (Real.log_pos ha)).mp (Nat.le_ceil _)

variable {p : Params} {f : MatrixSpace p.m p.n → ℝ} {c : Factors p.m p.n p.r}

lemma condition_lower (H : Model p f c) : 64 ≤ condition p := by
  have hden : 0 < p.μ * p.s ^ 2 := by have := H.mu_pos; have := H.s_pos; positivity
  unfold condition
  apply (le_div_iff₀ hden).mpr
  have hh : p.μ * p.s ^ 2 ≤ p.ρ * p.R ^ 2 :=
    mul_le_mul H.mu_le (pow_le_pow_left₀ (le_of_lt H.s_pos) H.s_le 2)
      (sq_nonneg _) (le_of_lt H.rho_pos)
  nlinarith

lemma depth_eq (p : Params) : depth p = ⌈Real.log (1 + 8 * condition p) / Real.log ratio⌉₊ := by
  unfold depth condition ratio
  congr 3
  ring

lemma depth_mass (H : Model p f c) : 1 + 8 * condition p ≤ ratio ^ depth p := by
  rw [depth_eq]
  exact pow_ceil_log (by linarith [ratio_gt_two]) (by have := condition_lower H; linarith)

lemma depth_condition (H : Model p f c) : condition p ≤ (4 : ℝ) ^ depth p := by
  have hh := depth_mass H
  have hp := pow_le_pow_left₀ (le_of_lt ratio_pos) (show ratio ≤ 4 by linarith [ratio_lt_three]) (depth p)
  have := condition_lower H
  linarith

lemma depth_positive (H : Model p f c) : 0 < depth p := by
  by_contra hh
  have hz : depth p = 0 := Nat.eq_zero_of_not_pos hh
  have hmass := depth_mass H
  rw [hz, pow_zero] at hmass
  linarith [condition_lower H]

lemma warmup_lower (p : Params) :
    128 * condition p * (depth p + 1 : ℝ) ≤ (warmup p : ℝ) := by
  have hh := Nat.le_ceil (condition p)
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 128))
    (show 0 ≤ (depth p + 1 : ℝ) by positivity)
  simpa only [warmup, condition, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hs

lemma geometric_exp {t : ℝ} (ht : t ≤ 1) (n : ℕ) :
    (1 - t) ^ n ≤ Real.exp (-(n : ℝ) * t) := by
  have hh : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr ht) hh n
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_neg, neg_mul] using hp

lemma exp_neg_nat (n : ℕ) : Real.exp (-(n : ℝ)) ≤ 1 / (2 : ℝ) ^ n := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he n
  rw [Real.exp_neg]
  have hn : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul (n := n) (1 : ℝ)
  rw [hn, one_div]
  exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr hp

lemma warmup_decay (H : Model p f c) :
    (1 - growth p / (4 * smoothness p)) ^ warmup p ≤
      1 / (2 : ℝ) ^ (32 * (depth p + 1)) := by
  have hL := H.smoothness_pos
  have hα := H.growth_pos
  have ht : growth p / (4 * smoothness p) ≤ 1 := by
    apply (div_le_one (show 0 < 4 * smoothness p by positivity)).mpr
    linarith [H.growth_le]
  have hg := geometric_exp ht (warmup p)
  have hcount : (32 * (depth p + 1) : ℝ) ≤
      (warmup p : ℝ) * (growth p / (4 * smoothness p)) := by
    have hh := mul_le_mul_of_nonneg_right (warmup_lower p)
      (show 0 ≤ growth p / (4 * smoothness p) by positivity)
    rw [H.condition_eq] at hh
    have he : 128 * (smoothness p / growth p) * (depth p + 1 : ℝ) *
        (growth p / (4 * smoothness p)) = 32 * (depth p + 1 : ℝ) := by
      have := ne_of_gt hL
      have := ne_of_gt hα
      field_simp
      ring
    rwa [he] at hh
  have he : Real.exp (-(warmup p : ℝ) * (growth p / (4 * smoothness p))) ≤
      Real.exp (-((32 * (depth p + 1) : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  exact hg.trans (he.trans (exp_neg_nat _))

lemma radius_eq (H : Model p f c) : radius p = p.R / (2 * condition p) := by
  have := ne_of_gt H.mu_pos
  have := ne_of_gt H.s_pos
  have := ne_of_gt H.rho_pos
  have := ne_of_gt H.R_pos
  unfold radius condition
  field_simp
  ring

lemma radius_pos (H : Model p f c) : 0 < radius p := by
  have := H.mu_pos
  have := H.s_pos
  have := H.rho_pos
  have := H.R_pos
  unfold radius
  positivity

lemma radius_bound (H : Model p f c) : radius p ≤ p.s / 128 := by
  have hh := LongTails.Proofs.LoraWarmup.initial_radius_bound H
  have he : radius p = 2 * (p.μ * p.s ^ 2 / (256 * p.ρ * p.R)) := by unfold radius; ring
  rw [he]
  linarith

noncomputable def tiny (p : Params) : ℝ := radius p / (2 : ℝ) ^ (12 * (depth p + 1))

lemma tiny_pos (H : Model p f c) : 0 < tiny p := by
  unfold tiny
  exact div_pos (radius_pos H) (by positivity)

lemma tiny_le_radius (H : Model p f c) : tiny p ≤ radius p := by
  unfold tiny
  apply div_le_self (le_of_lt (radius_pos H))
  exact one_le_pow₀ (by norm_num)

lemma certificate_power_bound (k : ℕ) :
    12 * (2 + 2 * ratio) ^ k * ((4 : ℝ) * 3 ^ k) ^ 3 ≤ (2 : ℝ) ^ (12 * (k + 1)) := by
  have h3 : ((3 : ℝ) ^ k) ^ 3 = (27 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
    norm_num
  have he : 12 * (2 + 2 * ratio) ^ k * ((4 : ℝ) * 3 ^ k) ^ 3 =
      768 * (27 * (2 + 2 * ratio)) ^ k := by
    simp only [mul_pow, h3]
    ring
  rw [he]
  have hbase : 0 ≤ 27 * (2 + 2 * ratio) := by have := ratio_pos; positivity
  have hcap : 27 * (2 + 2 * ratio) ≤ 4096 := by linarith [ratio_lt_three]
  calc
    768 * (27 * (2 + 2 * ratio)) ^ k ≤ 4096 * (4096 : ℝ) ^ k :=
      mul_le_mul (by norm_num) (pow_le_pow_left₀ hbase hcap k) (by positivity) (by norm_num)
    _ = (2 : ℝ) ^ (12 * (k + 1)) := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, ← pow_succ', ← pow_mul]

lemma tube_power_bound (k : ℕ) :
    2 * ((4 : ℝ) * 3 ^ k + 4) ≤ (2 : ℝ) ^ (12 * (k + 1)) := by
  have hp : 1 ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hcap := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) ≤ 4096) k
  calc
    2 * ((4 : ℝ) * 3 ^ k + 4) ≤ 16 * (3 : ℝ) ^ k := by nlinarith
    _ ≤ 4096 * (4096 : ℝ) ^ k := mul_le_mul (by norm_num) hcap (by positivity) (by norm_num)
    _ = (2 : ℝ) ^ (12 * (k + 1)) := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, ← pow_succ', ← pow_mul]

lemma tiny_certificate (H : Model p f c) :
    12 * (2 + 2 * ratio) ^ depth p * ((4 : ℝ) * 3 ^ depth p) ^ 3 * tiny p ≤ p.R := by
  have hr := radius_pos H
  have hd : 0 < (2 : ℝ) ^ (12 * (depth p + 1)) := by positivity
  have hh := mul_le_mul_of_nonneg_right (certificate_power_bound (depth p))
    (show 0 ≤ tiny p by exact le_of_lt (tiny_pos H))
  have he : (2 : ℝ) ^ (12 * (depth p + 1)) * tiny p = radius p := by
    unfold tiny
    field_simp
  rw [he] at hh
  exact hh.trans ((radius_bound H).trans (by linarith [H.s_pos, H.s_le]))

lemma tiny_tube (H : Model p f c) :
    ((4 : ℝ) * 3 ^ depth p + 4) * tiny p ≤ p.s / 256 := by
  have hh := mul_le_mul_of_nonneg_right (tube_power_bound (depth p))
    (show 0 ≤ tiny p by exact le_of_lt (tiny_pos H))
  have he : (2 : ℝ) ^ (12 * (depth p + 1)) * tiny p = radius p := by
    unfold tiny
    field_simp
  rw [he] at hh
  nlinarith [radius_bound H]

lemma warmup_repair_accuracy (H : Model p f c) {d e : ℝ} (hd : 0 ≤ d)
    (hrepair : growth p * d ^ 2 ≤ 2 * e)
    (he : e ≤ (growth p ^ 2 / (256 * p.ρ)) / (2 : ℝ) ^ (32 * (depth p + 1))) :
    d ≤ tiny p := by
  have hα := H.growth_pos
  have hr := radius_pos H
  have hκ : 0 < condition p := by linarith [condition_lower H]
  have heq : 2 * ((growth p ^ 2 / (256 * p.ρ)) / (2 : ℝ) ^ (32 * (depth p + 1))) =
      growth p * (radius p ^ 2 * condition p / (2 : ℝ) ^ (32 * (depth p + 1))) / 4 := by
    have := ne_of_gt H.mu_pos
    have := ne_of_gt H.s_pos
    have := ne_of_gt H.rho_pos
    have := ne_of_gt H.R_pos
    unfold growth radius condition
    field_simp
    ring
  have hdist : d ^ 2 ≤ radius p ^ 2 * condition p / (2 : ℝ) ^ (32 * (depth p + 1)) := by
    apply (mul_le_mul_iff_of_pos_left hα).mp
    have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)
    rw [heq] at hh
    have hn : 0 ≤ growth p * (radius p ^ 2 * condition p / (2 : ℝ) ^ (32 * (depth p + 1))) := by positivity
    nlinarith
  have hc : condition p ≤ (2 : ℝ) ^ (8 * (depth p + 1)) := by
    calc
      condition p ≤ (4 : ℝ) ^ depth p := depth_condition H
      _ = (2 : ℝ) ^ (2 * depth p) := by rw [pow_mul]; norm_num
      _ ≤ (2 : ℝ) ^ (8 * (depth p + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpowers : (2 : ℝ) ^ (32 * (depth p + 1)) =
      (2 : ℝ) ^ (8 * (depth p + 1)) * ((2 : ℝ) ^ (12 * (depth p + 1))) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hratio : radius p ^ 2 * (2 : ℝ) ^ (8 * (depth p + 1)) /
      (2 : ℝ) ^ (32 * (depth p + 1)) = tiny p ^ 2 := by
    rw [hpowers]
    unfold tiny
    field_simp
  have hbound := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (sq_nonneg (radius p)))
    (show 0 ≤ (2 : ℝ) ^ (32 * (depth p + 1)) by positivity)
  rw [hratio] at hbound
  have ht := tiny_pos H
  nlinarith

lemma epochs_accuracy (H : Model p f c) (hε : 0 < p.ε) :
    4 * smoothness p * p.R ^ 2 / (4 : ℝ) ^ epochs p ≤ p.ε := by
  have hL := H.smoothness_pos
  have hR := H.R_pos
  have hh := pow_ceil_log (by norm_num : (1 : ℝ) < 4)
    (show 0 < 1 + 32 * p.ρ * p.R ^ 4 / p.ε by have := H.rho_pos; positivity)
  change 1 + 32 * p.ρ * p.R ^ 4 / p.ε ≤ (4 : ℝ) ^ epochs p at hh
  have heq : 32 * p.ρ * p.R ^ 4 = 4 * smoothness p * p.R ^ 2 := by unfold smoothness; ring
  rw [heq] at hh
  have hdiv : 4 * smoothness p * p.R ^ 2 / p.ε ≤ (4 : ℝ) ^ epochs p := by linarith
  have hmul := (div_le_iff₀ hε).mp hdiv
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hmul])

end LongTails.Proofs.LoraSilverTuning
