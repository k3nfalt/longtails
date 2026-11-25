import LongTails.Algorithms.CyclicLogisticFeatureLearning
import LongTails.Proofs.CyclicLogisticTrajectory

open LongTails.Setups.CyclicLogisticFeatureLearning
open LongTails.Algorithms.CyclicLogisticFeatureLearning (stepSize)

namespace LongTails.Proofs.CyclicLogisticTuning

noncomputable def scale (p : Params) : ℝ := p.n / (p.μ * p.κ)

noncomputable def logFactor (p : Params) : ℝ := 1 + Real.log (2 + scale p)

noncomputable def horizon (p : Params) : ℕ := ⌈128 * scale p * logFactor p / stepSize p⌉₊

noncomputable def energyCap (p : Params) : ℝ := 1024 * scale p * logFactor p

private lemma power_bound {x b L : ℝ} {K : ℕ} (hx : 1 ≤ x) (hL : L = 1 + Real.log (2 + x))
    (hb : 0 < b) (hb' : b ≤ 1) (hK : 16 * L ≤ K * b) :
    2 + Real.sqrt (1024 * x * L) ≤ (1 + b) ^ K := by
  have hx' : 0 < 2 + x := by linarith
  have hL' : L ≤ 2 + x := by linarith [Real.log_le_sub_one_of_pos hx']
  have hL0 : 0 ≤ L := by linarith [Real.log_nonneg (by linarith : 1 ≤ 2 + x)]
  have hr : Real.sqrt (1024 * x * L) ≤ 32 * (2 + x) :=
    (Real.sqrt_le_iff).2 ⟨by linarith, by
      nlinarith [mul_le_mul_of_nonneg_left hL' (by linarith : 0 ≤ x)]⟩
  have hlog : b / 2 ≤ Real.log (1 + b) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + b)
    have he : (1 + b)⁻¹ ≤ 1 - b / 2 := by
      rw [← one_div, div_le_iff₀ (by linarith : 0 < 1 + b)]
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb')]
    linarith
  have hxlog := Real.log_nonneg (by linarith : 1 ≤ 2 + x)
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg K)
  have hl : 4 * Real.log (2 + x) + 8 ≤ K * Real.log (1 + b) := by linarith
  have hex : (33 : ℝ) ≤ Real.exp 8 := by
    have h : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    rw [show (8 : ℝ) = ↑(4 : ℕ) * 2 by norm_num, Real.exp_nat_mul]
    linarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) h 4]
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_add, show 4 * Real.log (2 + x) = ↑(4 : ℕ) * Real.log (2 + x) by norm_num,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hx', Real.exp_log (by linarith : 0 < 1 + b)] at he
  have hpow : 2 + x ≤ (2 + x) ^ 4 := by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), pow_nonneg hx'.le 3]
  nlinarith [mul_le_mul hpow hex (by norm_num : (0 : ℝ) ≤ 33) (pow_nonneg hx'.le 4)]

structure Tuned (p : Params) : Prop where
  positive : 0 < stepSize p
  small : stepSize p ≤ 1 / 8
  curvature : stepSize p * (1 + (1 + (2 * p.n + p.μ * energyCap p) / p.ρ +
    p.μ ^ 2 * energyCap p)) ≤ 1 / 8
  energy : 2 + 4 * stepSize p * horizon p ≤ energyCap p
  signal : 2 + Real.sqrt (energyCap p) ≤
    (1 + stepSize p * (p.μ * p.κ) / (8 * p.n)) ^ horizon p

lemma tuned (p : Params) (hp : spec.valid p) : Tuned p := by
  obtain ⟨hμ, hμ', hκ, hκ', hρ, hρ', _, _⟩ := hp
  have hn : 1 ≤ (p.n : ℝ) := by exact_mod_cast p.n.pos
  have hx : 1 ≤ scale p := by
    apply (le_div_iff₀ (mul_pos hμ hκ)).2
    nlinarith [mul_le_mul hμ' hκ' hκ.le zero_le_one]
  have hl : 1 ≤ logFactor p := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2 + scale p)
    unfold logFactor; linarith
  let Y := p.n * logFactor p / p.κ
  have hY : (p.n : ℝ) ≤ Y := by
    apply (le_div_iff₀ hκ).2
    gcongr; linarith
  have hY' : 0 < Y := by linarith
  have hstep : stepSize p = p.ρ / (65536 * Y) := by
    change p.ρ * p.κ / (65536 * p.n * logFactor p) = p.ρ / (65536 * (p.n * logFactor p / p.κ))
    have hLpos : 0 < logFactor p := by linarith
    field_simp
  have hη : 0 < stepSize p := by rw [hstep]; positivity
  have hηY : stepSize p * Y = p.ρ / 65536 := by rw [hstep]; field_simp
  have hη' : stepSize p ≤ 1 / 8 := by
    linarith [mul_le_mul_of_nonneg_left (show 1 ≤ Y by linarith) hη.le]
  have hcap : p.μ * energyCap p = 1024 * Y := by
    dsimp [energyCap, scale, Y]; field_simp
  have hcap0 : 0 ≤ energyCap p := by
    unfold energyCap; positivity
  have hXη : 0 ≤ 128 * scale p * logFactor p / stepSize p := by positivity
  have hlo := Nat.le_ceil (128 * scale p * logFactor p / stepSize p)
  have hhi := (Nat.ceil_lt_add_one hXη).le
  change _ ≤ (horizon p : ℝ) at hlo
  change (horizon p : ℝ) ≤ _ at hhi
  have htlo := (div_le_iff₀ hη).mp hlo
  have hthi := mul_le_mul_of_nonneg_right hhi hη.le
  rw [add_mul, div_mul_cancel₀ _ hη.ne', one_mul] at hthi
  refine ⟨hη, hη', ?_, ?_, ?_⟩
  · have hc : p.μ ^ 2 * energyCap p ≤ 1024 * Y := by
      rw [← hcap, sq, mul_assoc]
      exact mul_le_of_le_one_left (mul_nonneg hμ.le hcap0) hμ'
    have hbound : 1 + (1 + (2 * p.n + p.μ * energyCap p) / p.ρ + p.μ ^ 2 * energyCap p)
        ≤ 4096 * Y / p.ρ := by
      apply (le_div_iff₀ hρ).2
      rw [add_mul, add_mul, add_mul, div_mul_cancel₀ _ hρ.ne', hcap]
      have h1 := mul_le_mul hc hρ' hρ.le (by linarith : 0 ≤ 1024 * Y)
      linarith
    have hf : stepSize p * (4096 * Y / p.ρ) = 1 / 16 := by
      field_simp; linarith
    linarith [mul_le_mul_of_nonneg_left hbound hη.le]
  · unfold energyCap
    nlinarith [mul_le_mul hx hl (by norm_num : (0 : ℝ) ≤ 1) (by linarith)]
  · let b := stepSize p * (p.μ * p.κ) / (8 * p.n)
    have hb : 0 < b := by dsimp [b]; positivity
    have hbX : b * (8 * scale p) = stepSize p := by
      dsimp [b, scale]; field_simp
    have hb' : b ≤ 1 := by
      linarith [mul_le_mul_of_nonneg_left (by linarith : 1 ≤ 8 * scale p) hb.le]
    apply power_bound hx rfl hb hb'
    apply le_of_mul_le_mul_right (a := 8 * scale p) _ (by linarith)
    calc
      16 * logFactor p * (8 * scale p) = 128 * scale p * logFactor p := by ring
      _ ≤ _ := htlo
      _ = _ := by rw [mul_assoc, hbX]

lemma horizon_eq (p : Params) : horizon p =
    ⌈8388608 * (p.n : ℝ) ^ 2 * (logFactor p) ^ 2 / (p.ρ * p.μ * p.κ ^ 2)⌉₊ := by
  unfold horizon stepSize logFactor scale
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end LongTails.Proofs.CyclicLogisticTuning
