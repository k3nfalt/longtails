import LongTails.Algorithms.DashaScaling
import Mathlib.Tactic

namespace LongTails.Proofs.DashaScalingParameters

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

lemma multiplier_ge_one (c : Choice p) : 1 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block := by
  unfold LongTails.Algorithms.DashaCyclic.multiplier
  apply (one_le_div (by positivity)).mpr
  exact_mod_cast Nat.succ_le_of_lt c.block.isLt

lemma variance_nonneg (c : Choice p) : 0 ≤ variance p c := by
  have hq := multiplier_ge_one c
  have hα : 0 ≤ 2 / (4 : ℝ) ^ c.precision := by positivity
  unfold variance
  nlinarith

lemma momentum_pos (c : Choice p) : 0 < momentum p c := by
  unfold momentum
  have := variance_nonneg c
  positivity

lemma momentum_le_one (c : Choice p) : momentum p c ≤ 1 := by
  unfold momentum
  have h := variance_nonneg c
  apply (div_le_one (by positivity)).mpr
  linarith

lemma denominator_pos (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    0 < denominator p c := by
  unfold denominator
  exact add_pos_of_pos_of_nonneg (lt_min hL hH) (mul_nonneg hH.le (Real.sqrt_nonneg _))

lemma stepSize_pos (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    0 < stepSize p c := by
  unfold stepSize
  have := denominator_pos c hL hH
  positivity

lemma spacing_pos (c : Choice p) (hε : 0 < p.ε) : 0 < spacing p c := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.d.pos
  have hω := variance_nonneg c
  unfold spacing
  positivity

lemma spacing_sq (c : Choice p) :
    spacing p c ^ 2 = p.ε ^ 2 * (p.n : ℝ) / (256 * p.d * (variance p c + 1)) := by
  have hω := variance_nonneg c
  unfold spacing
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  norm_num
  field_simp

lemma iterations_accuracy (c : Choice p) (hε : 0 < p.ε) :
    16 * p.Δ * denominator p c / (iterations p c : ℕ) +
      p.ε ^ 2 / (32 * (iterations p c : ℕ)) + p.ε ^ 2 / 16 ≤ 19 * p.ε ^ 2 / 32 := by
  let K : ℝ := (iterations p c : ℕ)
  have hK : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.succ_le_of_lt (iterations p c).pos)
  have hKpos : 0 < K := by linarith
  have hb : 32 * p.Δ * denominator p c / p.ε ^ 2 ≤ K := by
    have hc := Nat.le_ceil (32 * p.Δ * denominator p c / p.ε ^ 2)
    dsimp [K, iterations]
    push_cast
    linarith
  have hm : 32 * p.Δ * denominator p c ≤ K * p.ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp hb
  have hfirst : 16 * p.Δ * denominator p c / K ≤ p.ε ^ 2 / 2 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith
  have hsecond : p.ε ^ 2 / (32 * K) ≤ p.ε ^ 2 / 32 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hK (sq_nonneg p.ε)]
  change 16 * p.Δ * denominator p c / K + p.ε ^ 2 / (32 * K) + p.ε ^ 2 / 16 ≤ _
  linarith

lemma stepSize_denominator (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    stepSize p c * denominator p c = 1 / 8 := by
  have hd := denominator_pos c hL hH
  unfold stepSize
  field_simp

lemma stepSize_smoothness (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    stepSize p c * min p.L p.Lhat ≤ 1 / 8 := by
  have hd : min p.L p.Lhat ≤ denominator p c := by
    unfold denominator
    exact le_add_of_nonneg_right (mul_nonneg hH.le (Real.sqrt_nonneg _))
  exact (mul_le_mul_of_nonneg_left hd (stepSize_pos c hL hH).le).trans_eq
    (stepSize_denominator c hL hH)

lemma stepSize_noise (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    stepSize p c ^ 2 * p.Lhat ^ 2 *
      (variance p c * (2 * variance p c + 1) / p.n) ≤ 1 / 64 := by
  let X := p.Lhat * Real.sqrt (variance p c * (2 * variance p c + 1) / p.n)
  have hX : 0 ≤ X := mul_nonneg hH.le (Real.sqrt_nonneg _)
  have hω := variance_nonneg c
  have harg : 0 ≤ variance p c * (2 * variance p c + 1) / (p.n : ℝ) := by positivity
  have hd : X ≤ denominator p c := by
    change X ≤ min p.L p.Lhat + X
    exact le_add_of_nonneg_left (lt_min hL hH).le
  have hsmall : stepSize p c * X ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hd (stepSize_pos c hL hH).le).trans_eq
      (stepSize_denominator c hL hH)
  have hsquare := (sq_le_sq₀ (mul_nonneg (stepSize_pos c hL hH).le hX) (by norm_num)).mpr hsmall
  dsimp [X] at hsquare
  rw [mul_pow, mul_pow, Real.sq_sqrt harg] at hsquare
  nlinarith only [hsquare]

lemma potential_absorption (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    (stepSize p c / momentum p c * (2 * variance p c / p.n) +
      2 * stepSize p c * variance p c / p.n * (2 * variance p c)) *
        (p.Lhat ^ 2 * stepSize p c ^ 2) ≤
      stepSize p c / 2 - min p.L p.Lhat * stepSize p c ^ 2 / 2 := by
  let γ := stepSize p c
  let ω := variance p c
  let L := min p.L p.Lhat
  have hγ : 0 < γ := stepSize_pos c hL hH
  have hω : 0 ≤ ω := variance_nonneg c
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hc := stepSize_noise c hL hH
  have hLγ := stepSize_smoothness c hL hH
  have hωcmp : ω * (4 * ω + 1) ≤ 2 * (ω * (2 * ω + 1)) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hωcmp
    (show 0 ≤ 2 * γ ^ 2 * p.Lhat ^ 2 / (p.n : ℝ) by positivity)
  have hsmall : 2 * γ ^ 2 * p.Lhat ^ 2 / (p.n : ℝ) * (ω * (4 * ω + 1)) ≤ 1 / 16 := by
    calc
      _ ≤ 2 * γ ^ 2 * p.Lhat ^ 2 / (p.n : ℝ) * (2 * (ω * (2 * ω + 1))) := hscaled
      _ = 4 * (stepSize p c ^ 2 * p.Lhat ^ 2 *
          (variance p c * (2 * variance p c + 1) / p.n)) := by dsimp [γ, ω]; ring
      _ ≤ 4 * (1 / 64) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = _ := by norm_num
  have hm := mul_le_mul_of_nonneg_left hsmall hγ.le
  have hl := mul_le_mul_of_nonneg_left hLγ hγ.le
  have he : (stepSize p c / momentum p c * (2 * variance p c / p.n) +
      2 * stepSize p c * variance p c / p.n * (2 * variance p c)) *
        (p.Lhat ^ 2 * stepSize p c ^ 2) =
      γ * (2 * γ ^ 2 * p.Lhat ^ 2 / (p.n : ℝ) * (ω * (4 * ω + 1))) := by
    dsimp [γ, ω, momentum]
    field_simp
    ring
  rw [he]
  dsimp [γ, L] at hm hl ⊢
  nlinarith only [hm, hl, hγ.le]

lemma initial_noise_bound (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) *
      ((p.d : ℝ) * spacing p c ^ 2 / p.n) ≤ stepSize p c * p.ε ^ 2 / 64 := by
  have hω := variance_nonneg c
  have hγ := stepSize_pos c hL hH
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  have hd : (p.d : ℝ) ≠ 0 := by exact_mod_cast p.d.ne_zero
  have hw : variance p c + 1 ≠ 0 := by positivity
  have ha : 2 * variance p c + 1 ≠ 0 := by positivity
  have he : (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) *
      ((p.d : ℝ) * spacing p c ^ 2 / p.n) =
      (stepSize p c * p.ε ^ 2 / 256) * ((4 * variance p c + 1) / (variance p c + 1)) := by
    rw [spacing_sq]
    unfold momentum
    field_simp
    ring
  have hr : (4 * variance p c + 1) / (variance p c + 1) ≤ 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  rw [he]
  calc
    _ ≤ (stepSize p c * p.ε ^ 2 / 256) * 4 :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

lemma round_noise_bound (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) *
      (2 * (c.block.val + 1) * spacing p c ^ 2 / p.n) ≤ stepSize p c * p.ε ^ 2 / 32 := by
  have hω := variance_nonneg c
  have hγ := stepSize_pos c hL hH
  have ha := momentum_pos c
  have hk : (c.block.val : ℝ) + 1 ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt c.block.isLt
  have hcoeff : 0 ≤ stepSize p c / momentum p c + 2 * stepSize p c * variance p c := by positivity
  have hsmall := initial_noise_bound c hL hH
  have hb := mul_le_mul_of_nonneg_right hk (show 0 ≤ 2 * spacing p c ^ 2 / (p.n : ℝ) by positivity)
  have hb' : 2 * (c.block.val + 1) * spacing p c ^ 2 / p.n ≤
      2 * ((p.d : ℝ) * spacing p c ^ 2 / p.n) := by
    convert hb using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hb' hcoeff
  nlinarith only [hm, hsmall]

lemma sparse_iterations_accuracy (c initializer : Choice p) (hε : 0 < p.ε) :
    (16 * p.Δ * denominator p c + 2 * initialPenalty p c initializer) /
        (sparseIterations p c initializer : ℕ) +
      p.ε ^ 2 / (16 * (sparseIterations p c initializer : ℕ)) + p.ε ^ 2 / 16 ≤
        5 * p.ε ^ 2 / 8 := by
  let K : ℝ := (sparseIterations p c initializer : ℕ)
  have hK : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.succ_le_of_lt (sparseIterations p c initializer).pos)
  have hKpos : 0 < K := by linarith
  have hb : (32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2 ≤ K := by
    have hc := Nat.le_ceil ((32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2)
    dsimp [K, sparseIterations]
    push_cast
    linarith
  have hm := (div_le_iff₀ (sq_pos_of_pos hε)).mp hb
  have hfirst : (16 * p.Δ * denominator p c + 2 * initialPenalty p c initializer) / K ≤ p.ε ^ 2 / 2 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith
  have hsecond : p.ε ^ 2 / (16 * K) ≤ p.ε ^ 2 / 16 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hK (sq_nonneg p.ε)]
  change (16 * p.Δ * denominator p c + 2 * initialPenalty p c initializer) / K +
    p.ε ^ 2 / (16 * K) + p.ε ^ 2 / 16 ≤ _
  linarith

lemma initialization_noise_bound (c initializer : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) *
      (2 * (initializer.block.val + 1) * spacing p c ^ 2 / p.n) ≤ stepSize p c * p.ε ^ 2 / 32 := by
  have hω := variance_nonneg c
  have hγ := stepSize_pos c hL hH
  have ha := momentum_pos c
  have hk : (initializer.block.val : ℝ) + 1 ≤ p.d := by
    exact_mod_cast Nat.succ_le_of_lt initializer.block.isLt
  have hcoeff : 0 ≤ stepSize p c / momentum p c + 2 * stepSize p c * variance p c := by positivity
  have hsmall := initial_noise_bound c hL hH
  have hb := mul_le_mul_of_nonneg_right hk (show 0 ≤ 2 * spacing p c ^ 2 / (p.n : ℝ) by positivity)
  have hb' : 2 * (initializer.block.val + 1) * spacing p c ^ 2 / p.n ≤
      2 * ((p.d : ℝ) * spacing p c ^ 2 / p.n) := by
    convert hb using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hb' hcoeff
  nlinarith only [hm, hsmall]

lemma dense_average_accuracy (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (S : ℝ) (hb : stepSize p c / 2 * S ≤ p.Δ + stepSize p c * p.ε ^ 2 / 64 +
      (iterations p c : ℕ) * (stepSize p c * p.ε ^ 2 / 32)) :
    (1 / ((iterations p c : ℕ) : ℝ)) * S ≤ p.ε ^ 2 := by
  have hγ := stepSize_pos c hL hH
  have hD := denominator_pos c hL hH
  have hK : (0 : ℝ) < (iterations p c : ℕ) := by exact_mod_cast (iterations p c).pos
  have hS : S ≤ 16 * p.Δ * denominator p c + p.ε ^ 2 / 32 +
      (iterations p c : ℕ) * p.ε ^ 2 / 16 := by
    calc
      _ = (2 / stepSize p c) * (stepSize p c / 2 * S) := by field_simp
      _ ≤ (2 / stepSize p c) * (p.Δ + stepSize p c * p.ε ^ 2 / 64 +
          (iterations p c : ℕ) * (stepSize p c * p.ε ^ 2 / 32)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by unfold stepSize; field_simp; ring
  calc
    _ ≤ (1 / ((iterations p c : ℕ) : ℝ)) *
        (16 * p.Δ * denominator p c + p.ε ^ 2 / 32 + (iterations p c : ℕ) * p.ε ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 16 * p.Δ * denominator p c / (iterations p c : ℕ) +
        p.ε ^ 2 / (32 * (iterations p c : ℕ)) + p.ε ^ 2 / 16 := by field_simp
    _ ≤ 19 * p.ε ^ 2 / 32 := iterations_accuracy c hε
    _ ≤ p.ε ^ 2 := by nlinarith [sq_nonneg p.ε]

lemma sparse_average_accuracy (c initializer : Choice p) (hε : 0 < p.ε)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (S : ℝ)
    (hb : stepSize p c / 2 * S ≤ p.Δ + stepSize p c * initialPenalty p c initializer +
      stepSize p c * p.ε ^ 2 / 32 + (sparseIterations p c initializer : ℕ) * (stepSize p c * p.ε ^ 2 / 32)) :
    (1 / ((sparseIterations p c initializer : ℕ) : ℝ)) * S ≤ p.ε ^ 2 := by
  have hγ := stepSize_pos c hL hH
  have hD := denominator_pos c hL hH
  have hK : (0 : ℝ) < (sparseIterations p c initializer : ℕ) := by
    exact_mod_cast (sparseIterations p c initializer).pos
  have hS : S ≤ 16 * p.Δ * denominator p c + 2 * initialPenalty p c initializer + p.ε ^ 2 / 16 +
      (sparseIterations p c initializer : ℕ) * p.ε ^ 2 / 16 := by
    calc
      _ = (2 / stepSize p c) * (stepSize p c / 2 * S) := by field_simp
      _ ≤ (2 / stepSize p c) * (p.Δ + stepSize p c * initialPenalty p c initializer +
          stepSize p c * p.ε ^ 2 / 32 +
          (sparseIterations p c initializer : ℕ) * (stepSize p c * p.ε ^ 2 / 32)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by unfold stepSize; field_simp; ring
  calc
    _ ≤ (1 / ((sparseIterations p c initializer : ℕ) : ℝ)) *
        (16 * p.Δ * denominator p c + 2 * initialPenalty p c initializer + p.ε ^ 2 / 16 +
          (sparseIterations p c initializer : ℕ) * p.ε ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (16 * p.Δ * denominator p c + 2 * initialPenalty p c initializer) /
        (sparseIterations p c initializer : ℕ) +
        p.ε ^ 2 / (16 * (sparseIterations p c initializer : ℕ)) + p.ε ^ 2 / 16 := by field_simp
    _ ≤ 5 * p.ε ^ 2 / 8 := sparse_iterations_accuracy c initializer hε
    _ ≤ p.ε ^ 2 := by nlinarith [sq_nonneg p.ε]

end LongTails.Proofs.DashaScalingParameters
