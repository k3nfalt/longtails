import LongTails.Proofs.BilevelTuning
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 800000

namespace LongTails.Proofs.BilevelBudget

lemma log_restart_bound {A P : ℝ} (hA : 0 ≤ A) (hP : 1 ≤ P)
    (hAP : A ≤ 2 ^ 68 * P ^ 7) :
    (⌈Real.log (1 + A) / Real.log 2⌉₊ : ℝ) + 1 ≤ 256 * Real.log (2 * P) := by
  have hPpos : 0 < P := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hH : 1 / 2 ≤ Real.log (2 * P) := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpow : 1 ≤ P ^ 7 := one_le_pow₀ hP
  have harg : 1 + A ≤ 2 ^ 69 * P ^ 7 := by norm_num at hAP ⊢; nlinarith only [hAP, hpow]
  have hlog := Real.log_le_log (show 0 < 1 + A by positivity) harg
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 69 ≠ 0) (pow_ne_zero _ hPpos.ne'), Real.log_pow, Real.log_pow] at hlog
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hlogA : Real.log (1 + A) ≤ 69 * Real.log (2 * P) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
    norm_num at hlog
    linarith
  have hratio : Real.log (1 + A) / Real.log 2 ≤ 138 * Real.log (2 * P) := by
    apply (div_le_iff₀ hlog2pos).mpr
    have hh := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 138 * Real.log (2 * P) by positivity)
    nlinarith only [hh, hlogA]
  have hratio0 : 0 ≤ Real.log (1 + A) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2pos.le
  have hceil := (Nat.ceil_lt_add_one hratio0).le
  nlinarith only [hceil, hratio, hH]

lemma polynomial_counter_bound {q U W : ℝ} (hq : 1 ≤ q) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (K E m J : ℕ) (hm : (m : ℝ) ≤ 9 * q) (hK : q * K ≤ 3 * U)
    (hE : (E : ℝ) ≤ 1 + 2 ^ 20 * W) :
    ((((2 + m * J) + m * J) * (K * E) : ℕ) : ℝ) ≤ (2 ^ 26 : ℝ) * (U + U * W) * ((J : ℝ) + 1) := by
  have hq0 : 0 ≤ q := by linarith
  have hinner : (2 + m * J + m * J : ℝ) ≤ 20 * q * ((J : ℝ) + 1) := by
    have hh := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg J)
    have hqJ := mul_nonneg hq0 (Nat.cast_nonneg J)
    nlinarith only [hh, hq, hqJ]
  have h1 := mul_le_mul_of_nonneg_right hinner (show 0 ≤ (K : ℝ) * E by positivity)
  have h2 := mul_le_mul_of_nonneg_right hK (show 0 ≤ 20 * (E : ℝ) * ((J : ℝ) + 1) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hE (show 0 ≤ 60 * U * ((J : ℝ) + 1) by positivity)
  have hc : 60 * U * (1 + 2 ^ 20 * W) ≤ (2 ^ 26 : ℝ) * (U + U * W) := by
    norm_num
    nlinarith only [hU, mul_nonneg hU hW]
  have h4 := mul_le_mul_of_nonneg_right hc (show 0 ≤ (J : ℝ) + 1 by positivity)
  push_cast
  nlinarith only [h1, h2, h3, h4]

lemma normalized_log_argument {κ l d g lam Q A : ℝ} (hκ : 1 ≤ κ)
    (hl : 0 ≤ l) (hd : 0 ≤ d) (hg : 0 ≤ g) (hQ : 0 ≤ Q)
    (hlamUpper : lam ≤ 2 ^ 22 * l * κ ^ 3)
    (hQUpper : Q ≤ 2 ^ 25 * (g + l) * (1 + d) * (1 + l) * κ ^ 2)
    (hA : A ≤ 2 ^ 21 * lam * κ ^ 2 * Q) :
    A ≤ 2 ^ 68 * (κ * (1 + l) * (1 + d) * (1 + g)) ^ 7 := by
  have hκ0 : 0 ≤ κ := by linarith
  have hprod : l * (g + l) ≤ (1 + l) ^ 2 * (1 + g) := by
    nlinarith [mul_nonneg hl hg, mul_nonneg (sq_nonneg l) hg]
  calc
    A ≤ 2 ^ 21 * lam * κ ^ 2 * Q := hA
    _ ≤ 2 ^ 21 * (2 ^ 22 * l * κ ^ 3) * κ ^ 2 *
        (2 ^ 25 * (g + l) * (1 + d) * (1 + l) * κ ^ 2) := by gcongr
    _ = 2 ^ 68 * κ ^ 7 * (1 + d) * (1 + l) * (l * (g + l)) := by ring
    _ ≤ 2 ^ 68 * κ ^ 7 * (1 + d) * (1 + l) * ((1 + l) ^ 2 * (1 + g)) := by gcongr
    _ = 2 ^ 68 * κ ^ 7 * (1 + l) ^ 3 * (1 + d) * (1 + g) := by ring
    _ ≤ 2 ^ 68 * κ ^ 7 * (1 + l) ^ 7 * (1 + d) ^ 7 * (1 + g) ^ 7 := by
      have hlp : (1 + l) ^ 3 ≤ (1 + l) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hdp : 1 + d ≤ (1 + d) ^ 7 := by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + d) (show 1 ≤ 7 by omega)
      have hgp : 1 + g ≤ (1 + g) ^ 7 := by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + g) (show 1 ≤ 7 by omega)
      have hh := mul_le_mul (mul_le_mul hlp hdp (by positivity) (by positivity)) hgp (by positivity) (by positivity)
      have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2 : ℝ) ^ 68 * κ ^ 7 by positivity)
      convert hh' using 1 <;> ring
    _ = _ := by ring

lemma counter_log_bound {q U W A P : ℝ} (hq : 1 ≤ q) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hP : 1 ≤ P) (hAP : A ≤ 2 ^ 68 * P ^ 7)
    (K E m : ℕ) (hm : (m : ℝ) ≤ 9 * q) (hK : q * K ≤ 3 * U)
    (hE : (E : ℝ) ≤ 1 + 2 ^ 20 * W) :
    let J := ⌈Real.log (1 + A) / Real.log 2⌉₊
    ((((2 + m * J) + m * J) * (K * E) : ℕ) : ℝ) ≤
      (2 ^ 40 : ℝ) * U * (1 + W) * Real.log (2 * P) := by
  intro J
  have hc := polynomial_counter_bound hq hU hW K E m J hm hK hE
  have hj : (J : ℝ) + 1 ≤ 256 * Real.log (2 * P) := log_restart_bound hA hP hAP
  have hmj := mul_le_mul_of_nonneg_left hj (show 0 ≤ (2 ^ 26 : ℝ) * (U + U * W) by positivity)
  have hlog : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
  have hnonneg : 0 ≤ U * (1 + W) * Real.log (2 * P) := by positivity
  norm_num at hc hmj ⊢
  nlinarith only [hc, hmj, hnonneg]

lemma rounded_counter_bounds {q a b U W : ℝ} (hq : 1 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hU : 0 ≤ U) (hW : 0 ≤ W) (ha4 : (q * a) ^ 4 = 32 * U ^ 4)
    (hb2 : b ^ 2 = 2 ^ 39 * W ^ 2) :
    q * (⌊a⌋₊ : ℝ) ≤ 3 * U ∧ (⌊b⌋₊ + 1 : ℝ) ≤ 1 + 2 ^ 20 * W ∧
      (⌈8 * q⌉₊ : ℝ) ≤ 9 * q := by
  have hq0 : 0 ≤ q := by linarith
  have haBound : q * a ≤ 3 * U := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [ha4, mul_pow]
    norm_num
    nlinarith [pow_nonneg hU 4]
  have hbBound : b ≤ 2 ^ 20 * W := by
    apply (pow_le_pow_iff_left₀ hb (by positivity) two_ne_zero).mp
    rw [hb2, mul_pow]
    norm_num
    nlinarith [sq_nonneg W]
  refine ⟨(mul_le_mul_of_nonneg_left (Nat.floor_le ha) hq0).trans haBound, ?_, ?_⟩
  · have hh := Nat.floor_le hb
    linarith
  · have hh := (Nat.ceil_lt_add_one (show 0 ≤ 8 * q by positivity)).le
    linarith

lemma fourth_root_fourth {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
  calc
    _ = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
    _ = x := by rw [Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx]

lemma unrounded_counter_identities {L q ε Δ : ℝ} (hL : 0 < L) (hq : 0 < q) (hε : 0 < ε) :
    let η := 1 / (4 * (32 * L * q ^ 5))
    let ρ := 512 * L * q ^ 8
    let e := ε / 1024
    let a := 1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))
    let b := Δ * Real.sqrt ρ / (e * Real.sqrt e)
    let U := Real.sqrt (Real.sqrt (L * q ^ 6 / ε))
    let W := Δ * Real.sqrt (L * q ^ 8 / ε ^ 3)
    (q * a) ^ 4 = 32 * U ^ 4 ∧ b ^ 2 = 2 ^ 39 * W ^ 2 := by
  let η := 1 / (4 * (32 * L * q ^ 5))
  let ρ := 512 * L * q ^ 8
  let e := ε / 1024
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hs : 0 < Real.sqrt (ρ * e) := Real.sqrt_pos.mpr (mul_pos hρ he)
  have hr : 0 < Real.sqrt (32 * η * Real.sqrt (ρ * e)) := Real.sqrt_pos.mpr (by positivity)
  have hr4 : (Real.sqrt (32 * η * Real.sqrt (ρ * e))) ^ 4 = ε / (32 * L * q ^ 2) := by
    calc
      _ = ((Real.sqrt (32 * η * Real.sqrt (ρ * e))) ^ 2) ^ 2 := by ring
      _ = (32 * η) ^ 2 * (ρ * e) := by
        rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (mul_pos hρ he).le]
      _ = _ := by dsimp [η, ρ, e]; field_simp; ring
  change (q * (1 / Real.sqrt (32 * η * Real.sqrt (ρ * e)))) ^ 4 = _ ∧
    (Δ * Real.sqrt ρ / (e * Real.sqrt e)) ^ 2 = _
  constructor
  · rw [fourth_root_fourth (by positivity), mul_pow, div_pow, hr4]
    field_simp
  · rw [div_pow, mul_pow, Real.sq_sqrt hρ.le, mul_pow, Real.sq_sqrt he.le,
      mul_pow, Real.sq_sqrt (by positivity : 0 ≤ L * q ^ 8 / ε ^ 3)]
    dsimp [ρ, e]
    field_simp
    ring

lemma penalty_upper_bound {κ l : ℝ} (hκ : 1 ≤ κ) (hl : 0 ≤ l) (hscale : 1 ≤ 2 * l * κ) :
    1 + 2 * κ + 1638400 * l * κ ^ 3 ≤ 2 ^ 22 * l * κ ^ 3 := by
  have hκ0 : 0 ≤ κ := by linarith
  have hp : κ ^ 2 ≤ κ ^ 3 := pow_le_pow_right₀ hκ (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hscale hκ0
  have hh' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * l by positivity)
  have hterm : 0 ≤ l * κ ^ 3 := by positivity
  norm_num
  nlinarith only [hκ, hh, hh', hterm]

lemma radius_upper_bound {E B η M σ T : ℝ} (hE : 1 ≤ E) (hB : B ≤ 2)
    (hstep : η * (M + σ) ≤ 1) (hET : E ≤ 2 ^ 20 * T) :
    E * (2 * B + η * (M + σ)) + 2 * B ≤ 2 ^ 24 * T := by
  have hinner : 2 * B + η * (M + σ) ≤ 5 := by linarith
  have hh := mul_le_mul_of_nonneg_left hinner (show 0 ≤ E by linarith)
  norm_num at hET ⊢
  nlinarith only [hh, hB, hE, hET]

lemma initial_residual_upper_bound {G L R lam T : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hlam : 1 ≤ lam) (hT : 1 ≤ T) (hR : R ≤ 2 ^ 24 * T) :
    G + L * R + L / lam ≤ 2 ^ 25 * (G + L) * T := by
  have hlampos : 0 < lam := by linarith
  have hdiv : L / lam ≤ L := (div_le_iff₀ hlampos).mpr (by nlinarith)
  have hLR := mul_le_mul_of_nonneg_left hR hL
  have hGT := mul_le_mul_of_nonneg_left hT hG
  have hLT := mul_le_mul_of_nonneg_left hT hL
  have hG0 : 0 ≤ G * T := by positivity
  have hL0 : 0 ≤ L * T := by positivity
  norm_num at hLR ⊢
  nlinarith only [hdiv, hLR, hGT, hLT, hG0, hL0]

lemma coarse_epoch_count {κ l d W E : ℝ} (hκ : 1 ≤ κ) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hW : W = d * Real.sqrt l * κ ^ 2) (hE : E ≤ 1 + 2 ^ 20 * W) :
    E ≤ 2 ^ 20 * (1 + d) * (1 + l) * κ ^ 2 := by
  have hs : Real.sqrt l ≤ 1 + l := by nlinarith [Real.sq_sqrt hl, Real.sqrt_nonneg l, sq_nonneg l]
  have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hds := mul_le_mul_of_nonneg_left hs hd
  have hprod : 1 + d * Real.sqrt l ≤ (1 + d) * (1 + l) := by nlinarith only [hds, hl]
  have hh := mul_le_mul_of_nonneg_right hprod (sq_nonneg κ)
  rw [hW] at hE
  norm_num at hE ⊢
  nlinarith only [hE, hh, hκ2]

lemma coarse_radius_factors {L q ε : ℝ} (hL : 0 < L) (hq : 1 ≤ q)
    (hεupper : ε ≤ 2 * L * q ^ 2) :
    Real.sqrt ((ε / 1024) / (512 * L * q ^ 8)) ≤ 2 ∧
      (1 / (4 * (32 * L * q ^ 5))) * (L * (1 + q ^ 2) + (ε / 1024) / 100) ≤ 1 := by
  have hqpos : 0 < q := by linarith
  have hq28 : q ^ 2 ≤ q ^ 8 := pow_le_pow_right₀ hq (by norm_num)
  have hq25 : q ^ 2 ≤ q ^ 5 := pow_le_pow_right₀ hq (by norm_num)
  have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have hL28 := mul_le_mul_of_nonneg_left hq28 hL.le
  have hL25 := mul_le_mul_of_nonneg_left hq25 hL.le
  have hL2 := mul_le_mul_of_nonneg_left hq2 hL.le
  constructor
  · apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr
    apply (div_le_iff₀ (by positivity : 0 < 512 * L * q ^ 8)).mpr
    nlinarith [mul_pos hL (pow_pos hqpos 8)]
  · rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (32 * L * q ^ 5))).mpr
    nlinarith [mul_pos hL (pow_pos hqpos 5)]

lemma fourth_root_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

lemma delta_root_normalization {L κ ε Δ : ℝ} (hL : 0 < L)
    (hε : 0 < ε) (hΔ : 0 ≤ Δ) :
    Δ * Real.sqrt (L * κ ^ 4 / ε ^ 3) = (Δ / ε) * Real.sqrt (L / ε) * κ ^ 2 := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ L * κ ^ 4 / ε ^ 3 by positivity),
    Real.sq_sqrt (show 0 ≤ L / ε by positivity)]
  field_simp

noncomputable def costExpression (p : LongTails.Setups.HigherSmoothBilevel.Params) : ℝ :=
  2 ^ 40 * (p.L * (p.L / p.μ) ^ 3 / p.ε) ^ ((1 : ℝ) / 4) * (1 + p.Δ * Real.sqrt (p.L * (p.L / p.μ) ^ 4 / p.ε ^ 3)) * Real.log (2 * (p.L / p.μ) * (1 + p.L / p.ε) * (1 + p.Δ / p.ε) * (1 + p.G / p.ε))

open LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated BilevelTuning

lemma oracle_cost_bound {p : Params} (hv : spec.valid p) (hsmall : p.ε < 2 * p.L * (p.L / p.μ)) :
    estimatorCalls (tuning p) * (tuning p).N ≤ ⌈costExpression p⌉₊ := by
  rcases hv with ⟨hμ, hμL, hΔ, hG, hε⟩
  have hL : 0 < p.L := hμ.trans_le hμL
  let κ := p.L / p.μ
  let q := Real.sqrt κ
  let η := 1 / (4 * (32 * p.L * q ^ 5))
  let ρ := 512 * p.L * q ^ 8
  let e := p.ε / 1024
  let σ := e / 100
  let B := Real.sqrt (e / ρ)
  let a := 1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))
  let b := p.Δ * Real.sqrt ρ / (e * Real.sqrt e)
  let K := ⌊a⌋₊
  let E := ⌊b⌋₊ + 1
  let m := ⌈8 * q⌉₊
  let R := (E : ℝ) * (2 * B + η * (p.L * (1 + κ) + σ)) + 2 * B
  let lam := 1 + 2 * κ + 16 * p.L * κ ^ 3 / σ
  let τ := σ * p.μ / (10 * lam * p.L)
  let Q := p.G + p.L * R + p.L / lam
  let A := 2 * p.L * (Q / p.μ) / τ
  let U := Real.sqrt (Real.sqrt (p.L * q ^ 6 / p.ε))
  let W := p.Δ * Real.sqrt (p.L * q ^ 8 / p.ε ^ 3)
  let l := p.L / p.ε
  let d := p.Δ / p.ε
  let g := p.G / p.ε
  let T := (1 + d) * (1 + l) * κ ^ 2
  let P := κ * (1 + l) * (1 + d) * (1 + g)
  have hκ : 1 ≤ κ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have hκpos : 0 < κ := by linarith
  have hq : 1 ≤ q := (condition_root hμ hμL).1
  have hqpos : 0 < q := by linarith
  have hq2 : q ^ 2 = κ := Real.sq_sqrt hκpos.le
  have hq6 : q ^ 6 = κ ^ 3 := by rw [← hq2]; ring
  have hq8 : q ^ 8 = κ ^ 4 := by rw [← hq2]; ring
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hT : 1 ≤ T := by
    have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
    dsimp [T]
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ (1 + d) * (1 + l) * κ ^ 2 := by gcongr <;> linarith
  have hP : 1 ≤ P := by
    dsimp [P]
    calc
      1 = 1 * 1 * 1 * 1 := by norm_num
      _ ≤ κ * (1 + l) * (1 + d) * (1 + g) := by gcongr <;> linarith
  have hid := unrounded_counter_identities (Δ := p.Δ) hL hqpos hε
  have hcounts := rounded_counter_bounds hq ha hb hU hW hid.1 hid.2
  have hKcount : q * (K : ℝ) ≤ 3 * U := hcounts.1
  have hEcount : (E : ℝ) ≤ 1 + 2 ^ 20 * W := by simpa [E] using hcounts.2.1
  have hmcount : (m : ℝ) ≤ 9 * q := hcounts.2.2
  have hWnorm : W = d * Real.sqrt l * κ ^ 2 := by
    dsimp [W, d, l]
    rw [hq8]
    exact delta_root_normalization hL hε hΔ.le
  have hET : (E : ℝ) ≤ 2 ^ 20 * T := by simpa only [T, mul_assoc] using coarse_epoch_count hκ hl hd hWnorm hEcount
  have hE1 : (1 : ℝ) ≤ E := by dsimp [E]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌊b⌋₊]
  have hfac := coarse_radius_factors (ε := p.ε) hL hq (by rw [hq2]; exact hsmall.le)
  have hRBound : R ≤ 2 ^ 24 * T := radius_upper_bound hE1 hfac.1
    (by simpa only [hq2] using hfac.2) hET
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlam1 : 1 ≤ lam := by
    have hh : 0 ≤ 16 * p.L * κ ^ 3 / σ := by positivity
    dsimp [lam]
    linarith
  have hlampos : 0 < lam := lt_of_lt_of_le (by norm_num) hlam1
  have hlscale : 1 ≤ 2 * l * κ := by
    have heq : 2 * l * κ = 2 * p.L * κ / p.ε := by dsimp [l]; ring
    rw [heq]
    exact (le_div_iff₀ hε).mpr (by simpa only [one_mul] using hsmall.le)
  have hlamEq : lam = 1 + 2 * κ + 1638400 * l * κ ^ 3 := by dsimp [lam, l, σ, e]; field_simp; ring
  have hlamUpper : lam ≤ 2 ^ 22 * l * κ ^ 3 := by rw [hlamEq]; exact penalty_upper_bound hκ hl hlscale
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQUpper : Q ≤ 2 ^ 25 * (p.G + p.L) * T := initial_residual_upper_bound hG hL.le hlam1 hT hRBound
  have hQbar : Q / p.ε ≤ 2 ^ 25 * (g + l) * (1 + d) * (1 + l) * κ ^ 2 := by
    apply (div_le_iff₀ hε).mpr
    convert hQUpper using 1
    dsimp [g, l, T]
    field_simp
  have hAeq : A = 2048000 * lam * κ ^ 2 * (Q / p.ε) := by
    dsimp [A, τ, σ, e, κ]
    field_simp
    ring
  have hA : 0 ≤ A := by rw [hAeq]; positivity
  have hAP : A ≤ 2 ^ 68 * P ^ 7 := by
    apply normalized_log_argument hκ hl hd hg (div_nonneg hQ hε.le) hlamUpper hQbar
    rw [hAeq]
    norm_num
    nlinarith only [mul_nonneg (mul_nonneg hlampos.le (sq_nonneg κ)) (div_nonneg hQ hε.le)]
  have hc := counter_log_bound hq hU hW hA hP hAP K E m hmcount hKcount hEcount
  have hUeq : U = (p.L * κ ^ 3 / p.ε) ^ ((1 : ℝ) / 4) := by
    dsimp [U]
    rw [hq6]
    exact fourth_root_eq_rpow (by positivity)
  have hcost : ((estimatorCalls (tuning p) * (tuning p).N : ℕ) : ℝ) ≤ costExpression p := by
    change ((((2 + m * ⌈Real.log (1 + A) / Real.log 2⌉₊) + m * ⌈Real.log (1 + A) / Real.log 2⌉₊) * (K * E) : ℕ) : ℝ) ≤ _
    convert hc using 1
    dsimp [costExpression]
    rw [hUeq]
    dsimp [W, P, κ, l, d, g]
    rw [hq8]
    congr 2
    ring
  exact_mod_cast hcost.trans (Nat.le_ceil (costExpression p))

end LongTails.Proofs.BilevelBudget
