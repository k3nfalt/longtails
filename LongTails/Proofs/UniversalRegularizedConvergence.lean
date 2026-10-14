import LongTails.Proofs.UniversalRegularizedRun
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped RealInnerProductSpace

namespace OracleTemplate.HolderMonotone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure RunCtx (F : E → E) (L r ε c1 B R r0 : ℝ) (x0 xs : E) : Prop where
  hyp : Hyp F L r ε
  hr : 0 < r
  hε : 0 < ε
  hL : 0 ≤ L
  hxs : F xs = 0
  hR : ‖x0 - xs‖ ≤ R
  hr0 : 0 < r0
  hr0R : r0 ≤ R
  hc1 : 16 * L / ε ≤ c1
  hc1r : ∀ ρ, 0 < ρ → ρ ≤ 2 * R → 2 * ρ / r ≤ c1 * ρ + 4
  hB : c1 * R ≤ B

namespace RunCtx

variable {F : E → E} {L r ε c1 B R r0 : ℝ} {x0 xs : E}

lemma hRpos (c : RunCtx F L r ε c1 B R r0 x0 xs) : 0 < R := lt_of_lt_of_le c.hr0 c.hr0R

lemma hc1pos (c : RunCtx F L r ε c1 B R r0 x0 xs) : 0 ≤ c1 :=
  le_trans (div_nonneg (mul_nonneg (by norm_num) c.hL) c.hε.le) c.hc1

lemma hBpos (c : RunCtx F L r ε c1 B R r0 x0 xs) : 0 ≤ B :=
  le_trans (mul_nonneg c.hc1pos c.hRpos.le) c.hB

lemma one_le_log (c : RunCtx F L r ε c1 B R r0 x0 xs) :
    1 ≤ Real.log ((2 * B + 4) * R / r0) := by
  have h1 : 1 ≤ R / r0 := (one_le_div c.hr0).mpr c.hr0R
  have h2 : (4 : ℝ) ≤ (2 * B + 4) * R / r0 := by
    rw [mul_div_assoc]
    nlinarith [c.hBpos]
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

end RunCtx

lemma stage_bound [FiniteDimensional ℝ E] {F : E → E} {L r ε c1 B R r0 : ℝ} {x0 xs : E}
    (c : RunCtx F L r ε c1 B R r0 x0 xs) {ρ : ℝ} (hρ0 : r0 ≤ ρ) (hρR : ρ ≤ 2 * R) :
    ∃ m : ℕ, (m : ℝ) ≤ 9 * Real.log ((2 * B + 4) * R / r0) * (c1 * ρ + 4) + 4 ∧
      (Done F ε ((trans F ε x0)^[m] (stageStart ε x0 ρ)) ∨
        (ρ < R ∧ (trans F ε x0)^[m] (stageStart ε x0 ρ) = stageStart ε x0 (2 * ρ))) := by
  have hρ : 0 < ρ := lt_of_lt_of_le c.hr0 hρ0
  have hε := c.hε
  have hRpos := c.hRpos
  have hμ : 0 < ε / (4 * ρ) := div_pos hε (mul_pos (by norm_num) hρ)
  have hLμ : 0 < L + ε / (4 * ρ) := add_pos_of_nonneg_of_pos c.hL hμ
  obtain ⟨z, hz⟩ := exists_reg_zero c.hyp.cont c.hyp.mono hμ x0
  have hzD : ‖x0 - z‖ ≤ R := by
    rw [norm_sub_rev]
    exact le_trans (anchor_dist c.hyp.mono hμ hz c.hxs) c.hR
  set sb := min (1 / (4 * (L + ε / (4 * ρ)))) (2 * r / ε) with hsbdef
  have ha : 0 < 1 / (4 * (L + ε / (4 * ρ))) := by positivity
  have hb : 0 < 2 * r / ε := div_pos (mul_pos (by norm_num) c.hr) hε
  have hsb : 0 < sb := lt_min ha hb
  have hsbL : sb * (L + ε / (4 * ρ)) ≤ 1 / 4 := by
    have h1 : sb ≤ 1 / (4 * (L + ε / (4 * ρ))) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_right h1 hLμ.le
    have e : 1 / (4 * (L + ε / (4 * ρ))) * (L + ε / (4 * ρ)) = 1 / 4 := by
      rw [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hLμ.ne']
      norm_num
    linarith
  have hsbρ : ε * sb ≤ ρ := by
    have h1 : sb * (ε / (4 * ρ)) ≤ 1 / 4 := by
      have : 0 ≤ sb * L := mul_nonneg hsb.le c.hL
      nlinarith
    have e : sb * (ε / (4 * ρ)) = ε * sb / (4 * ρ) := by ring
    rw [e, div_le_iff₀ (by positivity)] at h1
    linarith
  have ctx : StageCtx F L r ε x0 z ρ sb (1 - sb * (ε / (4 * ρ)) / 2) R (2 * R) :=
    ⟨c.hyp, c.hr, hε, c.hL, hρ, hz, hzD, by linarith, hsb, hsbL, min_le_right _ _, rfl,
      by linarith⟩
  have hεsb : 0 < ε * sb := mul_pos hε hsb
  set X := ρ / (ε * sb) with hX
  have hXpos : 0 < X := div_pos hρ hεsb
  have hXle : 4 * X ≤ c1 * ρ + 4 := by
    rcases min_choice (1 / (4 * (L + ε / (4 * ρ)))) (2 * r / ε) with hm | hm
    · have e : X = 4 * L * ρ / ε + 1 := by
        rw [hX, hsbdef, hm]
        field_simp
      have h1 := mul_le_mul_of_nonneg_right c.hc1 hρ.le
      have e2 : 16 * L / ε * ρ = 4 * (4 * L * ρ / ε) := by ring
      rw [e]
      linarith
    · have e : 4 * X = 2 * ρ / r := by
        rw [hX, hsbdef, hm]
        have := c.hr.ne'
        field_simp
        ring
      rw [e]
      exact c.hc1r ρ hρ hρR
  set Λ := Real.log ((2 * B + 4) * R / r0) with hΛ
  have hΛ1 : 1 ≤ Λ := c.one_le_log
  have hc1 := c.hc1pos
  have hlog : Real.log (2 * R / (ε * sb)) ≤ Λ := by
    apply Real.log_le_log (div_pos (by linarith) hεsb)
    have e : 2 * R / (ε * sb) = R / (2 * ρ) * (4 * X) := by
      rw [hX]
      field_simp
      ring
    have h1 : c1 * ρ + 4 ≤ 2 * B + 4 := by
      have := mul_le_mul_of_nonneg_left hρR hc1
      linarith [c.hB]
    have h2 : R / (2 * ρ) ≤ R / r0 := by
      apply div_le_div_of_nonneg_left hRpos.le c.hr0
      linarith
    have h3 : 0 ≤ R / (2 * ρ) := by positivity
    calc 2 * R / (ε * sb) = R / (2 * ρ) * (4 * X) := e
      _ ≤ R / (2 * ρ) * (2 * B + 4) := mul_le_mul_of_nonneg_left (by linarith) h3
      _ ≤ R / r0 * (2 * B + 4) := mul_le_mul_of_nonneg_right h2 (by linarith [c.hBpos])
      _ = (2 * B + 4) * R / r0 := by ring
  set Nr := 3 + X + 32 * X * Real.log (2 * R / (ε * sb)) with hNr
  have hlog0 : 0 ≤ Real.log (2 * R / (ε * sb)) :=
    Real.log_nonneg ((one_le_div hεsb).mpr (by linarith))
  have hNr0 : 0 ≤ Nr := by positivity
  obtain ⟨m, hm, hit⟩ := stage_hit ctx (⌊Nr⌋₊ + 1) (by
    push_cast
    exact Nat.lt_floor_add_one Nr)
  refine ⟨m, ?_, hit⟩
  have h1 : (m : ℝ) ≤ Nr + 1 := by
    have : (m : ℝ) ≤ ((⌊Nr⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this
    linarith [Nat.floor_le hNr0]
  have h2 : 32 * X * Real.log (2 * R / (ε * sb)) ≤ 32 * X * Λ :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h3 : X ≤ X * Λ := by nlinarith
  have h4 : 4 * X * Λ ≤ (c1 * ρ + 4) * Λ := mul_le_mul_of_nonneg_right hXle (by linarith)
  have h5 : 0 ≤ (c1 * ρ + 4) * Λ := mul_nonneg (by positivity) (by linarith)
  nlinarith

lemma finish [FiniteDimensional ℝ E] {F : E → E} {L r ε c1 B R r0 : ℝ} {x0 xs : E}
    (c : RunCtx F L r ε c1 B R r0 x0 xs) (k : ℕ) :
    ∀ ρ, r0 ≤ ρ → ρ ≤ 2 * R → R ≤ ρ * 2 ^ k →
      ∃ m : ℕ, (m : ℝ) ≤ 9 * Real.log ((2 * B + 4) * R / r0) * c1 * ρ * (2 ^ (k + 1) - 1) +
          (36 * Real.log ((2 * B + 4) * R / r0) + 4) * (k + 1) ∧
        Done F ε ((trans F ε x0)^[m] (stageStart ε x0 ρ)) := by
  have hΛ1 := c.one_le_log
  have hc1 := c.hc1pos
  set Λ := Real.log ((2 * B + 4) * R / r0) with hΛ
  induction k with
  | zero =>
    intro ρ hρ0 hρR hRρ
    obtain ⟨m, hm, hd | ⟨hlt, -⟩⟩ := stage_bound c hρ0 hρR
    · refine ⟨m, ?_, hd⟩
      rw [← hΛ] at hm
      simp only [zero_add, pow_one, Nat.cast_zero]
      linarith
    · simp only [pow_zero, mul_one] at hRρ
      linarith
  | succ k ih =>
    intro ρ hρ0 hρR hRρ
    have hρ : 0 < ρ := lt_of_lt_of_le c.hr0 hρ0
    obtain ⟨m, hm, hd | ⟨hlt, hre⟩⟩ := stage_bound c hρ0 hρR
    · refine ⟨m, ?_, hd⟩
      rw [← hΛ] at hm
      have h2 : (1 : ℝ) ≤ 2 ^ (k + 1 + 1) - 1 := by
        have : (2 : ℝ) ≤ 2 ^ (k + 1 + 1) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have h3 : 0 ≤ 9 * Λ * c1 * ρ := by positivity
      have h4 : 9 * Λ * c1 * ρ * 1 ≤ 9 * Λ * c1 * ρ * (2 ^ (k + 1 + 1) - 1) :=
        mul_le_mul_of_nonneg_left h2 h3
      have h5 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      nlinarith
    · obtain ⟨m2, hm2, hd2⟩ := ih (2 * ρ) (by linarith) (by linarith) (by
        rw [pow_succ] at hRρ; linarith)
      refine ⟨m2 + m, ?_, ?_⟩
      · rw [← hΛ] at hm
        push_cast
        have e : 9 * Λ * c1 * ρ * (2 ^ (k + 1 + 1) - 1) =
            9 * Λ * (c1 * ρ) + 9 * Λ * c1 * (2 * ρ) * (2 ^ (k + 1) - 1) := by ring
        rw [e]
        linarith
      · rw [Function.iterate_add_apply, hre]
        exact hd2

theorem converge [FiniteDimensional ℝ E] {F : E → E} {L r ε c1 B R r0 : ℝ} {x0 xs : E}
    (c : RunCtx F L r ε c1 B R r0 x0 xs) (K : ℕ)
    (hK : 40 * (B + Real.logb 2 (R / r0) + 2) * Real.log ((2 * B + 4) * R / r0) ≤ K) :
    Done F ε ((trans F ε x0)^[K] (stageStart ε x0 r0)) := by
  have hΛ1 := c.one_le_log
  have hc1 := c.hc1pos
  have hBpos := c.hBpos
  have hRpos := c.hRpos
  set Λ := Real.log ((2 * B + 4) * R / r0) with hΛ
  have hx1 : 1 ≤ R / r0 := (one_le_div c.hr0).mpr c.hr0R
  set lg := Real.logb 2 (R / r0) with hlg
  have hlg0 : 0 ≤ lg := Real.logb_nonneg (by norm_num) hx1
  set J := ⌈lg⌉₊ with hJ
  have hJ1 : lg ≤ J := Nat.le_ceil lg
  have hJ2 : (J : ℝ) < lg + 1 := Nat.ceil_lt_add_one hlg0
  have hpow : (2 : ℝ) ^ lg = R / r0 :=
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hJlow : R / r0 ≤ (2 : ℝ) ^ J := by
    rw [← hpow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hJ1
  have hJup : (2 : ℝ) ^ J ≤ 2 * (R / r0) := by
    rw [← hpow, ← Real.rpow_natCast]
    calc (2 : ℝ) ^ (J : ℝ) ≤ 2 ^ (lg + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hJ2.le
      _ = 2 * 2 ^ lg := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have hR1 : R ≤ r0 * 2 ^ J := by
    have := mul_le_mul_of_nonneg_left hJlow c.hr0.le
    have e : r0 * (R / r0) = R := by
      have := c.hr0.ne'
      field_simp
    linarith
  have hR2 : r0 * 2 ^ J ≤ 2 * R := by
    have := mul_le_mul_of_nonneg_left hJup c.hr0.le
    have e : r0 * (2 * (R / r0)) = 2 * R := by
      have := c.hr0.ne'
      field_simp
    linarith
  obtain ⟨m, hm, hd⟩ := finish c J r0 le_rfl (by linarith [c.hr0R]) hR1
  rw [← hΛ] at hm
  have hmK : (m : ℝ) ≤ K := by
    have h1 : 9 * Λ * c1 * r0 * (2 ^ (J + 1) - 1) ≤ 36 * Λ * B := by
      have h2 : r0 * (2 ^ (J + 1) - 1) ≤ 4 * R := by
        rw [pow_succ]
        nlinarith [c.hr0]
      have h3 : c1 * (r0 * (2 ^ (J + 1) - 1)) ≤ c1 * (4 * R) := mul_le_mul_of_nonneg_left h2 hc1
      have h4 : 9 * Λ * (c1 * (r0 * (2 ^ (J + 1) - 1))) ≤ 9 * Λ * (c1 * (4 * R)) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      have h5 : 9 * Λ * (c1 * R) ≤ 9 * Λ * B := mul_le_mul_of_nonneg_left c.hB (by linarith)
      nlinarith
    have h6 : (36 * Λ + 4) * ((J : ℝ) + 1) ≤ 40 * Λ * (lg + 2) := by
      have h7 : (J : ℝ) + 1 ≤ lg + 2 := by linarith
      have h8 : 36 * Λ + 4 ≤ 40 * Λ := by linarith
      calc (36 * Λ + 4) * ((J : ℝ) + 1) ≤ (36 * Λ + 4) * (lg + 2) :=
            mul_le_mul_of_nonneg_left h7 (by linarith)
        _ ≤ 40 * Λ * (lg + 2) := mul_le_mul_of_nonneg_right h8 (by linarith)
    have h9 : 36 * Λ * B ≤ 40 * Λ * B := by nlinarith
    nlinarith
  have hmK' : m ≤ K := by exact_mod_cast hmK
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK'
  rw [add_comm, Function.iterate_add_apply, iterate_done x0 hd]
  exact hd

lemma execute_universal (F : E → E) (ε r0 : ℝ) (x0 : E) (K : ℕ) :
    execute { answer := fun _ (_, x) _ => F x } (universalRegularizedExtragradient ε r0 x0) (fun _ => K) =
      ((trans F ε x0)^[K] (stageStart ε x0 r0)).x := by
  erw [execute_iterate]
  rfl

end OracleTemplate.HolderMonotone
