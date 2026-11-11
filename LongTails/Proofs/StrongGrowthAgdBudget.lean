import LongTails.Proofs.StrongGrowthAgdBridge
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.StrongGrowthAgdBudget

open LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdEpochRun LongTails.Proofs.StrongGrowthAgdCounting
  LongTails.Proofs.StrongGrowthAgdTrial

structure Tune (L ρ κ Δ ε : ℝ) : Prop where
  hL : 0 < L
  hρ : 0 < ρ
  hκ : 1 ≤ κ
  hΔ : 0 ≤ Δ
  hε : 0 < ε
  hvalid : 4 ^ 8 * ρ * ε ≤ L ^ 2

noncomputable def θc (L ρ ε : ℝ) : ℝ := Real.sqrt (Real.sqrt (ρ * ε) / L)
noncomputable def Kc (L ρ ε : ℝ) : ℕ := ⌈1 / θc L ρ ε⌉₊
noncomputable def Bc (ρ ε : ℝ) : ℝ := Real.sqrt (ε / ρ) / 1024
noncomputable def bc (κ : ℝ) : ℕ := ⌈800 * κ⌉₊
noncomputable def N1c (ρ Δ ε : ℝ) : ℕ := ⌈268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε)⌉₊ + 1
noncomputable def Rc (L Δ ε : ℝ) : ℕ := ⌈Real.log (1 + 8 * Real.sqrt (2 * L * Δ) / ε)⌉₊ + 1
noncomputable def Gbar (L ρ Δ ε : ℝ) : ℝ :=
  Real.sqrt (8 * L * Δ + L * ε * Real.sqrt (ε / ρ) + ε ^ 2) + L * Real.sqrt (ε / ρ)
noncomputable def mc (L ρ Δ ε : ℝ) : ℕ :=
  8 + ⌈2 * Real.log (1 + 8 * (Real.log (1 + 8 * Real.sqrt (2 * L * Δ) / ε) + 2) *
    (268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) + 2) * Gbar L ρ Δ ε / ε)⌉₊

noncomputable def cfgOf (L ρ κ Δ ε : ℝ) : Config where
  η := 1 / (8 * L)
  θ := θc L ρ ε
  B := Bc ρ ε
  ηf := 1 / L
  thr := 3 / 2 * (ε / 4)
  K := Kc L ρ ε
  b := bc κ
  m := mc L ρ Δ ε
  N1 := N1c ρ Δ ε

section facts

variable {L ρ κ Δ ε : ℝ} (T : Tune L ρ κ Δ ε)
include T

lemma su_facts : 0 < Real.sqrt (ρ * ε) ∧ 0 < Real.sqrt (ε / ρ) ∧
    Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ) = ε ∧ Real.sqrt (ρ * ε) = ρ * Real.sqrt (ε / ρ) ∧
    Real.sqrt (ρ * ε) ^ 2 = ρ * ε ∧ Real.sqrt (ε / ρ) ^ 2 = ε / ρ := by
  have hρ := T.hρ; have hε := T.hε
  have h1 : 0 < Real.sqrt (ρ * ε) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (ε / ρ) := Real.sqrt_pos.mpr (by positivity)
  have h3 : Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ) = ε := by
    rw [← Real.sqrt_mul (by positivity)]
    have : ρ * ε * (ε / ρ) = ε ^ 2 := by field_simp
    rw [this, Real.sqrt_sq hε.le]
  have h5 : Real.sqrt (ρ * ε) ^ 2 = ρ * ε := Real.sq_sqrt (by positivity)
  have h6 : Real.sqrt (ε / ρ) ^ 2 = ε / ρ := Real.sq_sqrt (by positivity)
  have h4 : Real.sqrt (ρ * ε) = ρ * Real.sqrt (ε / ρ) := by
    have : Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ) = ρ * Real.sqrt (ε / ρ) * Real.sqrt (ε / ρ) := by
      rw [h3, mul_assoc, ← sq, h6]; field_simp
    exact mul_right_cancel₀ h2.ne' this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

lemma θ_facts : 0 < θc L ρ ε ∧ θc L ρ ε ^ 2 = Real.sqrt (ρ * ε) / L ∧ θc L ρ ε ≤ 1 / 16 := by
  have hL := T.hL
  obtain ⟨hs, _, _, _, hs2, _⟩ := su_facts T
  have h1 : 0 < θc L ρ ε := Real.sqrt_pos.mpr (by positivity)
  have h2 : θc L ρ ε ^ 2 = Real.sqrt (ρ * ε) / L := Real.sq_sqrt (by positivity)
  refine ⟨h1, h2, ?_⟩
  have h4 : θc L ρ ε ^ 4 = ρ * ε / L ^ 2 := by
    rw [show θc L ρ ε ^ 4 = (θc L ρ ε ^ 2) ^ 2 by ring, h2, div_pow, hs2]
  have hv := T.hvalid
  have h5 : θc L ρ ε ^ 4 ≤ (1 / 16) ^ 4 := by
    rw [h4, div_le_iff₀ (by positivity)]
    norm_num
    nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h5

lemma K_facts : 3 ≤ Kc L ρ ε ∧ 1 ≤ θc L ρ ε * Kc L ρ ε ∧ (Kc L ρ ε : ℝ) * θc L ρ ε ≤ 2 := by
  obtain ⟨hθ, _, hθ16⟩ := θ_facts T
  have hinv : 16 ≤ 1 / θc L ρ ε := by
    rw [le_div_iff₀ hθ]; linarith
  have hK1 : 1 / θc L ρ ε ≤ (Kc L ρ ε : ℝ) := Nat.le_ceil _
  have hK2 : (Kc L ρ ε : ℝ) < 1 / θc L ρ ε + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : (3 : ℝ) ≤ Kc L ρ ε := by linarith
    exact_mod_cast this
  · have := mul_le_mul_of_nonneg_left hK1 hθ.le
    rwa [mul_one_div_cancel hθ.ne'] at this
  · have := mul_le_mul_of_nonneg_right hK2.le hθ.le
    rw [add_mul, one_div_mul_cancel hθ.ne', one_mul] at this
    linarith

lemma b_facts : 0 < bc κ ∧ (κ - 1) / (bc κ : ℝ) ≤ 1 / 800 := by
  have hκ := T.hκ
  have h1 : 800 * κ ≤ (bc κ : ℝ) := Nat.le_ceil _
  have hb : (0 : ℝ) < bc κ := by linarith
  refine ⟨by exact_mod_cast hb, ?_⟩
  rw [div_le_div_iff₀ hb (by norm_num)]
  linarith

lemma N1_facts : 0 < N1c ρ Δ ε ∧ 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) ≤ (N1c ρ Δ ε : ℝ) ∧
    (N1c ρ Δ ε : ℝ) ≤ 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) + 2 := by
  unfold N1c
  refine ⟨by omega, ?_, ?_⟩
  · push_cast; linarith [Nat.le_ceil (268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε))]
  · push_cast
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) by
      have := T.hΔ; have := T.hε; positivity)
    linarith

lemma cfg_hyp : CfgHyp (cfgOf L ρ κ Δ ε) := by
  obtain ⟨hθ, _, hθ16⟩ := θ_facts T
  obtain ⟨hK3, _, _⟩ := K_facts T
  obtain ⟨_, hu, _, _, _, _⟩ := su_facts T
  refine ⟨hK3, hθ, by show θc L ρ ε ≤ 1; linarith, by have := T.hL; simp only [cfgOf]; positivity, ?_, ?_⟩
  · simp only [cfgOf, Bc]; positivity
  · show 1 ≤ mc L ρ Δ ε
    unfold mc; omega

lemma A0_eq : (cfgOf L ρ κ Δ ε).θ ^ 2 * (cfgOf L ρ κ Δ ε).B ^ 2 / (32 * (cfgOf L ρ κ Δ ε).η) =
    ε * Real.sqrt (ε / ρ) / 4194304 := by
  obtain ⟨hs, hu, hsu, hsρ, hs2, hu2⟩ := su_facts T
  obtain ⟨hθ, hθ2, _⟩ := θ_facts T
  have hL := T.hL
  simp only [cfgOf, Bc]
  rw [hθ2]
  field_simp
  nlinarith [hsu, hs2, hu2]

lemma Dm_eq : Dm (cfgOf L ρ κ Δ ε) ρ = ε / 262144 := by
  obtain ⟨hs, hu, hsu, hsρ, hs2, hu2⟩ := su_facts T
  have hρ := T.hρ
  simp only [Dm, cfgOf, Bc]
  rw [div_pow, hu2]
  field_simp
  ring

lemma cert_le : cert (cfgOf L ρ κ Δ ε) ρ ≤ (72 / 1024 + 1 / 131072) * ε := by
  obtain ⟨hs, hu, hsu, hsρ, hs2, hu2⟩ := su_facts T
  obtain ⟨hθ, hθ2, hθ16⟩ := θ_facts T
  obtain ⟨hK3, hKθ, hKθ2⟩ := K_facts T
  have hL := T.hL
  have hε := T.hε
  unfold cert cw
  rw [Dm_eq T]
  simp only [cfgOf, Bc]
  have hKpos : (0 : ℝ) < Kc L ρ ε := by exact_mod_cast (show 0 < Kc L ρ ε by omega)
  have hinvK : 1 / (Kc L ρ ε : ℝ) ≤ θc L ρ ε := by
    rw [div_le_iff₀ hKpos]; linarith
  have hinvK2 : 1 / (Kc L ρ ε : ℝ) ^ 2 ≤ θc L ρ ε ^ 2 := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (by rw [← one_div]; exact hinvK) 2
  have hcw : 7 / (Kc L ρ ε : ℝ) ^ 2 + 2 * θc L ρ ε / Kc L ρ ε ≤ 9 * θc L ρ ε ^ 2 := by
    have h7 : 7 / (Kc L ρ ε : ℝ) ^ 2 ≤ 7 * θc L ρ ε ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hKθ hKθ zero_le_one (by positivity)]
    have h8 : 2 * θc L ρ ε / Kc L ρ ε ≤ 2 * θc L ρ ε ^ 2 := by
      rw [div_le_iff₀ hKpos]
      nlinarith [mul_le_mul_of_nonneg_left hKθ hθ.le]
    linarith
  have hBη : Real.sqrt (ε / ρ) / 1024 / (1 / (8 * L)) = 8 * L * Real.sqrt (ε / ρ) / 1024 := by
    field_simp
  have hpos : 0 ≤ Real.sqrt (ε / ρ) / 1024 / (1 / (8 * L)) := by positivity
  calc (7 / (Kc L ρ ε : ℝ) ^ 2 + 2 * θc L ρ ε / Kc L ρ ε) * (Real.sqrt (ε / ρ) / 1024) / (1 / (8 * L)) +
        2 * (ε / 262144)
      = (7 / (Kc L ρ ε : ℝ) ^ 2 + 2 * θc L ρ ε / Kc L ρ ε) * (Real.sqrt (ε / ρ) / 1024 / (1 / (8 * L))) +
        2 * (ε / 262144) := by ring
    _ ≤ 9 * θc L ρ ε ^ 2 * (Real.sqrt (ε / ρ) / 1024 / (1 / (8 * L))) + 2 * (ε / 262144) := by
        nlinarith [mul_le_mul_of_nonneg_right hcw hpos]
    _ = (72 / 1024 + 1 / 131072) * ε := by
        rw [hBη, hθ2]
        field_simp
        nlinarith [hsu]

lemma cert_lt : cert (cfgOf L ρ κ Δ ε) ρ < ε / 4 ∧ 17 / 100 * ε ≤ ε / 4 - cert (cfgOf L ρ κ Δ ε) ρ := by
  have := cert_le T
  have hε := T.hε
  constructor <;> nlinarith

lemma cEpoch_le : cEpoch (cfgOf L ρ κ Δ ε) ρ ≤
    (1 / 50) * (2 * (ε * Real.sqrt (ε / ρ) / 4194304)) := by
  obtain ⟨hs, hu, hsu, hsρ, hs2, hu2⟩ := su_facts T
  obtain ⟨hθ, hθ2, hθ16⟩ := θ_facts T
  obtain ⟨hK3, hKθ, hKθ2⟩ := K_facts T
  have hL := T.hL
  have hε := T.hε
  have hρ := T.hρ
  have hDm := Dm_eq T
  unfold cEpoch cStep cEnd
  rw [hDm]
  simp only [cfgOf, Bc]
  have hKpos : (0 : ℝ) < Kc L ρ ε := by exact_mod_cast (show 0 < Kc L ρ ε by omega)
  have hK2 : (Kc L ρ ε : ℝ) ≤ 2 / θc L ρ ε := by rw [le_div_iff₀ hθ]; exact hKθ2
  have hθL : θc L ρ ε ^ 2 * L = Real.sqrt (ρ * ε) := by rw [hθ2]; field_simp
  have hu3 : Real.sqrt (ε / ρ) ^ 3 = (ε / ρ) * Real.sqrt (ε / ρ) := by rw [pow_succ, hu2]
  have hstep : (Kc L ρ ε : ℝ) * ((58 / 25 * (1 / (8 * L) / θc L ρ ε) + 8 * (1 / (8 * L))) * (ε / 262144) ^ 2) ≤
      ε * Real.sqrt (ε / ρ) / 4194304 / 10000 := by
    have h1 : (Kc L ρ ε : ℝ) * (58 / 25 * (1 / (8 * L) / θc L ρ ε) + 8 * (1 / (8 * L))) ≤
        (2 / θc L ρ ε) * (58 / 25 * (1 / (8 * L) / θc L ρ ε) + 8 * (1 / (8 * L))) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have h2 : (2 / θc L ρ ε) * (58 / 25 * (1 / (8 * L) / θc L ρ ε) + 8 * (1 / (8 * L))) =
        (116 / 25 + 16 * θc L ρ ε) / (8 * L * θc L ρ ε ^ 2) := by field_simp; ring
    have h3 : (116 / 25 + 16 * θc L ρ ε) / (8 * L * θc L ρ ε ^ 2) ≤ 6 / (8 * Real.sqrt (ρ * ε)) := by
      rw [← hθL, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hL (pow_pos hθ 2)]
    have h4 : 6 / (8 * Real.sqrt (ρ * ε)) * (ε / 262144) ^ 2 ≤ ε * Real.sqrt (ε / ρ) / 4194304 / 10000 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ) = ε := hsu
      nlinarith [sq_nonneg ε, mul_pos hε hε, hs, hu, mul_pos hs hu]
    calc _ = (Kc L ρ ε : ℝ) * (58 / 25 * (1 / (8 * L) / θc L ρ ε) + 8 * (1 / (8 * L))) * (ε / 262144) ^ 2 := by ring
      _ ≤ (116 / 25 + 16 * θc L ρ ε) / (8 * L * θc L ρ ε ^ 2) * (ε / 262144) ^ 2 := by
          rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 6 / (8 * Real.sqrt (ρ * ε)) * (ε / 262144) ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ _ := h4
  have hend1 : 8 * ρ * (Real.sqrt (ε / ρ) / 1024) ^ 3 = (1 / 64) * (2 * (ε * Real.sqrt (ε / ρ) / 4194304)) := by
    rw [div_pow, hu3]; field_simp; ring
  have hend2 : 18 * (1 / (8 * L)) * (ε / 262144) ^ 2 ≤ ε * Real.sqrt (ε / ρ) / 4194304 / 1000 := by
    have hθ' : Real.sqrt (ρ * ε) ≤ L / 256 := by
      have h := hθ2
      have : θc L ρ ε ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hθ.le hθ16 2
      rw [h, div_le_iff₀ hL] at this
      linarith
    have hε2 : ε ^ 2 = Real.sqrt (ρ * ε) * (ε * Real.sqrt (ε / ρ)) := by
      calc ε ^ 2 = ε * (Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ)) := by rw [hsu]; ring
        _ = _ := by ring
    have key : 18 * (1 / (8 * L)) * (ε / 262144) ^ 2 = 18 * ε ^ 2 / (8 * L * 262144 ^ 2) := by
      field_simp
    have key2 : ε * Real.sqrt (ε / ρ) / 4194304 / 1000 = ε * Real.sqrt (ε / ρ) / 4194304000 := by ring
    rw [key, key2, div_le_div_iff₀ (by positivity) (by positivity), hε2]
    have hY : 0 < ε * Real.sqrt (ε / ρ) := mul_pos hε hu
    nlinarith [mul_le_mul_of_nonneg_left hθ' hY.le, mul_pos hs hY]
  have : (1 / 50) * (2 * (ε * Real.sqrt (ε / ρ) / 4194304)) =
      ε * Real.sqrt (ε / ρ) / 4194304 / 10000 + (1 / 64) * (2 * (ε * Real.sqrt (ε / ρ) / 4194304)) +
        ε * Real.sqrt (ε / ρ) / 4194304 / 1000 + (2 / 50 - 1 / 10000 - 2 / 64 - 1 / 1000) *
          (ε * Real.sqrt (ε / ρ) / 4194304) := by ring
  nlinarith [hstep, hend1, hend2, mul_pos hε hu]

lemma r_le : ((1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2) ≤ 203 / 400 := by
  obtain ⟨_, hδ⟩ := b_facts T
  linarith

lemma r_pow_eight : ((1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2) ^ 8 ≤ 1 / 200 := by
  have h1 := r_le T
  have h0 : 0 ≤ (1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2 := by
    have := T.hκ; have : (0:ℝ) ≤ (κ - 1) / (bc κ : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
    positivity
  calc _ ≤ (203 / 400 : ℝ) ^ 8 := pow_le_pow_left₀ h0 h1 8
    _ ≤ 1 / 200 := by norm_num

lemma r_pow_m_le : ((1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2) ^ mc L ρ Δ ε ≤ 1 / 200 := by
  have h0 : 0 ≤ (1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2 := by
    have := T.hκ; have : (0:ℝ) ≤ (κ - 1) / (bc κ : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
    positivity
  have h1 : ((1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2) ≤ 1 := by linarith [r_le T]
  calc _ ≤ ((1 + 3 * (4 * ((κ - 1) / (bc κ : ℝ)))) / 2) ^ 8 :=
        pow_le_pow_of_le_one h0 h1 (by unfold mc; omega)
    _ ≤ _ := r_pow_eight T

set_option maxHeartbeats 1000000 in
lemma fail_le_quarter :
    (1 / (cfgOf L ρ κ Δ ε).N1 : ℝ) *
      ((2 / ((cfgOf L ρ κ Δ ε).θ ^ 2 * (cfgOf L ρ κ Δ ε).B ^ 2 / (32 * (cfgOf L ρ κ Δ ε).η)) +
          kap1 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ) * (Δ + (cfgOf L ρ κ Δ ε).N1 * cEpoch (cfgOf L ρ κ Δ ε) ρ) +
        (cfgOf L ρ κ Δ ε).N1 * kap2 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ +
        (cfgOf L ρ κ Δ ε).N1 * ((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m) ≤
      1 / 4 := by
  obtain ⟨hs, hu, hsu, hsρ, hs2, hu2⟩ := su_facts T
  obtain ⟨hθ, hθ2, hθ16⟩ := θ_facts T
  obtain ⟨hK3, hKθ, hKθ2⟩ := K_facts T
  obtain ⟨hb, hδ⟩ := b_facts T
  obtain ⟨hN1, hN1lo, hN1hi⟩ := N1_facts T
  have hL := T.hL
  have hε := T.hε
  have hρ := T.hρ
  have hΔ := T.hΔ
  have hA0 := A0_eq T
  have hcE := cEpoch_le T
  obtain ⟨_, hcert⟩ := cert_lt T
  have hr := r_pow_m_le T
  set X := ε * Real.sqrt (ε / ρ) / 4194304 with hX
  have hX0 : 0 < X := by positivity
  set N1 : ℝ := ((cfgOf L ρ κ Δ ε).N1 : ℝ) with hN1def
  have hN1pos : 0 < N1 := by simp only [hN1def, cfgOf]; exact_mod_cast hN1
  set c := cEpoch (cfgOf L ρ κ Δ ε) ρ with hc
  have hc0 : 0 ≤ c := by
    simp only [hc, cEpoch, cStep, cEnd, cfgOf, Bc]
    have hDm : 0 ≤ Dm (cfgOf L ρ κ Δ ε) ρ := by rw [Dm_eq T]; positivity
    simp only [cfgOf] at hDm
    positivity
  have hcX : c ≤ X / 25 := by rw [hX]; linarith [hcE]
  have hΔN : 64 * Δ ≤ N1 * X := by
    have hsq : Real.sqrt ρ * Real.sqrt (ε / ρ) = Real.sqrt ε := by
      rw [← Real.sqrt_mul hρ.le]; congr 1; field_simp
    have hN1lo' : 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) ≤ N1 := by
      simp only [hN1def, cfgOf]; exact hN1lo
    have hε' : 0 < ε * Real.sqrt ε := by positivity
    have := mul_le_mul_of_nonneg_right hN1lo' hX0.le
    rw [hX] at this ⊢
    have key : 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) * (ε * Real.sqrt (ε / ρ) / 4194304) = 64 * Δ := by
      field_simp
      rw [mul_comm (Real.sqrt ρ) _, mul_assoc, mul_comm (Real.sqrt (ε / ρ)) _] at *
      nlinarith [hsq, Real.sqrt_nonneg ε, Real.sqrt_nonneg ρ, hu]
    linarith
  have hKpos : (0 : ℝ) < (cfgOf L ρ κ Δ ε).K := by
    simp only [cfgOf]; exact_mod_cast (show 0 < Kc L ρ ε by omega)
  have hinvK : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 ≤ 4 * θc L ρ ε ^ 2 := by
    have h1 : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ≤ 2 * θc L ρ ε := by
      rw [div_le_iff₀ hKpos]; simp only [cfgOf]; nlinarith
    calc (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 ≤ (2 * θc L ρ ε) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 4 * θc L ρ ε ^ 2 := by ring
  have hcert2 : (17 / 100 * ε) ^ 2 ≤ (ε / 4 - cert (cfgOf L ρ κ Δ ε) ρ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcert 2
  have hθL : θc L ρ ε ^ 2 * L = Real.sqrt (ρ * ε) := by rw [hθ2]; field_simp
  have hδ' : (κ - 1) / ((cfgOf L ρ κ Δ ε).b : ℝ) ≤ 1 / 800 := by simp only [cfgOf]; exact hδ
  have hδ0 : 0 ≤ (κ - 1) / ((cfgOf L ρ κ Δ ε).b : ℝ) := div_nonneg (by linarith [T.hκ]) (Nat.cast_nonneg _)
  have hsX : Real.sqrt (ρ * ε) * X = ε ^ 2 / 4194304 := by
    rw [hX]
    calc Real.sqrt (ρ * ε) * (ε * Real.sqrt (ε / ρ) / 4194304)
        = (Real.sqrt (ρ * ε) * Real.sqrt (ε / ρ)) * ε / 4194304 := by ring
      _ = ε ^ 2 / 4194304 := by rw [hsu]; ring
  have hk1 : kap1 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ * (Δ / N1 + c) ≤ 1 / 1000 := by
    unfold kap1
    have hη : (64 / (cfgOf L ρ κ Δ ε).η : ℝ) = 512 * L := by simp only [cfgOf]; field_simp; ring
    rw [hη]
    have hD : Δ / N1 + c ≤ X / 64 + X / 25 := by
      have : Δ / N1 ≤ X / 64 := by rw [div_le_div_iff₀ hN1pos (by norm_num)]; linarith
      linarith
    have hD0 : 0 ≤ Δ / N1 + c := by positivity
    have hk : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b) * (512 * L) /
        (ε / 4 - cert (cfgOf L ρ κ Δ ε) ρ) ^ 2 ≤ 4 * θc L ρ ε ^ 2 * (1 / 800) * (512 * L) / (17 / 100 * ε) ^ 2 := by
      have hnum : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b) * (512 * L) ≤
          4 * θc L ρ ε ^ 2 * (1 / 800) * (512 * L) := by
        have := mul_le_mul hinvK hδ' hδ0 (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 512 * L)]
      exact div_le_div₀ (by positivity) hnum (by positivity) hcert2
    calc _ ≤ 4 * θc L ρ ε ^ 2 * (1 / 800) * (512 * L) / (17 / 100 * ε) ^ 2 * (X / 64 + X / 25) :=
          mul_le_mul hk hD hD0 (by positivity)
      _ = (4 * 512 / 800) * (θc L ρ ε ^ 2 * L) * X * (1 / 64 + 1 / 25) / ((17 / 100) ^ 2 * ε ^ 2) := by ring
      _ = (4 * 512 / 800) * (1 / 64 + 1 / 25) / ((17 / 100) ^ 2 * 4194304) := by
          rw [hθL, mul_assoc _ _ X, hsX]; field_simp
      _ ≤ 1 / 1000 := by norm_num
  have hk2 : kap2 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ ≤ 1 / 1000 := by
    unfold kap2
    rw [Dm_eq T]
    have hKθ' : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 * (2 * (cfgOf L ρ κ Δ ε).K) = 8 / (cfgOf L ρ κ Δ ε).K := by
      field_simp; ring
    have h8 : (8 / (cfgOf L ρ κ Δ ε).K : ℝ) ≤ 8 * θc L ρ ε := by
      rw [div_le_iff₀ hKpos]; simp only [cfgOf]; nlinarith
    have hnum : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b) *
        (2 * (cfgOf L ρ κ Δ ε).K * (ε / 262144) ^ 2) ≤ 8 * θc L ρ ε * (1 / 800) * (ε / 262144) ^ 2 := by
      have e : (2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b) *
          (2 * (cfgOf L ρ κ Δ ε).K * (ε / 262144) ^ 2) =
          ((2 / (cfgOf L ρ κ Δ ε).K : ℝ) ^ 2 * (2 * (cfgOf L ρ κ Δ ε).K)) * ((κ - 1) / (cfgOf L ρ κ Δ ε).b) *
            (ε / 262144) ^ 2 := by ring
      rw [e, hKθ']
      have := mul_le_mul h8 hδ' hδ0 (by positivity)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc _ ≤ 8 * θc L ρ ε * (1 / 800) * (ε / 262144) ^ 2 / (17 / 100 * ε) ^ 2 :=
          div_le_div₀ (by positivity) hnum (by positivity) hcert2
      _ = 8 * θc L ρ ε * (1 / 800) / (262144 ^ 2 * (17 / 100) ^ 2) := by field_simp
      _ ≤ 8 * (1 / 16) * (1 / 800) / (262144 ^ 2 * (17 / 100) ^ 2) := by gcongr
      _ ≤ 1 / 1000 := by norm_num
  have hrm : ((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m ≤ 1 / 200 := by
    simp only [cfgOf]; exact hr
  rw [hA0]
  have hmain : (2 / X + kap1 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ) * (Δ + N1 * c) =
      N1 * ((2 / X) * (Δ / N1 + c) + kap1 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ * (Δ / N1 + c)) := by
    field_simp
  have h2X : (2 / X) * (Δ / N1 + c) ≤ 2 / 64 + 2 / 25 := by
    have hΔ' : Δ / N1 ≤ X / 64 := by rw [div_le_div_iff₀ hN1pos (by norm_num)]; linarith
    have : (2 / X) * (Δ / N1 + c) ≤ (2 / X) * (X / 64 + X / 25) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : (2 / X) * (X / 64 + X / 25) = 2 / 64 + 2 / 25 := by field_simp
    linarith
  rw [hmain]
  have hfinal : (1 / N1) * (N1 * ((2 / X) * (Δ / N1 + c) + kap1 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ * (Δ / N1 + c)) +
      N1 * kap2 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ +
      N1 * ((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m) =
      (2 / X) * (Δ / N1 + c) + kap1 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ * (Δ / N1 + c) +
        kap2 (cfgOf L ρ κ Δ ε) ρ (ε / 4) κ +
        ((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m := by
    field_simp
  rw [hfinal]
  linarith

omit T in
lemma r_le_exp : (203 / 400 : ℝ) ≤ Real.exp (-(1 / 2)) := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp (1 / 2) < 165 / 100 := by
    have hpos := Real.exp_pos (1 / 2)
    nlinarith [sq_nonneg (Real.exp (1 / 2) - 165 / 100)]
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

omit T in
lemma quarter_le_exp : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
  have h1 := Real.exp_one_lt_d9
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

omit T in
lemma pow_le_exp_neg {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ Real.exp (-c)) (n : ℕ) :
    a ^ n ≤ Real.exp (-(n * c)) := by
  calc a ^ n ≤ Real.exp (-c) ^ n := pow_le_pow_left₀ ha hac n
    _ = Real.exp (-(n * c)) := by rw [← Real.exp_nat_mul]; ring_nf

omit T in
lemma exp_neg_le_inv {x y : ℝ} (hy : 0 ≤ y) (hx : Real.log (1 + y) ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + y) := by
  rw [Real.exp_neg, one_div]
  refine inv_anti₀ (by linarith) ?_
  calc 1 + y = Real.exp (Real.log (1 + y)) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp x := Real.exp_le_exp.mpr hx

set_option maxHeartbeats 1000000 in
lemma final_le (G0 : ℝ) (_hG0 : 0 ≤ G0) (hG0' : G0 ≤ Real.sqrt (2 * L * Δ)) :
    G0 * (1 / 4) ^ Rc L Δ ε + 3 * (ε / 4) +
      ((Rc L Δ ε : ℝ) * ((cfgOf L ρ κ Δ ε).N1 : ℝ)) *
        (((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m *
          (Real.sqrt (2 * L * (Δ + (cfgOf L ρ κ Δ ε).N1 * cEpoch (cfgOf L ρ κ Δ ε) ρ) + (ε / 4) ^ 2) / 2 +
            L / Real.sqrt (2 * L * (Δ + (cfgOf L ρ κ Δ ε).N1 * cEpoch (cfgOf L ρ κ Δ ε) ρ) + (ε / 4) ^ 2) *
              (Δ + (cfgOf L ρ κ Δ ε).N1 * cEpoch (cfgOf L ρ κ Δ ε) ρ) + 2 * L * (cfgOf L ρ κ Δ ε).B)) ≤ ε := by
  obtain ⟨hs, hu, hsu, hsρ, hs2, hu2⟩ := su_facts T
  obtain ⟨hN1, hN1lo, hN1hi⟩ := N1_facts T
  have hL := T.hL
  have hε := T.hε
  have hρ := T.hρ
  have hΔ := T.hΔ
  have hcE := cEpoch_le T
  set X := ε * Real.sqrt (ε / ρ) / 4194304 with hX
  have hX0 : 0 < X := by positivity
  set N1 : ℝ := ((cfgOf L ρ κ Δ ε).N1 : ℝ) with hN1def
  have hN1pos : 0 < N1 := by simp only [hN1def, cfgOf]; exact_mod_cast hN1
  set c := cEpoch (cfgOf L ρ κ Δ ε) ρ with hc
  have hc0 : 0 ≤ c := by
    simp only [hc, cEpoch, cStep, cEnd, cfgOf, Bc]
    have hDm : 0 ≤ Dm (cfgOf L ρ κ Δ ε) ρ := by rw [Dm_eq T]; positivity
    simp only [cfgOf] at hDm
    have hθ := (θ_facts T).1
    positivity
  have hcX : c ≤ X / 25 := by rw [hX]; linarith [hcE]
  set S := Δ + N1 * c with hS
  have hS0 : 0 ≤ S := by positivity
  set τ := Real.sqrt (2 * L * S + (ε / 4) ^ 2) with hτ
  have hτpos : 0 < τ := Real.sqrt_pos.mpr (by positivity)
  have hτ2 : τ ^ 2 = 2 * L * S + (ε / 4) ^ 2 := Real.sq_sqrt (by positivity)
  have hpart1 : G0 * (1 / 4) ^ Rc L Δ ε ≤ ε / 8 := by
    set Y := 8 * Real.sqrt (2 * L * Δ) / ε with hY
    have hY0 : 0 ≤ Y := by positivity
    have hR : Real.log (1 + Y) ≤ (Rc L Δ ε : ℝ) := by
      unfold Rc; push_cast; linarith [Nat.le_ceil (Real.log (1 + Y))]
    have h1 : (1 / 4 : ℝ) ^ Rc L Δ ε ≤ Real.exp (-((Rc L Δ ε : ℝ) * 1)) :=
      pow_le_exp_neg (by norm_num) quarter_le_exp _
    have h2 : Real.exp (-((Rc L Δ ε : ℝ) * 1)) ≤ 1 / (1 + Y) := exp_neg_le_inv hY0 (by rw [mul_one]; exact hR)
    have h3 : Real.sqrt (2 * L * Δ) * (1 / (1 + Y)) ≤ ε / 8 := by
      rw [hY, mul_one_div, div_le_iff₀ (by positivity)]
      have : ε / 8 * (1 + 8 * Real.sqrt (2 * L * Δ) / ε) = ε / 8 + Real.sqrt (2 * L * Δ) := by field_simp
      rw [this]; linarith
    calc G0 * (1 / 4) ^ Rc L Δ ε ≤ Real.sqrt (2 * L * Δ) * (1 / (1 + Y)) :=
          mul_le_mul hG0' (h1.trans h2) (by positivity) (Real.sqrt_nonneg _)
      _ ≤ ε / 8 := h3
  have hG : τ / 2 + L / τ * S + 2 * L * (cfgOf L ρ κ Δ ε).B ≤ Gbar L ρ Δ ε := by
    have h1 : L / τ * S ≤ τ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hτpos (by norm_num)]
      nlinarith [hτ2, sq_nonneg (ε / 4)]
    have hN1X : N1 * X ≤ 64 * Δ + 2 * X := by
      have hsq : Real.sqrt ρ * Real.sqrt (ε / ρ) = Real.sqrt ε := by
        rw [← Real.sqrt_mul hρ.le]; congr 1; field_simp
      have hN1hi' : N1 ≤ 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) + 2 := by
        simp only [hN1def, cfgOf]; exact hN1hi
      have := mul_le_mul_of_nonneg_right hN1hi' hX0.le
      have key : 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) * X = 64 * Δ := by
        rw [hX]; field_simp
        rw [mul_comm (Real.sqrt ρ) _, mul_assoc, mul_comm (Real.sqrt (ε / ρ)) _] at *
        nlinarith [hsq, Real.sqrt_nonneg ε, Real.sqrt_nonneg ρ, hu]
      linarith [this, key]
    have hS' : 2 * L * S + (ε / 4) ^ 2 ≤ 8 * L * Δ + L * ε * Real.sqrt (ε / ρ) + ε ^ 2 := by
      have hXu : X ≤ ε * Real.sqrt (ε / ρ) := by rw [hX]; linarith [mul_pos hε hu]
      have hNc : N1 * c ≤ 3 * Δ + ε * Real.sqrt (ε / ρ) / 2 := by
        have := mul_le_mul_of_nonneg_left hcX hN1pos.le
        linarith [hΔ, hXu, hX0]
      rw [hS]
      have := mul_le_mul_of_nonneg_left hNc hL.le
      linarith [sq_nonneg ε]
    have hτle : τ ≤ Real.sqrt (8 * L * Δ + L * ε * Real.sqrt (ε / ρ) + ε ^ 2) := Real.sqrt_le_sqrt hS'
    have hB : 2 * L * (cfgOf L ρ κ Δ ε).B ≤ L * Real.sqrt (ε / ρ) := by
      simp only [cfgOf, Bc]
      linarith [mul_pos hL hu]
    unfold Gbar
    linarith
  have hGbar0 : 0 < Gbar L ρ Δ ε := by
    unfold Gbar; have := Real.sqrt_nonneg (8 * L * Δ + L * ε * Real.sqrt (ε / ρ) + ε ^ 2); positivity
  set Rb := Real.log (1 + 8 * Real.sqrt (2 * L * Δ) / ε) + 2 with hRb
  have hRb0 : 0 < Rb := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 8 * Real.sqrt (2 * L * Δ) / ε by
      have : 0 ≤ 8 * Real.sqrt (2 * L * Δ) / ε := by positivity
      linarith)
    linarith
  have hRle : (Rc L Δ ε : ℝ) ≤ Rb := by
    unfold Rc; push_cast
    have := Nat.ceil_lt_add_one (Real.log_nonneg (show (1 : ℝ) ≤ 1 + 8 * Real.sqrt (2 * L * Δ) / ε by
      have : 0 ≤ 8 * Real.sqrt (2 * L * Δ) / ε := by positivity
      linarith))
    linarith
  set Nb := 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) + 2 with hNb
  have hNb0 : 0 < Nb := by
    have : 0 ≤ 268435456 * Δ * Real.sqrt ρ / (ε * Real.sqrt ε) := by positivity
    linarith
  have hNle : N1 ≤ Nb := by simp only [hN1def, cfgOf]; exact hN1hi
  set Z := 8 * Rb * Nb * Gbar L ρ Δ ε / ε with hZ
  have hZ0 : 0 < Z := by positivity
  have hm : 2 * Real.log (1 + Z) ≤ ((cfgOf L ρ κ Δ ε).m : ℝ) := by
    simp only [cfgOf, mc]; push_cast
    linarith [Nat.le_ceil (2 * Real.log (1 + Z)), Real.log_nonneg (show (1:ℝ) ≤ 1 + Z by linarith)]
  have hr0 : 0 ≤ (1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2 := by
    have := T.hκ
    have : (0:ℝ) ≤ (κ - 1) / ((cfgOf L ρ κ Δ ε).b : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
    positivity
  have hrle : (1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2 ≤ Real.exp (-(1 / 2)) := by
    simp only [cfgOf]; exact (r_le T).trans r_le_exp
  have hrm : ((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m ≤ 1 / (1 + Z) := by
    refine (pow_le_exp_neg hr0 hrle _).trans (exp_neg_le_inv hZ0.le ?_)
    linarith
  have hpart3 : ((Rc L Δ ε : ℝ) * N1) *
      (((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m *
        (τ / 2 + L / τ * S + 2 * L * (cfgOf L ρ κ Δ ε).B)) ≤ ε / 8 := by
    have hG0' : 0 ≤ τ / 2 + L / τ * S + 2 * L * (cfgOf L ρ κ Δ ε).B := by
      have : 0 ≤ (cfgOf L ρ κ Δ ε).B := by simp only [cfgOf, Bc]; positivity
      positivity
    have hRN : (Rc L Δ ε : ℝ) * N1 ≤ Rb * Nb := mul_le_mul hRle hNle hN1pos.le hRb0.le
    have hrG : ((1 + 3 * (4 * ((κ - 1) / (cfgOf L ρ κ Δ ε).b))) / 2) ^ (cfgOf L ρ κ Δ ε).m *
        (τ / 2 + L / τ * S + 2 * L * (cfgOf L ρ κ Δ ε).B) ≤ 1 / (1 + Z) * Gbar L ρ Δ ε :=
      mul_le_mul hrm hG hG0' (by positivity)
    calc _ ≤ Rb * Nb * (1 / (1 + Z) * Gbar L ρ Δ ε) :=
          mul_le_mul hRN hrG (by positivity) (by positivity)
      _ ≤ Rb * Nb * Gbar L ρ Δ ε / Z := by
          rw [show Rb * Nb * (1 / (1 + Z) * Gbar L ρ Δ ε) = Rb * Nb * Gbar L ρ Δ ε / (1 + Z) by ring]
          exact div_le_div_of_nonneg_left (by positivity) hZ0 (by linarith)
      _ = ε / 8 := by rw [hZ]; field_simp
  linarith

end facts

section hyps

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]

omit [BorelSpace E] in
lemma hyps_of {L ρ κ Δ ε : ℝ} (T : Tune L ρ κ Δ ε) (x0 : E) (f : E → ℝ) (g : E → Ω → E)
    (p : MeasureTheory.Measure Ω)
    (hf : ContDiff ℝ 2 f) (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hhess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hΔf : ∀ x, f x0 - f x ≤ Δ) (hmeas : Measurable (Function.uncurry g))
    (hint : ∀ x, MeasureTheory.Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hint2 : ∀ x, MeasureTheory.Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hvar : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ (κ - 1) * ‖gradient f x‖ ^ 2) :
    Hyps (cfgOf L ρ κ Δ ε) x0 g f p L ρ κ Δ (ε / 4) := by
  obtain ⟨hθ, _, hθ16⟩ := θ_facts T
  obtain ⟨hK3, hKθ, hKθ2⟩ := K_facts T
  obtain ⟨hb, hδ⟩ := b_facts T
  obtain ⟨hN1, _, _⟩ := N1_facts T
  refine ⟨hb, ⟨T.hL, T.hρ.le, hf, hlip, hhess⟩, ⟨hmeas, hint, hmean, hint2, hvar⟩, T.hκ, cfg_hyp T, rfl,
    ?_, hδ, rfl, hΔf, T.hΔ, hKθ, hKθ2, hN1, ?_, by have := T.hε; positivity, rfl⟩
  · show θc L ρ ε ≤ 1 / 8; linarith
  · show 1 ≤ mc L ρ Δ ε; unfold mc; omega

end hyps

end LongTails.Proofs.StrongGrowthAgdBudget
