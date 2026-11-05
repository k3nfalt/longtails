import LongTails.Algorithms.BilevelAccelerated
import Mathlib.Tactic

namespace LongTails.Proofs.BilevelTuning

lemma floor_inverse_sqrt_bounds {a : ℝ} (ha : 0 < a) (haquarter : a ≤ 1 / 4) :
    2 ≤ ⌊1 / Real.sqrt a⌋₊ ∧
      a * (⌊1 / Real.sqrt a⌋₊ : ℝ) ^ 2 ≤ 1 ∧
      1 ≤ 4 * a * (⌊1 / Real.sqrt a⌋₊ : ℝ) ^ 2 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs2 := Real.sq_sqrt ha.le
  have hsupper : Real.sqrt a ≤ 1 / 2 := by nlinarith [Real.sqrt_nonneg a]
  have ht : 2 ≤ 1 / Real.sqrt a := (le_div_iff₀ hs).mpr (by linarith)
  have hK : 2 ≤ ⌊1 / Real.sqrt a⌋₊ := Nat.le_floor ht
  have hKR : (2 : ℝ) ≤ (⌊1 / Real.sqrt a⌋₊ : ℝ) := by exact_mod_cast hK
  have hfloor := Nat.floor_le (show 0 ≤ 1 / Real.sqrt a by positivity)
  have hlt := Nat.lt_floor_add_one (1 / Real.sqrt a)
  have hu : (⌊1 / Real.sqrt a⌋₊ : ℝ) * Real.sqrt a ≤ 1 := (le_div_iff₀ hs).mp hfloor
  have hl : 1 ≤ 2 * (⌊1 / Real.sqrt a⌋₊ : ℝ) * Real.sqrt a := by
    have hh := (div_lt_iff₀ hs).mp hlt
    have hmul := mul_le_mul_of_nonneg_right (show (⌊1 / Real.sqrt a⌋₊ : ℝ) + 1 ≤ 2 * (⌊1 / Real.sqrt a⌋₊ : ℝ) by linarith) hs.le
    linarith
  refine ⟨hK, ?_, ?_⟩
  · have hh := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hs.le) hu 2
    nlinarith only [hh, hs2]
  · have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hl 2
    nlinarith only [hh, hs2]

lemma condition_root {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    1 ≤ Real.sqrt (L / μ) ∧ μ * (Real.sqrt (L / μ)) ^ 2 = L := by
  have hκ : 1 ≤ L / μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  constructor
  · exact (Real.one_le_sqrt).mpr hκ
  · rw [Real.sq_sqrt (by linarith : 0 ≤ L / μ)]
    field_simp

lemma epoch_length_bounds {η ρ e : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (he : 0 < e)
    (hsmall : η * Real.sqrt (ρ * e) ≤ 1 / 128) :
    2 ≤ ⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ ∧
      32 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2 * Real.sqrt (ρ * e) ≤ 1 ∧
      1 ≤ 128 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2 * Real.sqrt (ρ * e) := by
  have hs : 0 < Real.sqrt (ρ * e) := Real.sqrt_pos.mpr (mul_pos hρ he)
  have hh := floor_inverse_sqrt_bounds (a := 32 * η * Real.sqrt (ρ * e)) (by positivity) (by linarith)
  refine ⟨hh.1, ?_, ?_⟩ <;> nlinarith only [hh.2.1, hh.2.2]

lemma smooth_scale_small {L ρ e : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (he : 0 < e)
    (hscale : 1024 * ρ * e ≤ L ^ 2) :
    (1 / (4 * L)) * Real.sqrt (ρ * e) ≤ 1 / 128 := by
  have hs := Real.sq_sqrt (mul_pos hρ he).le
  have hroot : Real.sqrt (ρ * e) ≤ L / 32 := by
    nlinarith [Real.sqrt_nonneg (ρ * e)]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
  have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 1 / (4 * L) by positivity)
  have heq : (1 / (4 * L)) * (L / 32) = 1 / 128 := by field_simp; ring
  rw [heq] at hh
  linarith

lemma bilevel_scale_small {L q ε : ℝ} (hL : 0 < L) (hq : 1 ≤ q) (hε : 0 < ε)
    (hεupper : ε ≤ 2 * L * q ^ 2) :
    (1 / (4 * (32 * L * q ^ 5))) * Real.sqrt ((512 * L * q ^ 8) * (ε / 1024)) ≤ 1 / 128 := by
  have hqpos : 0 < q := by linarith
  apply smooth_scale_small (by positivity) (by positivity) (by positivity)
  calc
    1024 * (512 * L * q ^ 8) * (ε / 1024) = ε * (512 * L * q ^ 8) := by ring
    _ ≤ (2 * L * q ^ 2) * (512 * L * q ^ 8) := mul_le_mul_of_nonneg_right hεupper (by positivity)
    _ = (32 * L * q ^ 5) ^ 2 := by ring

lemma penalty_parameter_bounds {L μ κ σ : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hκ : 1 ≤ κ) (heq : μ * κ = L) (hσ : 0 < σ) :
    let lam := 1 + 2 * κ + 16 * L * κ ^ 3 / σ
    1 ≤ lam ∧ L * lam⁻¹ ≤ μ / 2 ∧ 4 * L * κ ^ 3 / lam ≤ σ / 4 := by
  let lam := 1 + 2 * κ + 16 * L * κ ^ 3 / σ
  change 1 ≤ lam ∧ L * lam⁻¹ ≤ μ / 2 ∧ 4 * L * κ ^ 3 / lam ≤ σ / 4
  have hκpos : 0 < κ := by linarith
  have hterm : 0 ≤ 16 * L * κ ^ 3 / σ := by positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlamκ : 2 * κ ≤ lam := by dsimp [lam]; linarith
  refine ⟨by dsimp [lam]; linarith, ?_, ?_⟩
  · rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hlam).mpr
    have hh := mul_le_mul_of_nonneg_left hlamκ hμ.le
    nlinarith only [hh, heq]
  · apply (div_le_iff₀ hlam).mpr
    have hh : 16 * L * κ ^ 3 ≤ σ * lam := by
      have hmul := mul_le_mul_of_nonneg_left
        (show 16 * L * κ ^ 3 / σ ≤ lam by dsimp [lam]; linarith) hσ.le
      have he : σ * (16 * L * κ ^ 3 / σ) = 16 * L * κ ^ 3 := by field_simp
      rw [he] at hmul
      exact hmul
    nlinarith only [hh]

lemma radius_drop_identities {ρ e : ℝ} (hρ : 0 < ρ) (he : 0 < e) :
    let B := Real.sqrt (e / ρ)
    let d := e * Real.sqrt e / Real.sqrt ρ
    0 < B ∧ 0 < d ∧ ρ * B ^ 2 = e ∧ ρ * B ^ 3 = d ∧
      Real.sqrt (ρ * e) * B = e ∧ Real.sqrt (ρ * e) * d = e ^ 2 := by
  let B := Real.sqrt (e / ρ)
  let d := e * Real.sqrt e / Real.sqrt ρ
  have hB : 0 < B := Real.sqrt_pos.mpr (div_pos he hρ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hBsq : ρ * B ^ 2 = e := by
    dsimp [B]
    rw [Real.sq_sqrt (div_pos he hρ).le]
    field_simp
  have hdB : d = e * B := by dsimp [d, B]; rw [Real.sqrt_div he.le]; ring
  have hBd : ρ * B ^ 3 = d := by rw [hdB, ← hBsq]; ring
  have hsB : Real.sqrt (ρ * e) * B = e := by
    dsimp [B]
    rw [Real.sqrt_mul hρ.le, Real.sqrt_div he.le]
    have hs := Real.sq_sqrt he.le
    have hρs : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
    field_simp
    nlinarith only [hs]
  refine ⟨hB, hd, hBsq, hBd, hsB, ?_⟩
  change Real.sqrt (ρ * e) * d = e ^ 2
  rw [hdB]
  nlinarith only [congrArg (fun z => e * z) hsB]

lemma outer_master_bound {η ρ e : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (he : 0 < e)
    (hsmall : η * Real.sqrt (ρ * e) ≤ 1 / 128) :
    32 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2 * e ≤ Real.sqrt (e / ρ) := by
  have hk := (epoch_length_bounds hη hρ he hsmall).2.1
  have hB := radius_drop_identities hρ he
  have hh := mul_le_mul_of_nonneg_right hk hB.1.le
  calc
    _ = (32 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2 * Real.sqrt (ρ * e)) * Real.sqrt (e / ρ) := by
      have hh := congrArg (fun z => (32 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2) * z) hB.2.2.2.2.1
      nlinarith only [hh]
    _ ≤ _ := by simpa using hh

lemma master_decrease_parameters {η K B ρ e : ℝ} (hη : 0 < η) (hK : 1 ≤ K)
    (hB : 0 < B) (he : 0 < e) (hBe : ρ * B ^ 2 = e)
    (hmaster : 32 * η * K ^ 2 * e ≤ B) :
    32 * η * K ^ 2 * (e * B) ≤ B ^ 2 ∧
    32 * η * K ^ 2 * e ^ 2 ≤ e * B ∧
    e / 100 + 2 * ρ * B ^ 2 ≤ 3 * e ∧
    η * (e / 100) ≤ B / 2 ∧ ρ * B ^ 3 = e * B ∧
    16 * η * (e * B) ≤ B ^ 2 ∧ (e / 100) * B ≤ (e * B) / 4 ∧
    3 * K * η * (e / 100) ^ 2 ≤ e * B := by
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hKB : 32 * η * e ≤ B := by
    have hh := mul_le_mul_of_nonneg_left hKsq (show 0 ≤ 32 * η * e by positivity)
    nlinarith only [hh, hmaster]
  have hdec := mul_le_mul_of_nonneg_right hmaster hB.le
  have hnoise := mul_le_mul_of_nonneg_right hmaster he.le
  have hKB' := mul_le_mul_of_nonneg_right hKB hB.le
  have hKle : K ≤ K ^ 2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right hKle (show 0 ≤ 3 * η * e ^ 2 by positivity)
  refine ⟨by nlinarith only [hdec], by nlinarith only [hnoise], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hBe, he]
  · nlinarith only [hKB, hB]
  · nlinarith only [congrArg (fun z => z * B) hBe]
  · nlinarith only [hKB', sq_nonneg B]
  · nlinarith [mul_pos he hB]
  · nlinarith only [hlast, hnoise, mul_pos he hB]

lemma outer_accuracy_bound {η ρ e : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (he : 0 < e)
    (hsmall : η * Real.sqrt (ρ * e) ≤ 1 / 128) :
    Real.sqrt (e / ρ) ≤ 128 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2 * e := by
  have hk := (epoch_length_bounds hη hρ he hsmall).2.2
  have hB := radius_drop_identities hρ he
  have hh := mul_le_mul_of_nonneg_right hk hB.1.le
  have heq := congrArg (fun z => (128 * η * (⌊1 / Real.sqrt (32 * η * Real.sqrt (ρ * e))⌋₊ : ℝ) ^ 2) * z) hB.2.2.2.2.1
  nlinarith only [hh, heq]

lemma inner_length_threshold {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    max 1 ⌈Real.sqrt (64 * L / μ)⌉₊ ≤ ⌈8 * Real.sqrt (L / μ)⌉₊ := by
  have hq := condition_root hμ hμL
  have hκ : 0 ≤ L / μ := by have hL : 0 < L := hμ.trans_le hμL; positivity
  have hs : Real.sqrt (64 * L / μ) = 8 * Real.sqrt (L / μ) := by
    have heq : 64 * L / μ = (8 * Real.sqrt (L / μ)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hκ]; ring
    rw [heq, Real.sqrt_sq (by positivity)]
  rw [hs]
  apply max_le
  · have hh := Nat.le_ceil (8 * Real.sqrt (L / μ))
    have ho : (1 : ℝ) ≤ (⌈8 * Real.sqrt (L / μ)⌉₊ : ℝ) := by linarith [hq.1]
    exact_mod_cast ho
  · exact le_rfl

lemma inner_error_tuning {L μ κ σ : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (hκ : 1 ≤ κ) (heq : μ * κ = L) (hσ : 0 < σ) :
    let lam := 1 + 2 * κ + 16 * L * κ ^ 3 / σ
    let τ := σ * μ / (10 * lam * L)
    0 < τ ∧ 4 * L * κ ^ 3 / lam + 5 * lam * L * τ / μ ≤ σ := by
  let lam := 1 + 2 * κ + 16 * L * κ ^ 3 / σ
  have hp := penalty_parameter_bounds hμ hL hκ heq hσ
  have hlam : 0 < lam := lt_of_lt_of_le (by norm_num) hp.1
  change 0 < σ * μ / (10 * lam * L) ∧ _
  constructor
  · positivity
  · have hh : 5 * lam * L * (σ * μ / (10 * lam * L)) / μ = σ / 2 := by field_simp; ring
    change 4 * L * κ ^ 3 / lam + 5 * lam * L * (σ * μ / (10 * lam * L)) / μ ≤ σ
    rw [hh]
    have hb : 4 * L * κ ^ 3 / lam ≤ σ / 4 := hp.2.2
    linarith

end LongTails.Proofs.BilevelTuning
