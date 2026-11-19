import LongTails.Proofs.SymmetricReverseFisherGeometry
import Mathlib.Data.Nat.Log

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTuning

lemma localization_radius {L R κ ρ B M : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hκ : 0 < κ) (hρ : 0 < ρ) (hB : 0 < B) (hM : 0 ≤ M) :
    let r := L * R / (L + 32 * κ * ρ * B * M * R)
    0 < r ∧ r ≤ R ∧ M * r ≤ L / (16 * κ * ρ * B) ∧ (M = 0 → r = R) := by
  let D := L + 32 * κ * ρ * B * M * R
  have hD : 0 < D := by dsimp [D]; positivity
  have hm : 0 ≤ 32 * κ * ρ * B * M * R := by positivity
  have hsmall : 16 * κ * ρ * B * M * R ≤ D := by dsimp [D]; nlinarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hD).mpr
    have hh := mul_le_mul_of_nonneg_right (show L ≤ D by dsimp [D]; linarith) hR.le
    simpa only [mul_comm] using hh
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hD (by positivity : 0 < 16 * κ * ρ * B)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall hL.le
    nlinarith
  · intro hzero
    simp [hzero, hL.ne']

lemma confidence_parameter {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) (hn : 0 < n) :
    let θ := Real.exp (-(2 / (n : ℝ)) * Real.log (1 / δ)) / 4
    0 < θ ∧ θ ≤ 1 ∧ (2 * Real.sqrt θ) ^ n = δ := by
  let θ := Real.exp (-(2 / (n : ℝ)) * Real.log (1 / δ)) / 4
  let z := Real.exp (-Real.log (1 / δ) / (n : ℝ))
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ).mpr hδ1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hz : 0 < z := Real.exp_pos _
  have he : Real.exp (-(2 / (n : ℝ)) * Real.log (1 / δ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hh := mul_nonneg (by positivity : 0 ≤ 2 / (n : ℝ)) hlog
    nlinarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hz2 : z ^ 2 = 4 * θ := by
    dsimp [z, θ]
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have hh : (2 : ℝ) * (-Real.log (1 / δ) / (n : ℝ)) =
        -(2 / (n : ℝ)) * Real.log (1 / δ) := by ring
    rw [hh]
    ring
  have hbase : 2 * Real.sqrt θ = z := by
    nlinarith [Real.sq_sqrt hθ.le, Real.sqrt_nonneg θ]
  refine ⟨hθ, hθ1, ?_⟩
  change (2 * Real.sqrt θ) ^ n = δ
  rw [hbase]
  dsimp [z]
  rw [← Real.exp_nat_mul]
  have hh : (n : ℝ) * (-Real.log (1 / δ) / (n : ℝ)) = -Real.log (1 / δ) := by
    field_simp
  rw [hh, Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / δ)]
  field_simp

lemma warm_count_bound {t R a δ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hR : 0 < R) (ha : 0 < a) (n : ℕ) :
    let s := ⌈(Real.log (4 * R ^ 2 / a ^ 2) + (2 / (n : ℝ)) * Real.log (1 / δ)) / t⌉₊
    (1 - t) ^ s * R ^ 2 / a ^ 2 ≤ Real.exp (-(2 / (n : ℝ)) * Real.log (1 / δ)) / 4 := by
  let A := (2 / (n : ℝ)) * Real.log (1 / δ)
  let s := ⌈(Real.log (4 * R ^ 2 / a ^ 2) + A) / t⌉₊
  have hceil : (Real.log (4 * R ^ 2 / a ^ 2) + A) / t ≤ (s : ℝ) := Nat.le_ceil _
  have htime : Real.log (4 * R ^ 2 / a ^ 2) + A ≤ t * s := by
    exact ((div_le_iff₀ ht).mp hceil).trans_eq (mul_comm _ _)
  have hp := SymmetricReverseFisherGeometry.one_sub_pow_le_exp ht.le ht1 s
  have he : Real.exp (-t * s) ≤ Real.exp (-Real.log (4 * R ^ 2 / a ^ 2) - A) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hx : Real.exp (-Real.log (4 * R ^ 2 / a ^ 2) - A) * R ^ 2 / a ^ 2 = Real.exp (-A) / 4 := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * R ^ 2 / a ^ 2), Real.exp_neg]
    field_simp
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hp.trans he) (sq_nonneg R)) (sq_nonneg a)
  change (1 - t) ^ s * R ^ 2 / a ^ 2 ≤ _
  calc
    _ ≤ _ := hb
    _ = _ := by rw [hx]; congr 2; dsimp [A]; ring

lemma refinement_count_bound {c r ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hr : 0 < r) (hε : 0 < ε) :
    let k := ⌈(2 / c) * Real.log (4 * r ^ 2 / ε ^ 2)⌉₊
    (1 - c / 2) ^ k * r ^ 2 ≤ ε ^ 2 / 4 := by
  let k := ⌈(2 / c) * Real.log (4 * r ^ 2 / ε ^ 2)⌉₊
  have hceil : (2 / c) * Real.log (4 * r ^ 2 / ε ^ 2) ≤ (k : ℝ) := Nat.le_ceil _
  have ht : Real.log (4 * r ^ 2 / ε ^ 2) ≤ (c / 2) * k := by
    have hh := mul_le_mul_of_nonneg_left hceil (half_pos hc).le
    have he : (c / 2) * ((2 / c) * Real.log (4 * r ^ 2 / ε ^ 2)) =
        Real.log (4 * r ^ 2 / ε ^ 2) := by field_simp
    rwa [he] at hh
  have hp := SymmetricReverseFisherGeometry.one_sub_pow_le_exp (half_pos hc).le
    (by linarith : c / 2 ≤ 1) k
  have he : Real.exp (-(c / 2) * k) ≤ Real.exp (-Real.log (4 * r ^ 2 / ε ^ 2)) := by
    apply Real.exp_le_exp.mpr
    linarith
  change (1 - c / 2) ^ k * r ^ 2 ≤ _
  calc
    _ ≤ Real.exp (-Real.log (4 * r ^ 2 / ε ^ 2)) * r ^ 2 :=
      mul_le_mul_of_nonneg_right (hp.trans he) (sq_nonneg r)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

lemma refinement_rounding_floor {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (d : ℕ) (hd : 0 < d) :
    (2 / c) * (1 + 2 / c) * (Real.sqrt d * (ε * c / (8 * Real.sqrt d))) ^ 2 ≤
      3 * ε ^ 2 / 32 := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd'
  have he : Real.sqrt d * (ε * c / (8 * Real.sqrt d)) = ε * c / 8 := by field_simp
  rw [he]
  have hf : (2 / c) * (1 + 2 / c) * (ε * c / 8) ^ 2 = ε ^ 2 * (c + 2) / 32 := by
    field_simp
    ring
  rw [hf]
  nlinarith [mul_le_mul_of_nonneg_left hc1 (sq_nonneg ε)]

lemma quantization_width_range {H spacing : ℝ} (hs : 0 < spacing) :
    let width := Nat.log2 ⌈2 * H / spacing⌉₊ + 1
    H ≤ spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2 := by
  let m := ⌈2 * H / spacing⌉₊
  have hm : 2 * H / spacing ≤ (m : ℝ) := Nat.le_ceil _
  have hn : m ≤ 2 ^ (Nat.log2 m + 1) - 1 := Nat.le_sub_one_of_lt Nat.lt_log2_self
  have hn' : (m : ℝ) ≤ ((2 ^ (Nat.log2 m + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hh := (div_le_iff₀ hs).mp (hm.trans hn')
  dsimp only
  nlinarith

lemma worker_local_depth {κ G n : ℝ} (hκ : 1 ≤ κ) (hG : 1 < G)
    (hn : 64 * κ * G ≤ n) :
    let T := min ⌊κ⌋₊ ⌊Real.log (n / (64 * κ)) / Real.log G⌋₊
    1 ≤ T ∧ (T : ℝ) ≤ κ ∧ 64 * κ * G ^ T ≤ n := by
  let T := min ⌊κ⌋₊ ⌊Real.log (n / (64 * κ)) / Real.log G⌋₊
  have hκ0 : 0 < κ := by linarith
  have hG0 : 0 < G := by linarith
  have hr : G ≤ n / (64 * κ) := by
    apply (le_div_iff₀ (by positivity : 0 < 64 * κ)).mpr
    nlinarith
  have hr0 : 0 < n / (64 * κ) := hG0.trans_le hr
  have hlG : 0 < Real.log G := Real.log_pos hG
  have hl : Real.log G ≤ Real.log (n / (64 * κ)) := Real.log_le_log hG0 hr
  have hquot : 1 ≤ Real.log (n / (64 * κ)) / Real.log G := (one_le_div hlG).mpr hl
  have hT1 : 1 ≤ T := Nat.le_min.mpr ⟨(Nat.one_le_floor_iff _).mpr hκ, (Nat.one_le_floor_iff _).mpr hquot⟩
  have hTκ : (T : ℝ) ≤ κ := (Nat.cast_le.mpr (Nat.min_le_left _ _)).trans (Nat.floor_le hκ0.le)
  have hTlog : (T : ℝ) ≤ Real.log (n / (64 * κ)) / Real.log G :=
    (Nat.cast_le.mpr (Nat.min_le_right _ _)).trans (Nat.floor_le (by linarith))
  have hpow : G ^ T ≤ n / (64 * κ) := by
    apply (Real.log_le_log_iff (pow_pos hG0 T) hr0).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hlG).mp hTlog
  refine ⟨hT1, hTκ, ?_⟩
  have hh := (le_div_iff₀ (by positivity : 0 < 64 * κ)).mp hpow
  nlinarith

end LongTails.Proofs.DistributedJacobianStrongGrowthTuning
