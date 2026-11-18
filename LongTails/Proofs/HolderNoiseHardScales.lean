import LongTails.Proofs.HolderNoiseHardScaling
import Mathlib.Algebra.Order.Floor.Ring
import LongTails.Proofs.FrontierChainWall

namespace LongTails.Proofs.HolderNoiseHardScales

noncomputable def spaceScale (ℓ ε : ℝ) : ℝ := 17600 * ε / ℓ
noncomputable def valueScale (ℓ ε : ℝ) : ℝ := 140800 * ε ^ 2 / ℓ

lemma spaceScale_pos {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) : 0 < spaceScale ℓ ε := by
  unfold spaceScale
  positivity

lemma valueScale_pos {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) : 0 < valueScale ℓ ε := by
  unfold valueScale
  positivity

lemma scale_ratio {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    valueScale ℓ ε / spaceScale ℓ ε = 8 * ε := by
  unfold valueScale spaceScale
  field_simp
  ring

lemma scale_smoothness {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    2200 * valueScale ℓ ε / spaceScale ℓ ε ^ 2 = ℓ := by
  unfold valueScale spaceScale
  field_simp
  ring

lemma scale_noise_norm {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    66 * valueScale ℓ ε / spaceScale ℓ ε = 528 * ε := by
  rw [mul_div_assoc, scale_ratio hℓ hε]
  ring

lemma scale_noise_lipschitz {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    10242 * valueScale ℓ ε / spaceScale ℓ ε ^ 2 ≤ 8 * ℓ := by
  have hs := scale_smoothness hℓ hε
  have ha := (valueScale_pos hℓ hε).le
  have hq : 0 ≤ valueScale ℓ ε / spaceScale ℓ ε ^ 2 := by positivity
  rw [mul_div_assoc] at hs ⊢
  nlinarith

lemma scale_holder_coefficient {ℓ ε ν : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (hν : 0 ≤ ν) :
    ((2 * (66 * valueScale ℓ ε / spaceScale ℓ ε)) ^ (2 - 2 * ν) *
      (10242 * valueScale ℓ ε / spaceScale ℓ ε ^ 2) ^ (2 * ν)) *
      (ε / ℓ) ^ (2 * ν) ≤ (2 : ℝ) ^ 22 * ε ^ 2 := by
  have ha := (valueScale_pos hℓ hε).le
  have hb := spaceScale_pos hℓ hε
  have hH : 0 ≤ 10242 * valueScale ℓ ε / spaceScale ℓ ε ^ 2 := by positivity
  have hr : 0 ≤ ε / ℓ := by positivity
  have hs : (10242 * valueScale ℓ ε / spaceScale ℓ ε ^ 2) * (ε / ℓ) ≤ 1056 * ε := by
    have h := mul_le_mul_of_nonneg_right (scale_noise_lipschitz hℓ hε) hr
    have he : (8 * ℓ) * (ε / ℓ) = 8 * ε := by field_simp
    rw [he] at h
    linarith
  rw [scale_noise_norm hℓ hε, show 2 * (528 * ε) = 1056 * ε by ring, mul_assoc,
    ← Real.mul_rpow hH hr]
  calc _ ≤ (1056 * ε) ^ (2 - 2 * ν) * (1056 * ε) ^ (2 * ν) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hH hr) hs (by positivity))
        (Real.rpow_nonneg (by positivity) _)
    _ = (1056 * ε) ^ 2 := by
      rw [← Real.rpow_add (by positivity), show 2 - 2 * ν + 2 * ν = (2 : ℝ) by ring, Real.rpow_two]
    _ ≤ _ := by nlinarith [sq_nonneg ε]

lemma scale_variance {ℓ ε v σ : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (hv : 0 < v)
    (hσ : ε ^ 2 * v ≤ σ ^ 2) :
    (66 * valueScale ℓ ε / spaceScale ℓ ε) ^ 2 / ((2 : ℝ) ^ 24 / v) ≤ σ ^ 2 := by
  rw [scale_noise_norm hℓ hε]
  have he : (528 * ε) ^ 2 / ((2 : ℝ) ^ 24 / v) = (278784 / 16777216) * (ε ^ 2 * v) := by
    field_simp
    ring
  rw [he]
  nlinarith [mul_nonneg (sq_nonneg ε) hv.le]

lemma scale_holder {ℓ ε v M ν : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (hv : 0 < v)
    (hν : 0 ≤ ν) (hM : ε ^ 2 * v ≤ M * (ε / ℓ) ^ (2 * ν)) :
    ((2 * (66 * valueScale ℓ ε / spaceScale ℓ ε)) ^ (2 - 2 * ν) *
      (10242 * valueScale ℓ ε / spaceScale ℓ ε ^ 2) ^ (2 * ν) / ((2 : ℝ) ^ 24 / v)) ≤ M := by
  have hr : 0 < (ε / ℓ) ^ (2 * ν) := Real.rpow_pos_of_pos (div_pos hε hℓ) _
  have hp : 0 < (2 : ℝ) ^ 24 / v := by positivity
  apply (mul_le_mul_iff_left₀ hr).mp
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  have hc := scale_holder_coefficient hℓ hε hν
  have hm := mul_le_mul_of_nonneg_right hM (show 0 ≤ (2 : ℝ) ^ 24 / v by positivity)
  have he : (ε ^ 2 * v) * ((2 : ℝ) ^ 24 / v) = (2 : ℝ) ^ 24 * ε ^ 2 := by field_simp
  rw [he] at hm
  nlinarith [sq_nonneg ε]

end LongTails.Proofs.HolderNoiseHardScales

namespace LongTails.Proofs.HolderNoiseHardLength

open HolderNoiseHardScales

lemma length_bounds (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    8 * N * p ≤ (⌈8 * N * p⌉₊ : ℝ) ∧
      (⌈8 * N * p⌉₊ : ℝ) + 1 ≤ 8 * N * p + 2 := by
  constructor
  · exact Nat.le_ceil _
  · have h := Nat.ceil_lt_add_one (show 0 ≤ 8 * N * p by positivity)
    linarith

lemma accuracy_margin {ℓ ε p : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (hp : 0 ≤ p) (N : ℕ) :
    ε < (valueScale ℓ ε / spaceScale ℓ ε) * (3 / 8 : ℝ) *
      (1 - N * p / ((⌈8 * N * p⌉₊ : ℝ) + 1)) := by
  rw [scale_ratio hℓ hε]
  have hk := (length_bounds N hp).1
  have hr : (N : ℝ) * p / ((⌈8 * N * p⌉₊ : ℝ) + 1) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  nlinarith

lemma probability_bounds {v : ℝ} (hv : (2 : ℝ) ^ 24 ≤ v) :
    0 < (2 : ℝ) ^ 24 / v ∧ (2 : ℝ) ^ 24 / v ≤ 1 := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  exact ⟨div_pos (by positivity) hv0, (div_le_one hv0).mpr hv⟩

lemma length_gap {D v : ℝ} (hD : (2 : ℝ) ^ 22 ≤ D) (hv : (2 : ℝ) ^ 24 ≤ v)
    (N : ℕ) (hN : (N : ℝ) ≤ D * v / (2 : ℝ) ^ 60) :
    1126400 * ((⌈8 * N * ((2 : ℝ) ^ 24 / v)⌉₊ : ℝ) + 1) ≤ D := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hp := probability_bounds hv
  have hn := mul_le_mul_of_nonneg_right hN hp.1.le
  have he : (D * v / (2 : ℝ) ^ 60) * ((2 : ℝ) ^ 24 / v) = D / (2 : ℝ) ^ 36 := by
    field_simp
  rw [he] at hn
  have hk := (length_bounds N hp.1.le).2
  norm_num at hn hD
  nlinarith

lemma length_le {D v : ℝ} (hD : (2 : ℝ) ^ 22 ≤ D) (hv : (2 : ℝ) ^ 24 ≤ v)
    (N : ℕ) (hN : (N : ℝ) ≤ D * v / (2 : ℝ) ^ 60) :
    (⌈8 * N * ((2 : ℝ) ^ 24 / v)⌉₊ : ℝ) + 1 ≤ D := by
  have h := length_gap hD hv N hN
  have hn : 0 ≤ (⌈8 * N * ((2 : ℝ) ^ 24 / v)⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith

lemma objective_gap_scale {ℓ ε Δ v : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε)
    (hD : (2 : ℝ) ^ 22 ≤ Δ * ℓ / ε ^ 2) (hv : (2 : ℝ) ^ 24 ≤ v)
    (N : ℕ) (hN : (N : ℝ) ≤ (Δ * ℓ / ε ^ 2) * v / (2 : ℝ) ^ 60) :
    8 * valueScale ℓ ε * ((⌈8 * N * ((2 : ℝ) ^ 24 / v)⌉₊ : ℝ) + 1) ≤ Δ := by
  have h := length_gap hD hv N hN
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ ε ^ 2 / ℓ by positivity)
  have he : (Δ * ℓ / ε ^ 2) * (ε ^ 2 / ℓ) = Δ := by field_simp
  rw [he] at hm
  calc
    _ = (1126400 * ((⌈8 * N * ((2 : ℝ) ^ 24 / v)⌉₊ : ℝ) + 1)) * (ε ^ 2 / ℓ) := by
      unfold valueScale
      ring
    _ ≤ _ := hm

end LongTails.Proofs.HolderNoiseHardLength

namespace LongTails.Proofs.HolderNoiseHardDimension

open FrontierChainWall

lemma radius_sq (k : ℕ) : radius k ^ 2 = 518400 * (k + 1) := by
  rw [radius, mul_pow, Real.sq_sqrt (by positivity)]
  norm_num

lemma dimension_margin {d k N : ℕ} {D A : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hd : (2 : ℝ) ^ 30 * (1 + D) ^ 3 * (1 + A) ≤ d)
    (hk : (k + 1 : ℕ) ≤ D) (hN : (N : ℝ) ≤ D * (1 + A)) :
    0 < (d : ℝ) - (k + 1) ∧
      4 * ((3 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * (radius k ^ 2 / (1 / 4) ^ 2)) ≤
        (d : ℝ) - (k + 1) := by
  let P := (1 + D) ^ 3 * (1 + A)
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hP : (k : ℝ) + 1 ≤ P := by
    have hs : 1 ≤ (1 + D) ^ 2 := one_le_pow₀ (by linarith : 1 ≤ 1 + D)
    have h1 : 1 + D ≤ (1 + D) ^ 3 := by nlinarith
    have h2 : (1 + D) ^ 3 ≤ P := by
      dsimp [P]
      nlinarith [mul_nonneg (show 0 ≤ (1 + D) ^ 3 by positivity) hA]
    have hk' : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
    linarith
  have hNk : ((N : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 ≤ P := by
    have hn : (N : ℝ) + 1 ≤ (1 + D) * (1 + A) := by nlinarith
    have hk' : (k : ℝ) + 1 ≤ 1 + D := by exact_mod_cast (show (k + 1 : ℕ) ≤ (1 + D : ℝ) by linarith)
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k + 1) hk' 2
    have hm := mul_le_mul hn hs (sq_nonneg ((k : ℝ) + 1)) (by positivity : 0 ≤ (1 + D) * (1 + A))
    exact hm.trans_eq (by dsimp [P]; ring)
  have hd' : 1073741824 * P ≤ (d : ℝ) := by
    norm_num [P, mul_assoc] at hd ⊢
    exact hd
  constructor
  · linarith
  · rw [radius_sq]
    have he : 4 * (3 * ((N : ℝ) + 1) * (k + 1 : ℕ) * (518400 * (k + 1) / (1 / 4) ^ 2)) =
        99532800 * (((N : ℝ) + 1) * ((k : ℝ) + 1) ^ 2) := by push_cast; ring
    rw [he]
    nlinarith

end LongTails.Proofs.HolderNoiseHardDimension
