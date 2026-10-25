import LongTails.Proofs.HeavyTailedProbeGeometry
import LongTails.Proofs.HeavyTailedSpectralGeometry

open scoped RealInnerProductSpace
open LongTails.Proofs.HeavyTailedProbeGeometry

namespace LongTails.Proofs.HeavyTailedSpectralPath

lemma log_product_deficit {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (sample : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {η ell p : ℝ} (hη : 0 ≤ η) (hell : 0 ≤ ell) (hηell : η * ell ≤ 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫) (hbound : ∀ v, ‖A v‖ ≤ ell * ‖v‖)
    (fallback v : EuclideanSpace ℝ (Fin d)) (hf : ‖fallback‖ = 1) (hv : ‖v‖ = 1)
    (n : ℕ)
    (hn : linearProduct (fun k => ContinuousLinearMap.id ℝ _ + η • sample k) n v ≠ 0) :
    let B := fun k => ContinuousLinearMap.id ℝ _ + η • sample k
    let path := normalizedPath B fallback v
    let err := fun k => sample k (path k) - A (path k)
    Real.log ‖linearProduct B n v‖ - n * Real.log (1 + η * ell) ≤
      -(η / 4) * ∑ k ∈ Finset.range n, (ell - ⟪path k, A (path k)⟫) +
      (∑ k ∈ Finset.range n,
        η * ⟪path k + η • A (path k), err k⟫ / ‖path k + η • A (path k)‖ ^ 2) +
      2 * η ^ p * ∑ k ∈ Finset.range n, ‖err k‖ ^ p := by
  intro B path err
  have hstep (k : ℕ) (hk : k ∈ Finset.range n) :
      Real.log ‖B k (path k)‖ - Real.log (1 + η * ell) ≤
        -(η * (ell - ⟪path k, A (path k)⟫)) / 4 +
        η * ⟪path k + η • A (path k), err k⟫ / ‖path k + η • A (path k)‖ ^ 2 +
        2 * η ^ p * ‖err k‖ ^ p := by
    have hunit : ‖path k‖ = 1 := normalizedPath_norm B hf hv k
    have hkn := Finset.mem_range.mp hk
    have hpre := linearProduct_prefix_ne_zero B v
      (show k + 1 ≤ n from Finset.mem_range.mp hk) hn
    have hprev := linearProduct_prefix_ne_zero B v (by omega : k ≤ n) hn
    have hnonzero : B k (path k) ≠ 0 := by
      dsimp only [path]
      rw [normalizedPath_eq_product B fallback v hv k hprev, map_smul]
      exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hprev)) hpre
    have heq : path k + η • A (path k) + η • err k = B k (path k) := by
      simp only [err, B, add_apply, smul_apply, ContinuousLinearMap.id_apply, smul_sub]
      abel
    have hh := HeavyTailedSpectralGeometry.shifted_rayleigh_log_noise hunit hη hell hηell
      (hpos (path k)) (by simpa only [hunit, mul_one] using hbound (path k)) hp hp2
      (by rwa [heq])
    rwa [heq] at hh
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib, product_log_sum B fallback v hv n hn] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  convert hsum using 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma average_deficit_of_growth {d : ℕ} (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (sample : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {η ell p γ : ℝ} (hη : 0 < η) (hell : 0 ≤ ell) (hηell : η * ell ≤ 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫) (hbound : ∀ v, ‖A v‖ ≤ ell * ‖v‖)
    (fallback v : EuclideanSpace ℝ (Fin d)) (hf : ‖fallback‖ = 1) (hv : ‖v‖ = 1)
    (n : ℕ)
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * d)) + 2) ≤ η * n * γ) :
    let B := fun k => ContinuousLinearMap.id ℝ _ + η • sample k
    let path := normalizedPath B fallback v
    let err := fun k => sample k (path k) - A (path k)
    ((1 + η * ell) ^ n / 2) ^ 2 / (2 * d) ≤ ‖linearProduct B n v‖ ^ 2 →
    (∑ k ∈ Finset.range n,
      η * ⟪path k + η • A (path k), err k⟫ / ‖path k + η • A (path k)‖ ^ 2) ≤ 1 →
    2 * η ^ p * (∑ k ∈ Finset.range n, ‖err k‖ ^ p) ≤ 1 →
    (∑ k ∈ Finset.range n, (ell - ⟪path k, A (path k)⟫)) ≤ n * γ / 2 := by
  intro B path err hg hM hR
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < 1 + η * ell := by positivity
  have hnonzero : linearProduct B n v ≠ 0 := by
    intro hh
    rw [hh, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hg
    have hpositive : 0 < ((1 + η * ell) ^ n / 2) ^ 2 / (2 * d) := by positivity
    linarith
  have hlower := HeavyTailedSpectralGeometry.logarithm_of_squared_growth ha
    (norm_nonneg (linearProduct B n v)) hd0 n hg
  have hupper := log_product_deficit A sample hη.le hell hηell hp hp2 hpos hbound
    fallback v hf hv n hnonzero
  change Real.log ‖linearProduct B n v‖ - n * Real.log (1 + η * ell) ≤
    -(η / 4) * (∑ k ∈ Finset.range n, (ell - ⟪path k, A (path k)⟫)) +
    (∑ k ∈ Finset.range n,
      η * ⟪path k + η • A (path k), err k⟫ / ‖path k + η • A (path k)‖ ^ 2) +
    2 * η ^ p * (∑ k ∈ Finset.range n, ‖err k‖ ^ p) at hupper
  nlinarith

end LongTails.Proofs.HeavyTailedSpectralPath
