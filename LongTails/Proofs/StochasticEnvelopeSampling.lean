import LongTails.Proofs.GdPL
import LongTails.Proofs.MultiplicativeRobustConfidence
import Mathlib.Algebra.Order.Chebyshev
import LongTails.Proofs.HeavyTailedMomentBounds
import LongTails.Proofs.HilbertSmallMoments
import LongTails.Proofs.MultiplicativeRobustSampling
import LongTails.Algorithms.StochasticEnvelopePilot

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.StochasticEnvelopeSampling

open OracleTemplate.MultiplicativeRobustEstimator

lemma ae_eq_of_fourth_moment_zero {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} {X : Ω → E} {u : E}
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 4) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 4 ∂P) ≤ 0) : ∀ᵐ ω ∂P, X ω = u := by
  have he : (∫ ω, ‖X ω - u‖ ^ 4 ∂P) = 0 :=
    le_antisymm hm (integral_nonneg (fun _ => by positivity))
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω =>
    (show (0 : ℝ) ≤ ‖X ω - u‖ ^ 4 by positivity)) hi).mp he
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hω))


lemma lower_power_moment {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E} (hX : Measurable X) {p q : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (hq4 : q ≤ p) (hi : Integrable (fun ω => ‖X ω‖ ^ p) P) :
    Integrable (fun ω => ‖X ω‖ ^ q) P ∧
      (∫ ω, ‖X ω‖ ^ q ∂P) ≤ (∫ ω, ‖X ω‖ ^ p ∂P) ^ (q / p) := by
  have hb (ω : Ω) : ‖X ω‖ ^ q ≤ 1 + ‖X ω‖ ^ p := by
    by_cases h : ‖X ω‖ ≤ 1
    · have hh := Real.rpow_le_rpow (norm_nonneg _) h hq
      simp only [Real.one_rpow] at hh
      linarith [Real.rpow_nonneg (norm_nonneg (X ω)) p]
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hq4
      exact hh.trans (le_add_of_nonneg_left zero_le_one)
  have hqi : Integrable (fun ω => ‖X ω‖ ^ q) P := by
    apply ((integrable_const 1).add hi).mono' (hX.norm.pow_const q).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hb ω)
  have he (ω : Ω) : (‖X ω‖ ^ p : ℝ) ^ (q / p) = ‖X ω‖ ^ q := by
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have hqi' : Integrable (fun ω => (‖X ω‖ ^ p : ℝ) ^ (q / p)) P := by
    simpa only [he] using hqi
  refine ⟨hqi, ?_⟩
  have hh := (Real.concaveOn_rpow (by positivity : 0 ≤ q / p)
    ((div_le_one hp).mpr hq4)).le_map_integral
    (Real.continuous_rpow_const (by positivity : 0 ≤ q / p)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (norm_nonneg (X ω)) p)) hi hqi'
  simpa only [he] using hh


lemma difference_moment {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y) (z : E)
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hiX : Integrable (fun ω => ‖X ω - z‖ ^ r) P)
    (hiY : Integrable (fun ω => ‖Y ω - z‖ ^ r) P) :
    Integrable (fun ω => ‖X ω - Y ω‖ ^ r) P ∧
      (∫ ω, ‖X ω - Y ω‖ ^ r ∂P) ≤
        2 * ((∫ ω, ‖X ω - z‖ ^ r ∂P) + ∫ ω, ‖Y ω - z‖ ^ r ∂P) := by
  have hpoint (ω : Ω) : ‖X ω - Y ω‖ ^ r ≤ 2 * (‖X ω - z‖ ^ r + ‖Y ω - z‖ ^ r) := by
    have hh := HilbertSmallMoments.addition_power_bound (X ω - z) (-(Y ω - z)) hr hr2
    rw [show X ω - z + -(Y ω - z) = X ω - Y ω by abel, norm_neg] at hh
    exact hh
  have hi : Integrable (fun ω => ‖X ω - Y ω‖ ^ r) P := by
    apply ((hiX.add hiY).const_mul 2).mono' ((hX.sub hY).norm.pow_const r).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hpoint ω
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi ((hiX.add hiY).const_mul 2) hpoint
  change (∫ ω, ‖X ω - Y ω‖ ^ r ∂P) ≤
    (∫ ω, 2 * (‖X ω - z‖ ^ r + ‖Y ω - z‖ ^ r) ∂P) at hh
  simpa only [integral_const_mul, integral_add hiX hiY] using hh

lemma confidence_allocation (K : ℕ) {η : ℝ} (hη : 0 < η) :
    let n := 7 + ⌈2 * Real.log (1 + (K + 1 : ℝ) / η)⌉₊
    8 ≤ n + 1 ∧ (K + 1 : ℝ) * (1 / 2 : ℝ) ^ (n + 1) ≤ η := by
  dsimp only
  refine ⟨by omega, ?_⟩
  have hh := OracleTemplate.PLGradient.geometric_budget 2 1 (K + 1) η
    (by norm_num) (by norm_num) (by positivity) hη
    (7 + ⌈2 * Real.log (1 + (K + 1 : ℝ) / η)⌉₊ + 1) (by simp only [div_one]; omega)
  norm_num only [div_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hh
  simpa only [mul_comm] using hh

variable {E : Type*} [NormedAddCommGroup E]

lemma medoid_power_domination {n : ℕ} (v : Fin (n + 1) → E) (u : E)
    (hn : 8 ≤ n + 1) (k : ℕ) :
    (n + 1 : ℝ) ^ 2 * ‖medoid v - u‖ ^ (2 * (k + 1)) ≤
      4608 ^ (k + 1) * ∑ ij ∈ (Finset.univ : Finset (Fin (n + 1))).offDiag,
        ‖v ij.1 - u‖ ^ (k + 1) * ‖v ij.2 - u‖ ^ (k + 1) := by
  classical
  let S := (Finset.univ : Finset (Fin (n + 1))).offDiag
  let b := fun ij : Fin (n + 1) × Fin (n + 1) => ‖v ij.1 - u‖ * ‖v ij.2 - u‖
  have hb (ij : Fin (n + 1) × Fin (n + 1)) : 0 ≤ b ij := by dsimp [b]; positivity
  have hc : (S.card : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    dsimp [S]
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show (n + 1) * (n + 1) - (n + 1) ≤ (n + 1) ^ 2 by
      simpa only [pow_two] using Nat.sub_le ((n + 1) * (n + 1)) (n + 1))
  have h0 := medoid_square_domination v u hn
  have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ (n + 1 : ℝ)^2 * ‖medoid v - u‖^2) h0 (k + 1)
  have h2 : (∑ ij ∈ S, b ij) ^ (k + 1) ≤
      ((n + 1 : ℝ)^2)^k * ∑ ij ∈ S, (b ij) ^ (k + 1) := by
    apply (pow_sum_le_card_mul_sum_pow (fun ij _ => hb ij) k).trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc k)
      (Finset.sum_nonneg fun ij _ => pow_nonneg (hb ij) _)
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (4608 : ℝ)^(k + 1))
  simp only [mul_pow, ← pow_mul] at h1
  change (n + 1 : ℝ)^(2*(k + 1)) * ‖medoid v-u‖^(2*(k + 1)) ≤
    4608^(k + 1) * (∑ ij ∈ S, b ij)^(k + 1) at h1
  have he : (n + 1 : ℝ)^(2*(k + 1)) = ((n + 1 : ℝ)^2)^k * (n + 1 : ℝ)^2 := by
    rw [← pow_succ, pow_mul]
  have hp : 0 < ((n + 1 : ℝ)^2)^k := by positivity
  have h4 : ((n + 1 : ℝ)^2)^k * ((n + 1 : ℝ)^2 * ‖medoid v-u‖^(2*(k + 1))) ≤
      ((n + 1 : ℝ)^2)^k * (4608^(k + 1) * ∑ ij ∈ S, (b ij)^(k + 1)) := by
    rw [← mul_assoc, ← he]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h1.trans h3
  have h5 := (mul_le_mul_iff_right₀ hp).mp h4
  simpa only [S, b, mul_pow] using h5

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma fourth_moment_of_affine_bound {X Y : Ω → ℝ} (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hi : Integrable (fun ω => X ω ^ 4) P) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdom : ∀ ω, Y ω ≤ A * X ω + B) :
    Integrable (fun ω => Y ω ^ 4) P ∧
      (∫ ω, Y ω ^ 4 ∂P) ≤ 8 * A ^ 4 * (∫ ω, X ω ^ 4 ∂P) + 8 * B ^ 4 := by
  have hb (ω : Ω) : Y ω ^ 4 ≤ 8 * A ^ 4 * X ω ^ 4 + 8 * B ^ 4 := by
    have h₁ := pow_le_pow_left₀ (hY0 ω) (hdom ω) 4
    have h₂ := add_pow_le (mul_nonneg hA (hX0 ω)) hB 4
    norm_num only [Nat.reduceSub, Nat.reducePow, mul_pow] at h₂
    nlinarith only [h₁, h₂]
  have hmajor : Integrable (fun ω => 8 * A ^ 4 * X ω ^ 4 + 8 * B ^ 4) P :=
    (hi.const_mul _).add (integrable_const _)
  have hYi : Integrable (fun ω => Y ω ^ 4) P := by
    apply hmajor.mono' (hY.pow_const 4).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hY0 ω) _)]
      exact hb ω)
  refine ⟨hYi, (integral_mono hYi hmajor hb).trans_eq ?_⟩
  rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma refined_radius_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {S U : Ω → ℝ} (hU : Measurable U)
    (hS0 : ∀ ω, 0 ≤ S ω) (hU0 : ∀ ω, 0 ≤ U ω)
    {κ r t : ℝ} (hκ : 1 ≤ κ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hi : Integrable (fun ω => S ω ^ 4) P)
    (hm : (∫ ω, S ω ^ 4 ∂P) ≤ 4096 * κ ^ 4 * (r + t) ^ 4)
    (hdom : ∀ ω, U ω ≤ 144 * Real.sqrt κ * S ω + 128 * t) :
    Integrable (fun ω => U ω ^ 4) P ∧
      (∫ ω, U ω ^ 4 ∂P) ≤ 2 ^ 48 * κ ^ 6 * (r + t) ^ 4 := by
  have hh := fourth_moment_of_affine_bound hU hS0 hU0 hi
    (by positivity : 0 ≤ 144 * Real.sqrt κ) (by positivity : 0 ≤ 128 * t) hdom
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hk0 : 0 ≤ κ := by linarith
  have hk6 : 1 ≤ κ ^ 6 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hκ 6
  have ht4 : t ^ 4 ≤ κ ^ 6 * (r + t) ^ 4 := by
    calc
      _ ≤ (r + t) ^ 4 := pow_le_pow_left₀ ht (by linarith) 4
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hk6 (show 0 ≤ (r + t) ^ 4 by positivity)]
  have hsqrt : (Real.sqrt κ) ^ 4 = κ ^ 2 := by
    calc
      _ = ((Real.sqrt κ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hk0]
  have hscale := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ 8 * (144 * Real.sqrt κ) ^ 4 by positivity)
  norm_num only [mul_pow, hsqrt] at hscale ⊢
  nlinarith only [hscale, ht4, mul_nonneg (pow_nonneg hk0 6) (show 0 ≤ (r + t) ^ 4 by positivity)]

omit [SecondCountableTopology E] in
lemma rough_radius_fourth_moment {X : Ω → E} (hX : Measurable X) (u : E)
    {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 4) P) :
    Integrable (fun ω => (4 * (‖X ω‖ + s) / μ) ^ 4) P ∧
      (∫ ω, (4 * (‖X ω‖ + s) / μ) ^ 4 ∂P) ≤
        2048 / μ ^ 4 * ((∫ ω, ‖X ω - u‖ ^ 4 ∂P) + (‖u‖ + s) ^ 4) := by
  have hh := fourth_moment_of_affine_bound (P := P)
    (X := fun ω => ‖X ω - u‖) (Y := fun ω => 4 * (‖X ω‖ + s) / μ)
    (A := 4 / μ) (B := 4 * (‖u‖ + s) / μ)
    (by fun_prop) (fun ω => norm_nonneg _) (fun ω => by positivity) hi
    (by positivity) (by positivity) (fun ω => by
      have hn := norm_le_norm_sub_add (X ω) u
      rw [div_mul_eq_mul_div, ← add_div]
      apply (div_le_div_iff_of_pos_right hμ).mpr
      nlinarith only [hn])
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  field_simp
  ring

omit [SecondCountableTopology E] in
lemma rough_radius_scaled_moment {X : Ω → E} (hX : Measurable X) (u : E)
    {μ s κ r : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (hκ : 1 ≤ κ)
    (hu : ‖u‖ ≤ μ * κ * r)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 4) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 4 ∂P) ≤ (‖u‖ + s) ^ 4) :
    Integrable (fun ω => (4 * (‖X ω‖ + s) / μ) ^ 4) P ∧
      (∫ ω, (4 * (‖X ω‖ + s) / μ) ^ 4 ∂P) ≤
        4096 * κ ^ 4 * (r + s / μ) ^ 4 := by
  obtain ⟨hSi, hSm⟩ := rough_radius_fourth_moment hX u hμ hs hi
  refine ⟨hSi, hSm.trans ?_⟩
  have hsκ : s ≤ κ * s := by nlinarith
  have hb : ‖u‖ + s ≤ μ * κ * (r + s / μ) := by
    have he : μ * κ * (r + s / μ) = μ * κ * r + κ * s := by field_simp
    rw [he]
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ‖u‖ + s) hb 4
  have hh := mul_le_mul_of_nonneg_left (add_le_add hm (le_refl ((‖u‖ + s) ^ 4)))
    (by positivity : 0 ≤ 2048 / μ ^ 4)
  apply hh.trans
  have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4096 / μ ^ 4)
  convert ht using 1 <;> field_simp
  ring

omit [SecondCountableTopology E] in
lemma lower_power_from_fourth {X : Ω → E} (hX : Measurable X) {q : ℝ}
    (hq : 0 ≤ q) (hq4 : q ≤ 4) (hi : Integrable (fun ω => ‖X ω‖ ^ 4) P) :
    Integrable (fun ω => ‖X ω‖ ^ q) P ∧
      (∫ ω, ‖X ω‖ ^ q ∂P) ≤ (∫ ω, ‖X ω‖ ^ 4 ∂P) ^ (q / 4) := by
  have hb (ω : Ω) : ‖X ω‖ ^ q ≤ 1 + ‖X ω‖ ^ 4 := by
    by_cases h : ‖X ω‖ ≤ 1
    · have hh := Real.rpow_le_rpow (norm_nonneg _) h hq
      simp only [Real.one_rpow] at hh
      linarith [pow_nonneg (norm_nonneg (X ω)) 4]
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hq4
      rw [Real.rpow_ofNat] at hh
      exact hh.trans (le_add_of_nonneg_left zero_le_one)
  have hqi : Integrable (fun ω => ‖X ω‖ ^ q) P := by
    apply ((integrable_const 1).add hi).mono' (hX.norm.pow_const q).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hb ω)
  have he (ω : Ω) : (‖X ω‖ ^ 4 : ℝ) ^ (q / 4) = ‖X ω‖ ^ q := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    congr 1
    ring
  have hqi' : Integrable (fun ω => (‖X ω‖ ^ 4 : ℝ) ^ (q / 4)) P := by
    simpa only [he] using hqi
  refine ⟨hqi, ?_⟩
  have hh := (Real.concaveOn_rpow (by positivity : 0 ≤ q / 4)
    (by linarith : q / 4 ≤ 1)).le_map_integral
    (Real.continuous_rpow_const (by positivity : 0 ≤ q / 4)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (norm_nonneg (X ω)) 4)) hi hqi'
  simpa only [he] using hh

omit [SecondCountableTopology E] in
lemma good_event_moment {X : Ω → E} (hX : Measurable X) {p a : ℝ} {A : Set Ω}
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a) (hA : MeasurableSet A)
    (hi : Integrable (fun ω => ‖X ω‖ ^ 4) P)
    (hgood : ∀ ω ∉ A, ‖X ω‖ ^ p ≤ a) :
    (∫ ω, ‖X ω‖ ^ p ∂P) ≤ a +
      (∫ ω, ‖X ω‖ ^ 4 ∂P) ^ (p / 4) * (P.real A) ^ (1 / 2 : ℝ) := by
  have hlo := lower_power_from_fourth hX hp (by linarith) hi
  have hhi := lower_power_from_fourth hX (by positivity : 0 ≤ 2 * p)
    (by linarith : 2 * p ≤ 4) hi
  have he (ω : Ω) : (‖X ω‖ ^ p) ^ (2 : ℕ) = ‖X ω‖ ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hsq : Integrable (fun ω => (‖X ω‖ ^ p) ^ (2 : ℕ)) P := by
    simpa only [he] using hhi.1
  have hmem : MemLp (fun ω => ‖X ω‖ ^ p) (ENNReal.ofReal 2) P := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq (hX.norm.pow_const p).aestronglyMeasurable).mpr hsq
  have hh := HeavyTailedMomentBounds.mean_le_threshold_add_tail
    (X := fun ω => ‖X ω‖ ^ p) Real.HolderConjugate.two_two hmem hlo.1
    (fun ω => Real.rpow_nonneg (norm_nonneg _) _) ha hA hgood
  have hpow := Real.rpow_le_rpow (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _))
    hhi.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he' : ((∫ ω, ‖X ω‖ ^ 4 ∂P) ^ (2 * p / 4)) ^ (1 / 2 : ℝ) =
      (∫ ω, ‖X ω‖ ^ 4 ∂P) ^ (p / 4) := by
    rw [← Real.rpow_mul (integral_nonneg (fun ω => pow_nonneg (norm_nonneg _) _))]
    congr 1
    ring
  rw [he'] at hpow
  simp only [Real.rpow_two, he] at hh
  exact hh.trans (add_le_add (le_refl a) (mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ (P.real A) ^ (1 / 2 : ℝ) by positivity)))

lemma medoid_even_moment {X : Ω → E} (hX : Measurable X) (u : E) (k : ℕ)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ (k + 1)) P) (n : ℕ) (hn : 8 ≤ n + 1) :
    Integrable (fun ξ : Fin (n + 1) → Ω =>
      ‖medoid (fun i => X (ξ i)) - u‖ ^ (2 * (k + 1))) (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin (n + 1) → Ω, ‖medoid (fun i => X (ξ i)) - u‖ ^ (2 * (k + 1))
      ∂Measure.pi (fun _ => P)) ≤
      4608 ^ (k + 1) * (∫ ω, ‖X ω - u‖ ^ (k + 1) ∂P) ^ 2 := by
  classical
  let Q := Measure.pi (fun _ : Fin (n + 1) => P)
  let e : Fin (n + 1) → (Fin (n + 1) → Ω) → ℝ := fun i ξ => ‖X (ξ i) - u‖ ^ (k + 1)
  let S := (Finset.univ : Finset (Fin (n + 1))).offDiag
  have hem (i : Fin (n + 1)) : Measurable (e i) := by dsimp [e]; fun_prop
  have hei (i : Fin (n + 1)) : Integrable (e i) Q :=
    ((measurePreserving_eval (fun _ : Fin (n + 1) => P) i).integrable_comp
      hi.aestronglyMeasurable).mpr hi
  have heind : ProbabilityTheory.iIndepFun e Q :=
    ProbabilityTheory.iIndepFun_pi (fun _ => (((hX.sub measurable_const).norm).pow_const _).aemeasurable)
  have hpair (ij : Fin (n + 1) × Fin (n + 1)) (hij : ij ∈ S) :
      Integrable (fun ξ => e ij.1 ξ * e ij.2 ξ) Q :=
    (heind.indepFun (Finset.mem_offDiag.mp hij).2.2).integrable_mul (hei _) (hei _)
  let F : (Fin (n + 1) → Ω) → ℝ := fun ξ =>
    4608 ^ (k + 1) / (n + 1 : ℝ)^2 * ∑ ij ∈ S, e ij.1 ξ * e ij.2 ξ
  have hFi : Integrable F Q := (integrable_finsetSum S hpair).const_mul _
  have hdom (ξ : Fin (n + 1) → Ω) :
      ‖medoid (fun i => X (ξ i)) - u‖ ^ (2 * (k + 1)) ≤ F ξ := by
    have h := medoid_power_domination (fun i => X (ξ i)) u hn k
    dsimp [F, S, e]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n + 1)^2)).mpr
    simpa only [mul_comm] using h
  have hmi : Integrable (fun ξ : Fin (n + 1) → Ω =>
      ‖medoid (fun i => X (ξ i)) - u‖ ^ (2 * (k + 1))) Q := by
    apply hFi.mono' (by
      apply Measurable.aestronglyMeasurable
      exact (((measurable_medoid.comp (Measurable.of_eval (fun i =>
        hX.comp (measurable_pi_apply i)))).sub measurable_const).norm).pow_const _)
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hdom ξ)
  refine ⟨hmi, (integral_mono hmi hFi hdom).trans ?_⟩
  have heint (i : Fin (n + 1)) :
      (∫ ξ, e i ξ ∂Q) = ∫ ω, ‖X ω - u‖ ^ (k + 1) ∂P := by
    have hm := measurePreserving_eval (fun _ : Fin (n + 1) => P) i
    exact (show ProbabilityTheory.HasLaw (Function.eval i) P Q from
      ⟨hm.measurable.aemeasurable, hm.map_eq⟩).integral_comp hi.aestronglyMeasurable
  have hpint (ij : Fin (n + 1) × Fin (n + 1)) (hij : ij ∈ S) :
      (∫ ξ, e ij.1 ξ * e ij.2 ξ ∂Q) = (∫ ω, ‖X ω - u‖ ^ (k + 1) ∂P)^2 := by
    rw [(heind.indepFun (Finset.mem_offDiag.mp hij).2.2).integral_fun_mul_eq_mul_integral
      (hem _).aestronglyMeasurable (hem _).aestronglyMeasurable, heint, heint, pow_two]
  change (∫ ξ, 4608 ^ (k + 1) / (n + 1 : ℝ)^2 * ∑ ij ∈ S, e ij.1 ξ * e ij.2 ξ ∂Q) ≤ _
  rw [integral_const_mul, integral_finsetSum S hpair]
  rw [Finset.sum_congr rfl hpint]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (S.card : ℝ) ≤ (n + 1 : ℝ)^2 := by
    dsimp [S]
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show (n + 1) * (n + 1) - (n + 1) ≤ (n + 1) ^ 2 by
      simpa only [pow_two] using Nat.sub_le ((n + 1) * (n + 1)) (n + 1))
  calc
    _ ≤ 4608 ^ (k + 1) / (n + 1 : ℝ)^2 *
        ((n + 1 : ℝ)^2 * (∫ ω, ‖X ω-u‖ ^ (k + 1) ∂P)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp

lemma nested_medoid_fourth_moment {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω - u‖) P) (n : ℕ) (hn : 8 ≤ n + 1) :
    let Q := Measure.pi (fun _ : Fin 8 => P)
    let Y := fun ξ : Fin 8 → Ω => medoid (fun i => X (ξ i))
    Integrable (fun ξ : Fin (n + 1) → (Fin 8 → Ω) =>
      ‖medoid (fun i => Y (ξ i)) - u‖ ^ 4) (Measure.pi fun _ => Q) ∧
    (∫ ξ : Fin (n + 1) → (Fin 8 → Ω), ‖medoid (fun i => Y (ξ i)) - u‖ ^ 4
      ∂Measure.pi (fun _ => Q)) ≤ 4608 ^ 4 * (∫ ω, ‖X ω - u‖ ∂P) ^ 4 := by
  let Q := Measure.pi (fun _ : Fin 8 => P)
  let Y := fun ξ : Fin 8 → Ω => medoid (fun i => X (ξ i))
  have hY : Measurable Y := measurable_medoid.comp
    (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  obtain ⟨hYi, hYb⟩ := medoid_even_moment hX u 0 (by simpa using hi) 7 (by norm_num)
  simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceMul, pow_one] at hYi hYb
  obtain ⟨hZi, hZb⟩ := medoid_even_moment (P := Q) hY u 1 hYi n hn
  simp only [Nat.reduceAdd, Nat.reduceMul] at hZi hZb
  refine ⟨hZi, hZb.trans ?_⟩
  have hp := pow_le_pow_left₀
    (integral_nonneg (fun ξ : Fin 8 → Ω => sq_nonneg ‖Y ξ - u‖)) hYb 2
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 4608 ^ 2)
  convert hm using 1
  ring

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma second_moment_tail {X : Ω → E} (u : E) {M : ℝ} (hM : 0 < M)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ 4608 * M ^ 2) :
    P.real {ω | 2048 * M < ‖X ω - u‖} ≤ 1 / 256 := by
  have hr : 0 < (2048 * M) ^ 2 := by positivity
  have h := (hi.div_const ((2048 * M) ^ 2)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => by positivity))
    (s := {ω | 2048 * M < ‖X ω - u‖}) (fun ω hω => by
      apply (one_le_div hr).mpr
      exact pow_le_pow_left₀ (by positivity) hω.le 2)
  have hb : P {ω | 2048 * M < ‖X ω - u‖} ≤ ENNReal.ofReal (1 / 256 : ℝ) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    apply (div_le_iff₀ hr).mpr
    nlinarith only [hm, sq_nonneg M]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 256)] using ht

lemma nested_medoid_failure {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω - u‖) P) {M : ℝ} (hM : 0 ≤ M)
    (hm : (∫ ω, ‖X ω - u‖ ∂P) ≤ M) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin 8 => P)
    let Y := fun ξ : Fin 8 → Ω => medoid (fun i => X (ξ i))
    (Measure.pi fun _ : Fin (n + 1) => Q)
      {ξ | 12288 * M < ‖medoid (fun i => Y (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  by_cases hzero : M = 0
  · have he : (∫ ω, ‖X ω - u‖ ∂P) = 0 :=
      le_antisymm (by simpa [hzero] using hm) (integral_nonneg (fun ω => norm_nonneg _))
    have hz := (integral_eq_zero_iff_of_nonneg (fun ω => norm_nonneg (X ω - u)) hi).mp he
    have hx : X =ᵐ[P] fun _ => u := by
      filter_upwards [hz] with ω hω
      exact sub_eq_zero.mp (norm_eq_zero.mp hω)
    have hrows := Measure.ae_eq_pi (fun _ : Fin 8 => hx)
    have hall := Measure.ae_eq_pi (fun _ : Fin (n + 1) => hrows)
    have hnull : (Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin 8 => P)
        {ξ | 12288 * M < ‖medoid (fun i => medoid (fun j => X (ξ i j))) - u‖} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hall] with ξ hξ
      have hc : (fun i : Fin (n + 1) => fun j : Fin 8 => X (ξ i j)) =
          fun _ _ => u := hξ
      have hc' : (fun i => medoid (fun j => X (ξ i j))) =
          (fun _ : Fin (n + 1) => u) := by
        change (fun i => medoid ((fun i : Fin (n + 1) => fun j : Fin 8 => X (ξ i j)) i)) = _
        rw [hc]
        simp [medoid]
      change ¬12288 * M < ‖medoid (fun i => medoid (fun j => X (ξ i j))) - u‖
      rw [hc']
      simp [medoid, hzero]
    simpa only [hnull] using (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) from bot_le)
  have hM : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
  let Q := Measure.pi (fun _ : Fin 8 => P)
  let Y := fun ξ : Fin 8 → Ω => medoid (fun i => X (ξ i))
  have hY : Measurable Y := measurable_medoid.comp
    (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  obtain ⟨hYi, hYb⟩ := medoid_even_moment hX u 0 (by simpa using hi) 7 (by norm_num)
  simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceMul, pow_one] at hYi hYb
  have hmoment : (∫ ξ, ‖Y ξ - u‖ ^ 2 ∂Q) ≤ 4608 * M ^ 2 := by
    exact hYb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun ω => norm_nonneg (X ω - u))) hm 2) (by norm_num))
  have ht := second_moment_tail u hM hYi hmoment
  have hf := medoid_failure_probability hY u (by positivity : 0 ≤ 2048 * M) ht n
  simpa only [show 6 * (2048 * M) = 12288 * M by ring] using hf

lemma fixed_batch_tuning {p : ℝ} (hp : 1 < p) :
    4 * (16777216 : ℝ) ^ p ≤
      (⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊ + 1 : ℝ) ^ (p - 1) := by
  have hpow : (1073741824 : ℝ) ^ p ≤
      (⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊ + 1 : ℝ) ^ (p - 1) := by
    have hb : (1073741824 : ℝ) ^ (p / (p - 1)) ≤
        (⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊ + 1 : ℝ) :=
      (Nat.le_ceil _).trans (by norm_num)
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (1073741824 : ℝ) ^ (p / (p - 1)))
      hb (by linarith : 0 ≤ p - 1)
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1073741824),
      div_mul_cancel₀ p (by linarith : p - 1 ≠ 0)] at hh
    exact hh
  apply le_trans ?_ hpow
  have h4 : (4 : ℝ) ≤ 4 ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) hp.le
  calc
    _ ≤ (4 : ℝ) ^ p * 16777216 ^ p :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (67108864 : ℝ) ^ p := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 16777216)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)

lemma batch_scaled_moment {B c M p v : ℝ} (hB : 0 < B) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hb : 4 * c ^ p ≤ B ^ (p - 1)) (hv : v ≤ (c * M) ^ p) :
    4 * B ^ (1 - p) * v ≤ M ^ p := by
  have hpos : 0 < B ^ (p - 1) := Real.rpow_pos_of_pos hB _
  rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg hB.le]
  apply (mul_le_mul_iff_right₀ hpos).mp
  have he : B ^ (p - 1) * (4 * (B ^ (p - 1))⁻¹ * v) = 4 * v := by
    field_simp
  rw [he]
  calc
    _ ≤ 4 * (c * M) ^ p := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = (4 * c ^ p) * M ^ p := by rw [Real.mul_rpow hc hM]; ring
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hM p)

lemma affine_tolerance_moment {p s a β g : ℝ} (hp : 1 ≤ p)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hg : 0 ≤ g) (haβ : a ≤ 512 * β) :
    s ^ p + a ^ p * g ^ p ≤ (16777216 * ((β * g + s) / 12288)) ^ p := by
  have hm := mul_le_mul_of_nonneg_right haβ hg
  have hb : s + a * g ≤ 16777216 * ((β * g + s) / 12288) := by
    have hn := mul_nonneg hβ hg
    nlinarith
  calc
    _ = s ^ p + (a * g) ^ p := by rw [Real.mul_rpow ha hg]
    _ ≤ (s + a * g) ^ p := Real.add_rpow_le_rpow_add hs (mul_nonneg ha hg) hp
    _ ≤ _ := Real.rpow_le_rpow (add_nonneg hs (mul_nonneg ha hg)) hb (by linarith)

omit [IsProbabilityMeasure P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma gap_distance_failure {X : Ω → E} (F : E → ℝ) (z : E) {μ D : ℝ}
    (hμ : 0 < μ) (hD : 0 < D)
    (hgap : ∀ ω, μ / 2 * ‖X ω - z‖ ^ 2 ≤ F (X ω) - F z)
    (hi : Integrable (fun ω => F (X ω) - F z) P)
    (hm : (∫ ω, F (X ω) - F z ∂P) ≤ μ * D ^ 2 / 2 ^ 17) :
    P.real {ω | D / 16 < ‖X ω - z‖} ≤ 1 / 256 := by
  have ht : 0 < μ * D ^ 2 / 512 := by positivity
  have hnonneg (ω : Ω) : 0 ≤ F (X ω) - F z :=
    (mul_nonneg (by positivity) (sq_nonneg _)).trans (hgap ω)
  have h := (hi.div_const (μ * D ^ 2 / 512)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (hnonneg ω) ht.le))
    (s := {ω | D / 16 < ‖X ω - z‖}) (fun ω hω => (one_le_div ht).mpr (by
      have hs : (D / 16) ^ 2 ≤ ‖X ω - z‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hω.le 2
      have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ μ / 2 by positivity)
      nlinarith [hgap ω]))
  have hb : P {ω | D / 16 < ‖X ω - z‖} ≤ ENNReal.ofReal (1 / 256 : ℝ) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    apply (div_le_iff₀ ht).mpr
    nlinarith [hm]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 256)] using hr

lemma gap_medoid_failure
    {X : Ω → E} (hX : Measurable X) (F : E → ℝ) (z : E) {μ D : ℝ}
    (hμ : 0 < μ) (hD : 0 < D)
    (hgap : ∀ ω, μ / 2 * ‖X ω - z‖ ^ 2 ≤ F (X ω) - F z)
    (hi : Integrable (fun ω => F (X ω) - F z) P)
    (hm : (∫ ω, F (X ω) - F z ∂P) ≤ μ * D ^ 2 / 2 ^ 17) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | D / 2 < ‖medoid (fun i => X (ξ i)) - z‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  apply (measure_mono ?_).trans
    (medoid_failure_probability hX z (by positivity : 0 ≤ D / 16)
      (gap_distance_failure F z hμ hD hgap hi hm) n)
  intro ξ hξ
  change D / 2 < _ at hξ
  change 6 * (D / 16) < _
  linarith


lemma rough_tolerance_moment {p s a g : ℝ} (hp : 1 ≤ p)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hg : 0 ≤ g) :
    s ^ p + a ^ p * g ^ p ≤ (16777216 * ((g + s) / 49152)) ^ p := by
  have hm := mul_le_mul_of_nonneg_right ha1 hg
  have hb : s + a * g ≤ 16777216 * ((g + s) / 49152) := by nlinarith
  calc
    _ = s ^ p + (a * g) ^ p := by rw [Real.mul_rpow ha hg]
    _ ≤ (s + a * g) ^ p := Real.add_rpow_le_rpow_add hs (mul_nonneg ha hg) hp
    _ ≤ _ := Real.rpow_le_rpow (add_nonneg hs (mul_nonneg ha hg)) hb (by linarith)

section Batch

variable [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

omit [CompleteSpace E] in
lemma measurable_robustMean (b n : ℕ) :
    Measurable (LongTails.Algorithms.StochasticEnvelopePilot.robustMean (E := E) (b := b) (n := n)) := by
  apply measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  apply measurable_medoid.comp
  apply Measurable.of_eval
  intro j
  exact measurable_blockMean.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma batch_first_moment {X : Ω₀ → E} (hX : Measurable X) (u : E)
    {p M : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hi : Integrable X P₀) (hmean : ∫ ω, X ω ∂P₀ = u)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P₀) (b : ℕ)
    (hb : 4 * (b + 1 : ℝ) ^ (1 - p) * (∫ ω, ‖X ω - u‖ ^ p ∂P₀) ≤ M ^ p) :
    Integrable (fun ξ : Fin (b + 1) → Ω₀ => ‖blockMean (fun i => X (ξ i)) - u‖)
      (Measure.pi fun _ => P₀) ∧
      (∫ ξ : Fin (b + 1) → Ω₀, ‖blockMean (fun i => X (ξ i)) - u‖
        ∂Measure.pi fun _ => P₀) ≤ M := by
  have hbi := (OracleTemplate.LightTail.finite_mean_integral hi (b + 1) (by omega)).1
  have hbin : Integrable (fun ξ : Fin (b + 1) → Ω₀ =>
      ‖blockMean (fun i => X (ξ i)) - u‖) (Measure.pi fun _ => P₀) := by
    simpa only [blockMean, one_div, Nat.cast_add, Nat.cast_one, Pi.sub_apply] using
      (hbi.sub (integrable_const u)).norm
  have hbp := HilbertSmallMoments.iid_centered_mean_power_bound
    hX hp hp2 hi u hpi hmean (b + 1) (by omega)
  have hbp' : Integrable (fun ξ : Fin (b + 1) → Ω₀ =>
      ‖blockMean (fun i => X (ξ i)) - u‖ ^ p) (Measure.pi fun _ => P₀) := by
    simpa only [blockMean, Nat.cast_add, Nat.cast_one] using hbp.1
  refine ⟨hbin, HilbertSmallMoments.first_power_from_moment hp hM hbin hbp' ?_⟩
  apply le_trans ?_ hb
  simpa only [blockMean, Nat.cast_add, Nat.cast_one] using hbp.2

lemma robustMean_contract {X : Ω₀ → E} (hX : Measurable X) (u : E)
    {p M : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hi : Integrable X P₀) (hmean : ∫ ω, X ω ∂P₀ = u)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P₀) (b n : ℕ) (hn : 8 ≤ n + 1)
    (hb : 4 * (b + 1 : ℝ) ^ (1 - p) * (∫ ω, ‖X ω - u‖ ^ p ∂P₀) ≤ M ^ p) :
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P₀
    let Z := fun ξ : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀ =>
      LongTails.Algorithms.StochasticEnvelopePilot.robustMean (fun i j k => X (ξ i j k))
    Integrable (fun ξ => ‖Z ξ - u‖ ^ 4) Q ∧
      (∫ ξ, ‖Z ξ - u‖ ^ 4 ∂Q) ≤ 4608 ^ 4 * M ^ 4 ∧
      Q {ξ | 12288 * M < ‖Z ξ - u‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let B := Measure.pi fun _ : Fin (b + 1) => P₀
  let Y := fun ξ : Fin (b + 1) → Ω₀ => blockMean (fun i => X (ξ i))
  have hY : Measurable Y := measurable_blockMean.comp
    (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  obtain ⟨hYi, hYb⟩ := batch_first_moment hX u hp hp2 hM hi hmean hpi b hb
  obtain ⟨hZi, hZb⟩ := nested_medoid_fourth_moment (P := B) hY u hYi n hn
  have hZt := nested_medoid_failure (P := B) hY u hYi hM hYb n
  refine ⟨hZi, hZb.trans ?_, hZt⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg (fun ξ => norm_nonneg (Y ξ - u))) hYb 4)
    (by norm_num)

lemma robustMean_affine {X : Ω₀ → E} (hX : Measurable X) (u : E)
    {p s a β : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hβ : 0 ≤ β) (haβ : a ≤ 512 * β)
    (hi : Integrable X P₀) (hmean : ∫ ω, X ω ∂P₀ = u)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P₀)
    (hm : (∫ ω, ‖X ω - u‖ ^ p ∂P₀) ≤ s ^ p + a ^ p * ‖u‖ ^ p)
    (n : ℕ) (hn : 8 ≤ n + 1) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P₀
    let Z := fun ξ : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀ =>
      LongTails.Algorithms.StochasticEnvelopePilot.robustMean (fun i j k => X (ξ i j k))
    Integrable (fun ξ => ‖Z ξ - u‖ ^ 4) Q ∧
      (∫ ξ, ‖Z ξ - u‖ ^ 4 ∂Q) ≤ 4608 ^ 4 * ((β * ‖u‖ + s) / 12288) ^ 4 ∧
      Q {ξ | β * ‖u‖ + s < ‖Z ξ - u‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  have hM : 0 ≤ (β * ‖u‖ + s) / 12288 := by positivity
  have hb : 4 * (b + 1 : ℝ) ^ (1 - p) * (∫ ω, ‖X ω - u‖ ^ p ∂P₀) ≤
      ((β * ‖u‖ + s) / 12288) ^ p :=
    batch_scaled_moment (by positivity) (by norm_num : (0 : ℝ) ≤ 16777216) hM
      (fixed_batch_tuning hp) (hm.trans (affine_tolerance_moment hp.le hs ha hβ (norm_nonneg _) haβ))
  have hh := robustMean_contract hX u hp.le hp2 hM hi hmean hpi b n hn hb
  have he : 12288 * ((β * ‖u‖ + s) / 12288) = β * ‖u‖ + s := by ring
  simpa only [he] using hh

lemma robustMean_rough {X : Ω₀ → E} (hX : Measurable X) (u : E)
    {p s a : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hi : Integrable X P₀) (hmean : ∫ ω, X ω ∂P₀ = u)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P₀)
    (hm : (∫ ω, ‖X ω - u‖ ^ p ∂P₀) ≤ s ^ p + a ^ p * ‖u‖ ^ p)
    (n : ℕ) (hn : 8 ≤ n + 1) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (n + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P₀
    let Z := fun ξ : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω₀ =>
      LongTails.Algorithms.StochasticEnvelopePilot.robustMean (fun i j k => X (ξ i j k))
    Integrable (fun ξ => ‖Z ξ - u‖ ^ 4) Q ∧
      (∫ ξ, ‖Z ξ - u‖ ^ 4 ∂Q) ≤ (‖u‖ + s) ^ 4 ∧
      Q {ξ | (‖u‖ + s) / 4 < ‖Z ξ - u‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  have hM : 0 ≤ (‖u‖ + s) / 49152 := by positivity
  have hb : 4 * (b + 1 : ℝ) ^ (1 - p) * (∫ ω, ‖X ω - u‖ ^ p ∂P₀) ≤
      ((‖u‖ + s) / 49152) ^ p :=
    batch_scaled_moment (by positivity) (by norm_num : (0 : ℝ) ≤ 16777216) hM
      (fixed_batch_tuning hp) (hm.trans (rough_tolerance_moment hp.le hs ha ha1 (norm_nonneg _)))
  obtain ⟨hZi, hZm, hZt⟩ := robustMean_contract hX u hp.le hp2 hM hi hmean hpi b n hn hb
  refine ⟨hZi, hZm.trans ?_, ?_⟩
  · rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hn := norm_nonneg u
    nlinarith
  · have he : 12288 * ((‖u‖ + s) / 49152) = (‖u‖ + s) / 4 := by ring
    simpa only [he] using hZt

end Batch

lemma final_fourth_moment {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : Ω → ℝ} {Y : Ω → E} (hY : Measurable Y) (target : E)
    (hU0 : ∀ ω, 0 ≤ U ω) {κ r t : ℝ} (hκ : 1 ≤ κ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hi : Integrable (fun ω => U ω ^ 4) P)
    (hm : (∫ ω, U ω ^ 4 ∂P) ≤ 2 ^ 48 * κ ^ 6 * (r + t) ^ 4)
    (hdom : ∀ ω, ‖Y ω - target‖ ≤ r + 2 * U ω) :
    Integrable (fun ω => ‖Y ω - target‖ ^ 4) P ∧
      (∫ ω, ‖Y ω - target‖ ^ 4 ∂P) ≤ 2 ^ 56 * κ ^ 6 * (r + t) ^ 4 := by
  have hh := fourth_moment_of_affine_bound ((hY.sub_const target).norm) hU0
    (fun ω => norm_nonneg (Y ω - target)) hi (by norm_num : (0 : ℝ) ≤ 2) hr
    (fun ω => by simpa only [add_comm] using hdom ω)
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hk0 : 0 ≤ κ := by linarith
  have hk6 : 1 ≤ κ ^ 6 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hκ 6
  have hr4 : r ^ 4 ≤ κ ^ 6 * (r + t) ^ 4 := by
    apply (pow_le_pow_left₀ hr (show r ≤ r + t by linarith) 4).trans
    nlinarith only [mul_le_mul_of_nonneg_right hk6 (show 0 ≤ (r + t) ^ 4 by positivity)]
  nlinarith only [hm, hr4, mul_nonneg (pow_nonneg hk0 6) (show 0 ≤ (r + t) ^ 4 by positivity)]

lemma two_event_moment {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → E} (hX : Measurable X) {p A B : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) {bad₀ bad₁ : Set Ω}
    (hbad₀ : MeasurableSet bad₀) (hbad₁ : MeasurableSet bad₁)
    (hi : Integrable (fun ω => ‖X ω‖ ^ 4) P)
    (hmid : ∀ ω ∉ bad₀, ω ∈ bad₁ → ‖X ω‖ ^ p ≤ B)
    (hgood : ∀ ω ∉ bad₀, ω ∉ bad₁ → ‖X ω‖ ^ p ≤ A) :
    (∫ ω, ‖X ω‖ ^ p ∂P) ≤ A + B * P.real bad₁ +
      (∫ ω, ‖X ω‖ ^ 4 ∂P) ^ (p / 4) * (P.real bad₀) ^ (1 / 2 : ℝ) := by
  classical
  let Z := bad₀.indicator X
  have hZ : Measurable Z := hX.indicator hbad₀
  have he4 : (fun ω => ‖Z ω‖ ^ 4) = bad₀.indicator (fun ω => ‖X ω‖ ^ 4) := by
    funext ω
    by_cases hw : ω ∈ bad₀ <;> simp [Z, hw]
  have hZi : Integrable (fun ω => ‖Z ω‖ ^ 4) P := by rw [he4]; exact hi.indicator hbad₀
  have hZ4 : (∫ ω, ‖Z ω‖ ^ 4 ∂P) ≤ ∫ ω, ‖X ω‖ ^ 4 ∂P := by
    apply integral_mono hZi hi
    intro ω
    by_cases hw : ω ∈ bad₀ <;> simp [Z, hw]
  have htail := good_event_moment hZ hp.le hp2 (le_refl 0) hbad₀ hZi
    (fun ω hw => by simp [Z, hw, Real.zero_rpow hp.ne'])
  have hscale := Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hZ4
    (by positivity : 0 ≤ p / 4)
  have htail' : (∫ ω, ‖Z ω‖ ^ p ∂P) ≤
      (∫ ω, ‖X ω‖ ^ 4 ∂P) ^ (p / 4) * (P.real bad₀) ^ (1 / 2 : ℝ) := by
    simp only [zero_add] at htail
    exact htail.trans (mul_le_mul_of_nonneg_right hscale (by positivity))
  have hXp := (lower_power_from_fourth hX hp.le (by linarith) hi).1
  have hZp := (lower_power_from_fourth hZ hp.le (by linarith) hZi).1
  have hI : Integrable (bad₁.indicator (fun _ : Ω => B)) P := (integrable_const B).indicator hbad₁
  have hbound := integral_mono hXp (((integrable_const A).add hI).add hZp) (fun ω =>
    show ‖X ω‖ ^ p ≤ A + bad₁.indicator (fun _ => B) ω + ‖Z ω‖ ^ p from by
      have hI0 : 0 ≤ bad₁.indicator (fun _ => B) ω := Set.indicator_nonneg (fun _ _ => hB0) ω
      by_cases h₀ : ω ∈ bad₀
      · simp only [Z, Set.indicator_of_mem h₀]
        linarith
      · by_cases h₁ : ω ∈ bad₁
        · have hh := hmid ω h₀ h₁
          simp only [Z, Set.indicator_of_notMem h₀, norm_zero, Real.zero_rpow hp.ne',
            Set.indicator_of_mem h₁, add_zero]
          linarith
        · simpa [Z, h₀, h₁, Real.zero_rpow hp.ne'] using hgood ω h₀ h₁)
  simp only [Pi.add_apply] at hbound
  have hAI : Integrable (fun ω => A + bad₁.indicator (fun _ => B) ω) P :=
    (integrable_const A).add hI
  rw [integral_add hAI hZp,
    integral_add (integrable_const A) hI, integral_const, integral_indicator hbad₁,
    setIntegral_const] at hbound
  simp only [probReal_univ, smul_eq_mul, one_mul] at hbound
  nlinarith only [hbound, htail']

lemma one_level_moment_cancellation {p κ a n r t : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hκ : 2 ≤ κ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hn : 1 ≤ n) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    let S := t + a * r
    let R := r + t
    (193 * S * n ^ (-(p - 1) / p)) ^ p +
      (385 * R) ^ p * ((2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))) +
      ((2 : ℝ) ^ (56 : ℝ) * κ ^ (6 : ℝ) * R ^ (4 : ℝ)) ^ (p / 4) *
        ((2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) *
          n ^ (-2 * (p - 1))) ^ (1 / 2 : ℝ) ≤
      (2 : ℝ) ^ (18 : ℝ) * S ^ p * n ^ (-(p - 1)) := by
  dsimp only
  let S := t + a * r
  let R := r + t
  have hp0 : 0 < p := by linarith
  have hk0 : 0 < κ := by linarith
  have hn0 : 0 < n := by linarith
  have hS : 0 ≤ S := add_nonneg ht (mul_nonneg ha.le hr)
  have hR : 0 ≤ R := add_nonneg hr ht
  have har : a * R ≤ S := by dsimp [S, R]; nlinarith
  have harpow : a ^ p * R ^ p ≤ S ^ p := by
    rw [← Real.mul_rpow ha.le hR]
    exact Real.rpow_le_rpow (mul_nonneg ha.le hR) har hp0.le
  have hnP : 0 ≤ n ^ (-(p - 1)) := Real.rpow_nonneg hn0.le _
  have hSP : 0 ≤ S ^ p := Real.rpow_nonneg hS _
  have hRP : 0 ≤ R ^ p := Real.rpow_nonneg hR _
  have haP : 0 ≤ a ^ p := Real.rpow_nonneg ha.le _
  have hnexp : (n ^ (-(p - 1) / p)) ^ p = n ^ (-(p - 1)) := by
    rw [← Real.rpow_mul hn0.le]
    congr 1
    field_simp
  have hfirst : (193 * S * n ^ (-(p - 1) / p)) ^ p ≤
      37249 * (S ^ p * n ^ (-(p - 1))) := by
    rw [Real.mul_rpow (mul_nonneg (by norm_num) hS) (Real.rpow_nonneg hn0.le _),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 193) hS, hnexp]
    have hc : (193 : ℝ) ^ p ≤ 37249 := by
      calc
        _ ≤ (193 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
        _ = _ := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc (mul_nonneg hSP hnP)]
  have hsecond : (385 * R) ^ p * ((2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))) ≤
      S ^ p * n ^ (-(p - 1)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 385) hR]
    have hc : (385 : ℝ) ^ p * (2 : ℝ) ^ (-32 : ℝ) ≤ 1 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 385) hp2
      norm_num at hh ⊢
      linarith
    calc
      _ = ((385 : ℝ) ^ p * (2 : ℝ) ^ (-32 : ℝ)) *
          ((a ^ p * R ^ p) * n ^ (-(p - 1))) := by ring
      _ ≤ 1 * ((a ^ p * R ^ p) * n ^ (-(p - 1))) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg haP hRP) hnP)
      _ ≤ S ^ p * n ^ (-(p - 1)) := by
        simpa using mul_le_mul_of_nonneg_right harpow hnP
  have hsqrt : ((2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) *
      n ^ (-2 * (p - 1))) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ (-64 : ℝ) * κ ^ (-6 : ℝ) * a ^ p * n ^ (-(p - 1)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hk0.le,
      ← Real.rpow_mul ha.le, ← Real.rpow_mul hn0.le]
    congr 2 <;> ring_nf
  have hA : 1 ≤ (2 : ℝ) ^ (56 : ℝ) * κ ^ (6 : ℝ) := by
    have hk : 1 ≤ κ ^ (6 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    norm_num at hk ⊢
    nlinarith
  have hthird : ((2 : ℝ) ^ (56 : ℝ) * κ ^ (6 : ℝ) * R ^ (4 : ℝ)) ^ (p / 4) *
      ((2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) *
        n ^ (-2 * (p - 1))) ^ (1 / 2 : ℝ) ≤ S ^ p * n ^ (-(p - 1)) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hR _),
      ← Real.rpow_mul hR, show (4 : ℝ) * (p / 4) = p by ring, hsqrt]
    have hc : ((2 : ℝ) ^ (56 : ℝ) * κ ^ (6 : ℝ)) ^ (p / 4) ≤
        (2 : ℝ) ^ (56 : ℝ) * κ ^ (6 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show p / 4 ≤ 1 by linarith)
    calc
      _ ≤ ((2 : ℝ) ^ (56 : ℝ) * κ ^ (6 : ℝ)) * R ^ p *
          ((2 : ℝ) ^ (-64 : ℝ) * κ ^ (-6 : ℝ) * a ^ p * n ^ (-(p - 1))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hRP) (by positivity)
      _ = (1 / 256 : ℝ) * ((a ^ p * R ^ p) * n ^ (-(p - 1))) := by
        have hk : κ ^ (6 : ℝ) * κ ^ (-6 : ℝ) = 1 := by
          rw [← Real.rpow_add hk0]; norm_num
        have htwo : (2 : ℝ) ^ (56 : ℝ) * (2 : ℝ) ^ (-64 : ℝ) = 1 / 256 := by norm_num
        calc
          _ = ((2 : ℝ) ^ (56 : ℝ) * (2 : ℝ) ^ (-64 : ℝ)) *
            (κ ^ (6 : ℝ) * κ ^ (-6 : ℝ)) * ((a ^ p * R ^ p) * n ^ (-(p - 1))) := by ring
          _ = _ := by rw [hk, htwo]; ring
      _ ≤ S ^ p * n ^ (-(p - 1)) := by
        have hh := mul_le_mul_of_nonneg_right harpow hnP
        nlinarith [mul_nonneg (mul_nonneg haP hRP) hnP]
  change _ ≤ (2 : ℝ) ^ (18 : ℝ) * S ^ p * n ^ (-(p - 1))
  dsimp [S, R] at hfirst hsecond hthird hSP hnP ⊢
  conv_rhs => rw [show (2 : ℝ) ^ (18 : ℝ) = 262144 by norm_num]
  have hsum := add_le_add (add_le_add hfirst hsecond) hthird
  refine hsum.trans ?_
  nlinarith [mul_nonneg hSP hnP]


section BatchAffine
lemma affine_batch_coefficient {p B : ℝ} (hp : 1 < p) (hB : 0 < B) :
    4 * B ^ (1 - p) ≤ (4 * B ^ (-(1 / (p / (p - 1))))) ^ p := by
  have hpow : (4 : ℝ) ≤ (4 : ℝ) ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hp.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), ← Real.rpow_mul hB.le]
  have he : -(1 / (p / (p - 1))) * p = 1 - p := by
    have hp0 : p ≠ 0 := by linarith
    have hp1 : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]
lemma batch_affine_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {g : E → Ω → E} {field : E → E} {p s a : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (B : ℕ) (hB : 0 < B) (x : E) :
    let Q := Measure.pi fun _ : Fin B => P
    let X := fun ξ : Fin B → Ω => (B : ℝ)⁻¹ • ∑ i, g x (ξ i)
    let c := 4 * (B : ℝ) ^ (-(1 / (p / (p - 1))))
    Integrable X Q ∧ (∫ w, X w ∂Q) = field x ∧
      Integrable (fun w => ‖X w - field x‖ ^ p) Q ∧
      (∫ w, ‖X w - field x‖ ^ p ∂Q) ≤ (c * s) ^ p + (c * a) ^ p * ‖field x‖ ^ p := by
  have hgm : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
  have hb := HilbertSmallMoments.iid_centered_mean_power_bound hgm hp.le hp2
    (hi x) (field x) (hpi x) (hmean x) B hB
  have hm' := OracleTemplate.LightTail.finite_mean_integral (hi x) B hB
  have he : (∫ ξ : Fin B → Ω, (B : ℝ)⁻¹ • ∑ i, g x (ξ i) ∂Measure.pi fun _ => P) = field x := by
    simpa only [one_div, hmean x] using hm'.2
  refine ⟨?_, he, hb.1, hb.2.trans ?_⟩
  · simpa only [one_div] using hm'.1
  · have hB0 : 0 < (B : ℝ) := by exact_mod_cast hB
    let c := 4 * (B : ℝ) ^ (-(1 / (p / (p - 1))))
    have hc : 0 ≤ c := by positivity
    calc
      _ ≤ c ^ p * (s ^ p + a ^ p * ‖field x‖ ^ p) :=
        mul_le_mul (affine_batch_coefficient hp hB0) (hm x)
          (integral_nonneg (fun _ => by positivity)) (by positivity)
      _ = (c * s) ^ p + (c * a) ^ p * ‖field x‖ ^ p := by
        rw [Real.mul_rpow hc hs, Real.mul_rpow hc ha]
        ring

end BatchAffine

end LongTails.Proofs.StochasticEnvelopeSampling
