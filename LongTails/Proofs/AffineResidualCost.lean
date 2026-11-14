import LongTails.Proofs.AffineResidualMultilevel
import LongTails.Proofs.AffineSoftmaxMultilevelCost

namespace LongTails.Proofs.AffineResidualCost

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot)

lemma sqrt_dyadic_le {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (j : ℕ) :
    Real.sqrt (A / (δ / 2 ^ j)) ≤ (2 : ℝ) ^ j * Real.sqrt (A / δ) := by
  have ht : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have he : A / (δ / 2 ^ j) = (A / δ) * 2 ^ j := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  rw [he, Real.sqrt_mul (div_nonneg hA hδ.le), mul_comm]
  have hs : Real.sqrt ((2 : ℝ) ^ j) ≤ (2 : ℝ) ^ j :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  exact mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)

lemma localSteps_level_le (m : ℕ) [NeZero m] {τ μ L r δ : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hδ : 0 < δ) (j : ℕ) :
    localSteps m τ μ L r (δ / 2 ^ j) ≤ 2 ^ j * localSteps m τ μ L r δ := by
  let A := 2 * μ * r ^ 2 + τ * Real.log m
  let V := (L * r) ^ 2 / μ + (m : ℝ) * (L * r ^ 2 / 2) ^ 2 / τ
  let β := localOffset m τ L r
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hβ : 0 ≤ β := le_trans (by norm_num) (AffineResidualLocal.localOffset_bounds m hτ hL).1
  have ht : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hs := mul_le_mul_of_nonneg_left (sqrt_dyadic_le hA hδ j)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hβ)
  have hn := Nat.le_ceil (4 * β * Real.sqrt (A / δ) + 64 * V / δ + 1)
  change ⌈4 * β * Real.sqrt (A / (δ / 2 ^ j)) + 64 * V / (δ / 2 ^ j) + 1⌉₊ ≤
    2 ^ j * ⌈4 * β * Real.sqrt (A / δ) + 64 * V / δ + 1⌉₊
  apply Nat.ceil_le.mpr
  push_cast
  apply le_trans _ (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2 : ℝ) ^ j))
  have he : 64 * V / (δ / 2 ^ j) = 2 ^ j * (64 * V / δ) := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  rw [he]
  nlinarith

lemma localSteps_bound (m : ℕ) {τ μ L r δ : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hδ : 0 < δ) :
    (localSteps m τ μ L r δ : ℝ) ≤
      4 * (2 + 8 * m * L * r ^ 2 / τ) * Real.sqrt ((2 * μ * r ^ 2 + τ * Real.log m) / δ) +
        64 * ((L * r) ^ 2 / μ + m * (L * r ^ 2 / 2) ^ 2 / τ) / δ + 2 := by
  have hb := (AffineResidualLocal.localOffset_bounds m hτ hL (r := r)).1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8 * m * L * r ^ 2 / τ by positivity)
  have hβ : localOffset m τ L r ≤ 2 + 8 * m * L * r ^ 2 / τ := by
    dsimp only [localOffset]
    linarith
  have hn := Nat.ceil_lt_add_one (show 0 ≤
      4 * localOffset m τ L r * Real.sqrt ((2 * μ * r ^ 2 + τ * Real.log m) / δ) +
        64 * ((L * r) ^ 2 / μ + m * (L * r ^ 2 / 2) ^ 2 / τ) / δ + 1 by positivity)
  have hh := mul_le_mul_of_nonneg_right hβ
    (Real.sqrt_nonneg ((2 * μ * r ^ 2 + τ * Real.log m) / δ))
  dsimp only [localSteps]
  nlinarith

lemma localSteps_scaled_mono (m : ℕ) [NeZero m] {τ μ floor L r q q₀ : ℝ}
    (hτ : 0 < τ) (hf : 0 < floor) (hμ : floor ≤ μ) (hL : 0 ≤ L)
    (hq : 0 < q₀) (hqq : q₀ ≤ q) :
    localSteps m τ μ L r (μ * q) ≤ localSteps m τ floor L r (floor * q₀) := by
  have hμpos := hf.trans_le hμ
  have hqpos := hq.trans_le hqq
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  have hA (v c : ℝ) (hv : 0 < v) (hc : 0 < c) :
      (2 * v * r ^ 2 + τ * Real.log m) / (v * c) =
        2 * r ^ 2 / c + τ * Real.log m / (v * c) := by field_simp
  have hV (v c : ℝ) (hv : 0 < v) (hc : 0 < c) :
      ((L * r) ^ 2 / v + m * (L * r ^ 2 / 2) ^ 2 / τ) / (v * c) =
        (L * r) ^ 2 / (v ^ 2 * c) + m * (L * r ^ 2 / 2) ^ 2 / (τ * v * c) := by field_simp
  have ha : (2 * μ * r ^ 2 + τ * Real.log m) / (μ * q) ≤
      (2 * floor * r ^ 2 + τ * Real.log m) / (floor * q₀) := by
    rw [hA μ q hμpos hqpos, hA floor q₀ hf hq]
    gcongr
  have hv : ((L * r) ^ 2 / μ + m * (L * r ^ 2 / 2) ^ 2 / τ) / (μ * q) ≤
      ((L * r) ^ 2 / floor + m * (L * r ^ 2 / 2) ^ 2 / τ) / (floor * q₀) := by
    rw [hV μ q hμpos hqpos, hV floor q₀ hf hq]
    gcongr
  have hβ : 0 ≤ localOffset m τ L r :=
    le_trans (by norm_num) (AffineResidualLocal.localOffset_bounds m hτ hL).1
  unfold localSteps
  apply Nat.ceil_mono
  have hs := Real.sqrt_le_sqrt ha
  simp only [mul_div_assoc] at hv ⊢
  nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * localOffset m τ L r by positivity)]

lemma localSteps_relative_bound (m : ℕ) [NeZero m] {τ μ L r k : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hr : 0 < r) (hk : 1 ≤ k) :
    (localSteps m τ μ L r (μ * r ^ 2 / k) : ℝ) ≤
      64 * k * ((1 + m * L * r ^ 2 / τ) *
        (1 + Real.sqrt (τ * Real.log m / (μ * r ^ 2))) +
        (L / μ) ^ 2 + m * L ^ 2 * r ^ 2 / (μ * τ) + 1) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  let a := (m : ℝ) * L * r ^ 2 / τ
  let q := τ * Real.log m / (μ * r ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsq := Real.sq_sqrt hq
  have hs2 : Real.sqrt (2 + q) ≤ 2 * (1 + Real.sqrt q) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sqrt_nonneg q]
  have hsk : Real.sqrt k ≤ k := (Real.sqrt_le_iff).2 ⟨hkpos.le, by nlinarith⟩
  have hratio : (2 * μ * r ^ 2 + τ * Real.log m) / (μ * r ^ 2 / k) = k * (2 + q) := by
    dsimp [q]
    field_simp
  have hs : Real.sqrt ((2 * μ * r ^ 2 + τ * Real.log m) / (μ * r ^ 2 / k)) ≤
      2 * k * (1 + Real.sqrt q) := by
    rw [hratio, Real.sqrt_mul hkpos.le]
    calc
      _ ≤ k * (2 * (1 + Real.sqrt q)) := mul_le_mul hsk hs2 (Real.sqrt_nonneg _) hkpos.le
      _ = _ := by ring
  have hv : ((L * r) ^ 2 / μ + m * (L * r ^ 2 / 2) ^ 2 / τ) / (μ * r ^ 2 / k) =
      k * ((L / μ) ^ 2 + m * L ^ 2 * r ^ 2 / (4 * μ * τ)) := by field_simp; ring
  have hn := localSteps_bound m (r := r) hτ hμ hL (show 0 < μ * r ^ 2 / k by positivity)
  have hinit : 4 * (2 + 8 * m * L * r ^ 2 / τ) *
      Real.sqrt ((2 * μ * r ^ 2 + τ * Real.log m) / (μ * r ^ 2 / k)) ≤
        64 * k * ((1 + a) * (1 + Real.sqrt q)) := by
    have hc : 4 * (2 + 8 * m * L * r ^ 2 / τ) ≤ 32 * (1 + a) := by dsimp [a]; ring_nf; linarith
    calc
      _ ≤ (32 * (1 + a)) * (2 * k * (1 + Real.sqrt q)) :=
        mul_le_mul hc hs (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hnoise : m * L ^ 2 * r ^ 2 / (4 * μ * τ) ≤ m * L ^ 2 * r ^ 2 / (μ * τ) := by
    gcongr
    nlinarith [mul_pos hμ hτ]
  have hv' := mul_le_mul_of_nonneg_left hnoise (show 0 ≤ 64 * k by positivity)
  rw [mul_div_assoc 64 _ (μ * r ^ 2 / k), hv] at hn
  change _ ≤ 64 * k * ((1 + a) * (1 + Real.sqrt q) + (L / μ) ^ 2 +
    m * L ^ 2 * r ^ 2 / (μ * τ) + 1)
  nlinarith only [hn, hinit, hv', hk]

lemma dyadic_cost_sum_le (c : ℕ → ℝ) {K : ℝ} (hc : ∀ j, c j ≤ (2 : ℝ) ^ j * K) (J : ℕ) :
    c 0 + ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1) * (c (j + 1) + c j) ≤
      (1 + 3 * (J : ℝ) / 2) * K := by
  have hterm (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1) * (c (j + 1) + c j) ≤ 3 * K / 2 := by
    apply (mul_le_mul_of_nonneg_left (add_le_add (hc (j + 1)) (hc j)) (by positivity)).trans_eq
    have hp : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((1 / 2 : ℝ) ^ j * 2 ^ j) * (3 * K / 2) := by rw [pow_succ, pow_succ]; ring
      _ = _ := by rw [hp, one_mul]
  have hs := Finset.sum_le_sum (s := Finset.range J) (fun j _ => hterm j)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hzero : c 0 ≤ K := by simpa using hc 0
  nlinarith

lemma multilevelPlan_cost_integral {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (s : Snapshot ι E) (τ μ L r δ : ℝ) (J : ℕ) (reply : ι × E → ℝ × E) :
    let c := fun j => (2 : ℝ) * localSteps (Fintype.card ι) τ μ L r (δ / 2 ^ j)
    Integrable (fun seed => (Program.cost reply (multilevelPlan C s τ μ L r δ J seed) : ℝ))
      (multilevelLaw : Measure MultilevelSeed) ∧
    (∫ seed, (Program.cost reply (multilevelPlan C s τ μ L r δ J seed) : ℝ)
      ∂(multilevelLaw : Measure MultilevelSeed)) =
      c 0 + ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1) * (c (j + 1) + c j) := by
  let c := fun j => (2 : ℝ) * localSteps (Fintype.card ι) τ μ L r (δ / 2 ^ j)
  have hh := AffineSoftmaxMultilevelCost.independent_level_cost localLaw
    (fun j _ => c j) (fun _ => integrable_const _) J
  simpa [AffineResidualMultilevel.multilevelPlan_cost, multilevelLaw, c] using hh

lemma multilevelPlan_cost_bound {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (s : Snapshot ι E) {τ μ L r δ : ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (J : ℕ) (reply : ι × E → ℝ × E) :
    (∫ seed, (Program.cost reply (multilevelPlan C s τ μ L r δ J seed) : ℝ)
      ∂(multilevelLaw : Measure MultilevelSeed)) ≤
      (2 + 3 * (J : ℝ)) * localSteps (Fintype.card ι) τ μ L r δ := by
  rw [(multilevelPlan_cost_integral C s τ μ L r δ J reply).2]
  have hc (j : ℕ) : (2 : ℝ) * localSteps (Fintype.card ι) τ μ L r (δ / 2 ^ j) ≤
      2 ^ j * (2 * localSteps (Fintype.card ι) τ μ L r δ) := by
    have hh : (localSteps (Fintype.card ι) τ μ L r (δ / 2 ^ j) : ℝ) ≤
        (2 : ℝ) ^ j * localSteps (Fintype.card ι) τ μ L r δ := by
      exact_mod_cast localSteps_level_le (Fintype.card ι) hτ hμ hL hδ j
    nlinarith
  have hh := dyadic_cost_sum_le _ hc J
  convert hh using 1
  ring

lemma cachedProxGradientPlan_cost_bound {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (s : Snapshot ι E) {τ μ L r σ : ℝ} (β : ℝ)
    (hτ : 0 < τ) (hμ : 0 < μ) (hL : 0 ≤ L) (hσ : 0 < σ) (reply : ι × E → ℝ × E) :
    let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
    let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
    Integrable (fun seed => (Program.cost reply (cachedProxGradientPlan C s τ μ L r σ β seed) : ℝ))
      (multilevelLaw : Measure MultilevelSeed) ∧
    (∫ seed, (Program.cost reply (cachedProxGradientPlan C s τ μ L r σ β seed) : ℝ)
      ∂(multilevelLaw : Measure MultilevelSeed)) ≤
      (2 + 3 * (J : ℝ)) * localSteps (Fintype.card ι) τ μ L r δ := by
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hi := (multilevelPlan_cost_integral C s τ μ L r δ J reply).1
  have hb := multilevelPlan_cost_bound C s (r := r) hτ hμ hL hδ J reply
  simpa only [cachedProxGradientPlan, Program.cost_map, J, δ] using And.intro hi hb

end LongTails.Proofs.AffineResidualCost
