import LongTails.Proofs.StochasticCompositeGeneralizedGrowth

namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

lemma clipRadius_nonneg (p : Public) (hσ : 0 ≤ p.σ) (k : ℕ) : 0 ≤ clipRadius p k :=
  le_trans (by positivity) (le_max_left _ _)

lemma varianceBound_nonneg (p : Public) (hσ : 0 ≤ p.σ) (k : ℕ) : 0 ≤ varianceBound p k := by
  have hb := clipRadius_nonneg p hσ k
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hσ _)

lemma clipRadius_mono (p : Public) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hα : 1 < p.α)
    (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) {j k : ℕ} (hjk : j ≤ k) :
    clipRadius p j ≤ clipRadius p k := by
  have hj := confidence_lower p hδ hδ1 j
  have hσa := Real.rpow_nonneg hσ p.α
  unfold clipRadius
  apply max_le_max le_rfl
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  gcongr
  exact confidence_mono p hδ hjk

lemma varianceBound_mono (p : Public) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hα : 1 < p.α)
    (hα2 : p.α ≤ 2) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    {j k : ℕ} (hjk : j ≤ k) : varianceBound p j ≤ varianceBound p k := by
  have hj := clipRadius_nonneg p hσ j
  have hm := clipRadius_mono p hR hσ hα hε hδ hδ1 hjk
  unfold varianceBound
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hσ _)
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

lemma pilotSize_upper (p : Public) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    {j k : ℕ} (hjk : j ≤ k) : (pilotSize p j : ℝ) ≤ 1 + 16 * confidence p k := by
  have hj := confidence_lower p hδ hδ1 j
  have hk := confidence_lower p hδ hδ1 k
  have hm := confidence_mono p hδ hjk
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 16 * confidence p j)).le
  simp only [pilotSize, Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

lemma batchSize_upper (p : Public) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hα : 1 < p.α)
    (hα2 : p.α ≤ 2) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    {j k : ℕ} (hjk : j ≤ k) {a : ℝ} (ha : 0 ≤ a) :
    (batchSize p j a : ℝ) ≤ 1 + 1099511627776 *
      (varianceBound p k * confidence p k ^ 2 / p.ε + clipRadius p k * confidence p k ^ 2 / p.R) * a := by
  have hj := confidence_lower p hδ hδ1 j
  have hcm := confidence_mono p hδ hjk
  have hBj := clipRadius_nonneg p hσ j
  have hVj := varianceBound_nonneg p hσ j
  have hBm := clipRadius_mono p hR hσ hα hε hδ hδ1 hjk
  have hBk := clipRadius_nonneg p hσ k
  have hVk := varianceBound_nonneg p hσ k
  have hVm := varianceBound_mono p hR hσ hα hα2 hε hδ hδ1 hjk
  have hx : 0 ≤ 1099511627776 * (varianceBound p j * a * confidence p j ^ 2 / p.ε +
      clipRadius p j * a * confidence p j ^ 2 / p.R) := by positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  have hb : (batchSize p j a : ℝ) ≤ 1099511627776 *
      (varianceBound p j * a * confidence p j ^ 2 / p.ε + clipRadius p j * a * confidence p j ^ 2 / p.R) + 1 := by
    simp only [batchSize, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) hc
  have ht1 : varianceBound p j * a * confidence p j ^ 2 / p.ε ≤
      varianceBound p k * a * confidence p k ^ 2 / p.ε := by gcongr
  have ht2 : clipRadius p j * a * confidence p j ^ 2 / p.R ≤
      clipRadius p k * a * confidence p k ^ 2 / p.R := by gcongr
  calc
    _ ≤ _ := hb
    _ ≤ 1099511627776 * (varianceBound p k * a * confidence p k ^ 2 / p.ε +
        clipRadius p k * a * confidence p k ^ 2 / p.R) + 1 := by linarith
    _ = _ := by ring

lemma phaseCost_upper (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (s : State p.E) (hs : WellFormed s) (k : ℕ) (hk : s.iteration ≤ k) :
    (phaseCost p s : ℝ) ≤ 2 + 16 * confidence p k + 1099511627776 *
      (varianceBound p k * confidence p k ^ 2 / p.ε + clipRadius p k * confidence p k ^ 2 / p.R) * phaseWeight p s := by
  have hl := confidence_lower p hδ hδ1 k
  by_cases hp : s.stage = 0 ∨ s.stage = 1
  · have hn : s.stage ≠ 2 := by omega
    simp only [phaseCost, hp, ite_true, phaseWeight, hn, ite_false, mul_zero, add_zero]
    have hh := pilotSize_upper p hδ hδ1 hk
    linarith
  · by_cases he : s.stage = 2
    · norm_num only [phaseCost, phaseWeight, he, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, or_false, false_or, ite_false, ite_true]
      have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inl he))
      have hh := batchSize_upper p hR hσ hα hα2 hε hδ hδ1 hk ha.le
      linarith
    · simp only [phaseCost, hp, ite_false, he, phaseWeight, mul_zero, add_zero, Nat.cast_one]
      linarith


lemma blockCalls_upper (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (ξ : ℕ → p.Ω) (n : ℕ) :
    (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ n : ℝ) ≤
      (n : ℝ) * (2 + 16 * confidence p n) + 8 * 1099511627776 *
        (varianceBound p n * p.R ^ 2 / p.ε ^ 2 + clipRadius p n * p.R / p.ε) * confidence p n ^ 2 := by
  let C := 1099511627776 * (varianceBound p n * confidence p n ^ 2 / p.ε +
    clipRadius p n * confidence p n ^ 2 / p.R)
  have hB := clipRadius_nonneg p hσ n
  have hV := varianceBound_nonneg p hσ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (i : ℕ) (hi : i ∈ Finset.range n) :
      (phaseCost p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ i).1 : ℝ) ≤
        2 + 16 * confidence p n + C * phaseWeight p
          (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ i).1 := by
    apply phaseCost_upper p hL1 hR hσ hα hα2 hε hδ hδ1 _
      (blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ (initialState p) (initialState_wellFormed p hR hΔ) i) n
    exact (blockTrace_protocol p I g hL0 hL1 hR hσ hΔ ξ i).iteration_le.trans
      (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hw := accumulated_phaseWeight_bound p I g hL0 hL1 hR hσ hΔ hε ξ n
  rw [StochasticGeneralized.accumulated_eq_sum] at hw
  rw [StochasticGeneralized.blockCalls, Nat.cast_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range n, (2 + 16 * confidence p n + C * phaseWeight p
        (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ i).1) :=
      Finset.sum_le_sum hp
    _ = (n : ℝ) * (2 + 16 * confidence p n) + C *
        ∑ i ∈ Finset.range n, phaseWeight p
          (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ i).1 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    _ ≤ (n : ℝ) * (2 + 16 * confidence p n) + C * (8 * p.R ^ 2 / p.ε) := by
      linarith [mul_le_mul_of_nonneg_left hw hC]
    _ = _ := by
      dsimp only [C]
      field_simp


lemma normalized_variance_upper {α q v ell C w : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (hq : q = 1 / (α - 1)) (hv : 0 ≤ v) (hl : 1 ≤ ell) (hC : 1 ≤ C)
    (hw0 : 0 ≤ w) (hw : w ≤ C * (max 1 v) ^ (α * q) * ell ^ q) :
    (2 * w) ^ (2 - α) * v ^ α ≤ 2 * C * (max 1 v) ^ (α * q) * ell ^ q := by
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hβ : 0 ≤ 2 - α := by linarith
  have hβ1 : 2 - α ≤ 1 := by linarith
  have hm : (1 : ℝ) ≤ max 1 v := le_max_left _ _
  have hm0 : 0 ≤ max 1 v := by linarith
  have hC0 : 0 ≤ 2 * C := by linarith
  have hr : α * q * (2 - α) + α = α * q := by
    rw [hq]
    field_simp [ne_of_gt (sub_pos.mpr hα)]
    ring
  have hqe : q * (2 - α) ≤ q := by nlinarith
  calc
    _ ≤ (2 * (C * (max 1 v) ^ (α * q) * ell ^ q)) ^ (2 - α) * (max 1 v) ^ α := by
      gcongr
      exact le_max_right _ _
    _ = (2 * C) ^ (2 - α) * (max 1 v) ^ (α * q * (2 - α) + α) * ell ^ (q * (2 - α)) := by
      rw [show 2 * (C * (max 1 v) ^ (α * q) * ell ^ q) =
        (2 * C * (max 1 v) ^ (α * q)) * ell ^ q by ring]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hC0 (by positivity), ← Real.rpow_mul hm0,
        ← Real.rpow_mul (by linarith : 0 ≤ ell), Real.rpow_add (by linarith : 0 < max 1 v)]
      ring
    _ ≤ (2 * C) ^ (1 : ℝ) * (max 1 v) ^ (α * q) * ell ^ q := by
      rw [hr]
      have hc := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 2 * C by linarith) hβ1
      have he := Real.rpow_le_rpow_of_exponent_le hl hqe
      exact mul_le_mul (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hm0 _)) he
        (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = _ := by rw [Real.rpow_one]

lemma clipping_scale_identity {α σ b ell c : ℝ} (hα : 1 < α) (hσ : 0 ≤ σ)
    (hb : 0 < b) (hl : 0 ≤ ell) (hc : 0 ≤ c) :
    (c * σ ^ α * b * ell) ^ (1 / (α - 1)) * b =
      c ^ (1 / (α - 1)) * (σ * b) ^ (α / (α - 1)) * ell ^ (1 / (α - 1)) := by
  have he : α / (α - 1) = 1 / (α - 1) + 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hα)]
    ring
  rw [Real.mul_rpow (by positivity) hl, Real.mul_rpow (by positivity) hb.le,
    Real.mul_rpow hc (Real.rpow_nonneg hσ _), ← Real.rpow_mul hσ,
    Real.mul_rpow hσ hb.le]
  rw [div_eq_mul_inv α (α - 1), one_div, ← div_eq_mul_inv]
  rw [he, Real.rpow_add_one hb.ne']
  ring

lemma variance_scale_identity {α σ b B : ℝ} (hσ : 0 ≤ σ) (hb : 0 < b) (hB : 0 ≤ B) :
    ((2 * B) ^ (2 - α) * σ ^ α) * b ^ 2 =
      (2 * (B * b)) ^ (2 - α) * (σ * b) ^ α := by
  rw [show 2 * (B * b) = (2 * B) * b by ring,
    Real.mul_rpow (by positivity) hb.le, Real.mul_rpow hσ hb.le]
  have he : b ^ (2 - α) * b ^ α = b ^ (2 : ℕ) := by
    rw [← Real.rpow_add hb, sub_add_cancel, Real.rpow_two]
  calc
    _ = ((2 * B) ^ (2 - α) * σ ^ α) * (b ^ (2 - α) * b ^ α) := by rw [he]
    _ = _ := by ring

lemma normalized_clipping_upper {α v ell : ℝ} (hα : 1 < α) (hv : 0 ≤ v) (hl : 1 ≤ ell) :
    max (384 * v) (2 * (1048576 : ℝ) ^ (1 / (α - 1)) * v ^ (α / (α - 1)) * ell ^ (1 / (α - 1))) ≤
      (1024 * (1048576 : ℝ) ^ (1 / (α - 1))) * (max 1 v) ^ (α / (α - 1)) * ell ^ (1 / (α - 1)) := by
  have hq : 0 ≤ 1 / (α - 1) := by positivity
  have hr : 1 ≤ α / (α - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hα)).mpr
    linarith
  have hc : 1 ≤ (1048576 : ℝ) ^ (1 / (α - 1)) := Real.one_le_rpow (by norm_num) hq
  have he : 1 ≤ ell ^ (1 / (α - 1)) := Real.one_le_rpow hl hq
  have hm : 1 ≤ max (1 : ℝ) v := le_max_left _ _
  have hmr : v ≤ (max 1 v) ^ (α / (α - 1)) := by
    calc
      v ≤ max 1 v := le_max_right _ _
      _ = (max 1 v) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm hr
  apply max_le
  · have h1 : 384 * v ≤ 1024 * (1048576 : ℝ) ^ (1 / (α - 1)) * (max 1 v) ^ (α / (α - 1)) := by
      exact mul_le_mul (by nlinarith : (384 : ℝ) ≤ 1024 * (1048576 : ℝ) ^ (1 / (α - 1))) hmr hv (by positivity)
    calc
      _ ≤ _ := h1
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  · have hvp := Real.rpow_le_rpow hv (le_max_right (1 : ℝ) v) (by linarith : 0 ≤ α / (α - 1))
    gcongr
    norm_num

lemma clipRadius_normalized_upper (p : Public) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (k : ℕ) :
    clipRadius p k * p.R / p.ε ≤ (1024 * (1048576 : ℝ) ^ (1 / (p.α - 1))) *
      (max 1 (p.σ * p.R / p.ε)) ^ (p.α / (p.α - 1)) * (confidence p k) ^ (1 / (p.α - 1)) := by
  have hl := confidence_lower p hδ hδ1 k
  have hb : 0 < p.R / p.ε := div_pos hR hε
  have he := clipping_scale_identity hα hσ hb (by linarith : 0 ≤ confidence p k)
    (by norm_num : (0 : ℝ) ≤ 1048576)
  have hr : clipRadius p k * p.R / p.ε =
      max (384 * (p.σ * p.R / p.ε))
        (2 * (1048576 : ℝ) ^ (1 / (p.α - 1)) * (p.σ * p.R / p.ε) ^ (p.α / (p.α - 1)) *
          confidence p k ^ (1 / (p.α - 1))) := by
    rw [clipRadius, mul_div_assoc, max_mul_of_nonneg _ _ hb.le]
    congr 1
    · ring
    · have hx : 1048576 * p.σ ^ p.α * p.R * confidence p k / p.ε =
        1048576 * p.σ ^ p.α * (p.R / p.ε) * confidence p k := by ring
      rw [hx]
      calc
        _ = 2 * ((1048576 * p.σ ^ p.α * (p.R / p.ε) * confidence p k) ^ (1 / (p.α - 1)) * (p.R / p.ε)) := by ring
        _ = _ := by rw [he]; simp only [mul_div_assoc]; ring
  rw [hr]
  exact normalized_clipping_upper hα (by positivity) hl

lemma varianceBound_normalized_upper (p : Public) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (k : ℕ) :
    varianceBound p k * p.R ^ 2 / p.ε ^ 2 ≤ 2 * (1024 * (1048576 : ℝ) ^ (1 / (p.α - 1))) *
      (max 1 (p.σ * p.R / p.ε)) ^ (p.α / (p.α - 1)) * (confidence p k) ^ (1 / (p.α - 1)) := by
  have hl := confidence_lower p hδ hδ1 k
  have hB := clipRadius_nonneg p hσ k
  have hc : 1 ≤ 1024 * (1048576 : ℝ) ^ (1 / (p.α - 1)) := by
    have hh := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 1048576)
      (by positivity : 0 ≤ 1 / (p.α - 1))
    linarith
  have hw := clipRadius_normalized_upper p hR hσ hα hε hδ hδ1 k
  have hh := normalized_variance_upper hα hα2 rfl (show 0 ≤ p.σ * p.R / p.ε by positivity) hl hc
    (show 0 ≤ clipRadius p k * p.R / p.ε by positivity)
    (by simpa only [div_eq_mul_inv, one_div, one_mul, mul_assoc] using hw)
  have he := variance_scale_identity (α := p.α) hσ (div_pos hR hε) hB
  calc
    _ = varianceBound p k * (p.R / p.ε) ^ 2 := by ring
    _ = (2 * (clipRadius p k * p.R / p.ε)) ^ (2 - p.α) * (p.σ * p.R / p.ε) ^ p.α := by
      simpa only [varianceBound, mul_div_assoc] using he
    _ ≤ _ := by simpa only [div_eq_mul_inv, one_div, one_mul, mul_assoc] using hh


lemma enlarged_transient_log {t d : ℝ} (ht : 0 ≤ t) (_hd : 0 ≤ d) :
    Real.log (2 + (3 + 192 * t) * Real.sqrt d) ≤
      9 * Real.log (2 + (1 + t) * Real.sqrt d) := by
  let u := 2 + (1 + t) * Real.sqrt d
  have hu : 2 ≤ u := by
    have hh : 0 ≤ (1 + t) * Real.sqrt d := by positivity
    dsimp [u]
    linarith
  have hlarge : 0 < 2 + (3 + 192 * t) * Real.sqrt d := by positivity
  have harg : 2 + (3 + 192 * t) * Real.sqrt d ≤ 256 * u := by
    dsimp [u]
    nlinarith [Real.sqrt_nonneg d, mul_nonneg ht (Real.sqrt_nonneg d)]
  have hlog := Real.log_le_log hlarge harg
  rw [Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (by linarith : u ≠ 0)] at hlog
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hu
  have hc : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hc] at hlog
  dsimp [u] at hlog h2
  linarith

lemma horizon_upper_core {t z d v r : ℝ} (ht : 0 ≤ t) (_hz : 0 ≤ z)
    (hd : 0 ≤ d) (hv : 0 ≤ v) :
    (⌈20 * Real.sqrt z + (6 + 256 * t) *
      Real.log (2 + (3 + 192 * t) * Real.sqrt d)⌉₊ : ℝ) ≤
      4096 * (1 + Real.sqrt z + (1 + t) * Real.log (2 + (1 + t) * Real.sqrt d) + v ^ r) := by
  have hb := enlarged_transient_log ht hd
  have hl : 0 ≤ Real.log (2 + (1 + t) * Real.sqrt d) := Real.log_nonneg (by nlinarith [Real.sqrt_nonneg d, mul_nonneg ht (Real.sqrt_nonneg d)])
  have hlarge : 0 ≤ Real.log (2 + (3 + 192 * t) * Real.sqrt d) := Real.log_nonneg (by nlinarith [Real.sqrt_nonneg d, mul_nonneg ht (Real.sqrt_nonneg d)])
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 20 * Real.sqrt z + (6 + 256 * t) *
    Real.log (2 + (3 + 192 * t) * Real.sqrt d) by positivity)).le
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 6 + 256 * t by positivity)
  have hvp := Real.rpow_nonneg hv r
  nlinarith [Real.sqrt_nonneg z, mul_nonneg ht hl]

lemma horizon_upper_scale {t z d H : ℝ} (ht : 0 ≤ t) (_hz : 0 ≤ z) (_hd : 0 ≤ d)
    (hH : 2 ≤ H) (htH : 1 + t ≤ H) (hzH : z ≤ H) (hdH : d ≤ H) :
    (⌈20 * Real.sqrt z + (6 + 256 * t) *
      Real.log (2 + (3 + 192 * t) * Real.sqrt d)⌉₊ : ℝ) ≤ 4096 * H ^ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hsd : Real.sqrt d ≤ H := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hH0
    · nlinarith
  have hsz : Real.sqrt z ≤ H := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hH0
    · nlinarith
  have hl0 : 0 ≤ Real.log (2 + (3 + 192 * t) * Real.sqrt d) :=
    Real.log_nonneg (by nlinarith [Real.sqrt_nonneg d, mul_nonneg ht (Real.sqrt_nonneg d)])
  have harg : 2 + (3 + 192 * t) * Real.sqrt d ≤ 256 * H ^ 2 := by
    have hh := mul_le_mul (show 3 + 192 * t ≤ 195 * H by linarith) hsd
      (Real.sqrt_nonneg d) (by positivity : 0 ≤ 195 * H)
    nlinarith
  have hl := Real.log_le_log (show 0 < 2 + (3 + 192 * t) * Real.sqrt d by positivity) harg
  rw [Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (pow_ne_zero 2 (by linarith : H ≠ 0)), Real.log_pow] at hl
  have hc : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + (3 + 192 * t) * Real.sqrt d) ≤ 10 * Real.log H := by
    rw [hc] at hl
    norm_num at hl
    linarith
  have hh := mul_le_mul (show 6 + 256 * t ≤ 256 * H by linarith) hlog hl0 (by positivity : 0 ≤ 256 * H)
  have hu := Real.log_le_sub_one_of_pos (show 0 < H by linarith)
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 20 * Real.sqrt z + (6 + 256 * t) *
    Real.log (2 + (3 + 192 * t) * Real.sqrt d) by positivity)).le
  have hmul := mul_le_mul_of_nonneg_left hu hH0
  nlinarith only [hc, hsz, hh, hmul, hH, sq_nonneg (H - 2)]

lemma horizon_confidence_upper {K : ℕ} {H δ : ℝ} (hδ : 0 < δ) (hH : 2 ≤ H)
    (hlH : 1 ≤ Real.log H) (hδH : 1 / δ ≤ H) (hK : (K : ℝ) ≤ 4096 * H ^ 2) :
    Real.log (64 * Real.exp 1 * (((4 * K : ℕ) : ℝ) + 1) ^ 2 / δ) ≤ 64 * Real.log H := by
  have hH0 : 0 < H := by linarith
  have hki : (4 : ℝ) * K + 1 ≤ 32768 * H ^ 2 := by nlinarith [sq_nonneg (H - 2)]
  have hk0 : 0 ≤ (4 : ℝ) * K + 1 := by positivity
  have harg : 64 * Real.exp 1 * ((4 : ℝ) * K + 1) ^ 2 / δ ≤
      ((2 : ℝ) ^ (36 : ℕ) * Real.exp 1) * H ^ 5 := by
    calc
      _ = (64 * Real.exp 1 * ((4 : ℝ) * K + 1) ^ 2) * (1 / δ) := by ring
      _ ≤ (64 * Real.exp 1 * (32768 * H ^ 2) ^ 2) * H := by
        gcongr
      _ = _ := by ring
  have hh := Real.log_le_log (show 0 < 64 * Real.exp 1 * ((4 : ℝ) * K + 1) ^ 2 / δ by positivity) harg
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ (36 : ℕ) * Real.exp 1 ≠ 0)
    (pow_ne_zero 5 hH0.ne'), Real.log_mul (by norm_num : (2 : ℝ) ^ (36 : ℕ) ≠ 0)
    (Real.exp_ne_zero 1), Real.log_pow, Real.log_exp, Real.log_pow] at hh
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh h2
  push_cast
  linarith

lemma cost_scale_properties {t z d v δ : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z)
    (hd : 0 ≤ d) (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let H := (8 + t + z + d + v) / δ
    2 ≤ H ∧ 1 + t ≤ H ∧ z ≤ H ∧ d ≤ H ∧ 1 / δ ≤ H ∧ 1 ≤ Real.log H := by
  dsimp only
  have hn : 0 ≤ 8 + t + z + d + v := by positivity
  have hh : 8 + t + z + d + v ≤ (8 + t + z + d + v) / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have h1 : 1 / δ ≤ (8 + t + z + d + v) / δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, h1, ?_⟩
  apply (Real.le_log_iff_exp_le (by positivity : 0 < (8 + t + z + d + v) / δ)).mpr
  have he := Real.exp_one_lt_three
  linarith


lemma call_envelope_power {K A M C ell q V w : ℝ} (hK0 : 0 ≤ K) (hK : K ≤ 4096 * A)
    (hA : 1 ≤ A) (_hM0 : 0 ≤ M) (hM : M ≤ A) (hC : 1 ≤ C) (hl : 1 ≤ ell) (hq : 0 ≤ q)
    (hV : V ≤ 2 * C * M * ell ^ q) (hw : w ≤ C * M * ell ^ q) :
    4 * K * (2 + 16 * ell) + 8 * 1099511627776 * (V + w) * ell ^ 2 ≤
      70368744177664 * C * A * ell ^ (q + 2) := by
  have hP : ell ^ (q + 2) = ell ^ q * ell ^ (2 : ℕ) := by
    rw [Real.rpow_add (by linarith : 0 < ell), Real.rpow_two]
  have hle : ell ≤ ell ^ (q + 2) := by
    calc
      ell = ell ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hl (by linarith)
  have hCA : A ≤ C * A := by nlinarith
  have hOver : 4 * K * (2 + 16 * ell) ≤ 294912 * C * A * ell ^ (q + 2) := by
    calc
      _ ≤ 4 * (4096 * A) * (18 * ell) := by gcongr; linarith
      _ = 294912 * A * ell := by ring
      _ ≤ _ := by gcongr; linarith
  have hnoise : 8 * 1099511627776 * (V + w) * ell ^ 2 ≤
      26388279066624 * C * A * ell ^ (q + 2) := by
    calc
      _ ≤ 8 * 1099511627776 * (3 * C * M * ell ^ q) * ell ^ 2 := by
        gcongr
        linarith
      _ = 26388279066624 * C * M * ell ^ (q + 2) := by rw [hP]; ring
      _ ≤ _ := by gcongr
  have hn : 0 ≤ C * A * ell ^ (q + 2) := by positivity
  nlinarith only [hOver, hnoise, hn]

lemma envelope_coefficient {q L ell A : ℝ} (hq : 0 ≤ q) (hL : 1 ≤ L)
    (hl0 : 0 ≤ ell) (hl : ell ≤ 64 * L) (hA : 0 ≤ A) :
    70368744177664 * (1024 * (1048576 : ℝ) ^ q) * A * ell ^ (q + 2) ≤
      (2 : ℝ) ^ (128 + 128 * q) * A * L ^ (q + 2) := by
  have hc : 70368744177664 * (1024 * (1048576 : ℝ) ^ q) * (64 : ℝ) ^ (q + 2) =
      (2 : ℝ) ^ (68 + 26 * q) := by
    rw [show (1048576 : ℝ) = (2 : ℝ) ^ (20 : ℝ) by norm_num,
      show (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hconst : (70368744177664 : ℝ) * 1024 = (2 : ℝ) ^ (56 : ℝ) := by norm_num
    calc
      _ = ((70368744177664 : ℝ) * 1024) * (2 : ℝ) ^ (20 * q) * (2 : ℝ) ^ (6 * (q + 2)) := by ring
      _ = _ := by rw [hconst, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; congr 1; ring
  calc
    _ ≤ 70368744177664 * (1024 * (1048576 : ℝ) ^ q) * A * (64 * L) ^ (q + 2) := by gcongr
    _ = (2 : ℝ) ^ (68 + 26 * q) * A * L ^ (q + 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) (by linarith : 0 ≤ L)]
      calc
        _ = (70368744177664 * (1024 * (1048576 : ℝ) ^ q) * (64 : ℝ) ^ (q + 2)) * A * L ^ (q + 2) := by ring
        _ = _ := by rw [hc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _)
      apply mul_le_mul_of_nonneg_right ?_ hA
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma explicit_call_budget (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (G : ℝ) (hG : 0 ≤ G) (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (ξ : ℕ → p.Ω) :
    let K := ⌈20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε) + (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) * Real.sqrt (p.Δ / (p.L0 * p.R ^ 2)))⌉₊
    let B := ⌈(2 : ℝ) ^ (128 + 128 / (p.α - 1)) * (1 + Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε) + (1 + p.L1 * p.R) * Real.log (2 + (1 + p.L1 * p.R) * Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) + (p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))) * (Real.log ((8 + p.L1 * p.R + (p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε + p.Δ / (p.L0 * p.R ^ 2) + p.σ * p.R / p.ε) / p.δ)) ^ (2 + 1 / (p.α - 1))⌉₊
    StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K) ≤ B := by
  let t := p.L1 * p.R
  let z := (p.L0 + 192 * p.L1 * p.σ + p.L1 * G) * p.R ^ 2 / p.ε
  let d := p.Δ / (p.L0 * p.R ^ 2)
  let v := p.σ * p.R / p.ε
  let q := 1 / (p.α - 1)
  let K := ⌈20 * Real.sqrt z + (6 + 256 * t) * Real.log (2 + (3 + 192 * t) * Real.sqrt d)⌉₊
  let H := (8 + t + z + d + v) / p.δ
  let A := 1 + Real.sqrt z + (1 + t) * Real.log (2 + (1 + t) * Real.sqrt d) + v ^ (p.α / (p.α - 1))
  let C := 1024 * (1048576 : ℝ) ^ q
  let M := (max 1 v) ^ (p.α / (p.α - 1))
  let ell := confidence p (4 * K)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ p.α / (p.α - 1) := by positivity
  have hlog : 0 ≤ Real.log (2 + (1 + t) * Real.sqrt d) :=
    Real.log_nonneg (by nlinarith [Real.sqrt_nonneg d, mul_nonneg ht (Real.sqrt_nonneg d)])
  have hA : 1 ≤ A := by
    have hh : 0 ≤ (1 + t) * Real.log (2 + (1 + t) * Real.sqrt d) := by positivity
    dsimp [A]
    linarith [Real.sqrt_nonneg z, Real.rpow_nonneg hv (p.α / (p.α - 1))]
  have hM0 : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  have hM : M ≤ A := by
    dsimp [M, A]
    rw [Real.rpow_max (by norm_num : (0 : ℝ) ≤ 1) hv hr, Real.one_rpow]
    apply max_le
    · have hh : 0 ≤ (1 + t) * Real.log (2 + (1 + t) * Real.sqrt d) := by positivity
      linarith [Real.sqrt_nonneg z, Real.rpow_nonneg hv (p.α / (p.α - 1))]
    · have hh : 0 ≤ (1 + t) * Real.log (2 + (1 + t) * Real.sqrt d) := by positivity
      linarith [Real.sqrt_nonneg z]
  have hC : 1 ≤ C := by
    have hh := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 1048576) hq
    dsimp only [C]
    linarith
  have hK : (K : ℝ) ≤ 4096 * A := horizon_upper_core ht hz hd hv
  have hHs := cost_scale_properties ht hz hd hv hδ hδ1
  change 2 ≤ H ∧ 1 + t ≤ H ∧ z ≤ H ∧ d ≤ H ∧ 1 / p.δ ≤ H ∧ 1 ≤ Real.log H at hHs
  have hKH : (K : ℝ) ≤ 4096 * H ^ 2 := horizon_upper_scale ht hz hd hHs.1 hHs.2.1 hHs.2.2.1 hHs.2.2.2.1
  have hell : ell ≤ 64 * Real.log H := horizon_confidence_upper hδ hHs.1 hHs.2.2.2.2.2 hHs.2.2.2.2.1 hKH
  have hell1 : 1 ≤ ell := confidence_lower p hδ hδ1 _
  have hV := varianceBound_normalized_upper p hR hσ hα hα2 hε hδ hδ1 (4 * K)
  have hw := clipRadius_normalized_upper p hR hσ hα hε hδ hδ1 (4 * K)
  have he := call_envelope_power (show 0 ≤ (K : ℝ) by positivity) hK hA hM0 hM hC hell1 hq hV hw
  have hbound := blockCalls_upper p I g hL0 hL1 hR hσ hα hα2 hΔ hε hδ hδ1 ξ (4 * K)
  have hc := envelope_coefficient hq hHs.2.2.2.2.2 (by linarith : 0 ≤ ell) hell (by linarith : 0 ≤ A)
  have hfinal : (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K) : ℝ) ≤
      (2 : ℝ) ^ (128 + 128 * q) * A * (Real.log H) ^ (q + 2) := by
    calc
      _ ≤ _ := hbound
      _ ≤ 70368744177664 * C * A * ell ^ (q + 2) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using he
      _ ≤ _ := hc
  rw [add_comm q 2] at hfinal
  have hf : StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ (4 * K) ≤
      ⌈(2 : ℝ) ^ (128 + 128 * q) * A * (Real.log H) ^ (2 + q)⌉₊ := by
    exact_mod_cast hfinal.trans (Nat.le_ceil _)
  simpa only [K, q, A, H, t, z, d, v, div_eq_mul_inv, one_mul, mul_assoc] using hf

end OracleTemplate.StochasticCompositeGeneralized
