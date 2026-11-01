import LongTails.Proofs.TwoSidedPerceptronExecution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronParameters

open LongTails.Setups.TwoSidedConvolutionalPerceptron
open LongTails.Algorithms.TwoSidedConvolutionalPerceptron
open TwoSidedPerceptronDynamics (State)
open TwoSidedPerceptronTrajectory
open TwoSidedPerceptronGeometry
open TwoSidedPerceptronExecution
open TwoSidedPerceptronCounting (pow_one_sub_le_exp)

noncomputable def count (p : Params) : ℕ :=
  ⌈2 ^ 24 * (p.upper / p.lower) ^ 2 * (1 + Real.log (1 + p.lower / p.contrast)) / p.margin ^ 3⌉₊

structure Basic (p : Params) : Prop where
  d_pos : 0 < p.dimension
  g_pos : 0 < p.lower
  g_le : p.lower ≤ p.upper
  μ_pos : 0 < p.contrast
  κ_pos : 0 < p.margin
  κ_le : p.margin ≤ 1
  regime : p.margin * p.contrast * count p ≤ 3 * p.upper / 2

section Sqrt

lemma s_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma s_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma s_lo : (1414 : ℝ) / 1000 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma s_hi : Real.sqrt 2 < (1415 : ℝ) / 1000 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma one_div_s : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  rw [div_eq_div_iff s_pos.ne' (by norm_num : (2 : ℝ) ≠ 0), one_mul, s_sq]

end Sqrt

variable {p : Params}

lemma upper_pos (h : Basic p) : 0 < p.upper := h.g_pos.trans_le h.g_le

lemma stepSize_pos (h : Basic p) : 0 < stepSize p := by
  unfold stepSize; have := upper_pos h; have := h.κ_pos; positivity

lemma stepSize_pos_of_valid (p : Params) (hp : spec.valid p) : 0 < stepSize p := by
  unfold stepSize
  have hR : 0 < p.upper := hp.2.1.trans_le hp.2.2.1
  have hκ := hp.2.2.2.2.1
  positivity

lemma margin_le_one {d n : ℕ} {D : Data d n} {g R μ κ : ℝ} (G : Geometry D g R μ κ) : κ ≤ 1 := by
  have h1 := G.derivative_margin 0
  have h2 := real_inner_le_norm (derivative (G.defect 0)) G.separator
  have h3 : ‖derivative (G.defect 0)‖ ≤ 1 := minus_norm G 0
  rw [G.separator_unit, mul_one] at h2
  linarith

lemma basic_of_valid (hp : spec.valid p) (hκ : p.margin ≤ 1) : Basic p :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hκ, hp.2.2.2.2.2⟩

noncomputable def control (p : Params) (h : Basic p) : Control where
  clo := Real.sqrt 2 * stepSize p * p.lower
  C := Real.sqrt 2 * stepSize p * p.upper
  κ := p.margin
  δ := stepSize p * p.contrast
  a₀ := 1 / Real.sqrt 2
  t₀ := 1 / Real.sqrt 2
  clo_pos := by have := stepSize_pos h; have := h.g_pos; have := s_pos; positivity
  clo_le := by
    have := stepSize_pos h; have := s_pos
    exact mul_le_mul_of_nonneg_left h.g_le (by positivity)
  C_le := by
    have hR := upper_pos h
    have e : Real.sqrt 2 * stepSize p * p.upper = Real.sqrt 2 * p.margin / 96 := by
      unfold stepSize; field_simp
    rw [e]
    have := s_hi; have := h.κ_le; have := h.κ_pos
    nlinarith
  C_le_κ := by
    have hR := upper_pos h
    have e : Real.sqrt 2 * stepSize p * p.upper = Real.sqrt 2 * p.margin / 96 := by
      unfold stepSize; field_simp
    rw [e]
    have := s_hi; have := h.κ_pos
    nlinarith
  κ_pos := h.κ_pos
  κ_le := h.κ_le
  δ_pos := by have := stepSize_pos h; have := h.μ_pos; positivity
  a₀_pos := by have := s_pos; positivity
  t₀_pos := by have := s_pos; positivity

section ControlFacts

variable (h : Basic p)

lemma control_start :
    ((control p h).start : State (Features p.dimension)) =
      ⟨1 / Real.sqrt 2, 0, 1 / Real.sqrt 2, 0⟩ := rfl

lemma control_δ : (control p h).δ = stepSize p * p.contrast := rfl

lemma control_C : (control p h).C = Real.sqrt 2 * p.margin / 96 := by
  change Real.sqrt 2 * stepSize p * p.upper = _
  have hR := upper_pos h
  unfold stepSize; field_simp

lemma control_clo : (control p h).clo = Real.sqrt 2 * (p.margin * p.lower / p.upper) / 96 := by
  change Real.sqrt 2 * stepSize p * p.lower = _
  have hR := upper_pos h
  unfold stepSize; field_simp

lemma control_F : (control p h).F = 2 * Real.sqrt 2 := by
  change 2 * (1 / Real.sqrt 2) + 2 * (1 / Real.sqrt 2) = _
  have := s_sq; have := s_pos.ne'
  field_simp
  nlinarith

lemma geometry {D : Data p.dimension p.samples}
    (G : Geometry D p.lower p.upper p.contrast p.margin) :
    TwoSidedPerceptronTrajectory.Geometry (control p h) (coeff G (stepSize p)) (plus G) (minus G)
      G.separator where
  lower i := by
    rw [coeff_abs G (stepSize_pos h)]
    change Real.sqrt 2 * stepSize p * p.lower ≤ _
    have := stepSize_pos h; have := s_pos
    exact mul_le_mul_of_nonneg_left (G.background_lower i) (by positivity)
  upper i := by
    rw [coeff_abs G (stepSize_pos h)]
    change _ ≤ Real.sqrt 2 * stepSize p * p.upper
    have := stepSize_pos h; have := s_pos
    exact mul_le_mul_of_nonneg_left (G.background_upper i) (by positivity)
  p_norm i := plus_norm G i
  r_norm i := minus_norm G i
  w_unit := G.separator_unit
  margin i := G.derivative_margin i

end ControlFacts

noncomputable def halfLength (p : Params) (h : Basic p) : ℕ :=
  ⌈Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) / ((control p h).clo ^ 2 / 8)⌉₊ + 1

noncomputable def xscale (p : Params) : ℝ := p.margin * p.lower / p.upper

section Arithmetic

variable (h : Basic p)
include h

lemma xscale_pos : 0 < xscale p := by
  unfold xscale; have := upper_pos h; have := h.g_pos; have := h.κ_pos; positivity

lemma xscale_le_one : xscale p ≤ 1 := by
  unfold xscale
  have hR := upper_pos h
  rw [div_le_one hR]
  have h1 : p.margin * p.lower ≤ p.lower := mul_le_of_le_one_left h.g_pos.le h.κ_le
  linarith [h.g_le]

lemma xscale_le_κ : xscale p ≤ p.margin := by
  unfold xscale
  have hR := upper_pos h
  rw [div_le_iff₀ hR]
  exact mul_le_mul_of_nonneg_left h.g_le h.κ_pos.le

lemma clo_eq : (control p h).clo = Real.sqrt 2 * xscale p / 96 := control_clo h

lemma clo_sq : (control p h).clo ^ 2 = (xscale p) ^ 2 / 4608 := by
  rw [clo_eq h, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring

omit h in
lemma count_ge : 2 ^ 24 * (1 + Real.log (1 + p.lower / p.contrast)) / (p.margin * (xscale p) ^ 2) ≤
    (count p : ℝ) := by
  have hx : p.margin * (xscale p) ^ 2 = p.margin ^ 3 * p.lower ^ 2 / p.upper ^ 2 := by
    unfold xscale; rw [div_pow]; ring
  have e : 2 ^ 24 * (p.upper / p.lower) ^ 2 * (1 + Real.log (1 + p.lower / p.contrast)) /
      p.margin ^ 3 = 2 ^ 24 * (1 + Real.log (1 + p.lower / p.contrast)) /
        (p.margin * (xscale p) ^ 2) := by
    rw [hx, div_div_eq_mul_div]; ring
  rw [← e]
  exact Nat.le_ceil _

lemma logp_nonneg : 0 ≤ Real.log (1 + p.lower / p.contrast) := by
  apply Real.log_nonneg
  have := h.g_pos; have := h.μ_pos
  have : 0 ≤ p.lower / p.contrast := by positivity
  linarith

lemma log_le_logp : Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) ≤
    Real.log (1 + p.lower / p.contrast) := by
  have hμ := h.μ_pos; have hg := h.g_pos; have hs := s_pos
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have e : p.lower / p.contrast * p.contrast = p.lower := div_mul_cancel₀ p.lower hμ.ne'
  have h1 : Real.sqrt 2 * p.lower ≤ 2 * p.lower :=
    mul_le_mul_of_nonneg_right (s_hi.le.trans (by norm_num)) hg.le
  linarith

lemma regime_small : (control p h).δ * (count p : ℝ) ≤ 1 / 64 := by
  rw [control_δ]
  unfold stepSize
  have hR := upper_pos h
  have hreg := h.regime
  have e : p.margin / (96 * p.upper) * p.contrast * (count p : ℝ) =
      p.margin * p.contrast * (count p : ℝ) / (96 * p.upper) := by ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith

lemma count_pos : (1 : ℝ) ≤ (count p : ℝ) := by
  have h1 := count_ge (p := p)
  have hx := xscale_pos h
  have hx1 := xscale_le_one h
  have hκ := h.κ_pos
  have hL := logp_nonneg h
  have hden : p.margin * (xscale p) ^ 2 ≤ 1 := by
    have := mul_le_mul h.κ_le (pow_le_one₀ hx.le hx1) (sq_nonneg (xscale p)) zero_le_one
    linarith
  have hden0 : 0 < p.margin * (xscale p) ^ 2 := by positivity
  have : (1 : ℝ) ≤ 2 ^ 24 * (1 + Real.log (1 + p.lower / p.contrast)) /
      (p.margin * (xscale p) ^ 2) := by
    rw [le_div_iff₀ hden0]; linarith
  linarith

lemma δ_le : (control p h).δ ≤ 1 / 64 := by
  have h1 := regime_small h
  have h2 := count_pos h
  have hδ := (control p h).δ_pos
  have h3 : (control p h).δ ≤ (control p h).δ * (count p : ℝ) := le_mul_of_one_le_right hδ.le h2
  linarith

lemma a₀_eq : (control p h).a₀ = 1 / Real.sqrt 2 := rfl

lemma t₀_eq : (control p h).t₀ = 1 / Real.sqrt 2 := rfl

lemma two_a₀ : 2 * (control p h).a₀ = Real.sqrt 2 := by
  rw [a₀_eq h, one_div_s]; ring

lemma regime : Regime (control p h) (count p) := by
  have hsmall := regime_small h
  have hδ := (control p h).δ_pos
  have hδ1 := δ_le h
  have hF := control_F h
  have hC := (control p h).C_le
  have hC0 : 0 ≤ (control p h).C := (control p h).clo_pos.le.trans (control p h).clo_le
  have hs2 := s_sq
  have hs0 := s_pos
  have ha₀ := a₀_eq h
  have ht₀ := t₀_eq h
  have hK0 : (0 : ℝ) ≤ (count p : ℝ) := Nat.cast_nonneg _
  obtain ⟨δ, hδdef⟩ : ∃ δ, (control p h).δ = δ := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, (count p : ℝ) = K := ⟨_, rfl⟩
  rw [hδdef, hKdef] at hsmall
  rw [hδdef] at hδ hδ1
  rw [hKdef] at hK0
  have hδK0 : 0 ≤ δ * K := mul_nonneg hδ.le hK0
  have hδK2 : (δ * K) ^ 2 ≤ 1 / 4096 := by
    have := pow_le_pow_left₀ hδK0 hsmall 2
    have e : ((1 : ℝ) / 64) ^ 2 = 1 / 4096 := by norm_num
    linarith
  have hδδK : δ * (δ * K) ≤ 1 / 4096 := by
    have := mul_le_mul hδ1 hsmall hδK0 (by norm_num)
    have e : (1 : ℝ) / 64 * (1 / 64) = 1 / 4096 := by norm_num
    linarith
  have hhalf : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hinv : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := mul_one_div_cancel hs0.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Control.drift Control.Z
    rw [hF, ha₀, hδdef, hKdef]
    have e2 : 12 * (1 / Real.sqrt 2) * δ * (δ * (2 * Real.sqrt 2) * K) = 24 * δ * (δ * K) := by
      linear_combination (24 * δ * (δ * K)) * hinv
    have hKd : K * (4 * (control p h).C * δ * (2 * Real.sqrt 2) * (δ * (2 * Real.sqrt 2) * K) +
        δ ^ 2 * (2 * Real.sqrt 2) ^ 2 + 12 * (1 / Real.sqrt 2) * δ * (δ * (2 * Real.sqrt 2) * K) +
        2 * δ ^ 2 * (δ * (2 * Real.sqrt 2) * K) ^ 2) =
        32 * (control p h).C * (δ * K) ^ 2 + 8 * δ * (δ * K) + 24 * (δ * K) ^ 2 +
          16 * (δ * K) ^ 2 * (δ * (δ * K)) := by
      rw [e2]
      linear_combination
        (16 * (control p h).C * δ ^ 2 * K ^ 2 + 4 * δ ^ 2 * K + 8 * δ ^ 4 * K ^ 3) * hs2
    have a1 : (control p h).C * (δ * K) ^ 2 ≤ 1 / 8 * (1 / 4096) :=
      mul_le_mul hC hδK2 (sq_nonneg _) (by norm_num)
    have a2 : (δ * K) ^ 2 * (δ * (δ * K)) ≤ 1 / 4096 * (1 / 4096) :=
      mul_le_mul hδK2 hδδK (mul_nonneg hδ.le hδK0) (by norm_num)
    linarith
  · rw [hF, ht₀, hδdef, hKdef, one_div_s]
    have := mul_le_mul_of_nonneg_right hδK2 hs0.le
    linarith
  · unfold Control.Z
    rw [hF, hδdef, hKdef]
    have := mul_le_mul_of_nonneg_right hδδK hs0.le
    linarith
  · rw [hδdef, hKdef]; exact hsmall
  · rw [hδdef]; linarith

lemma halfLength_pos : 0 < halfLength p h := by unfold halfLength; omega

lemma halfLength_ge_one : (1 : ℝ) ≤ (halfLength p h : ℝ) := by
  have : 1 ≤ halfLength p h := halfLength_pos h
  exact_mod_cast this

lemma Z_two_m : (control p h).Z (2 * halfLength p h) =
    4 * Real.sqrt 2 * (control p h).δ * (halfLength p h : ℝ) := by
  unfold Control.Z; rw [control_F h]; push_cast; ring

lemma threshold_sq_eq : (control p h).threshold (2 * halfLength p h) ^ 2 =
    9437184 * (control p h).δ ^ 2 * (halfLength p h : ℝ) / (xscale p) ^ 2 := by
  rw [(control p h).threshold_sq, Z_two_m h, control_F h, clo_sq h, div_div_eq_mul_div]
  congr 1
  linear_combination (4718592 * (control p h).δ ^ 2 * (halfLength p h : ℝ)) * s_sq

lemma δ_div_x : (control p h).δ / xscale p = p.contrast / (96 * p.lower) := by
  rw [control_δ]; unfold stepSize xscale
  have hR := upper_pos h; have hg := h.g_pos; have hκ := h.κ_pos
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

lemma threshold_lower :
    32 * p.contrast / p.lower ≤ (control p h).threshold (2 * halfLength p h) := by
  have hnn := (control p h).threshold_nonneg (2 * halfLength p h)
  have hg := h.g_pos; have hμ := h.μ_pos
  have hm := halfLength_ge_one h
  have hδx := δ_div_x h
  have hval : (32 * p.contrast / p.lower) ^ 2 ≤
      (control p h).threshold (2 * halfLength p h) ^ 2 := by
    rw [threshold_sq_eq h]
    have e : 9437184 * (control p h).δ ^ 2 * (halfLength p h : ℝ) / (xscale p) ^ 2 =
        9437184 * ((control p h).δ / xscale p) ^ 2 * (halfLength p h : ℝ) := by
      rw [div_pow]; ring
    rw [e, hδx]
    have e2 : 9437184 * (p.contrast / (96 * p.lower)) ^ 2 = 1024 * (p.contrast / p.lower) ^ 2 := by
      rw [div_pow, div_pow, mul_pow]; ring
    rw [e2]
    have h0 : 0 ≤ (p.contrast / p.lower) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hm h0
    have e3 : (32 * p.contrast / p.lower) ^ 2 = 1024 * (p.contrast / p.lower) ^ 2 := by
      rw [div_pow, div_pow, mul_pow]; ring
    rw [e3]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) hnn two_ne_zero).mp hval

lemma decay :
    (1 - (control p h).clo ^ 2 / 8) ^ halfLength p h * (2 * (control p h).a₀) ≤
      (control p h).threshold (2 * halfLength p h) := by
  have hclo := (control p h).clo_pos
  have hclo1 := (control p h).clo_le_one
  have hq0 : 0 < (control p h).clo ^ 2 / 8 := by positivity
  have hq1 : (control p h).clo ^ 2 / 8 ≤ 1 := by
    have : (control p h).clo ^ 2 ≤ 1 := pow_le_one₀ hclo.le hclo1
    linarith
  have hg := h.g_pos; have hμ := h.μ_pos; have hs0 := s_pos
  have hpos : 0 < Real.sqrt 2 * p.lower / (32 * p.contrast) := by positivity
  have hm : Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) / ((control p h).clo ^ 2 / 8) ≤
      (halfLength p h : ℝ) := by
    unfold halfLength; push_cast
    linarith [Nat.le_ceil (Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) /
      ((control p h).clo ^ 2 / 8))]
  rw [div_le_iff₀ hq0] at hm
  have h1 := pow_one_sub_le_exp hq0.le hq1 (halfLength p h)
  have h2 : Real.exp (-((control p h).clo ^ 2 / 8 * (halfLength p h : ℝ))) ≤
      Real.exp (-Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast))) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast))) =
      32 * p.contrast / (Real.sqrt 2 * p.lower) := by
    rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have h4 : 32 * p.contrast / (Real.sqrt 2 * p.lower) * Real.sqrt 2 = 32 * p.contrast / p.lower := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) hg.ne']
    ring
  rw [two_a₀ h]
  calc (1 - (control p h).clo ^ 2 / 8) ^ halfLength p h * Real.sqrt 2
      ≤ Real.exp (-Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast))) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hs0.le
    _ = 32 * p.contrast / p.lower := by rw [h3, h4]
    _ ≤ _ := threshold_lower h

lemma halfLength_le :
    (halfLength p h : ℝ) ≤ 36864 * (1 + Real.log (1 + p.lower / p.contrast)) / (xscale p) ^ 2 := by
  have hx := xscale_pos h
  have hx1 := xscale_le_one h
  have hL := logp_nonneg h
  have hLL := log_le_logp h
  have hx2 : 0 < (xscale p) ^ 2 := by positivity
  have hx21 : (xscale p) ^ 2 ≤ 1 := pow_le_one₀ hx.le hx1
  have hq : (control p h).clo ^ 2 / 8 = (xscale p) ^ 2 / 36864 := by rw [clo_sq h]; ring
  have hceil : (⌈Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) /
      ((xscale p) ^ 2 / 36864)⌉₊ : ℝ) ≤
      36864 * Real.log (1 + p.lower / p.contrast) / (xscale p) ^ 2 + 1 := by
    have hpos : 0 ≤ 36864 * Real.log (1 + p.lower / p.contrast) / (xscale p) ^ 2 := by positivity
    by_cases hneg : Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) /
        ((xscale p) ^ 2 / 36864) ≤ 0
    · rw [Nat.ceil_eq_zero.mpr hneg]; push_cast; linarith
    · replace hneg := not_le.mp hneg
      have h1 := Nat.ceil_lt_add_one hneg.le
      have e : Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) / ((xscale p) ^ 2 / 36864) =
          36864 * Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) / (xscale p) ^ 2 := by
        rw [div_div_eq_mul_div]; ring
      have h2 : 36864 * Real.log (Real.sqrt 2 * p.lower / (32 * p.contrast)) / (xscale p) ^ 2 ≤
          36864 * Real.log (1 + p.lower / p.contrast) / (xscale p) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) hx2.le
      linarith
  have h36 : (2 : ℝ) ≤ 36864 / (xscale p) ^ 2 := by
    rw [le_div_iff₀ hx2]; linarith
  have e : 36864 * (1 + Real.log (1 + p.lower / p.contrast)) / (xscale p) ^ 2 =
      36864 / (xscale p) ^ 2 + 36864 * Real.log (1 + p.lower / p.contrast) / (xscale p) ^ 2 := by
    ring
  rw [e]
  unfold halfLength
  rw [hq]
  push_cast
  linarith

lemma threshold_upper :
    (control p h).threshold (2 * halfLength p h) ≤
      589824 * (control p h).δ * (1 + Real.log (1 + p.lower / p.contrast)) / (xscale p) ^ 2 := by
  have hnn := (control p h).threshold_nonneg (2 * halfLength p h)
  have hδ := (control p h).δ_pos
  have hx := xscale_pos h
  have hL := logp_nonneg h
  have hm := halfLength_le h
  have hx2 : 0 < (xscale p) ^ 2 := by positivity
  have hmx : (halfLength p h : ℝ) * (xscale p) ^ 2 ≤
      36864 * (1 + Real.log (1 + p.lower / p.contrast)) := by
    rw [le_div_iff₀ hx2] at hm; exact hm
  have hval : (control p h).threshold (2 * halfLength p h) ^ 2 ≤
      (589824 * (control p h).δ * (1 + Real.log (1 + p.lower / p.contrast)) /
        (xscale p) ^ 2) ^ 2 := by
    rw [threshold_sq_eq h, div_pow, div_le_div_iff₀ hx2 (by positivity)]
    have hδ2 : 0 ≤ (control p h).δ ^ 2 := sq_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hmx
      (by positivity : (0 : ℝ) ≤ 9437184 * (control p h).δ ^ 2)
    have h2 : 0 ≤ (control p h).δ ^ 2 * ((1 + Real.log (1 + p.lower / p.contrast)) *
        Real.log (1 + p.lower / p.contrast)) := mul_nonneg hδ2 (mul_nonneg (by linarith) hL)
    have h3 : 9437184 * (control p h).δ ^ 2 *
        (36864 * (1 + Real.log (1 + p.lower / p.contrast))) ≤
        (589824 * (control p h).δ * (1 + Real.log (1 + p.lower / p.contrast))) ^ 2 := by
      linarith
    have h4 := mul_le_mul_of_nonneg_right (h1.trans h3) hx2.le
    linarith
  exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).mp hval

lemma main_inequality :
    2 * (halfLength p h : ℝ) + (control p h).bound (halfLength p h) < (count p : ℝ) := by
  have hs2 := s_sq
  have hs0 := s_pos
  have hshi := s_hi
  have hκ := h.κ_pos
  have hκ1 := h.κ_le
  have hx := xscale_pos h
  have hx1 := xscale_le_one h
  have hL := logp_nonneg h
  have hδK := regime_small h
  have hδ := (control p h).δ_pos
  have hF := control_F h
  have hZ := Z_two_m h
  have ht₀ := t₀_eq h
  have hκeq : (control p h).κ = p.margin := rfl
  have h2a := two_a₀ h
  have hm0 : (0 : ℝ) ≤ (halfLength p h : ℝ) := Nat.cast_nonneg _
  have hx2 : 0 < (xscale p) ^ 2 := by positivity
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 1 / (xscale p) ^ 2 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = 1 / p.margin := ⟨_, rfl⟩
  have hU0 : 0 < U := by rw [hU]; positivity
  have hV0 : 0 < V := by rw [hV]; positivity
  have hU1 : 1 ≤ U := by rw [hU, le_div_iff₀ hx2, one_mul]; exact pow_le_one₀ hx.le hx1
  have hV1 : 1 ≤ V := by rw [hV, le_div_iff₀ hκ, one_mul]; exact hκ1
  have hUV : V ≤ U := by
    rw [hU, hV]
    apply div_le_div_of_nonneg_left zero_le_one hx2
    have : xscale p * xscale p ≤ xscale p := mul_le_of_le_one_left hx.le hx1
    have := xscale_le_κ h
    rw [sq]; linarith
  have hm : (halfLength p h : ℝ) ≤ 36864 * (1 + Real.log (1 + p.lower / p.contrast)) * U := by
    have e : 36864 * (1 + Real.log (1 + p.lower / p.contrast)) / (xscale p) ^ 2 =
        36864 * (1 + Real.log (1 + p.lower / p.contrast)) * U := by rw [hU]; ring
    rw [← e]; exact halfLength_le h
  have hK : 2 ^ 24 * (1 + Real.log (1 + p.lower / p.contrast)) * U * V ≤ (count p : ℝ) := by
    have e : 2 ^ 24 * (1 + Real.log (1 + p.lower / p.contrast)) / (p.margin * (xscale p) ^ 2) =
        2 ^ 24 * (1 + Real.log (1 + p.lower / p.contrast)) * U * V := by rw [hU, hV]; ring
    rw [← e]; exact count_ge
  have hthr : (control p h).threshold (2 * halfLength p h) ≤
      589824 * (control p h).δ * (1 + Real.log (1 + p.lower / p.contrast)) * U := by
    have e : 589824 * (control p h).δ * (1 + Real.log (1 + p.lower / p.contrast)) /
        (xscale p) ^ 2 =
        589824 * (control p h).δ * (1 + Real.log (1 + p.lower / p.contrast)) * U := by
      rw [hU]; ring
    rw [← e]; exact threshold_upper h
  have hLU0 : 0 ≤ Real.log (1 + p.lower / p.contrast) * U := mul_nonneg hL hU0.le
  have hWx0 : 0 ≤ (1 + Real.log (1 + p.lower / p.contrast)) * U :=
    mul_nonneg (by linarith) hU0.le
  have hW0 : 0 < (1 + Real.log (1 + p.lower / p.contrast)) * U * V :=
    mul_pos (mul_pos (by linarith) hU0) hV0
  have hκW : (1 + Real.log (1 + p.lower / p.contrast)) * U ≤
      (1 + Real.log (1 + p.lower / p.contrast)) * U * V := by
    have := mul_le_mul_of_nonneg_left hV1 hWx0
    linarith
  have hκ2W : V * V ≤ (1 + Real.log (1 + p.lower / p.contrast)) * U * V := by
    have h1 := mul_le_mul_of_nonneg_left hUV hV0.le
    have h2 := mul_le_mul_of_nonneg_right
      (by linarith : (1 : ℝ) ≤ 1 + Real.log (1 + p.lower / p.contrast)) (mul_nonneg hU0.le hV0.le)
    linarith
  have hm455 : 455 * (halfLength p h : ℝ) ≤ (count p : ℝ) := by linarith
  have hδm : (control p h).δ * (halfLength p h : ℝ) ≤ 1 / 29120 := by
    have := mul_le_mul_of_nonneg_left hm455 hδ.le
    linarith
  have hδm0 : 0 ≤ (control p h).δ * (halfLength p h : ℝ) := mul_nonneg hδ.le hm0
  have hδm2 : ((control p h).δ * (halfLength p h : ℝ)) ^ 2 ≤ 1 / 847974400 := by
    have := pow_le_pow_left₀ hδm0 hδm 2
    have e : ((1 : ℝ) / 29120) ^ 2 = 1 / 847974400 := by norm_num
    linarith
  have b1 : Real.sqrt 2 * U ≤ 1415 / 1000 * U := mul_le_mul_of_nonneg_right hshi.le hU0.le
  have b3 : Real.sqrt 2 * ((control p h).δ * (halfLength p h : ℝ)) ^ 2 ≤
      1415 / 1000 * (1 / 847974400) :=
    mul_le_mul hshi.le hδm2 (sq_nonneg _) (by norm_num)
  have b2 := mul_le_mul_of_nonneg_right b3 hU0.le
  have b4 : Real.sqrt 2 * ((control p h).δ * (halfLength p h : ℝ)) ≤ 1415 / 1000 * (1 / 29120) :=
    mul_le_mul hshi.le hδm hδm0 (by norm_num)
  have b5 := mul_le_mul_of_nonneg_right b4 hU0.le
  have hps : (control p h).phaseSum (halfLength p h) ≤ 55426 * U := by
    have e : (control p h).phaseSum (halfLength p h) =
        17 / 16 * (8 * Real.sqrt 2 * 4608 * U +
          40 * (halfLength p h : ℝ) * ((control p h).δ *
            (4 * Real.sqrt 2 * (control p h).δ * (halfLength p h : ℝ))) * 4608 * U) +
          (halfLength p h : ℝ) * ((control p h).δ *
            (4 * Real.sqrt 2 * (control p h).δ * (halfLength p h : ℝ))) := by
      unfold Control.phaseSum
      rw [hZ, h2a, clo_sq h, hU]
      ring
    linarith
  have hthr' : (control p h).threshold (2 * halfLength p h) / (control p h).δ ≤
      589824 * (1 + Real.log (1 + p.lower / p.contrast)) * U := by
    rw [div_le_iff₀ hδ]
    linarith
  have htail : (control p h).tail (halfLength p h) ≤
      (589824 * (1 + Real.log (1 + p.lower / p.contrast)) + 36) * U := by
    have e : (control p h).tail (halfLength p h) =
        (control p h).threshold (2 * halfLength p h) / (control p h).δ +
          40 * (4 * Real.sqrt 2 * (control p h).δ * (halfLength p h : ℝ)) * 4608 * U := by
      unfold Control.tail
      rw [hZ, clo_sq h, hU]
      ring
    linarith
  have e8 : 2 * Real.sqrt 2 * (2 * Real.sqrt 2) * (halfLength p h : ℝ) =
      8 * (halfLength p h : ℝ) := by
    linear_combination (4 * (halfLength p h : ℝ)) * hs2
  have hA : (control p h).phaseSum (halfLength p h) +
      65 / 64 * (2 * Real.sqrt 2 * (2 * Real.sqrt 2) * (halfLength p h : ℝ) +
        (control p h).tail (halfLength p h)) ≤
      954100 * (1 + Real.log (1 + p.lower / p.contrast)) * U := by
    linarith
  have hbound : (control p h).bound (halfLength p h) ≤
      7632800 * Real.sqrt 2 * (1 + Real.log (1 + p.lower / p.contrast)) * U * V +
        4225 / 2 * (V * V) := by
    have e : (control p h).bound (halfLength p h) =
        8 * ((control p h).phaseSum (halfLength p h) +
          65 / 64 * (2 * Real.sqrt 2 * (2 * Real.sqrt 2) * (halfLength p h : ℝ) +
            (control p h).tail (halfLength p h))) * Real.sqrt 2 * V +
          64 * (65 / 64 * Real.sqrt 2 * (2 * Real.sqrt 2)) ^ 2 * Real.sqrt 2 ^ 2 * (V * V) := by
      unfold Control.bound
      rw [hF, ht₀, hκeq, one_div_mul_eq_div, div_div_eq_mul_div, div_pow, div_div_eq_mul_div, hV]
      ring
    have e2 : 64 * (65 / 64 * Real.sqrt 2 * (2 * Real.sqrt 2)) ^ 2 * Real.sqrt 2 ^ 2 * (V * V) =
        4225 / 2 * (V * V) := by
      linear_combination (4225 / 16 * (Real.sqrt 2 ^ 4 + 2 * Real.sqrt 2 ^ 2 + 4) * (V * V)) * hs2
    have hAs := mul_le_mul_of_nonneg_left hA
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hs0) hV0).le
    linarith
  have hsW := mul_le_mul_of_nonneg_right hshi.le hW0.le
  linarith

end Arithmetic

lemma iterate_budget_separates (p : Params) (hp : spec.valid p) {D : Data p.dimension p.samples}
    (G : Geometry D p.lower p.upper p.contrast p.margin) :
    Separates D ((TwoSidedPerceptronExecution.step D (stepSize p))^[(p.samples + 1) *
      ⌈2 ^ 24 * (p.upper / p.lower) ^ 2 * (1 + Real.log (1 + p.lower / p.contrast)) /
        p.margin ^ 3⌉₊] (initial p.dimension p.samples)).point := by
  have h := basic_of_valid hp (margin_le_one G)
  exact iterate_separates G h.d_pos (stepSize_pos h) (control_δ h) (control_start h) (geometry h G)
    (regime h) (halfLength_pos h) (decay h) (main_inequality h)

end LongTails.Proofs.TwoSidedPerceptronParameters
