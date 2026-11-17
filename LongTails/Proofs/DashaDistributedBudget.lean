import LongTails.Proofs.DashaDistributedSelection
import LongTails.Proofs.DashaPrecisionCutoff

namespace LongTails.Proofs.DashaDistributedBudget

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedTrackedParameters
open LongTails.Algorithms.DashaDistributedSelection
open DashaPrecisionCutoff

lemma timeBudget_expanded (p : Params) (cfg : Config p) :
    timeBudget p cfg = (cfg.iterations : ℕ) * (computationTime p + p.l + 64 * p.b) +
      p.b * ((initialBits p cfg : Time) + (((cfg.iterations : ℕ) - 1 : ℕ) : Time) * (roundBits p cfg : Time)) + cfg.slack := by
  have hk : (cfg.iterations : ℕ) - 1 + 1 = cfg.iterations := Nat.sub_add_cancel cfg.iterations.pos
  have hc : (((cfg.iterations : ℕ) - 1 : ℕ) : Time) + 1 = (cfg.iterations : ℕ) := by exact_mod_cast hk
  unfold timeBudget
  push_cast
  rw [← hc]
  norm_num [clockBits]
  ring

lemma size_double_add_one (m : ℕ) : Nat.size (2 * m + 1) ≤ Nat.size m + 1 := by
  apply Nat.size_le.mpr
  have hm := Nat.lt_size_self m
  rw [pow_succ]
  omega

lemma size_le_of_double {m n : ℕ} (h : m ≤ 2 * n) : Nat.size m ≤ Nat.size n + 1 :=
  (Nat.size_le_size (h.trans (by omega))).trans (size_double_add_one n)

lemma ceil_le_double {x y : ℝ} (h : x ≤ 2 * y) : ⌈x⌉₊ ≤ 2 * ⌈y⌉₊ := by
  apply Nat.ceil_le.mpr
  push_cast
  linarith [Nat.le_ceil y]

lemma size_ceil_le_double {x y : ℝ} (h : x ≤ 2 * y) :
    Nat.size ⌈x⌉₊ ≤ Nat.size ⌈y⌉₊ + 1 := size_le_of_double (ceil_le_double h)

lemma double_size_ceil_le {x y : ℝ} (h : x ≤ 2 * y) :
    Nat.size (Nat.size ⌈x⌉₊) ≤ Nat.size (Nat.size ⌈y⌉₊) + 1 := by
  have hs := size_ceil_le_double h
  exact (Nat.size_le_size (hs.trans (by omega))).trans (size_double_add_one _)

lemma exponent_width_cap {A Anew C Cnew : ℝ} {K Knew : ℕ}
    (hA : Anew ≤ 2 * A) (hC : Cnew ≤ C) (hK : Knew ≤ 2 * K) :
    Nat.size (Nat.size ⌈Anew⌉₊ + Knew * Nat.size ⌈Cnew⌉₊) ≤
      Nat.size (Nat.size ⌈A⌉₊ + K * Nat.size ⌈C⌉₊) + 1 := by
  have ha := size_ceil_le_double hA
  have hc := Nat.size_le_size (Nat.ceil_mono hC)
  have hm := Nat.mul_le_mul hK hc
  have ht : Nat.size ⌈Anew⌉₊ + Knew * Nat.size ⌈Cnew⌉₊ ≤
      2 * (Nat.size ⌈A⌉₊ + K * Nat.size ⌈C⌉₊) + 1 := by nlinarith
  exact (Nat.size_le_size ht).trans (size_double_add_one _)

lemma packet_bits_cap {k r rnew e enew : ℕ} (hr : rnew ≤ r) (he : enew ≤ e + 1) :
    3 * (k * (rnew + enew + 3)) ≤ 4 * (k * (r + e + 3)) := by
  have hs : 3 * (rnew + enew + 3) ≤ 4 * (r + e + 3) := by omega
  nlinarith only [Nat.mul_le_mul_left k hs]

lemma dense_bits_cap {d w wnew : ℕ} (hw : 1 ≤ w) (he : wnew ≤ w + 1) : d * wnew ≤ 2 * (d * w) := by
  have hs : wnew ≤ 2 * w := by omega
  nlinarith only [Nat.mul_le_mul_left d hs]

lemma time_formula_cap (τ b : Time) {K Knew I Inew B Bnew : ℕ}
    (hK0 : 2 ≤ K) (hK : Knew ≤ 2 * K) (hI : Inew ≤ 2 * I) (hB : 3 * Bnew ≤ 4 * B) :
    (Knew : Time) * τ + b * ((Inew : Time) + ((Knew - 1 : ℕ) : Time) * Bnew) ≤
      4 * ((K : Time) * τ + b * ((I : Time) + ((K - 1 : ℕ) : Time) * B)) := by
  have hround : Knew - 1 ≤ 3 * (K - 1) := by omega
  have hroundB : (Knew - 1) * Bnew ≤ 4 * ((K - 1) * B) := by
    have h1 := Nat.mul_le_mul_right Bnew hround
    have h2 := Nat.mul_le_mul_left (K - 1) hB
    nlinarith only [h1, h2]
  have hwork : Inew + (Knew - 1) * Bnew ≤ 4 * (I + (K - 1) * B) := by omega
  have hkc : (Knew : Time) ≤ 4 * (K : Time) := by exact_mod_cast (show Knew ≤ 4 * K by omega)
  have hwc : (Inew : Time) + ((Knew - 1 : ℕ) : Time) * Bnew ≤
      4 * ((I : Time) + ((K - 1 : ℕ) : Time) * B) := by exact_mod_cast hwork
  have h1 := mul_le_mul_of_nonneg_right hkc (show 0 ≤ τ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hwc (show 0 ≤ b by positivity)
  calc
    _ ≤ (4 * (K : Time)) * τ + b * (4 * ((I : Time) + ((K - 1 : ℕ) : Time) * B)) := add_le_add h1 h2
    _ = _ := by ring

lemma range_ratio {X Xnew ρ ρnew : ℝ} (hX : 0 ≤ X) (hnew : Xnew ≤ X)
    (hρ : 0 < ρ) (hρnew : 0 < ρnew) (hratio : ρ ≤ 2 * ρnew) :
    Xnew / ρnew ≤ 2 * (X / ρ) := by
  have h1 := mul_le_mul_of_nonneg_right hnew hρ.le
  have h2 := mul_le_mul_of_nonneg_left hratio hX
  have he : 2 * (X / ρ) = (2 * X) / ρ := by ring
  rw [he]
  apply (div_le_div_iff₀ hρnew hρ).mpr
  nlinarith only [h1, h2]

variable {p : Params}

lemma growthFactor_cap (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) :
    growthFactor p (capChoice p c) ≤ growthFactor p c := by
  have hq := DashaScalingParameters.multiplier_ge_one c
  change (2 + 2 * LongTails.Algorithms.DashaCyclic.multiplier c.block) *
      (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p (capChoice p c)) ≤ _
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ))
    (mul_le_mul_of_nonneg_left (capChoice_stepSize_le c hL hH)
      (show 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat by positivity))) (by positivity)

lemma trackingInitialEnvelope_cap (c : Choice p) (initializer : Option (Choice p)) (hε : 0 < p.ε) :
    trackingInitialEnvelope p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) ≤
      trackingInitialEnvelope p c initializer := by
  have hd := mul_le_mul_of_nonneg_right (capChoice_spacing_le c hε) (Real.sqrt_nonneg (p.d : ℝ))
  cases initializer <;> simp only [trackingInitialEnvelope, Option.map_none, Option.map_some, capInitializer] <;> linarith

lemma trackingInputBound_cap (c : Choice p) (initializer : Option (Choice p))
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    trackingInputBound p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) ≤
      2 * trackingInputBound p c initializer := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hηnew := DashaScalingParameters.stepSize_pos (capChoice p c) hL hH
  have hq := DashaScalingParameters.multiplier_ge_one c
  have hR := DashaDistributedTrackingCapacity.trackingRadius_nonneg (trackedConfig p c initializer false) hε hG
  have hRnew := DashaDistributedTrackingCapacity.trackingRadius_nonneg
    (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) false) hε hG
  have hf := add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left (capChoice_stepSize_le c hL hH)
    (show 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat by positivity))
  have hp := mul_le_mul hf (trackingInitialEnvelope_cap c initializer hε) hRnew (by positivity)
  have hx := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block by linarith)
  have hb := range_ratio (show 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block *
      ((1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) * trackingInitialEnvelope p c initializer) by positivity)
    hx (DashaScalingParameters.spacing_pos c hε) (DashaScalingParameters.spacing_pos (capChoice p c) hε)
    (capChoice_spacing_ratio c hε)
  unfold trackingInputBound
  change LongTails.Algorithms.DashaCyclic.multiplier c.block * _ * _ / _ ≤ _
  convert hb using 1 <;> ring

lemma roundCount_cap (c : Choice p) (initializer : Option (Choice p)) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (roundCount p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) : ℕ) ≤
      2 * (roundCount p c initializer : ℕ) := by
  cases initializer with
  | none => exact cap_iterations c hL hH hΔ hε
  | some initializer => exact cap_sparseIterations c initializer hL hH hΔ hG hε

lemma tracked_exponentWidth_cap (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) modularInitialization).exponentWidth ≤
      (trackedConfig p c initializer modularInitialization).exponentWidth + 1 :=
  exponent_width_cap (trackingInputBound_cap c initializer hL hH hG hε)
    (growthFactor_cap c hL hH) (roundCount_cap c initializer hL hH hΔ hG hε)

lemma signedInitialRange_cap (c : Choice p) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    p.G / spacing p (capChoice p c) + 1 ≤ 2 * (p.G / spacing p c + 1) := by
  have hb := range_ratio hG (le_refl p.G) (DashaScalingParameters.spacing_pos c hε)
    (DashaScalingParameters.spacing_pos (capChoice p c) hε) (capChoice_spacing_ratio c hε)
  linarith

lemma modularInitialBound_cap (c : Choice p) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    modularInitialBound p (capChoice p c) ≤ 2 * modularInitialBound p c := by
  have hJ : 0 ≤ globalInitialBound p := by unfold globalInitialBound; positivity
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hd := mul_le_mul_of_nonneg_right (capChoice_spacing_le c hε) (Real.sqrt_nonneg (p.d : ℝ))
  have hn := mul_le_mul_of_nonneg_left (add_le_add (le_refl (globalInitialBound p)) hd)
    (show (0 : ℝ) ≤ p.n by positivity)
  exact range_ratio (by positivity) hn hρ (DashaScalingParameters.spacing_pos (capChoice p c) hε)
    (capChoice_spacing_ratio c hε)

lemma sparseInitialRange_cap (c initializer : Choice p) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    LongTails.Algorithms.DashaCyclic.multiplier initializer.block * p.G / spacing p (capChoice p c) ≤
      2 * (LongTails.Algorithms.DashaCyclic.multiplier initializer.block * p.G / spacing p c) := by
  have hq := DashaScalingParameters.multiplier_ge_one initializer
  exact range_ratio (by positivity) (le_refl _) (DashaScalingParameters.spacing_pos c hε)
    (DashaScalingParameters.spacing_pos (capChoice p c) hε) (capChoice_spacing_ratio c hε)

lemma tracked_initialWidth_cap (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) modularInitialization).initialWidth ≤
      (trackedConfig p c initializer modularInitialization).initialWidth + 1 := by
  cases initializer with
  | none =>
      cases modularInitialization with
      | false =>
          have hb := size_ceil_le_double (signedInitialRange_cap c hG hε)
          change Nat.size ⌈p.G / spacing p (capChoice p c) + 1⌉₊ + 1 ≤
            Nat.size ⌈p.G / spacing p c + 1⌉₊ + 1 + 1
          omega
      | true =>
          have hb := size_ceil_le_double (modularInitialBound_cap c hG hε)
          change Nat.size ⌈modularInitialBound p (capChoice p c)⌉₊ + 1 ≤
            Nat.size ⌈modularInitialBound p c⌉₊ + 1 + 1
          omega
  | some initializer =>
      cases modularInitialization <;> exact double_size_ceil_le (sparseInitialRange_cap c initializer hG hε)

lemma tracked_roundBits_cap (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    3 * roundBits p (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) modularInitialization) ≤
      4 * roundBits p (trackedConfig p c initializer modularInitialization) :=
  packet_bits_cap (Nat.min_le_left _ _) (tracked_exponentWidth_cap c initializer modularInitialization hL hH hΔ hG hε)

lemma tracked_initialBits_cap (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    initialBits p (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) modularInitialization) ≤
      2 * initialBits p (trackedConfig p c initializer modularInitialization) := by
  have hw := tracked_initialWidth_cap c initializer modularInitialization hG hε
  cases initializer with
  | none =>
      have hwidth : 1 ≤ (trackedConfig p c none modularInitialization).initialWidth := by
        cases modularInitialization <;> change 1 ≤ Nat.size _ + 1 <;> omega
      exact dense_bits_cap hwidth hw
  | some initializer =>
      have hb := packet_bits_cap (k := initializer.block.val + 1)
        (Nat.min_le_left initializer.precision (initialPrecision p (capChoice p c))) hw
      change 3 * initialBits p (trackedConfig p (capChoice p c)
          ((some initializer).map (capInitializer p (capChoice p c))) modularInitialization) ≤
        4 * initialBits p (trackedConfig p c (some initializer) modularInitialization) at hb
      omega

lemma roundCount_ge_two (c : Choice p) (initializer : Option (Choice p))
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    2 ≤ (roundCount p c initializer : ℕ) := by
  have hD := DashaScalingParameters.denominator_pos c hL hH
  cases initializer with
  | none =>
      have hn : 0 < 32 * p.Δ * denominator p c / p.ε ^ 2 := by positivity
      have hc := Nat.ceil_pos.mpr hn
      change 2 ≤ 1 + ⌈32 * p.Δ * denominator p c / p.ε ^ 2⌉₊
      omega
  | some initializer =>
      have hw := DashaScalingParameters.variance_nonneg c
      have hwi := DashaScalingParameters.variance_nonneg initializer
      have hA : 0 ≤ initialPenalty p c initializer := by unfold initialPenalty; positivity
      have hn : 0 < (32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2 := by positivity
      have hc := Nat.ceil_pos.mpr hn
      change 2 ≤ 1 + ⌈(32 * p.Δ * denominator p c + 4 * initialPenalty p c initializer) / p.ε ^ 2⌉₊
      omega

lemma tracked_time_cap (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 < p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    timeBudget p (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) modularInitialization) ≤
      4 * timeBudget p (trackedConfig p c initializer modularInitialization) := by
  rw [timeBudget_expanded, timeBudget_expanded]
  have hz : (trackedConfig p c initializer modularInitialization).slack = 0 := rfl
  have hznew : (trackedConfig p (capChoice p c)
      (initializer.map (capInitializer p (capChoice p c))) modularInitialization).slack = 0 := rfl
  rw [hz, hznew]
  simp only [add_zero]
  exact time_formula_cap (computationTime p + p.l + 64 * p.b) p.b (roundCount_ge_two c initializer hL hH hΔ hε)
    (roundCount_cap c initializer hL hH hΔ.le hG hε) (tracked_initialBits_cap c initializer modularInitialization hG hε)
    (tracked_roundBits_cap c initializer modularInitialization hL hH hΔ.le hG hε)

lemma candidateCost_ofChoices (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool) :
    candidateCost p (candidateOfChoices p c initializer modularInitialization) =
      timeBudget p (trackedConfig p (capChoice p c) (initializer.map (capInitializer p (capChoice p c))) modularInitialization) := by
  cases initializer <;> rfl

lemma selected_cost_le_any_precision (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hΔ : 0 < p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    candidateCost p (selected p) ≤ 4 * timeBudget p (trackedConfig p c initializer modularInitialization) := by
  have hs := DashaDistributedSelection.selected_le p (candidateOfChoices p c initializer modularInitialization)
  rw [candidateCost_ofChoices] at hs
  exact hs.trans (tracked_time_cap c initializer modularInitialization hL hH hΔ hG hε)

lemma timeBound_competitive (hp : spec.valid p)
    (c : Choice (LongTails.Algorithms.DashaDistributedNormalization.normalize p))
    (initializer : Option (Choice (LongTails.Algorithms.DashaDistributedNormalization.normalize p)))
    (modularInitialization : Bool) :
    timeBound p ≤ 4 * timeBudget (LongTails.Algorithms.DashaDistributedNormalization.normalize p)
      (trackedConfig (LongTails.Algorithms.DashaDistributedNormalization.normalize p) c initializer modularInitialization) := by
  classical
  unfold timeBound
  split_ifs with hc
  · positivity
  · have hLeff : 0 < min p.L p.Lhat := lt_min hp.2.1 hp.2.2.1
    have hgap : p.ε ^ 2 < 2 * min p.L p.Lhat * p.Δ := (lt_of_not_ge hc).trans_le (min_le_left _ _)
    have hprod : 0 < (2 * min p.L p.Lhat) * p.Δ := (sq_nonneg p.ε).trans_lt hgap
    have hΔ : 0 < p.Δ := (mul_pos_iff_of_pos_left (show 0 < 2 * min p.L p.Lhat by positivity)).mp hprod
    obtain ⟨_, hL, hH, _, hG, hε⟩ := DashaDistributedNormalization.normalized_valid hp
    exact selected_cost_le_any_precision c initializer modularInitialization hL hH hΔ hG hε

lemma size_mul_le (m n : ℕ) : Nat.size (m * n) ≤ Nat.size m + Nat.size n := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have hm := Nat.lt_size_self m
  have hn := Nat.lt_size_self n
  nlinarith

lemma exponent_width_sum_upper {u c K : ℕ} (hu : 1 ≤ u) (hK : 1 ≤ K) (hc : c ≤ u + 1) :
    Nat.size (u + K * c) ≤ Nat.size K + Nat.size u + 2 := by
  have hbound : u + K * c ≤ 4 * (K * u) := by
    have hmul := Nat.mul_le_mul_left K hc
    have hku : u ≤ K * u := by nlinarith
    have hk : K ≤ K * u := by nlinarith
    nlinarith
  apply Nat.size_le.mpr
  have hp := Nat.size_le.mp (size_mul_le K u)
  have hstrict : 4 * (K * u) < 4 * 2 ^ (Nat.size K + Nat.size u) := by omega
  have heq : 4 * 2 ^ (Nat.size K + Nat.size u) = 2 ^ (Nat.size K + Nat.size u + 2) := by
    rw [pow_add]
    ring
  exact hbound.trans_lt (hstrict.trans_eq heq)

lemma exponent_width_sum_lower {u c K : ℕ} (hc : 1 ≤ c) :
    Nat.size K + Nat.size u ≤ 2 * Nat.size (u + K * c) := by
  have hK : K ≤ u + K * c := by nlinarith
  have hu : u ≤ u + K * c := by omega
  have h1 := Nat.size_le_size hK
  have h2 := Nat.size_le_size hu
  omega

lemma range_growth_comparison {q t R ρ : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ t)
    (hρ : 0 < ρ) (hR : 3 * ρ ≤ R) :
    1 ≤ q * t * R / ρ ∧ 1 ≤ (2 + 2 * q) * t ∧ (2 + 2 * q) * t ≤ 2 * (q * t * R / ρ) := by
  have hqt : 1 ≤ q * t := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ q * t by linarith)
  have hU : 3 * (q * t) ≤ q * t * R / ρ := (le_div_iff₀ hρ).mpr (by nlinarith only [hm])
  have hC : (2 + 2 * q) * t ≤ 4 * (q * t) := by
    have hm := mul_le_mul_of_nonneg_right hq (show 0 ≤ t by linarith)
    nlinarith only [hm]
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma tracking_range_growth (c : Choice p) (initializer : Option (Choice p))
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    1 ≤ trackingInputBound p c initializer ∧ 1 ≤ growthFactor p c ∧
      growthFactor p c ≤ 2 * trackingInputBound p c initializer := by
  have hq := DashaScalingParameters.multiplier_ge_one c
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have ht : 1 ≤ 1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c := by
    have hh : 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c := by positivity
    linarith
  have hd : (1 : ℝ) ≤ Real.sqrt (p.d : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p.d by exact_mod_cast (show (1 : ℕ) ≤ p.d from p.d.pos))
  have hbase : 0 ≤ globalInitialBound p + (match initializer with
      | none => 0
      | some c₀ => (2 * LongTails.Algorithms.DashaCyclic.multiplier c₀.block + 1) * p.G) := by
    cases initializer <;> simp only [globalInitialBound, LongTails.Algorithms.DashaCyclic.multiplier] <;> positivity
  have hR : 3 * spacing p c ≤ trackingInitialEnvelope p c initializer := by
    unfold trackingInitialEnvelope
    have hm := mul_le_mul_of_nonneg_left hd hρ.le
    cases initializer <;> dsimp only at hbase ⊢ <;> nlinarith only [hbase, hm]
  exact range_growth_comparison hq ht hρ hR

lemma tracked_exponentWidth_sum (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (trackedConfig p c initializer modularInitialization).exponentWidth ≤
      Nat.size (roundCount p c initializer) + Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊) + 2 := by
  obtain ⟨hU, hC, hCU⟩ := tracking_range_growth c initializer hL hH hG hε
  have hceil : 1 ≤ ⌈trackingInputBound p c initializer⌉₊ := by
    exact_mod_cast hU.trans (Nat.le_ceil _)
  have hu : 1 ≤ Nat.size ⌈trackingInputBound p c initializer⌉₊ := by
    have hm := Nat.size_le_size hceil
    norm_num at hm ⊢
    exact hm
  exact exponent_width_sum_upper hu (roundCount p c initializer).pos (size_ceil_le_double hCU)

lemma tracked_exponentWidth_sum_lower (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    Nat.size (roundCount p c initializer) + Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊) ≤
      2 * (trackedConfig p c initializer modularInitialization).exponentWidth := by
  obtain ⟨_, hC, _⟩ := tracking_range_growth c initializer hL hH hG hε
  have hceil : 1 ≤ ⌈growthFactor p c⌉₊ := by exact_mod_cast hC.trans (Nat.le_ceil _)
  have hc : 1 ≤ Nat.size ⌈growthFactor p c⌉₊ := by
    simpa using Nat.size_le_size hceil
  exact exponent_width_sum_lower hc

lemma tracked_roundBits_sum_comparison (c : Choice p) (initializer : Option (Choice p)) (modularInitialization : Bool)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    roundBits p (trackedConfig p c initializer modularInitialization) ≤
      (c.block.val + 1) * (c.precision + Nat.size (roundCount p c initializer) +
        Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊) + 5) ∧
    (c.block.val + 1) * (c.precision + Nat.size (roundCount p c initializer) +
        Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊) + 5) ≤
      2 * roundBits p (trackedConfig p c initializer modularInitialization) := by
  have hu := tracked_exponentWidth_sum c initializer modularInitialization hL hH hG hε
  have hl := tracked_exponentWidth_sum_lower c initializer modularInitialization hL hH hG hε
  change (c.block.val + 1) * (c.precision + (trackedConfig p c initializer modularInitialization).exponentWidth + 3) ≤ _ ∧
    _ ≤ 2 * ((c.block.val + 1) * (c.precision + (trackedConfig p c initializer modularInitialization).exponentWidth + 3))
  constructor
  · exact Nat.mul_le_mul_left _ (by omega)
  · have hm := Nat.mul_le_mul_left (c.block.val + 1)
      (show c.precision + Nat.size (roundCount p c initializer) +
        Nat.size (Nat.size ⌈trackingInputBound p c initializer⌉₊) + 5 ≤
        2 * (c.precision + (trackedConfig p c initializer modularInitialization).exponentWidth + 3) by omega)
    nlinarith only [hm]

end LongTails.Proofs.DashaDistributedBudget
