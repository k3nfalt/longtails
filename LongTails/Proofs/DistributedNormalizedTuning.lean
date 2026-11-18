import LongTails.Proofs.DistributedNormalizedPrecision
import LongTails.Proofs.DistributedNormalizedEstimator

namespace LongTails.Proofs.DistributedNormalizedTuning

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTuning

lemma phaseScale_bounds (p : Params) :
    256 * (computationTime p : ℝ) ≤ phaseScale p ∧
    256 * uplinkCost p ≤ phaseScale p ∧
    256 * downlinkCost p ≤ phaseScale p ∧
    256 * (p.d * uplinkCost p / p.n) ≤ phaseScale p ∧
    256 * (p.d * downlinkCost p / Real.sqrt p.n) ≤ phaseScale p ∧
    256 * (((p.d : ℝ) ^ 3 * uplinkCost p * downlinkCost p ^ 2 / p.n) ^ (1 / 3 : ℝ)) ≤ phaseScale p ∧
    256 * (p.σ ^ 2 * (computationTime p : ℝ) / (p.n * p.ε ^ 2)) ≤ phaseScale p ∧
    256 * Real.sqrt (p.d * p.σ ^ 2 * (computationTime p : ℝ) * uplinkCost p / (p.n * p.ε ^ 2)) ≤ phaseScale p ∧
    256 * (p.d * downlinkCost p * min 1 (Real.sqrt (p.Q * p.ε) / p.L)) ≤ phaseScale p := by
  unfold phaseScale
  repeat' constructor
  all_goals apply mul_le_mul_of_nonneg_left _ (by norm_num)
  · exact le_max_left _ _
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))

lemma computationTime_pos (p : Params) (hh : ∀ i, 0 < p.h i) : 0 < computationTime p := by
  have h := Finset.le_sup (f := p.h) (Finset.mem_univ (0 : Fin p.n))
  exact (hh 0).trans_le h

lemma phaseScale_pos (p : Params) (hh : ∀ i, 0 < p.h i) : 0 < phaseScale p := by
  have hH : (0 : ℝ) < computationTime p := computationTime_pos p hh
  exact (mul_pos (by norm_num) hH).trans_le (phaseScale_bounds p).1

lemma max_floor_bounds {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ ((max 1 ⌊x⌋₊ : ℕ) : ℝ) ∧ ((max 1 ⌊x⌋₊ : ℕ) : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hlo := Nat.lt_floor_add_one x
  have hup := Nat.floor_le hx0
  rw [Nat.cast_max, Nat.cast_one]
  constructor
  · exact (show x / 2 ≤ (⌊x⌋₊ : ℝ) by linarith).trans (le_max_right _ _)
  · exact max_le (by linarith) hup

lemma uplinkCost_nonneg (p : Params) : 0 ≤ uplinkCost p := by
  unfold uplinkCost
  positivity

lemma downlinkCost_nonneg (p : Params) : 0 ≤ downlinkCost p := by
  unfold downlinkCost
  positivity

lemma compressed_uplink_count (p : Params)
    (hfull : fullUplink p = false) :
    0 < uplinkCost p ∧ phaseScale p ≤ 2 * uplinkCost p * uplinkCount p ∧
      (uplinkCount p : ℝ) * uplinkCost p ≤ phaseScale p := by
  have hf : ¬ (uplinkCost p = 0 ∨ p.d * uplinkCost p ≤ phaseScale p) := by
    simpa only [fullUplink, decide_eq_false_iff_not] using hfull
  have hc : 0 < uplinkCost p := lt_of_le_of_ne (uplinkCost_nonneg p) (Ne.symm fun h => hf (Or.inl h))
  have ht := (phaseScale_bounds p).2.1
  have hratio : 2 ≤ phaseScale p / uplinkCost p := (le_div_iff₀ hc).mpr (by linarith)
  have hb := max_floor_bounds hratio
  have he : ((uplinkCount p : ℕ) : ℝ) = ((max 1 ⌊phaseScale p / uplinkCost p⌋₊ : ℕ) : ℝ) := by
    simp only [uplinkCount, hfull, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [← he] at hb
  refine ⟨hc, ?_, ?_⟩
  · have hv := (div_le_iff₀ hc).mp (show phaseScale p / uplinkCost p ≤ 2 * uplinkCount p by linarith [hb.1])
    nlinarith
  · exact (le_div_iff₀ hc).mp hb.2

lemma compression_variance_scale (p : Params) (hd : 0 < p.d) (hh : ∀ i, 0 < p.h i) :
    compressionVariance p * phaseScale p ≤ 2 * p.d * uplinkCost p := by
  have ht := phaseScale_pos p hh
  have hc := uplinkCost_nonneg p
  cases hf : fullUplink p
  · obtain ⟨_, hm, _⟩ := compressed_uplink_count p hf
    have hmpos : (0 : ℝ) < uplinkCount p := by exact_mod_cast (uplinkCount p).pos
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    unfold compressionVariance
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmpos).mpr
    have hb := mul_le_mul_of_nonneg_left hm hd0
    nlinarith
  · simp only [compressionVariance, hf, ↓reduceIte, zero_mul]
    positivity

lemma relative_variance_small (p : Params) (hd : 0 < p.d) (hh : ∀ i, 0 < p.h i) :
    compressionVariance p / p.n ≤ 1 / 128 := by
  have ht := phaseScale_pos p hh
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hv := compression_variance_scale p hd hh
  have hb := (phaseScale_bounds p).2.2.2.1
  have hb' : 256 * p.d * uplinkCost p ≤ phaseScale p * p.n := by
    apply (div_le_iff₀ hn).mp
    convert hb using 1
    ring
  apply (div_le_iff₀ hn).mpr
  nlinarith

lemma compressed_downlink_count (p : Params)
    (hfull : fullDownlink p = false) :
    0 < downlinkCost p ∧ phaseScale p ≤ 2 * downlinkCost p * downlinkCount p ∧
      (downlinkCount p : ℝ) * downlinkCost p ≤ phaseScale p := by
  have hf : ¬ (downlinkCost p = 0 ∨ p.d * downlinkCost p ≤ phaseScale p) := by
    simpa only [fullDownlink, decide_eq_false_iff_not] using hfull
  have hc : 0 < downlinkCost p := lt_of_le_of_ne (downlinkCost_nonneg p) (Ne.symm fun h => hf (Or.inl h))
  have ht := (phaseScale_bounds p).2.2.1
  have hratio : 2 ≤ phaseScale p / downlinkCost p := (le_div_iff₀ hc).mpr (by linarith)
  have hb := max_floor_bounds hratio
  have he : ((downlinkCount p : ℕ) : ℝ) = ((max 1 ⌊phaseScale p / downlinkCost p⌋₊ : ℕ) : ℝ) := by
    simp only [downlinkCount, hfull, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [← he] at hb
  refine ⟨hc, ?_, ?_⟩
  · have hv := (div_le_iff₀ hc).mp (show phaseScale p / downlinkCost p ≤ 2 * downlinkCount p by linarith [hb.1])
    nlinarith
  · exact (le_div_iff₀ hc).mp hb.2

lemma refreshPeriod_sub_one (p : Params) (hh : ∀ i, 0 < p.h i) :
    ((refreshPeriod p : ℝ) - 1) * phaseScale p ≤ p.d * downlinkCost p := by
  have ht := phaseScale_pos p hh
  have hc := downlinkCost_nonneg p
  cases hf : fullDownlink p
  · have hq : 0 ≤ p.d * downlinkCost p / phaseScale p := by positivity
    have hfloor := Nat.floor_le hq
    have hb : ((max 1 ⌊p.d * downlinkCost p / phaseScale p⌋₊ : ℕ) : ℝ) - 1 ≤
        p.d * downlinkCost p / phaseScale p := by
      apply (sub_le_iff_le_add).mpr
      rw [Nat.cast_max, Nat.cast_one]
      exact max_le (by linarith) (by linarith)
    have he : (refreshPeriod p : ℝ) = ((max 1 ⌊p.d * downlinkCost p / phaseScale p⌋₊ : ℕ) : ℝ) := by
      simp only [refreshPeriod, hf, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [← he] at hb
    exact (le_div_iff₀ ht).mp hb
  · simp only [refreshPeriod, hf, ↓reduceIte]
    simp only [PNat.one_coe, Nat.cast_one, sub_self, zero_mul]
    positivity

noncomputable def consensusFactor (p : Params) : ℝ :=
  1 / 64 + 2 * p.d * ((refreshPeriod p : ℝ) - 1) / downlinkCount p

lemma consensusFactor_nonneg (p : Params) : 0 ≤ consensusFactor p := by
  have hr : (1 : ℝ) ≤ refreshPeriod p := by exact_mod_cast Nat.succ_le_of_lt (refreshPeriod p).pos
  unfold consensusFactor
  positivity

lemma consensusFactor_bound (p : Params) (hh : ∀ i, 0 < p.h i) :
    consensusFactor p ≤ 1 / 64 + 4 * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 / phaseScale p ^ 2 := by
  have ht := phaseScale_pos p hh
  have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hc := downlinkCost_nonneg p
  have hr : (1 : ℝ) ≤ refreshPeriod p := by exact_mod_cast Nat.succ_le_of_lt (refreshPeriod p).pos
  cases hf : fullDownlink p
  · obtain ⟨_, hl, _⟩ := compressed_downlink_count p hf
    have hℓ : (0 : ℝ) < downlinkCount p := by exact_mod_cast (downlinkCount p).pos
    have hR := refreshPeriod_sub_one p hh
    have hm := mul_le_mul hR hl ht.le (mul_nonneg hd hc)
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * (p.d : ℝ) by positivity)
    unfold consensusFactor
    apply add_le_add le_rfl
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hℓ).mpr
    nlinarith
  · have hr' : (refreshPeriod p : ℝ) = 1 := by
      simp only [refreshPeriod, hf, ↓reduceIte, PNat.one_coe, Nat.cast_one]
    unfold consensusFactor
    rw [hr']
    simp only [sub_self, mul_zero, zero_div, add_zero]
    exact le_add_of_nonneg_right (by positivity)

lemma periodic_consensus_bound (p : Params) (k : ℕ) {η : ℝ} :
    η ^ 2 / 64 + ((k % (refreshPeriod p : ℕ) : ℕ) : ℝ) *
      (2 * p.d * η ^ 2 / downlinkCount p) ≤ η ^ 2 * consensusFactor p := by
  have hr := Nat.mod_lt k (refreshPeriod p).pos
  have hmod : ((k % (refreshPeriod p : ℕ) : ℕ) : ℝ) ≤ (refreshPeriod p : ℝ) - 1 := by
    have h := Nat.succ_le_of_lt hr
    have hc : ((k % (refreshPeriod p : ℕ) : ℕ) : ℝ) + 1 ≤ (refreshPeriod p : ℝ) := by exact_mod_cast h
    linarith
  have hm := mul_le_mul_of_nonneg_right hmod
    (show 0 ≤ 2 * p.d * η ^ 2 / (downlinkCount p : ℝ) by positivity)
  calc
    _ ≤ η ^ 2 / 64 + ((refreshPeriod p : ℝ) - 1) *
        (2 * p.d * η ^ 2 / downlinkCount p) := add_le_add le_rfl hm
    _ = _ := by unfold consensusFactor; ring

lemma estimator_relative_variance (p : Params) :
    DistributedNormalizedEstimator.relativeVariance p (config p) = compressionVariance p := rfl

lemma compression_coefficient_small (p : Params) (hd : 0 < p.d) (hh : ∀ i, 0 < p.h i) :
    Real.sqrt (2 * compressionVariance p / p.n) ≤ 1 / 8 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have h := relative_variance_small p hd hh
  rw [mul_div_assoc]
  nlinarith

lemma estimator_grid_variance (p : Params) (hd : 0 < p.d) :
    DistributedNormalizedEstimator.gridVariance p (config p) / p.n = p.ε ^ 2 / 16384 := by
  have hdpos : (0 : ℝ) < p.d := Nat.cast_pos.mpr hd
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hm : (0 : ℝ) < uplinkCount p := by exact_mod_cast (uplinkCount p).pos
  cases hf : fullUplink p
  · have hsq := Real.sq_sqrt (show 0 ≤ (uplinkCount p : ℝ) * p.n by positivity)
    simp only [DistributedNormalizedEstimator.gridVariance, config, hf, Bool.false_eq_true, ↓reduceIte]
    rw [div_pow, mul_pow, hsq]
    field_simp
    ring
  · have hsq := Real.sq_sqrt (show 0 ≤ (p.n : ℝ) / p.d by positivity)
    simp only [DistributedNormalizedEstimator.gridVariance, config, hf, ↓reduceIte]
    rw [div_pow, mul_pow, hsq]
    field_simp
    ring

lemma grid_norm_error (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) :
    Real.sqrt (DistributedNormalizedEstimator.gridVariance p (config p) / p.n) = p.ε / 128 := by
  rw [estimator_grid_variance p hd]
  have he : p.ε ^ 2 / 16384 = (p.ε / 128) ^ 2 := by ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

lemma clipping_bias_small (p : Params) (hε : 0 < p.ε) :
    (p.σ ^ 2 / batch p) / (4 * clipMargin p) ≤ p.ε / 128 := by
  have hv : 0 ≤ p.σ ^ 2 / (batch p : ℝ) := by positivity
  have ha : 0 < clipMargin p := by unfold clipMargin; positivity
  apply (div_le_iff₀ (show 0 < 4 * clipMargin p by positivity)).mpr
  unfold clipMargin
  field_simp
  nlinarith

lemma stochastic_norm_error (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) :
    Real.sqrt ((1 + compressionVariance p) * (p.σ ^ 2 / batch p) / p.n) ≤ p.ε / 128 := by
  have hb := DistributedNormalizedPrecision.batch_ge_target p
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hbatch : (0 : ℝ) < batch p := by exact_mod_cast (batch p).pos
  have hω := DistributedNormalizedPrecision.compressionVariance_nonneg p hd
  have hb' : 16384 * p.σ ^ 2 * (1 + compressionVariance p) ≤ (batch p : ℝ) * (p.n * p.ε ^ 2) :=
    (div_le_iff₀ (by positivity)).mp hb
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ hn).mpr
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hbatch).mpr
  nlinarith

lemma downlink_square_scale (p : Params) :
    65536 * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 ≤ phaseScale p ^ 2 * p.n := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hs : 0 < Real.sqrt p.n := Real.sqrt_pos.mpr hn
  have hc := downlinkCost_nonneg p
  have hb := (phaseScale_bounds p).2.2.2.2.1
  have hb' : 256 * (p.d * downlinkCost p) ≤ phaseScale p * Real.sqrt p.n := by
    apply (div_le_iff₀ hs).mp
    convert hb using 1
    ring
  have hp := pow_le_pow_left₀ (show 0 ≤ 256 * (p.d * downlinkCost p) by positivity) hb' 2
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hn.le] at hp
  norm_num at hp
  nlinarith

lemma mixed_cube_scale (p : Params) :
    16777216 * ((p.d : ℝ) ^ 3 * uplinkCost p * downlinkCost p ^ 2 / p.n) ≤ phaseScale p ^ 3 := by
  let z := (p.d : ℝ) ^ 3 * uplinkCost p * downlinkCost p ^ 2 / p.n
  have hz : 0 ≤ z := by
    have hc := uplinkCost_nonneg p
    dsimp [z]
    positivity
  have hb : 256 * z ^ (1 / 3 : ℝ) ≤ phaseScale p := (phaseScale_bounds p).2.2.2.2.2.1
  have he : (z ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = z := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 3) hz (by decide)
  have hp := pow_le_pow_left₀ (show 0 ≤ 256 * z ^ (1 / 3 : ℝ) by positivity) hb 3
  rw [mul_pow, he] at hp
  norm_num at hp
  exact hp

lemma mean_consensus_small (p : Params) (hh : ∀ i, 0 < p.h i) :
    consensusFactor p / p.n ≤ 1 / 32 := by
  have ht := phaseScale_pos p hh
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast Nat.succ_le_of_lt p.n.pos
  have hs := downlink_square_scale p
  have hterm : 4 * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 / phaseScale p ^ 2 ≤ (p.n : ℝ) / 16384 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    nlinarith
  have hA := (consensusFactor_bound p hh).trans (add_le_add le_rfl hterm)
  apply (div_le_iff₀ hn).mpr
  nlinarith

lemma mixed_consensus_small (p : Params) (hd : 0 < p.d) (hh : ∀ i, 0 < p.h i) :
    compressionVariance p * consensusFactor p / p.n ≤ 1 / 2048 := by
  have ht := phaseScale_pos p hh
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hω := DistributedNormalizedPrecision.compressionVariance_nonneg p hd
  have hscale := compression_variance_scale p hd hh
  have hcube := mixed_cube_scale p
  have hc : 16777216 * (p.d : ℝ) ^ 3 * uplinkCost p * downlinkCost p ^ 2 ≤ phaseScale p ^ 3 * p.n := by
    apply (div_le_iff₀ hn).mp
    convert hcube using 1
    ring
  have hm := mul_le_mul_of_nonneg_right hscale
    (show 0 ≤ (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 by positivity)
  have hscaled : (8388608 * compressionVariance p * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2) * phaseScale p ≤
      (phaseScale p ^ 2 * p.n) * phaseScale p := by
    nlinarith
  have hcancel := (mul_le_mul_iff_left₀ ht).mp hscaled
  have hterm : 4 * compressionVariance p * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 /
      ((p.n : ℝ) * phaseScale p ^ 2) ≤ 1 / 2097152 := by
    apply (div_le_iff₀ (show 0 < (p.n : ℝ) * phaseScale p ^ 2 by positivity)).mpr
    nlinarith
  calc
    _ = (compressionVariance p / p.n) * consensusFactor p := by ring
    _ ≤ (compressionVariance p / p.n) *
        (1 / 64 + 4 * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 / phaseScale p ^ 2) :=
      mul_le_mul_of_nonneg_left (consensusFactor_bound p hh) (by positivity)
    _ = (compressionVariance p / p.n) / 64 +
        4 * compressionVariance p * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 / ((p.n : ℝ) * phaseScale p ^ 2) := by ring
    _ ≤ (1 / 128 : ℝ) / 64 + 1 / 2097152 :=
      add_le_add (div_le_div_of_nonneg_right (relative_variance_small p hd hh) (by norm_num)) hterm
    _ ≤ 1 / 2048 := by norm_num

lemma curvature_consensus_small (p : Params) (hL : 0 < p.L) (hQ : 0 ≤ p.Q) (hε : 0 < p.ε)
    (hh : ∀ i, 0 < p.h i) (hreg : p.Q * p.ε ≤ p.L ^ 2) :
    (p.Q * p.ε / p.L ^ 2) * consensusFactor p ≤ 1 := by
  have ht := phaseScale_pos p hh
  have hc := downlinkCost_nonneg p
  have hq : 0 ≤ p.Q * p.ε := mul_nonneg hQ hε.le
  have hs : Real.sqrt (p.Q * p.ε) ≤ p.L := Real.sqrt_le_iff.mpr ⟨hL.le, hreg⟩
  have hsdiv : Real.sqrt (p.Q * p.ε) / p.L ≤ 1 := (div_le_one hL).mpr hs
  have hb := (phaseScale_bounds p).2.2.2.2.2.2.2.2
  rw [min_eq_right hsdiv] at hb
  have hb' : 256 * (p.d * downlinkCost p) * Real.sqrt (p.Q * p.ε) ≤ phaseScale p * p.L := by
    apply (div_le_iff₀ hL).mp
    convert hb using 1
    ring
  have hp := pow_le_pow_left₀ (show 0 ≤ 256 * (p.d * downlinkCost p) * Real.sqrt (p.Q * p.ε) by positivity) hb' 2
  simp only [mul_pow, Real.sq_sqrt hq] at hp
  norm_num at hp
  have hterm : (p.Q * p.ε / p.L ^ 2) * (4 * (p.d : ℝ) ^ 2 * downlinkCost p ^ 2 / phaseScale p ^ 2) ≤ 1 / 16384 := by
    rw [div_mul_div_comm]
    apply (div_le_iff₀ (show 0 < p.L ^ 2 * phaseScale p ^ 2 by positivity)).mpr
    nlinarith
  have hq1 : p.Q * p.ε / p.L ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hL)).mpr hreg
  have hA := mul_le_mul_of_nonneg_left (consensusFactor_bound p hh)
    (show 0 ≤ p.Q * p.ε / p.L ^ 2 by positivity)
  rw [mul_add] at hA
  nlinarith

lemma large_curvature_full_downlink (p : Params) (hL : 0 < p.L)
    (hreg : p.L ^ 2 ≤ p.Q * p.ε) : fullDownlink p = true := by
  have hs : p.L ≤ Real.sqrt (p.Q * p.ε) := Real.le_sqrt_of_sq_le hreg
  have hsdiv : 1 ≤ Real.sqrt (p.Q * p.ε) / p.L := (le_div_iff₀ hL).mpr (by simpa using hs)
  have hb := (phaseScale_bounds p).2.2.2.2.2.2.2.2
  rw [min_eq_left hsdiv, mul_one] at hb
  have hc := downlinkCost_nonneg p
  have he : p.d * downlinkCost p ≤ phaseScale p := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    nlinarith [mul_nonneg hd hc]
  simp only [fullDownlink, decide_eq_true_eq]
  exact Or.inr he

lemma full_downlink_factor (p : Params) (hfull : fullDownlink p = true) : consensusFactor p = 1 / 64 := by
  unfold consensusFactor
  simp only [refreshPeriod, hfull, ↓reduceIte, PNat.one_coe, Nat.cast_one, sub_self, mul_zero, zero_div, add_zero]

lemma spatial_error_small (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hQ : 0 ≤ p.Q) (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    let V := stepSize p ^ 2 * consensusFactor p
    let β := Real.sqrt (2 * compressionVariance p / p.n)
    p.L * β * Real.sqrt V + min (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V) ≤ p.ε / 128 := by
  intro V β
  have hη := DistributedNormalizedPrecision.stepSize_pos p hL hε
  have hA := consensusFactor_nonneg p
  have hω := DistributedNormalizedPrecision.compressionVariance_nonneg p hd
  have hLη : p.L * stepSize p = p.ε / 128 := by
    unfold stepSize
    field_simp
  have hsqrt : Real.sqrt V = stepSize p * Real.sqrt (consensusFactor p) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hη.le]
  have hsqrtn : Real.sqrt (V / p.n) = stepSize p * Real.sqrt (consensusFactor p / p.n) := by
    have he : V / p.n = stepSize p ^ 2 * (consensusFactor p / p.n) := by dsimp [V]; ring
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hη.le]
  have hmean : Real.sqrt (consensusFactor p / p.n) ≤ 1 / 4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mean_consensus_small p hh).trans (by norm_num)
  have hcomp : β * Real.sqrt (consensusFactor p) ≤ 1 / 4 := by
    dsimp [β]
    rw [← Real.sqrt_mul (show 0 ≤ 2 * compressionVariance p / (p.n : ℝ) by positivity)]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hm := mixed_consensus_small p hd hh
    calc
      _ = 2 * (compressionVariance p * consensusFactor p / p.n) := by ring
      _ ≤ 2 * (1 / 2048 : ℝ) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ ≤ (1 / 4 : ℝ) ^ 2 := by norm_num
  have hlinear : p.L * β * Real.sqrt V ≤ p.ε / 512 := by
    calc
      _ = (p.L * stepSize p) * (β * Real.sqrt (consensusFactor p)) := by rw [hsqrt]; ring
      _ ≤ (p.ε / 128) * (1 / 4) := by
        rw [hLη]
        exact mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = _ := by ring
  by_cases hreg : p.Q * p.ε ≤ p.L ^ 2
  · have hcurv := curvature_consensus_small p hL hQ hε hh hreg
    have he : p.Q * V = (p.ε / 16384) * ((p.Q * p.ε / p.L ^ 2) * consensusFactor p) := by
      dsimp [V, stepSize]
      field_simp
      ring
    have hcurv' : p.Q * V ≤ p.ε / 16384 := by
      rw [he]
      simpa using mul_le_mul_of_nonneg_left hcurv (show 0 ≤ p.ε / 16384 by positivity)
    have hmean' : p.L * Real.sqrt (V / p.n) ≤ p.ε / 512 := by
      rw [hsqrtn, ← mul_assoc, hLη]
      have hm := mul_le_mul_of_nonneg_left hmean (show 0 ≤ p.ε / 128 by positivity)
      nlinarith
    have hmin := min_le_left (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V)
    nlinarith
  · have hfull := large_curvature_full_downlink p hL (le_of_lt (lt_of_not_ge hreg))
    have hfactor := full_downlink_factor p hfull
    have hsqrt' : Real.sqrt V = stepSize p / 8 := by
      rw [hsqrt, hfactor]
      norm_num
      ring
    have hD : p.L * Real.sqrt V = p.ε / 1024 := by
      rw [hsqrt', ← mul_div_assoc, hLη]
      ring
    have hmin := min_le_right (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V)
    nlinarith

lemma total_additive_error_small (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hQ : 0 ≤ p.Q) (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    let V := stepSize p ^ 2 * consensusFactor p
    let β := Real.sqrt (2 * compressionVariance p / p.n)
    p.L * β * Real.sqrt V + min (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V) +
      (Real.sqrt ((1 + compressionVariance p) * (p.σ ^ 2 / batch p) / p.n) +
        Real.sqrt (DistributedNormalizedEstimator.gridVariance p (config p) / p.n) +
        (p.σ ^ 2 / batch p) / (4 * clipMargin p)) ≤ p.ε / 32 := by
  intro V β
  have hs := spatial_error_small p hd hL hQ hε hh
  have hn := stochastic_norm_error p hd hε
  have hg := grid_norm_error p hd hε
  have hb := clipping_bias_small p hε
  change p.L * β * Real.sqrt V + min (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V) ≤ p.ε / 128 at hs
  linarith

lemma step_scale (p : Params) (hL : 0 < p.L) : p.L * stepSize p = p.ε / 128 := by
  unfold stepSize
  field_simp

lemma iteration_gap (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) :
    p.Δ ≤ (iterations p : ℝ) * stepSize p * p.ε / 8 := by
  have hK : 1024 * p.L * p.Δ / p.ε ^ 2 ≤ (iterations p : ℝ) := by
    change 1024 * p.L * p.Δ / p.ε ^ 2 ≤ ((max 1 ⌈1024 * p.L * p.Δ / p.ε ^ 2⌉₊ : ℕ) : ℝ)
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right 1 ⌈1024 * p.L * p.Δ / p.ε ^ (2 : ℕ)⌉₊))
  have hb := (div_le_iff₀ (sq_pos_of_pos hε)).mp hK
  have he : (iterations p : ℝ) * stepSize p * p.ε / 8 =
      ((iterations p : ℝ) * p.ε ^ 2) / (1024 * p.L) := by unfold stepSize; ring
  rw [he]
  apply (le_div_iff₀ (show 0 < 1024 * p.L by positivity)).mpr
  nlinarith

end LongTails.Proofs.DistributedNormalizedTuning
