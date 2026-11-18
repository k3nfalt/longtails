import LongTails.Proofs.DashaDistributedTuningBounds

namespace LongTails.Proofs.DashaDistributedCostBounds

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling LongTails.Algorithms.DashaCyclic
open LongTails.Algorithms.DashaDistributed LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedTrackedParameters
open DashaScalingParameters DashaDistributedSimplification DashaDistributedLogBounds DashaDistributedTuningBounds

variable {p : Params}

lemma sparse_input_le (c c₀ : Choice p) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    multiplier c₀.block * p.G / spacing p c ≤
      32 * (p.d : ℝ) ^ 2 * Real.sqrt (p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) / (c₀.block.val + 1) := by
  have hg := divide_by_spacing_le c hε p.G hG
  have he := scaled_G_eq_sqrt hG hε
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ multiplier c₀.block by unfold multiplier; positivity)
  calc
    _ ≤ multiplier c₀.block * (32 * (p.d : ℝ) * p.G / (p.ε * Real.sqrt (p.n : ℝ))) := by
      convert hm using 1
      ring
    _ = _ := by rw [show 32 * (p.d : ℝ) * p.G / (p.ε * Real.sqrt (p.n : ℝ)) =
        32 * (p.d : ℝ) * (p.G / (p.ε * Real.sqrt (p.n : ℝ))) by ring, he]; unfold multiplier; ring

lemma modular_input_le (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    modularInitialBound p c ≤ 49 * ((p.n : ℝ) * p.d * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2)) := by
  let N := 1 + min p.L p.Lhat * p.Δ / p.ε ^ 2
  have hN : 1 ≤ N := by
    dsimp [N]
    have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
    linarith
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  have hρ := spacing_pos c hε
  have hJ0 : 0 ≤ globalInitialBound p := by unfold globalInitialBound; positivity
  have hJ := globalInitialBound_scaled hL hH hΔ hG hε
  change globalInitialBound p / (p.ε * Real.sqrt (p.n : ℝ)) ≤ (3 / 2 : ℝ) * Real.sqrt N at hJ
  have hJρ : globalInitialBound p / spacing p c ≤ 48 * (p.d : ℝ) * Real.sqrt N := by
    apply (divide_by_spacing_le c hε (globalInitialBound p) hJ0).trans
    have hm := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 32 * (p.d : ℝ) by positivity)
    convert hm using 1 <;> ring
  have hrootN : Real.sqrt N ≤ N := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith)).mp
    rw [Real.sq_sqrt (by linarith)]
    nlinarith [sq_nonneg (N - 1)]
  have hrootd : Real.sqrt (p.d : ℝ) ≤ p.d := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg ((p.d : ℝ) - 1)]
  have h1 := mul_le_mul_of_nonneg_left hrootN (show 0 ≤ 48 * (p.d : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hN (show 0 ≤ (p.d : ℝ) by positivity)
  have hinner : globalInitialBound p / spacing p c + Real.sqrt (p.d : ℝ) ≤ 49 * (p.d : ℝ) * N := by
    nlinarith only [hJρ, h1, h2, hrootd]
  have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ (p.n : ℝ) by positivity)
  unfold modularInitialBound
  change _ ≤ 49 * ((p.n : ℝ) * p.d * N)
  convert hm using 1 <;> field_simp

lemma modular_bits_le (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hΔ : 0 ≤ p.Δ) (hG : 0 ≤ p.G) (hε : 0 < p.ε) :
    (initialBits p (trackedConfig p c none true) : ℝ) ≤
      16 * (p.d : ℝ) * modularLogScale ((p.n : ℝ) * p.d) (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2) := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  have hN : 1 ≤ 1 + min p.L p.Lhat * p.Δ / p.ε ^ 2 := by
    have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
    linarith
  have ht : 1 ≤ (p.n : ℝ) * p.d * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2) := by
    nlinarith [mul_le_mul hn hd (by norm_num) (by positivity),
      mul_le_mul_of_nonneg_left hN (show 0 ≤ (p.n : ℝ) * p.d by positivity)]
  have hρ := spacing_pos c hε
  have hu : 0 ≤ modularInitialBound p c := by unfold modularInitialBound globalInitialBound; positivity
  have hb := dense_width_le _ _ ht hu (modular_input_le c hL hH hΔ hG hε)
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (p.d : ℝ) by positivity)
  simpa [initialBits, trackedConfig, config, modularLogScale, Nat.cast_mul, Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using hm

lemma sparse_bits_le_of_word (c c₀ : Choice p) (modular : Bool) (W : ℝ)
    (hword : (c₀.precision : ℝ) + Nat.size (Nat.size ⌈multiplier c₀.block * p.G / spacing p c⌉₊) + 3 ≤ W) :
    (initialBits p (trackedConfig p c (some c₀) modular) : ℝ) ≤ (c₀.block.val + 1) * W := by
  have hm := mul_le_mul_of_nonneg_left hword (show (0 : ℝ) ≤ c₀.block.val + 1 by positivity)
  simpa [initialBits, trackedConfig, config] using hm

lemma sparse_bits_small_le (c c₀ : Choice p) (modular : Bool) (N : ℝ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) (hN : 1 ≤ N) (hs : c₀.precision = 0)
    (hinput : (p.d : ℝ) ^ 2 * Real.sqrt (p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) / (c₀.block.val + 1) ≤ p.d) :
    (initialBits p (trackedConfig p c (some c₀) modular) : ℝ) ≤
      16 * (c₀.block.val + 1) * initialLogScale p.d N := by
  have hρ := spacing_pos c hε
  have hu : 0 ≤ multiplier c₀.block * p.G / spacing p c := by unfold multiplier; positivity
  have hbound : multiplier c₀.block * p.G / spacing p c ≤ 32 * (p.d : ℝ) := by
    have hb := sparse_input_le c c₀ hG hε
    have hm := mul_le_mul_of_nonneg_left hinput (show (0 : ℝ) ≤ 32 by norm_num)
    apply hb.trans
    convert hm using 1
    ring
  have hw := float_word_small_le (p.d : ℝ) N _ (by exact_mod_cast p.d.pos) hN hu hbound
  have hb := sparse_bits_le_of_word c c₀ modular (16 * initialLogScale p.d N) (by simpa [hs] using hw)
  convert hb using 1
  ring

lemma sparse_bits_precise_le (c c₀ : Choice p) (modular : Bool) (N B : ℝ)
    (hG : 0 ≤ p.G) (hε : 0 < p.ε) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hk : c₀.block.val + 1 = p.d)
    (hs : c₀.precision = Nat.size ⌈p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2) * B⌉₊) :
    (initialBits p (trackedConfig p c (some c₀) modular) : ℝ) +
      2 * (p.d : ℝ) * Real.log (1 + p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)) ≤
      32 * (p.d : ℝ) * (initialLogScale p.d N + Real.log (1 + p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2) * B)) := by
  let Z := p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hρ := spacing_pos c hε
  have hkR : (c₀.block.val : ℝ) + 1 = p.d := by exact_mod_cast hk
  have hu : 0 ≤ multiplier c₀.block * p.G / spacing p c := by unfold multiplier; positivity
  have hbound : multiplier c₀.block * p.G / spacing p c ≤ 32 * (p.d : ℝ) * Real.sqrt Z := by
    have hb := sparse_input_le c c₀ hG hε
    rw [hkR] at hb
    convert hb using 1
    dsimp [Z]
    field_simp
  have hw := float_word_precise_le (p.d : ℝ) N Z B _ (by exact_mod_cast p.d.pos) hN hZ hB hu hbound
  have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ (p.d : ℝ) by positivity)
  have he : (initialBits p (trackedConfig p c (some c₀) modular) : ℝ) =
      (p.d : ℝ) * ((c₀.precision : ℝ) + Nat.size (Nat.size ⌈multiplier c₀.block * p.G / spacing p c⌉₊) + 3) := by
    simp [initialBits, trackedConfig, config, hkR]
  rw [he, hs]
  dsimp [Z] at hm
  nlinarith only [hm]

lemma tracked_time_le (c : Choice p) (initializer : Option (Choice p)) (modular : Bool) :
    (timeBudget p (trackedConfig p c initializer modular) : ℝ) ≤
      (roundCount p c initializer : ℝ) * ((computationTime p : ℝ) + p.l + 64 * p.b) +
        (p.b : ℝ) * ((initialBits p (trackedConfig p c initializer modular) : ℝ) +
          (roundCount p c initializer : ℝ) * (roundBits p (trackedConfig p c initializer modular) : ℝ)) := by
  rw [DashaDistributedBudget.timeBudget_expanded]
  simp only [trackedConfig, config, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    add_zero]
  have hsub : (((roundCount p c initializer : ℕ) - 1 : ℕ) : ℝ) ≤ (roundCount p c initializer : ℝ) := by
    exact_mod_cast Nat.sub_le (roundCount p c initializer : ℕ) 1
  gcongr

end LongTails.Proofs.DashaDistributedCostBounds
