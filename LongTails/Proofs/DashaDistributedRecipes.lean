import LongTails.Proofs.DashaDistributedCostBounds

namespace LongTails.Proofs.DashaDistributedRecipes

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling LongTails.Algorithms.DashaCyclic
open LongTails.Algorithms.DashaDistributed LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaDistributedTrackedParameters
open DashaScalingParameters DashaDistributedSimplification DashaDistributedLogBounds
open DashaDistributedTuningBounds DashaDistributedCostBounds

noncomputable def workScale (p : Params) : ℝ := 1 + min p.L p.Lhat * p.Δ / p.ε ^ 2
noncomputable def heterogeneityScale (p : Params) : ℝ := p.Lhat * p.Δ / (p.ε ^ 2 * Real.sqrt (p.n : ℝ))
noncomputable def noiseScale (p : Params) : ℝ := p.G ^ 2 / ((p.n : ℝ) * p.ε ^ 2)
noncomputable def packetScale (p : Params) : ℝ := logScale ((p.n : ℝ) * p.d) (workScale p) (heterogeneityScale p)
noncomputable def floatScale (p : Params) : ℝ := initialLogScale p.d (workScale p)
noncomputable def denseScale (p : Params) : ℝ := modularLogScale ((p.n : ℝ) * p.d) (workScale p)

variable {p : Params}

lemma scales_valid (hp : spec.valid p) :
    1 ≤ workScale p ∧ 0 ≤ heterogeneityScale p ∧ 0 ≤ noiseScale p ∧ 2 ≤ packetScale p ∧
      1 ≤ floatScale p ∧ floatScale p ≤ packetScale p ∧ floatScale p ≤ denseScale p := by
  rcases hp with ⟨_, hL, hH, hΔ, _, hε⟩
  have hN : 1 ≤ workScale p := by
    unfold workScale
    have ha : 0 ≤ min p.L p.Lhat * p.Δ / p.ε ^ 2 := by positivity
    linarith
  have hX : 0 ≤ heterogeneityScale p := by unfold heterogeneityScale; positivity
  have hZ : 0 ≤ noiseScale p := by unfold noiseScale; positivity
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  have hwd : (p.d : ℝ) ≤ (p.n : ℝ) * p.d := by nlinarith
  have hb := two_le_logScale ((p.n : ℝ) * p.d) (workScale p) (heterogeneityScale p) (hd.trans hwd) hN hX
  have hi := initialLogScale_bounds ((p.n : ℝ) * p.d) p.d (workScale p) (heterogeneityScale p) hd hwd hN hX
  exact ⟨hN, hX, hZ, hb, hi⟩

lemma exists_small_recipe (hp : spec.valid p)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (hXN : heterogeneityScale p ≤ workScale p)
    (hsmall : noiseScale p * packetScale p ≤ floatScale p) :
    ∃ c c₀ : Choice p,
      (timeBudget p (trackedConfig p c (some c₀) false) : ℝ) ≤
        32768 * (workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
          (p.b : ℝ) * (packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) +
            (p.d : ℝ) * Real.sqrt (noiseScale p * packetScale p * floatScale p))) := by
  obtain ⟨hN, hX, hZ, hB, hL, hLB, _⟩ := scales_valid hp
  obtain ⟨_, hLp, hH, hΔ, hG, hε⟩ := hp
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  have hN0 : 0 < workScale p := by linarith
  have hB0 : 0 < packetScale p := by linarith
  have hL0 : 0 < floatScale p := by linarith
  obtain ⟨i₀, hi₀, hi₀up⟩ := exists_block_between p.d
    ((p.d : ℝ) * Real.sqrt (noiseScale p * packetScale p / floatScale p)) (by positivity)
  have hroot := sqrt_ratio_le_one (noiseScale p * packetScale p) (floatScale p) (by positivity) hL0 hsmall
  have ht : (p.d : ℝ) * Real.sqrt (noiseScale p * packetScale p / floatScale p) ≤ p.d := by
    nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ (p.d : ℝ) by positivity)]
  rw [min_eq_right ht] at hi₀
  let c₀ : Choice p := ⟨i₀, 0⟩
  obtain ⟨i, hi, hiup⟩ := exists_block_between p.d
    (((p.d : ℝ) * heterogeneityScale p + (p.d : ℝ) ^ 2 * noiseScale p / (i₀.val + 1)) / workScale p) (by positivity)
  let c : Choice p := ⟨i, 0⟩
  let K : ℝ := sparseIterations p c c₀
  have hKraw := sparseIterations_le_multipliers c c₀ hLp hH hΔ hε
  have hK : K ≤ 160 * (workScale p +
      ((p.d : ℝ) * heterogeneityScale p + (p.d : ℝ) ^ 2 * noiseScale p / (i₀.val + 1)) / (i.val + 1)) := by
    convert hKraw using 1
    dsimp [workScale, heterogeneityScale, noiseScale, multiplier, c, c₀, K]
    ring
  obtain ⟨hK480, hKB, hinit, hinput⟩ := small_recipe_bounds (p.d : ℝ) (workScale p)
    (heterogeneityScale p) (noiseScale p) (packetScale p) (floatScale p) (i₀.val + 1) (i.val + 1) K
    hd hN hX hXN hZ hB hL hLB hsmall (by positivity) (by positivity) hi₀ hi₀up hi hiup hK
  have hK1 : 1 ≤ K := by dsimp [K]; exact_mod_cast (sparseIterations p c c₀).pos
  have hw : (1 : ℝ) ≤ (p.n : ℝ) * p.d := by
    have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
    nlinarith
  have hlogK := log_iterations_le_scale ((p.n : ℝ) * p.d) (workScale p) (heterogeneityScale p) K hw hN hX (by linarith) hK480
  have hpacket := tracked_roundBits_le_scale c (some c₀) false (noiseScale p) hZ hLp hH hΔ hG hε hgap
    (fun _ _ => (scaled_G_eq_sqrt hG hε).le)
  norm_num only [show c.precision = 0 from rfl, Nat.cast_zero] at hpacket
  change _ ≤ (i.val + 1) * (9 + 2 * Real.log (1 + K) + 6 * packetScale p + 2 * Real.log (1 + Real.log (1 + noiseScale p))) at hpacket
  have hZ1 : noiseScale p ≤ 1 := by
    have h := (le_div_iff₀ hB0).mpr (hsmall.trans hLB)
    simpa only [div_self hB0.ne'] using h
  have htotal := packet_total_small_noise_le _ (i.val + 1) K (packetScale p) 0 (noiseScale p)
    (by positivity) hK1 hB (by linarith) hlogK hZ hZ1 (by simpa only [zero_add] using hpacket)
  have hbits := sparse_bits_small_le c c₀ false (workScale p) hG hε hN rfl hinput
  have htime := tracked_time_le c (some c₀) false
  change _ ≤ K * ((computationTime p : ℝ) + p.l + 64 * p.b) +
    (p.b : ℝ) * ((initialBits p (trackedConfig p c (some c₀) false) : ℝ) +
      K * (roundBits p (trackedConfig p c (some c₀) false) : ℝ)) at htime
  change (initialBits p (trackedConfig p c (some c₀) false) : ℝ) ≤ 16 * (i₀.val + 1) * floatScale p at hbits
  let Q := packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) +
    (p.d : ℝ) * Real.sqrt (noiseScale p * packetScale p * floatScale p)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hBN : packetScale p ≤ packetScale p * workScale p := by nlinarith [mul_le_mul_of_nonneg_left hN hB0.le]
  have hsum : (initialBits p (trackedConfig p c (some c₀) false) : ℝ) +
      K * (roundBits p (trackedConfig p c (some c₀) false) : ℝ) ≤ 32768 * Q := by
    dsimp [Q]
    have hNX : 0 ≤ (p.d : ℝ) * heterogeneityScale p * packetScale p := by positivity
    nlinarith only [hbits, hinit, htotal, hKB, hBN, hQ, hNX]
  have hb := mul_le_mul_of_nonneg_left hsum p.b.coe_nonneg
  have htK := mul_le_mul_of_nonneg_right hK480
    (show 0 ≤ (computationTime p : ℝ) + p.l + 64 * p.b by positivity)
  refine ⟨c, c₀, ?_⟩
  change _ ≤ 32768 * (workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) + (p.b : ℝ) * Q)
  have hbase : 0 ≤ workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) := by positivity
  nlinarith only [htime, hb, htK, hbase]

lemma tracked_packets_le (hp : spec.valid p)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (c : Choice p) (initializer : Option (Choice p)) (modular : Bool) (Z : ℝ) (hZ : 0 ≤ Z)
    (hnoise : ∀ c₀, initializer = some c₀ → p.G / (p.ε * Real.sqrt (p.n : ℝ)) ≤ Real.sqrt Z)
    (hK : (roundCount p c initializer : ℝ) ≤ 480 * workScale p)
    (hr : (c.precision : ℝ) ≤ 2 * packetScale p) :
    (roundCount p c initializer : ℝ) * (roundBits p (trackedConfig p c initializer modular) : ℝ) ≤
      40 * (c.block.val + 1) * (roundCount p c initializer : ℝ) * packetScale p +
        2 * (p.d : ℝ) * Real.log (1 + Z) := by
  obtain ⟨hN, hX, _, hB, _⟩ := scales_valid hp
  obtain ⟨_, hL, hH, hΔ, hG, hε⟩ := hp
  have hK1 : (1 : ℝ) ≤ roundCount p c initializer := by exact_mod_cast (roundCount p c initializer).pos
  have hw : (1 : ℝ) ≤ (p.n : ℝ) * p.d := by
    have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
    have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
    nlinarith
  have hlog := log_iterations_le_scale ((p.n : ℝ) * p.d) (workScale p) (heterogeneityScale p)
    (roundCount p c initializer : ℝ) hw hN hX (by linarith) hK
  have hpacket := tracked_roundBits_le_scale c initializer modular Z hZ hL hH hΔ hG hε hgap hnoise
  exact packet_total_le _ (c.block.val + 1) (p.d : ℝ) (roundCount p c initializer : ℝ)
    (packetScale p) c.precision Z (by positivity) (by exact_mod_cast Nat.succ_le_of_lt c.block.isLt)
    hK1 hB hr hlog hZ hpacket

lemma full_float_cost_le (hp : spec.valid p)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (c c₀ : Choice p) (B M : ℝ) (hB : 1 ≤ B) (hk : c₀.block.val + 1 = p.d)
    (hs : c₀.precision = Nat.size ⌈noiseScale p * B⌉₊)
    (hK : (sparseIterations p c c₀ : ℝ) ≤ 480 * workScale p)
    (hKB : (c.block.val + 1) * (sparseIterations p c c₀ : ℝ) * packetScale p ≤ 480 * M)
    (hr : (c.precision : ℝ) ≤ 2 * packetScale p) :
    (timeBudget p (trackedConfig p c (some c₀) false) : ℝ) ≤
      480 * workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
        (p.b : ℝ) * (19200 * M + 32 * (p.d : ℝ) * (floatScale p + Real.log (1 + noiseScale p * B))) := by
  obtain ⟨hN, _, hZ, _⟩ := scales_valid hp
  have hG := hp.2.2.2.2.1
  have hε := hp.2.2.2.2.2
  have hpacket := tracked_packets_le hp hgap c (some c₀) false (noiseScale p) hZ
    (fun _ _ => (scaled_G_eq_sqrt hG hε).le) hK hr
  have hbits := sparse_bits_precise_le c c₀ false (workScale p) B hG hε hN hB hk hs
  have htime := tracked_time_le c (some c₀) false
  have hsum : (initialBits p (trackedConfig p c (some c₀) false) : ℝ) +
      (sparseIterations p c c₀ : ℝ) * (roundBits p (trackedConfig p c (some c₀) false) : ℝ) ≤
      19200 * M + 32 * (p.d : ℝ) * (floatScale p + Real.log (1 + noiseScale p * B)) := by
    change (sparseIterations p c c₀ : ℝ) * (roundBits p (trackedConfig p c (some c₀) false) : ℝ) ≤
      40 * (c.block.val + 1) * (sparseIterations p c c₀ : ℝ) * packetScale p +
      2 * (p.d : ℝ) * Real.log (1 + noiseScale p) at hpacket
    change (initialBits p (trackedConfig p c (some c₀) false) : ℝ) + 2 * (p.d : ℝ) * Real.log (1 + noiseScale p) ≤
      32 * (p.d : ℝ) * (floatScale p + Real.log (1 + noiseScale p * B)) at hbits
    nlinarith only [hpacket, hbits, hKB]
  have hb := mul_le_mul_of_nonneg_left hsum p.b.coe_nonneg
  have htK := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ (computationTime p : ℝ) + p.l + 64 * p.b by positivity)
  change (timeBudget p (trackedConfig p c (some c₀) false) : ℝ) ≤
    (sparseIterations p c c₀ : ℝ) * ((computationTime p : ℝ) + p.l + 64 * p.b) +
      (p.b : ℝ) * ((initialBits p (trackedConfig p c (some c₀) false) : ℝ) +
        (sparseIterations p c c₀ : ℝ) * (roundBits p (trackedConfig p c (some c₀) false) : ℝ)) at htime
  nlinarith only [htime, hb, htK]

lemma dense_cost_le (hp : spec.valid p)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (c : Choice p) (M : ℝ)
    (hK : (iterations p c : ℝ) ≤ 480 * workScale p)
    (hKB : (c.block.val + 1) * (iterations p c : ℝ) * packetScale p ≤ 480 * M)
    (hr : (c.precision : ℝ) ≤ 2 * packetScale p) :
    (timeBudget p (trackedConfig p c none true) : ℝ) ≤
      480 * workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
        (p.b : ℝ) * (19200 * M + 16 * (p.d : ℝ) * denseScale p) := by
  have hpacket := tracked_packets_le hp hgap c none true 0 (by norm_num)
    (by intro _ h; cases h) hK hr
  obtain ⟨_, hL, hH, hΔ, hG, hε⟩ := hp
  have hbits := modular_bits_le c hL hH hΔ hG hε
  have htime := tracked_time_le c none true
  simp only [add_zero, Real.log_one, mul_zero] at hpacket
  change (iterations p c : ℝ) * (roundBits p (trackedConfig p c none true) : ℝ) ≤
    40 * (c.block.val + 1) * (iterations p c : ℝ) * packetScale p at hpacket
  change (initialBits p (trackedConfig p c none true) : ℝ) ≤ 16 * (p.d : ℝ) * denseScale p at hbits
  have hsum : (initialBits p (trackedConfig p c none true) : ℝ) +
      (iterations p c : ℝ) * (roundBits p (trackedConfig p c none true) : ℝ) ≤
      19200 * M + 16 * (p.d : ℝ) * denseScale p := by nlinarith only [hpacket, hbits, hKB]
  have hb := mul_le_mul_of_nonneg_left hsum p.b.coe_nonneg
  have htK := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ (computationTime p : ℝ) + p.l + 64 * p.b by positivity)
  change (timeBudget p (trackedConfig p c none true) : ℝ) ≤
    (iterations p c : ℝ) * ((computationTime p : ℝ) + p.l + 64 * p.b) +
      (p.b : ℝ) * ((initialBits p (trackedConfig p c none true) : ℝ) +
        (iterations p c : ℝ) * (roundBits p (trackedConfig p c none true) : ℝ)) at htime
  nlinarith only [htime, hb, htK]

lemma exists_full_recipe (hp : spec.valid p)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    ∃ (c : Choice p) (initializer : Option (Choice p)) (modular : Bool),
      (timeBudget p (trackedConfig p c initializer modular) : ℝ) ≤
        32768 * (workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
          (p.b : ℝ) * p.d * (workScale p * packetScale p + min (Real.log (1 + noiseScale p)) (denseScale p))) := by
  obtain ⟨hN, hX, hZ, hB, hL, hLB, hLU⟩ := scales_valid hp
  have hLp := hp.2.1
  have hH := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hN0 : 0 < workScale p := by linarith
  have hB0 : 0 ≤ packetScale p := by linarith
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.pos
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  let i : Fin p.d := ⟨(p.d : ℕ) - 1, by have h := p.d.pos; omega⟩
  have hi : i.val + 1 = p.d := by dsimp [i]; have h := p.d.pos; omega
  have hiR : (i.val : ℝ) + 1 = p.d := by exact_mod_cast hi
  let c : Choice p := ⟨i, Nat.size ⌈heterogeneityScale p / workScale p⌉₊⟩
  let c₀ : Choice p := ⟨i, Nat.size ⌈noiseScale p⌉₊⟩
  have hc : c.block.val + 1 = p.d := hi
  have hc₀ : c₀.block.val + 1 = p.d := hi
  have hpow := two_pow_size_ceil_ge (heterogeneityScale p / workScale p)
  have hXdiv : heterogeneityScale p / (2 : ℝ) ^ c.precision ≤ workScale p := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_le_iff₀ hN0).mp hpow
    change heterogeneityScale p ≤ _
    nlinarith only [hh]
  have hZdiv : noiseScale p / (4 : ℝ) ^ c₀.precision ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul] using four_pow_size_ceil_ge (noiseScale p)
  have hKraw := full_iterations_le c c₀ hc hc₀ hLp hH hΔ
  have hKr : (sparseIterations p c c₀ : ℝ) ≤
      128 * (workScale p + heterogeneityScale p / (2 : ℝ) ^ c.precision + noiseScale p / (4 : ℝ) ^ c₀.precision) := by
    convert hKraw using 1
    dsimp [workScale, heterogeneityScale, noiseScale]
    ring
  have hK : (sparseIterations p c c₀ : ℝ) ≤ 480 * workScale p := by linarith
  have hKB : (c.block.val + 1) * (sparseIterations p c c₀ : ℝ) * packetScale p ≤
      480 * ((p.d : ℝ) * workScale p * packetScale p) := by
    have hm := mul_le_mul_of_nonneg_left hK (show 0 ≤ (p.d : ℝ) * packetScale p by positivity)
    change ((i.val : ℝ) + 1) * (sparseIterations p c c₀ : ℝ) * packetScale p ≤ _
    rw [hiR]
    nlinarith only [hm]
  have hr : (c.precision : ℝ) ≤ 2 * packetScale p :=
    precision_le_logScale ((p.n : ℝ) * p.d) (workScale p) (heterogeneityScale p) (by nlinarith) hN hX
  have hlog0 : 0 ≤ Real.log (1 + noiseScale p) := Real.log_nonneg (by linarith)
  have hU0 : 0 ≤ denseScale p := by linarith
  have hNB : packetScale p ≤ workScale p * packetScale p := by nlinarith [mul_le_mul_of_nonneg_right hN hB0]
  have hbase : 0 ≤ workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) := by positivity
  by_cases hchoose : Real.log (1 + noiseScale p) ≤ denseScale p
  · have hb := full_float_cost_le hp hgap c c₀ 1 ((p.d : ℝ) * workScale p * packetScale p)
      (by norm_num) hc₀ (by simp [c₀]) hK hKB hr
    simp only [mul_one] at hb
    have hBL := mul_le_mul_of_nonneg_left (hLB.trans hNB) (show 0 ≤ (p.d : ℝ) by positivity)
    have hcomm : 19200 * ((p.d : ℝ) * workScale p * packetScale p) +
        32 * (p.d : ℝ) * (floatScale p + Real.log (1 + noiseScale p)) ≤
        32768 * (p.d : ℝ) * (workScale p * packetScale p + Real.log (1 + noiseScale p)) := by
      have h1 : 0 ≤ (p.d : ℝ) * workScale p * packetScale p := by positivity
      have h2 : 0 ≤ (p.d : ℝ) * Real.log (1 + noiseScale p) := by positivity
      nlinarith only [hBL, h1, h2]
    have hm := mul_le_mul_of_nonneg_left hcomm p.b.coe_nonneg
    refine ⟨c, some c₀, false, ?_⟩
    rw [min_eq_left hchoose]
    nlinarith only [hb, hm, hbase]
  · have hmono : (iterations p c : ℝ) ≤ (sparseIterations p c c₀ : ℝ) := by
      exact_mod_cast iterations_le_sparseIterations c c₀
    have hKd := hmono.trans hK
    have hKBd : (c.block.val + 1) * (iterations p c : ℝ) * packetScale p ≤
        480 * ((p.d : ℝ) * workScale p * packetScale p) := by
      have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ (c.block.val + 1) * packetScale p by positivity)
      nlinarith only [hm, hKB]
    have hb := dense_cost_le hp hgap c ((p.d : ℝ) * workScale p * packetScale p) hKd hKBd hr
    have hcomm : 19200 * ((p.d : ℝ) * workScale p * packetScale p) + 16 * (p.d : ℝ) * denseScale p ≤
        32768 * (p.d : ℝ) * (workScale p * packetScale p + denseScale p) := by
      have h1 : 0 ≤ (p.d : ℝ) * workScale p * packetScale p := by positivity
      have h2 : 0 ≤ (p.d : ℝ) * denseScale p := by positivity
      nlinarith only [h1, h2]
    have hm := mul_le_mul_of_nonneg_left hcomm p.b.coe_nonneg
    refine ⟨c, none, true, ?_⟩
    rw [min_eq_right (le_of_not_ge hchoose)]
    nlinarith only [hb, hm, hbase]

lemma exists_mixed_recipe (hp : spec.valid p)
    (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (hXN : heterogeneityScale p ≤ workScale p) :
    ∃ (c : Choice p) (initializer : Option (Choice p)) (modular : Bool),
      (timeBudget p (trackedConfig p c initializer modular) : ℝ) ≤
        32768 * (workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
          (p.b : ℝ) * (packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) +
            (p.d : ℝ) * min (floatScale p + Real.log (1 + noiseScale p * packetScale p)) (denseScale p))) := by
  obtain ⟨hN, hX, hZ, hB, hL, hLB, hLU⟩ := scales_valid hp
  have hLp := hp.2.1
  have hH := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hN0 : 0 < workScale p := by linarith
  have hB0 : 0 < packetScale p := by linarith
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast p.d.pos
  let i₀ : Fin p.d := ⟨(p.d : ℕ) - 1, by have h := p.d.pos; omega⟩
  have hi₀ : i₀.val + 1 = p.d := by dsimp [i₀]; have h := p.d.pos; omega
  let c₀ : Choice p := ⟨i₀, Nat.size ⌈noiseScale p * packetScale p⌉₊⟩
  obtain ⟨i, hi, hiup⟩ := exists_block_between p.d
    (max ((p.d : ℝ) * heterogeneityScale p / workScale p) ((p.d : ℝ) / (workScale p * packetScale p))) (by positivity)
  have ht₁ : (p.d : ℝ) * heterogeneityScale p / workScale p ≤ p.d := by
    apply (div_le_iff₀ hN0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hXN (show 0 ≤ (p.d : ℝ) by positivity)]
  have ht₂ : (p.d : ℝ) / (workScale p * packetScale p) ≤ p.d := by
    apply (div_le_iff₀ (mul_pos hN0 hB0)).mpr
    have hNB : 1 ≤ workScale p * packetScale p := by nlinarith [mul_le_mul_of_nonneg_left hB hN0.le]
    nlinarith [mul_le_mul_of_nonneg_left hNB (show 0 ≤ (p.d : ℝ) by positivity)]
  rw [min_eq_right (max_le ht₁ ht₂)] at hi
  have hiX := (le_max_left _ _).trans hi
  have hiB := (le_max_right _ _).trans hi
  have hiup' : (i.val : ℝ) + 1 ≤ 1 + (p.d : ℝ) * heterogeneityScale p / workScale p +
      (p.d : ℝ) / (workScale p * packetScale p) := by
    have hmax : max ((p.d : ℝ) * heterogeneityScale p / workScale p) ((p.d : ℝ) / (workScale p * packetScale p)) ≤
        (p.d : ℝ) * heterogeneityScale p / workScale p + (p.d : ℝ) / (workScale p * packetScale p) :=
      max_le (by have h : 0 ≤ (p.d : ℝ) / (workScale p * packetScale p) := by positivity
                 linarith)
        (by have h : 0 ≤ (p.d : ℝ) * heterogeneityScale p / workScale p := by positivity
            linarith)
    linarith
  let c : Choice p := ⟨i, 0⟩
  let Q : ℝ := (4 : ℝ) ^ c₀.precision
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQZ : noiseScale p * packetScale p ≤ Q := four_pow_size_ceil_ge _
  have hKraw := full_initial_iterations_le c c₀ hi₀ hLp hH hΔ
  have hKr : (sparseIterations p c c₀ : ℝ) ≤ 160 * (workScale p +
      (p.d : ℝ) * heterogeneityScale p / (i.val + 1) + (p.d : ℝ) * noiseScale p / ((i.val + 1) * Q)) := by
    convert hKraw using 1
    dsimp [workScale, heterogeneityScale, noiseScale, multiplier, c, Q]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  obtain ⟨hK, hKB⟩ := mixed_recipe_bounds (p.d : ℝ) (workScale p) (heterogeneityScale p) (noiseScale p)
    (packetScale p) Q (i.val + 1) (sparseIterations p c c₀ : ℝ) (by positivity) hN hX hZ hB hQ hQZ
    (by positivity) hiX hiB hiup' hKr
  have hr : (c.precision : ℝ) ≤ 2 * packetScale p := by
    simpa only [show c.precision = 0 from rfl, Nat.cast_zero] using (show (0 : ℝ) ≤ 2 * packetScale p by positivity)
  have hF : 1 ≤ floatScale p + Real.log (1 + noiseScale p * packetScale p) := by
    have hlog : 0 ≤ Real.log (1 + noiseScale p * packetScale p) := Real.log_nonneg (by nlinarith)
    linarith
  have hU : 1 ≤ denseScale p := hL.trans hLU
  have hbase : 0 ≤ workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) := by positivity
  have hmain : 0 ≤ workScale p * packetScale p + (p.d : ℝ) * heterogeneityScale p * packetScale p := by positivity
  by_cases hchoose : floatScale p + Real.log (1 + noiseScale p * packetScale p) ≤ denseScale p
  · have hb := full_float_cost_le hp hgap c c₀ (packetScale p)
      (workScale p * packetScale p + (p.d : ℝ) * heterogeneityScale p * packetScale p + p.d)
      (by linarith) hi₀ rfl hK hKB hr
    have hinit := mul_le_mul_of_nonneg_left hF (show 0 ≤ (p.d : ℝ) by positivity)
    have hcomm : 19200 * (workScale p * packetScale p + (p.d : ℝ) * heterogeneityScale p * packetScale p + p.d) +
        32 * (p.d : ℝ) * (floatScale p + Real.log (1 + noiseScale p * packetScale p)) ≤
        32768 * (packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) +
          (p.d : ℝ) * (floatScale p + Real.log (1 + noiseScale p * packetScale p))) := by
      nlinarith only [hinit, hmain, hd]
    have hm := mul_le_mul_of_nonneg_left hcomm p.b.coe_nonneg
    refine ⟨c, some c₀, false, ?_⟩
    rw [min_eq_left hchoose]
    nlinarith only [hb, hm, hbase]
  · have hmono : (iterations p c : ℝ) ≤ (sparseIterations p c c₀ : ℝ) := by
      exact_mod_cast iterations_le_sparseIterations c c₀
    have hKBd : (c.block.val + 1) * (iterations p c : ℝ) * packetScale p ≤
        480 * (workScale p * packetScale p + (p.d : ℝ) * heterogeneityScale p * packetScale p + p.d) := by
      have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ (c.block.val + 1) * packetScale p by positivity)
      nlinarith only [hm, hKB]
    have hb := dense_cost_le hp hgap c
      (workScale p * packetScale p + (p.d : ℝ) * heterogeneityScale p * packetScale p + p.d)
      (hmono.trans hK) hKBd hr
    have hinit := mul_le_mul_of_nonneg_left hU (show 0 ≤ (p.d : ℝ) by positivity)
    have hcomm : 19200 * (workScale p * packetScale p + (p.d : ℝ) * heterogeneityScale p * packetScale p + p.d) +
        16 * (p.d : ℝ) * denseScale p ≤
        32768 * (packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) + (p.d : ℝ) * denseScale p) := by
      nlinarith only [hinit, hmain, hd]
    have hm := mul_le_mul_of_nonneg_left hcomm p.b.coe_nonneg
    refine ⟨c, none, true, ?_⟩
    rw [min_eq_right (le_of_not_ge hchoose)]
    nlinarith only [hb, hm, hbase]

noncomputable def rawTimeBound (p : Params) : ℝ :=
  workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
    (p.b : ℝ) * (packetScale p * (workScale p + (p.d : ℝ) * min (heterogeneityScale p) (workScale p)) +
      (p.d : ℝ) * initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p))

lemma initialCharge_nonneg (hp : spec.valid p) :
    0 ≤ initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p) := by
  obtain ⟨_, _, hZ, hB, hL, _, hLU⟩ := scales_valid hp
  have hlog : 0 ≤ Real.log (1 + noiseScale p * packetScale p) := Real.log_nonneg (by nlinarith)
  unfold initialCharge
  exact le_min (Real.sqrt_nonneg _) (le_min (by linarith) (by linarith))

lemma rawTimeBound_nonneg (hp : spec.valid p) : 0 ≤ rawTimeBound p := by
  obtain ⟨hN, hX, _, hB, _⟩ := scales_valid hp
  have hi := initialCharge_nonneg hp
  unfold rawTimeBound
  positivity

lemma exists_recipe (hp : spec.valid p) (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    ∃ (c : Choice p) (initializer : Option (Choice p)) (modular : Bool),
      (timeBudget p (trackedConfig p c initializer modular) : ℝ) ≤ 98304 * rawTimeBound p := by
  obtain ⟨hN, hX, hZ, hB, hL, hLB, hLU⟩ := scales_valid hp
  have hi := initialCharge_nonneg hp
  have hraw := rawTimeBound_nonneg hp
  have ht : 0 ≤ workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) := by positivity
  have hmain : 0 ≤ (p.b : ℝ) * packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) := by positivity
  by_cases hXN : heterogeneityScale p ≤ workScale p
  · by_cases hsmall : noiseScale p * packetScale p ≤ floatScale p
    · obtain ⟨c, c₀, hb⟩ := exists_small_recipe hp hgap hXN hsmall
      have he := initialCharge_small (packetScale p) (floatScale p) (denseScale p) (noiseScale p)
        (by linarith) (by linarith) hLU hZ hsmall
      have heq : rawTimeBound p = workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
          (p.b : ℝ) * (packetScale p * (workScale p + (p.d : ℝ) * heterogeneityScale p) +
            (p.d : ℝ) * Real.sqrt (noiseScale p * packetScale p * floatScale p)) := by
        unfold rawTimeBound
        rw [min_eq_left hXN, he]
      rw [← heq] at hb
      exact ⟨c, some c₀, false, hb.trans (by nlinarith only [hraw])⟩
    · obtain ⟨c, initializer, modular, hb⟩ := exists_mixed_recipe hp hgap hXN
      have hi3 := initialCharge_large (packetScale p) (floatScale p) (denseScale p) (noiseScale p)
        (by linarith) hL (by linarith) hZ (le_of_not_ge hsmall)
      have hm := mul_le_mul_of_nonneg_left hi3 (show 0 ≤ (p.b : ℝ) * p.d by positivity)
      refine ⟨c, initializer, modular, ?_⟩
      unfold rawTimeBound
      rw [min_eq_left hXN]
      nlinarith only [hb, hm, ht, hmain]
  · obtain ⟨c, initializer, modular, hb⟩ := exists_full_recipe hp hgap
    have hi2 := initialCharge_high (packetScale p) (floatScale p) (denseScale p) (noiseScale p)
      (by linarith) hL (by linarith) hZ
    have hm := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ (p.b : ℝ) * p.d by positivity)
    have hbase : 0 ≤ (p.b : ℝ) * packetScale p * workScale p := by positivity
    have hdim : 0 ≤ (p.b : ℝ) * p.d * packetScale p * workScale p := by positivity
    have hinit : 0 ≤ (p.b : ℝ) * p.d * initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p) := by positivity
    refine ⟨c, initializer, modular, ?_⟩
    unfold rawTimeBound
    rw [min_eq_right (le_of_not_ge hXN)]
    nlinarith only [hb, hm, ht, hbase, hdim, hinit]

end LongTails.Proofs.DashaDistributedRecipes
