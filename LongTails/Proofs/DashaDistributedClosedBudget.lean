import LongTails.Proofs.DashaDistributedRecipes

namespace LongTails.Proofs.DashaDistributedClosedBudget

open DashaDistributedLogBounds DashaDistributedTuningBounds DashaDistributedRecipes

noncomputable def singleLogScale (d N : ℝ) : ℝ := 2 + Real.log N + Real.log (1 + Real.log d)

lemma single_worker_raw_bound (d N Z τ b : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hZ : 0 ≤ Z) (hZN : Z ≤ 2 * (N - 1)) (ht : 0 ≤ τ) (hb : 0 ≤ b) :
    N * τ + b * (logScale d N (N - 1) * (N + d * min (N - 1) N) +
      d * initialCharge (logScale d N (N - 1)) (initialLogScale d N) (modularLogScale d N) Z) ≤
      8 * N * (τ + b * d * singleLogScale d N) := by
  let B := logScale d N (N - 1)
  let S := singleLogScale d N
  have hN0 : 0 < N := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hiter : 0 ≤ Real.log (1 + Real.log d) := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hS : 2 ≤ S := by dsimp [S, singleLogScale]; linarith
  have hB : 2 ≤ B := two_le_logScale d N (N - 1) hd hN (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogB := Real.log_le_log (show 0 < N + (N - 1) by linarith)
    (show N + (N - 1) ≤ 2 * N by linarith)
  rw [Real.log_mul (by norm_num) hN0.ne'] at hlogB
  have hBS : B ≤ (3 / 2 : ℝ) * S := by
    dsimp [B, S, logScale, singleLogScale] at *
    linarith
  have hlogZ := Real.log_le_log (show 0 < 1 + Z by positivity) (show 1 + Z ≤ 2 * N by linarith)
  rw [Real.log_mul (by norm_num) hN0.ne'] at hlogZ
  have hZS : Real.log (1 + Z) ≤ S := by dsimp [S, singleLogScale]; linarith
  have hprod : 1 + Z * B ≤ (1 + Z) * (1 + B) := by nlinarith
  have hsum := Real.log_le_log (show 0 < 1 + Z * B by positivity) hprod
  rw [Real.log_mul (by positivity) (by positivity)] at hsum
  have hlog1B := Real.log_le_sub_one_of_pos (show 0 < 1 + B by positivity)
  have hLB := (initialLogScale_bounds d d N (N - 1) hd le_rfl hN (by linarith)).2.1
  have hcharge : initialCharge B (initialLogScale d N) (modularLogScale d N) Z ≤ 4 * S := by
    have hm : initialCharge B (initialLogScale d N) (modularLogScale d N) Z ≤ initialLogScale d N + Real.log (1 + Z * B) :=
      (min_le_right _ _).trans (min_le_left _ _)
    change initialLogScale d N ≤ B at hLB
    linarith
  have hmain : N + d * min (N - 1) N ≤ 2 * d * N := by
    rw [min_eq_left (show N - 1 ≤ N by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hd hN0.le]
  have hmainB := mul_le_mul hmain hBS (by linarith : 0 ≤ B) (by positivity : 0 ≤ 2 * d * N)
  have hinit := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ d by linarith)
  have hNinit := mul_le_mul_of_nonneg_left hN (show 0 ≤ 4 * d * S by positivity)
  have hcomm : B * (N + d * min (N - 1) N) + d * initialCharge B (initialLogScale d N) (modularLogScale d N) Z ≤
      7 * d * N * S := by nlinarith only [hmainB, hinit, hNinit]
  have hm := mul_le_mul_of_nonneg_left hcomm hb
  change N * τ + b * (B * (N + d * min (N - 1) N) + d * initialCharge B (initialLogScale d N) (modularLogScale d N) Z) ≤
    8 * N * (τ + b * d * S)
  have h1 : 0 ≤ N * τ := by positivity
  have h2 : 0 ≤ b * d * N * S := by positivity
  nlinarith only [hm, h1, h2]

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed LongTails.Algorithms.DashaDistributedNormalization
open LongTails.Algorithms.DashaDistributedSelection

variable {p : Params}

noncomputable def mainScale (p : Params) : ℝ :=
  1 + p.Δ * (min p.L p.Lhat + (p.d : ℝ) * min (min p.L p.Lhat) (p.Lhat / Real.sqrt (p.n : ℝ))) / p.ε ^ 2

noncomputable def condensedTimeBound (p : Params) : ℝ :=
  workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) +
    (p.b : ℝ) * (packetScale p * mainScale p +
      (p.d : ℝ) * initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p))

lemma mainScale_eq (hΔ : 0 ≤ p.Δ) :
    workScale p + (p.d : ℝ) * min (heterogeneityScale p) (workScale p - 1) = mainScale p := by
  let t := p.Δ / p.ε ^ 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hX : heterogeneityScale p = t * (p.Lhat / Real.sqrt (p.n : ℝ)) := by
    dsimp [heterogeneityScale, t]
    ring
  have ha : workScale p - 1 = t * min p.L p.Lhat := by dsimp [workScale, t]; ring
  rw [hX, ha, ← mul_min_of_nonneg _ _ ht, min_comm (p.Lhat / Real.sqrt (p.n : ℝ))]
  dsimp [mainScale, workScale, t]
  ring

lemma condensedTimeBound_nonneg (hp : spec.valid p) : 0 ≤ condensedTimeBound p := by
  obtain ⟨hN, hX, _, hB, _⟩ := scales_valid hp
  have hi := initialCharge_nonneg hp
  have hm : 0 ≤ mainScale p := by
    rw [← mainScale_eq hp.2.2.2.1]
    have ha : 0 ≤ workScale p - 1 := by linarith
    positivity
  unfold condensedTimeBound
  positivity

lemma raw_le_condensed (hp : spec.valid p) (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    rawTimeBound p ≤ 3 * condensedTimeBound p := by
  obtain ⟨hN, hX, _, hB, _⟩ := scales_valid hp
  have hi := initialCharge_nonneg hp
  have ha : 1 / 2 ≤ workScale p - 1 := by
    have hε2 : 0 < p.ε ^ 2 := sq_pos_of_pos hp.2.2.2.2.2
    have h := (le_div_iff₀ hε2).mpr (show (1 / 2 : ℝ) * p.ε ^ 2 ≤ min p.L p.Lhat * p.Δ by linarith)
    dsimp [workScale]
    linarith
  have hc := main_charge_collapse (workScale p - 1) (p.d : ℝ) (heterogeneityScale p) ha (by positivity) hX
  have he : 1 + (workScale p - 1) = workScale p := by ring
  rw [he, mainScale_eq hp.2.2.2.1] at hc
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (p.b : ℝ) * packetScale p by positivity)
  have hbase : 0 ≤ workScale p * ((computationTime p : ℝ) + p.l + 64 * p.b) := by positivity
  have hinit : 0 ≤ (p.b : ℝ) * p.d * initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p) := by positivity
  unfold rawTimeBound condensedTimeBound
  nlinarith only [hm, hbase, hinit]

lemma normalized_min : min (LongTails.Algorithms.DashaDistributedNormalization.normalize p).L (LongTails.Algorithms.DashaDistributedNormalization.normalize p).Lhat = min p.L p.Lhat := by
  by_cases hn : p.n = 1 <;> simp [LongTails.Algorithms.DashaDistributedNormalization.normalize, hn]

lemma normalized_workScale : workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p) = workScale p := by
  unfold workScale
  rw [normalized_min]
  rfl

lemma normalized_raw_eq (hn : p.n ≠ 1) : rawTimeBound (LongTails.Algorithms.DashaDistributedNormalization.normalize p) = rawTimeBound p := by
  simp [rawTimeBound, workScale, heterogeneityScale, packetScale, floatScale, denseScale, noiseScale,
    LongTails.Algorithms.DashaDistributedNormalization.normalize, hn, computationTime]
  exact Or.inl rfl

lemma selected_raw_bound (hp : spec.valid p) (hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ) :
    (timeBound p : ℝ) ≤ 393216 * rawTimeBound (LongTails.Algorithms.DashaDistributedNormalization.normalize p) := by
  have hpn := DashaDistributedNormalization.normalized_valid hp
  have hgapn : (LongTails.Algorithms.DashaDistributedNormalization.normalize p).ε ^ 2 ≤ 2 * min (LongTails.Algorithms.DashaDistributedNormalization.normalize p).L (LongTails.Algorithms.DashaDistributedNormalization.normalize p).Lhat * (LongTails.Algorithms.DashaDistributedNormalization.normalize p).Δ := by
    rw [normalized_min]
    exact hgap
  obtain ⟨c, initializer, modular, hb⟩ := exists_recipe hpn hgapn
  have hc := DashaDistributedBudget.timeBound_competitive hp c initializer modular
  have hcR : (timeBound p : ℝ) ≤ 4 * (timeBudget (LongTails.Algorithms.DashaDistributedNormalization.normalize p)
      (LongTails.Algorithms.DashaDistributedTrackedParameters.trackedConfig (LongTails.Algorithms.DashaDistributedNormalization.normalize p) c initializer modular) : ℝ) := by
    exact_mod_cast hc
  linarith

lemma normalized_single_raw_bound (hp : spec.valid p) (hn : p.n = 1) :
    rawTimeBound (LongTails.Algorithms.DashaDistributedNormalization.normalize p) ≤ 8 * workScale p *
      (((computationTime p : ℝ) + p.l + 64 * p.b) + (p.b : ℝ) * p.d * singleLogScale p.d (workScale p)) := by
  have hpn := DashaDistributedNormalization.normalized_valid hp
  obtain ⟨hN, _, _, _, _⟩ := scales_valid hp
  have hZ := (scales_valid hpn).2.2.1
  have hX : heterogeneityScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p) = workScale p - 1 := by
    simp [heterogeneityScale, workScale, LongTails.Algorithms.DashaDistributedNormalization.normalize, hn]
  have hG0 : 0 ≤ (LongTails.Algorithms.DashaDistributedNormalization.normalize p).G := hpn.2.2.2.2.1
  have hG : (LongTails.Algorithms.DashaDistributedNormalization.normalize p).G ≤ Real.sqrt (2 * min p.L p.Lhat * p.Δ) := by
    simp only [LongTails.Algorithms.DashaDistributedNormalization.normalize, hn, ite_true]
    exact min_le_right _ _
  have hGsq := (sq_le_sq₀ hG0 (Real.sqrt_nonneg _)).mpr hG
  rw [Real.sq_sqrt (by have hL := hp.2.1; have hH := hp.2.2.1; have hΔ := hp.2.2.2.1; positivity)] at hGsq
  have hZN : noiseScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p) ≤ 2 * (workScale p - 1) := by
    have hb := div_le_div_of_nonneg_right hGsq (sq_nonneg p.ε)
    simpa [noiseScale, LongTails.Algorithms.DashaDistributedNormalization.normalize, hn, workScale, mul_div_assoc, mul_assoc] using hb
  have hb := single_worker_raw_bound (p.d : ℝ) (workScale p) (noiseScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p))
    ((computationTime p : ℝ) + p.l + 64 * p.b) p.b (by exact_mod_cast p.d.pos) hN hZ hZN (by positivity) p.b.coe_nonneg
  have hnR : (p.n : ℝ) = 1 := by simp [hn]
  unfold rawTimeBound packetScale floatScale denseScale
  change workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p) * ((computationTime p : ℝ) + p.l + 64 * p.b) +
    (p.b : ℝ) * (logScale ((p.n : ℝ) * p.d) (workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p)) (heterogeneityScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p)) *
      (workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p) + (p.d : ℝ) * min (heterogeneityScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p)) (workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p))) +
      (p.d : ℝ) * initialCharge
        (logScale ((p.n : ℝ) * p.d) (workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p)) (heterogeneityScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p)))
        (initialLogScale p.d (workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p))) (modularLogScale ((p.n : ℝ) * p.d) (workScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p)))
        (noiseScale (LongTails.Algorithms.DashaDistributedNormalization.normalize p))) ≤ _
  rw [normalized_workScale, hX, hnR, one_mul]
  exact hb

noncomputable def singleTimeBound (p : Params) : ℝ :=
  workScale p * (((computationTime p : ℝ) + p.l + 64 * p.b) +
    (p.b : ℝ) * p.d * singleLogScale p.d (workScale p))

lemma singleLogScale_nonneg (hp : spec.valid p) : 0 ≤ singleLogScale p.d (workScale p) := by
  have hN := (scales_valid hp).1
  have hlogN := Real.log_nonneg hN
  have hlogd := Real.log_nonneg (show (1 : ℝ) ≤ p.d by exact_mod_cast p.d.pos)
  have hiter := Real.log_nonneg (show 1 ≤ 1 + Real.log (p.d : ℝ) by linarith)
  unfold singleLogScale
  linarith

lemma singleTimeBound_nonneg (hp : spec.valid p) : 0 ≤ singleTimeBound p := by
  have hN := (scales_valid hp).1
  have hS := singleLogScale_nonneg hp
  unfold singleTimeBound
  positivity

lemma communicationBound_nonneg (hp : spec.valid p) :
    0 ≤ packetScale p * mainScale p + (p.d : ℝ) *
      initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p) := by
  obtain ⟨hN, hX, _, hB, _⟩ := scales_valid hp
  have hi := initialCharge_nonneg hp
  have hm : 0 ≤ mainScale p := by
    rw [← mainScale_eq hp.2.2.2.1]
    have ha : 0 ≤ workScale p - 1 := by linarith
    positivity
  positivity

noncomputable def closedDeadline (p : Params) : DistributedTemplate.Time :=
  (2 ^ 22 : DistributedTemplate.Time) * (if min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then 0
    else if p.n = 1 then Real.toNNReal (workScale p) *
      ((computationTime p + p.l + 64 * p.b) + p.b * p.d * Real.toNNReal (singleLogScale p.d (workScale p)))
    else Real.toNNReal (workScale p) * (computationTime p + p.l + 64 * p.b) + p.b * Real.toNNReal
      (packetScale p * mainScale p + (p.d : ℝ) * initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p)))

lemma closedDeadline_zero (hz : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2) : closedDeadline p = 0 := by
  simp [closedDeadline, hz]

lemma closedDeadline_coe (hp : spec.valid p)
    (hz : ¬ min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2) :
    (closedDeadline p : ℝ) = 4194304 * (if p.n = 1 then singleTimeBound p else condensedTimeBound p) := by
  have hN : 0 ≤ workScale p := by have h := (scales_valid hp).1; linarith
  have hS := singleLogScale_nonneg hp
  have hC := communicationBound_nonneg hp
  by_cases hn : p.n = 1
  · simp [closedDeadline, hz, hn, Real.coe_toNNReal _ hN, Real.coe_toNNReal _ hS, singleTimeBound]
    norm_num
  · simp [closedDeadline, hz, hn, Real.coe_toNNReal _ hN, Real.coe_toNNReal _ hC, condensedTimeBound]
    norm_num

lemma closedDeadline_suffices (hp : spec.valid p) : timeBound p ≤ closedDeadline p := by
  by_cases hz : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2
  · rw [closedDeadline_zero hz]
    simp [timeBound, hz]
  · have hgap : p.ε ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ :=
      ((lt_of_not_ge hz).trans_le (min_le_left _ _)).le
    have hb := selected_raw_bound hp hgap
    apply NNReal.coe_le_coe.mp
    rw [closedDeadline_coe hp hz]
    by_cases hn : p.n = 1
    · rw [ite_eq_left hn]
      have hr := normalized_single_raw_bound hp hn
      change rawTimeBound (LongTails.Algorithms.DashaDistributedNormalization.normalize p) ≤ 8 *
        workScale p * (((computationTime p : ℝ) + p.l + 64 * p.b) +
          (p.b : ℝ) * p.d * singleLogScale p.d (workScale p)) at hr
      have h0 := singleTimeBound_nonneg hp
      unfold singleTimeBound at h0 ⊢
      nlinarith only [hb, hr, h0]
    · rw [ite_eq_right hn]
      rw [normalized_raw_eq hn] at hb
      have hr := raw_le_condensed hp hgap
      have h0 := condensedTimeBound_nonneg hp
      nlinarith only [hb, hr, h0]

lemma packetScale_eq : packetScale p = 2 +
    Real.log (1 + p.Δ * (min p.L p.Lhat + p.Lhat / Real.sqrt (p.n : ℝ)) / p.ε ^ 2) +
      Real.log (1 + Real.log ((p.n : ℝ) * p.d)) := by
  have he : workScale p + heterogeneityScale p =
      1 + p.Δ * (min p.L p.Lhat + p.Lhat / Real.sqrt (p.n : ℝ)) / p.ε ^ 2 := by
    dsimp [workScale, heterogeneityScale]
    ring
  unfold packetScale logScale
  rw [he]

lemma initialCharge_eq (hp : spec.valid p) :
    initialCharge (packetScale p) (floatScale p) (denseScale p) (noiseScale p) =
      min (p.G / (p.ε * Real.sqrt (p.n : ℝ)) * Real.sqrt (packetScale p * floatScale p))
        (min (floatScale p + Real.log (1 + p.G ^ 2 * packetScale p / ((p.n : ℝ) * p.ε ^ 2))) (denseScale p)) := by
  have hZ := (scales_valid hp).2.2.1
  have he : Real.sqrt (noiseScale p * packetScale p * floatScale p) =
      p.G / (p.ε * Real.sqrt (p.n : ℝ)) * Real.sqrt (packetScale p * floatScale p) := by
    calc
      _ = Real.sqrt (noiseScale p) * Real.sqrt (packetScale p * floatScale p) := by
        rw [← Real.sqrt_mul hZ]
        congr 1
        ring
      _ = _ := by unfold noiseScale; rw [← DashaDistributedSimplification.scaled_G_eq_sqrt hp.2.2.2.2.1 hp.2.2.2.2.2]
  have hprod : noiseScale p * packetScale p = p.G ^ 2 * packetScale p / ((p.n : ℝ) * p.ε ^ 2) := by
    unfold noiseScale
    ring
  unfold initialCharge
  rw [he, hprod]

end LongTails.Proofs.DashaDistributedClosedBudget
