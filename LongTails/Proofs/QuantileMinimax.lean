import LongTails.Proofs.QuantileExecutionLowerBound

open MeasureTheory

namespace LongTails.Proofs.QuantileMinimax

open OracleTemplate
open LongTails.Setups.QuantileSymmetricRemainderConvex
open QuantileOracleLowerBound QuantileShellOracle QuantileQuadraticOracle QuantileExecutionLowerBound

lemma two_oracle_failure {ι : Type} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {d : ℕ} (hd : 0 < d) {L R r M ε h : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hL : h * Real.sqrt d / R ≤ L)
    (P Q x : ι → ℝ) (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hPs : ∑ i, P i = 1) (hQs : ∑ i, Q i = 1) (hx : Measurable x)
    (hpnoise : NoiseCondition ((atomicMeasure P x).map (fun ω => h - ω)) r M)
    (hqnoise : NoiseCondition ((atomicMeasure Q x).map (fun ω => -h - ω)) r M)
    (N : ℕ) (hN : N * (∑ i, (P i - Q i) ^ 2 / Q i) ≤ 1 / 8)
    (hgap : 8 * ε < h * Real.sqrt d * R)
    (A : Algorithm (Space d) (Space d) (Space d)) :
    ¬ ∀ f O, spec.admissible (params d L R r M ε) f O →
      spec.successful (params d L R r M ε) f
        (fun s : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) s.1 s.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  intro hall
  let p : ProbabilityMeasure ℝ := ⟨atomicMeasure P x, atomic_probability P x (fun i => (hP i).le) hPs⟩
  let q : ProbabilityMeasure ℝ := ⟨atomicMeasure Q x, atomic_probability Q x (fun i => (hQ i).le) hQs⟩
  let lam := h * Real.sqrt d / R
  let c := center d R
  let out := fun s : A.Seed × (ℕ → ℝ) => execute (oracle d lam p) A (fun _ => N) s.1 s.2
  have hp := hall _ _ (positive_admissible hd hR hh.le hL p hpnoise)
  have hq := hall _ _ (negative_admissible hd hR hh.le hL q hqnoise)
  obtain ⟨hmp, u, hminp, hIp, hbp⟩ := hp
  obtain ⟨_, v, hminq, hIq, hbq⟩ := hq
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hzp := minimizer_value hlam c u hminp
  have hzq := minimizer_value hlam (-c) v hminq
  have hip : Integrable (fun s => centeredQuadratic lam c (out s))
      ((A.law : Measure A.Seed).prod (Measure.infinitePi fun _ : ℕ => atomicMeasure P x)) := by
    change Integrable (fun s => centeredQuadratic lam c (out s) - centeredQuadratic lam c u)
      ((A.law : Measure A.Seed).prod (Measure.infinitePi fun _ : ℕ => atomicMeasure P x)) at hIp
    simpa only [hzp, sub_zero] using hIp
  have hiq : Integrable (fun s => centeredQuadratic lam (-c) (out s))
      ((A.law : Measure A.Seed).prod (Measure.infinitePi fun _ : ℕ => atomicMeasure Q x)) := by
    change Integrable (fun s => centeredQuadratic lam (-c) (out s) - centeredQuadratic lam (-c) v)
      ((A.law : Measure A.Seed).prod (Measure.infinitePi fun _ : ℕ => atomicMeasure Q x)) at hIq
    simpa only [hzq, sub_zero] using hIq
  have htest := atomic_observation_testing A.law P Q x hP hQ hPs hQs hx N hN out hmp
    (fun a ξ ζ he => execute_prefix_congr (oracle d lam p) A N a ξ ζ he) hlam c hip hiq
  have hbp' : (∫ s, centeredQuadratic lam c (out s) ∂(A.law : Measure A.Seed).prod
      (Measure.infinitePi fun _ : ℕ => atomicMeasure P x)) ≤ ε := by
    change (∫ s, centeredQuadratic lam c (out s) - centeredQuadratic lam c u
      ∂(A.law : Measure A.Seed).prod (Measure.infinitePi fun _ : ℕ => atomicMeasure P x)) ≤ ε at hbp
    simpa only [hzp, sub_zero] using hbp
  have hbq' : (∫ s, centeredQuadratic lam (-c) (out s) ∂(A.law : Measure A.Seed).prod
      (Measure.infinitePi fun _ : ℕ => atomicMeasure Q x)) ≤ ε := by
    change (∫ s, centeredQuadratic lam (-c) (out s) - centeredQuadratic lam (-c) v
      ∂(A.law : Measure A.Seed).prod (Measure.infinitePi fun _ : ℕ => atomicMeasure Q x)) ≤ ε at hbq
    simpa only [hzq, sub_zero] using hbq
  have hcn : ‖c‖ = R := center_norm hd hR.le
  have hval : lam * ‖c‖ ^ 2 / 4 = h * Real.sqrt d * R / 4 := by
    rw [hcn]
    dsimp [lam]
    field_simp
  rw [hval] at htest
  linarith

lemma shell_oracle_failure {d : ℕ} (hd : 0 < d) {L R r M ε h : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hL : h * Real.sqrt d / R ≤ L)
    (hr : h ≤ r) (hM : h ^ 2 ≤ M / 512)
    (N : ℕ) (hN : N * (4096 * h ^ 4 / M ^ 2) ≤ 1 / 8)
    (hgap : 8 * ε < h * Real.sqrt d * R)
    (A : Algorithm (Space d) (Space d) (Space d)) :
    ¬ ∀ f O, spec.admissible (params d L R r M ε) f O →
      spec.successful (params d L R r M ε) f
        (fun s : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) s.1 s.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let k := ⌈M / (4 * h ^ 2)⌉₊
  have hk := shell_count_bounds hh hM
  have ha := (fixed_shell_conditions hk.1).2.1
  have habs : |h| ≤ r := by rwa [abs_of_pos hh]
  have hp := QuantileNoiseLaws.noise_reflection (fixed_shell_noise hk.1 habs hk.2)
  have hq := QuantileNoiseLaws.noise_reflection (fixed_shell_negative_noise hk.1 habs hk.2)
  rw [Measure.map_map measurable_neg (by fun_prop)] at hp hq
  have hp' : NoiseCondition ((shellLaw (1 / 64) (1 / (3 * k)) k h).map (fun z => h - z)) r M := by
    convert hp using 1
    congr 1
    funext z
    dsimp only [Function.comp_apply]
    ring
  have hq' : NoiseCondition ((shellLaw (1 / 64) (-(1 / (3 * k))) k h).map (fun z => -h - z)) r M := by
    convert hq using 1
    congr 1
    funext z
    dsimp only [Function.comp_apply]
    ring
  apply two_oracle_failure hd hR hh hL
    (shellWeights (1 / 64) (1 / (3 * k)) k)
    (shellWeights (1 / 64) (-(1 / (3 * k))) k) (shellPoints k h)
    (shellWeights_pos (by norm_num) (by norm_num) ha k)
    (shellWeights_pos (by norm_num) (by norm_num) (by simpa only [abs_neg] using ha) k)
    (shellWeights_sum _ _ _) (shellWeights_sum _ _ _) (measurable_of_finite _) hp' hq' N _ hgap A
  exact (mul_le_mul_of_nonneg_left (chosen_shell_chi hh hM) (Nat.cast_nonneg N)).trans hN

lemma oracle_complexity_lower {d : ℕ} (hd : 0 < d) {L R r M ε : ℝ}
    (hR : 0 < R) (he : 0 < ε) (hM : 0 < M)
    (heL : ε ≤ L * R ^ 2 / 16) (her : ε ≤ r * R * Real.sqrt d / 16)
    (heM : ε ^ 2 ≤ (d : ℝ) * M * R ^ 2 / 131072)
    (N : ℕ) (hN : (N : ℝ) ≤ (d : ℝ) ^ 2 * M ^ 2 * R ^ 4 / (2147483648 * ε ^ 4))
    (A : Algorithm (Space d) (Space d) (Space d)) :
    ¬ ∀ f O, spec.admissible (params d L R r M ε) f O →
      spec.successful (params d L R r M ε) f
        (fun s : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) s.1 s.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hs := Real.sq_sqrt hdR.le
  let h := 16 * ε / (R * Real.sqrt d)
  have hh : 0 < h := by dsimp [h]; positivity
  have hL : h * Real.sqrt d / R ≤ L := by
    have hid : h * Real.sqrt d / R = 16 * ε / R ^ 2 := by dsimp [h]; field_simp
    rw [hid, div_le_iff₀ (sq_pos_of_pos hR)]
    linarith
  have hr : h ≤ r := by
    dsimp [h]
    rw [div_le_iff₀ (mul_pos hR hsd)]
    nlinarith
  have hm : h ^ 2 ≤ M / 512 := by
    dsimp [h]
    rw [div_pow, mul_pow, mul_pow, hs, div_le_iff₀ (mul_pos (sq_pos_of_pos hR) hdR)]
    nlinarith
  have hgap : 8 * ε < h * Real.sqrt d * R := by
    have hid : h * Real.sqrt d * R = 16 * ε := by dsimp [h]; field_simp
    rw [hid]
    linarith
  have hc : (N : ℝ) * (4096 * h ^ 4 / M ^ 2) ≤ 1 / 8 := by
    calc
      _ ≤ ((d : ℝ) ^ 2 * M ^ 2 * R ^ 4 / (2147483648 * ε ^ 4)) *
          (4096 * h ^ 4 / M ^ 2) := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 1 / 8 := by
        have hs4 : Real.sqrt d ^ 4 = (d : ℝ) ^ 2 := by
          calc
            _ = (Real.sqrt d ^ 2) ^ 2 := by ring
            _ = _ := by rw [hs]
        dsimp [h]
        field_simp
        rw [hs4]
        ring
  exact shell_oracle_failure hd hR hh hL hr hm N hc hgap A

end LongTails.Proofs.QuantileMinimax
