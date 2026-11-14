import LongTails.Proofs.StretchedExponentialLowerParameters
import LongTails.Proofs.CountdownHardInstance
import LongTails.Proofs.CountdownTesting
import LongTails.TemplateLowerBound

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.StretchedExponentialLowerBound

open LongTails.Setups.StretchedExponentialMarkovConvex
open CountdownMarkov CountdownHardInstance

noncomputable def jump (p : Params) (hp : spec.valid p) : unitInterval :=
  calibratedJump (length p) (mass p) (length_pos p hp) (mass_bounds p hp).1.le
    (by have := (mass_bounds p hp).2; linarith)

noncomputable def trajectory (p : Params) (hp : spec.valid p) : ProbabilityMeasure (ℕ → ℝ) :=
  LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
    (kernel (length p) (jump p hp)) (stationaryLaw (length p) (jump p hp))

noncomputable def hardObjective (p : Params) (c : Space p) : Space p → ℝ :=
  objective (4 * p.ε / p.R ^ 2) p.x0 c

noncomputable def hardOracle (p : Params) (hp : spec.valid p) (c : Space p) :
    Oracle (Space p) (Space p) :=
  sampledOracle (reply (4 * p.ε / p.R ^ 2) (mass p) p.x0 c) (trajectory p hp)

lemma hardObjective_admissible (p : Params) (hp : spec.valid p) (c : Space p)
    (hc : ‖c‖ = p.R) : spec.admissible p (hardObjective p c) (hardOracle p hp c) := by
  obtain ⟨hq, hq1⟩ := mass_bounds p hp
  have hH := length_pos p hp
  have hC := lengthScale_ge_one p hp
  rcases hp with ⟨hd, hL, hR, hσ, hα, hα2, hτ, hγ, hγ1, hε, hLR, hsmall, hreg⟩
  have hμ : 0 ≤ 4 * p.ε / p.R ^ 2 := by positivity
  have hμL : 4 * p.ε / p.R ^ 2 ≤ p.L := (div_le_iff₀ (by positivity)).mpr hLR
  have hnorm : ‖(4 * p.ε / p.R ^ 2) • c‖ = 4 * p.ε / p.R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ, hc]
    field_simp
  refine ⟨reply (4 * p.ε / p.R ^ 2) (mass p) p.x0 c,
    kernel (length p) (jump p ⟨hd, hL, hR, hσ, hα, hα2, hτ, hγ, hγ1, hε, hLR, hsmall, hreg⟩),
    inferInstance, stationaryLaw (length p) (jump p ⟨hd, hL, hR, hσ, hα, hα2, hτ, hγ, hγ1, hε, hLR, hsmall, hreg⟩),
    rfl, stationary _ _, (fun t => integrable_stationary _ _ _), ?_, ?_, ?_, ?_, ?_,
    reply_measurable _ _ _ _, (fun x => integrable_stationary _ _ _), ?_,
    (fun x => integrable_stationary _ _ _), ?_⟩
  · intro n
    apply calibrated_mixing (length p) (mass p) hH hq hq1 (by linarith) hγ hγ1 _ n
    exact Nat.floor_le (by linarith : 0 ≤ lengthScale p)
  · exact LongTails.Proofs.QuantileOracleLowerBound.centeredQuadratic_convex hμ _
  · intro x
    change HasGradientAt (objective (4 * p.ε / p.R ^ 2) p.x0 c)
      (gradient (objective (4 * p.ε / p.R ^ 2) p.x0 c) x) x
    rw [(objective_gradient (4 * p.ε / p.R ^ 2) p.x0 c x).gradient]
    exact objective_gradient (4 * p.ε / p.R ^ 2) p.x0 c x
  · intro x y
    exact LongTails.Proofs.QuantileOracleLowerBound.centeredQuadratic_lipschitz hμ hμL _ x y
  · refine ⟨p.x0 + c, objective_min hμ _ _, ?_⟩
    simpa only [sub_add_cancel_left, norm_neg, hc] using le_refl p.R
  · intro x
    exact reply_mean _ _ _ _ _ _ hH hq (by linarith)
  · intro x
    have hm := reply_moment (4 * p.ε / p.R ^ 2) (mass p) p.α p.x0 c x
      (length p) hH hq (by linarith) hα.le
    rw [hnorm] at hm
    exact hm.trans (mass_noise_bound p ⟨hd, hL, hR, hσ, hα, hα2, hτ, hγ, hγ1, hε, hLR, hsmall, hreg⟩)

lemma successful_objective (p : Params) (hp : spec.valid p) (c : Space p)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (output : Ω → Space p)
    (h : spec.successful p (hardObjective p c) output P) :
    Integrable (fun ω => hardObjective p c (output ω)) (P : Measure Ω) ∧
      (∫ ω, hardObjective p c (output ω) ∂(P : Measure Ω)) ≤ p.ε := by
  rcases h with ⟨_, xstar, hmin, hi, hb⟩
  have hε := hp.2.2.2.2.2.2.2.2.2.1
  have hμ : 0 ≤ 4 * p.ε / p.R ^ 2 := by positivity
  have hx := hmin (Set.mem_univ (p.x0 + c))
  change hardObjective p c xstar ≤ hardObjective p c (p.x0 + c) at hx
  have hz : hardObjective p c (p.x0 + c) = 0 := objective_at_center _ _ _
  have hn : 0 ≤ hardObjective p c xstar := objective_nonneg hμ _ _ _
  have he : hardObjective p c xstar = 0 := by rw [hz] at hx; linarith
  simpa only [he, sub_zero] using And.intro hi hb

lemma hard_pair_not_successful (p : Params) (hp : spec.valid p) (c : Space p)
    (hc : ‖c‖ = p.R) (A : Algorithm (Space p) (Space p) (Space p))
    (n : ℕ) (hn : n ≤ ⌊lengthScale p / (32 * mass p)⌋₊) :
    ¬ (spec.successful p (hardObjective p c)
        (fun w : A.Seed × (ℕ → ℝ) => execute (hardOracle p hp c) A (fun _ => n) w.1 w.2)
        ⟨(A.law : Measure A.Seed).prod (trajectory p hp : Measure (ℕ → ℝ)), inferInstance⟩ ∧
      spec.successful p (hardObjective p (-c))
        (fun w : A.Seed × (ℕ → ℝ) => execute (hardOracle p hp (-c)) A (fun _ => n) w.1 w.2)
        ⟨(A.law : Measure A.Seed).prod (trajectory p hp : Measure (ℕ → ℝ)), inferInstance⟩) := by
  rintro ⟨hplus, hminus⟩
  obtain ⟨hip, hbp⟩ := successful_objective p hp c _ _ hplus
  obtain ⟨him, hbm⟩ := successful_objective p hp (-c) _ _ hminus
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.1
  have hR : 0 < p.R := hp.2.2.1
  have hμ : 0 ≤ 4 * p.ε / p.R ^ 2 := by positivity
  have he : (4 * p.ε / p.R ^ 2) * ‖c‖ ^ 2 = 4 * p.ε := by
    rw [hc, div_mul_cancel₀ _ (by positivity)]
  have hpair := execution_pair_lower
    (reply (4 * p.ε / p.R ^ 2) (mass p) p.x0 c)
    (reply (4 * p.ε / p.R ^ 2) (mass p) p.x0 (-c)) (trajectory p hp)
    0 (measurableSet_singleton 0) (fun x => by simp only [reply_common]) A n
    (hardObjective p c) (hardObjective p (-c))
    (fun x => objective_nonneg hμ _ _ _) (fun x => objective_nonneg hμ _ _ _)
    (4 * p.ε) (fun x => by
      have h := objective_pair_lower hμ p.x0 c x
      rw [he] at h
      exact h) hip him
  have hprob : 7 / 8 ≤ (trajectory p hp : Measure (ℕ → ℝ)).real (commonPrefix 0 n) :=
    calibrated_commonPrefix_seven_eighths (mass_bounds p hp).1 (mass_bounds p hp).2
      (lengthScale_ge_one p hp) hn
  change 4 * p.ε * (trajectory p hp : Measure (ℕ → ℝ)).real (commonPrefix 0 n) ≤
    (∫ w : A.Seed × (ℕ → ℝ), hardObjective p c
      (execute (hardOracle p hp c) A (fun _ => n) w.1 w.2)
      ∂((A.law : Measure A.Seed).prod (trajectory p hp : Measure (ℕ → ℝ)))) +
    (∫ w : A.Seed × (ℕ → ℝ), hardObjective p (-c)
      (execute (hardOracle p hp (-c)) A (fun _ => n) w.1 w.2)
      ∂((A.law : Measure A.Seed).prod (trajectory p hp : Measure (ℕ → ℝ)))) at hpair
  simp only [ProbabilityMeasure.coe_mk] at hbp hbm
  nlinarith only [hpair, hbp, hbm, hprob, hε]

lemma exists_failure (p : Params) (hp : spec.valid p)
    (A : Algorithm (Space p) (Space p) (Space p)) (b : Fin 1 → ℕ)
    (hb : b 0 ≤ ⌊lengthScale p / (32 * mass p)⌋₊) :
    ∃ (f : Space p → ℝ) (O : Oracle (Space p) (Space p)), spec.admissible p f O ∧
      ¬ spec.successful p f
        (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b w.1 w.2)
        ⟨(A.law : Measure A.Seed).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let c : Space p := PiLp.single 2 (⟨0, hp.1⟩ : Fin p.d) p.R
  have hR : 0 < p.R := hp.2.2.1
  have hc : ‖c‖ = p.R := by simp [c, Real.norm_eq_abs, abs_of_pos hR]
  have hbfun : b = fun _ => b 0 := by funext i; exact congrArg b (Fin.eq_zero i)
  have hpair := hard_pair_not_successful p hp c hc A (b 0) hb
  by_cases hplus : spec.successful p (hardObjective p c)
      (fun w : A.Seed × (ℕ → ℝ) => execute (hardOracle p hp c) A (fun _ => b 0) w.1 w.2)
      ⟨(A.law : Measure A.Seed).prod (trajectory p hp : Measure (ℕ → ℝ)), inferInstance⟩
  · refine ⟨hardObjective p (-c), hardOracle p hp (-c),
      hardObjective_admissible p hp (-c) (by simpa only [norm_neg] using hc), ?_⟩
    rw [hbfun]
    exact fun hminus => hpair ⟨hplus, hminus⟩
  · refine ⟨hardObjective p c, hardOracle p hp c, hardObjective_admissible p hp c hc, ?_⟩
    rw [hbfun]
    exact hplus

end OracleTemplate.StretchedExponentialLowerBound
