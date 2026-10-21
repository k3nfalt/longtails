import outputs.Setups.MaleniaUniformTime
import outputs.Proofs.SingleOracleCounted
import outputs.Setups.MaleniaUniformTime
import outputs.Proofs.MaleniaUniformTiming
import outputs.Proofs.MaleniaStochastic
import outputs.Proofs.RennalaConvergence

open MeasureTheory

namespace OracleTemplate.MaleniaUniform

open Rennala

noncomputable def budget : outputs.Setups.MaleniaUniformTime.spec.Params → Fin outputs.Setups.MaleniaUniformTime.spec.numOracles → ℕ := fun p _ => p.calls

theorem result : Convergence outputs.Setups.MaleniaUniformTime.spec budget := by
  classical
  refine ⟨malenia, ?_, ?_⟩
  · intro p hp I O hO
    rcases hO with ⟨hf, fs, hfs, hgi, Ω, m, μ, Pst, g, hst, ho, rfl⟩
    letI := m
    let q := publicInput p
    let V : Fin p.n → ℝ → ℝ := fun i => RennalaUniform.work (p.power i)
    let ρ : ProbabilityMeasure (ℕ → ℕ → Ω) :=
      ⟨Measure.map arrays (Pst : Measure (ℕ → Ω)), inferInstance⟩
    let Q : ProbabilityMeasure (Fin (q.K + 1) × (ℕ → ℕ → ℕ → Ω)) :=
      ⟨(PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure.prod
        (Measure.map (fun ξ (_ : ℕ) => arrays ξ) (Pst : Measure (ℕ → Ω))), inferInstance⟩
    change outputs.Setups.MaleniaUniformTime.spec.successful p I (fun z : Fin (q.K + 1) × (ℕ → ℕ → ℕ → Ω) =>
      (executeCounted (eventOracle q V Pst g) (malenia q) (budget p 0) z.1 z.2).1) Q
    intro hfin hcalls
    have hn := hp.1
    have hL := hp.2.1
    have hv := hp.2.2.1
    have heps := hp.2.2.2.1
    have hV : ∀ i, ContinuousOn (V i) (Set.Ici 0) ∧ MonotoneOn (V i) (Set.Ici 0) := fun i =>
      RennalaUniform.work_properties (p.power i) (hp.2.2.2.2 i)
    have hV0 (i : Fin p.n) : V i 0 = 0 := intervalIntegral.integral_same
    have hSn : q.n ≤ q.S := le_max_right _ _
    have hnr : (0 : ℝ) < p.n := by exact_mod_cast hn
    have heta : (q.S : ℝ) / q.n ≤ threshold p.n p.v p.eps := by
      change ((max ⌈p.v / p.eps⌉₊ p.n : ℕ) : ℝ) / p.n ≤ max (2 * p.v / (p.n * p.eps)) 1
      rcases le_total ⌈p.v / p.eps⌉₊ p.n with h | h
      · rw [max_eq_right h, div_self hnr.ne']
        exact le_max_right _ _
      · rw [max_eq_left h]
        by_cases h1 : 1 ≤ p.v / p.eps
        · refine le_trans ?_ (le_max_left _ _)
          have hc : (⌈p.v / p.eps⌉₊ : ℝ) ≤ 2 * p.v / p.eps := by
            have := Nat.ceil_lt_add_one (div_nonneg hv heps.le)
            have h2 : 2 * p.v / p.eps = 2 * (p.v / p.eps) := by ring
            rw [h2]
            linarith
          rw [div_le_div_iff₀ hnr (by positivity)]
          have h3 : (⌈p.v / p.eps⌉₊ : ℝ) * p.eps ≤ 2 * p.v := (le_div_iff₀ heps).mp hc
          nlinarith [mul_le_mul_of_nonneg_left h3 hnr.le]
        · push Not at h1
          refine le_trans ?_ (le_max_right _ _)
          have hle : ⌈p.v / p.eps⌉₊ ≤ 1 := Nat.ceil_le.mpr (by exact_mod_cast h1.le)
          rw [div_le_one hnr]
          have : (⌈p.v / p.eps⌉₊ : ℝ) ≤ 1 := by exact_mod_cast hle
          have h1n : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
          linarith
    have hcalls' : ∑ i, ⌊V i (deadline V (threshold p.n p.v p.eps) q.K).toReal - V i 0⌋₊ ≤ budget p 0 := by
      simp only [hV0, sub_zero]
      exact hcalls
    obtain ⟨c, B, M, hcd, hB, hexe⟩ := execute_malenia q V hV hn hSn Pst g (threshold p.n p.v p.eps)
      heta hfin (budget p 0) hcalls'
    let Ψ : (ℕ → ℕ → ℕ → Ω) → (ℕ → ℕ → Ω) := fun z r c' => z (M r c') r c'
    have hΨm : Measurable Ψ := by
      show Measurable (fun (z : ℕ → ℕ → ℕ → Ω) (r c' : ℕ) => z (M r c') r c')
      fun_prop
    have hmapΨ : (Measure.map (fun ξ (_ : ℕ) => arrays ξ) (Pst : Measure (ℕ → Ω))).map Ψ =
        (ρ : Measure (ℕ → ℕ → Ω)) := environment_transport Pst M
    let U : Measure (Fin (q.K + 1)) := (PMF.uniformOfFintype (Fin (q.K + 1))).toMeasure
    let Φ : Fin (q.K + 1) × (ℕ → ℕ → ℕ → Ω) → Fin (q.K + 1) × (ℕ → ℕ → Ω) := Prod.map id Ψ
    have hΦm : Measurable Φ := measurable_id.prodMap hΨm
    have hmapΦ : (Q : Measure _).map Φ = U.prod (ρ : Measure (ℕ → ℕ → Ω)) := by
      change (U.prod (Measure.map (fun ξ (_ : ℕ) => arrays ξ) (Pst : Measure (ℕ → Ω)))).map (Prod.map id Ψ) = _
      rw [← Measure.map_prod_map _ _ measurable_id hΨm, Measure.map_id, hmapΨ]
    let μ' : ProbabilityMeasure (ℕ → Ω) :=
      ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)), inferInstance⟩
    have hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun r (ω : ℕ → ℕ → Ω) => ω r) (μ' : Measure (ℕ → Ω))
        (ρ : Measure (ℕ → ℕ → Ω)) := by
      change LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID _ _ (Measure.map arrays (Pst : Measure (ℕ → Ω)))
      rw [arrays_law μ Pst hst]
      exact StochasticGeneralized.infinitePi_iid _
    have hS : 0 < q.S := lt_of_lt_of_le hn hSn
    have hoG (r : ℕ) : StochasticOracle (ℕ → Ω) μ' I.f (estimator (B r) g) (p.v / q.S) :=
      estimator_moments fs I.f hfs hgi μ g p.v hv ho hn q.S hS (B r) (hB r)
    let x : Fin (q.K + 1) → (ℕ → ℕ → Ω) → Point p.d := fun j ω => iterate g q.gamma B q.x0 ω j.val
    have hm (j : Fin (q.K + 1)) : Measurable (x j) :=
      (sgd_moments I.f (fun r => estimator (B r) g) μ' ρ (fun r ω => ω r) p.L (p.v / q.S) q.gamma
        q.x0 hL (div_nonneg hv (Nat.cast_nonneg _)) hf.hasGradient hf.lipschitz hoG hiid j.val).1
    have hi (j : Fin (q.K + 1)) : Integrable (fun ω => ‖gradient I.f (x j ω)‖ ^ 2) (ρ : Measure _) :=
      (sgd_moments I.f (fun r => estimator (B r) g) μ' ρ (fun r ω => ω r) p.L (p.v / q.S) q.gamma
        q.x0 hL (div_nonneg hv (Nat.cast_nonneg _)) hf.hasGradient hf.lipschitz hoG hiid j.val).2.2.2
    have hbudget : 24 * p.L * p.Delta / p.eps ≤ ((q.K + 1 : ℕ) : ℝ) := by
      have hh := Nat.le_ceil (24 * p.L * p.Delta / p.eps)
      change 24 * p.L * p.Delta / p.eps ≤ ((⌈24 * p.L * p.Delta / p.eps⌉₊ + 1 : ℕ) : ℝ)
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have ha : (1 / ((q.K + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.K + 1),
        (∫ ω, ‖gradient I.f (x j ω)‖ ^ 2 ∂(ρ : Measure _)) ≤ p.eps := by
      have hh := malenia_accuracy fs I.f hfs hgi μ Pst hst g p.L p.v p.eps p.Delta I.lower p.x0 hn hL hv heps
        hf.hasGradient hf.lipschitz hf.lower hf.gap ho B hB (q.K + 1) (Nat.succ_pos _) hbudget
      erw [← Fin.sum_univ_eq_sum_range (fun k => ∫ ω, ‖gradient I.f (iterate g
        (MaleniaIterations.stepSize p.L p.v p.eps (MaleniaIterations.batchSize p.n p.v p.eps)) B p.x0 ω k)‖ ^ 2
          ∂(Measure.map arrays (Pst : Measure (ℕ → Ω)))) (q.K + 1)] at hh
      exact hh
    have hu := uniform_prefix_accuracy ρ I.f q.K x p.eps hm hi ha
    have hexFun : (fun z : Fin (q.K + 1) × (ℕ → ℕ → ℕ → Ω) =>
        (executeCounted (eventOracle q V Pst g) (malenia q) (budget p 0) z.1 z.2).1) =
        (fun w : Fin (q.K + 1) × (ℕ → ℕ → Ω) => (x w.1 w.2, c)) ∘ Φ := by
      funext z
      rw [hexe z.1 z.2]
      rfl
    rw [hexFun]
    have hgm : AEStronglyMeasurable (fun w : Fin (q.K + 1) × (ℕ → ℕ → Ω) => ‖gradient I.f (x w.1 w.2)‖ ^ 2)
        ((Q : Measure _).map Φ) := by
      rw [hmapΦ]
      exact hu.2.1.aestronglyMeasurable
    refine ⟨(hu.1.prodMk measurable_const).comp hΦm, ?_, ?_, Filter.Eventually.of_forall (fun _ => hcd)⟩
    · have hint : Integrable (fun w : Fin (q.K + 1) × (ℕ → ℕ → Ω) => ‖gradient I.f (x w.1 w.2)‖ ^ 2)
          ((Q : Measure _).map Φ) := by
        rw [hmapΦ]
        exact hu.2.1
      exact (integrable_map_measure hgm hΦm.aemeasurable).mp hint
    · have he := integral_map hΦm.aemeasurable hgm
      change (∫ ω, ‖gradient I.f (x (Φ ω).1 (Φ ω).2)‖ ^ 2 ∂(Q : Measure _)) ≤ p.eps
      rw [← he, hmapΦ]
      exact hu.2.2.2
  · intro p hp
    rfl


end OracleTemplate.MaleniaUniform
