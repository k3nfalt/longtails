import LongTails.Setups.CompositionalEntropicRisk
import LongTails.Proofs.Execution
import LongTails.Proofs.ScentConvergence

open MeasureTheory Real

namespace OracleTemplate.Scent.ScentCompositionalEntropicRisk

open LongTails.Setups.CompositionalEntropicRisk
open OracleTemplate.Scent

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => (q.B + 1) * ⌈(64 * q.κ * q.G ^ 2 * q.R ^ 2 * (1 + Real.exp (q.c1 - q.c0) * q.ε) + 32 * min (2 * Real.exp (q.c1 - q.c0) * q.σ ^ 2) (Real.exp (2 * (q.c1 - q.c0)) * q.G ^ 2) * q.R ^ 2 * (1 + q.ε) / q.B + 8 * q.n * Real.exp (q.c1 - q.c0) * (1 + 64 * (1 + (q.c1 - q.c0)) * (q.κ - 1)) * (1 + q.ε) / q.B) / q.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.CompositionalEntropicRisk.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨fun q => scent q (stepSize q) (dualStep q) (horizon q), ?_, fun _ _ => trivial⟩
  rintro q ⟨hB, hc, hG, hκ, hσ, hR, hε⟩ I O ⟨projection, P, hIID, hO, hconv, hclosed, hw0, hpm, hpmem,
    hpineq, hms, hmg, hsub, hbd, hgi, hgs, hk, hsg, wstar, hwmem, hwmin, hdist⟩
  have hlaw : (P : Measure _) = PP I := by
    have h := hIID.independent.map_fun_eq_infinitePi_map hIID.measurable
    change (P : Measure (ℕ → Seed q)).map id = _ at h
    simpa only [hIID.marginal, Measure.map_id] using h
  have hlaw' : P = ⟨PP I, inferInstance⟩ := Subtype.ext hlaw
  subst hO
  subst hlaw'
  have h : SysHyp I projection wstar :=
    ⟨hconv, hclosed, hw0, hpm, hpmem, hpineq,
      fun i => ⟨hms i, hmg i, hsub i, hbd i, hgi i, hgs i, hk i, hsg i⟩,
      hB, hc, hG.le, hκ, hσ, hwmem, hwmin⟩
  set T := horizon q with hTdef
  set η := stepSize q with hηdef
  set α := dualStep q with hαdef
  obtain ⟨hTpos, hTge⟩ := horizon_bound q hB hc hG hκ hσ hR hε
  have hBr : (0 : ℝ) < q.B := by exact_mod_cast hB
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hV : 0 ≤ V1 q := by unfold V1; exact le_min (by positivity) (by positivity)
  have hΔ : 0 ≤ q.c1 - q.c0 := sub_nonneg.mpr hc
  have hκ' : 0 ≤ q.κ - 1 := sub_nonneg.mpr hκ
  have hL1 : 0 < V1 q / q.B + 2 * q.κ * q.G ^ 2 := by positivity
  have hL2 : 0 < V1 q / q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 := by positivity
  have hK : 0 ≤ 4 * (q.κ - 1) * exp q.c1 := by positivity
  have hC : 0 ≤ 2 * (1 + (q.c1 - q.c0)) := by positivity
  have hD : 0 ≤ (q.n : ℝ) * exp (-q.c0) := by positivity
  obtain ⟨hη, hα, hαe, hqq, hacc⟩ := tuning hε hL1 hL2 hK hC (exp_pos q.c1) hD le_rfl hR hBr hTr hTge
  have eη : (1 / (8 * (V1 q / q.B + 2 * q.κ * q.G ^ 2) / q.ε +
      4 * (V1 q / q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2))) = η := rfl
  have eα : (1 / (exp q.c1 + 8 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * exp q.c1) / q.ε +
      4 * (2 * (1 + (q.c1 - q.c0))) * (4 * (q.κ - 1) * exp q.c1))) = α := rfl
  rw [eη] at hη hqq hacc
  rw [eα] at hα hαe hqq hacc
  have hexec : ∀ seed : Unit × (ℕ → Seed q),
      execute (sampleOracle I projection ⟨PP I, inferInstance⟩) (scent q η α T) (fun _ => budget q 0)
        seed.1 seed.2 = average I projection η α seed.2 T := by
    intro seed
    have hb : (fun _ : Fin 1 => budget q 0) = fun _ => T * (q.B + 1) := by
      funext _
      show (q.B + 1) * horizon q = T * (q.B + 1)
      rw [hTdef, Nat.mul_comm]
    rw [hb]
    exact execute_scent I projection η α _ seed.2 T hB hTpos seed.1
  show spec.successful q I
    (fun seed : Unit × (ℕ → Seed q) =>
      execute (sampleOracle I projection ⟨PP I, inferInstance⟩) (scent q η α T) (fun _ => budget q 0)
        seed.1 seed.2)
    ⟨(Measure.dirac ()).prod (PP I), inferInstance⟩
  have hres : (fun seed : Unit × (ℕ → Seed q) =>
      execute (sampleOracle I projection ⟨PP I, inferInstance⟩) (scent q η α T) (fun _ => budget q 0)
        seed.1 seed.2) = fun seed => average I projection η α seed.2 T := funext hexec
  rw [hres]
  obtain ⟨hint, hgap⟩ := expected_gap I η α h hα (ρ := 1) (by linarith) hη hB hTpos
    (by
      calc η * V1 q / q.B + 4 * η * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 +
          (1 + 1) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + 1) * (q.κ - 1) * exp q.c1)
          = η * (V1 q / q.B + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2) +
            2 * (1 + (q.c1 - q.c0)) * α * (4 * (q.κ - 1) * exp q.c1) := by ring
        _ ≤ 1 / 2 := hqq)
  refine ⟨(measurable_average I η α h T).comp measurable_snd, fun ω => average_mem I η α h hTpos ω.2,
    wstar, hwmem, hwmin, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := PP I)).integrable_comp_of_integrable hint
  · have hsnd : ∫ seed : Unit × (ℕ → Seed q),
        (fun ξ => objective I (average I projection η α ξ T) - objective I wstar) seed.2
          ∂((Measure.dirac ()).prod (PP I)) =
        ∫ ξ, objective I (average I projection η α ξ T) - objective I wstar ∂(PP I) := by
      have := integral_fun_snd (μ := (Measure.dirac () : Measure Unit)) (ν := PP I)
        (fun ξ => objective I (average I projection η α ξ T) - objective I wstar)
      simpa using this
    show ∫ seed : Unit × (ℕ → Seed q),
        (fun ξ => objective I (average I projection η α ξ T) - objective I wstar) seed.2
          ∂((Measure.dirac ()).prod (PP I)) ≤ q.ε
    rw [hsnd]
    have hd2 : ‖q.w0 - wstar‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    have hmono : ‖q.w0 - wstar‖ ^ 2 / (η * T) ≤ q.R ^ 2 / (η * T) :=
      div_le_div_of_nonneg_right hd2 (by positivity)
    have e : 2 * (η * V1 q / q.B + 2 * η * q.κ * q.G ^ 2 +
        (1 + 1) * (1 + (q.c1 - q.c0)) * α * (2 * (1 + 1) * (q.κ - 1) * exp q.c1)) =
        2 * (η * (V1 q / q.B + 2 * q.κ * q.G ^ 2) + 2 * (1 + (q.c1 - q.c0)) * α * (4 * (q.κ - 1) * exp q.c1)) := by
      ring
    have e2 : 2 * q.n * exp (-q.c0) / (α * T * q.B) = 2 * (q.n * exp (-q.c0)) / (α * T * q.B) := by ring
    linarith [hgap, hacc, hmono, e, e2]

end OracleTemplate.Scent.ScentCompositionalEntropicRisk
