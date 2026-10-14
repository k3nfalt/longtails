import LongTails.Proofs.Execution
import LongTails.Proofs.LinearDecaySgdExpectation
import LongTails.Proofs.LinearDecaySgdExecution

open MeasureTheory

namespace OracleTemplate.SampledConvex

open LongTails.Setups.SampledSmoothConvex

noncomputable def horizon (q : spec.Params) : ℕ :=
  ⌈48 * q.L * q.R ^ 2 / q.ε + 324 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem convergence :
    Convergence spec (fun p _ => horizon p) := by
  apply convergence_of_public_budget (S := spec) horizon
  refine ⟨fun q => linearDecaySgd (scale q.L q.R q.σ (horizon q)) (horizon q) q.x0, ?_,
    fun q hq => ⟨_, _, by dsimp [scale]; positivity [hq.1, hq.2.1, hq.2.2.1], rfl⟩⟩
  rintro q ⟨hL, hR, hσ, hε⟩ M O ⟨law, h_samples, hO, hmeas, hconv, hgrad, hlip, hint, xstar, hmin, hdist, hsqi, hsq⟩
  have hlaw : (law : Measure _) = Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)) := by
    have h := h_samples.independent.map_fun_eq_infinitePi_map h_samples.measurable
    change (law : Measure (ℕ → q.Ξ)).map id = _ at h
    simpa only [h_samples.marginal, Measure.map_id] using h
  have hlaw' : law = ⟨Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)), inferInstance⟩ :=
    Subtype.ext hlaw
  rw [hlaw'] at hO
  set T := horizon q
  set η := scale q.L q.R q.σ T
  set P := Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ))
  have hO' : O = sampleOracle M.law M.grad := hO
  subst hO'
  have hexec : ∀ ξ : ℕ → q.Ξ, execute (sampleOracle M.law M.grad) (linearDecaySgd η T q.x0) (fun _ => T) () ξ =
      path M.grad η T q.x0 ξ T := fun ξ => execute_linearDecaySgd M.law M.grad η T q.x0 T ξ
  have hpm : Measurable (fun ξ : ℕ → q.Ξ => path M.grad η T q.x0 ξ T) :=
    measurable_path hmeas η T q.x0 T
  change spec.successful q M
      (fun seed : Unit × (ℕ → q.Ξ) =>
        (execute (sampleOracle M.law M.grad) (linearDecaySgd η T q.x0) (fun _ => T) seed.1 seed.2))
      ⟨(Measure.dirac ()).prod P, inferInstance⟩
  have hres : (fun seed : Unit × (ℕ → q.Ξ) =>
      (execute (sampleOracle M.law M.grad) (linearDecaySgd η T q.x0) (fun _ => T) seed.1 seed.2)) =
      fun seed => path M.grad η T q.x0 seed.2 T := by
    funext ⟨⟨⟩, ξ⟩
    exact (hexec ξ)
  rw [hres]
  refine ⟨hpm.comp measurable_snd, xstar, hmin, ?_⟩
  · show Integrable (fun seed : Unit × (ℕ → q.Ξ) =>
        (fun ξ => objective M (path M.grad η T q.x0 ξ T) - objective M xstar) seed.2)
        ((Measure.dirac ()).prod P) ∧
      ∫ seed, (fun ξ => objective M (path M.grad η T q.x0 ξ T) - objective M xstar) seed.2
        ∂((Measure.dirac ()).prod P) ≤ q.ε
    have hsnd : ∫ seed : Unit × (ℕ → q.Ξ),
        (fun ξ => objective M (path M.grad η T q.x0 ξ T) - objective M xstar) seed.2
          ∂((Measure.dirac ()).prod P) =
        ∫ ξ, objective M (path M.grad η T q.x0 ξ T) - objective M xstar ∂P := by
      have := integral_fun_snd (μ := (Measure.dirac () : Measure Unit)) (ν := P)
        (fun ξ => objective M (path M.grad η T q.x0 ξ T) - objective M xstar)
      simpa using this
    rw [hsnd]
    rcases eq_or_lt_of_le hR with hR0 | hRpos
    · have hx : q.x0 = xstar := by
        have : ‖q.x0 - xstar‖ ≤ 0 := by rw [hR0]; exact hdist
        exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
      have hη0 : η = 0 := by simp [η, scale, ← hR0]
      have hp : ∀ ξ : ℕ → q.Ξ, path M.grad η T q.x0 ξ T = xstar := by
        intro ξ; rw [hη0, path_zero_scale, hx]
      simp only [hp, sub_self]
      refine ⟨integrable_const _, ?_⟩
      simp only [integral_const, smul_zero]
      exact hε.le
    · have hTb : 48 * q.L * q.R ^ 2 / q.ε + 324 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 ≤ (T : ℝ) :=
        Nat.le_ceil _
      obtain ⟨hη, hLη, hacc⟩ := tuning_bound hL hRpos hσ hε hTb
      have hηdef : η = q.R / (8 * q.L * q.R + q.σ * Real.sqrt T) := rfl
      rw [← hηdef] at hη hLη hacc
      have hTpos : 0 < T := by
        have hA : 0 < 48 * q.L * q.R ^ 2 / q.ε := by positivity
        have hB : 0 ≤ 324 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 := by positivity
        exact_mod_cast (show (0 : ℝ) < T by linarith)
      have hyp : Hyp (M.law : Measure q.Ξ) M.loss M.grad q.L q.σ xstar :=
        ⟨hL, hmeas, hconv, hgrad, hlip, hint, hmin, hsqi, hsq⟩
      obtain ⟨hi, hb⟩ := hyp.expected_gap hη hLη hTpos q.x0
      refine ⟨(measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi, ?_⟩
      have hd2 : ‖q.x0 - xstar‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
      have hmono : 3 * ‖q.x0 - xstar‖ ^ 2 / (η * T) ≤ 3 * q.R ^ 2 / (η * T) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      exact le_trans hb (by linarith)

end OracleTemplate.SampledConvex
