import LongTails.Proofs.Execution
import LongTails.Proofs.ProximalLinearDecayExpectation
import LongTails.Proofs.ProximalLinearDecayExecution

open MeasureTheory

namespace OracleTemplate.SampledComposite

open LongTails.Setups.SampledCompositeSmoothConvex
open OracleTemplate.SampledConvex (scale)

noncomputable def horizon (q : spec.Params) : ℕ :=
  ⌈72 * q.L * q.R ^ 2 / q.ε + 900 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 + 6 * q.Δ / q.ε⌉₊

theorem convergence :
    Convergence spec (fun p _ => 2 * horizon p) := by
  apply convergence_of_public_budget (S := spec) (fun p => 2 * horizon p)
  refine ⟨fun q => proximalLinearDecaySgd (scale q.L q.R q.σ (horizon q)) (horizon q) q.x0, ?_,
    fun q hq => ⟨_, _, by dsimp [scale]; positivity [hq.1, hq.2.1, hq.2.2.2.1], rfl⟩⟩
  rintro q ⟨hL, hR, hΔ, hσ, hε⟩ M O ⟨law, h_samples, hO, hmeas, hconv, hgrad, hlip, hint, hQ, hclosed,
    hψ, hlsc, hprox, hx0Q, xstar, hxQ, hmin, hdist, hgap, hgint, hvint, hvar⟩
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
  have hO' : O = compositeOracle M := hO
  subst hO'
  have hexec : ∀ ξ : ℕ → q.Ξ,
      execute (compositeOracle M) (proximalLinearDecaySgd η T q.x0) (fun _ => 2 * T) () ξ =
        path M.grad M.prox η T q.x0 ξ T :=
    fun ξ => execute_proximalLinearDecaySgd M η T q.x0 T ξ
  have hyp : Hyp (M.law : Measure q.Ξ) M.loss M.grad M.ψ M.Q M.prox q.L q.σ xstar :=
    ⟨hL, hmeas, hconv, hgrad, hlip, hint, hQ, hclosed, hψ, hlsc, hprox, hxQ, hmin, hgint, hvint, hvar⟩
  have hTb : 72 * q.L * q.R ^ 2 / q.ε + 900 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 + 6 * q.Δ / q.ε ≤ (T : ℝ) :=
    Nat.le_ceil _
  obtain ⟨hη, hLη, hacc⟩ := ptuning_bound hL hR hσ hΔ hε hTb
  have hηdef : η = q.R / (8 * q.L * q.R + q.σ * Real.sqrt T) := rfl
  rw [← hηdef] at hη hLη hacc
  have hTpos : 0 < T := by
    have hA : 0 < 72 * q.L * q.R ^ 2 / q.ε := by positivity
    have hB : 0 ≤ 900 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2 := by positivity
    have hC : 0 ≤ 6 * q.Δ / q.ε := by positivity
    exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hpm : Measurable (fun ξ : ℕ → q.Ξ => path M.grad M.prox η T q.x0 ξ T) :=
    measurable_path hyp hη T le_rfl
  change spec.successful q M
      (fun seed : Unit × (ℕ → q.Ξ) =>
        (execute (compositeOracle M) (proximalLinearDecaySgd η T q.x0)
          (fun _ => 2 * T) seed.1 seed.2))
      ⟨(Measure.dirac ()).prod P, inferInstance⟩
  have hres : (fun seed : Unit × (ℕ → q.Ξ) =>
      (execute (compositeOracle M) (proximalLinearDecaySgd η T q.x0)
        (fun _ => 2 * T) seed.1 seed.2)) =
      fun seed => path M.grad M.prox η T q.x0 seed.2 T := by
    funext ⟨⟨⟩, ξ⟩
    exact (hexec ξ)
  rw [hres]
  refine ⟨hpm.comp measurable_snd, xstar, hxQ, hmin, ?_⟩
  show Integrable (fun seed : Unit × (ℕ → q.Ξ) =>
      (fun ξ => objective M (path M.grad M.prox η T q.x0 ξ T) - objective M xstar) seed.2)
      ((Measure.dirac ()).prod P) ∧
    ∫ seed, (fun ξ => objective M (path M.grad M.prox η T q.x0 ξ T) - objective M xstar) seed.2
      ∂((Measure.dirac ()).prod P) ≤ q.ε
  have hsnd : ∫ seed : Unit × (ℕ → q.Ξ),
      (fun ξ => objective M (path M.grad M.prox η T q.x0 ξ T) - objective M xstar) seed.2
        ∂((Measure.dirac ()).prod P) =
      ∫ ξ, objective M (path M.grad M.prox η T q.x0 ξ T) - objective M xstar ∂P := by
    have := integral_fun_snd (μ := (Measure.dirac () : Measure Unit)) (ν := P)
      (fun ξ => objective M (path M.grad M.prox η T q.x0 ξ T) - objective M xstar)
    simpa using this
  rw [hsnd]
  have hgap' : total (M.law : Measure q.Ξ) M.loss M.ψ q.x0 - total (M.law : Measure q.Ξ) M.loss M.ψ xstar ≤
      q.Δ := hgap
  obtain ⟨hi, hb⟩ := expected_gap hyp hη hLη hx0Q hTpos hΔ hgap'
  have hobj : (fun ξ : ℕ → q.Ξ => objective M (path M.grad M.prox η T q.x0 ξ T) - objective M xstar) =
      fun ξ => total (M.law : Measure q.Ξ) M.loss M.ψ (path M.grad M.prox η T q.x0 ξ T) -
        total (M.law : Measure q.Ξ) M.loss M.ψ xstar := rfl
  rw [hobj]
  refine ⟨(measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi, ?_⟩
  have hd2 : ‖q.x0 - xstar‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hmono : 3 * ‖q.x0 - xstar‖ ^ 2 / (η * T) ≤ 3 * q.R ^ 2 / (η * T) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  exact le_trans hb (by linarith)

end OracleTemplate.SampledComposite
