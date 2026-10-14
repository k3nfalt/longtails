import tutorial.ToBeDiscovered.Proofs.SgdOutput
import tutorial.ToBeDiscovered.Proofs.RandomSgdExecution
import tutorial.ToBeDiscovered.Proofs.SgdBudget

open MeasureTheory

namespace OracleTemplate.StochasticNonconvex

open LongTails.Setups.StochasticSmoothNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈4 * p.L * p.Δ / p.ε ^ 2 + 8 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4⌉₊ + 1

theorem result : Convergence LongTails.Setups.StochasticSmoothNonconvex.spec budget := by
  refine ⟨tunedSgd, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hΔ, hσ, hε⟩ f O ⟨g, p, P, hiid, rfl, hg, hlip, ⟨lower, hb, hgap⟩, ho⟩
  let η := 1 / (q.L + 2 * q.L * q.σ ^ 2 / q.ε ^ 2)
  let K := ⌈4 * q.L * q.Δ / q.ε ^ 2 + 8 * q.L * q.Δ * q.σ ^ 2 / q.ε ^ 4⌉₊ + 1
  have ht := tuning (σ := q.σ) hL hΔ hε
  let μ := (PMF.uniformOfFintype (Fin K)).toMeasure
  let Q := Measure.pi (fun _ : Fin K => (p : Measure q.Ω))
  let out := fun z : Fin K × (Fin K → q.Ω) => selected g η K q.x0 z.2 z.1
  have hr := selected_rate hL ht.1 ht.2.1 hg hlip hb ho K q.x0
  have hp := iid_prefix hiid K
  have hmap : MeasurePreserving
      (fun z : Fin K × (ℕ → q.Ω) => (z.1, fun i : Fin K => z.2 i.val))
      (μ.prod (P : Measure _)) (μ.prod Q) :=
    (MeasurePreserving.id μ).prod hp
  let outStream := fun z : Fin K × (ℕ → q.Ω) => out (z.1, fun i => z.2 i.val)
  have hm : Measurable outStream := hr.1.comp hmap.measurable
  have hint : Integrable (fun z => ‖gradient f (outStream z)‖ ^ 2) (μ.prod (P : Measure _)) :=
    hmap.integrable_comp_of_integrable hr.2.1
  have he : (∫ z, ‖gradient f (outStream z)‖ ^ 2 ∂μ.prod (P : Measure _)) =
      (∫ z, ‖gradient f (out z)‖ ^ 2 ∂μ.prod Q) := by
    have hfun : Measurable (fun z => ‖gradient f (out z)‖ ^ 2) :=
      ((gradient_measurable hL.le hlip).comp hr.1).norm.pow_const 2
    rw [← hmap.map_eq, integral_map hmap.measurable.aemeasurable hfun.aestronglyMeasurable]
  have hacc : (∫ z, ‖gradient f (outStream z)‖ ^ 2 ∂μ.prod (P : Measure _)) ≤ q.ε ^ 2 := by
    rw [he]
    apply ht.2.2
    exact hr.2.2.trans (add_le_add hgap le_rfl)
  change spec.successful q f
    (fun z : Fin K × (ℕ → q.Ω) =>
      execute { Seed := fun _ => q.Ω
                law := P
                answer := fun _ (_, x) seed => g x seed }
        (randomSgd η K q.x0) (fun _ => K) z.1 z.2) _
  simp only [execute_randomSgd]
  exact ⟨hm, hint, hacc⟩

end OracleTemplate.StochasticNonconvex
