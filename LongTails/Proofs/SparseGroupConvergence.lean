import LongTails.Proofs.SparseGroupAccuracy
import LongTails.Proofs.SparseGroupExecution
import LongTails.Proofs.SparseGroupConcentration
import LongTails.Proofs.SparseGroupBudget

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.SparseGroupConvergence

open OracleTemplate LongTails.Setups.OptimumGapGroupDro
open LongTails.Algorithms.SparseGroupSampling
open SparseGroupAccuracy SparseGroupExecution SparseGroupConcentration SparseGroupBudget

noncomputable def sampleBudget (p : Params) : ℕ :=
  Nat.ceil (512 * (p.data.d + 1 : ℝ) ^ 2 * confidenceLog p.data *
    ∑ i, 1 / max (p.gaps i) p.data.ε ^ 2)

noncomputable def horizon (q : Public) : ℕ := Nat.ceil (Real.exp (4 * confidenceLog q))

lemma accuracy_on_confidence (p : Params) (hp : spec.valid p)
    (model : ProbabilityMeasure (Rows p.data)) (ω : Reservoir p.data)
    (xstar : Space p.data.d) (hxstar : xstar ∈ p.data.domain)
    (hmin : IsMinOn (objective p.data model) p.data.domain xstar)
    (hgap : ∀ i, p.gaps i ≤ objective p.data model xstar - risk p.data model i xstar)
    (hconf : Confidence p.data model (horizon p.data) ω) :
    objective p.data model (output p.data (process p.data (fun _ => ω) (sampleBudget p)).1) -
      objective p.data model xstar ≤ p.data.ε := by
  rcases hp with ⟨hR, hG, hε, hε1, hδ, hδ4, hx0, _, hQ, hbound, hm, hconv, hb, hl, hΔ⟩
  let q := p.data
  let N := sampleBudget p
  let M : Fin q.K → ℝ := fun i =>
    128 * (q.d + 1 : ℝ) ^ 2 * confidenceLog q / max (p.gaps i) q.ε ^ 2
  have hK : (1 : ℝ) ≤ q.K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q.K)
  have hs : (1 : ℝ) ≤ q.d + 1 := by have := Nat.cast_nonneg (α := ℝ) q.d; linarith
  have hlogs := log_scales q hR hG hε hε1 hδ hδ4
  have hL : 0 ≤ confidenceLog q := by linarith [hlogs.1]
  have hNT : N ≤ horizon q := budget_le_horizon p.gaps (q.d + 1 : ℝ) q.ε
    (confidenceLog q) hK hs hε hε1 hΔ hlogs.1 hlogs.2.1
  have hcertificate (k : ℕ) (hk : k ≤ N) :=
    state_certificate q model (process q (fun _ => ω) k).1 ω xstar p.gaps hε hG hx0
      hbound hQ hm hconv hb hl hxstar hmin hgap (process_totals q ω k)
      (fun i h => hconf i h ((process q (fun _ => ω) k).1.1 i)
        ((process_count_le_clock q _ k i).trans (hk.trans hNT)))
  have hcap : ∀ k < N, (process q (fun _ => ω) k).1.2.2 = none →
      ((process q (fun _ => ω) k).1.1 (selectedGroup q (process q (fun _ => ω) k).1) : ℝ) ≤
        M (selectedGroup q (process q (fun _ => ω) k).1) := by
    intro k hk hnone
    exact uncertified_selected_count q _ p.gaps hε (fun i => (hΔ i).1) hL
      (process_none_uncertified q _ k hε hε1 hnone) (hcertificate k hk.le).1
  have hM : ∀ i, 0 ≤ M i := by intro i; dsimp [M]; positivity
  have hdom : (∑ i, (M i + 1)) < N :=
    budget_dominates_counts p.gaps (q.d + 1 : ℝ) q.ε (confidenceLog q) hK hs hε hε1 hΔ hlogs.1
  have hcert := process_certified_of_budget q (fun _ => ω) M hM N hcap hdom
  rw [process_output_primal]
  exact certified_gap_le q _ p.gaps _ hε (fun i => (hΔ i).1) hcert (hcertificate N le_rfl).2

lemma confidence_failure_probability (p : Params) (hp : spec.valid p)
    (model : ProbabilityMeasure (Rows p.data)) (P : ProbabilityMeasure (Reservoir p.data))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir p.data) => ω k) (model : Measure _) (P : Measure _)) :
    (P : Measure _).real {ω | ¬ Confidence p.data model (horizon p.data) ω} ≤ p.data.δ := by
  rcases hp with ⟨hR, hG, hε, hε1, hδ, hδ4, hx0, _, _, hbound, hm, _, hb, _, _⟩
  let q := p.data
  have hlogs := log_scales q hR hG hε hε1 hδ hδ4
  have hL : 0 ≤ confidenceLog q := by linarith [hlogs.1]
  have hmesh := SparseGroupGeometry.primalMesh_valid q hε hG hx0 hbound
  have htail := confidence_failure_le q model P hIID (horizon q)
    (fun h => hmesh.2.2.1 h.val h.property) hm hb hL
  have hK : (q.K : ℝ) ≤ Real.exp (confidenceLog q) := by
    apply le_trans _ hlogs.2.1
    apply (le_div_iff₀ hε).mpr
    have hs : (1 : ℝ) ≤ q.d + 1 := by have := Nat.cast_nonneg (α := ℝ) q.d; linarith
    have hk : (0 : ℝ) ≤ q.K := Nat.cast_nonneg _
    nlinarith
  have hM := mesh_card_le_exp_log q hR hG hε hε1 hδ hδ4 hx0 hbound
  exact htail.trans (horizon_confidence_bound (confidenceLog q) q.δ q.K (primalMesh q).card
    hlogs.1 hδ hK hM hlogs.2.2)

lemma measurable_process_objective (q : Public) (model : ProbabilityMeasure (Rows q))
    (hm : Measurable (Function.uncurry q.loss)) (n : ℕ) :
    Measurable (fun ξ : ℕ → Reservoir q => objective q model (output q (process q ξ n).1)) := by
  have he : (fun ξ : ℕ → Reservoir q => objective q model (output q (process q ξ n).1)) =
      (fun ξ => objective q model (primalChoice q (process q ξ n).1).val) := by
    funext ξ
    rw [process_output_primal]
  rw [he]
  exact (measurable_of_countable (fun h : PrimalIndex q => objective q model h.val)).comp
    ((SparseGroupChoices.measurable_primalChoice q).comp
      (measurable_fst.comp (measurable_process q hm n)))

lemma joint_failure_probability (p : Params) (hp : spec.valid p)
    (model : ProbabilityMeasure (Rows p.data)) (P : ProbabilityMeasure (Reservoir p.data))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir p.data) => ω k) (model : Measure _) (P : Measure _))
    (xstar : Space p.data.d) (hxstar : xstar ∈ p.data.domain)
    (hmin : IsMinOn (objective p.data model) p.data.domain xstar)
    (hgap : ∀ i, p.gaps i ≤ objective p.data model xstar - risk p.data model i xstar) :
    ((Measure.dirac ()).prod ((P : Measure _).map (fun ω => fun _ : ℕ => ω)))
      {seed : Unit × (ℕ → Reservoir p.data) |
        p.data.ε < objective p.data model (output p.data (process p.data seed.2 (sampleBudget p)).1) -
          objective p.data model xstar} ≤ ENNReal.ofReal p.data.δ := by
  have hm := hp.2.2.2.2.2.2.2.2.2.2.1
  have hobj := measurable_process_objective p.data model hm (sampleBudget p)
  have hbad : MeasurableSet {seed : Unit × (ℕ → Reservoir p.data) |
        p.data.ε < objective p.data model (output p.data (process p.data seed.2 (sampleBudget p)).1) -
          objective p.data model xstar} :=
    measurableSet_lt measurable_const ((hobj.comp measurable_snd).sub_const _)
  have hdiag : Measurable (fun ω : Reservoir p.data => fun _ : ℕ => ω) := by fun_prop
  rw [Measure.dirac_prod, Measure.map_map measurable_prodMk_left hdiag,
    Measure.map_apply (measurable_prodMk_left.comp hdiag) hbad]
  have hsub : (Prod.mk () ∘ (fun ω : Reservoir p.data => fun _ : ℕ => ω)) ⁻¹'
      {seed : Unit × (ℕ → Reservoir p.data) |
        p.data.ε < objective p.data model (output p.data (process p.data seed.2 (sampleBudget p)).1) -
          objective p.data model xstar} ⊆
      {ω | ¬ Confidence p.data model (horizon p.data) ω} := by
    intro ω hbad hconf
    exact (not_lt_of_ge (accuracy_on_confidence p hp model ω xstar hxstar hmin hgap hconf)) hbad
  apply (measure_mono hsub).trans
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (confidence_failure_probability p hp model P hIID)

lemma reservoir_successful (p : Params) (hp : spec.valid p)
    (model : ProbabilityMeasure (Rows p.data)) (P : ProbabilityMeasure (Reservoir p.data))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ω : Reservoir p.data) => ω k) (model : Measure _) (P : Measure _))
    (xstar : Space p.data.d) (hxstar : xstar ∈ p.data.domain)
    (hmin : IsMinOn (objective p.data model) p.data.domain xstar)
    (hgap : ∀ i, p.gaps i ≤ objective p.data model xstar - risk p.data model i xstar) :
    spec.successful p model
      (fun seed : (algorithm p.data).Seed × (ℕ → Reservoir p.data) =>
        execute (reservoirOracle p.data P) (algorithm p.data) (fun _ => sampleBudget p) seed.1 seed.2)
      ⟨(Measure.dirac ()).prod ((P : Measure (Reservoir p.data)).map (fun ω : Reservoir p.data => fun _ : ℕ => ω)), by dsimp only [algorithm]; infer_instance⟩ := by
  have he : (fun seed : (algorithm p.data).Seed × (ℕ → Reservoir p.data) =>
      execute (reservoirOracle p.data P) (algorithm p.data) (fun _ => sampleBudget p) seed.1 seed.2) =
      (fun seed : Unit × (ℕ → Reservoir p.data) => output p.data (process p.data seed.2 (sampleBudget p)).1) := by
    funext seed
    obtain ⟨u, ξ⟩ := seed
    cases u
    exact execute_eq_process p.data P ξ (sampleBudget p)
  rw [he]
  rcases hp with ⟨hR, hG, hε, hε1, hδ, hδ4, hx0, hcompact, hQ, hbound, hm, hconv, hb, hl, hΔ⟩
  refine ⟨?_, ?_, xstar, hxstar, hmin, ?_⟩
  · exact (SparseGroupChoices.measurable_output p.data).comp
      ((measurable_fst.comp (measurable_process p.data hm (sampleBudget p))).comp measurable_snd)
  · intro seed
    exact output_feasible p.data hε hG hx0 hbound _
  · exact joint_failure_probability p
      ⟨hR, hG, hε, hε1, hδ, hδ4, hx0, hcompact, hQ, hbound, hm, hconv, hb, hl, hΔ⟩
      model P hIID xstar hxstar hmin hgap

end LongTails.Proofs.SparseGroupConvergence
