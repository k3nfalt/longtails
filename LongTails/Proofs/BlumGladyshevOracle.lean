import LongTails.Proofs.BlumGladyshevMoments
import LongTails.Proofs.AdaptiveIID

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Setups.TerminalClippingConvex (Public Query Instance)
open LongTails.Proofs.BlumGladyshevValley LongTails.Proofs.BlumGladyshevTesting
open LongTails.Proofs.PolynomialMixingLowerBound (integrable_two_atoms)
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BlumGladyshevHardInstance

abbrev E (p : Public) := LongTails.Setups.TerminalClippingConvex.Vector p.d

noncomputable def responses (p : Public) (e w : E p) (q : unitInterval) :
    Query p → Bool → E p
  | .subgradient x, z => field p e w q x z
  | .projection x, _ => x

noncomputable def oracle (p : Public) (e w : E p) (q : unitInterval) :=
  CountdownMarkov.sampledOracle (responses p e w q) (stream q)

noncomputable def instanceOf (p : Public) (e w : E p) : Instance p :=
  ⟨objective p e w, Set.univ⟩

lemma objective_nonneg (p : Public) (hε : 0 < p.ε) (e w x : E p) : 0 ≤ objective p e w x :=
  add_nonneg (mul_nonneg (by positivity) (valley_nonneg _)) (mul_nonneg (by positivity) (valley_nonneg _))

lemma objective_minimum (p : Public) (hε : 0 < p.ε) (hR : 0 < p.R)
    {e w : E p} (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (hew : ⟪e,w⟫ = 0) :
    IsMinOn (objective p e w) Set.univ (point p e w) := by
  intro x _
  change objective p e w (point p e w) ≤ objective p e w x
  obtain ⟨h₁,h₂⟩ := point_zero p hR he hw hew
  simpa only [objective, h₁, h₂, add_zero] using objective_nonneg p hε e w x

lemma model_admissible (p : Public) (hG : 0 < p.G) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hscale : 65536*p.ε ≤ p.G*p.R) {e w : E p} (he : ‖e‖ = 1) (hw : ‖w‖ = 1)
    (hew : ⟪e,w⟫ = 0) (q : unitInterval) (hqeq : (q : ℝ) = BlumGladyshevMask.probability p.G p.B p.R p.ε) :
    LongTails.Setups.InterpolatedDistanceGrowingSubgradient.spec.admissible p
      (instanceOf p e w) (oracle p e w q) := by
  have hq : 0 < (q:ℝ) := hqeq ▸ (BlumGladyshevMask.mask_bounds hG hR hε hscale).1
  have hdist := point_radius p hR.le he hw
  have hmin := objective_minimum p hε hR he hw hew
  have hi {F : Type} [NormedAddCommGroup F] (f : Bool → F) : Integrable f (marginal q : Measure Bool) :=
    integrable_two_atoms _ _ (measurableSet_singleton _) (measurableSet_singleton _) q f
  constructor
  · refine ⟨Bool, inferInstance, ?_⟩
    dsimp only [Setups.DistanceGrowingSubgradient.withSamples, Setups.TerminalClippingConvex.spec]
    refine ⟨field p e w q, id, marginal q, stream q,
      OracleTemplate.StochasticGeneralized.infinitePi_iid (marginal q : Measure Bool), ?_, convex_univ, isClosed_univ,
      Set.mem_univ _, ?_, ?_, ⟨_, Set.mem_univ _, hmin, hdist⟩, measurable_id,
      fun x => Set.mem_univ _, ?_, field_measurable _ _ _ _, fun x _ => hi _, ?_,
      fun x _ => hi _, fun x _ => field_second p he hw hG hR hε hscale q hqeq x⟩
    · unfold oracle CountdownMarkov.sampledOracle
      congr 1
      funext h query z
      obtain ⟨_,x⟩ := query
      cases x <;> rfl
    · exact (ridge_convex (a := 512*p.ε) (by positivity) _ _ _).add
        (ridge_convex (a := 512*p.ε) (by positivity) _ _ _)
    · exact ((ridge_smooth _ _ _ _).continuous.add (ridge_smooth _ _ _ _).continuous).measurable
    · intro x y _
      simp
    · intro x _ y _
      rw [field_mean _ _ _ _ _ hq]
      have h₁ := ridge_support (a := 512*p.ε) (by positivity) (1/2) (axis p e) p.x0 x y
      have h₂ := ridge_support (a := 512*p.ε) (by positivity) 0 (axis p (e+w)) p.x0 x y
      change objective p e w x - objective p e w y ≤ _
      unfold objective common tilt baseField tiltField
      simp only [inner_add_left, inner_sub_right] at *
      linarith only [h₁,h₂]
  · refine ⟨rfl, point p e w, baseField p e p.x0, fun _ z => loss p e w q z,
      hdist, fun _ z => ⟨loss_convex p hε.le e w hq z, loss_smooth _ _ _ _ _,
        loss_minimum p hε.le hR he hw hew hq z⟩, ?_, ?_, ?_⟩
    · intro k z
      change gradient (loss p e w q z) p.x0 = _
      rw [(field_gradient _ _ _ _ _ _).gradient, anchor_field]
    · intro h x z
      exact (field_gradient _ _ _ _ _ _).gradient.symm
    · intro k x
      let F := fun z => loss p e w q z x
      have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => (marginal q : Measure Bool)) k
      have hf : Measurable F := Measurable.of_discrete
      have heq : (∫ ξ : ℕ → Bool, F (ξ k) ∂(stream q : Measure _)) =
          ∫ z, F z ∂(marginal q : Measure Bool) := by
        rw [← hmp.map_eq]
        exact (integral_map hmp.measurable.aemeasurable hf.aestronglyMeasurable).symm
      exact ⟨hmp.integrable_comp_of_integrable (hi F), (heq.trans (loss_mean p e w x q hq)).symm⟩

end LongTails.Proofs.BlumGladyshevHardInstance
