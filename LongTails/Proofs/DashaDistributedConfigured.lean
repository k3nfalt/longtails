import LongTails.Algorithms.DashaDistributedParameters
import LongTails.Proofs.DashaDistributedCapacity
import LongTails.Proofs.DashaScalingConvergence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedConfigured

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaDistributedParameters
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedCapacity

variable {p : Params}

lemma configured_transport (c : Choice p) (initializer : Option (Choice p))
    (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) : TransportExact (config p c initializer) f seed := by
  apply transportExact (config p c initializer) rfl hε hL hH hG0 f hs hG
  · rfl
  · rfl
  · rfl

lemma configured_finiteEvents (c : Choice p) (initializer : Option (Choice p))
    (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG0 : 0 ≤ p.G)
    (hpos : ∀ i, 0 < p.h i) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (selected : Fin (roundCount p c initializer)) :
    FiniteEvents (system p f) (algorithm p (config p c initializer)) (timeBudget p (config p c initializer))
      ((selected, seed), ()) :=
  DashaDistributedTermination.finiteEvents _ f seed selected
    (configured_transport c initializer hε hL hH hG0 f hs hG seed) hpos

lemma configured_execute (c : Choice p) (initializer : Option (Choice p))
    (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG0 : 0 ≤ p.G)
    (hpos : ∀ i, 0 < p.h i) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (selected : Fin (roundCount p c initializer)) :
    execute (system p f) (algorithm p (config p c initializer)) (timeBudget p (config p c initializer))
      (selected, seed) () = idealOutput p (config p c initializer) f (selected, seed) :=
  DashaDistributedTermination.execute_eq_ideal _ f seed selected
    (configured_transport c initializer hε hL hH hG0 f hs hG seed) hpos

lemma ideal_accuracy (c : Choice p) (initializer : Option (Choice p))
    (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x) (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    Measurable (idealOutput p (config p c initializer) f) ∧
    Integrable (fun seed => ‖gradient (objective p f) (idealOutput p (config p c initializer) f seed)‖ ^ 2)
      ((algorithm p (config p c initializer)).law : Measure (algorithm p (config p c initializer)).Seed) ∧
    (∫ seed : (algorithm p (config p c initializer)).Seed, ‖gradient (objective p f) (idealOutput p (config p c initializer) f seed)‖ ^ 2
      ∂((algorithm p (config p c initializer)).law : Measure (algorithm p (config p c initializer)).Seed)) ≤ p.ε ^ 2 := by
  cases initializer with
  | none =>
      have ho : idealOutput p (config p c none) f = output p c f := by
        funext seed
        exact congrArg Iterate.point (idealTrajectory_none (config p c none) f seed.2 rfl seed.1.val)
      rw [ho]
      exact DashaScalingConvergence.dense_output_accuracy c hε hL hH f hg hlip hs lower hlower hgap
  | some c₀ =>
      have ho : idealOutput p (config p c (some c₀)) f = sparseOutput p c c₀ f := by
        funext seed
        exact congrArg Iterate.point (idealTrajectory_some (config p c (some c₀)) f seed.2 c₀ rfl seed.1.val)
      rw [ho]
      exact DashaScalingConvergence.sparse_output_accuracy c c₀ hε hL hH f hg hlip hs hG lower hlower hgap

lemma configured_success (c : Choice p) (initializer : Option (Choice p))
    (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat) (hG0 : 0 ≤ p.G)
    (hpos : ∀ i, 0 < p.h i) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x) (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    spec.successful p f
      (fun ω => execute (system p f) (algorithm p (config p c initializer)) (timeBudget p (config p c initializer)) ω.1 ω.2)
      (law (system p f) (algorithm p (config p c initializer))) := by
  have he : (fun ω : (algorithm p (config p c initializer)).Seed × Unit =>
      execute (system p f) (algorithm p (config p c initializer)) (timeBudget p (config p c initializer)) ω.1 ω.2) =
      fun ω => idealOutput p (config p c initializer) f ω.1 := by
    funext ω
    rcases ω with ⟨⟨selected, seed⟩, oracleSeed⟩
    cases oracleSeed
    exact configured_execute c initializer hε hL hH hG0 hpos f hs hG seed selected
  change Measurable _ ∧ Integrable _ _ ∧ _
  erw [he]
  obtain ⟨hm, hi, hb⟩ := ideal_accuracy c initializer hε hL hH f hg hlip hs hG lower hlower hgap
  refine ⟨hm.comp measurable_fst, ?_, ?_⟩
  · exact hi.comp_fst ((system p f).law : Measure (system p f).Seed)
  · change (∫ ω : (algorithm p (config p c initializer)).Seed × (system p f).Seed,
        ‖gradient (objective p f) (idealOutput p (config p c initializer) f ω.1)‖ ^ 2
        ∂(((algorithm p (config p c initializer)).law : Measure (algorithm p (config p c initializer)).Seed).prod ((system p f).law : Measure (system p f).Seed))) ≤ _
    have hprod := integral_fun_fst
      (μ := ((algorithm p (config p c initializer)).law : Measure (algorithm p (config p c initializer)).Seed))
      (ν := ((system p f).law : Measure (system p f).Seed))
      (fun seed : (algorithm p (config p c initializer)).Seed =>
        ‖gradient (objective p f) (idealOutput p (config p c initializer) f seed)‖ ^ 2)
    exact hprod.le.trans (by simpa using hb)

end LongTails.Proofs.DashaDistributedConfigured
