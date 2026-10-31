import LongTails.Proofs.HessianAdaptiveCubicInvariants

namespace LongTails.Proofs.HessianAdaptiveCubicMeasurability

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicModel
open LongTails.Proofs.HessianAdaptiveCubicWeights
open LongTails.Proofs.HessianAdaptiveCubicInvariants

structure MeasurableState {X : Type*} [MeasurableSpace X] (p : Public) (s : X → State p.d) : Prop where
  iteration : Measurable (fun x => (s x).iteration)
  phase : Measurable (fun x => (s x).phase)
  weight : Measurable (fun x => (s x).weight)
  point : Measurable (fun x => (s x).point)
  dual : Measurable (fun x => (s x).dual)
  scale : Measurable (fun x => (s x).scale)
  modelGradient : Measurable (fun x => (s x).modelGradient)
  modelHessian : Measurable (fun x => (s x).modelHessian)
  trial : Measurable (fun x => (s x).trial)

variable {X : Type*} [MeasurableSpace X] (p : Public) (s : X → State p.d)

lemma measurable_center (hs : MeasurableState p s) : Measurable (fun x => center (s x)) := by
  have hi := hs.iteration
  have hw := hs.point
  have hz := hs.dual
  unfold center mixing
  fun_prop

lemma measurable_displacement (hs : MeasurableState p s) : Measurable (fun x => displacement (s x)) := by
  have hi := hs.iteration
  have hu := hs.trial
  have hz := hs.dual
  unfold displacement mixing
  fun_prop

lemma measurable_queryPoint (hs : MeasurableState p s) : Measurable (fun x => queryPoint (s x)) :=
  (measurable_center p s hs).add (measurable_displacement p s hs)

lemma measurable_quadraticDamping (hs : MeasurableState p s) :
    Measurable (fun x => quadraticDamping p (s x)) := by
  have hi := hs.iteration
  have hκ := hs.scale
  unfold quadraticDamping
  fun_prop

lemma measurable_damping (hs : MeasurableState p s) : Measurable (fun x => damping p (s x)) := by
  exact (measurable_quadraticDamping p s hs).add
    (hs.scale.mul (measurable_displacement p s hs).norm)

lemma measurable_increment (hs : MeasurableState p s) : Measurable (fun x => increment p (s x)) := by
  have hi := hs.iteration
  have hκ := hs.scale
  have hA := hs.weight
  have hτ := measurable_damping p s hs
  unfold increment mixing
  apply Measurable.ite (measurableSet_eq_fun hi measurable_const) <;> fun_prop

lemma measurable_residualWeight (hs : MeasurableState p s) :
    Measurable (fun x => residualWeight p (s x)) := by
  have hi := hs.iteration
  have hκ := hs.scale
  have ha := measurable_increment p s hs
  have hτ := measurable_damping p s hs
  unfold residualWeight mixing
  fun_prop

lemma measurable_primal (hs : MeasurableState p s) (hD : 0 < p.D)
    (hinv : ∀ x, Invariant p (s x))
    (H : X → Point p.d →L[ℝ] Point p.d) (hH : Measurable H) (hPSD : ∀ x, IsPSD (H x)) :
    Measurable (fun x => primal p (s x) (H x)) := by
  have hi := hs.iteration
  have hκ := hs.scale
  have hβ := measurable_quadraticDamping p s hs
  apply measurable_model_minimize p.C p.x0 _ _ _ _ _ hs.dual hs.modelGradient
  · unfold mixing
    fun_prop
  · unfold mixing
    fun_prop
  · unfold mixing
    fun_prop
  · exact fun x => isPSD_smul (hPSD x) (mixing_pos _).le
  · intro x
    have hα := mixing_pos (s x).iteration
    have hb := quadraticDamping_pos p (s x) hD (hinv x).scale (hinv x).iteration
    positivity
  · intro x
    have hk := (hinv x).scale
    positivity

lemma measurable_advance (hs : MeasurableState p s) (hD : 0 < p.D)
    (hinv : ∀ x, Invariant p (s x)) (g : X → Point p.d) (hg : Measurable g) :
    MeasurableState p (fun x => advance p (s x) (g x)) := by
  have hi := hs.iteration
  have hκ := hs.scale
  have hA := hs.weight
  have hw := hs.point
  have hu := hs.trial
  have hg0 := hs.modelGradient
  have hH := hs.modelHessian
  have ha := measurable_increment p s hs
  have hW := measurable_residualWeight p s hs
  have hd := measurable_displacement p s hs
  have heval : Continuous (fun z : (Point p.d →L[ℝ] Point p.d) × Point p.d => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hHs : Measurable (fun x => (s x).modelHessian (displacement (s x))) :=
    heval.measurable.comp (hH.prodMk hd)
  have hdual := measurable_model_minimize p.C p.x0 (fun x => (s x).dual) g
    (fun _ => 0) (fun x => (s x).scale / (2 * increment p (s x))) (fun _ => 0)
    hs.dual hg measurable_const (by fun_prop) measurable_const (fun _ => isPSD_zero)
    (fun x => by
      have hk := (hinv x).scale
      have hap := increment_pos p (s x) hD (hinv x).scale (hinv x).iteration (hinv x).weight_pos
      positivity) (fun _ => le_rfl)
  constructor
  · exact hi.add_const 1
  · exact measurable_const
  · exact hA.add ha
  · dsimp only [advance]
    fun_prop
  · exact hdual
  · dsimp only [advance]
    fun_prop
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const

lemma measurable_modelState (hs : MeasurableState p s) (hD : 0 < p.D)
    (hinv : ∀ x, Invariant p (s x)) (g : X → Point p.d)
    (H : X → Point p.d →L[ℝ] Point p.d) (hg : Measurable g) (hH : Measurable H)
    (hPSD : ∀ x, IsPSD (H x)) : MeasurableState p (fun x => modelState p (s x) (g x) (H x)) := by
  let s1 : X → State p.d := fun x => { s x with phase := 1, modelGradient := g x }
  have hm : MeasurableState p s1 :=
    ⟨hs.iteration, measurable_const, hs.weight, hs.point, hs.dual, hs.scale,
      hg, hs.modelHessian, hs.trial⟩
  have hv : ∀ x, Invariant p (s1 x) := fun x =>
    ⟨(hinv x).iteration, (hinv x).scale, (hinv x).weight, (hinv x).weight_pos,
      (hinv x).point, (hinv x).dual, (hinv x).trial⟩
  exact ⟨hs.iteration, measurable_const, hs.weight, hs.point, hs.dual, hs.scale,
    hg, hH, measurable_primal p s1 hm hD hv H hH hPSD⟩

lemma measurable_round {Ω : Type*} [MeasurableSpace Ω] (hs : MeasurableState p s)
    (hD : 0 < p.D) (hinv : ∀ x, Invariant p (s x))
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (ξ : ℕ → X → Ω) (hξ : ∀ k, Measurable (ξ k)) (n : ℕ) :
    MeasurableState p (fun x => round p g H (fun k => ξ k x) n (s x)) := by
  let gr := fun x => g (center (s x)) (ξ (3 * n) x)
  let Hr := fun x => H (center (s x)) (ξ (3 * n + 1) x)
  let m := fun x => modelState p (s x) (gr x) (Hr x)
  have hgr : Measurable gr := hg.comp ((measurable_center p s hs).prodMk (hξ _))
  have hHr : Measurable Hr := hH.comp ((measurable_center p s hs).prodMk (hξ _))
  have hm : MeasurableState p m := measurable_modelState p s hs hD hinv gr Hr hgr hHr
    (fun x => hPSD _ (center_mem p (s x) (hinv x)) _)
  have hmv : ∀ x, Invariant p (m x) := fun x => modelState_invariant p _ _ _ (hinv x)
  have hgd : Measurable (fun x => g (queryPoint (m x)) (ξ (3 * n + 2) x)) :=
    hg.comp ((measurable_queryPoint p m hm).prodMk (hξ _))
  exact measurable_advance p m hm hD hmv _ hgd

lemma measurable_roundState {Ω : Type*} [MeasurableSpace Ω]
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (ξ : ℕ → X → Ω) (hξ : ∀ k, Measurable (ξ k)) (n : ℕ) :
    MeasurableState p (fun x => roundState p g H (fun k => ξ k x) n) := by
  induction n with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const, measurable_const,
      measurable_const, measurable_const, measurable_const, measurable_const, measurable_const⟩
  | succ n ih =>
    exact measurable_round p _ ih hD
      (fun x => roundState_invariant p g H (fun k => ξ k x) hD hρ hσ hx n) g H hg hH hPSD ξ hξ n

lemma integrable_gap (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (f : Point p.d → ℝ) (hf : Continuous f) (xstar : Point p.d)
    (Y : X → Point p.d) (hY : Measurable Y) (hC : ∀ x, Y x ∈ p.C) :
    MeasureTheory.Integrable (fun x => f (Y x) - f xstar) μ := by
  obtain ⟨B, hB⟩ := p.C.isCompact.exists_bound_of_continuousOn
    (hf.sub continuous_const).continuousOn
  apply MeasureTheory.Integrable.of_bound
    ((hf.measurable.comp hY).sub measurable_const).aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun x => hB (Y x) (hC x))

lemma measurable_modelAt {Ω : Type*} [MeasurableSpace Ω]
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (ξ : ℕ → X → Ω) (hξ : ∀ k, Measurable (ξ k)) (n : ℕ) :
    MeasurableState p (fun x => modelAt p g H (fun k => ξ k x) n) := by
  let st := fun x => roundState p g H (fun k => ξ k x) n
  have hm : MeasurableState p st := measurable_roundState p hD hρ hσ hx g H hg hH hPSD ξ hξ n
  have hv : ∀ x, Invariant p (st x) := fun x =>
    roundState_invariant p g H (fun k => ξ k x) hD hρ hσ hx n
  have hcenter := measurable_center p st hm
  exact measurable_modelState p st hm hD hv _ _
    (hg.comp (hcenter.prodMk (hξ (3 * n)))) (hH.comp (hcenter.prodMk (hξ (3 * n + 1))))
    (fun x => hPSD _ (center_mem p (st x) (hv x)) _)

end LongTails.Proofs.HessianAdaptiveCubicMeasurability
