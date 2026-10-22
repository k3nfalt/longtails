import LongTails.Proofs.ScentPrefix
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner


namespace OracleTemplate.Scent

open MeasureTheory Real
open LongTails.Setups.CompositionalEntropicRisk
open OracleTemplate.SampledConvex (extend measurable_extend extend_agree integral_prefix)
open scoped RealInnerProductSpace BigOperators

variable {q : Params} (I : Instance q) (projection : q.E → q.E) (η α : ℝ)

noncomputable abbrev PP : Measure (ℕ → Seed q) := Measure.infinitePi fun _ : ℕ => sampleLaw I

noncomputable def W (ξ : ℕ → Seed q) (t : ℕ) : q.E := (iter I projection η α ξ t).1

noncomputable def Nu (ξ : ℕ → Seed q) (t : ℕ) : Fin q.n → ℝ := (iter I projection η α ξ t).2

noncomputable def Nb (ξ : ℕ → Seed q) (t b : ℕ) : Fin q.n → ℝ :=
  (subSteps I α (W I projection η α ξ t) (Nu I projection η α ξ t) ξ (t * (q.B + 1)) b).1

noncomputable def Acc (ξ : ℕ → Seed q) (t b : ℕ) : q.E :=
  (subSteps I α (W I projection η α ξ t) (Nu I projection η α ξ t) ξ (t * (q.B + 1)) b).2

def callIdx (q : Params) (t b : ℕ) : ℕ := t * (q.B + 1) + b

noncomputable def Z (ξ : ℕ → Seed q) (t b : ℕ) : q.E :=
  piece I α (W I projection η α ξ t) (Nb I projection η α ξ t b) (ξ (callIdx q t b))

noncomputable def M (ξ : ℕ → Seed q) (t b : ℕ) : q.E :=
  meanGrad I α (W I projection η α ξ t) (Nb I projection η α ξ t b)

noncomputable def Dpot (wstar : q.E) (ξ : ℕ → Seed q) (t b : ℕ) : ℝ :=
  dualPot (nuStar I wstar) (Nb I projection η α ξ t b)

noncomputable def Reg (wstar : q.E) (ξ : ℕ → Seed q) (t b : ℕ) : ℝ :=
  dualRegret I α (W I projection η α ξ t) (Nb I projection η α ξ t b) (nuStar I wstar)

noncomputable def Dnoise (ξ : ℕ → Seed q) (t b : ℕ) : ℝ :=
  dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b)

noncomputable def dZ (ξ : ℕ → Seed q) (t b : ℕ) : q.E :=
  Z I projection η α ξ t b - M I projection η α ξ t b

noncomputable def S (ξ : ℕ → Seed q) (t b : ℕ) : q.E :=
  ∑ b' ∈ Finset.range b, dZ I projection η α ξ t b'

noncomputable def Vobj (ξ : ℕ → Seed q) (t b : ℕ) : ℝ :=
  virtualObj I α (W I projection η α ξ t) (Nb I projection η α ξ t b)

noncomputable def Vgap (ξ : ℕ → Seed q) (t b : ℕ) : ℝ :=
  virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b)

noncomputable def Fstar (wstar : q.E) : ℝ := jointObj I wstar (nuStar I wstar)

section Basic

lemma Nb_zero (ξ : ℕ → Seed q) (t : ℕ) : Nb I projection η α ξ t 0 = Nu I projection η α ξ t := rfl

lemma Acc_zero (ξ : ℕ → Seed q) (t : ℕ) : Acc I projection η α ξ t 0 = 0 := rfl

lemma Nb_succ (ξ : ℕ → Seed q) (t b : ℕ) :
    Nb I projection η α ξ t (b + 1) =
      newDual I α (W I projection η α ξ t) (Nb I projection η α ξ t b) (ξ (callIdx q t b)) := rfl

lemma Acc_succ (ξ : ℕ → Seed q) (t b : ℕ) :
    Acc I projection η α ξ t (b + 1) = Acc I projection η α ξ t b + Z I projection η α ξ t b := rfl

lemma W_succ (ξ : ℕ → Seed q) (t : ℕ) :
    W I projection η α ξ (t + 1) =
      projection (W I projection η α ξ t - (η / q.B) • Acc I projection η α ξ t q.B) := rfl

lemma Nu_succ (ξ : ℕ → Seed q) (t : ℕ) :
    Nu I projection η α ξ (t + 1) = Nb I projection η α ξ t q.B := rfl

lemma W_zero (ξ : ℕ → Seed q) : W I projection η α ξ 0 = q.w0 := rfl

lemma Nu_zero (ξ : ℕ → Seed q) : Nu I projection η α ξ 0 = fun _ => q.c1 := rfl

lemma Acc_eq_sum (ξ : ℕ → Seed q) (t : ℕ) :
    ∀ b, Acc I projection η α ξ t b = ∑ b' ∈ Finset.range b, Z I projection η α ξ t b' := by
  intro b
  induction b with
  | zero => simp [Acc_zero]
  | succ b ih => rw [Acc_succ, ih, Finset.sum_range_succ]

end Basic

section Invariants

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)
include h

lemma W_mem (ξ : ℕ → Seed q) : ∀ t, W I projection η α ξ t ∈ I.domain := by
  intro t
  cases t with
  | zero => exact h.w0_mem
  | succ t => rw [W_succ]; exact h.proj_mem _

include hα in
lemma Nb_mem (ξ : ℕ → Seed q) : ∀ t b i, Nb I projection η α ξ t b i ∈ Set.Icc q.c0 q.c1 := by
  intro t
  induction t with
  | zero =>
    intro b
    induction b with
    | zero => intro i; simp [Nb_zero, Nu_zero, h.hc]
    | succ b ih =>
      intro i
      rw [Nb_succ]
      unfold newDual
      rw [Function.update_apply]
      split_ifs with hi
      · subst hi
        exact spmd_mem_Icc hα (ih _) ((h.anchor _).bound _ _ (W_mem I η α h ξ 0))
      · exact ih i
  | succ t iht =>
    intro b
    induction b with
    | zero => intro i; rw [Nb_zero, Nu_succ]; exact iht q.B i
    | succ b ih =>
      intro i
      rw [Nb_succ]
      unfold newDual
      rw [Function.update_apply]
      split_ifs with hi
      · subst hi
        exact spmd_mem_Icc hα (ih _) ((h.anchor _).bound _ _ (W_mem I η α h ξ (t + 1)))
      · exact ih i

end Invariants

section Measurable

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar)
include h

lemma measurable_W (t : ℕ) : Measurable (fun ξ => W I projection η α ξ t) :=
  (measurable_iter I η α h t).1

lemma measurable_Nu (t : ℕ) : Measurable (fun ξ => Nu I projection η α ξ t) :=
  (measurable_iter I η α h t).2

lemma measurable_Nb (t b : ℕ) : Measurable (fun ξ => Nb I projection η α ξ t b) :=
  (measurable_subSteps I α h (measurable_W I η α h t) (measurable_Nu I η α h t) _ b).1

lemma measurable_Acc (t b : ℕ) : Measurable (fun ξ => Acc I projection η α ξ t b) :=
  (measurable_subSteps I α h (measurable_W I η α h t) (measurable_Nu I η α h t) _ b).2

lemma measurable_Z (t b : ℕ) : Measurable (fun ξ => Z I projection η α ξ t b) :=
  measurable_piece I α h (measurable_W I η α h t) (measurable_Nb I η α h t b) _

end Measurable

section Congr

lemma W_congr {ξ ξ' : ℕ → Seed q} (t : ℕ) (hξ : ∀ i, i < t * (q.B + 1) → ξ i = ξ' i) :
    W I projection η α ξ t = W I projection η α ξ' t := by
  unfold W; rw [iter_congr I projection η α t hξ]

lemma Nb_congr {ξ ξ' : ℕ → Seed q} (t b : ℕ) (hξ : ∀ i, i < callIdx q t b → ξ i = ξ' i) :
    Nb I projection η α ξ t b = Nb I projection η α ξ' t b := by
  unfold Nb Nu callIdx at *
  rw [W_congr I projection η α t (fun i hi => hξ i (by omega)),
    iter_congr I projection η α t (fun i hi => hξ i (by omega)),
    subSteps_congr I α _ _ (t * (q.B + 1)) b hξ]

lemma Acc_congr {ξ ξ' : ℕ → Seed q} (t b : ℕ) (hξ : ∀ i, i < callIdx q t b → ξ i = ξ' i) :
    Acc I projection η α ξ t b = Acc I projection η α ξ' t b := by
  unfold Acc Nu callIdx at *
  rw [W_congr I projection η α t (fun i hi => hξ i (by omega)),
    iter_congr I projection η α t (fun i hi => hξ i (by omega)),
    subSteps_congr I α _ _ (t * (q.B + 1)) b hξ]

end Congr


section Workhorse

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)

def good (q : Params) (I : Instance q) : Set (q.E × (Fin q.n → ℝ)) :=
  (Prod.fst ⁻¹' I.domain) ∩ ⋂ i, (fun y : q.E × (Fin q.n → ℝ) => y.2 i) ⁻¹' Set.Icc q.c0 q.c1

include h in
lemma measurableSet_good : MeasurableSet (good q I) :=
  (h.closed.measurableSet.preimage measurable_fst).inter
    (MeasurableSet.iInter fun i => measurableSet_Icc.preimage ((measurable_pi_apply i).comp measurable_snd))

omit h in
lemma mem_good_iff (y : q.E × (Fin q.n → ℝ)) :
    y ∈ good q I ↔ y.1 ∈ I.domain ∧ ∀ i, y.2 i ∈ Set.Icc q.c0 q.c1 := by
  simp [good]

include h hα in
lemma state_good (ξ : ℕ → Seed q) (t b : ℕ) :
    (W I projection η α ξ t, Nb I projection η α ξ t b) ∈ good q I :=
  (mem_good_iff I _).mpr ⟨W_mem I η α h ξ t, Nb_mem I η α h hα ξ t b⟩

include I in
lemma nonempty_seed : Nonempty (Seed q) := by
  have hn : Nonempty (Fin q.n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne q.n)⟩⟩
  obtain ⟨i⟩ := hn
  have : Nonempty q.Ξ := Measure.nonempty_of_neZero (I.law i : Measure q.Ξ)
  obtain ⟨x⟩ := this
  exact ⟨(i, fun _ => x, fun _ => x)⟩

include h hα in
lemma substep_integral (t b : ℕ) (Φ : q.E × (Fin q.n → ℝ) → Seed q → ℝ)
    (hΦ : Measurable (Function.uncurry Φ)) (C : ℝ)
    (hsec : ∀ y ∈ good q I, Integrable (Φ y) (sampleLaw I))
    (hbd : ∀ y ∈ good q I, (∫ ω, |Φ y ω| ∂(sampleLaw I)) ≤ C) :
    Integrable (fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)))
      (PP I) ∧
    ∫ ξ, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)) ∂(PP I) =
      ∫ ξ, (∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I)) ∂(PP I) := by
  classical
  obtain ⟨ω0⟩ := nonempty_seed I
  set k := callIdx q t b with hk
  let X : (Fin k → Seed q) → q.E × (Fin q.n → ℝ) := fun u =>
    (W I projection η α (extend ω0 u) t, Nb I projection η α (extend ω0 u) t b)
  have hX : Measurable X :=
    ((measurable_W I η α h t).comp (measurable_extend ω0)).prodMk
      ((measurable_Nb I η α h t b).comp (measurable_extend ω0))
  have hXeq : ∀ ξ : ℕ → Seed q, X (fun i : Fin k => ξ i) =
      (W I projection η α ξ t, Nb I projection η α ξ t b) := by
    intro ξ
    simp only [X]
    rw [W_congr I projection η α t (fun i hi => extend_agree ω0 ξ i (by rw [hk]; unfold callIdx; omega)),
      Nb_congr I projection η α t b (fun i hi => extend_agree ω0 ξ i (by rw [hk]; exact hi))]
  let Φ' : q.E × (Fin q.n → ℝ) → Seed q → ℝ := fun y ω => if y ∈ good q I then Φ y ω else 0
  have hΦ' : Measurable (Function.uncurry Φ') := by
    have : Function.uncurry Φ' = fun p : (q.E × (Fin q.n → ℝ)) × Seed q =>
        if p.1 ∈ good q I then Function.uncurry Φ p else 0 := rfl
    rw [this]
    exact Measurable.ite ((measurableSet_good I h).preimage measurable_fst) hΦ measurable_const
  have hsec' : ∀ y, Integrable (Φ' y) (sampleLaw I) := by
    intro y
    by_cases hy : y ∈ good q I
    · simp only [Φ', hy, ↓reduceIte]; exact hsec y hy
    · simp only [Φ', hy, ↓reduceIte]; exact integrable_const 0
  have hbd' : ∀ y, (∫ ω, |Φ' y ω| ∂(sampleLaw I)) ≤ max C 0 := by
    intro y
    by_cases hy : y ∈ good q I
    · simp only [Φ', hy, ↓reduceIte]; exact (hbd y hy).trans (le_max_left _ _)
    · simp only [Φ', hy, ↓reduceIte, abs_zero, integral_zero]; exact le_max_right _ _
  have hint := prefix_split_bounded (sampleLaw I) k X hX Φ' hΦ' (max C 0) hsec' hbd'
  obtain ⟨_, heq⟩ := integral_prefix (sampleLaw I) k X hX Φ' hΦ' hint
  have hfun : (fun ξ : ℕ → Seed q => Φ' (X (fun i : Fin k => ξ i)) (ξ k)) =
      fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)) := by
    funext ξ
    simp only [Φ', hXeq, state_good I η α h hα ξ t b, ↓reduceIte]
    rfl
  have hfun2 : (fun ξ : ℕ → Seed q => ∫ ω, Φ' (X (fun i : Fin k => ξ i)) ω ∂(sampleLaw I)) =
      fun ξ => ∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I) := by
    funext ξ
    simp only [Φ', hXeq, state_good I η α h hα ξ t b, ↓reduceIte]
  rw [hfun] at hint heq
  rw [hfun2] at heq
  exact ⟨hint, heq⟩

end Workhorse

section Functionals

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar)
include h

omit h in
lemma measurable_cond_real {F : (ℕ → Seed q) → q.Ξ → ℝ} (hF : Measurable (Function.uncurry F))
    (i : Fin q.n) : Measurable (fun ξ => ∫ ζ, F ξ ζ ∂(I.law i : Measure q.Ξ)) :=
  (hF.stronglyMeasurable.integral_prod_right').measurable

omit h in
lemma measurable_cond_vec {F : (ℕ → Seed q) → q.Ξ → q.E} (hF : Measurable (Function.uncurry F))
    (i : Fin q.n) : Measurable (fun ξ => ∫ ζ, F ξ ζ ∂(I.law i : Measure q.Ξ)) :=
  (hF.stronglyMeasurable.integral_prod_right').measurable

lemma measurable_scoreW (t : ℕ) (i : Fin q.n) :
    Measurable (fun p : (ℕ → Seed q) × q.Ξ => I.score i (W I projection η α p.1 t) p.2) :=
  (h.anchor i).meas_s.comp (((measurable_W I η α h t).comp measurable_fst).prodMk measurable_snd)

lemma measurable_gradW' (t : ℕ) (i : Fin q.n) :
    Measurable (fun p : (ℕ → Seed q) × q.Ξ => I.grad i (W I projection η α p.1 t) p.2) :=
  (h.anchor i).meas_g.comp (((measurable_W I η α h t).comp measurable_fst).prodMk measurable_snd)

lemma measurable_mass (t : ℕ) (i : Fin q.n) :
    Measurable (fun ξ => mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t)) :=
  measurable_cond_real I (F := fun ξ ζ => exp (I.score i (W I projection η α ξ t) ζ))
    (measurable_exp.comp (measurable_scoreW I η α h t i)) i

lemma measurable_spmdNb (t b : ℕ) (i : Fin q.n) :
    Measurable (fun p : (ℕ → Seed q) × q.Ξ =>
      spmd α (Nb I projection η α p.1 t b i) (I.score i (W I projection η α p.1 t) p.2)) := by
  have hν : Measurable (fun p : (ℕ → Seed q) × q.Ξ => Nb I projection η α p.1 t b i) :=
    (measurable_pi_apply i).comp ((measurable_Nb I η α h t b).comp measurable_fst)
  have hs := measurable_scoreW I η α h t i
  unfold spmd
  exact ((hν.add (measurable_log.comp (measurable_const.add (measurable_const.mul
    (measurable_exp.comp hs))))).sub (measurable_log.comp (measurable_const.add
    (measurable_const.mul (measurable_exp.comp hν)))))

lemma measurable_virtualGap (t b : ℕ) :
    Measurable (fun ξ => virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) := by
  unfold virtualGap
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  refine measurable_cond_real I (F := fun ξ ζ => anchorGap (I.law i : Measure q.Ξ) (I.score i)
    (W I projection η α ξ t) (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ))) ?_ i
  unfold anchorGap psi
  have hm : Measurable (fun p : (ℕ → Seed q) × q.Ξ =>
      mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α p.1 t)) :=
    (measurable_mass I η α h t i).comp measurable_fst
  have hsp := measurable_spmdNb I η α h t b i
  exact ((measurable_exp.comp ((measurable_log.comp hm).sub hsp)).sub measurable_const).sub
    ((measurable_log.comp hm).sub hsp)

lemma measurable_virtualObj (t b : ℕ) :
    Measurable (fun ξ => virtualObj I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) := by
  unfold virtualObj
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  refine measurable_cond_real I (F := fun ξ ζ => dualObj (I.law i : Measure q.Ξ) (I.score i)
    (W I projection η α ξ t) (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ))) ?_ i
  unfold dualObj
  have hm : Measurable (fun p : (ℕ → Seed q) × q.Ξ =>
      mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α p.1 t)) :=
    (measurable_mass I η α h t i).comp measurable_fst
  have hsp := measurable_spmdNb I η α h t b i
  exact (hm.mul (measurable_exp.comp hsp.neg)).add hsp

lemma measurable_dualNoise (t b : ℕ) :
    Measurable (fun ξ => dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b)) := by
  unfold dualNoise
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  refine Measurable.mul (measurable_exp.comp ((measurable_pi_apply i).comp
    (measurable_Nb I η α h t b)).neg) ?_
  refine measurable_cond_real I (F := fun ξ ζ => (exp (I.score i (W I projection η α ξ t) ζ) -
    mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t)) ^ 2) ?_ i
  have hm : Measurable (fun p : (ℕ → Seed q) × q.Ξ =>
      mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α p.1 t)) :=
    (measurable_mass I η α h t i).comp measurable_fst
  exact ((measurable_exp.comp (measurable_scoreW I η α h t i)).sub hm).pow_const 2

lemma measurable_dualRegret (t b : ℕ) :
    Measurable (fun ξ => dualRegret I α (W I projection η α ξ t) (Nb I projection η α ξ t b)
      (nuStar I wstar)) := by
  unfold dualRegret
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  refine measurable_cond_real I (F := fun ξ ζ => (1 - mass (I.law i : Measure q.Ξ) (I.score i)
    (W I projection η α ξ t) * exp (-(spmd α (Nb I projection η α ξ t b i)
    (I.score i (W I projection η α ξ t) ζ)))) * (spmd α (Nb I projection η α ξ t b i)
    (I.score i (W I projection η α ξ t) ζ) - nuStar I wstar i)) ?_ i
  have hm : Measurable (fun p : (ℕ → Seed q) × q.Ξ =>
      mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α p.1 t)) :=
    (measurable_mass I η α h t i).comp measurable_fst
  have hsp := measurable_spmdNb I η α h t b i
  exact (measurable_const.sub (hm.mul (measurable_exp.comp hsp.neg))).mul (hsp.sub measurable_const)

lemma measurable_centerGrad (t : ℕ) (i : Fin q.n) :
    Measurable (fun ξ => ∫ ζ', exp (I.score i (W I projection η α ξ t) ζ') •
      I.grad i (W I projection η α ξ t) ζ' ∂(I.law i : Measure q.Ξ)) :=
  measurable_cond_vec I (F := fun ξ ζ' => exp (I.score i (W I projection η α ξ t) ζ') •
    I.grad i (W I projection η α ξ t) ζ')
    ((measurable_exp.comp (measurable_scoreW I η α h t i)).smul (measurable_gradW' I η α h t i)) i

lemma measurable_M (t b : ℕ) : Measurable (fun ξ => M I projection η α ξ t b) := by
  unfold M meanGrad
  refine Measurable.const_smul (Finset.measurable_sum _ fun i _ => ?_) _
  have hrepr : (fun ξ => ∫ ζ, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i)
      (W I projection η α ξ t) (spmd α (Nb I projection η α ξ t b i)
      (I.score i (W I projection η α ξ t) ζ)) ∂(I.law i : Measure q.Ξ)) =
      fun ξ => (∫ ζ, exp (-(spmd α (Nb I projection η α ξ t b i)
        (I.score i (W I projection η α ξ t) ζ))) ∂(I.law i : Measure q.Ξ)) •
        ∫ ζ', exp (I.score i (W I projection η α ξ t) ζ') • I.grad i (W I projection η α ξ t) ζ'
          ∂(I.law i : Measure q.Ξ) := by
    funext ξ
    exact AnchorHyp.integral_gradVirt (W I projection η α ξ t) α _
  rw [hrepr]
  refine Measurable.smul ?_ (measurable_centerGrad I η α h t i)
  exact measurable_cond_real I (F := fun ξ ζ => exp (-(spmd α (Nb I projection η α ξ t b i)
    (I.score i (W I projection η α ξ t) ζ)))) (measurable_exp.comp (measurable_spmdNb I η α h t b i).neg) i

end Functionals


section Stage3a

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)

include I in
lemma expect_substep_of_integrable (t b : ℕ) {Y : Type*} [MeasurableSpace Y]
    (G : (ℕ → Seed q) → Y) (hG : Measurable G)
    (hGc : ∀ ξ ξ' : ℕ → Seed q, (∀ i, i < callIdx q t b → ξ i = ξ' i) → G ξ = G ξ')
    (Φ : Y → Seed q → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hint : Integrable (fun ξ => Φ (G ξ) (ξ (callIdx q t b))) (PP I)) :
    Integrable (fun ξ => ∫ ω, Φ (G ξ) ω ∂(sampleLaw I)) (PP I) ∧
    ∫ ξ, Φ (G ξ) (ξ (callIdx q t b)) ∂(PP I) =
      ∫ ξ, (∫ ω, Φ (G ξ) ω ∂(sampleLaw I)) ∂(PP I) := by
  obtain ⟨ω0⟩ := nonempty_seed I
  set k := callIdx q t b with hk
  let X : (Fin k → Seed q) → Y := fun u => G (extend ω0 u)
  have hX : Measurable X := hG.comp (measurable_extend ω0)
  have hXeq : ∀ ξ : ℕ → Seed q, X (fun i : Fin k => ξ i) = G ξ := fun ξ =>
    hGc _ _ (fun i hi => extend_agree ω0 ξ i hi)
  have hfun : (fun ξ : ℕ → Seed q => Φ (X (fun i : Fin k => ξ i)) (ξ k)) =
      fun ξ => Φ (G ξ) (ξ (callIdx q t b)) := by funext ξ; rw [hXeq]
  have hfun2 : (fun ξ : ℕ → Seed q => ∫ ω, Φ (X (fun i : Fin k => ξ i)) ω ∂(sampleLaw I)) =
      fun ξ => ∫ ω, Φ (G ξ) ω ∂(sampleLaw I) := by funext ξ; rw [hXeq]
  have := integral_prefix (sampleLaw I) k X hX Φ hΦ (by rw [hfun]; exact hint)
  rw [hfun, hfun2] at this
  exact this

include h in
lemma measurable_piece_joint :
    Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => piece I α p.1.1 p.1.2 p.2) := by
  unfold piece
  have hidx : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hζ : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.2.2.1 p.2.1) :=
    meas_eval_fin.comp ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hidx)
  have hζ' : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.2.2.2 p.2.1) :=
    meas_eval_fin.comp ((measurable_snd.comp (measurable_snd.comp measurable_snd)).prodMk hidx)
  have hw : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hν : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.1.2 p.2.1) :=
    meas_eval_fin.comp ((measurable_snd.comp measurable_fst).prodMk hidx)
  have hs : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => I.score p.2.1 p.1.1 (p.2.2.1 p.2.1)) :=
    (meas_score_triple I h).comp (hidx.prodMk (hw.prodMk hζ))
  have hs' : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => I.score p.2.1 p.1.1 (p.2.2.2 p.2.1)) :=
    (meas_score_triple I h).comp (hidx.prodMk (hw.prodMk hζ'))
  have hg' : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => I.grad p.2.1 p.1.1 (p.2.2.2 p.2.1)) :=
    (meas_grad_triple I h).comp (hidx.prodMk (hw.prodMk hζ'))
  have hspmd : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q =>
      spmd α (p.1.2 p.2.1) (I.score p.2.1 p.1.1 (p.2.2.1 p.2.1))) := by
    unfold spmd
    exact ((hν.add (measurable_log.comp (measurable_const.add (measurable_const.mul
      (measurable_exp.comp hs))))).sub (measurable_log.comp (measurable_const.add
      (measurable_const.mul (measurable_exp.comp hν)))))
  exact (measurable_exp.comp (hs'.sub hspmd)).smul hg'

include h hα in
lemma Vgap_le (ξ : ℕ → Seed q) (t b : ℕ) :
    virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ≤ exp (q.c1 - q.c0) := by
  unfold virtualGap
  have hper : ∀ i, (∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t)
      (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ))
      ∂(I.law i : Measure q.Ξ)) ≤ exp (q.c1 - q.c0) := by
    intro i
    have hA := h.anchor i
    have := integral_mono (hA.gap_virtual_int (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b i))
      (integrable_const _) (fun ζ => hA.gap_bound (W_mem I η α h ξ t)
        (hA.spmd_s_mem (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b i) ζ))
    simpa using this
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc _ ≤ (q.n : ℝ)⁻¹ * ((q.n : ℝ) * exp (q.c1 - q.c0)) := mul_le_mul_of_nonneg_left hsum hn
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (SysHyp.n_pos (q := q)).ne', one_mul]

include h hα in
lemma Vgap_int (t b : ℕ) :
    Integrable (fun ξ => virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) (PP I) := by
  refine Integrable.of_bound (measurable_virtualGap I η α h t b).aestronglyMeasurable (exp (q.c1 - q.c0)) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (SysHyp.virtualGap_nonneg (q := q) (I := I) α _ _)]
    exact Vgap_le I η α h hα ξ t b

include h hα in
lemma Zsq_bounds (t b : ℕ) :
    Integrable (fun ξ => ‖Z I projection η α ξ t b‖ ^ 2) (PP I) ∧
    (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤ 2 * exp (q.c1 - q.c0) * q.σ ^ 2 *
      (1 + ∫ ξ, virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ∂(PP I)) ∧
    (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤ exp (2 * (q.c1 - q.c0)) * q.G ^ 2 := by
  let Φ : q.E × (Fin q.n → ℝ) → Seed q → ℝ := fun y ω => ‖piece I α y.1 y.2 ω‖ ^ 2
  have hΦ : Measurable (Function.uncurry Φ) := (measurable_piece_joint I α h).norm.pow_const 2
  have hsec : ∀ y ∈ good q I, Integrable (Φ y) (sampleLaw I) := fun y hy =>
    (h.expected_piece_sq ((mem_good_iff I y).mp hy).1 hα ((mem_good_iff I y).mp hy).2).1
  have hbd : ∀ y ∈ good q I, (∫ ω, |Φ y ω| ∂(sampleLaw I)) ≤ exp (2 * (q.c1 - q.c0)) * q.G ^ 2 := by
    intro y hy
    have habs : ∀ ω, |Φ y ω| = Φ y ω := fun ω => abs_of_nonneg (sq_nonneg _)
    simp only [habs]
    exact (h.expected_piece_sq ((mem_good_iff I y).mp hy).1 hα ((mem_good_iff I y).mp hy).2).2.2
  obtain ⟨hint, heq⟩ := substep_integral I η α h hα t b Φ hΦ _ hsec hbd
  have hG : Measurable (fun ξ => (W I projection η α ξ t, Nb I projection η α ξ t b)) :=
    (measurable_W I η α h t).prodMk (measurable_Nb I η α h t b)
  have hGc : ∀ ξ ξ' : ℕ → Seed q, (∀ i, i < callIdx q t b → ξ i = ξ' i) →
      (W I projection η α ξ t, Nb I projection η α ξ t b) =
      (W I projection η α ξ' t, Nb I projection η α ξ' t b) := fun ξ ξ' hξ => by
    rw [W_congr I projection η α t (fun i hi => hξ i (by unfold callIdx; omega)),
      Nb_congr I projection η α t b hξ]
  have hin := (expect_substep_of_integrable I t b _ hG hGc Φ hΦ hint).1
  have hZ : (fun ξ => ‖Z I projection η α ξ t b‖ ^ 2) =
      fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)) := rfl
  refine ⟨by rw [hZ]; exact hint, ?_, ?_⟩
  · rw [hZ, heq]
    have hpt : ∀ ξ, (∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I)) ≤
        2 * exp (q.c1 - q.c0) * q.σ ^ 2 *
          (1 + virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) := fun ξ =>
      (h.expected_piece_sq (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)).2.1
    have hi2 : Integrable (fun ξ => 2 * exp (q.c1 - q.c0) * q.σ ^ 2 *
        (1 + virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b))) (PP I) :=
      ((integrable_const _).add (Vgap_int I η α h hα t b)).const_mul _
    calc _ ≤ _ := integral_mono hin hi2 hpt
      _ = _ := by
          rw [integral_const_mul, integral_add (integrable_const _) (Vgap_int I η α h hα t b)]
          simp
  · rw [hZ, heq]
    have hpt : ∀ ξ, (∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I)) ≤
        exp (2 * (q.c1 - q.c0)) * q.G ^ 2 := fun ξ =>
      (h.expected_piece_sq (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)).2.2
    calc _ ≤ ∫ _ξ, exp (2 * (q.c1 - q.c0)) * q.G ^ 2 ∂(PP I) :=
          integral_mono hin (integrable_const _) hpt
      _ = _ := by simp

include h hα in
lemma Msq_bound (t b : ℕ) :
    Integrable (fun ξ => ‖M I projection η α ξ t b‖ ^ 2) (PP I) ∧
    (∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤ 2 * q.κ * q.G ^ 2 +
      4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 *
        ∫ ξ, virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ∂(PP I) := by
  have hpt : ∀ ξ, ‖M I projection η α ξ t b‖ ^ 2 ≤ 2 * q.κ * q.G ^ 2 +
      4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 *
        virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b) := fun ξ =>
    h.meanGrad_sq_le (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)
  have hi2 : Integrable (fun ξ => 2 * q.κ * q.G ^ 2 + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 *
      virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) (PP I) :=
    (integrable_const _).add ((Vgap_int I η α h hα t b).const_mul _)
  have hint : Integrable (fun ξ => ‖M I projection η α ξ t b‖ ^ 2) (PP I) := by
    refine Integrable.mono' hi2 ((measurable_M I η α h t b).norm.pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ξ
  refine ⟨hint, ?_⟩
  calc _ ≤ _ := integral_mono hint hi2 hpt
    _ = _ := by
        rw [integral_add (integrable_const _) ((Vgap_int I η α h hα t b).const_mul _),
          integral_const, integral_const_mul]
        simp

include h hα in
lemma Dnoise_bound {ρ : ℝ} (hρ : α * exp q.c1 ≤ ρ) (t b : ℕ) :
    Integrable (fun ξ => dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b)) (PP I) ∧
    (∫ ξ, dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b) ∂(PP I)) ≤
      2 * (1 + ρ) * (q.κ - 1) * exp q.c1 *
        (1 + ∫ ξ, virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ∂(PP I)) := by
  have hpt : ∀ ξ, dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b) ≤
      2 * (1 + ρ) * (q.κ - 1) * exp q.c1 *
        (1 + virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) := fun ξ =>
    h.dualNoise_le (W_mem I η α h ξ t) hα hρ (Nb_mem I η α h hα ξ t b)
  have hnn : ∀ ξ, 0 ≤ dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b) := by
    intro ξ
    unfold dualNoise
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (exp_pos _).le (integral_nonneg fun _ => sq_nonneg _)
  have hi2 : Integrable (fun ξ => 2 * (1 + ρ) * (q.κ - 1) * exp q.c1 *
      (1 + virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b))) (PP I) :=
    ((integrable_const _).add (Vgap_int I η α h hα t b)).const_mul _
  have hint : Integrable (fun ξ => dualNoise I (W I projection η α ξ t) (Nb I projection η α ξ t b))
      (PP I) := by
    refine Integrable.mono' hi2 (measurable_dualNoise I η α h t b).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn ξ)]; exact hpt ξ
  refine ⟨hint, ?_⟩
  calc _ ≤ _ := integral_mono hint hi2 hpt
    _ = _ := by
        rw [integral_const_mul, integral_add (integrable_const _) (Vgap_int I η α h hα t b)]
        simp

end Stage3a


section Stage3b

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)

omit h in
lemma measurable_breg2 : Measurable (fun p : ℝ × ℝ => breg p.1 p.2) := by
  unfold breg
  exact ((measurable_exp.comp measurable_fst.neg).sub (measurable_exp.comp measurable_snd.neg)).add
    ((measurable_exp.comp measurable_snd.neg).mul (measurable_fst.sub measurable_snd))

include h in
lemma measurable_Dpot (t b : ℕ) : Measurable (fun ξ => Dpot I projection η α wstar ξ t b) := by
  unfold Dpot dualPot
  exact Finset.measurable_sum _ fun i _ =>
    measurable_breg2.comp (measurable_const.prodMk ((measurable_pi_apply i).comp (measurable_Nb I η α h t b)))

include h hα in
lemma Dpot_bound (ξ : ℕ → Seed q) (t b : ℕ) :
    |Dpot I projection η α wstar ξ t b| ≤ q.n * (3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|)) := by
  unfold Dpot dualPot
  calc |∑ i, breg (nuStar I wstar i) (Nb I projection η α ξ t b i)|
      ≤ ∑ i, |breg (nuStar I wstar i) (Nb I projection η α ξ t b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin q.n, 3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|) :=
        Finset.sum_le_sum fun i _ => SysHyp.breg_bounded (q := q) (h.nuStar_mem i) (Nb_mem I η α h hα ξ t b i)
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

include h hα in
lemma Dpot_int (t b : ℕ) : Integrable (fun ξ => Dpot I projection η α wstar ξ t b) (PP I) :=
  Integrable.of_bound (measurable_Dpot I η α h t b).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact Dpot_bound I η α h hα ξ t b)

omit h in
lemma Dpot_nonneg (ξ : ℕ → Seed q) (t b : ℕ) : 0 ≤ Dpot I projection η α wstar ξ t b := by
  unfold Dpot dualPot
  exact Finset.sum_nonneg fun i _ => breg_nonneg _ _

include h hα in
lemma Reg_bound (ξ : ℕ → Seed q) (t b : ℕ) :
    |Reg I projection η α wstar ξ t b| ≤ (1 + exp q.c1 * exp (-q.c0)) * (|q.c0| + |q.c1| + (|q.c0| + |q.c1|)) := by
  unfold Reg dualRegret
  set C := (1 + exp q.c1 * exp (-q.c0)) * (|q.c0| + |q.c1| + (|q.c0| + |q.c1|))
  have hper : ∀ i, |∫ ζ, (1 - mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t) *
      exp (-(spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)))) *
      (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ) - nuStar I wstar i)
      ∂(I.law i : Measure q.Ξ)| ≤ C := by
    intro i
    have hA := h.anchor i
    have hw := W_mem I η α h ξ t
    have hνi := Nb_mem I η α h hα ξ t b i
    have hu := h.nuStar_mem i
    have hpt : ∀ ζ, |(1 - mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t) *
        exp (-(spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)))) *
        (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ) - nuStar I wstar i)| ≤ C := by
      intro ζ
      have hr := hA.spmd_s_mem hw hα hνi ζ
      rw [abs_mul]
      have hm := hA.mass_bounds hw
      have h1 : |1 - mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t) *
          exp (-(spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)))| ≤
          1 + exp q.c1 * exp (-q.c0) := by
        rw [abs_le]
        have := mul_le_mul hm.2 (exp_le_exp.mpr (show -(spmd α (Nb I projection η α ξ t b i)
          (I.score i (W I projection η α ξ t) ζ)) ≤ -q.c0 by linarith [hr.1])) (exp_pos _).le (exp_pos _).le
        have h0 : 0 ≤ mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t) *
            exp (-(spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ))) :=
          mul_nonneg (hA.mass_pos hw).le (exp_pos _).le
        constructor <;> linarith
      have h2 : |spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ) -
          nuStar I wstar i| ≤ |q.c0| + |q.c1| + (|q.c0| + |q.c1|) := by
        have ha : |spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)| ≤
            |q.c0| + |q.c1| := by
          rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;>
            linarith [hr.1, hr.2]
        have hb : |nuStar I wstar i| ≤ |q.c0| + |q.c1| := by
          rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;>
            linarith [hu.1, hu.2]
        calc _ ≤ |spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)| +
              |nuStar I wstar i| := abs_sub _ _
          _ ≤ _ := add_le_add ha hb
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hint := hA.regret_integrand_int hw hα hνi hu
    calc _ ≤ ∫ ζ, |(1 - mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t) *
          exp (-(spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)))) *
          (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ) - nuStar I wstar i)|
          ∂(I.law i : Measure q.Ξ) := by
          have := norm_integral_le_integral_norm (μ := (I.law i : Measure q.Ξ)) (fun ζ =>
            (1 - mass (I.law i : Measure q.Ξ) (I.score i) (W I projection η α ξ t) *
            exp (-(spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ)))) *
            (spmd α (Nb I projection η α ξ t b i) (I.score i (W I projection η α ξ t) ζ) - nuStar I wstar i))
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ _ζ, C ∂(I.law i : Measure q.Ξ) := integral_mono hint.abs (integrable_const _) hpt
      _ = C := by simp
  calc |(q.n : ℝ)⁻¹ * ∑ i, _| = (q.n : ℝ)⁻¹ * |∑ i, _| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    _ ≤ (q.n : ℝ)⁻¹ * ∑ _i : Fin q.n, C :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hper i)) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (SysHyp.n_pos (q := q)).ne', one_mul]

include h hα in
lemma Reg_int (t b : ℕ) : Integrable (fun ξ => Reg I projection η α wstar ξ t b) (PP I) :=
  Integrable.of_bound (measurable_dualRegret I η α h t b).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact Reg_bound I η α h hα ξ t b)

include h in
lemma measurable_newDual_joint :
    Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => dualPot (nuStar I wstar) (newDual I α p.1.1 p.1.2 p.2)) := by
  have hrepr : (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => dualPot (nuStar I wstar) (newDual I α p.1.1 p.1.2 p.2)) =
      fun p => dualPot (nuStar I wstar) p.1.2 + (breg (nuStar I wstar p.2.1)
        (spmd α (p.1.2 p.2.1) (I.score p.2.1 p.1.1 (p.2.2.1 p.2.1))) - breg (nuStar I wstar p.2.1) (p.1.2 p.2.1)) := by
    funext p; unfold newDual; rw [SysHyp.dualPot_update]
  rw [hrepr]
  have hidx : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hζ : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.2.2.1 p.2.1) :=
    meas_eval_fin.comp ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hidx)
  have hw : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hν : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => p.1.2 p.2.1) :=
    meas_eval_fin.comp ((measurable_snd.comp measurable_fst).prodMk hidx)
  have hs : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => I.score p.2.1 p.1.1 (p.2.2.1 p.2.1)) :=
    (meas_score_triple I h).comp (hidx.prodMk (hw.prodMk hζ))
  have hspmd : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q =>
      spmd α (p.1.2 p.2.1) (I.score p.2.1 p.1.1 (p.2.2.1 p.2.1))) := by
    unfold spmd
    exact ((hν.add (measurable_log.comp (measurable_const.add (measurable_const.mul
      (measurable_exp.comp hs))))).sub (measurable_log.comp (measurable_const.add
      (measurable_const.mul (measurable_exp.comp hν)))))
  have hνs : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => nuStar I wstar p.2.1) :=
    (measurable_of_countable (nuStar I wstar)).comp hidx
  have hpot : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × Seed q => dualPot (nuStar I wstar) p.1.2) := by
    unfold dualPot
    exact Finset.measurable_sum _ fun i _ =>
      measurable_breg2.comp (measurable_const.prodMk ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))
  exact hpot.add ((measurable_breg2.comp (hνs.prodMk hspmd)).sub (measurable_breg2.comp (hνs.prodMk hν)))

include h hα in
lemma dual_step_expect {ρ : ℝ} (hρ : α * exp q.c1 ≤ ρ) (t b : ℕ) :
    α * ∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I) ≤
      (∫ ξ, Dpot I projection η α wstar ξ t b ∂(PP I)) -
      (∫ ξ, Dpot I projection η α wstar ξ t (b + 1) ∂(PP I)) +
      (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 * ∫ ξ, Dnoise I projection η α ξ t b ∂(PP I) := by
  let Φ : q.E × (Fin q.n → ℝ) → Seed q → ℝ := fun y ω => dualPot (nuStar I wstar) (newDual I α y.1 y.2 ω)
  have hΦ : Measurable (Function.uncurry Φ) := measurable_newDual_joint I α h
  have hnew_mem : ∀ y ∈ good q I, ∀ ω : Seed q, ∀ i, newDual I α y.1 y.2 ω i ∈ Set.Icc q.c0 q.c1 := by
    intro y hy ω i
    obtain ⟨hw, hν⟩ := (mem_good_iff I y).mp hy
    unfold newDual
    rw [Function.update_apply]
    split_ifs with hi
    · subst hi; exact spmd_mem_Icc hα (hν _) ((h.anchor _).bound _ _ hw)
    · exact hν i
  have hbd_pt : ∀ y ∈ good q I, ∀ ω, |Φ y ω| ≤ q.n * (3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|)) := by
    intro y hy ω
    simp only [Φ]
    unfold dualPot
    calc |∑ i, breg (nuStar I wstar i) (newDual I α y.1 y.2 ω i)|
        ≤ ∑ i, |breg (nuStar I wstar i) (newDual I α y.1 y.2 ω i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin q.n, 3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|) :=
          Finset.sum_le_sum fun i _ => SysHyp.breg_bounded (q := q) (h.nuStar_mem i) (hnew_mem y hy ω i)
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsec : ∀ y ∈ good q I, Integrable (Φ y) (sampleLaw I) := fun y hy =>
    Integrable.of_bound (hΦ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd_pt y hy ω)
  have hbd : ∀ y ∈ good q I, (∫ ω, |Φ y ω| ∂(sampleLaw I)) ≤
      q.n * (3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|)) := by
    intro y hy
    calc _ ≤ ∫ _ω, q.n * (3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|)) ∂(sampleLaw I) :=
          integral_mono (hsec y hy).abs (integrable_const _) (hbd_pt y hy)
      _ = _ := by simp
  obtain ⟨hint, heq⟩ := substep_integral I η α h hα t b Φ hΦ _ hsec hbd
  have hG : Measurable (fun ξ => (W I projection η α ξ t, Nb I projection η α ξ t b)) :=
    (measurable_W I η α h t).prodMk (measurable_Nb I η α h t b)
  have hGc : ∀ ξ ξ' : ℕ → Seed q, (∀ i, i < callIdx q t b → ξ i = ξ' i) →
      (W I projection η α ξ t, Nb I projection η α ξ t b) =
      (W I projection η α ξ' t, Nb I projection η α ξ' t b) := fun ξ ξ' hξ => by
    rw [W_congr I projection η α t (fun i hi => hξ i (by unfold callIdx; omega)),
      Nb_congr I projection η α t b hξ]
  have hin := (expect_substep_of_integrable I t b _ hG hGc Φ hΦ hint).1
  have hDsucc : (fun ξ => Dpot I projection η α wstar ξ t (b + 1)) =
      fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)) := rfl
  have hpt : ∀ ξ, α * Reg I projection η α wstar ξ t b ≤
      Dpot I projection η α wstar ξ t b -
      (∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I)) +
      (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 * Dnoise I projection η α ξ t b := fun ξ =>
    h.dual_regret_bound (W_mem I η α h ξ t) hα hρ (Nb_mem I η α h hα ξ t b)
  have hi_lhs : Integrable (fun ξ => α * Reg I projection η α wstar ξ t b) (PP I) :=
    (Reg_int I η α h hα t b).const_mul α
  have hi1 : Integrable (fun ξ => Dpot I projection η α wstar ξ t b -
      (∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I))) (PP I) :=
    (Dpot_int I η α h hα t b).sub hin
  have hi2 : Integrable (fun ξ => (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 *
      Dnoise I projection η α ξ t b) (PP I) :=
    (Dnoise_bound I η α h hα hρ t b).1.const_mul _
  have hi_rhs : Integrable (fun ξ => Dpot I projection η α wstar ξ t b -
      (∫ ω, Φ (W I projection η α ξ t, Nb I projection η α ξ t b) ω ∂(sampleLaw I)) +
      (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 * Dnoise I projection η α ξ t b) (PP I) := hi1.add hi2
  have := integral_mono hi_lhs hi_rhs hpt
  rw [integral_const_mul, integral_add hi1 hi2, integral_sub (Dpot_int I η α h hα t b) hin,
    integral_const_mul, ← heq, ← hDsucc] at this
  exact this

end Stage3b


section Stage3c

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)

omit h in
lemma S_succ (ξ : ℕ → Seed q) (t b : ℕ) :
    S I projection η α ξ t (b + 1) = S I projection η α ξ t b + dZ I projection η α ξ t b := by
  unfold S; rw [Finset.sum_range_succ]

omit h in
lemma Acc_eq_S (ξ : ℕ → Seed q) (t b : ℕ) :
    Acc I projection η α ξ t b = S I projection η α ξ t b +
      ∑ b' ∈ Finset.range b, M I projection η α ξ t b' := by
  rw [Acc_eq_sum]
  unfold S dZ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b' _; abel

include h in
lemma measurable_meanGrad_y :
    Measurable (fun y : q.E × (Fin q.n → ℝ) => meanGrad I α y.1 y.2) := by
  unfold meanGrad
  refine Measurable.const_smul (Finset.measurable_sum _ fun i _ => ?_) _
  have hA := h.anchor i
  have hs : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × q.Ξ => I.score i p.1.1 p.2) :=
    hA.meas_s.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × q.Ξ => I.grad i p.1.1 p.2) :=
    hA.meas_g.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hν : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × q.Ξ => p.1.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hspmd : Measurable (fun p : (q.E × (Fin q.n → ℝ)) × q.Ξ => spmd α (p.1.2 i) (I.score i p.1.1 p.2)) := by
    unfold spmd
    exact ((hν.add (measurable_log.comp (measurable_const.add (measurable_const.mul
      (measurable_exp.comp hs))))).sub (measurable_log.comp (measurable_const.add
      (measurable_const.mul (measurable_exp.comp hν)))))
  have hC : Measurable (fun y : q.E × (Fin q.n → ℝ) =>
      ∫ ζ', exp (I.score i y.1 ζ') • I.grad i y.1 ζ' ∂(I.law i : Measure q.Ξ)) :=
    (((measurable_exp.comp hs).smul hg).stronglyMeasurable.integral_prod_right').measurable
  have hE : Measurable (fun y : q.E × (Fin q.n → ℝ) =>
      ∫ ζ, exp (-(spmd α (y.2 i) (I.score i y.1 ζ))) ∂(I.law i : Measure q.Ξ)) :=
    ((measurable_exp.comp hspmd.neg).stronglyMeasurable.integral_prod_right').measurable
  have hrepr : (fun y : q.E × (Fin q.n → ℝ) => ∫ ζ, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i)
      y.1 (spmd α (y.2 i) (I.score i y.1 ζ)) ∂(I.law i : Measure q.Ξ)) =
      fun y => (∫ ζ, exp (-(spmd α (y.2 i) (I.score i y.1 ζ))) ∂(I.law i : Measure q.Ξ)) •
        ∫ ζ', exp (I.score i y.1 ζ') • I.grad i y.1 ζ' ∂(I.law i : Measure q.Ξ) := by
    funext y
    simp_rw [AnchorHyp.gradW_eq y.1]
    exact integral_smul_const _ _
  rw [hrepr]
  exact hE.smul hC

include h in
lemma measurable_dZ (t b : ℕ) : Measurable (fun ξ => dZ I projection η α ξ t b) :=
  (measurable_Z I η α h t b).sub (measurable_M I η α h t b)

include h in
lemma measurable_S (t b : ℕ) : Measurable (fun ξ => S I projection η α ξ t b) :=
  Finset.measurable_sum _ fun b' _ => measurable_dZ I η α h t b'

omit h in
lemma S_congr {ξ ξ' : ℕ → Seed q} (t b : ℕ) (hξ : ∀ i, i < callIdx q t b → ξ i = ξ' i) :
    S I projection η α ξ t b = S I projection η α ξ' t b := by
  have h2 : ∀ b' ∈ Finset.range b, M I projection η α ξ t b' = M I projection η α ξ' t b' := by
    intro b' hb'
    have hb' := Finset.mem_range.mp hb'
    unfold M
    rw [W_congr I projection η α t (fun i hi => hξ i (by unfold callIdx; omega)),
      Nb_congr I projection η α t b' (fun i hi => hξ i (by unfold callIdx at *; omega))]
  have hsum : ∑ b' ∈ Finset.range b, M I projection η α ξ t b' =
      ∑ b' ∈ Finset.range b, M I projection η α ξ' t b' := Finset.sum_congr rfl h2
  have e1 : S I projection η α ξ t b = Acc I projection η α ξ t b -
      ∑ b' ∈ Finset.range b, M I projection η α ξ t b' := by rw [Acc_eq_S]; abel
  have e2 : S I projection η α ξ' t b = Acc I projection η α ξ' t b -
      ∑ b' ∈ Finset.range b, M I projection η α ξ' t b' := by rw [Acc_eq_S]; abel
  rw [e1, e2, Acc_congr I projection η α t b hξ, hsum]

end Stage3c


section Stage3d

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)

include h in
lemma proj_contract (x : q.E) : ‖projection x - wstar‖ ^ 2 ≤ ‖x - wstar‖ ^ 2 := by
  have hineq := h.proj_ineq x wstar h.wstar_mem
  have hdecomp : x - wstar = (x - projection x) + (projection x - wstar) := by abel
  rw [hdecomp, norm_add_sq_real]
  have : 0 ≤ ⟪x - projection x, projection x - wstar⟫ := by
    rw [← neg_sub wstar (projection x), inner_neg_right]; linarith
  nlinarith [sq_nonneg ‖x - projection x‖]

omit h in
lemma Accsq_le_sum (ξ : ℕ → Seed q) (t b : ℕ) :
    ‖Acc I projection η α ξ t b‖ ^ 2 ≤ b * ∑ b' ∈ Finset.range b, ‖Z I projection η α ξ t b'‖ ^ 2 := by
  rw [Acc_eq_sum]
  have h1 : ‖∑ b' ∈ Finset.range b, Z I projection η α ξ t b'‖ ^ 2 ≤
      (∑ b' ∈ Finset.range b, ‖Z I projection η α ξ t b'‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range b) (f := fun b' => ‖Z I projection η α ξ t b'‖)
  rw [Finset.card_range] at h2
  exact h1.trans h2

include h hα in
lemma sumZsq_int (t b : ℕ) :
    Integrable (fun ξ => ∑ b' ∈ Finset.range b, ‖Z I projection η α ξ t b'‖ ^ 2) (PP I) :=
  integrable_finsetSum _ fun b' _ => (Zsq_bounds I η α h hα t b').1

include h hα in
lemma Accsq_int (t b : ℕ) : Integrable (fun ξ => ‖Acc I projection η α ξ t b‖ ^ 2) (PP I) := by
  refine Integrable.mono' ((sumZsq_int I η α h hα t b).const_mul (b : ℝ))
    ((measurable_Acc I η α h t b).norm.pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact Accsq_le_sum I η α ξ t b

include h hα in
lemma Wdist_sq_int : ∀ t, Integrable (fun ξ => ‖W I projection η α ξ t - wstar‖ ^ 2) (PP I) := by
  intro t
  induction t with
  | zero => simp only [W_zero]; exact integrable_const _
  | succ t ih =>
    have hpt : ∀ ξ, ‖W I projection η α ξ (t + 1) - wstar‖ ^ 2 ≤
        2 * ‖W I projection η α ξ t - wstar‖ ^ 2 +
        2 * (η / q.B) ^ 2 * ‖Acc I projection η α ξ t q.B‖ ^ 2 := by
      intro ξ
      rw [W_succ]
      refine (proj_contract I h _).trans ?_
      have hdecomp : W I projection η α ξ t - (η / q.B) • Acc I projection η α ξ t q.B - wstar =
          (W I projection η α ξ t - wstar) - (η / q.B) • Acc I projection η α ξ t q.B := by abel
      rw [hdecomp, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have := abs_real_inner_le_norm (W I projection η α ξ t - wstar) ((η / q.B) • Acc I projection η α ξ t q.B)
      rw [norm_smul, Real.norm_eq_abs] at this
      have hab := (abs_le.mp this).2
      have hab' := (abs_le.mp this).1
      nlinarith [sq_nonneg (‖W I projection η α ξ t - wstar‖ - |η / q.B| * ‖Acc I projection η α ξ t q.B‖),
        sq_abs (η / q.B)]
    have hdom : Integrable (fun ξ => 2 * ‖W I projection η α ξ t - wstar‖ ^ 2 +
        2 * (η / q.B) ^ 2 * ‖Acc I projection η α ξ t q.B‖ ^ 2) (PP I) :=
      (ih.const_mul 2).add ((Accsq_int I η α h hα t q.B).const_mul _)
    refine Integrable.mono' hdom
      (((measurable_W I η α h (t + 1)).sub measurable_const).norm.pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ξ

include h hα in
lemma Msq_bounded (ξ : ℕ → Seed q) (t b : ℕ) :
    ‖M I projection η α ξ t b‖ ^ 2 ≤ 2 * q.κ * q.G ^ 2 + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * exp (q.c1 - q.c0) := by
  have h1 : ‖M I projection η α ξ t b‖ ^ 2 ≤ 2 * q.κ * q.G ^ 2 + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 *
      virtualGap I α (W I projection η α ξ t) (Nb I projection η α ξ t b) :=
    h.meanGrad_sq_le (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)
  have h2 := Vgap_le I η α h hα ξ t b
  have h0 : 0 ≤ 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 := by
    have := h.hκ; positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

include h hα in
lemma dZsq_int (t b : ℕ) : Integrable (fun ξ => ‖dZ I projection η α ξ t b‖ ^ 2) (PP I) := by
  have hdom : Integrable (fun ξ => 2 * ‖Z I projection η α ξ t b‖ ^ 2 +
      2 * ‖M I projection η α ξ t b‖ ^ 2) (PP I) :=
    ((Zsq_bounds I η α h hα t b).1.const_mul 2).add ((Msq_bound I η α h hα t b).1.const_mul 2)
  refine Integrable.mono' hdom ((measurable_dZ I η α h t b).norm.pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold dZ
    have := norm_sub_le (Z I projection η α ξ t b) (M I projection η α ξ t b)
    nlinarith [sq_nonneg (‖Z I projection η α ξ t b‖ - ‖M I projection η α ξ t b‖), norm_nonneg
      (Z I projection η α ξ t b), norm_nonneg (M I projection η α ξ t b), norm_nonneg (Z I projection η α ξ t b - M I projection η α ξ t b)]

include h hα in
lemma Ssq_int (t b : ℕ) : Integrable (fun ξ => ‖S I projection η α ξ t b‖ ^ 2) (PP I) := by
  refine Integrable.mono' ((integrable_finsetSum _ fun b' (_ : b' ∈ Finset.range b) =>
    dZsq_int I η α h hα t b').const_mul (b : ℝ))
    ((measurable_S I η α h t b).norm.pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold S
    have h1 : ‖∑ b' ∈ Finset.range b, dZ I projection η α ξ t b'‖ ^ 2 ≤
        (∑ b' ∈ Finset.range b, ‖dZ I projection η α ξ t b'‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range b) (f := fun b' => ‖dZ I projection η α ξ t b'‖)
    rw [Finset.card_range] at h2
    exact h1.trans h2

omit h in
lemma inner_abs_le_sq (u v : q.E) : |⟪u, v⟫| ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  have := abs_real_inner_le_norm u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

include h hα in
lemma inner_Z_expect (t b : ℕ) :
    Integrable (fun ξ => ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫) (PP I) ∧
    ∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I) =
      ∫ ξ, ⟪M I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I) := by
  let Φ : q.E × (Fin q.n → ℝ) → Seed q → ℝ := fun y ω => ⟪piece I α y.1 y.2 ω, y.1 - wstar⟫
  have hΦ : Measurable (Function.uncurry Φ) :=
    Measurable.inner (measurable_piece_joint I α h) ((measurable_fst.comp measurable_fst).sub measurable_const)
  have hG : Measurable (fun ξ => (W I projection η α ξ t, Nb I projection η α ξ t b)) :=
    (measurable_W I η α h t).prodMk (measurable_Nb I η α h t b)
  have hGc : ∀ ξ ξ' : ℕ → Seed q, (∀ i, i < callIdx q t b → ξ i = ξ' i) →
      (W I projection η α ξ t, Nb I projection η α ξ t b) =
      (W I projection η α ξ' t, Nb I projection η α ξ' t b) := fun ξ ξ' hξ => by
    rw [W_congr I projection η α t (fun i hi => hξ i (by unfold callIdx; omega)),
      Nb_congr I projection η α t b hξ]
  have hdom : Integrable (fun ξ => (1 / 2) * (‖Z I projection η α ξ t b‖ ^ 2 +
      ‖W I projection η α ξ t - wstar‖ ^ 2)) (PP I) :=
    ((Zsq_bounds I η α h hα t b).1.add (Wdist_sq_int I η α h hα t)).const_mul (1 / 2)
  have hint' : Integrable (fun ξ => ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫) (PP I) := by
    refine Integrable.mono' hdom
      (Measurable.inner (measurable_Z I η α h t b) ((measurable_W I η α h t).sub measurable_const)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      have := inner_abs_le_sq (q := q) (Z I projection η α ξ t b) (W I projection η α ξ t - wstar)
      linarith
  have hZ : (fun ξ => ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫) =
      fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)) := rfl
  have hint : Integrable (fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b)
      (ξ (callIdx q t b))) (PP I) := by rw [← hZ]; exact hint'
  obtain ⟨_, heq⟩ := expect_substep_of_integrable I t b _ hG hGc Φ hΦ hint
  refine ⟨hint', ?_⟩
  rw [hZ, heq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [Φ]
    have hw := W_mem I η α h ξ t
    have hν := Nb_mem I η α h hα ξ t b
    have hp := h.piece_int hw hα hν
    rw [show (fun ω => ⟪piece I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ω,
        W I projection η α ξ t - wstar⟫) = fun ω => ⟪W I projection η α ξ t - wstar,
        piece I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ω⟫ by
      funext ω; rw [real_inner_comm]]
    rw [integral_inner hp, h.expected_piece hw hα hν, real_inner_comm]
    rfl

include h hα in
lemma inner_ZM_expect (t b : ℕ) :
    Integrable (fun ξ => ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫) (PP I) ∧
    ∫ ξ, ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫ ∂(PP I) =
      ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I) := by
  let Φ : q.E × (Fin q.n → ℝ) → Seed q → ℝ := fun y ω => ⟪piece I α y.1 y.2 ω, meanGrad I α y.1 y.2⟫
  have hΦ : Measurable (Function.uncurry Φ) :=
    Measurable.inner (measurable_piece_joint I α h) ((measurable_meanGrad_y I α h).comp measurable_fst)
  have hG : Measurable (fun ξ => (W I projection η α ξ t, Nb I projection η α ξ t b)) :=
    (measurable_W I η α h t).prodMk (measurable_Nb I η α h t b)
  have hGc : ∀ ξ ξ' : ℕ → Seed q, (∀ i, i < callIdx q t b → ξ i = ξ' i) →
      (W I projection η α ξ t, Nb I projection η α ξ t b) =
      (W I projection η α ξ' t, Nb I projection η α ξ' t b) := fun ξ ξ' hξ => by
    rw [W_congr I projection η α t (fun i hi => hξ i (by unfold callIdx; omega)),
      Nb_congr I projection η α t b hξ]
  have hdom : Integrable (fun ξ => (1 / 2) * (‖Z I projection η α ξ t b‖ ^ 2 +
      ‖M I projection η α ξ t b‖ ^ 2)) (PP I) :=
    ((Zsq_bounds I η α h hα t b).1.add (Msq_bound I η α h hα t b).1).const_mul (1 / 2)
  have hint' : Integrable (fun ξ => ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫) (PP I) := by
    refine Integrable.mono' hdom
      (Measurable.inner (measurable_Z I η α h t b) (measurable_M I η α h t b)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      have := inner_abs_le_sq (q := q) (Z I projection η α ξ t b) (M I projection η α ξ t b)
      linarith
  have hZ : (fun ξ => ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫) =
      fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b) (ξ (callIdx q t b)) := rfl
  have hint : Integrable (fun ξ => Φ (W I projection η α ξ t, Nb I projection η α ξ t b)
      (ξ (callIdx q t b))) (PP I) := by rw [← hZ]; exact hint'
  obtain ⟨_, heq⟩ := expect_substep_of_integrable I t b _ hG hGc Φ hΦ hint
  refine ⟨hint', ?_⟩
  rw [hZ, heq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [Φ]
    have hw := W_mem I η α h ξ t
    have hν := Nb_mem I η α h hα ξ t b
    have hp := h.piece_int hw hα hν
    rw [show (fun ω => ⟪piece I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ω,
        meanGrad I α (W I projection η α ξ t) (Nb I projection η α ξ t b)⟫) =
        fun ω => ⟪meanGrad I α (W I projection η α ξ t) (Nb I projection η α ξ t b),
        piece I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ω⟫ by
      funext ω; rw [real_inner_comm]]
    rw [integral_inner hp, h.expected_piece hw hα hν, real_inner_self_eq_norm_sq]
    rfl

include h hα in
lemma dZsq_le (t b : ℕ) :
    (∫ ξ, ‖dZ I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤ ∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I) := by
  have hpt : ∀ ξ, ‖dZ I projection η α ξ t b‖ ^ 2 = ‖Z I projection η α ξ t b‖ ^ 2 -
      2 * ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫ + ‖M I projection η α ξ t b‖ ^ 2 :=
    fun ξ => by unfold dZ; exact norm_sub_sq_real _ _
  have hi1 := (Zsq_bounds I η α h hα t b).1
  have hi2 := (inner_ZM_expect I η α h hα t b).1
  have hi3 := (Msq_bound I η α h hα t b).1
  have hfun : (fun ξ => ‖dZ I projection η α ξ t b‖ ^ 2) = fun ξ => ‖Z I projection η α ξ t b‖ ^ 2 -
      2 * ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫ + ‖M I projection η α ξ t b‖ ^ 2 :=
    funext hpt
  have hi12 : Integrable (fun ξ => ‖Z I projection η α ξ t b‖ ^ 2 -
      2 * ⟪Z I projection η α ξ t b, M I projection η α ξ t b⟫) (PP I) := hi1.sub (hi2.const_mul 2)
  rw [hfun, integral_add hi12 hi3, integral_sub hi1 (hi2.const_mul 2),
    integral_const_mul, (inner_ZM_expect I η α h hα t b).2]
  have hMnn : 0 ≤ ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I) :=
    integral_nonneg fun ξ => sq_nonneg _
  linarith

include h hα in
lemma inner_S_dZ_expect (t b : ℕ) :
    Integrable (fun ξ => ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫) (PP I) ∧
    ∫ ξ, ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫ ∂(PP I) = 0 := by
  let Φ : q.E × (q.E × (Fin q.n → ℝ)) → Seed q → ℝ := fun y ω =>
    ⟪y.1, piece I α y.2.1 y.2.2 ω - meanGrad I α y.2.1 y.2.2⟫
  have hΦ : Measurable (Function.uncurry Φ) := by
    have hp : Measurable (fun p : (q.E × (q.E × (Fin q.n → ℝ))) × Seed q => piece I α p.1.2.1 p.1.2.2 p.2) :=
      (measurable_piece_joint I α h).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hm : Measurable (fun p : (q.E × (q.E × (Fin q.n → ℝ))) × Seed q => meanGrad I α p.1.2.1 p.1.2.2) :=
      (measurable_meanGrad_y I α h).comp (measurable_snd.comp measurable_fst)
    exact Measurable.inner (measurable_fst.comp measurable_fst) (hp.sub hm)
  have hG : Measurable (fun ξ => (S I projection η α ξ t b, (W I projection η α ξ t, Nb I projection η α ξ t b))) :=
    (measurable_S I η α h t b).prodMk ((measurable_W I η α h t).prodMk (measurable_Nb I η α h t b))
  have hGc : ∀ ξ ξ' : ℕ → Seed q, (∀ i, i < callIdx q t b → ξ i = ξ' i) →
      (S I projection η α ξ t b, (W I projection η α ξ t, Nb I projection η α ξ t b)) =
      (S I projection η α ξ' t b, (W I projection η α ξ' t, Nb I projection η α ξ' t b)) := fun ξ ξ' hξ => by
    rw [S_congr I η α t b hξ, W_congr I projection η α t (fun i hi => hξ i (by unfold callIdx; omega)),
      Nb_congr I projection η α t b hξ]
  have hdom : Integrable (fun ξ => (1 / 2) * (‖S I projection η α ξ t b‖ ^ 2 +
      ‖dZ I projection η α ξ t b‖ ^ 2)) (PP I) :=
    ((Ssq_int I η α h hα t b).add (dZsq_int I η α h hα t b)).const_mul (1 / 2)
  have hint' : Integrable (fun ξ => ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫) (PP I) := by
    refine Integrable.mono' hdom
      (Measurable.inner (measurable_S I η α h t b) (measurable_dZ I η α h t b)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      have := inner_abs_le_sq (q := q) (S I projection η α ξ t b) (dZ I projection η α ξ t b)
      linarith
  have hZ : (fun ξ => ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫) =
      fun ξ => Φ (S I projection η α ξ t b, (W I projection η α ξ t, Nb I projection η α ξ t b))
        (ξ (callIdx q t b)) := rfl
  have hint : Integrable (fun ξ => Φ (S I projection η α ξ t b,
      (W I projection η α ξ t, Nb I projection η α ξ t b)) (ξ (callIdx q t b))) (PP I) := by
    rw [← hZ]; exact hint'
  obtain ⟨_, heq⟩ := expect_substep_of_integrable I t b _ hG hGc Φ hΦ hint
  refine ⟨hint', ?_⟩
  rw [hZ, heq]
  have hzero : ∀ ξ, (∫ ω, Φ (S I projection η α ξ t b, (W I projection η α ξ t, Nb I projection η α ξ t b)) ω
      ∂(sampleLaw I)) = 0 := by
    intro ξ
    simp only [Φ]
    have hw := W_mem I η α h ξ t
    have hν := Nb_mem I η α h hα ξ t b
    have hp := h.piece_int hw hα hν
    have hps : Integrable (fun ω => piece I α (W I projection η α ξ t) (Nb I projection η α ξ t b) ω -
        meanGrad I α (W I projection η α ξ t) (Nb I projection η α ξ t b)) (sampleLaw I) :=
      hp.sub (integrable_const _)
    rw [integral_inner hps, integral_sub hp (integrable_const _), h.expected_piece hw hα hν]
    simp
  simp only [hzero, integral_zero]

include h hα in
lemma Ssq_le (t : ℕ) : ∀ b, (∫ ξ, ‖S I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
    ∑ b' ∈ Finset.range b, ∫ ξ, ‖Z I projection η α ξ t b'‖ ^ 2 ∂(PP I) := by
  intro b
  induction b with
  | zero => simp [S]
  | succ b ih =>
    have hpt : ∀ ξ, ‖S I projection η α ξ t (b + 1)‖ ^ 2 = ‖S I projection η α ξ t b‖ ^ 2 +
        2 * ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫ + ‖dZ I projection η α ξ t b‖ ^ 2 :=
      fun ξ => by rw [S_succ]; exact norm_add_sq_real _ _
    have hfun : (fun ξ => ‖S I projection η α ξ t (b + 1)‖ ^ 2) = fun ξ => ‖S I projection η α ξ t b‖ ^ 2 +
        2 * ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫ + ‖dZ I projection η α ξ t b‖ ^ 2 :=
      funext hpt
    have hi12 : Integrable (fun ξ => ‖S I projection η α ξ t b‖ ^ 2 +
        2 * ⟪S I projection η α ξ t b, dZ I projection η α ξ t b⟫) (PP I) :=
      (Ssq_int I η α h hα t b).add ((inner_S_dZ_expect I η α h hα t b).1.const_mul 2)
    rw [hfun, integral_add hi12 (dZsq_int I η α h hα t b), integral_add (Ssq_int I η α h hα t b)
      ((inner_S_dZ_expect I η α h hα t b).1.const_mul 2), integral_const_mul,
      (inner_S_dZ_expect I η α h hα t b).2, Finset.sum_range_succ]
    linarith [dZsq_le I η α h hα t b]

include h hα in
lemma Accsq_expect (t b : ℕ) :
    (∫ ξ, ‖Acc I projection η α ξ t b‖ ^ 2 ∂(PP I)) ≤
      2 * ∑ b' ∈ Finset.range b, (∫ ξ, ‖Z I projection η α ξ t b'‖ ^ 2 ∂(PP I)) +
      2 * b * ∑ b' ∈ Finset.range b, ∫ ξ, ‖M I projection η α ξ t b'‖ ^ 2 ∂(PP I) := by
  have hpt : ∀ ξ, ‖Acc I projection η α ξ t b‖ ^ 2 ≤ 2 * ‖S I projection η α ξ t b‖ ^ 2 +
      2 * b * ∑ b' ∈ Finset.range b, ‖M I projection η α ξ t b'‖ ^ 2 := by
    intro ξ
    rw [Acc_eq_S]
    have h1 : ‖S I projection η α ξ t b + ∑ b' ∈ Finset.range b, M I projection η α ξ t b'‖ ^ 2 ≤
        2 * ‖S I projection η α ξ t b‖ ^ 2 + 2 * ‖∑ b' ∈ Finset.range b, M I projection η α ξ t b'‖ ^ 2 := by
      have := norm_add_le (S I projection η α ξ t b) (∑ b' ∈ Finset.range b, M I projection η α ξ t b')
      nlinarith [sq_nonneg (‖S I projection η α ξ t b‖ - ‖∑ b' ∈ Finset.range b, M I projection η α ξ t b'‖),
        norm_nonneg (S I projection η α ξ t b + ∑ b' ∈ Finset.range b, M I projection η α ξ t b')]
    have h2 : ‖∑ b' ∈ Finset.range b, M I projection η α ξ t b'‖ ^ 2 ≤
        b * ∑ b' ∈ Finset.range b, ‖M I projection η α ξ t b'‖ ^ 2 := by
      have ha : ‖∑ b' ∈ Finset.range b, M I projection η α ξ t b'‖ ^ 2 ≤
          (∑ b' ∈ Finset.range b, ‖M I projection η α ξ t b'‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      have hb := sq_sum_le_card_mul_sum_sq (s := Finset.range b) (f := fun b' => ‖M I projection η α ξ t b'‖)
      rw [Finset.card_range] at hb
      exact ha.trans hb
    nlinarith
  have hiM : Integrable (fun ξ => ∑ b' ∈ Finset.range b, ‖M I projection η α ξ t b'‖ ^ 2) (PP I) :=
    integrable_finsetSum _ fun b' _ => (Msq_bound I η α h hα t b').1
  have hi2 : Integrable (fun ξ => 2 * ‖S I projection η α ξ t b‖ ^ 2 +
      2 * b * ∑ b' ∈ Finset.range b, ‖M I projection η α ξ t b'‖ ^ 2) (PP I) :=
    ((Ssq_int I η α h hα t b).const_mul 2).add (hiM.const_mul _)
  calc _ ≤ _ := integral_mono (Accsq_int I η α h hα t b) hi2 hpt
    _ = 2 * (∫ ξ, ‖S I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
        2 * b * ∑ b' ∈ Finset.range b, ∫ ξ, ‖M I projection η α ξ t b'‖ ^ 2 ∂(PP I) := by
        rw [integral_add ((Ssq_int I η α h hα t b).const_mul 2) (hiM.const_mul _), integral_const_mul,
          integral_const_mul, integral_finsetSum _ fun b' _ => (Msq_bound I η α h hα t b').1]
    _ ≤ _ := by
        have := Ssq_le I η α h hα t b
        nlinarith

include h in
lemma primal_step (ξ : ℕ → Seed q) (t : ℕ) :
    ‖W I projection η α ξ (t + 1) - wstar‖ ^ 2 ≤ ‖W I projection η α ξ t - wstar‖ ^ 2 -
      2 * (η / q.B) * ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫ +
      (η / q.B) ^ 2 * ‖Acc I projection η α ξ t q.B‖ ^ 2 := by
  rw [W_succ]
  refine (proj_contract I h _).trans ?_
  have hdecomp : W I projection η α ξ t - (η / q.B) • Acc I projection η α ξ t q.B - wstar =
      (W I projection η α ξ t - wstar) - (η / q.B) • Acc I projection η α ξ t q.B := by abel
  rw [hdecomp, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right,
    real_inner_comm]
  ring_nf
  exact le_refl _

end Stage3d


section Stage4

variable {projection} {wstar : q.E} (h : SysHyp I projection wstar) (hα : 0 ≤ α)

include h in
lemma measurable_objective : Measurable (objective I) := by
  unfold objective normalizer
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  refine measurable_log.comp ?_
  exact ((measurable_exp.comp ((h.anchor i).meas_s)).stronglyMeasurable.integral_prod_right').measurable

include h in
lemma objective_bounds {w : q.E} (hw : w ∈ I.domain) : q.c0 ≤ objective I w ∧ objective I w ≤ q.c1 := by
  unfold objective
  have hper : ∀ i, q.c0 ≤ log (normalizer I i w) ∧ log (normalizer I i w) ≤ q.c1 := fun i =>
    (h.anchor i).log_mass_mem hw
  constructor
  · have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hper i).1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc q.c0 = (q.n : ℝ)⁻¹ * ((q.n : ℝ) * q.c0) := by
          rw [← mul_assoc, inv_mul_cancel₀ (SysHyp.n_pos (q := q)).ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (Nat.cast_nonneg _))
  · have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hper i).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc _ ≤ (q.n : ℝ)⁻¹ * ((q.n : ℝ) * q.c1) := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = q.c1 := by rw [← mul_assoc, inv_mul_cancel₀ (SysHyp.n_pos (q := q)).ne', one_mul]

include h hα in
lemma Vobj_eq (ξ : ℕ → Seed q) (t b : ℕ) :
    Vobj I projection η α ξ t b = Vgap I projection η α ξ t b + (1 + objective I (W I projection η α ξ t)) := by
  unfold Vobj Vgap
  rw [h.virtualGap_eq (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)]
  ring

include h hα in
lemma Vobj_int (t b : ℕ) : Integrable (fun ξ => Vobj I projection η α ξ t b) (PP I) := by
  have hfun : (fun ξ => Vobj I projection η α ξ t b) = fun ξ => Vgap I projection η α ξ t b +
      (1 + objective I (W I projection η α ξ t)) := funext (Vobj_eq I η α h hα · t b)
  rw [hfun]
  refine (Vgap_int I η α h hα t b).add ((integrable_const _).add ?_)
  refine Integrable.of_bound ((measurable_objective I h).comp (measurable_W I η α h t)).aestronglyMeasurable
    (|q.c0| + |q.c1|) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs]
    have := objective_bounds I h (W_mem I η α h ξ t)
    rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;> linarith

include h hα in
lemma Vgap_le_Vobj (ξ : ℕ → Seed q) (t b : ℕ) :
    Vgap I projection η α ξ t b ≤ Vobj I projection η α ξ t b - Fstar I wstar :=
  h.virtualGap_le (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)

include h hα in
lemma vv_le_inner_reg (t b : ℕ) :
    (∫ ξ, (Vobj I projection η α ξ t b - Fstar I wstar) ∂(PP I)) ≤
      (∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I)) +
      ∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I) := by
  have hpt : ∀ ξ, Vobj I projection η α ξ t b - Fstar I wstar ≤
      ⟪M I projection η α ξ t b, W I projection η α ξ t - wstar⟫ + Reg I projection η α wstar ξ t b :=
    fun ξ => h.virtual_joint_convex (W_mem I η α h ξ t) hα (Nb_mem I η α h hα ξ t b)
  have hiM : Integrable (fun ξ => ⟪M I projection η α ξ t b, W I projection η α ξ t - wstar⟫) (PP I) := by
    have hdom : Integrable (fun ξ => (1 / 2) * (‖M I projection η α ξ t b‖ ^ 2 +
        ‖W I projection η α ξ t - wstar‖ ^ 2)) (PP I) :=
      ((Msq_bound I η α h hα t b).1.add (Wdist_sq_int I η α h hα t)).const_mul (1 / 2)
    refine Integrable.mono' hdom
      (Measurable.inner (measurable_M I η α h t b) ((measurable_W I η α h t).sub measurable_const)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      have := inner_abs_le_sq (q := q) (M I projection η α ξ t b) (W I projection η α ξ t - wstar)
      linarith
  have hi_rhs : Integrable (fun ξ => ⟪M I projection η α ξ t b, W I projection η α ξ t - wstar⟫ +
      Reg I projection η α wstar ξ t b) (PP I) := hiM.add (Reg_int I η α h hα t b)
  have := integral_mono ((Vobj_int I η α h hα t b).sub (integrable_const _)) hi_rhs hpt
  rw [integral_add hiM (Reg_int I η α h hα t b), ← (inner_Z_expect I η α h hα t b).2] at this
  exact this

include h hα in
lemma sum_inner_eq (t : ℕ) :
    ∑ b ∈ Finset.range q.B, (∫ ξ, ⟪Z I projection η α ξ t b, W I projection η α ξ t - wstar⟫ ∂(PP I)) =
      ∫ ξ, ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫ ∂(PP I) := by
  rw [← integral_finsetSum _ fun b _ => (inner_Z_expect I η α h hα t b).1]
  congr 1
  funext ξ
  rw [Acc_eq_sum, sum_inner]

include h hα in
lemma inner_Acc_le (hη : 0 < η) (hB : 0 < q.B) (t : ℕ) :
    (∫ ξ, ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫ ∂(PP I)) ≤
      (q.B / (2 * η)) * ((∫ ξ, ‖W I projection η α ξ t - wstar‖ ^ 2 ∂(PP I)) -
        ∫ ξ, ‖W I projection η α ξ (t + 1) - wstar‖ ^ 2 ∂(PP I)) +
      (η / (2 * q.B)) * ∫ ξ, ‖Acc I projection η α ξ t q.B‖ ^ 2 ∂(PP I) := by
  have hpt := primal_step I η α h
  have hiA : Integrable (fun ξ => ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫) (PP I) := by
    have hdom : Integrable (fun ξ => (1 / 2) * (‖Acc I projection η α ξ t q.B‖ ^ 2 +
        ‖W I projection η α ξ t - wstar‖ ^ 2)) (PP I) :=
      ((Accsq_int I η α h hα t q.B).add (Wdist_sq_int I η α h hα t)).const_mul (1 / 2)
    refine Integrable.mono' hdom
      (Measurable.inner (measurable_Acc I η α h t q.B) ((measurable_W I η α h t).sub measurable_const)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      have := inner_abs_le_sq (q := q) (Acc I projection η α ξ t q.B) (W I projection η α ξ t - wstar)
      linarith
  have hi1 : Integrable (fun ξ => ‖W I projection η α ξ t - wstar‖ ^ 2 -
      2 * (η / q.B) * ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫) (PP I) :=
    (Wdist_sq_int I η α h hα t).sub (hiA.const_mul _)
  have hi_rhs : Integrable (fun ξ => ‖W I projection η α ξ t - wstar‖ ^ 2 -
      2 * (η / q.B) * ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫ +
      (η / q.B) ^ 2 * ‖Acc I projection η α ξ t q.B‖ ^ 2) (PP I) :=
    hi1.add ((Accsq_int I η α h hα t q.B).const_mul _)
  have := integral_mono (Wdist_sq_int I η α h hα (t + 1)) hi_rhs (hpt · t)
  rw [integral_add hi1 ((Accsq_int I η α h hα t q.B).const_mul _),
    integral_sub (Wdist_sq_int I η α h hα t) (hiA.const_mul _), integral_const_mul, integral_const_mul] at this
  have hBpos : (0 : ℝ) < q.B := by exact_mod_cast hB
  have hηB : 0 < η / q.B := div_pos hη hBpos
  set A := ∫ ξ, ⟪Acc I projection η α ξ t q.B, W I projection η α ξ t - wstar⟫ ∂(PP I)
  set D0 := ∫ ξ, ‖W I projection η α ξ t - wstar‖ ^ 2 ∂(PP I)
  set D1 := ∫ ξ, ‖W I projection η α ξ (t + 1) - wstar‖ ^ 2 ∂(PP I)
  set Q := ∫ ξ, ‖Acc I projection η α ξ t q.B‖ ^ 2 ∂(PP I)
  have h2 : 2 * (η / q.B) * A ≤ D0 - D1 + (η / q.B) ^ 2 * Q := by linarith
  have hkey : A ≤ (D0 - D1 + (η / q.B) ^ 2 * Q) / (2 * (η / q.B)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc A ≤ (D0 - D1 + (η / q.B) ^ 2 * Q) / (2 * (η / q.B)) := hkey
    _ = (q.B / (2 * η)) * (D0 - D1) + (η / (2 * q.B)) * Q := by
        field_simp

include h hα in
lemma Accsq_total (t : ℕ) :
    (∫ ξ, ‖Acc I projection η α ξ t q.B‖ ^ 2 ∂(PP I)) ≤
      2 * ∑ b ∈ Finset.range q.B, (∫ ξ, ‖Z I projection η α ξ t b‖ ^ 2 ∂(PP I)) +
      2 * q.B * ∑ b ∈ Finset.range q.B, ∫ ξ, ‖M I projection η α ξ t b‖ ^ 2 ∂(PP I) :=
  Accsq_expect I η α h hα t q.B

omit h in
lemma Dpot_zero_eq (ξ : ℕ → Seed q) : Dpot I projection η α wstar ξ 0 0 =
    dualPot (nuStar I wstar) (fun _ => q.c1) := rfl

include h hα in
lemma dual_telescope {ρ : ℝ} (hρ : α * exp q.c1 ≤ ρ) (T : ℕ) :
    α * ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, (∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I)) ≤
      dualPot (nuStar I wstar) (fun _ => q.c1) +
      (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 *
        ∑ t ∈ Finset.range T, ∑ b ∈ Finset.range q.B, ∫ ξ, Dnoise I projection η α ξ t b ∂(PP I) := by
  set C := (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2
  have hinner : ∀ t, α * ∑ b ∈ Finset.range q.B, (∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I)) ≤
      (∫ ξ, Dpot I projection η α wstar ξ t 0 ∂(PP I)) - (∫ ξ, Dpot I projection η α wstar ξ t q.B ∂(PP I)) +
      C * ∑ b ∈ Finset.range q.B, ∫ ξ, Dnoise I projection η α ξ t b ∂(PP I) := by
    intro t
    have hstep := fun b => dual_step_expect I η α h hα hρ t b
    have : ∀ B', α * ∑ b ∈ Finset.range B', (∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I)) ≤
        (∫ ξ, Dpot I projection η α wstar ξ t 0 ∂(PP I)) - (∫ ξ, Dpot I projection η α wstar ξ t B' ∂(PP I)) +
        C * ∑ b ∈ Finset.range B', ∫ ξ, Dnoise I projection η α ξ t b ∂(PP I) := by
      intro B'
      induction B' with
      | zero => simp
      | succ B' ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
        have := hstep B'
        linarith
    exact this q.B
  have hsucc : ∀ t, (∫ ξ, Dpot I projection η α wstar ξ t q.B ∂(PP I)) =
      ∫ ξ, Dpot I projection η α wstar ξ (t + 1) 0 ∂(PP I) := fun t => rfl
  have htel : ∀ T', α * ∑ t ∈ Finset.range T', ∑ b ∈ Finset.range q.B,
      (∫ ξ, Reg I projection η α wstar ξ t b ∂(PP I)) ≤
      (∫ ξ, Dpot I projection η α wstar ξ 0 0 ∂(PP I)) - (∫ ξ, Dpot I projection η α wstar ξ T' 0 ∂(PP I)) +
      C * ∑ t ∈ Finset.range T', ∑ b ∈ Finset.range q.B, ∫ ξ, Dnoise I projection η α ξ t b ∂(PP I) := by
    intro T'
    induction T' with
    | zero => simp
    | succ T' ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      have := hinner T'
      rw [hsucc T'] at this
      linarith
  have hT := htel T
  have hnn : 0 ≤ ∫ ξ, Dpot I projection η α wstar ξ T 0 ∂(PP I) :=
    integral_nonneg fun ξ => Dpot_nonneg I η α ξ T 0
  have h0 : (∫ ξ, Dpot I projection η α wstar ξ 0 0 ∂(PP I)) = dualPot (nuStar I wstar) (fun _ => q.c1) := by
    simp only [Dpot_zero_eq I η α, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [h0] at hT
  linarith

end Stage4

end OracleTemplate.Scent
