import LongTails.Proofs.HeavyTailedSospExecution
import LongTails.Proofs.AdaptiveEntropicMeasurable
import Mathlib.Logic.Equiv.Option

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open scoped OracleTemplate.AdaptiveList

namespace LongTails.Proofs.HeavyTailedSospMeasurable

set_option backward.isDefEq.respectTransparency false

abbrev ProbeCode (d : ℕ) := ℕ × ℕ × EuclideanSpace ℝ (Fin d) ×
  EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × Bool

def probeEquiv (d : ℕ) : LongTails.Algorithms.HeavyTailedEnergyProbe.State d ≃ ProbeCode d where
  toFun s := (s.index, s.target, s.fallback, s.vector, s.selected, s.alive)
  invFun w := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by rcases w with ⟨a, b, c, d, e, f⟩; rfl

instance (d : ℕ) : MeasurableSpace (LongTails.Algorithms.HeavyTailedEnergyProbe.State d) :=
  MeasurableSpace.comap (probeEquiv d) inferInstance

abbrev ResumeCode (p : Params) := Unit ⊕ Unit ⊕ (ℕ × Space p)

def resumeCode (p : Params) : Resume p → ResumeCode p
  | .startCycle => .inl ()
  | .detect => .inr (.inl ())
  | .ncRest n v => .inr (.inr (n, v))

def codeResume (p : Params) : ResumeCode p → Resume p
  | .inl _ => .startCycle
  | .inr (.inl _) => .detect
  | .inr (.inr (n, v)) => .ncRest n v

instance (p : Params) : MeasurableSpace (Resume p) :=
  MeasurableSpace.comap (resumeCode p) inferInstance

abbrev AcceptedCode (p : Params) := Space p ⊕ PUnit.{1}

abbrev PhaseCode (p : Params) :=
  (ℕ × Space p × Resume p) ⊕ (Space p × ℕ × Space p × Resume p) ⊕
  (ℕ × AcceptedCode p) ⊕
  (ℕ × AcceptedCode p × LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) ⊕
  (ℕ × AcceptedCode p × Space p × List ℝ) ⊕ Space p ⊕ Unit

def phaseCode (p : Params) : Phase p → PhaseCode p
  | .reset k z a => .inl (k, z, a)
  | .transport v k z a => .inr (.inl (v, k, z, a))
  | .probeInit k a => .inr (.inr (.inl (k, Equiv.optionEquivSumPUnit.{0, 0} (Space p) a)))
  | .probe k a s => .inr (.inr (.inr (.inl (k, Equiv.optionEquivSumPUnit.{0, 0} (Space p) a, s))))
  | .validate k a v l => .inr (.inr (.inr (.inr (.inl (k, Equiv.optionEquivSumPUnit.{0, 0} (Space p) a, v, l)))))
  | .ncInit v => .inr (.inr (.inr (.inr (.inr (.inl v)))))
  | .done => .inr (.inr (.inr (.inr (.inr (.inr ())))))

def codePhase (p : Params) : PhaseCode p → Phase p
  | .inl (k, z, a) => .reset k z a
  | .inr (.inl (v, k, z, a)) => .transport v k z a
  | .inr (.inr (.inl (k, a))) => .probeInit k ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm a)
  | .inr (.inr (.inr (.inl (k, a, s)))) => .probe k ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm a) s
  | .inr (.inr (.inr (.inr (.inl (k, a, v, l))))) =>
    .validate k ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm a) v l
  | .inr (.inr (.inr (.inr (.inr (.inl v))))) => .ncInit v
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .done

instance (p : Params) : MeasurableSpace (Phase p) :=
  MeasurableSpace.comap (phaseCode p) inferInstance

abbrev StateCode (p : Params) := Space p × Space p × ℕ × ℕ × ℕ × Space p × Phase p

def stateEquiv (p : Params) : State p ≃ StateCode p where
  toFun s := (s.point, s.estimate, s.virtualIndex, s.cycleIndex, s.target, s.selected, s.phase)
  invFun w := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by rcases w with ⟨a, b, c, d, e, f, g⟩; rfl

instance (p : Params) : MeasurableSpace (State p) :=
  MeasurableSpace.comap (stateEquiv p) inferInstance

lemma codeResume_resumeCode (p : Params) (r : Resume p) : codeResume p (resumeCode p r) = r := by
  cases r <;> rfl

lemma codePhase_phaseCode (p : Params) (r : Phase p) : codePhase p (phaseCode p r) = r := by
  cases r <;> simp [phaseCode, codePhase]

@[fun_prop] lemma measurable_point (p : Params) : Measurable (fun s : State p => s.point) :=
  (comap_measurable (stateEquiv p)).fst

@[fun_prop] lemma measurable_estimate (p : Params) : Measurable (fun s : State p => s.estimate) :=
  (comap_measurable (stateEquiv p)).snd.fst

@[fun_prop] lemma measurable_virtualIndex (p : Params) : Measurable (fun s : State p => s.virtualIndex) :=
  (comap_measurable (stateEquiv p)).snd.snd.fst

@[fun_prop] lemma measurable_cycleIndex (p : Params) : Measurable (fun s : State p => s.cycleIndex) :=
  (comap_measurable (stateEquiv p)).snd.snd.snd.fst

@[fun_prop] lemma measurable_target (p : Params) : Measurable (fun s : State p => s.target) :=
  (comap_measurable (stateEquiv p)).snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_selected (p : Params) : Measurable (fun s : State p => s.selected) :=
  (comap_measurable (stateEquiv p)).snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_phase (p : Params) : Measurable (fun s : State p => s.phase) :=
  (comap_measurable (stateEquiv p)).snd.snd.snd.snd.snd.snd

@[fun_prop] lemma measurable_mk (p : Params) {Z : Type*} [MeasurableSpace Z]
    {x e o : Z → Space p} {v k t : Z → ℕ} {ph : Z → Phase p}
    (hx : Measurable x) (he : Measurable e) (hv : Measurable v) (hk : Measurable k)
    (ht : Measurable t) (ho : Measurable o) (hph : Measurable ph) :
    Measurable (fun z => State.mk (x z) (e z) (v z) (k z) (t z) (o z) (ph z)) := by
  apply measurable_comap_iff.mpr
  exact hx.prodMk (he.prodMk (hv.prodMk (hk.prodMk (ht.prodMk (ho.prodMk hph)))))


lemma measurable_sum_uncurry {A B Z Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace Z] [MeasurableSpace Y] {F : A ⊕ B → Z → Y}
    (ha : Measurable (fun z : A × Z => F (.inl z.1) z.2))
    (hb : Measurable (fun z : B × Z => F (.inr z.1) z.2)) :
    Measurable (fun z : (A ⊕ B) × Z => F z.1 z.2) := by
  apply (MeasurableEquiv.sumProdDistrib A B Z).symm.measurable_comp_iff.mp
  exact measurable_fun_sum ha hb

lemma measurable_phase_uncurry (p : Params) {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {F : Phase p → Z → Y}
    (hr : Measurable (fun w : (ℕ × Space p × Resume p) × Z => F (.reset w.1.1 w.1.2.1 w.1.2.2) w.2))
    (ht : Measurable (fun w : (Space p × ℕ × Space p × Resume p) × Z =>
      F (.transport w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2) w.2))
    (hi : Measurable (fun w : (ℕ × AcceptedCode p) × Z =>
      F (.probeInit w.1.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2)) w.2))
    (hp : Measurable (fun w : (ℕ × AcceptedCode p ×
        LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) × Z =>
      F (.probe w.1.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2.1) w.1.2.2) w.2))
    (hv : Measurable (fun w : (ℕ × AcceptedCode p × Space p × List ℝ) × Z =>
      F (.validate w.1.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2.1) w.1.2.2.1 w.1.2.2.2) w.2))
    (hn : Measurable (fun w : Space p × Z => F (.ncInit w.1) w.2))
    (hd : Measurable (fun w : Unit × Z => F .done w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : PhaseCode p × Z => F (codePhase p w.1) w.2) := by
    apply measurable_sum_uncurry (F := fun ph z => F (codePhase p ph) z)
    · exact hr
    · apply measurable_sum_uncurry (F := fun ph z => F (codePhase p (.inr ph)) z)
      · exact ht
      · apply measurable_sum_uncurry (F := fun ph z => F (codePhase p (.inr (.inr ph))) z)
        · exact hi
        · apply measurable_sum_uncurry (F := fun ph z => F (codePhase p (.inr (.inr (.inr ph)))) z)
          · exact hp
          · apply measurable_sum_uncurry (F := fun ph z => F (codePhase p (.inr (.inr (.inr (.inr ph))))) z)
            · exact hv
            · exact measurable_sum_uncurry (F := fun ph z => F (codePhase p (.inr (.inr (.inr (.inr (.inr ph)))))) z) hn hd
  have hh := hm.comp (((comap_measurable (phaseCode p)).comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  exact (congrArg (fun ph => F ph w.2) (codePhase_phaseCode p w.1)).symm

@[fun_prop] lemma measurable_probe_vector (d : ℕ) :
    Measurable (fun s : LongTails.Algorithms.HeavyTailedEnergyProbe.State d => s.vector) :=
  (comap_measurable (probeEquiv d)).snd.snd.snd.fst

lemma measurable_signedSegment (p : Params) (c : Config) :
    Measurable (fun z : Aux p c × Space p => signedSegment p c z.1 z.2) := by
  unfold signedSegment
  have hm : Measurable (fun z : Aux p c × Space p => if z.1.2.1 then (1 : ℝ) else -1) :=
    Measurable.ite (measurableSet_eq_fun (measurable_fst.snd.fst) measurable_const)
      measurable_const measurable_const
  exact ((hm.mul_const c.s).div_const _).smul measurable_snd

lemma measurable_encoded_query (p : Params) (c : Config) :
    Measurable (fun w : State p × Aux p c =>
      ((query p c w.1 w.2).1, Equiv.optionEquivSumPUnit.{0, 0} (Space p) (query p c w.1 w.2).2)) := by
  have hi : Measurable (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector (d := p.d)) :=
    measurable_of_finite _
  let F := fun (ph : Phase p) (w : State p × Aux p c) =>
    let q := query p c { w.1 with phase := ph } w.2
    (q.1, Equiv.optionEquivSumPUnit.{0, 0} (Space p) q.2)
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_none]; fun_prop
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_some]; fun_prop
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_some]; fun_prop
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_some]; fun_prop
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_some]; fun_prop
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_some]
      have hseg : Measurable (fun w : Space p × (State p × Aux p c) => signedSegment p c w.2.2 w.1) := (measurable_signedSegment p c).comp
        ((measurable_snd.snd).prodMk measurable_fst)
      exact (measurable_point p |>.comp measurable_snd.fst |>.add
        (measurable_snd.snd.fst.smul hseg)).prodMk (measurable_inl.comp hseg)
    · simp only [F, query, Equiv.optionEquivSumPUnit, Equiv.coe_fn_mk, Option.elim_none]; fun_prop
  have hh := hm.comp (((measurable_phase p).comp measurable_fst).prodMk measurable_id)
  convert hh using 1
  funext w
  rcases w with ⟨state, aux⟩
  cases state
  rfl

@[fun_prop] lemma measurable_reset (p : Params) :
    Measurable (fun w : ℕ × Space p × Resume p => Phase.reset w.1 w.2.1 w.2.2) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl

@[fun_prop] lemma measurable_transport (p : Params) :
    Measurable (fun w : Space p × ℕ × Space p × Resume p =>
      Phase.transport w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp measurable_inl

@[fun_prop] lemma measurable_ncRest (p : Params) :
    Measurable (fun w : ℕ × Space p => Resume.ncRest w.1 w.2) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp measurable_inr

lemma measurable_startCycle (p : Params) (c : Config) : Measurable (startCycle p c) := by
  unfold startCycle
  apply Measurable.ite (measurableSet_lt (measurable_cycleIndex p) measurable_const)
  · apply measurable_mk <;> try fun_prop
    exact Measurable.ite (measurableSet_eq_fun (measurable_cycleIndex p) (measurable_target p))
      (measurable_point p) (measurable_selected p)
  · apply measurable_mk <;> fun_prop

lemma measurable_resume_uncurry (p : Params) {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {F : Resume p → Z → Y}
    (hs : Measurable (fun w : Unit × Z => F .startCycle w.2))
    (hd : Measurable (fun w : Unit × Z => F .detect w.2))
    (hn : Measurable (fun w : (ℕ × Space p) × Z => F (.ncRest w.1.1 w.1.2) w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : ResumeCode p × Z => F (codeResume p w.1) w.2) := by
    apply measurable_sum_uncurry (F := fun r z => F (codeResume p r) z)
    · exact hs
    · exact measurable_sum_uncurry (F := fun r z => F (codeResume p (.inr r)) z) hd hn
  have hh := hm.comp (((comap_measurable (resumeCode p)).comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  exact (congrArg (fun r => F r w.2) (codeResume_resumeCode p w.1)).symm

lemma measurable_resume (p : Params) (c : Config) :
    Measurable (fun w : Resume p × State p => resume p c w.2 w.1) := by
  apply measurable_resume_uncurry (F := fun r s => resume p c s r)
  · exact (measurable_startCycle p c).comp measurable_snd
  · apply measurable_mk <;> fun_prop
  · simp only [resume]
    apply Measurable.ite (measurableSet_eq_fun measurable_fst.fst measurable_const)
    · apply (measurable_startCycle p c).comp
      apply measurable_mk <;> fun_prop
    · apply measurable_mk <;> fun_prop

lemma measurable_completeTransport (p : Params) (c : Config) :
    Measurable (fun w : State p × Space p × Space p × Resume p =>
      completeTransport p c w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  let next := fun w : State p × Space p × Space p × Resume p =>
    { w.1 with point := w.1.point + w.2.1
               estimate := w.1.estimate + ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ • w.2.2.1
               virtualIndex := w.1.virtualIndex + 1 }
  have hn : Measurable next := by
    apply measurable_mk <;> fun_prop
  change Measurable (fun w => if (next w).virtualIndex % max 1 c.epoch = 0 then
    { next w with phase := .reset 0 0 w.2.2.2 } else resume p c (next w) w.2.2.2)
  apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
  · apply measurable_mk <;> fun_prop
  · exact (measurable_resume p c).comp (measurable_snd.snd.snd.prodMk hn)

lemma measurable_transportReply (p : Params) (c : Config) :
    Measurable (fun w : State p × Space p × ℕ × Space p × Space p × Resume p =>
      transportReply p c w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2) := by
  unfold transportReply
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
  · apply measurable_mk <;> fun_prop
  · exact (measurable_completeTransport p c).comp
      (measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((measurable_snd.snd.snd.fst.add measurable_snd.snd.snd.snd.fst).prodMk
          measurable_snd.snd.snd.snd.snd)))

lemma measurable_probe_step (d : ℕ) (shift η : ℝ) :
    Measurable (fun w : LongTails.Algorithms.HeavyTailedEnergyProbe.State d × EuclideanSpace ℝ (Fin d) =>
      LongTails.Algorithms.HeavyTailedEnergyProbe.step shift η w.1 w.2) := by
  apply measurable_comap_iff.mpr
  have hc := (comap_measurable (probeEquiv d)).comp
    (measurable_fst : Measurable (Prod.fst :
      LongTails.Algorithms.HeavyTailedEnergyProbe.State d × EuclideanSpace ℝ (Fin d) → _))
  change Measurable (fun w : LongTails.Algorithms.HeavyTailedEnergyProbe.State d × EuclideanSpace ℝ (Fin d) =>
    (w.1.index + 1, w.1.target, w.1.fallback,
      LongTails.Algorithms.HeavyTailedEnergyProbe.normalize w.1.fallback
        ((1 + η * shift) • w.1.vector - η • w.2),
      if w.1.index = w.1.target then w.1.vector else w.1.selected,
      w.1.alive && decide ((1 + η * shift) • w.1.vector - η • w.2 ≠ 0)))
  have hi := hc.fst
  have ht := hc.snd.fst
  have hf := hc.snd.snd.fst
  have hv := hc.snd.snd.snd.fst
  have hs := hc.snd.snd.snd.snd.fst
  have ha := hc.snd.snd.snd.snd.snd
  have hw := (hv.const_smul (1 + η * shift)).sub (measurable_snd.const_smul η)
  refine (hi.add_const 1).prodMk (ht.prodMk (hf.prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))))
  · exact Measurable.ite (measurableSet_eq_fun hw measurable_const) hf (hw.norm.inv.smul hw)
  · exact Measurable.ite (measurableSet_eq_fun hi ht) hv hs
  · exact (measurable_of_finite (fun z : Bool × Bool => z.1 && z.2)).comp
      (ha.prodMk (show Measurable (fun w => decide ((1 + η * shift) • w.1.vector - η • w.2 ≠ 0)) from by
        have hm : Measurable (fun w : LongTails.Algorithms.HeavyTailedEnergyProbe.State d × EuclideanSpace ℝ (Fin d) =>
            if (1 + η * shift) • w.1.vector - η • w.2 ≠ 0 then true else false) :=
          Measurable.ite (measurableSet_eq_fun hw (measurable_const (a := 0))).compl
          (measurable_const (a := true)) (measurable_const (a := false))
        convert hm using 1
        funext w
        split_ifs <;> simp_all))

@[fun_prop] lemma measurable_probe_index (d : ℕ) :
    Measurable (fun s : LongTails.Algorithms.HeavyTailedEnergyProbe.State d => s.index) :=
  (comap_measurable (probeEquiv d)).fst

@[fun_prop] lemma measurable_probe_selected (d : ℕ) :
    Measurable (fun s : LongTails.Algorithms.HeavyTailedEnergyProbe.State d => s.selected) :=
  (comap_measurable (probeEquiv d)).snd.snd.snd.snd.fst

lemma measurable_probeReply (p : Params) (c : Config) :
    Measurable (fun w : State p × ℕ × AcceptedCode p ×
        LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d × Space p =>
      probeReply p c w.1 w.2.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.2.2.1)
        w.2.2.2.1 w.2.2.2.2) := by
  have hn := (measurable_probe_step p.d c.shift c.η).comp
    (show Measurable (fun w : State p × ℕ × AcceptedCode p ×
        LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d × Space p => w.2.2.2) from by fun_prop)
  unfold probeReply
  dsimp only
  apply Measurable.ite (measurableSet_lt ((measurable_probe_index p.d).comp hn) measurable_const)
  · apply measurable_mk <;> try fun_prop
    apply measurable_comap_iff.mpr
    simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
    fun_prop
  · apply measurable_mk <;> try fun_prop
    apply measurable_comap_iff.mpr
    simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
    fun_prop

lemma measurable_rayleigh_output (n m : ℕ) :
    Measurable (LongTails.Algorithms.HeavyTailedRayleighMedian.output n m) := by
  have hg (j : ℕ) : Measurable (LongTails.Algorithms.HeavyTailedRayleighMedian.groupMean n · j) := by
    unfold LongTails.Algorithms.HeavyTailedRayleighMedian.groupMean
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun k _ => OracleTemplate.AdaptiveList.measurable_getD _ 0)
  have hm : Measurable (fun l : List ℝ => List.ofFn (fun j : Fin m =>
      LongTails.Algorithms.HeavyTailedRayleighMedian.groupMean n l j.val)) :=
    (OracleTemplate.AdaptiveList.measurable_ofFn m).comp (measurable_pi_iff.mpr (fun j => hg j.val))
  exact (OracleTemplate.AdaptiveList.measurable_getD (m / 2) 0).comp
    (OracleTemplate.AdaptiveHeavyTailSimplex.measurable_mergeSort.comp hm)

lemma measurable_reverse : Measurable (List.reverse : List ℝ → List ℝ) := by
  apply OracleTemplate.AdaptiveList.measurable_cases
  intro n
  have he : (fun x : Fin n → ℝ => (List.ofFn x).reverse) =
      fun x => List.ofFn (fun i : Fin n => x i.rev) := by
    funext x
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn, Fin.rev]
      congr 2; omega
  rw [he]
  exact (OracleTemplate.AdaptiveList.measurable_ofFn n).comp
    (measurable_pi_iff.mpr (fun _ => measurable_pi_apply _))

lemma measurable_accept (p : Params) : Measurable (fun w : AcceptedCode p × Space p =>
    Equiv.optionEquivSumPUnit.{0, 0} (Space p)
      (((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1).or (some w.2))) := by
  apply measurable_sum_uncurry (F := fun a v => Equiv.optionEquivSumPUnit.{0, 0} (Space p)
    (((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm a).or (some v)))
  · exact measurable_inl.comp measurable_fst
  · exact measurable_inl.comp measurable_snd

lemma measurable_probe_initial (p : Params) (c : Config) : Measurable
    (fun a : Aux p c => LongTails.Algorithms.HeavyTailedEnergyProbe.initialState a.2.2.1 a.2.2.2.val) := by
  apply measurable_comap_iff.mpr
  have hi : Measurable (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector (d := p.d)) :=
    measurable_of_finite _
  change Measurable (fun a : Aux p c => (0, a.2.2.2.val,
    LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector a.2.2.1,
    LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector a.2.2.1,
    LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector a.2.2.1, true))
  fun_prop

lemma measurable_finish_trials (p : Params) (c : Config) :
    Measurable (fun w : AcceptedCode p × (State p × ℕ) =>
      if w.2.2 + 1 < max 1 c.repeats then
        { w.2.1 with phase := .probeInit (w.2.2 + 1) ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1) }
      else match (Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1 with
        | none => startCycle p c { w.2.1 with cycleIndex := w.2.1.cycleIndex + 1 }
        | some v => { w.2.1 with phase := .ncInit v }) := by
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
  · apply measurable_mk <;> try fun_prop
    apply measurable_comap_iff.mpr
    simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
    fun_prop
  · apply (MeasurableEquiv.sumProdDistrib (Space p) PUnit.{1} (State p × ℕ)).symm.measurable_comp_iff.mp
    apply measurable_fun_sum
    · apply measurable_mk <;> try fun_prop
      apply measurable_comap_iff.mpr
      change Measurable (fun w : Space p × (State p × ℕ) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w.1))))))
      fun_prop
    · apply (measurable_startCycle p c).comp
      apply measurable_mk <;> fun_prop

lemma measurable_update (p : Params) (c : Config) :
    Measurable (fun w : State p × Aux p c × Space p => update p c w.1 w.2.1 w.2.2) := by
  let F := fun (ph : Phase p) (w : State p × Aux p c × Space p) =>
    update p c { w.1 with phase := ph } w.2.1 w.2.2
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, update]
      apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      · apply measurable_mk <;> fun_prop
      · apply (measurable_resume p c).comp (f := fun w : (ℕ × Space p × Resume p) × (State p × Aux p c × Space p) =>
          (w.1.2.2, { w.2.1 with
            phase := .reset w.1.1 w.1.2.1 w.1.2.2
            estimate := ((max 1 c.resetBatch : ℕ) : ℝ)⁻¹ • (w.1.2.1 + w.2.2.2) }))
        apply Measurable.prodMk (by fun_prop)
        apply measurable_mk <;> try fun_prop
    · simp only [F, update]
      apply (measurable_transportReply p c).comp (f := fun w : (Space p × ℕ × Space p × Resume p) × (State p × Aux p c × Space p) =>
        ({ w.2.1 with phase := .transport w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 },
          w.1.1, w.1.2.1, w.1.2.2.1, w.2.2.2, w.1.2.2.2))
      apply Measurable.prodMk
      · apply measurable_mk <;> try fun_prop
      · fun_prop
    · simp only [F, update]
      apply (measurable_probeReply p c).comp (f := fun w : (ℕ × AcceptedCode p) × (State p × Aux p c × Space p) =>
        ({ w.2.1 with phase := .probeInit w.1.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2) },
          w.1.1, w.1.2, LongTails.Algorithms.HeavyTailedEnergyProbe.initialState w.2.2.1.2.2.1 w.2.2.1.2.2.2.val, w.2.2.2))
      apply Measurable.prodMk
      · apply measurable_mk <;> try fun_prop
        apply measurable_comap_iff.mpr
        simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
        fun_prop
      · refine measurable_fst.fst.prodMk (measurable_fst.snd.prodMk ?_)
        exact ((measurable_probe_initial p c).comp measurable_snd.snd.fst).prodMk measurable_snd.snd.snd
    · simp only [F, update]
      apply (measurable_probeReply p c).comp (f := fun w : (ℕ × AcceptedCode p × LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) × (State p × Aux p c × Space p) =>
        ({ w.2.1 with phase := .probe w.1.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2.1) w.1.2.2 },
          w.1.1, w.1.2.1, w.1.2.2, w.2.2.2))
      apply Measurable.prodMk
      · apply measurable_mk <;> try fun_prop
        apply measurable_comap_iff.mpr
        simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
        fun_prop
      · fun_prop
    · simp only [F, update]
      let V := (ℕ × AcceptedCode p × Space p × List ℝ) × (State p × Aux p c × Space p)
      let next := fun w : V => inner ℝ w.1.2.2.1 w.2.2.2 :: w.1.2.2.2
      have hn : Measurable next := (OracleTemplate.AdaptiveList.measurable_cons 0).comp
        ((show Measurable (fun w : V => inner ℝ w.1.2.2.1 w.2.2.2) from by fun_prop).prodMk measurable_fst.snd.snd.snd)
      apply Measurable.ite (measurableSet_lt
        (OracleTemplate.AdaptiveList.measurable_length.comp hn) measurable_const)
      · apply measurable_mk <;> try fun_prop
        apply measurable_comap_iff.mpr
        simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
        exact measurable_inr.comp (measurable_inr.comp (measurable_inr.comp (measurable_inr.comp
          (measurable_inl.comp (measurable_fst.fst.prodMk
            (measurable_fst.snd.fst.prodMk (measurable_fst.snd.snd.fst.prodMk hn)))))))
      · let acode := fun w : V => if LongTails.Algorithms.HeavyTailedRayleighMedian.output
            (max 1 c.meanBatch) (max 1 c.groups) (next w).reverse ≤ -2 * c.γ then
            Equiv.optionEquivSumPUnit.{0, 0} (Space p)
              (((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2.1).or (some w.1.2.2.1))
          else w.1.2.1
        have ha : Measurable acode := Measurable.ite
          (measurableSet_le ((measurable_rayleigh_output _ _).comp (measurable_reverse.comp hn)) measurable_const)
          ((measurable_accept p).comp (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd.fst))
          measurable_fst.snd.fst
        let state := fun w : V => { w.2.1 with phase := .validate w.1.1 ((Equiv.optionEquivSumPUnit.{0, 0} (Space p)).symm w.1.2.1) w.1.2.2.1 w.1.2.2.2 }
        have hs : Measurable state := by
          apply measurable_mk <;> try fun_prop
          apply measurable_comap_iff.mpr
          simp only [Function.comp_def, phaseCode, Equiv.apply_symm_apply]
          fun_prop
        have hh := (measurable_finish_trials p c).comp (ha.prodMk (hs.prodMk measurable_fst.fst))
        convert hh using 1
        funext w
        dsimp only [acode, next, state, Function.comp_def]
        split_ifs <;> first | rfl | simp_all
    · simp only [F, update]
      apply (measurable_transportReply p c).comp (f := fun w : Space p × (State p × Aux p c × Space p) =>
        ({ w.2.1 with phase := .ncInit w.1 }, signedSegment p c w.2.2.1 w.1,
          0, 0, w.2.2.2, Resume.ncRest (max 1 c.ncSegments - 1) (signedSegment p c w.2.2.1 w.1)))
      apply Measurable.prodMk
      · apply measurable_mk <;> try fun_prop
        apply measurable_comap_iff.mpr
        change Measurable (fun w : Space p × (State p × Aux p c × Space p) =>
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w.1))))))
        fun_prop
      · have hseg : Measurable (fun w : Space p × (State p × Aux p c × Space p) =>
            signedSegment p c w.2.2.1 w.1) :=
          (measurable_signedSegment p c).comp (measurable_snd.snd.fst.prodMk measurable_fst)
        exact hseg.prodMk (measurable_const.prodMk (measurable_const.prodMk
          (measurable_snd.snd.snd.prodMk ((measurable_ncRest p).comp
            (measurable_const.prodMk hseg)))))
    · simp only [F, update]
      apply measurable_mk <;> fun_prop
  have hh := hm.comp (((measurable_phase p).comp measurable_fst).prodMk measurable_id)
  convert hh using 1
  funext w
  rcases w with ⟨state, aux, reply⟩
  cases state
  rfl

lemma measurable_sampleStep (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun w : State p × (Aux p c × p.Ω) =>
      LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H w.1 w.2) := by
  let answer := fun (a : AcceptedCode p) (w : Space p × p.Ω) =>
    match a with
    | .inl v => H w.1 w.2 v
    | .inr _ => g w.1 w.2
  have hm : Measurable (Function.uncurry answer) := by
    apply measurable_sum_uncurry (F := answer)
    · exact isBoundedBilinearMap_apply.continuous.measurable.comp
        ((hH.comp measurable_snd).prodMk measurable_fst)
    · exact hg.comp measurable_snd
  have hq := (measurable_encoded_query p c).comp
    (show Measurable (fun w : State p × (Aux p c × p.Ω) => (w.1, w.2.1)) from by fun_prop)
  have ha := hm.comp (hq.snd.prodMk (hq.fst.prodMk measurable_snd.snd))
  have hu := (measurable_update p c).comp (measurable_fst.prodMk (measurable_snd.fst.prodMk ha))
  convert hu using 1
  funext w
  dsimp only [LongTails.Proofs.HeavyTailedSospExecution.sampleStep, Function.comp_def,
    Function.uncurry, answer]
  cases (query p c w.1 w.2.1).2 <;> rfl

lemma measurable_initial (p : Params) : Measurable (initial p) := by
  apply measurable_mk <;> fun_prop

lemma measurable_trajectory_output (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H)) (K : ℕ) :
    Measurable (fun w : ℕ × (ℕ → Aux p c × p.Ω) =>
      (LongTails.Proofs.HeavyTailedProductProcess.trajectory
        (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) K (initial p w.1) w.2).selected) := by
  exact (measurable_selected p).comp
    ((LongTails.Proofs.HeavyTailedProductProcess.trajectory_measurable
      (measurable_sampleStep p c g H hg hH) K).comp
        (((measurable_initial p).comp measurable_fst).prodMk measurable_snd))

lemma measurable_execute_sosp (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, x, v) ω => match v with | none => g x ω | some u => H x ω u }
    Measurable (fun w : (Fin (max 1 c.cycles) × (ℕ → Aux p c)) × (ℕ → p.Ω) =>
      OracleTemplate.execute O (algorithm p c) (fun _ => K) w.1 w.2) := by
  intro O
  have hm := (measurable_trajectory_output p c g H hg hH K).comp
    (show Measurable (fun w : (Fin (max 1 c.cycles) × (ℕ → Aux p c)) × (ℕ → p.Ω) =>
      (w.1.1.val, fun k => (w.1.2 k, w.2 k))) from by fun_prop)
  convert hm using 1
  funext w
  exact LongTails.Proofs.HeavyTailedSospExecution.execute_sosp p c g H P w.1 w.2 K

end LongTails.Proofs.HeavyTailedSospMeasurable
