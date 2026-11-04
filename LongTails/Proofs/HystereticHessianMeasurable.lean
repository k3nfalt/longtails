import LongTails.Proofs.HystereticHessianAnchorBlocks
import LongTails.Proofs.GuardedHessianMeasurable

open MeasureTheory

namespace LongTails.Proofs.HystereticHessianMeasurable

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianMoments HystereticHessianBlocks HystereticHessianAnchorBlocks HystereticHessianPhases

def optionCode {E : Type*} : Option E → E ⊕ Unit
  | some x => .inl x
  | none => .inr ()

scoped instance optionMeasurableSpace {E : Type*} [MeasurableSpace E] : MeasurableSpace (Option E) :=
  MeasurableSpace.comap optionCode inferInstance

@[fun_prop] lemma measurable_some {E : Type*} [MeasurableSpace E] :
    Measurable (some : E → Option E) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl

abbrev GradientCode (p : Params) (c : Config) :=
  Bool × Fin (c.groups + 1) × ℕ × Space p × (Fin (c.groups + 1) → Space p)

abbrev PhaseCode (p : Params) (c : Config) := GradientCode p c ⊕ (ℕ × Space p) ⊕ Unit

def phaseCode (p : Params) (c : Config) : Phase p c → PhaseCode p c
  | .gradient refresh j i sum values => .inl (refresh, j, i, sum, values)
  | .transport i sum => .inr (.inl (i, sum))
  | .padding => .inr (.inr ())

def codePhase (p : Params) (c : Config) : PhaseCode p c → Phase p c
  | .inl (refresh, j, i, sum, values) => .gradient refresh j i sum values
  | .inr (.inl (i, sum)) => .transport i sum
  | .inr (.inr _) => .padding

instance (p : Params) (c : Config) : MeasurableSpace (Phase p c) :=
  MeasurableSpace.comap (phaseCode p c) inferInstance

abbrev StateCode (p : Params) (c : Config) :=
  Space p × Space p × Space p × ℕ × ℕ × Bool × Bool × Bool × Phase p c

def stateEquiv (p : Params) (c : Config) : State p c ≃ StateCode p c where
  toFun s := (s.point, s.estimate, s.move, s.inner, s.slot, s.fine, s.active, s.success, s.phase)
  invFun w := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1,
    w.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by rcases w with ⟨a,b,c,d,e,f,g,h,i⟩; rfl

instance (p : Params) (c : Config) : MeasurableSpace (State p c) :=
  MeasurableSpace.comap (stateEquiv p c) inferInstance

@[fun_prop] lemma measurable_point (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.point) :=
  (comap_measurable (stateEquiv p c)).fst

@[fun_prop] lemma measurable_estimate (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.estimate) :=
  (comap_measurable (stateEquiv p c)).snd.fst

@[fun_prop] lemma measurable_move (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.move) :=
  (comap_measurable (stateEquiv p c)).snd.snd.fst

@[fun_prop] lemma measurable_inner (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.inner) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.fst

@[fun_prop] lemma measurable_slot (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.slot) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_fine (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.fine) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_active (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.active) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_success (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.success) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_phase (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.phase) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.snd.snd.snd.snd

@[fun_prop] lemma measurable_mk (p : Params) (c : Config) {Z : Type*} [MeasurableSpace Z]
    {x e v : Z → Space p} {i t : Z → ℕ} {f a b : Z → Bool} {ph : Z → Phase p c}
    (hx : Measurable x) (he : Measurable e) (hv : Measurable v) (hi : Measurable i)
    (ht : Measurable t) (hf : Measurable f) (ha : Measurable a) (hb : Measurable b)
    (hph : Measurable ph) :
    Measurable (fun z => State.mk (x z) (e z) (v z) (i z) (t z) (f z) (a z) (b z) (ph z)) := by
  apply measurable_comap_iff.mpr
  exact hx.prodMk (he.prodMk (hv.prodMk (hi.prodMk (ht.prodMk
    (hf.prodMk (ha.prodMk (hb.prodMk hph)))))))

@[fun_prop] lemma measurable_gradient (p : Params) (c : Config) :
    Measurable (fun w : GradientCode p c =>
      (Phase.gradient w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 : Phase p c)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl

@[fun_prop] lemma measurable_transport (p : Params) (c : Config) :
    Measurable (fun w : ℕ × Space p => (Phase.transport w.1 w.2 : Phase p c)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp measurable_inl

lemma measurable_phase_uncurry (p : Params) (c : Config) {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y] {F : Phase p c → Z → Y}
    (hg : Measurable (fun w : GradientCode p c × Z =>
      F (.gradient w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2.1 w.1.2.2.2.2) w.2))
    (ht : Measurable (fun w : (ℕ × Space p) × Z => F (.transport w.1.1 w.1.2) w.2))
    (hp : Measurable (fun w : Unit × Z => F .padding w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : PhaseCode p c × Z => F (codePhase p c w.1) w.2) := by
    apply HeavyTailedSospMeasurable.measurable_sum_uncurry
      (F := fun ph z => F (codePhase p c ph) z)
    · exact hg
    · exact HeavyTailedSospMeasurable.measurable_sum_uncurry
        (F := fun ph z => F (codePhase p c (.inr ph)) z) ht hp
  have hh := hm.comp (((comap_measurable (phaseCode p c)).comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  rcases w with ⟨ph, z⟩
  cases ph <;> rfl

def anchorEquiv (p : Params) (c : Config) : AnchoredState p c ≃ State p c × Space p where
  toFun s := (s.value, s.anchor)
  invFun w := ⟨w.1, w.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by cases w; rfl

instance (p : Params) (c : Config) : MeasurableSpace (AnchoredState p c) :=
  MeasurableSpace.comap (anchorEquiv p c) inferInstance

@[fun_prop] lemma measurable_value (p : Params) (c : Config) :
    Measurable (fun s : AnchoredState p c => s.value) := (comap_measurable (anchorEquiv p c)).fst

@[fun_prop] lemma measurable_anchor (p : Params) (c : Config) :
    Measurable (fun s : AnchoredState p c => s.anchor) := (comap_measurable (anchorEquiv p c)).snd

@[fun_prop] lemma measurable_anchor_mk (p : Params) (c : Config) {Z : Type*} [MeasurableSpace Z]
    {s : Z → State p c} {a : Z → Space p} (hs : Measurable s) (ha : Measurable a) :
    Measurable (fun z => (⟨s z, a z⟩ : AnchoredState p c)) := by
  apply measurable_comap_iff.mpr
  exact hs.prodMk ha

lemma measurable_potential (p : Params) (c : Config) (g : Space p → Space p)
    (hg : Measurable g) : Measurable (potential p c g) := by
  unfold potential
  apply Measurable.ite
  · apply measurableSet_eq_fun _ measurable_const
    exact (measurable_of_finite (fun z : Bool × Bool => z.1 || z.2)).comp
      (((measurable_active p c).comp (measurable_value p c)).prodMk
        ((measurable_success p c).comp (measurable_value p c)))
  · exact ((hg.comp (measurable_anchor p c)).norm).pow_const 2
  · exact measurable_const

@[fun_prop] lemma measurable_fineDisplacement (p : Params) (c : Config) :
    Measurable (fineDisplacement p c) := by
  unfold fineDisplacement
  fun_prop

@[fun_prop] lemma measurable_coarseDisplacement (p : Params) (c : Config) :
    Measurable (coarseDisplacement p c) := by
  unfold coarseDisplacement
  fun_prop

@[fun_prop] lemma measurable_beginFineStep (p : Params) (c : Config) :
    Measurable (beginFineStep p c) := by
  unfold beginFineStep
  apply Measurable.ite (measurableSet_le (measurable_estimate p c |>.norm) measurable_const)
  · apply measurable_mk <;> fun_prop
  · apply measurable_mk <;> fun_prop

@[fun_prop] lemma measurable_finishPilot (p : Params) (c : Config) :
    Measurable (Function.uncurry (finishPilot p c)) := by
  simp only [Function.uncurry_def, finishPilot]
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd.norm)
  · apply measurable_mk <;> fun_prop
  · apply Measurable.ite (measurableSet_eq_fun
      ((measurable_fine p c).comp measurable_fst) measurable_const)
    · apply Measurable.ite (measurableSet_le measurable_const measurable_snd.norm)
      · apply measurable_mk <;> fun_prop
      · apply Measurable.ite (measurableSet_eq_fun
          ((measurable_inner p c).comp measurable_fst) measurable_const)
        · apply measurable_mk <;> fun_prop
        · exact (measurable_beginFineStep p c).comp measurable_fst
    · apply Measurable.ite (measurableSet_le measurable_snd.norm measurable_const)
      · apply measurable_mk <;> fun_prop
      · apply measurable_mk <;> fun_prop

lemma measurable_phaseCalls (p : Params) (c : Config) : Measurable (phaseCalls p c) := by
  let F := fun (ph : Phase p c) (s : State p c) => phaseCalls p c { s with phase := ph }
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, phaseCalls, batchRemaining]
      have hb : Measurable (fun w : GradientCode p c × State p c =>
          if w.1.1 then c.resetBatch else c.pilotBatch) :=
        Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
          measurable_const measurable_const
      apply Measurable.ite (measurableSet_eq_fun
        ((measurable_active p c).comp measurable_snd) measurable_const) <;> fun_prop
    · simp only [F, phaseCalls]
      apply Measurable.ite (measurableSet_eq_fun
        ((measurable_active p c).comp measurable_snd) measurable_const) <;> fun_prop
    · simp only [F, phaseCalls, ite_self]
      fun_prop
  have hh := hm.comp ((measurable_phase p c).prodMk measurable_id)
  convert hh using 1
  funext s
  cases s
  rfl

lemma measurable_anchoredTimedCost (p : Params) (c : Config) :
    Measurable (anchoredTimedCost p c) := by
  unfold anchoredTimedCost timedCost forgetAnchor
  apply Measurable.ite (measurableSet_lt measurable_snd measurable_const)
  · exact (measurable_phaseCalls p c).comp ((measurable_value p c).comp measurable_fst)
  · exact measurable_const

set_option maxHeartbeats 300000 in
lemma measurable_fixed_gradient_reply (p : Params) (c : Config)
    (refresh : Bool) (j : Fin (c.groups + 1)) (i : ℕ) :
    Measurable (fun w : State p c × Space p × (Fin (c.groups + 1) → Space p) × Space p =>
      rawUpdate p c { w.1 with phase := .gradient refresh j i w.2.1 w.2.2.1 } w.2.2.2) := by
  classical
  let b := if refresh then c.resetBatch else c.pilotBatch
  have hv : Measurable (fun w : State p c × Space p × (Fin (c.groups + 1) → Space p) × Space p =>
      Function.update w.2.2.1 j (((b + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) :=
    (measurable_update' (a := j)).comp (f := fun w : State p c × Space p ×
      (Fin (c.groups + 1) → Space p) × Space p =>
        (w.2.2.1, ((b + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) (by fun_prop)
  have hm := (OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid
    (E := Space p) (n := c.groups)).comp hv
  simp only [rawUpdate]
  apply Measurable.ite (measurableSet_eq_fun
    ((measurable_active p c).comp measurable_fst) measurable_const)
  · by_cases hi : i < b
    · simp only [show i < (if refresh then c.resetBatch else c.pilotBatch) from hi, ite_true]
      apply measurable_mk <;> fun_prop
    · simp only [show ¬i < (if refresh then c.resetBatch else c.pilotBatch) from hi, ite_false]
      by_cases hj : j.val + 1 < c.groups + 1
      · simp only [hj, dite_true]
        apply measurable_mk <;> fun_prop
      · simp only [hj, dite_false]
        cases refresh with
        | true =>
          simp only [b, ite_true] at hm
          simp only [ite_true]
          have he : Measurable (fun w : State p c × Space p ×
              (Fin (c.groups + 1) → Space p) × Space p =>
              { w.1 with
                phase := .gradient true j i w.2.1 w.2.2.1
                estimate := OracleTemplate.MultiplicativeRobustEstimator.medoid
                  (Function.update w.2.2.1 j
                    (((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) }) := by
            apply measurable_mk
            · fun_prop
            · exact hm
            all_goals fun_prop
          exact (measurable_beginFineStep p c).comp he
        | false =>
          simp only [b, Bool.false_eq_true, ite_false] at hm
          simp only [Bool.false_eq_true, ite_false]
          have hs : Measurable (fun w : State p c × Space p ×
              (Fin (c.groups + 1) → Space p) × Space p =>
              { w.1 with phase := .gradient false j i w.2.1 w.2.2.1 }) := by
            apply measurable_mk <;> fun_prop
          convert (measurable_finishPilot p c).comp (hs.prodMk hm) using 1
          funext w
          rfl

  · apply measurable_mk <;> fun_prop

lemma measurable_query (p : Params) (c : Config) : Measurable (Function.uncurry (query p c)) := by
  let F := fun (ph : Phase p c) (w : State p c × ℝ) => query p c { w.1 with phase := ph } w.2
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, query]
      apply Measurable.ite (measurableSet_eq_fun
        ((measurable_active p c).comp measurable_snd.fst) measurable_const) <;> fun_prop
    · simp only [F, query]
      apply Measurable.ite (measurableSet_eq_fun
        ((measurable_active p c).comp measurable_snd.fst) measurable_const) <;> fun_prop
    · simp only [F, query, ite_self]
      exact measurable_const
  have hh := hm.comp (((measurable_phase p c).comp measurable_fst).prodMk measurable_id)
  convert hh using 1
  funext w
  cases w.1
  rfl

set_option maxHeartbeats 800000 in
lemma measurable_rawUpdate (p : Params) (c : Config) :
    Measurable (Function.uncurry (rawUpdate p c)) := by
  let F := fun (ph : Phase p c) (w : State p c × Space p) => rawUpdate p c { w.1 with phase := ph } w.2
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · have hg : Measurable (fun w : Bool × Fin (c.groups + 1) × ℕ ×
          (State p c × Space p × (Fin (c.groups + 1) → Space p) × Space p) =>
          rawUpdate p c { w.2.2.2.1 with
            phase := .gradient w.1 w.2.1 w.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2.1 } w.2.2.2.2.2.2) :=
        measurable_from_prod_countable_right (fun refresh =>
          measurable_from_prod_countable_right (fun j =>
            measurable_from_prod_countable_right (fun i => measurable_fixed_gradient_reply p c refresh j i)))
      exact hg.comp (f := fun w : GradientCode p c × (State p c × Space p) =>
        (w.1.1, w.1.2.1, w.1.2.2.1, w.2.1, w.1.2.2.2.1, w.1.2.2.2.2, w.2.2)) (by fun_prop)
    · simp only [F, rawUpdate]
      have hclip : Measurable (fun w : (ℕ × Space p) × (State p c × Space p) =>
          OracleTemplate.clip c.clipThreshold w.2.2) :=
        (OracleTemplate.measurable_clip c.clipThreshold).comp measurable_snd.snd
      apply Measurable.ite (measurableSet_eq_fun
        ((measurable_active p c).comp measurable_snd.fst) measurable_const)
      · apply Measurable.ite (measurableSet_lt measurable_fst.fst measurable_const)
        · apply measurable_mk <;> fun_prop
        · apply measurable_mk <;> try fun_prop
          apply Measurable.ite (measurableSet_lt
            ((measurable_inner p c).comp measurable_snd.fst) measurable_const) <;> fun_prop
      · apply measurable_mk <;> fun_prop
    · simp only [F, rawUpdate, ite_self]
      apply measurable_mk <;> fun_prop
  have hh := hm.comp (((measurable_phase p c).comp measurable_fst).prodMk measurable_id)
  convert hh using 1
  funext w
  cases w.1
  rfl

lemma measurable_update (p : Params) (c : Config) :
    Measurable (fun w : State p c × Space p => update p c w.1 0 w.2) := by
  have hr := measurable_rawUpdate p c
  simp only [update]
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
  · apply measurable_mk <;> fun_prop
  · apply measurable_mk <;> fun_prop

lemma measurable_fixed_gradient_anchor (p : Params) (c : Config)
    (refresh : Bool) (j : Fin (c.groups + 1)) (i : ℕ) :
    Measurable (fun w : AnchoredState p c × Space p × (Fin (c.groups + 1) → Space p) × Space p =>
      nextAnchor p c ⟨{ w.1.value with phase := .gradient refresh j i w.2.1 w.2.2.1 }, w.1.anchor⟩ w.2.2.2) := by
  classical
  cases refresh with
  | true => simp only [nextAnchor, ite_self]; fun_prop
  | false =>
    by_cases hi : i < c.pilotBatch
    · simp only [nextAnchor, hi, ite_true, ite_self]
      fun_prop
    · by_cases hj : j.val + 1 < c.groups + 1
      · simp only [nextAnchor, hi, hj, ite_true, ite_self]
        fun_prop
      · have hv : Measurable (fun w : AnchoredState p c × Space p ×
            (Fin (c.groups + 1) → Space p) × Space p =>
            Function.update w.2.2.1 j (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) :=
          (measurable_update' (a := j)).comp (f := fun w : AnchoredState p c × Space p ×
            (Fin (c.groups + 1) → Space p) × Space p =>
              (w.2.2.1, ((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) (by fun_prop)
        have hm := (OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid
          (E := Space p) (n := c.groups)).comp hv
        simp only [nextAnchor, hi, ite_false, hj]
        apply Measurable.ite (measurableSet_eq_fun
          ((measurable_active p c).comp ((measurable_value p c).comp measurable_fst)) measurable_const)
        · apply Measurable.ite (measurableSet_lt measurable_const hm.norm) <;> fun_prop
        · fun_prop

lemma measurable_nextAnchor (p : Params) (c : Config) :
    Measurable (Function.uncurry (nextAnchor p c)) := by
  let F := fun (ph : Phase p c) (w : AnchoredState p c × Space p) =>
    nextAnchor p c ⟨{ w.1.value with phase := ph }, w.1.anchor⟩ w.2
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · have hg : Measurable (fun w : Bool × Fin (c.groups + 1) × ℕ ×
          (AnchoredState p c × Space p × (Fin (c.groups + 1) → Space p) × Space p) =>
          nextAnchor p c ⟨{ w.2.2.2.1.value with
            phase := .gradient w.1 w.2.1 w.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2.1 },
            w.2.2.2.1.anchor⟩ w.2.2.2.2.2.2) :=
        measurable_from_prod_countable_right (fun refresh =>
          measurable_from_prod_countable_right (fun j =>
            measurable_from_prod_countable_right (fun i => measurable_fixed_gradient_anchor p c refresh j i)))
      exact hg.comp (f := fun w : GradientCode p c × (AnchoredState p c × Space p) =>
        (w.1.1, w.1.2.1, w.1.2.2.1, w.2.1, w.1.2.2.2.1, w.1.2.2.2.2, w.2.2)) (by fun_prop)
    · simp only [F, nextAnchor, ite_self]
      fun_prop
    · simp only [F, nextAnchor, ite_self]
      fun_prop
  have hh := hm.comp (((measurable_phase p c).comp
    ((measurable_value p c).comp measurable_fst)).prodMk measurable_id)
  convert hh using 1
  funext w
  rcases w with ⟨⟨s, a⟩, r⟩
  cases s
  rfl

lemma measurable_anchoredTimedAdvance (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) :
    Measurable (Function.uncurry (anchoredTimedAdvance p c answer)) := by
  have hreply : Measurable (fun w : AnchoredTimedState p c × (ℝ × Ω) =>
      answer (query p c w.1.1.value w.2.1) w.2.2) :=
    ha.comp (((measurable_query p c).comp
      (((measurable_value p c).comp measurable_fst.fst).prodMk measurable_snd.fst)).prodMk
        measurable_snd.snd)
  change Measurable (fun w : AnchoredTimedState p c × (ℝ × Ω) =>
    (anchoredUpdate p c w.1.1 w.2.1 (answer (query p c w.1.1.value w.2.1) w.2.2), w.1.2 + 1))
  apply Measurable.prodMk _ (by fun_prop)
  unfold anchoredUpdate
  apply measurable_anchor_mk
  · exact (measurable_update p c).comp
      (((measurable_value p c).comp measurable_fst.fst).prodMk hreply)
  · exact (measurable_nextAnchor p c).comp (measurable_fst.fst.prodMk hreply)

lemma measurable_blockNext (p : Params) (c : Config) {Ω : Type}
    [MeasurableSpace Ω] [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M) (n : ℕ) :
    Measurable (Function.uncurry (blockNext p c answer g M hcoarse hfine n)) := by
  have hr := (finiteRun_measurable (anchoredTimedAdvance p c answer)
    (measurable_anchoredTimedAdvance p c answer ha) n).comp
    (((measurable_subtype_coe : Measurable (Subtype.val : BlockState p c g M → AnchoredTimedState p c)).comp
      measurable_fst).prodMk measurable_snd)
  have hc : Measurable (fun w : BlockState p c g M × (Fin n → ℝ × Ω) =>
      anchoredTimedCost p c w.1.val) := (measurable_anchoredTimedCost p c).comp
    ((measurable_subtype_coe : Measurable (Subtype.val : BlockState p c g M → AnchoredTimedState p c)).comp
      measurable_fst)
  apply Measurable.subtype_mk
  convert Measurable.ite (measurableSet_eq_fun (measurable_const (a := n)) hc) hr
    (measurable_subtype_coe.comp measurable_fst) using 1
  funext w
  change (blockNext p c answer g M hcoarse hfine n w.1 w.2).val =
    if n = anchoredTimedCost p c w.1.val then
      finiteRun (anchoredTimedAdvance p c answer) n w.1.val w.2 else w.1.val
  by_cases hn : n = anchoredTimedCost p c w.1.val <;> simp [blockNext, hn]


lemma measurable_oracle_answer (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (g : Space p → Ω → Space p) (h : (Space p × Space p) → Ω → Space p)
    (hg : Measurable (Function.uncurry g)) (hh : Measurable (Function.uncurry h)) :
    Measurable (fun w : (Space p × Option (Space p)) × Ω =>
      match w.1.2 with
      | none => g w.1.1 w.2
      | some v => h (w.1.1, v) w.2) := by
  let F : (Space p ⊕ Unit) → (Space p × Ω) → Space p := fun v w =>
    match v with
    | .inl v => h (w.1, v) w.2
    | .inr _ => g w.1 w.2
  have hm : Measurable (Function.uncurry F) := by
    apply HeavyTailedSospMeasurable.measurable_sum_uncurry
    · exact hh.comp (f := fun w : Space p × (Space p × Ω) => ((w.2.1, w.1), w.2.2)) (by fun_prop)
    · exact hg.comp measurable_snd
  have hc : Measurable (fun w : (Space p × Option (Space p)) × Ω =>
      (optionCode w.1.2, (w.1.1, w.2))) :=
    ((comap_measurable optionCode).comp measurable_fst.snd).prodMk
      (measurable_fst.fst.prodMk measurable_snd)
  convert hm.comp hc using 1
  funext w
  rcases w with ⟨⟨x, v⟩, ω⟩
  cases v <;> rfl

end LongTails.Proofs.HystereticHessianMeasurable
