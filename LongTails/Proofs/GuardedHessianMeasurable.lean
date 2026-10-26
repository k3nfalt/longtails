import LongTails.Algorithms.GuardedHessianTransport
import LongTails.Proofs.HeavyTailedSospMeasurable
import LongTails.Proofs.MultiplicativeRobustMedoid

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport

namespace LongTails.Proofs.GuardedHessianMeasurable

abbrev PhaseCode (p : Params) (c : Config) :=
  (ℕ × Space p) ⊕ Unit ⊕
    (Fin (c.groups + 1) × ℕ × Space p × (Fin (c.groups + 1) → Space p)) ⊕ Unit

def phaseCode (p : Params) (c : Config) : Phase p c → PhaseCode p c
  | .reset i v => .inl (i, v)
  | .transport => .inr (.inl ())
  | .guard j i v values => .inr (.inr (.inl (j, i, v, values)))
  | .done => .inr (.inr (.inr ()))

def codePhase (p : Params) (c : Config) : PhaseCode p c → Phase p c
  | .inl (i, v) => .reset i v
  | .inr (.inl _) => .transport
  | .inr (.inr (.inl (j, i, v, values))) => .guard j i v values
  | .inr (.inr (.inr _)) => .done

instance (p : Params) (c : Config) : MeasurableSpace (Phase p c) :=
  MeasurableSpace.comap (phaseCode p c) inferInstance

abbrev StateCode (p : Params) (c : Config) :=
  Space p × Space p × ℕ × Fin (c.steps + 1) × Space p × Bool × Phase p c

def stateEquiv (p : Params) (c : Config) : State p c ≃ StateCode p c where
  toFun s := (s.point, s.estimate, s.index, s.target, s.selected, s.alive, s.phase)
  invFun w := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1,
    w.2.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv w := by rcases w with ⟨a,b,c,d,e,f,g⟩; rfl

instance (p : Params) (c : Config) : MeasurableSpace (State p c) :=
  MeasurableSpace.comap (stateEquiv p c) inferInstance

@[fun_prop] lemma measurable_point (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.point) := (comap_measurable (stateEquiv p c)).fst
@[fun_prop] lemma measurable_estimate (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.estimate) := (comap_measurable (stateEquiv p c)).snd.fst
@[fun_prop] lemma measurable_index (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.index) := (comap_measurable (stateEquiv p c)).snd.snd.fst
@[fun_prop] lemma measurable_target (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.target) := (comap_measurable (stateEquiv p c)).snd.snd.snd.fst
@[fun_prop] lemma measurable_selected (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.selected) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.fst
@[fun_prop] lemma measurable_alive (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.alive) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.snd.fst
@[fun_prop] lemma measurable_phase (p : Params) (c : Config) :
    Measurable (fun s : State p c => s.phase) :=
  (comap_measurable (stateEquiv p c)).snd.snd.snd.snd.snd.snd

@[fun_prop] lemma measurable_mk (p : Params) (c : Config) {Z : Type*} [MeasurableSpace Z]
    {x e o : Z → Space p} {i : Z → ℕ} {t : Z → Fin (c.steps + 1)}
    {a : Z → Bool} {ph : Z → Phase p c}
    (hx : Measurable x) (he : Measurable e) (hi : Measurable i) (ht : Measurable t)
    (ho : Measurable o) (ha : Measurable a) (hph : Measurable ph) :
    Measurable (fun z => State.mk (x z) (e z) (i z) (t z) (o z) (a z) (ph z)) := by
  apply measurable_comap_iff.mpr
  exact hx.prodMk (he.prodMk (hi.prodMk (ht.prodMk (ho.prodMk (ha.prodMk hph)))))

@[fun_prop] lemma measurable_reset (p : Params) (c : Config) :
    Measurable (fun w : ℕ × Space p => (Phase.reset w.1 w.2 : Phase p c)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl

@[fun_prop] lemma measurable_guard (p : Params) (c : Config) :
    Measurable (fun w : Fin (c.groups + 1) × ℕ × Space p × (Fin (c.groups + 1) → Space p) =>
      (Phase.guard w.1 w.2.1 w.2.2.1 w.2.2.2 : Phase p c)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inr.comp measurable_inl)

lemma measurable_beginStep (p : Params) (c : Config) : Measurable (beginStep p c) := by
  unfold beginStep
  apply measurable_mk <;> try fun_prop
  exact Measurable.ite (measurableSet_eq_fun (measurable_index p c)
    ((measurable_of_finite Fin.val).comp (measurable_target p c)))
    (measurable_point p c) (measurable_selected p c)

lemma measurable_nextStep (p : Params) (c : Config) : Measurable (nextStep p c) := by
  unfold nextStep
  apply Measurable.ite (measurableSet_lt (measurable_index p c) measurable_const)
  · dsimp only
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    · apply measurable_mk <;> fun_prop
    · exact (measurable_beginStep p c).comp (by apply measurable_mk <;> fun_prop)
  · apply measurable_mk <;> fun_prop

lemma measurable_phase_uncurry (p : Params) (c : Config) {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y] {F : Phase p c → Z → Y}
    (hr : Measurable (fun w : (ℕ × Space p) × Z => F (.reset w.1.1 w.1.2) w.2))
    (ht : Measurable (fun w : Unit × Z => F .transport w.2))
    (hg : Measurable (fun w :
      (Fin (c.groups + 1) × ℕ × Space p × (Fin (c.groups + 1) → Space p)) × Z =>
      F (.guard w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2) w.2))
    (hd : Measurable (fun w : Unit × Z => F .done w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : PhaseCode p c × Z => F (codePhase p c w.1) w.2) := by
    apply HeavyTailedSospMeasurable.measurable_sum_uncurry
      (F := fun ph z => F (codePhase p c ph) z)
    · exact hr
    · apply HeavyTailedSospMeasurable.measurable_sum_uncurry
        (F := fun ph z => F (codePhase p c (.inr ph)) z)
      · exact ht
      · exact HeavyTailedSospMeasurable.measurable_sum_uncurry
          (F := fun ph z => F (codePhase p c (.inr (.inr ph))) z) hg hd
  have hh := hm.comp (((comap_measurable (phaseCode p c)).comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  rcases w with ⟨ph, z⟩
  cases ph <;> rfl

lemma measurable_displacement (p : Params) (c : Config) : Measurable (displacement p c) := by
  unfold displacement
  fun_prop

lemma measurable_effective_displacement (p : Params) (c : Config) :
    Measurable (fun s : State p c => if s.alive then displacement p c s else 0) :=
  Measurable.ite (measurableSet_eq_fun (measurable_alive p c) measurable_const)
    (measurable_displacement p c) measurable_const

lemma measurable_response (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : (Space p × Space p) → p.Ω → Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun w : State p c × ℝ × p.Ω =>
      match (query p c w.1 w.2.1).2 with
      | none => g (query p c w.1 w.2.1).1 w.2.2
      | some v => H ((query p c w.1 w.2.1).1, v) w.2.2) := by
  let F := fun (ph : Phase p c) (w : State p c × ℝ × p.Ω) =>
    let q := query p c { w.1 with phase := ph } w.2.1
    match q.2 with
    | none => g q.1 w.2.2
    | some v => H (q.1, v) w.2.2
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, query]
      exact hg.comp ((measurable_point p c |>.comp measurable_snd.fst).prodMk
        measurable_snd.snd.snd)
    · simp only [F, query]
      have hv := (measurable_effective_displacement p c).comp
        (measurable_snd.fst : Measurable (fun w : Unit × (State p c × ℝ × p.Ω) => w.2.1))
      exact hH.comp (((measurable_point p c |>.comp measurable_snd.fst |>.add
        (measurable_snd.snd.fst.smul hv)).prodMk hv).prodMk measurable_snd.snd.snd)
    · simp only [F, query]
      exact hg.comp ((measurable_point p c |>.comp measurable_snd.fst).prodMk
        measurable_snd.snd.snd)
    · simp only [F, query]
      exact hg.comp ((measurable_point p c |>.comp measurable_snd.fst).prodMk
        measurable_snd.snd.snd)
  have hh := hm.comp (((measurable_phase p c).comp measurable_fst).prodMk measurable_id)
  convert hh using 1
  funext w
  rcases w with ⟨state, a, ω⟩
  cases state
  rfl

lemma measurable_guard_acceptance (p : Params) (c : Config) :
    Measurable (fun w : State p c × (Fin (c.groups + 1) → Space p) =>
      w.1.alive && decide
        (‖OracleTemplate.MultiplicativeRobustEstimator.medoid w.2‖ ≤ c.threshold)) := by
  classical
  have hn : Measurable (fun w : State p c × (Fin (c.groups + 1) → Space p) =>
      OracleTemplate.MultiplicativeRobustEstimator.medoid w.2) := (OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid
    (E := Space p) (n := c.groups)).comp measurable_snd
  have hd : Measurable (fun w : State p c × (Fin (c.groups + 1) → Space p) =>
      decide (‖OracleTemplate.MultiplicativeRobustEstimator.medoid w.2‖ ≤ c.threshold)) := by
    have hh : Measurable (fun w : State p c × (Fin (c.groups + 1) → Space p) =>
        if ‖OracleTemplate.MultiplicativeRobustEstimator.medoid w.2‖ ≤ c.threshold
          then true else false) := Measurable.ite (measurableSet_le hn.norm measurable_const)
      (measurable_const (a := true)) (measurable_const (a := false))
    convert hh using 1
    funext w
    by_cases h : ‖OracleTemplate.MultiplicativeRobustEstimator.medoid w.2‖ ≤ c.threshold <;>
      simp [h]
  exact (measurable_of_finite (fun z : Bool × Bool => z.1 && z.2)).comp
    (((measurable_alive p c).comp measurable_fst).prodMk hd)

lemma measurable_guard_finish (p : Params) (c : Config) :
    Measurable (fun w : State p c × (Fin (c.groups + 1) → Space p) =>
      let accepted := w.1.alive && decide
        (‖OracleTemplate.MultiplicativeRobustEstimator.medoid w.2‖ ≤ c.threshold)
      nextStep p c { w.1 with
        alive := accepted
        point := if accepted then w.1.point else p.x0
        selected := if accepted then w.1.selected else p.x0 }) := by
  have ha := measurable_guard_acceptance p c
  have hset := measurableSet_eq_fun ha (measurable_const (a := true))
  apply (measurable_nextStep p c).comp
  apply measurable_mk
  · exact Measurable.ite hset ((measurable_point p c).comp measurable_fst) measurable_const
  · fun_prop
  · fun_prop
  · fun_prop
  · exact Measurable.ite hset ((measurable_selected p c).comp measurable_fst) measurable_const
  · exact ha
  · fun_prop

set_option maxHeartbeats 800000 in
lemma measurable_fixed_guard_reply (p : Params) (c : Config)
    (j : Fin (c.groups + 1)) (i : ℕ) :
    Measurable (fun w : State p c × Space p × (Fin (c.groups + 1) → Space p) × Space p =>
      update p c { w.1 with phase := .guard j i w.2.1 w.2.2.1 } 0 w.2.2.2) := by
  classical
  by_cases hi : i < c.guardBatch
  · simp only [update, ite_eq_left hi]
    apply measurable_mk <;> fun_prop
  · by_cases hj : j.val + 1 < c.groups + 1
    · simp only [update, ite_eq_right hi, dite_eq_left hj]
      have hv : Measurable (fun w : State p c × Space p ×
          (Fin (c.groups + 1) → Space p) × Space p =>
          Function.update w.2.2.1 j (((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) :=
        (measurable_update' (a := j)).comp (f := fun w : State p c × Space p ×
          (Fin (c.groups + 1) → Space p) × Space p =>
            (w.2.2.1, ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) (by fun_prop)
      apply measurable_mk <;> try fun_prop
    · simp only [update, ite_eq_right hi, dite_eq_right hj]
      have hv : Measurable (fun w : State p c × Space p ×
          (Fin (c.groups + 1) → Space p) × Space p =>
          Function.update w.2.2.1 j (((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) :=
        (measurable_update' (a := j)).comp (f := fun w : State p c × Space p ×
          (Fin (c.groups + 1) → Space p) × Space p =>
            (w.2.2.1, ((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))) (by fun_prop)
      apply (measurable_guard_finish p c).comp (f := fun w : State p c × Space p ×
        (Fin (c.groups + 1) → Space p) × Space p =>
        ({ w.1 with phase := .guard j i w.2.1 w.2.2.1 },
          Function.update w.2.2.1 j (((c.guardBatch + 1 : ℕ) : ℝ)⁻¹ • (w.2.1 + w.2.2.2))))
      apply Measurable.prodMk
      · apply measurable_mk <;> fun_prop
      · exact hv

lemma measurable_update (p : Params) (c : Config) :
    Measurable (fun w : State p c × Space p => update p c w.1 0 w.2) := by
  let F := fun (ph : Phase p c) (w : State p c × Space p) =>
    update p c { w.1 with phase := ph } 0 w.2
  have hm : Measurable (Function.uncurry F) := by
    apply measurable_phase_uncurry
    · simp only [F, update]
      apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      · apply measurable_mk <;> fun_prop
      · apply (measurable_beginStep p c).comp
        apply measurable_mk <;> try fun_prop
        · exact Measurable.ite
            (measurableSet_eq_fun ((measurable_alive p c).comp measurable_snd.fst) measurable_const)
            (by fun_prop) measurable_const
    · simp only [F, update]
      have ha := measurableSet_eq_fun
        ((measurable_alive p c).comp
          (measurable_snd.fst : Measurable (fun w : Unit × (State p c × Space p) => w.2.1)))
        (measurable_const (a := true))
      apply measurable_mk
      · change Measurable (fun w : Unit × (State p c × Space p) =>
          if w.2.1.alive then w.2.1.point + displacement p c w.2.1 else p.x0)
        exact Measurable.ite ha
          (((measurable_point p c).comp measurable_snd.fst).add
            ((measurable_displacement p c).comp measurable_snd.fst)) measurable_const
      · exact Measurable.ite ha (by fun_prop) measurable_const
      · fun_prop
      · fun_prop
      · fun_prop
      · fun_prop
      · exact measurable_const
    · have hg : Measurable (fun w : Fin (c.groups + 1) × ℕ ×
          (State p c × Space p × (Fin (c.groups + 1) → Space p) × Space p) =>
          update p c { w.2.2.1 with phase := .guard w.1 w.2.1 w.2.2.2.1 w.2.2.2.2.1 }
            0 w.2.2.2.2.2) :=
        measurable_from_prod_countable_right (fun j =>
          measurable_from_prod_countable_right (fun i => measurable_fixed_guard_reply p c j i))
      exact hg.comp (f := fun w :
        (Fin (c.groups + 1) × ℕ × Space p × (Fin (c.groups + 1) → Space p)) ×
          (State p c × Space p) =>
        (w.1.1, w.1.2.1, w.2.1, w.1.2.2.1, w.1.2.2.2, w.2.2)) (by fun_prop)
    · simp only [F, update]
      apply measurable_mk <;> fun_prop
  have hh := hm.comp (((measurable_phase p c).comp measurable_fst).prodMk measurable_id)
  convert hh using 1
  funext w
  rcases w with ⟨state, reply⟩
  cases state
  rfl

lemma measurable_step (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : (Space p × Space p) → p.Ω → Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun w : State p c × ℝ × p.Ω =>
      update p c w.1 w.2.1
        (match (query p c w.1 w.2.1).2 with
        | none => g (query p c w.1 w.2.1).1 w.2.2
        | some v => H ((query p c w.1 w.2.1).1, v) w.2.2)) := by
  exact (measurable_update p c).comp
    (measurable_fst.prodMk (measurable_response p c g H hg hH))

lemma measurable_trial_path (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : (Space p × Space p) → p.Ω → Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H)) (n : ℕ) :
    Measurable (fun w : Fin (c.steps + 1) × (ℕ → ℝ × p.Ω) =>
      HeavyTailedProductProcess.trajectory
        (fun s (z : ℝ × p.Ω) => update p c s z.1
          (match (query p c s z.1).2 with
          | none => g (query p c s z.1).1 z.2
          | some v => H ((query p c s z.1).1, v) z.2))
        n (⟨p.x0, 0, 0, w.1, p.x0, true, .reset 0 0⟩ : State p c) w.2) := by
  exact (HeavyTailedProductProcess.trajectory_measurable (measurable_step p c g H hg hH) n).comp
    (((measurable_of_finite (fun target : Fin (c.steps + 1) =>
      (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c))).comp measurable_fst).prodMk
      measurable_snd)

lemma measurable_output (p : Params) (c : Config) :
    Measurable (fun s : State p c => if s.alive then s.selected else p.x0) :=
  Measurable.ite (measurableSet_eq_fun (measurable_alive p c) measurable_const)
    (measurable_selected p c) measurable_const

end LongTails.Proofs.GuardedHessianMeasurable
