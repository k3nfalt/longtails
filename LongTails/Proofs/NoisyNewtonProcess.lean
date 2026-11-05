import LongTails.Proofs.NoisyNewtonMeasurability
import LongTails.Proofs.NoisyNewtonExecution
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.NoisyNewtonTuning
import LongTails.Proofs.NoisyMsEnergy

namespace LongTails.Proofs.NoisyNewtonProcess

open MeasureTheory
open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonMeasurability
open LongTails.Proofs.NoisyNewtonExecution
open OracleTemplate.GeneralizedAccelerated (Iterate tentativeWeight coupling)

noncomputable def sampleReplies (p : Params) (n : ℕ) (g : Point p.d → p.Ω → Point p.d)
    (x : Point p.d) (ξ : Fin n → p.Ω) : ℕ → Point p.d :=
  fun i => if hi : i < n then g x (ξ ⟨i, hi⟩) else 0

lemma measurable_sampleReplies (p : Params) (n : ℕ) (g : Point p.d → p.Ω → Point p.d)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : Point p.d × (Fin n → p.Ω) => sampleReplies p n g w.1 w.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i < n
  · simp only [sampleReplies, dite_eq_left hi]
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply (⟨i, hi⟩ : Fin n)).comp measurable_snd))
  · simp only [sampleReplies, dite_eq_right hi]
    exact measurable_const

noncomputable def phaseCost (p : Params) : State (Point p.d) → ℕ
  | .model s _ _ => modelCost p (tentativeWeight s)
  | .hessian _ _ => 1
  | .correction t _ _ => updateSize p (actualWeight t)
  | .done _ => 0

noncomputable def phaseNext (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (state : State (Point p.d)) (ξ : Fin n → p.Ω) : State (Point p.d) :=
  match state with
  | .model s _ _ => .hessian s (modelEstimate p (tentativeWeight s) (sampleReplies p n g (coupling s) ξ))
  | .hessian s v => .correction (prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) s (H (coupling s)) v) 0 (fun _ => 0)
  | .correction t _ _ => resume p (finish (curvatureFloor p) t
      (updateEstimate p t (sampleReplies p n g (trialPoint t) ξ)))
  | .done s => .done s

lemma measurable_phaseCost (p : Params) : Measurable (phaseCost p) := by
  have hh : Measurable (fun w : State (Point p.d) × Unit => phaseCost p w.1) := by
    apply measurable_state_uncurry (F := fun s (_ : Unit) => phaseCost p s)
    all_goals dsimp only [phaseCost]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_phaseNext (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable H) (n : ℕ) :
    Measurable (Function.uncurry (phaseNext p g H n)) := by
  apply measurable_state_uncurry
  · dsimp only [phaseNext]
    apply measurable_state_hessian (by fun_prop)
    have hp : Measurable (fun w : (Iterate (Point p.d) × ℕ × (ℕ → Point p.d)) × (Fin n → p.Ω) => coupling w.1.1) := by fun_prop
    have hr := (measurable_sampleReplies p n g hg).comp (hp.prodMk measurable_snd)
    have ha : Measurable (fun w : (Iterate (Point p.d) × ℕ × (ℕ → Point p.d)) × (Fin n → p.Ω) => tentativeWeight w.1.1) := by fun_prop
    have hh := (measurable_modelEstimate p).comp (ha.prodMk hr)
    simpa only [Function.comp_def] using hh
  · dsimp only [phaseNext]
    apply measurable_state_correction _ measurable_const measurable_const
    exact measurable_prepare _ _ _ (by fun_prop) (hH.comp (by fun_prop)) (by fun_prop) _ _ _ _ _
  · dsimp only [phaseNext]
    have ht : Measurable (fun w : (Trial (Point p.d) × ℕ × (ℕ → Point p.d)) × (Fin n → p.Ω) => w.1.1) := by fun_prop
    have hr := (measurable_sampleReplies p n g hg).comp ((measurable_trialPoint.comp ht).prodMk measurable_snd)
    have hu := (measurable_updateEstimate p).comp (ht.prodMk hr)
    have hh := (measurable_resume p).comp ((measurable_finish (curvatureFloor p)).comp (ht.prodMk hu))
    simpa only [Function.comp_def] using hh
  · dsimp only [phaseNext]
    fun_prop

lemma sampleReplies_prefix (p : Params) (n : ℕ) (g : Point p.d → p.Ω → Point p.d)
    (x : Point p.d) (ξ : ℕ → p.Ω) (call : ℕ) :
    sampleReplies p n g x (fun i => ξ (call + i)) =
      OracleTemplate.AdaptiveRobustGeneralized.replyPrefix n (fun i => g x (ξ (call + i))) := by
  funext i
  simp only [sampleReplies, OracleTemplate.AdaptiveRobustGeneralized.replyPrefix]
  split_ifs <;> rfl

def PhaseStart {E : Type*} [Zero E] : State E → Prop
  | .model _ n v => n = 0 ∧ v = fun _ => 0
  | .hessian _ _ => True
  | .correction _ n v => n = 0 ∧ v = fun _ => 0
  | .done _ => True

lemma phaseNext_start (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (state : State (Point p.d)) (ξ : Fin n → p.Ω) : PhaseStart (phaseNext p g H n state ξ) := by
  cases state with
  | model s k v => trivial
  | hessian s v => exact ⟨rfl, rfl⟩
  | correction t k v =>
    dsimp only [phaseNext]
    unfold resume
    split_ifs <;> simp [PhaseStart]
  | done s => trivial

lemma rawAdvance_phase (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (state : State (Point p.d)) (hs : PhaseStart state) (call : ℕ) :
    rawAdvance p g H ξ (phaseCost p state) call state =
      phaseNext p g H (phaseCost p state) state (fun i => ξ (call + i)) := by
  cases state with
  | model s n v =>
    obtain ⟨rfl, rfl⟩ := hs
    dsimp only [phaseCost, phaseNext]
    rw [rawAdvance_model_block, sampleReplies_prefix, modelEstimate_replyPrefix]
  | hessian s v => exact rawAdvance_hessian p g H ξ s v call
  | correction t n v =>
    obtain ⟨rfl, rfl⟩ := hs
    dsimp only [phaseCost, phaseNext]
    rw [rawAdvance_correction_block, sampleReplies_prefix, updateEstimate_replyPrefix]
  | done s => rfl

open OracleTemplate.StochasticGeneralized (blockTrace blockCalls blockAdvance
  blockTrace_succ blockCalls_succ blockTrace_tail)

lemma blockTrace_start (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (state : State (Point p.d)) (hs : PhaseStart state) (n : ℕ) :
    PhaseStart (blockTrace (phaseCost p) (phaseNext p g H) state ξ n).1 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [blockTrace_succ]
    exact phaseNext_start p g H _ _ _

lemma blockTrace_eq_rawAdvance (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (state : State (Point p.d)) (hs : PhaseStart state) (n : ℕ) :
    (blockTrace (phaseCost p) (phaseNext p g H) state ξ n).1 =
      rawAdvance p g H ξ (blockCalls (phaseCost p) (phaseNext p g H) state ξ n) 0 state := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blockTrace_succ, blockCalls_succ, rawAdvance_add, Nat.zero_add, ← ih]
    change phaseNext p g H _ _ _ = _
    rw [rawAdvance_phase p g H ξ _ (blockTrace_start p g H ξ state hs n)]
    congr 1
    funext i
    exact blockTrace_tail (phaseCost p) (phaseNext p g H) state ξ n i

def baseIterate {E : Type*} : State E → Iterate E
  | .model s _ _ => s
  | .hessian s _ => s
  | .correction t _ _ => t.previous
  | .done s => s

noncomputable def stateEnergy (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (s : State (Point p.d)) : ℝ :=
  (baseIterate s).A * (f (baseIterate s).x - f u) + ‖(baseIterate s).z - u‖ ^ 2 / 2

abbrev Ghost (p : Params) := State (Point p.d) × ℝ × Bool × Bool

def stopped (p : Params) (s : Ghost p) : Prop := s.2.2.1 = true ∨ s.2.2.2 = true

noncomputable def ghostCost (p : Params) (s : Ghost p) : ℕ := by
  classical
  exact if stopped p s then 0 else phaseCost p s.1

noncomputable def ghostNext (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) : Ghost p := by
  classical
  exact if stopped p s then s else
    let next := phaseNext p g H n s.1 ξ
    match s.1 with
    | .model it _ _ =>
      let error := ‖modelEstimate p (tentativeWeight it)
        (sampleReplies p n g (coupling it) ξ) - grad (coupling it)‖
      (next, error, decide (modelRadius p (tentativeWeight it) / 2 < error), false)
    | .correction _ _ _ =>
      (next, s.2.1, false, decide (8 * p.R ^ 2 < stateEnergy p f u next))
    | _ => (next, s.2.1, false, false)

lemma ghostNext_of_stopped (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hs : stopped p s) :
    ghostNext p f u grad g H n s ξ = s := by
  simp [ghostNext, hs]

lemma ghostNext_state (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hs : ¬ stopped p s) :
    (ghostNext p f u grad g H n s ξ).1 = phaseNext p g H n s.1 ξ := by
  simp only [ghostNext, ite_eq_right hs]
  cases s.1 <;> rfl

lemma ghostNext_sticky (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hs : stopped p s) :
    stopped p (ghostNext p f u grad g H n s ξ) := by
  rw [ghostNext_of_stopped p f u grad g H n s ξ hs]
  exact hs

lemma measurable_baseIterate (p : Params) :
    Measurable (baseIterate : State (Point p.d) → Iterate (Point p.d)) := by
  have hh : Measurable (fun w : State (Point p.d) × Unit => baseIterate w.1) := by
    apply measurable_state_uncurry (F := fun s (_ : Unit) => baseIterate s)
    all_goals dsimp only [baseIterate]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_stateEnergy (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (hf : Measurable f) : Measurable (stateEnergy p f u) := by
  unfold stateEnergy
  have hb := measurable_baseIterate p
  fun_prop

lemma measurableSet_stopped (p : Params) : MeasurableSet {s : Ghost p | stopped p s} := by
  exact (measurableSet_eq_fun (by fun_prop) measurable_const).union
    (measurableSet_eq_fun (by fun_prop) measurable_const)

lemma measurable_ghostCost (p : Params) : Measurable (ghostCost p) := by
  unfold ghostCost
  exact Measurable.ite (measurableSet_stopped p) measurable_const
    ((measurable_phaseCost p).comp measurable_fst)

lemma measurable_decision {X : Type*} [MeasurableSpace X] (P : X → Prop)
    [DecidablePred P] (hP : MeasurableSet {x | P x}) : Measurable (fun x => decide (P x)) := by
  have hh : Measurable (fun x => if P x then true else false) :=
    Measurable.ite hP measurable_const measurable_const
  convert hh using 1
  funext x
  by_cases hx : P x <;> simp [hx]

lemma ghostNext_phaseStart (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hs : PhaseStart s.1) :
    PhaseStart (ghostNext p f u grad g H n s ξ).1 := by
  by_cases hstop : stopped p s
  · rw [ghostNext_of_stopped p f u grad g H n s ξ hstop]
    exact hs
  · rw [ghostNext_state p f u grad g H n s ξ hstop]
    exact phaseNext_start p g H n s.1 ξ

lemma live_flags (p : Params) (s : Ghost p) (hs : ¬ stopped p s) :
    s.2.2.1 = false ∧ s.2.2.2 = false := by
  simpa [stopped] using hs

lemma ghostNext_live_energy (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω)
    (henergy : stateEnergy p f u s.1 ≤ 8 * p.R ^ 2)
    (hlive : ¬ stopped p (ghostNext p f u grad g H n s ξ)) :
    stateEnergy p f u (ghostNext p f u grad g H n s ξ).1 ≤ 8 * p.R ^ 2 := by
  have hs : ¬ stopped p s := fun h => hlive (ghostNext_sticky p f u grad g H n s ξ h)
  rw [ghostNext_state p f u grad g H n s ξ hs]
  rcases s with ⟨state, error, flags⟩
  cases state with
  | model it k v => exact henergy
  | hessian it v => exact henergy
  | correction t k v =>
    simp only [ghostNext, ite_eq_right hs] at hlive
    simpa [stopped] using hlive
  | done it => exact henergy

lemma ghostTrace_stopped (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) (hs : stopped p s) :
    (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1 = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blockTrace_succ]
    change ghostNext p f u grad g H _ _ _ = s
    rw [ih, ghostNext_of_stopped p f u grad g H _ s _ hs]

lemma ghostTrace_live_energy (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) (hs : stateEnergy p f u s.1 ≤ 8 * p.R ^ 2)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1) :
    stateEnergy p f u (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1 ≤ 8 * p.R ^ 2 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [blockTrace_succ] at hlive ⊢
    apply ghostNext_live_energy p f u grad g H _ _ _ _ hlive
    apply ih
    intro hstop
    exact hlive (ghostNext_sticky p f u grad g H _ _ _ hstop)

lemma ghostTrace_phaseStart (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) (hs : PhaseStart s.1) :
    PhaseStart (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [blockTrace_succ]
    exact ghostNext_phaseStart p f u grad g H _ _ _ ih

lemma ghostTrace_coupling (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1) :
    (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1 =
      (blockTrace (phaseCost p) (phaseNext p g H) s.1 ξ n).1 ∧
    (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).2 =
      (blockTrace (phaseCost p) (phaseNext p g H) s.1 ξ n).2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [blockTrace_succ] at hlive
    have hprev : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1 := by
      intro hstop
      exact hlive (ghostNext_sticky p f u grad g H _ _ _ hstop)
    obtain ⟨hstate, hstream⟩ := ih hprev
    rw [blockTrace_succ, blockTrace_succ]
    dsimp only [blockAdvance]
    rw [ghostNext_state p f u grad g H _ _ _ hprev]
    have hc : ghostCost p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1 =
        phaseCost p (blockTrace (phaseCost p) (phaseNext p g H) s.1 ξ n).1 := by
      simp only [ghostCost, hprev, ↓reduceIte, hstate]
    rw [hc, hstate, hstream]
    exact ⟨rfl, rfl⟩

lemma measurable_ghostNext_live (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hf : Measurable f) (hgrad : Measurable grad)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable H) (n : ℕ) :
    Measurable (fun w : State (Point p.d) × (ℝ × (Fin n → p.Ω)) =>
      ghostNext p f u grad g H n (w.1, w.2.1, false, false) w.2.2) := by
  classical
  apply measurable_state_uncurry (X := ℝ × (Fin n → p.Ω)) (Y := Ghost p)
    (F := fun state w => ghostNext p f u grad g H n (state, w.1, false, false) w.2)
  · let X := (Iterate (Point p.d) × ℕ × (ℕ → Point p.d)) × (ℝ × (Fin n → p.Ω))
    have hi : Measurable (fun w : X => w.1.1) := by fun_prop
    have hb : Measurable (fun w : X => w.2.2) := by fun_prop
    have ha : Measurable (fun w : X => tentativeWeight w.1.1) := by fun_prop
    have hx : Measurable (fun w : X => coupling w.1.1) := by fun_prop
    have hr := (measurable_sampleReplies p n g hg).comp (hx.prodMk hb)
    have he := (measurable_modelEstimate p).comp (ha.prodMk hr)
    have herr : Measurable (fun w : X => ‖modelEstimate p (tentativeWeight w.1.1)
        (sampleReplies p n g (coupling w.1.1) w.2.2) - grad (coupling w.1.1)‖) :=
      (he.sub (hgrad.comp hx)).norm
    have hflag := measurable_decision _ (measurableSet_lt
      (((measurable_modelRadius p).comp ha).div_const 2) herr)
    have hn := (measurable_phaseNext p g H hg hH n).comp
      ((by fun_prop : Measurable (fun w : X => State.model w.1.1 w.1.2.1 w.1.2.2)).prodMk hb)
    have hfalse : Measurable (fun _ : X => false) := measurable_const
    have hh := hn.prodMk (herr.prodMk (hflag.prodMk hfalse))
    simpa only [ghostNext, stopped, Bool.false_eq_true, or_self, ite_false,
      Function.comp_def, Function.uncurry_def] using hh
  · simp only [ghostNext, stopped, Bool.false_eq_true, or_self, ite_false]
    apply Measurable.prodMk
    · exact (measurable_phaseNext p g H hg hH n).comp
        ((by fun_prop : Measurable (fun w : (Iterate (Point p.d) × Point p.d) × (ℝ × (Fin n → p.Ω)) => State.hessian w.1.1 w.1.2)).prodMk
          (by fun_prop : Measurable (fun w : (Iterate (Point p.d) × Point p.d) × (ℝ × (Fin n → p.Ω)) => w.2.2)))
    · fun_prop
  · let X := (Trial (Point p.d) × ℕ × (ℕ → Point p.d)) × (ℝ × (Fin n → p.Ω))
    have hn := (measurable_phaseNext p g H hg hH n).comp
      ((by fun_prop : Measurable (fun w : X => State.correction w.1.1 w.1.2.1 w.1.2.2)).prodMk
        (by fun_prop : Measurable (fun w : X => w.2.2)))
    have hflag := measurable_decision _ (measurableSet_lt (measurable_const (a := 8 * p.R ^ 2))
      ((measurable_stateEnergy p f u hf).comp hn))
    have hfalse : Measurable (fun _ : X => false) := measurable_const
    have hh := hn.prodMk ((by fun_prop : Measurable (fun w : X => w.2.1)).prodMk
      (hfalse.prodMk hflag))
    simp only [ghostNext, stopped, Bool.false_eq_true, or_self, ite_false]
    convert hh using 1
    funext w
    congr 1
  · simp only [ghostNext, stopped, Bool.false_eq_true, or_self, ite_false]
    apply Measurable.prodMk
    · exact (measurable_phaseNext p g H hg hH n).comp
        ((by fun_prop : Measurable (fun w : Iterate (Point p.d) × (ℝ × (Fin n → p.Ω)) => State.done w.1)).prodMk
          (by fun_prop : Measurable (fun w : Iterate (Point p.d) × (ℝ × (Fin n → p.Ω)) => w.2.2)))
    · fun_prop

lemma measurable_ghostNext (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hf : Measurable f) (hgrad : Measurable grad)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable H) (n : ℕ) :
    Measurable (Function.uncurry (ghostNext p f u grad g H n)) := by
  classical
  have hm := (measurable_ghostNext_live p f u grad g H hf hgrad hg hH n).comp
    (by fun_prop : Measurable (fun w : Ghost p × (Fin n → p.Ω) => (w.1.1, w.1.2.1, w.2)))
  have hh : Measurable (fun w : Ghost p × (Fin n → p.Ω) =>
      if stopped p w.1 then w.1 else ghostNext p f u grad g H n
        (w.1.1, w.1.2.1, false, false) w.2) :=
    Measurable.ite ((measurableSet_stopped p).preimage measurable_fst) measurable_fst hm
  convert hh using 1
  funext w
  by_cases hs : stopped p w.1
  · simp [Function.uncurry_def, ghostNext_of_stopped p f u grad g H n w.1 w.2 hs, hs]
  · simp only [Function.uncurry_def, ghostNext, stopped, Bool.false_eq_true, or_self, ite_false]
    have hf := live_flags p w.1 hs
    simp only [hf.1, hf.2, Bool.false_eq_true, or_self, ite_false]

def ModelConsistent (p : Params) (grad : Point p.d → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p) : Prop :=
  match s.1 with
  | .hessian it v => s.2.1 = ‖v - grad (coupling it)‖ ∧
      s.2.1 ≤ modelRadius p (tentativeWeight it) / 2
  | .correction t _ _ => ∃ v,
      t = prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) t.previous (H (coupling t.previous)) v ∧
      s.2.1 = ‖v - grad (coupling t.previous)‖ ∧
      s.2.1 ≤ modelRadius p (tentativeWeight t.previous) / 2
  | _ => True

lemma ghostNext_modelConsistent (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hc : ModelConsistent p grad H s)
    (hlive : ¬ stopped p (ghostNext p f u grad g H n s ξ)) :
    ModelConsistent p grad H (ghostNext p f u grad g H n s ξ) := by
  have hs : ¬ stopped p s := fun h => hlive (ghostNext_sticky p f u grad g H n s ξ h)
  simp only [ghostNext, ite_eq_right hs] at hlive ⊢
  rcases s with ⟨state, error, flags⟩
  cases state with
  | model it k v =>
    refine ⟨rfl, ?_⟩
    simpa [stopped] using hlive
  | hessian it v =>
    exact ⟨v, rfl, hc⟩
  | correction t k v =>
    dsimp only [ModelConsistent, phaseNext]
    unfold resume
    split_ifs <;> trivial
  | done it => trivial

lemma ghostTrace_modelConsistent (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) (hs : ModelConsistent p grad H s)
    (hlive : ¬ stopped p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1) :
    ModelConsistent p grad H (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [blockTrace_succ] at hlive ⊢
    apply ghostNext_modelConsistent p f u grad g H _ _ _ _ hlive
    apply ih
    intro hstop
    exact hlive (ghostNext_sticky p f u grad g H _ _ _ hstop)

open LongTails.Proofs.NoisyNewtonTuning

noncomputable def IterateBounds (p : Params) (s : Iterate (Point p.d)) : Prop :=
  0 < s.A ∧ s.A ≤ 3 * target p / 2 ∧ curvatureFloor p ≤ s.guess

noncomputable def StateBounds (p : Params) (s : State (Point p.d)) : Prop :=
  IterateBounds p (baseIterate s) ∧ match s with
  | .model it _ _ => it.A < target p / 2
  | .hessian it _ => it.A < target p / 2
  | .correction t _ _ => t.previous.A < target p / 2 ∧ t.previous.guess ≤ t.curvature
  | .done _ => True

lemma baseIterate_resume (p : Params) (s : Iterate (Point p.d)) :
    baseIterate (resume p s) = s := by
  unfold resume
  split_ifs <;> rfl

lemma resume_bounds (p : Params) (s : Iterate (Point p.d)) (hs : IterateBounds p s) :
    StateBounds p (resume p s) := by
  unfold resume
  split_ifs with h
  · exact ⟨hs, trivial⟩
  · exact ⟨hs, lt_of_not_ge h⟩

lemma phaseNext_bounds (p : Params) (hp : spec.valid p)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (n : ℕ) (s : State (Point p.d)) (ξ : Fin n → p.Ω) (hs : StateBounds p s) :
    StateBounds p (phaseNext p g H n s ξ) := by
  have hW := target_pos p hp
  have hfloor : 0 < curvatureFloor p := by unfold curvatureFloor; positivity
  cases s with
  | model it k v => exact hs
  | hessian it v =>
    refine ⟨hs.1, hs.2, ?_⟩
    exact LongTails.Proofs.NoisyNewtonModel.backtrack_curvature_lower
      _ _ _ _ _ _ _ _ (hfloor.le.trans hs.1.2.2)
  | correction t k v =>
    apply resume_bounds
    have hcap := finish_weight_cap t (curvatureFloor p) (target p) hW hs.1.1.le
      hs.2.1.le hs.1.2.2 hs.2.2 (updateEstimate p t (sampleReplies p n g (trialPoint t) ξ))
    exact ⟨hs.1.1.trans hcap.1, hcap.2, finish_floor t _ hfloor.le hs.1.2.2 _⟩
  | done it => exact hs

lemma ghostNext_bounds (p : Params) (hp : spec.valid p) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) (hs : StateBounds p s.1) :
    StateBounds p (ghostNext p f u grad g H n s ξ).1 := by
  by_cases hstop : stopped p s
  · rw [ghostNext_of_stopped p f u grad g H n s ξ hstop]
    exact hs
  · rw [ghostNext_state p f u grad g H n s ξ hstop]
    exact phaseNext_bounds p hp g H n s.1 ξ hs

lemma ghostTrace_bounds (p : Params) (hp : spec.valid p) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) (hs : StateBounds p s.1) :
    StateBounds p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [blockTrace_succ]
    exact ghostNext_bounds p hp f u grad g H _ _ _ ih

noncomputable def phaseWeight (p : Params) : State (Point p.d) → ℝ
  | .correction t _ _ => actualWeight t
  | _ => 0

noncomputable def ghostWeight (p : Params) (s : Ghost p) : ℝ := by
  classical
  exact if stopped p s then 0 else phaseWeight p s.1

lemma phaseNext_weight (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : State (Point p.d)) (ξ : Fin n → p.Ω) :
    (baseIterate (phaseNext p g H n s ξ)).A = (baseIterate s).A + phaseWeight p s := by
  cases s with
  | model it k v => simp [phaseNext, baseIterate, phaseWeight]
  | hessian it v => simp [phaseNext, baseIterate, phaseWeight, prepare]
  | correction t k v =>
    dsimp only [phaseNext]
    rw [baseIterate_resume]
    rfl
  | done it => simp [phaseNext, baseIterate, phaseWeight]

lemma ghostNext_weight (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) :
    (baseIterate (ghostNext p f u grad g H n s ξ).1).A =
      (baseIterate s.1).A + ghostWeight p s := by
  by_cases hs : stopped p s
  · simp [ghostNext_of_stopped p f u grad g H n s ξ hs, ghostWeight, hs]
  · rw [ghostNext_state p f u grad g H n s ξ hs, phaseNext_weight]
    simp [ghostWeight, hs]

lemma ghostWeight_nonneg (p : Params) (hp : spec.valid p) (s : Ghost p)
    (hs : StateBounds p s.1) : 0 ≤ ghostWeight p s := by
  have hfloor : 0 < curvatureFloor p := by
    unfold curvatureFloor
    exact div_pos (by norm_num) (target_pos p hp)
  unfold ghostWeight
  split_ifs
  · exact le_rfl
  · cases hstate : s.1 with
    | model it k v => exact le_rfl
    | hessian it v => exact le_rfl
    | correction t k v =>
      rw [hstate] at hs
      exact (actualWeight_bounds t (hfloor.trans_le hs.1.2.2) hs.2.2).1.le
    | done it => exact le_rfl

lemma ghostWeight_sum (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    ∑ i ∈ Finset.range n, ghostWeight p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ i).1 =
      (baseIterate (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1).A -
        (baseIterate s.1).A := by
  induction n with
  | zero => simp [OracleTemplate.StochasticGeneralized.blockTrace_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, blockTrace_succ]
    dsimp only [blockAdvance]
    rw [ghostNext_weight]
    ring

lemma ghostWeight_sum_bound (p : Params) (hp : spec.valid p) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ) (hs : StateBounds p s.1) :
    ∑ i ∈ Finset.range n, ghostWeight p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ i).1 ≤
      3 * target p / 2 := by
  rw [ghostWeight_sum]
  exact (sub_le_self _ hs.1.1.le).trans (ghostTrace_bounds p hp f u grad g H s ξ n hs).1.2.1

def CorrectionReady (p : Params) (grad : Point p.d → Point p.d) (u : Point p.d)
    (t : Trial (Point p.d)) : Prop :=
  0 < actualWeight t ∧ ‖t.previous.z - actualWeight t • grad (trialPoint t) - u‖ ≤ 5 * p.R ∧
    ‖grad (trialPoint t) + t.curvature • t.displacement‖ ≤ updateRadius p (actualWeight t) / 2

lemma correctionReady_of_invariants (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (A H : Point p.d → Point p.d →L[ℝ] Point p.d) (u : Point p.d)
    (hc : ConvexOn ℝ Set.univ f) (hgrad : ∀ x, HasGradientAt f (grad x) x)
    (hderiv : ∀ x, HasFDerivAt grad (A x) x)
    (hA : ∀ x v, 0 ≤ inner ℝ (A x v) v) (hmin : ∀ x, f u ≤ f x)
    (hLip : ∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖A y - A x‖ ≤ (p.M₀ + p.M₁ * ‖grad x‖) * ‖y - x‖)
    (hH : ∀ x, ‖H x - A x‖ ≤ p.δ)
    (s : Ghost p) (t : Trial (Point p.d)) (k : ℕ) (v : ℕ → Point p.d)
    (hstate : s.1 = .correction t k v) (hb : StateBounds p s.1)
    (hm : ModelConsistent p grad H s) (he : stateEnergy p f u s.1 ≤ 8 * p.R ^ 2) :
    CorrectionReady p grad u t := by
  have hfloor : 0 < curvatureFloor p := by
    unfold curvatureFloor
    exact div_pos (by norm_num) (target_pos p hp)
  rw [hstate] at hb he
  unfold ModelConsistent at hm
  rw [hstate] at hm
  obtain ⟨model, ht, herr, hmodel⟩ := hm
  have hη := hfloor.trans_le hb.1.2.2
  have hα := tolerance_bounds p hp
  have hr := LongTails.Proofs.NoisyNewtonModel.prepare_residual hderiv hA
    p.M₀ p.M₁ p.ρ p.δ (tolerance p) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hα.1 (by linarith [hα.2]) hLip t.previous hη (H (coupling t.previous))
    (hH (coupling t.previous)) (model - grad (coupling t.previous))
  simp only [add_sub_cancel] at hr
  rw [← ht, ← herr] at hr
  have hready := LongTails.Proofs.NoisyMsEnergy.correction_ready p hp hc hgrad u hmin t
    hb.1.1.le hb.2.1.le hb.1.2.2 hb.2.2 s.2.1
    (herr.symm ▸ norm_nonneg _) hmodel he (by simpa only [mul_assoc] using hr)
  exact ⟨(actualWeight_bounds t hη hb.2.2).1, hready⟩

noncomputable def initialGhost (p : Params) : Ghost p :=
  ((algorithm p).initial (), 0, false, false)

lemma initial_baseIterate (p : Params) : baseIterate (initialGhost p).1 = initialIterate p := by
  change baseIterate (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)) = _
  split_ifs
  · rfl
  · exact baseIterate_resume p _

lemma initial_bounds (p : Params) (hp : spec.valid p) : StateBounds p (initialGhost p).1 := by
  have hh := initial_properties p hp
  have hW := target_pos p hp
  have hi : IterateBounds p (initialIterate p) := ⟨hh.1, by linarith [hh.2.1], le_rfl⟩
  change StateBounds p (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p))
  split_ifs
  · exact ⟨hi, trivial⟩
  · exact resume_bounds p _ hi

lemma initial_phaseStart (p : Params) : PhaseStart (initialGhost p).1 := by
  change PhaseStart (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p))
  split_ifs
  · trivial
  · unfold resume
    split_ifs <;> simp [PhaseStart]

lemma initial_modelConsistent (p : Params) (grad : Point p.d → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) : ModelConsistent p grad H (initialGhost p) := by
  unfold ModelConsistent initialGhost
  change (match (if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)) with
    | .hessian it v => _
    | .correction t _ _ => _
    | _ => True)
  split_ifs
  · trivial
  · unfold resume
    split_ifs <;> trivial

lemma initial_energy (p : Params) (hp : spec.valid p) (f : Point p.d → ℝ) (u : Point p.d)
    (hdist : ‖p.x0 - u‖ ≤ p.R) (hgap : f p.x0 - f u ≤ p.Δ) :
    stateEnergy p f u (initialGhost p).1 ≤ p.R ^ 2 := by
  have hA := (initial_properties p hp).1
  have hΔ := hp.2.2.2.2.2.2.1
  have hbound : (initialIterate p).A ≤ p.R ^ 2 / (2 * p.Δ) := min_le_right _ _
  have hprod := (le_div_iff₀ (by positivity : 0 < 2 * p.Δ)).mp hbound
  have hg := mul_le_mul_of_nonneg_left hgap hA.le
  have hd := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  unfold stateEnergy
  rw [initial_baseIterate]
  change (initialIterate p).A * (f p.x0 - f u) + ‖p.x0 - u‖ ^ 2 / 2 ≤ p.R ^ 2
  nlinarith only [hprod, hg, hd]

lemma ghostNext_energyFailure (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω)
    (hs : s.2.2.2 = true → 8 * p.R ^ 2 < stateEnergy p f u s.1)
    (hflag : (ghostNext p f u grad g H n s ξ).2.2.2 = true) :
    8 * p.R ^ 2 < stateEnergy p f u (ghostNext p f u grad g H n s ξ).1 := by
  by_cases hstop : stopped p s
  · rw [ghostNext_of_stopped p f u grad g H n s ξ hstop] at hflag ⊢
    exact hs hflag
  · simp only [ghostNext, ite_eq_right hstop] at hflag ⊢
    rcases s with ⟨state, error, flags⟩
    cases state with
    | model it k v => simp at hflag
    | hessian it v => simp at hflag
    | correction t k v => exact of_decide_eq_true hflag
    | done it => simp at hflag

lemma ghostTrace_energyFailure (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (grad : Point p.d → Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (s : Ghost p)
    (ξ : ℕ → p.Ω) (n : ℕ)
    (hs : s.2.2.2 = true → 8 * p.R ^ 2 < stateEnergy p f u s.1)
    (hflag : (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.2.2.2 = true) :
    8 * p.R ^ 2 < stateEnergy p f u (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1.1 := by
  induction n with
  | zero => exact hs hflag
  | succ n ih =>
    rw [blockTrace_succ] at hflag ⊢
    exact ghostNext_energyFailure p f u grad g H _ _ _ ih hflag

end LongTails.Proofs.NoisyNewtonProcess
