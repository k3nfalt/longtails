import LongTails.Algorithms.StochasticGeneralizedMirror
import LongTails.Proofs.RobustPilot
import LongTails.Proofs.GeneralNormClipping
import LongTails.Proofs.GeneralizedMirrorTuning
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.AcceleratedMarkovExecution

open MeasureTheory
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror

namespace LongTails.Proofs.GeneralizedMirrorExecution

abbrev StateCode (q : Public) (m : ℕ) :=
  ℝ × q.E × q.E × ℕ × ℕ × (Fin m → Dual q) × Dual q × Dual q

def stateCode {q : Public} {m : ℕ} (s : State q m) : StateCode q m :=
  (s.A, s.x, s.z, s.stage, s.received, s.pilot, s.center, s.direction)

noncomputable instance {q : Public} {m : ℕ} : MeasurableSpace (State q m) :=
  MeasurableSpace.comap stateCode inferInstance

lemma measurable_stateCode (q : Public) (m : ℕ) : Measurable (@stateCode q m) :=
  comap_measurable _

@[fun_prop] lemma measurable_state_A (q : Public) (m : ℕ) :
    Measurable (@State.A q m) := (measurable_stateCode q m).fst

@[fun_prop] lemma measurable_state_x (q : Public) (m : ℕ) :
    Measurable (@State.x q m) := (measurable_stateCode q m).snd.fst

@[fun_prop] lemma measurable_state_z (q : Public) (m : ℕ) :
    Measurable (@State.z q m) := (measurable_stateCode q m).snd.snd.fst

@[fun_prop] lemma measurable_state_stage (q : Public) (m : ℕ) :
    Measurable (@State.stage q m) := (measurable_stateCode q m).snd.snd.snd.fst

@[fun_prop] lemma measurable_state_received (q : Public) (m : ℕ) :
    Measurable (@State.received q m) := (measurable_stateCode q m).snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_pilot (q : Public) (m : ℕ) :
    Measurable (@State.pilot q m) := (measurable_stateCode q m).snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_center (q : Public) (m : ℕ) :
    Measurable (@State.center q m) := (measurable_stateCode q m).snd.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_direction (q : Public) (m : ℕ) :
    Measurable (@State.direction q m) := (measurable_stateCode q m).snd.snd.snd.snd.snd.snd.snd

@[fun_prop] lemma measurable_state_mk {W : Type*} [MeasurableSpace W]
    {q : Public} {m : ℕ} {A : W → ℝ} {x z : W → q.E} {stage received : W → ℕ}
    {pilot : W → Fin m → Dual q} {center direction : W → Dual q}
    (hA : Measurable A) (hx : Measurable x) (hz : Measurable z)
    (hs : Measurable stage) (hr : Measurable received) (hp : Measurable pilot)
    (hc : Measurable center) (hd : Measurable direction) :
    Measurable (fun w => State.mk (A w) (x w) (z w) (stage w) (received w)
      (pilot w) (center w) (direction w)) := by
  apply measurable_comap_iff.mpr
  exact hA.prodMk (hx.prodMk (hz.prodMk (hs.prodMk (hr.prodMk (hp.prodMk (hc.prodMk hd))))))

@[fun_prop] lemma measurable_stepWeight (q : Public) (ell : ℝ) :
    Measurable (stepWeight q ell) := by
  unfold stepWeight
  fun_prop

@[fun_prop] lemma measurable_mix (q : Public) :
    Measurable (fun w : ℝ × ℝ × q.E × q.E => mix w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  unfold mix
  fun_prop

lemma measurable_storePilot (q : Public) (m : ℕ) :
    Measurable (fun w : State q m × Dual q => storePilot w.1 w.2) := by
  apply Measurable.of_eval
  intro i
  unfold storePilot
  exact measurable_snd.ite
    (measurableSet_eq_fun measurable_const ((measurable_state_received q m).comp measurable_fst))
    ((measurable_pi_apply i).comp ((measurable_state_pilot q m).comp measurable_fst))

lemma measurable_update_gradient (q : Public) (ell : ℝ) (m : ℕ) :
    Measurable (fun w : State q m × Dual q => update q ell w.1 (Sum.inl w.2)) := by
  have hfst : Measurable (Prod.fst : State q m × Dual q → State q m) := measurable_fst
  have hA := (measurable_state_A q m).comp hfst
  have hx := (measurable_state_x q m).comp hfst
  have hz := (measurable_state_z q m).comp hfst
  have hs := (measurable_state_stage q m).comp hfst
  have hr := (measurable_state_received q m).comp hfst
  have hp := (measurable_state_pilot q m).comp hfst
  have hc := (measurable_state_center q m).comp hfst
  have hd := (measurable_state_direction q m).comp hfst
  have hw := measurable_storePilot q m
  have hcenter := (OracleTemplate.RobustGradient.measurable_pilotCenter m).comp
    ((measurable_const (a := clipRadius q)).prodMk hw)
  have hclip := hc.add ((OracleTemplate.GeneralNormClipping.measurable_clip (clipRadius q)).comp
    (measurable_snd.sub hc))
  unfold update
  dsimp only
  apply Measurable.ite (measurableSet_le measurable_const hA) measurable_fst
  apply Measurable.ite (measurableSet_eq_fun hs measurable_const)
  · apply Measurable.ite (measurableSet_eq_fun (hr.add_const 1) measurable_const)
    · exact measurable_state_mk hA hx hz measurable_const hr hw hcenter hd
    · exact measurable_state_mk hA hx hz hs (hr.add_const 1) hw hc hd
  · apply Measurable.ite (measurableSet_eq_fun hs measurable_const)
    · exact measurable_state_mk hA hx hz measurable_const hr hp hc hclip
    · exact measurable_fst

lemma measurable_update_prox (q : Public) (ell : ℝ) (m : ℕ) :
    Measurable (fun w : State q m × q.E => update q ell w.1 (Sum.inr w.2)) := by
  have hfst : Measurable (Prod.fst : State q m × q.E → State q m) := measurable_fst
  have hA := (measurable_state_A q m).comp hfst
  have hx := (measurable_state_x q m).comp hfst
  have hs := (measurable_state_stage q m).comp hfst
  have ha := (measurable_stepWeight q ell).comp hA
  have hm : Measurable (fun w : State q m × q.E =>
      mix w.1.A (stepWeight q ell w.1.A) w.1.x w.2) := by
    unfold mix
    exact ((hA.div (hA.add ha)).smul hx).add ((ha.div (hA.add ha)).smul measurable_snd)
  unfold update
  dsimp only
  apply Measurable.ite (measurableSet_le measurable_const hA) measurable_fst
  apply Measurable.ite (measurableSet_eq_fun hs measurable_const)
  · exact measurable_state_mk (hA.add ha) hm measurable_snd measurable_const
      measurable_const measurable_const measurable_const measurable_const
  · exact measurable_fst

lemma measurable_update (q : Public) (ell : ℝ) (m : ℕ) :
    Measurable (fun w : State q m × Reply q => update q ell w.1 w.2) := by
  classical
  have hl : Measurable (fun r : Reply q => Sum.elim id (fun _ => (0 : Dual q)) r) :=
    measurable_id.sumElim measurable_const
  have hr : Measurable (fun r : Reply q => Sum.elim (fun _ => (0 : q.E)) id r) :=
    measurable_const.sumElim measurable_id
  have hg := (measurable_update_gradient q ell m).comp
    (measurable_fst.prodMk (hl.comp measurable_snd))
  have hp := (measurable_update_prox q ell m).comp
    (measurable_fst.prodMk (hr.comp measurable_snd))
  have hh : Measurable (fun w : State q m × Reply q =>
      if w.2 ∈ Set.range Sum.inl then
        update q ell w.1 (Sum.inl (Sum.elim id (fun _ => (0 : Dual q)) w.2))
      else update q ell w.1 (Sum.inr (Sum.elim (fun _ => (0 : q.E)) id w.2))) :=
    hg.ite ((measurableSet_range_inl (α := Dual q) (β := q.E)).preimage measurable_snd) hp
  convert hh using 1
  funext w
  rcases w with ⟨s, v | p⟩ <;> simp

lemma update_frozen (q : Public) (ell : ℝ) {m : ℕ} (s : State q m)
    (reply : Reply q) (h : q.R ^ 2 / q.ε ≤ s.A) : update q ell s reply = s := by
  simp only [update, h, ite_eq_left]

lemma update_gradient_output (q : Public) (ell : ℝ) {m : ℕ} (s : State q m)
    (v : Dual q) : (update q ell s (Sum.inl v)).x = s.x := by
  unfold update
  split_ifs <;> rfl

lemma update_positive_weight (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    {m : ℕ} (s : State q m) (hA : 0 < s.A) (r : Reply q) :
    0 < (update q ell s r).A := by
  have ha := GeneralizedMirrorTuning.stepWeight_pos q hq hell hA
  cases r <;> unfold update <;> split_ifs <;> (try dsimp only) <;> linarith

lemma update_pilot (q : Public) (ell : ℝ) {m : ℕ} (s : State q m) (v : Dual q)
    (hactive : s.A < q.R ^ 2 / q.ε) (hs : s.stage = 0) (hn : s.received + 1 ≠ m) :
    update q ell s (Sum.inl v) =
      { s with received := s.received + 1, pilot := storePilot s v } := by
  simp [update, not_le.mpr hactive, hs, hn]

lemma update_last_pilot (q : Public) (ell : ℝ) {m : ℕ} (s : State q m) (v : Dual q)
    (hactive : s.A < q.R ^ 2 / q.ε) (hs : s.stage = 0) (hn : s.received + 1 = m) :
    update q ell s (Sum.inl v) = { s with
      stage := 1
      pilot := storePilot s v
      center := OracleTemplate.RobustGradient.pilotCenter (clipRadius q) (storePilot s v) } := by
  simp [update, not_le.mpr hactive, hs, hn]

lemma update_fresh (q : Public) (ell : ℝ) {m : ℕ} (s : State q m) (v : Dual q)
    (hactive : s.A < q.R ^ 2 / q.ε) (hs : s.stage = 1) :
    update q ell s (Sum.inl v) = { s with
      stage := 2
      direction := OracleTemplate.RobustGradient.centeredClip (clipRadius q) s.center v } := by
  simp [update, not_le.mpr hactive, hs]

noncomputable def oracleReply {q : Public} (I : Instance q) (g : q.E → q.Ω → Dual q)
    (request : Query q) (ω : q.Ω) : Reply q := match request with
  | .gradient x => Sum.inl (g x ω)
  | .prox a z v => Sum.inr (I.prox a z v)

noncomputable def rawAdvance (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (n call : ℕ) (s : State q m) : State q m :=
  OracleTemplate.StochasticGradient.advance
    (fun k state => update q ell state (oracleReply I g (query q ell state) (ξ k))) n call s

lemma rawAdvance_add (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (n l call : ℕ) (s : State q m) :
    rawAdvance q ell m I g ξ (n + l) call s =
      rawAdvance q ell m I g ξ l (call + n) (rawAdvance q ell m I g ξ n call s) :=
  OracleTemplate.HeavyTailedMarkovGradient.advance_add _ _ _ _ _

lemma execute_eq_rawAdvance (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (P : ProbabilityMeasure (ℕ → q.Ω)) (K : ℕ) (ξ : ℕ → q.Ω) :
    OracleTemplate.execute
      { Seed := fun _ => q.Ω, law := P,
        answer := fun _ (_, request) seed => oracleReply I g request seed }
      (algorithm q ell m) (fun _ => K) () ξ =
      (rawAdvance q ell m I g ξ K 0 (initialState q m)).x := by
  exact OracleTemplate.StochasticGradient.execute_advance P (oracleReply I g)
    (algorithm q ell m) K () ξ

lemma rawAdvance_frozen (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (n call : ℕ) (s : State q m)
    (h : q.R ^ 2 / q.ε ≤ s.A) : rawAdvance q ell m I g ξ n call s = s := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih =>
    change rawAdvance q ell m I g ξ n (call + 1)
      (update q ell s (oracleReply I g (query q ell s) (ξ call))) = s
    rw [update_frozen q ell s _ h]
    exact ih (call + 1)

end LongTails.Proofs.GeneralizedMirrorExecution
