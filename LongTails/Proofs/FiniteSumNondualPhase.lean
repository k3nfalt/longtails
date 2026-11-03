import LongTails.Proofs.FiniteSumNondualHistory
import LongTails.Proofs.FiniteSumNondualLineSearch
import LongTails.Proofs.FiniteSumNondualPhaseGeometry

open Set Classical
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualPhase

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual
open FiniteSumNondualHistory FiniteSumNondualLineSearch FiniteSumNondualOuterGeometry
open FiniteSumNondualProxGeometry FiniteSumNondualSampling FiniteSumNondualExecution
open RecursiveEnvelopeGeometry (Model)
open FiniteSumNondualDomain

structure TrialValid (p : Params) (μ ρ δ η : ℝ) (f : Point p → ℝ) (g : Point p → Point p)
    (base : Feasible p) (past : List (Trial p)) (trial : Trial p) : Prop where
  selector_eq : trial.selector = selector p (cutBody p δ past)
  certified : Certified (domain p) g μ ρ trial.center.val trial.certificate
  coupling : ⟪μ • (trial.center.val - trial.certificate.point), trial.center.val - trial.selector.val⟫ ≤ 0
  value : envelope (domain p) f μ trial.center.val ≤ envelope (domain p) f μ (lastPoint p base past).val + η

def HistoryValid (p : Params) (μ ρ δ η : ℝ) (f : Point p → ℝ) (g : Point p → Point p)
    (base : Feasible p) (history : List (Trial p)) : Prop :=
  ∀ i (hi : i < history.length), TrialValid p μ ρ δ η f g base (history.take i) history[i]

lemma lastPoint_nil (p : Params) (base : Feasible p) : lastPoint p base [] = base := rfl

lemma lastPoint_append (p : Params) (base : Feasible p) (history : List (Trial p)) (trial : Trial p) :
    lastPoint p base (history ++ [trial]) = trialPoint p trial := by simp [lastPoint, List.foldl_append]

lemma lastPoint_take_succ (p : Params) (base : Feasible p) (history : List (Trial p))
    (i : ℕ) (hi : i < history.length) :
    lastPoint p base (history.take (i + 1)) = trialPoint p history[i] := by
  induction history generalizing i base with
  | nil => simp at hi
  | cons trial history ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < history.length := by simpa using hi
      exact ih (trialPoint p trial) i hi'

lemma historyValid_append (p : Params) (μ ρ δ η : ℝ) (f : Point p → ℝ) (g : Point p → Point p)
    (base : Feasible p) (history : List (Trial p)) (trial : Trial p)
    (hv : HistoryValid p μ ρ δ η f g base history)
    (ht : TrialValid p μ ρ δ η f g base history trial) :
    HistoryValid p μ ρ δ η f g base (history ++ [trial]) := by
  intro i hi
  by_cases hlt : i < history.length
  · simpa only [List.getElem_append_left hlt, List.take_append,
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt), List.take_zero, List.append_nil] using hv i hlt
  · have he : i = history.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa only [List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil,
      List.getElem_append_right le_rfl, List.getElem_cons_zero] using ht

lemma trialPoint_eq (p : Params) {μ ρ δ η : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    {base : Feasible p} {history : List (Trial p)} {trial : Trial p}
    (ht : TrialValid p μ ρ δ η f g base history trial) :
    (trialPoint p trial).val = trial.certificate.point :=
  feasiblePoint_val p _ ht.certified.1

lemma history_gradients (p : Params) {μ ρ δ η : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    {base : Feasible p} {history : List (Trial p)} (hv : HistoryValid p μ ρ δ η f g base history) :
    ∀ trial ∈ history, trial.certificate.gradient = g (trialPoint p trial).val := by
  intro trial ht
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  subst trial
  have hh := hv i.val i.isLt
  change history[i.val].certificate.gradient = g (trialPoint p history[i.val]).val
  rw [trialPoint_eq p hh]
  exact hh.certified.2.1

noncomputable def trialDistance (p : Params) (history : List (Trial p)) (t : ℕ) : ℝ :=
  if ht : t < history.length then ‖history[t].center.val - history[t].certificate.point‖ else 0

noncomputable def historyMovement (p : Params) (δ : ℝ) (history : List (Trial p)) (t : ℕ) : ℝ :=
  ‖(selector p (cutBody p δ (history.take t))).val -
    (selector p (cutBody p δ (history.take (t + 1)))).val‖

lemma history_descent (p : Params) {L μ ρ δ η : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ)
    {base : Feasible p} {history : List (Trial p)} (hv : HistoryValid p μ ρ δ η f g base history)
    (hρ : ρ ^ 2 / (2 * μ) ≤ η / 2) (t : ℕ) (ht : t < history.length) :
    f (lastPoint p base (history.take (t + 1))).val ≤
      f (lastPoint p base (history.take t)).val + 3 * η / 2 - μ / 2 * trialDistance p history t ^ 2 := by
  have htrial := hv t ht
  have hh := certified_descent (domain_nonempty p) (domain_compact p) hf hcont hμ
    history[t].center.val (lastPoint p base (history.take t)).val (lastPoint p base (history.take t)).property
    history[t].certificate htrial.certified htrial.value hρ
  rw [lastPoint_take_succ p base history t ht, trialPoint_eq p htrial]
  simpa only [trialDistance, dite_eq_left ht] using hh

lemma history_product (p : Params) [NeZero p.d] {μ ρ δ η : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    (hμ : 0 ≤ μ) {base : Feasible p} {history : List (Trial p)}
    (hv : HistoryValid p μ ρ δ η f g base history) (hne : (cutBody p δ history).Nonempty)
    (hρ : 2 * p.R * ρ ≤ δ / 2) (t : ℕ) (ht : t < history.length) :
    δ / 2 ≤ (μ * trialDistance p history t) * historyMovement p δ history t := by
  have htrial := hv t ht
  have hn : (cutBody p δ (history.take (t + 1))).Nonempty :=
    hne.mono (cutBody_antitone p δ (List.take_subset (t + 1) history))
  have hz := selector_mem p hn (cutBody_compact p δ _) (cutBody_convex p δ _) (cutBody_subset p δ _)
  have htake : t < (history.take (t + 1)).length := by simp only [List.length_take]; omega
  have hmem : history[t] ∈ history.take (t + 1) := by
    simpa only [List.getElem_take] using (List.getElem_mem htake)
  have hcut := hz.2 history[t] hmem
  rw [trialPoint_eq p htrial] at hcut
  have hh := certified_cut_movement hμ history[t].center.val history[t].selector.val
    (selector p (cutBody p δ (history.take (t + 1)))).val hz.1 history[t].certificate htrial.certified
    (domain_distance p htrial.certified.1 (selector p (cutBody p δ (history.take (t + 1)))).property)
    htrial.coupling hcut
  rw [htrial.selector_eq] at hh
  simp only [trialDistance, dite_eq_left ht, historyMovement]
  nlinarith

lemma history_body_empty (p : Params) [NeZero p.d] {L μ ρ δ : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) (hδ : 0 < δ) (hR : 0 < p.R)
    {m : ℕ} (hm : 0 < m) (base xstar : Feasible p) (hmin : IsMinOn f (domain p) xstar.val)
    (hgap : f base.val - f xstar.val ≤ 2 * δ) (history : List (Trial p)) (hlen : history.length = 10 * m)
    (hv : HistoryValid p μ ρ δ (δ / (16 * m)) f g base history)
    (hρ : 2 * p.R * ρ ≤ δ / 2) (hρval : ρ ^ 2 / (2 * μ) ≤ (δ / (16 * m)) / 2)
    (hbudget : 256 * μ * p.R ^ 2 * (1 + Nat.log 2 p.d : ℕ) * (1 + Nat.log 2 (10 * m) : ℕ) ≤
      (m : ℝ) ^ 3 * δ) : ¬(cutBody p δ history).Nonempty := by
  intro hne
  have hn (t : ℕ) (_ht : t ≤ 10 * m) : (cutBody p δ (history.take t)).Nonempty :=
    hne.mono (cutBody_antitone p δ (List.take_subset t history))
  have hd := FiniteSumNondualPhaseGeometry.phase_energy hm
    (fun t => f (lastPoint p base (history.take t)).val) (trialDistance p history)
    (fun t ht => history_descent p hf hcont hμ hv hρval t (by omega))
    (show f (lastPoint p base (history.take 0)).val - f (lastPoint p base (history.take (10 * m))).val ≤ 2 * δ by
      have hh := hmin (lastPoint p base (history.take (10 * m))).property
      change f xstar.val ≤ f (lastPoint p base (history.take (10 * m))).val at hh
      simp only [List.take_zero, lastPoint_nil]
      linarith) hδ.le
  have hmovement := history_movement p hR δ history (10 * m) hn
  exact FiniteSumNondualPhaseGeometry.phase_impossible hm (trialDistance p history) (historyMovement p δ history)
    hμ hδ hR.le (by positivity) (by positivity) (fun _ _ => norm_nonneg _)
    (fun t ht => history_product p hμ.le hv hne hρ t (by omega)) hd hmovement hbudget

lemma phase_contract (p : Params) [NeZero p.d] {L μ ρ δ : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) (hδ : 0 < δ) (hR : 0 < p.R)
    {m : ℕ} (hm : 0 < m) (base xstar : Feasible p) (hmin : IsMinOn f (domain p) xstar.val)
    (hgap : f base.val - f xstar.val ≤ 2 * δ) (lineFuel : ℕ)
    (hρ : 2 * p.R * ρ ≤ (δ / (16 * m)) / 2)
    (hρval : ρ ^ 2 / (2 * μ) ≤ (δ / (16 * m)) / 2)
    (hprecision : 4 * μ * p.R ^ 2 / (2 : ℝ) ^ lineFuel ≤ (δ / (16 * m)) / 2)
    (hbudget : 256 * μ * p.R ^ 2 * (1 + Nat.log 2 p.d : ℕ) * (1 + Nat.log 2 (10 * m) : ℕ) ≤
      (m : ℝ) ^ 3 * δ)
    (fuel : ℕ) (history : List (Trial p)) (hlen : history.length + fuel = 10 * m)
    (hv : HistoryValid p μ ρ δ (δ / (16 * m)) f g base history) :
    Contract (fun q out => Certified (domain p) g μ ρ q.val out)
      (fun out => f out.val - f xstar.val ≤ δ) (phasePlan p μ δ lineFuel fuel history base) := by
  let good := fun (q : Feasible p) out => Certified (domain p) g μ ρ q.val out
  have hη : 0 ≤ δ / (16 * (m : ℝ)) := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hηδ : δ / (16 * (m : ℝ)) ≤ δ := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * (m : ℝ))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hm1 hδ.le]
  have hρcut : 2 * p.R * ρ ≤ δ / 2 := by linarith
  have henv := envelope_model (domain_nonempty p) (domain_compact p) (domain_convex p) hf hcont hμ
  have herr : ∀ q out, good q out →
      ‖μ • (q.val - out.point) - envelopeSlope (domain p) f μ q.val‖ ≤ ρ := by
    intro q out hc
    exact certified_gradient_error (domain_nonempty p) (domain_compact p) (domain_convex p) hf hcont hμ q.val out hc
  induction fuel generalizing history with
  | zero =>
    change (fun out : Feasible p => f out.val - f xstar.val ≤ δ)
      (if (cutBody p δ history).Nonempty then lastPoint p base history else historyOutput p δ history)
    split_ifs with hn
    · exact False.elim (history_body_empty p hf hcont hμ hδ hR hm base xstar hmin hgap history
        (by omega) hv hρcut hρval hbudget hn)
    · exact (historyOutput_gap p hf history (history_gradients p hv) hn xstar.val xstar.property).le
  | succ fuel ih =>
    change Contract good _ (if (cutBody p δ history).Nonempty then _ else .done (historyOutput p δ history))
    split_ifs with hn
    · apply contract_bind (line_contract p henv (selector p (cutBody p δ history))
        (lastPoint p base history) good herr hη hρ lineFuel hprecision)
      intro e he
      let trial : Trial p := ⟨selector p (cutBody p δ history),
        linePoint p (selector p (cutBody p δ history)) (lastPoint p base history) e.time, e.certificate⟩
      have ht : TrialValid p μ ρ δ (δ / (16 * m)) f g base history trial :=
        ⟨rfl, he.2.2.1, he.2.2.2.1, he.2.2.2.2⟩
      exact ih (history ++ [trial]) (by simp only [List.length_append, List.length_singleton]; omega)
        (historyValid_append p μ ρ δ (δ / (16 * m)) f g base history trial hv ht)
    · exact (historyOutput_gap p hf history (history_gradients p hv) hn xstar.val xstar.property).le

lemma phase_within (p : Params) (μ δ : ℝ) (lineFuel fuel : ℕ) (history : List (Trial p)) (base : Feasible p) :
    Within (fuel * (lineFuel + 2)) (phasePlan p μ δ lineFuel fuel history base) := by
  induction fuel generalizing history with
  | zero => simp [phasePlan, Within]
  | succ fuel ih =>
    simp only [phasePlan]
    split_ifs
    · have hh := within_bind (line_within p μ (selector p (cutBody p δ history)) (lastPoint p base history) lineFuel)
        (fun e => phasePlan p μ δ lineFuel fuel
          (history ++ [⟨selector p (cutBody p δ history),
            linePoint p (selector p (cutBody p δ history)) (lastPoint p base history) e.time, e.certificate⟩]) base)
        (fun _ => ih _)
      convert hh using 1
      ring
    · simp [Within]

lemma phases_within (p : Params) (μ : ℝ) (phaseFuel lineFuel phases : ℕ) (base : Feasible p) :
    Within (phases * (phaseFuel * (lineFuel + 2))) (phasesPlan p μ phaseFuel lineFuel phases base) := by
  induction phases generalizing base with
  | zero => simp [phasesPlan, Within]
  | succ phases ih =>
    have hh := within_bind (phase_within p μ (p.ε / 2 * (2 : ℝ) ^ phases) lineFuel phaseFuel [] base)
      (fun next => phasesPlan p μ phaseFuel lineFuel phases next) (fun next => ih next)
    change Within ((phases + 1) * (phaseFuel * (lineFuel + 2)))
      ((phasePlan p μ (p.ε / 2 * (2 : ℝ) ^ phases) lineFuel phaseFuel [] base).bind fun next =>
        phasesPlan p μ phaseFuel lineFuel phases next)
    convert hh using 1
    ring

lemma phases_contract (p : Params) [NeZero p.d] {L μ ρ : ℝ} {f : Point p → ℝ} {g : Point p → Point p}
    (hf : Model L f g) (hcont : Continuous f) (hμ : 0 < μ) (hε : 0 < p.ε) (hR : 0 < p.R)
    {m : ℕ} (hm : 0 < m) (xstar : Feasible p) (hmin : IsMinOn f (domain p) xstar.val)
    (lineFuel : ℕ) (hρ : 2 * p.R * ρ ≤ p.ε / (64 * m))
    (hρval : ρ ^ 2 / (2 * μ) ≤ p.ε / (64 * m))
    (hprecision : 4 * μ * p.R ^ 2 / (2 : ℝ) ^ lineFuel ≤ p.ε / (64 * m))
    (hbudget : 512 * μ * p.R ^ 2 * (1 + Nat.log 2 p.d : ℕ) * (1 + Nat.log 2 (10 * m) : ℕ) ≤
      (m : ℝ) ^ 3 * p.ε)
    (phases : ℕ) (hphases : 0 < phases) (base : Feasible p)
    (hgap : f base.val - f xstar.val ≤ p.ε / 2 * (2 : ℝ) ^ phases) :
    Contract (fun q out => Certified (domain p) g μ ρ q.val out)
      (fun out => f out.val - f xstar.val ≤ p.ε / 2) (phasesPlan p μ (10 * m) lineFuel phases base) := by
  induction phases generalizing base with
  | zero => omega
  | succ phases ih =>
    let δ := p.ε / 2 * (2 : ℝ) ^ phases
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδmin : p.ε / 2 ≤ δ := by
      have hh : (1 : ℝ) ≤ (2 : ℝ) ^ phases := one_le_pow₀ (by norm_num)
      dsimp only [δ]
      nlinarith
    have hgap' : f base.val - f xstar.val ≤ 2 * δ := by
      dsimp only [δ]
      rw [pow_succ] at hgap
      nlinarith
    have htol : p.ε / (64 * (m : ℝ)) ≤ (δ / (16 * m)) / 2 := by
      have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have hh := div_le_div_of_nonneg_right hδmin (show 0 ≤ 32 * (m : ℝ) by positivity)
      convert hh using 1 <;> ring
    have hbudget' : 256 * μ * p.R ^ 2 * (1 + Nat.log 2 p.d : ℕ) * (1 + Nat.log 2 (10 * m) : ℕ) ≤
        (m : ℝ) ^ 3 * δ := by
      have hh := mul_le_mul_of_nonneg_left hδmin (show 0 ≤ (m : ℝ) ^ 3 by positivity)
      nlinarith
    have hfirst := phase_contract p hf hcont hμ hδ hR hm base xstar hmin hgap' lineFuel
      (hρ.trans htol) (hρval.trans htol) (hprecision.trans htol) hbudget' (10 * m) [] (by simp)
      (by intro i hi; simp at hi)
    change Contract _ _ ((phasePlan p μ δ lineFuel (10 * m) [] base).bind fun next =>
      phasesPlan p μ (10 * m) lineFuel phases next)
    apply contract_bind hfirst
    intro next hnext
    cases phases with
    | zero => simpa only [δ, pow_zero, mul_one, phasesPlan, Contract] using hnext
    | succ phases =>
      exact ih (by omega) next hnext

end LongTails.Proofs.FiniteSumNondualPhase
