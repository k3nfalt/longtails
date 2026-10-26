import LongTails.Proofs.StochasticEnvelopeLocalization
import LongTails.Proofs.StochasticEnvelopeFreshness
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Proofs.RecursiveEnvelopeExecution

open MeasureTheory

namespace LongTails.Proofs.StochasticEnvelopeExecution

open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution

variable {Q R U : Type*}

lemma slotCalls_sum (cost : ℕ → ℕ) (n slot : ℕ) :
    slotCalls cost n slot = ∑ i ∈ Finset.range n, cost (slot + i) := by
  induction n generalizing slot with
  | zero => simp [slotCalls]
  | succ n ih =>
    rw [slotCalls, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm]

lemma evalAt_slotPlan_succ (reply : ℕ → Q → R) (cost : ℕ → ℕ)
    (step : (i : ℕ) → U → QueryPlan Q R U (cost i)) (n slot call : ℕ) (state : U) :
    evalAt reply (slotPlan cost step (n + 1) slot state) call =
      evalAt reply (slotPlan cost step n (slot + 1)
        (evalAt reply (step slot state) call)) (call + cost slot) := by
  exact evalAt_bind reply (step slot state) (slotPlan cost step n (slot + 1)) call

lemma execute_complete {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (program : S → Σ k, QueryPlan Q R U k) (O : Oracle Q R) (K : ℕ) (seed : S)
    (ξ : (k : ℕ) → O.Seed k) (reply : ℕ → Q → R)
    (hr : ∀ history query, O.answer history query (ξ history.length) = reply history.length query.2)
    (hK : (program seed).1 ≤ K) :
    execute O (algorithm law q0 u0 program) (fun _ => K) seed ξ =
      evalAt reply (program seed).2 0 := by
  erw [StochasticGradient.execute_advance_of_answer O (algorithm law q0 u0 program)
    K seed ξ (fun k query => reply k query.2) hr]
  change QueryPlan.output u0 (StochasticGradient.advance
    (fun k state => QueryPlan.update state (reply k (QueryPlan.query q0 state)))
    K 0 (program seed)) = _
  rw [advance_plan_indexed reply q0 (program seed).2 hK]
  rfl

section LocalizationPlans
open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution
variable {Q R U : Type*}

lemma evalAt_castPlan (reply : ℕ → Q → R) {k m : ℕ} (h : k = m)
    (plan : QueryPlan Q R U k) (call : ℕ) :
    evalAt reply (castPlan h plan) call = evalAt reply plan call := by cases h; rfl

lemma evalAt_collectPlans (reply : ℕ → Q → R) {k : ℕ} (n : ℕ)
    (plans : Fin n → QueryPlan Q R U k) (call : ℕ) :
    evalAt reply (collectPlans n plans) call =
      fun i => evalAt reply (plans i) (call + k * i.val) := by
  induction n generalizing call with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      rw [collectPlans, evalAt_bind, evalAt_map, ih]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cases_succ, Fin.val_succ]
        congr 1
        ring

lemma advance_plan_remaining (reply : ℕ → Q → R) (q0 : Q) {k : ℕ}
    (plan : QueryPlan Q R U k) (K call : ℕ) :
    (StochasticGradient.advance (fun n state =>
      QueryPlan.update state (reply n (QueryPlan.query q0 state))) K call ⟨k, plan⟩).1 =
      k - K := by
  induction plan generalizing K call with
  | done value =>
      induction K generalizing call with
      | zero => rfl
      | succ K ih => simpa [StochasticGradient.advance, QueryPlan.update, Nat.zero_sub] using ih (call + 1)
  | @ask k query next ih =>
      cases K with
      | zero => rfl
      | succ K => simpa [StochasticGradient.advance, QueryPlan.update, QueryPlan.query] using ih (reply call query) K (call + 1)

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma evalAt_clippedPlan (g : E → Ω → E) (Λ D C μ : ℝ) (center anchor : E)
    (ξ : ℕ → Ω) (K call : ℕ) :
    evalAt (fun k x => g x (ξ k)) (clippedPlan Λ D C μ center anchor K) call =
      HeavyTailedMarkovGradient.clippedRun (fun x ω => g x ω + μ • (x - center))
        Λ D C 1 anchor (fun k => ξ (call + k)) K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [clippedPlan, evalAt_castPlan, evalAt_bind, ih]
      simp only [evalAt, HeavyTailedMarkovGradient.clippedRun, Nat.mul_one]

lemma evalAt_stagePlan (g : E → Ω → E) (L μ p s a U D : ℝ) (center anchor : E)
    (K replicas call : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun k x => g x (ξ k)) (stagePlan L μ p s a U D center anchor K replicas) call =
      LongTails.Algorithms.StochasticEnvelopeLocalization.stage g L μ p s a U D
        center anchor K replicas (fun i k => ξ (call + K * i.val + k)) := by
  simp only [stagePlan, evalAt_map, evalAt_collectPlans, evalAt_clippedPlan,
    LongTails.Algorithms.StochasticEnvelopeLocalization.stage]

lemma evalAt_refinePlan (g : E → Ω → E) (L μ p s a U n : ℝ) (center start : E)
    (K replicas J call : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun k x => g x (ξ k)) (refinePlan L μ p s a U n center start K replicas J) call =
      LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun g L μ p s a U n
        center start K replicas
        (fun j i k => ξ (call + K * (replicas + 1) * j + K * i.val + k)) J := by
  induction J with
  | zero => rfl
  | succ J ih =>
      rw [refinePlan, evalAt_castPlan, evalAt_bind, ih, evalAt_map, evalAt_stagePlan]
      rfl


end LocalizationPlans

section Substitution
open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution
variable {Q R U A B : Type*}

lemma slotCalls_prefix_succ (cost : ℕ → ℕ) (slot : ℕ) :
    slotCalls cost (slot + 1) 0 = slotCalls cost slot 0 + cost slot := by
  simp only [slotCalls_sum, Nat.zero_add, Finset.sum_range_succ]

lemma evalAt_substitutePlan (raw : ℕ → A → B) (cost : ℕ → ℕ)
    (child : (i : ℕ) → Q → QueryPlan A B R (cost i)) {k : ℕ}
    (plan : QueryPlan Q R U k) (slot offset : ℕ) :
    evalAt raw (substitutePlan cost child plan slot) (offset + slotCalls cost slot 0) =
      evalAt (fun i q => evalAt raw (child i q) (offset + slotCalls cost i 0)) plan slot := by
  induction plan generalizing slot with
  | done value => rfl
  | @ask k query next ih =>
      simp only [substitutePlan, slotCalls, evalAt_bind]
      have he : offset + slotCalls cost slot 0 + cost slot =
          offset + slotCalls cost (slot + 1) 0 := by rw [slotCalls_prefix_succ]; omega
      rw [he, ih]
      rfl


end Substitution

section PilotPlans
open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma evalAt_robustPlan (g : E → Ω → E) (point : E) (b replicas call : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun k x => g x (ξ k)) (robustPlan point b replicas) call =
      LongTails.Algorithms.StochasticEnvelopePilot.robustMean (b := b) (n := replicas)
        (fun i j k => g point (ξ (call + (b + 1) * 8 * i.val + (b + 1) * j.val + k.val))) := by
  simp only [robustPlan, evalAt_map, evalAt_collectPlans, evalAt_castPlan, evalAt, Nat.one_mul]

lemma evalAt_pilotPlan (g : E → Ω → E) (L μ β radius : ℝ) (center : E)
    (b replicas N call : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun k x => g x (ξ k)) (pilotPlan L μ β radius center b replicas N) call =
      LongTails.Algorithms.StochasticEnvelopePilot.sampledRun (b := b) (n := replicas) g L μ β radius center
        (fun j i k l => ξ (call + (b + 1) * 8 * (replicas + 1) * j +
          (b + 1) * 8 * i.val + (b + 1) * k.val + l.val)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [pilotPlan, evalAt_castPlan, evalAt_bind, ih, evalAt_map, evalAt_robustPlan]
      unfold LongTails.Algorithms.StochasticEnvelopePilot.sampledRun
      rw [HeavyTailedMarkovGradient.advance_add]
      simp only [StochasticGradient.advance, Nat.zero_add]
      rfl

lemma evalAt_radiusPlan (g : E → Ω → E) (L μ s β : ℝ) (center : E)
    (b replicas N call : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun k x => g x (ξ k)) (radiusPlan L μ s β center b replicas N) call =
      LongTails.Algorithms.StochasticEnvelopePilot.localizedRadius (b := b) (n := replicas)
        g L μ s β center
        (fun i j k => ξ (call + (b + 1) * 8 * i.val + (b + 1) * j.val + k.val))
        (fun j i k l => ξ (call + (b + 1) * 8 * (replicas + 1) +
          (b + 1) * 8 * (replicas + 1) * j + (b + 1) * 8 * i.val + (b + 1) * k.val + l.val)) N := by
  simp only [radiusPlan, evalAt_castPlan, evalAt_bind, evalAt_robustPlan, evalAt_map, evalAt_pilotPlan,
    LongTails.Algorithms.StochasticEnvelopePilot.localizedRadius]

lemma evalAt_approximatePlan (g : E → Ω → E) (L μ p s a n β : ℝ) (center : E)
    (b pilotReplicas innerReplicas N K J call : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun k x => g x (ξ k))
      (approximatePlan L μ p s a n β center b pilotReplicas innerReplicas N K J) call =
      LongTails.Algorithms.StochasticEnvelopeLocalization.approximate g L μ p s a n β center
        b pilotReplicas innerReplicas N K J
        (fun i j k => ξ (call + (b + 1) * 8 * i.val + (b + 1) * j.val + k.val))
        (fun j i k l => ξ (call + (b + 1) * 8 * (pilotReplicas + 1) +
          (b + 1) * 8 * (pilotReplicas + 1) * j + (b + 1) * 8 * i.val + (b + 1) * k.val + l.val))
        (fun j i k => ξ (call + (b + 1) * 8 * (pilotReplicas + 1) * (N + 1) +
          K * (innerReplicas + 1) * j + K * i.val + k)) := by
  rw [approximatePlan, evalAt_castPlan, evalAt_bind, evalAt_radiusPlan, evalAt_refinePlan]
  rfl


end PilotPlans

section DebiasedPlan
open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma evalAt_debiasedPlan (reply : ℕ → E → E) (v : ℝ) (cost : ℕ → ℕ)
    (plans : (ell : ℕ) → QueryPlan E E E (cost ell)) (n call : ℕ) :
    evalAt reply (debiasedPlan v cost plans n) call = debiasedValue v n
      (evalAt reply (plans 0) call)
      (evalAt reply (plans (n + 1)) (call + cost 0))
      (evalAt reply (plans n) (call + cost 0 + cost (n + 1))) := by
  rw [debiasedPlan, evalAt_castPlan, evalAt_bind, evalAt_bind, evalAt_map]


end DebiasedPlan

section CursorMachine
open MeasureTheory
open OracleTemplate LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution
open LongTails.Proofs.StochasticEnvelopeFreshness

variable {Q R U S A B Ω : Type*}

lemma evalAt_prefix_congr (reply other : ℕ → Q → R) {k : ℕ} (plan : QueryPlan Q R U k)
    (call : ℕ) (h : ∀ j, j < k → ∀ q, reply (call + j) q = other (call + j) q) :
    evalAt reply plan call = evalAt other plan call := by
  induction plan generalizing call with
  | done value => rfl
  | @ask k query next ih =>
      have h0 := h 0 (by omega) query
      simp only [Nat.add_zero] at h0
      simp only [evalAt, h0]
      apply ih
      intro j hj q
      have hh := h (j + 1) (by omega) q
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma evalAt_shift (reply : ℕ → Q → R) {k : ℕ} (plan : QueryPlan Q R U k)
    (offset call : ℕ) :
    evalAt (fun j q => reply (offset + j) q) plan call = evalAt reply plan (offset + call) := by
  induction plan generalizing call with
  | done value => rfl
  | ask query next ih =>
      simp only [evalAt, ih, Nat.add_assoc]

lemma evalAt_statePlan (reply : ℕ → Q → R) (query : ℕ → U → Q) (update : ℕ → U → R → U)
    (N call : ℕ) (state : U) :
    evalAt reply (statePlan query update N call state) call =
      StochasticGradient.advance (fun j u => update j u (reply j (query j u))) N call state := by
  induction N generalizing call state with
  | zero => rfl
  | succ N ih => exact ih (call + 1) _

lemma cursorCalls_sum (cost : ℕ → S → ℕ) (seeds : ℕ → S) (N call slot : ℕ) :
    cursorCalls cost seeds N call slot = ∑ j ∈ Finset.range N, cost (call + j) (seeds (slot + j)) := by
  induction N generalizing call slot with
  | zero => simp [cursorCalls]
  | succ N ih =>
      rw [cursorCalls, ih, Finset.sum_range_succ']
      simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm]

lemma cursorCalls_slotCalls (cost : ℕ → S → ℕ) (seeds : ℕ → S) (N call : ℕ) :
    cursorCalls cost seeds N call call = slotCalls (fun j => cost j (seeds j)) N call := by
  rw [cursorCalls_sum, slotCalls_sum]

lemma cursorRun_cursor (cost : ℕ → S → ℕ) (response : ℕ → S → Q → (ℕ → Ω) → R)
    (query : ℕ → U → Q) (update : ℕ → U → R → U) (seeds : ℕ → S) (ξ : ℕ → Ω)
    (N call slot raw : ℕ) (state : U) :
    (cursorRun cost response query update seeds ξ N call slot raw state).2 =
      raw + cursorCalls cost seeds N call slot := by
  induction N generalizing call slot raw state with
  | zero => simp [cursorRun, cursorCalls]
  | succ N ih => rw [cursorRun, ih, cursorCalls, Nat.add_assoc]

lemma cursorRun_freshRun (cost : ℕ → S → ℕ) (response : ℕ → S → Q → (ℕ → Ω) → R)
    (query : ℕ → U → Q) (update : ℕ → U → R → U) (seeds : ℕ → S) (ξ : ℕ → Ω)
    (N call slot raw : ℕ) (state : U) :
    (cursorRun cost response query update seeds ξ N call slot raw state).1 =
      freshRun cost (fun j u child => update j u (response j child.1 (query j u) child.2))
        N call state ((fun j => seeds (slot + j)), fun j => ξ (raw + j)) := by
  induction N generalizing call slot raw state with
  | zero => rfl
  | succ N ih =>
      simp only [cursorRun, ih, freshRun, Nat.add_zero]
      congr 2 <;> funext j <;> simp only [Nat.add_comm, Nat.add_left_comm]

lemma evalAt_substituted_statePlan (cost : ℕ → S → ℕ)
    (child : (j : ℕ) → (s : S) → Q → QueryPlan A B R (cost j s))
    (g : A → Ω → B) (query : ℕ → U → Q) (update : ℕ → U → R → U)
    (seeds : ℕ → S) (ξ : ℕ → Ω) (N call offset : ℕ) (state : U) :
    evalAt (fun j x => g x (ξ j))
      (substitutePlan (fun j => cost j (seeds j)) (fun j => child j (seeds j))
        (statePlan query update N call state) call)
      (offset + slotCalls (fun j => cost j (seeds j)) call 0) =
    (cursorRun cost (fun j s q ζ => evalAt (fun k x => g x (ζ k)) (child j s q) 0)
      query update seeds ξ N call call
      (offset + slotCalls (fun j => cost j (seeds j)) call 0) state).1 := by
  rw [evalAt_substitutePlan]
  induction N generalizing call state with
  | zero => rfl
  | succ N ih =>
      simp only [statePlan, evalAt, cursorRun]
      have hs := evalAt_shift (fun j x => g x (ξ j))
        (child call (seeds call) (query call state))
        (offset + slotCalls (fun j => cost j (seeds j)) call 0) 0
      simp only [Nat.add_zero] at hs
      rw [hs]
      have he : offset + slotCalls (fun j => cost j (seeds j)) call 0 + cost call (seeds call) =
          offset + slotCalls (fun j => cost j (seeds j)) (call + 1) 0 := by
        rw [slotCalls_prefix_succ]; omega
      rw [he]
      exact ih (call + 1) _

lemma child_eval_prefix (cost : ℕ → S → ℕ)
    (child : (j : ℕ) → (s : S) → Q → QueryPlan A B R (cost j s))
    (g : A → Ω → B) (j : ℕ) (s : S) (q : Q) (ξ ζ : ℕ → Ω)
    (h : ∀ k, k < cost j s → ξ k = ζ k) :
    evalAt (fun k x => g x (ξ k)) (child j s q) 0 =
      evalAt (fun k x => g x (ζ k)) (child j s q) 0 := by
  apply evalAt_prefix_congr
  intro k hk x
  simpa only [Nat.zero_add] using congrArg (g x) (h k hk)

section MeasurableMachine
variable [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Q]
  [MeasurableSpace R] [MeasurableSpace U]

lemma measurable_machine_step (response : ℕ → S → Q → (ℕ → Ω) → R)
    (query : ℕ → U → Q) (update : ℕ → U → R → U)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) => response j w.2.1 w.1 w.2.2))
    (hq : ∀ j, Measurable (query j))
    (hu : ∀ j, Measurable (Function.uncurry (update j))) (j : ℕ) :
    Measurable (fun w : U × (S × (ℕ → Ω)) =>
      update j w.1 (response j w.2.1 (query j w.1) w.2.2)) :=
  (hu j).comp (measurable_fst.prodMk
    ((hr j).comp (((hq j).comp measurable_fst).prodMk measurable_snd)))

lemma substituted_statePlan_identDistrib (P : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    (cost : ℕ → S → ℕ) (hc : ∀ j, Measurable (cost j))
    (child : (j : ℕ) → (s : S) → Q → QueryPlan A B R (cost j s))
    (g : A → Ω → B) (query : ℕ → U → Q) (update : ℕ → U → R → U)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k)) (child j w.2.1 w.1) 0))
    (hq : ∀ j, Measurable (query j))
    (hu : ∀ j, Measurable (Function.uncurry (update j))) (N : ℕ) (state : U) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun j x => g x (w.2 j))
        (substitutePlan (fun j => cost j (w.1 j)) (fun j => child j (w.1 j))
          (statePlan query update N 0 state) 0) 0)
      (idealRun (fun j u childSample => update j u
        (evalAt (fun k x => g x (childSample.2 k)) (child j childSample.1 (query j u)) 0)) N 0 state)
      ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.infinitePi fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  let response := fun j s q (ζ : ℕ → Ω) => evalAt (fun k x => g x (ζ k)) (child j s q) 0
  let step := fun j u (sample : S × (ℕ → Ω)) => update j u (response j sample.1 (query j u) sample.2)
  have hs : ∀ j, Measurable (Function.uncurry (step j)) :=
    measurable_machine_step response query update hr hq hu
  have hd : ∀ call u s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      step call u (s, ξ) = step call u (s, ζ) := by
    intro call u s ξ ζ h
    exact congrArg (update call u) (child_eval_prefix cost child g call s (query call u) ξ ζ h)
  have hh := freshRun_identDistrib P p hc hs hd N 0 state
  convert hh using 1
  try rfl
  funext w
  have he := evalAt_substituted_statePlan cost child g query update w.1 w.2 N 0 0 state
  simp only [slotCalls, Nat.zero_add] at he
  rw [he, cursorRun_freshRun]
  simp only [Nat.zero_add]
  rfl

lemma represented_plan_substitution_identDistrib {V : Type*} [MeasurableSpace V]
    (P : Measure S) (p : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    (cost : ℕ → S → ℕ) (hc : ∀ j, Measurable (cost j))
    (child : (j : ℕ) → (s : S) → Q → QueryPlan A B R (cost j s))
    (g : A → Ω → B) (query : ℕ → U → Q) (update : ℕ → U → R → U)
    (output : U → V) (ho : Measurable output)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) =>
      evalAt (fun k x => g x (w.2.2 k)) (child j w.2.1 w.1) 0))
    (hq : ∀ j, Measurable (query j))
    (hu : ∀ j, Measurable (Function.uncurry (update j))) (N : ℕ) (state : U)
    (plan : QueryPlan Q R V N)
    (hrep : ∀ reply : ℕ → Q → R, evalAt reply plan 0 =
      output (evalAt reply (statePlan query update N 0 state) 0)) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun j x => g x (w.2 j))
        (substitutePlan (fun j => cost j (w.1 j)) (fun j => child j (w.1 j)) plan 0) 0)
      (fun samples => output (idealRun (fun j u childSample => update j u
        (evalAt (fun k x => g x (childSample.2 k)) (child j childSample.1 (query j u)) 0)) N 0 state samples))
      ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.infinitePi fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  have hh := (substituted_statePlan_identDistrib P p cost hc child g query update hr hq hu N state).comp ho
  convert hh using 1 <;> try rfl
  funext w
  have h1 := evalAt_substitutePlan (fun j x => g x (w.2 j))
    (fun j => cost j (w.1 j)) (fun j => child j (w.1 j)) plan 0 0
  have h2 := evalAt_substitutePlan (fun j x => g x (w.2 j))
    (fun j => cost j (w.1 j)) (fun j => child j (w.1 j)) (statePlan query update N 0 state) 0 0
  simp only [slotCalls, Nat.zero_add] at h1 h2
  simpa only [Function.comp_apply, h1, h2] using hrep
    (fun i q => evalAt (fun j x => g x (w.2 j)) (child i (w.1 i) q)
      (slotCalls (fun j => cost j (w.1 j)) i 0))

end MeasurableMachine
section ClippedRepresentation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clippedPlan_state_representation (reply : ℕ → E → E) (Λ D C μ : ℝ)
    (center anchor : E) (K : ℕ) :
    evalAt reply (clippedPlan Λ D C μ center anchor K) 0 =
      evalAt reply (statePlan (fun _ => Gradient.acceleratedQuery)
        (fun _ state r => HeavyTailedMarkovGradient.projectedClippedUpdate Λ D C anchor state
          (r + μ • (Gradient.acceleratedQuery state - center))) K 0 (0, anchor, anchor)) 0 := by
  rw [evalAt_statePlan]
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [clippedPlan, evalAt_castPlan, evalAt_bind, HeavyTailedMarkovGradient.advance_add]
      simp only [evalAt, StochasticGradient.advance, Nat.zero_add]
      rw [← ih]

end ClippedRepresentation

end CursorMachine

namespace PlanFamily
universe u
variable {Q R U V A B : Type u}

def terminal : QueryPlan Q R U 0 → U
  | .done u => u

def head {k : ℕ} : QueryPlan Q R U (k + 1) → Q
  | .ask q _ => q

def next {k : ℕ} : QueryPlan Q R U (k + 1) → R → QueryPlan Q R U k
  | .ask _ f => f

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace U]

def MeasurableFamily : (k : ℕ) → {A : Type u} → [MeasurableSpace A] →
    (A → QueryPlan Q R U k) → Prop
  | 0, _, _, plan => Measurable (fun a => terminal (plan a))
  | k + 1, A, _, plan => Measurable (fun a => head (plan a)) ∧
      MeasurableFamily k (fun ar : A × R => next (plan ar.1) ar.2)

lemma done [MeasurableSpace A] {f : A → U} (hf : Measurable f) :
    MeasurableFamily 0 (fun a => .done (f a) : A → QueryPlan Q R U 0) := hf

lemma ask [MeasurableSpace A] {k : ℕ} {q : A → Q}
    {rest : A × R → QueryPlan Q R U k} (hq : Measurable q)
    (hr : MeasurableFamily k rest) :
    MeasurableFamily (k + 1) (fun a => .ask (q a) (fun r => rest (a, r))) := ⟨hq, hr⟩

lemma comp [MeasurableSpace A] [MeasurableSpace B] {k : ℕ}
    {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan)
    {f : B → A} (hf : Measurable f) : MeasurableFamily k (plan ∘ f) := by
  induction k generalizing A B with
  | zero => exact hp.comp hf
  | succ k ih =>
      refine ⟨hp.1.comp hf, ?_⟩
      exact ih hp.2 ((hf.comp measurable_fst).prodMk measurable_snd)

lemma cast [MeasurableSpace A] {k m : ℕ} (h : k = m)
    {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan) :
    MeasurableFamily m (fun a => castPlan h (plan a)) := by subst m; exact hp

lemma bind [MeasurableSpace A] [MeasurableSpace V] {k m : ℕ}
    {plan : A → QueryPlan Q R U k} {rest : A × U → QueryPlan Q R V m}
    (hp : MeasurableFamily k plan) (hr : MeasurableFamily m rest) :
    MeasurableFamily (m + k) (fun a => (plan a).bind (fun u => rest (a, u))) := by
  induction k generalizing A with
  | zero =>
      have hh := comp hr (measurable_id.prodMk hp)
      convert hh using 1
      funext a
      dsimp only [Function.comp_apply, id_eq]
      cases plan a
      rfl
  | succ k ih =>
      refine ⟨?_, ?_⟩
      · convert hp.1 using 1
        funext a
        dsimp only
        cases plan a
        rfl
      · have hh := ih hp.2 (comp hr (show Measurable
            (fun w : (A × R) × U => (w.1.1, w.2)) by fun_prop))
        convert hh using 1
        funext ar
        dsimp only
        cases plan ar.1
        rfl

lemma map [MeasurableSpace A] [MeasurableSpace V] {k : ℕ}
    {plan : A → QueryPlan Q R U k} {f : A × U → V}
    (hp : MeasurableFamily k plan) (hf : Measurable f) :
    MeasurableFamily k (fun a => (plan a).map (fun u => f (a, u))) := by
  induction k generalizing A with
  | zero =>
      change Measurable (fun a => terminal ((plan a).map (fun u => f (a, u))))
      have hh := hf.comp (measurable_id.prodMk hp)
      convert hh using 1
      funext a
      dsimp only [Function.comp_apply, id_eq]
      cases plan a
      rfl
  | succ k ih =>
      refine ⟨?_, ?_⟩
      · convert hp.1 using 1
        funext a
        dsimp only
        cases plan a
        rfl
      · have hh := ih hp.2 (hf.comp (show Measurable
            (fun w : (A × R) × U => (w.1.1, w.2)) by fun_prop))
        convert hh using 1
        funext ar
        dsimp only
        cases plan ar.1
        rfl

lemma collect [MeasurableSpace A] {k : ℕ} (n : ℕ)
    {plans : A → Fin n → QueryPlan Q R U k}
    (hp : ∀ i, MeasurableFamily k (fun a => plans a i)) :
    MeasurableFamily (k * n) (fun a => collectPlans n (plans a)) := by
  induction n generalizing A with
  | zero => exact done measurable_const
  | succ n ih =>
      change MeasurableFamily (k * n + k) (fun a =>
        (plans a 0).bind (fun value => (collectPlans n (fun i => plans a i.succ)).map
          (fun values => (Fin.cases value values : Fin (n + 1) → U))))
      refine bind (rest := fun w => (collectPlans n (fun i => plans w.1 i.succ)).map
        (fun values => (Fin.cases w.2 values : Fin (n + 1) → U))) (hp 0) ?_
      refine map (plan := fun w : A × U => collectPlans n (fun i => plans w.1 i.succ)) (f := fun w : (A × U) × (Fin n → U) => (Fin.cases w.1.2 w.2 : Fin (n + 1) → U)) ?_ ?_
      · exact ih (fun i => comp (hp i.succ) measurable_fst)
      · apply Measurable.of_eval
        intro i
        cases i using Fin.cases with
        | zero => exact measurable_snd.comp measurable_fst
        | succ i => exact (measurable_pi_apply i).comp measurable_snd

lemma bind' [MeasurableSpace A] [MeasurableSpace V] {k m : ℕ}
    {plan : A → QueryPlan Q R U k} {rest : A → U → QueryPlan Q R V m}
    (hp : MeasurableFamily k plan) (hr : MeasurableFamily m (Function.uncurry rest)) :
    MeasurableFamily (m + k) (fun a => (plan a).bind (rest a)) := bind hp hr

lemma map' [MeasurableSpace A] [MeasurableSpace V] {k : ℕ}
    {plan : A → QueryPlan Q R U k} {f : A → U → V}
    (hp : MeasurableFamily k plan) (hf : Measurable (Function.uncurry f)) :
    MeasurableFamily k (fun a => (plan a).map (f a)) := map hp hf


section Concrete
variable {E X : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace X]

lemma clipped {Λ D C : X → ℝ} {center anchor : X → E} (μ : ℝ)
    (hΛ : Measurable Λ) (hD : Measurable D) (hC : Measurable C)
    (hc : Measurable center) (ha : Measurable anchor) (K : ℕ) :
    MeasurableFamily K (fun x => clippedPlan (Λ x) (D x) (C x) μ (center x) (anchor x) K) := by
  induction K with
  | zero => exact done (measurable_const.prodMk (ha.prodMk ha))
  | succ K ih =>
      apply cast _
      refine bind (rest := fun w => .ask (Gradient.acceleratedQuery w.2) (fun reply =>
        .done (HeavyTailedMarkovGradient.projectedClippedUpdate (Λ w.1) (D w.1) (C w.1)
          (anchor w.1) w.2 (reply + μ • (Gradient.acceleratedQuery w.2 - center w.1))))) ih ?_
      constructor
      · unfold head Gradient.acceleratedQuery
        fun_prop
      · apply done
        let base := fun w : (X × (ℕ × E × E)) × E => w.1.1
        let state := fun w : (X × (ℕ × E × E)) × E => w.1.2
        have hb : Measurable base := by fun_prop
        have hs : Measurable state := by fun_prop
        have hq : Measurable (fun w => Gradient.acceleratedQuery (state w)) := by
          unfold Gradient.acceleratedQuery; fun_prop
        have hr : Measurable (fun w => clip (C (base w))
            (w.2 + μ • (Gradient.acceleratedQuery (state w) - center (base w)))) :=
          StochasticEnvelopePilot.measurable_variable_clip (hC.comp hb)
            (measurable_snd.add ((hq.sub (hc.comp hb)).const_smul μ))
        have hz : Measurable (fun w => anchor (base w) + clip (D (base w))
            ((state w).2.2 - ((((state w).1 : ℝ) + 1) / 2 / Λ (base w)) •
              clip (C (base w)) (w.2 + μ • (Gradient.acceleratedQuery (state w) - center (base w))) - anchor (base w))) :=
          (ha.comp hb).add (StochasticEnvelopePilot.measurable_variable_clip (hD.comp hb)
            ((hs.snd.snd.sub ((by fun_prop : Measurable (fun w => (((state w).1 : ℝ) + 1) / 2 / Λ (base w))).smul hr)).sub (ha.comp hb)))
        unfold HeavyTailedMarkovGradient.projectedClippedUpdate
        change Measurable (fun w => ((state w).1 + 1, _, _))
        simpa only [Gradient.acceleratedQuery, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', base, state] using (hs.fst.add_const 1).prodMk (((by fun_prop : Measurable (fun w =>
          (((state w).1 : ℝ) * (((state w).1 : ℝ) + 1) / 4) /
          ((((state w).1 : ℝ) * (((state w).1 : ℝ) + 1) / 4) + (((state w).1 : ℝ) + 1) / 2))).smul hs.snd.fst).add
          ((by fun_prop : Measurable (fun w => ((((state w).1 : ℝ) + 1) / 2) /
          ((((state w).1 : ℝ) * (((state w).1 : ℝ) + 1) / 4) + (((state w).1 : ℝ) + 1) / 2))).smul hz) |>.prodMk hz)

lemma stage (L μ p s a : ℝ) {U D : X → ℝ} {center anchor : X → E}
    (hU : Measurable U) (hD : Measurable D) (hc : Measurable center)
    (ha : Measurable anchor) (K replicas : ℕ) :
    MeasurableFamily (K * (replicas + 1))
      (fun x => stagePlan L μ p s a (U x) (D x) (center x) (anchor x) K replicas) := by
  unfold stagePlan
  apply map'
  · apply collect
    intro i
    apply map'
    · apply clipped μ _ hD _ hc ha K <;> fun_prop
    · exact measurable_fst.comp measurable_snd.snd
  · exact MultiplicativeRobustEstimator.measurable_medoid.comp measurable_snd

lemma refine (L μ p s a n : ℝ) {U : X → ℝ} {center start : X → E}
    (hU : Measurable U) (hc : Measurable center) (hs : Measurable start)
    (K replicas J : ℕ) :
    MeasurableFamily (K * (replicas + 1) * J)
      (fun x => refinePlan L μ p s a (U x) n (center x) (start x) K replicas J) := by
  induction J with
  | zero => exact done hs
  | succ J ih =>
      apply cast _
      apply bind' ih
      apply map'
      · exact stage L μ p s a (hU.comp measurable_fst)
          ((hU.comp measurable_fst).div_const _) (hc.comp measurable_fst) measurable_snd K replicas
      · exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
          measurable_fst.snd measurable_snd

lemma robust {point : X → E} (hp : Measurable point) (b replicas : ℕ) :
    MeasurableFamily ((b + 1) * 8 * (replicas + 1))
      (fun x => robustPlan (point x) b replicas) := by
  unfold robustPlan
  apply map'
  · apply collect
    intro i
    apply collect
    intro j
    apply cast _
    apply collect
    intro k
    exact ⟨hp, measurable_snd⟩
  · exact (StochasticEnvelopeSampling.measurable_robustMean b replicas).comp measurable_snd

lemma pilot (L μ β : ℝ) {radius : X → ℝ} {center : X → E}
    (hR : Measurable radius) (hc : Measurable center) (b replicas N : ℕ) :
    MeasurableFamily ((b + 1) * 8 * (replicas + 1) * N)
      (fun x => pilotPlan L μ β (radius x) (center x) b replicas N) := by
  induction N with
  | zero => exact done (hc.prodMk hc)
  | succ N ih =>
      apply cast _
      apply bind' ih
      apply map'
      · apply robust _ b replicas
        unfold InexactGradient.query
        fun_prop
      · let base := fun w : (X × (E × E)) × E => w.1.1
        have hb : Measurable base := by fun_prop
        have hn : Measurable (fun w : (X × (E × E)) × E =>
            LongTails.Algorithms.StochasticEnvelopePilot.update L μ β (center (base w)) w.1.2 w.2) := by
          unfold LongTails.Algorithms.StochasticEnvelopePilot.update InexactGradient.step InexactGradient.query
          fun_prop
        exact ((hc.comp hb).add (StochasticEnvelopePilot.measurable_variable_clip (hR.comp hb)
          (hn.fst.sub (hc.comp hb)))).prodMk
          ((hc.comp hb).add (StochasticEnvelopePilot.measurable_variable_clip (hR.comp hb)
          (hn.snd.sub (hc.comp hb))))

lemma radius (L μ s β : ℝ) {center : X → E} (hc : Measurable center) (b replicas N : ℕ) :
    MeasurableFamily ((b + 1) * 8 * (replicas + 1) * (N + 1))
      (fun x => radiusPlan L μ s β (center x) b replicas N) := by
  unfold radiusPlan
  apply cast _
  apply bind' (robust hc b replicas)
  apply map'
  · apply pilot L μ β _ (hc.comp measurable_fst) b replicas N
    fun_prop
  · fun_prop

lemma approximate (L μ p s a n β : ℝ) {center : X → E} (hc : Measurable center)
    (b pilotReplicas innerReplicas N K J : ℕ) :
    MeasurableFamily ((b + 1) * 8 * (pilotReplicas + 1) * (N + 1) + K * (innerReplicas + 1) * J)
      (fun x => approximatePlan L μ p s a n β (center x) b pilotReplicas innerReplicas N K J) := by
  unfold approximatePlan
  apply cast _
  apply bind' (radius L μ s β hc b pilotReplicas N)
  exact refine L μ p s a n measurable_snd (hc.comp measurable_fst) (hc.comp measurable_fst)
    K innerReplicas J

lemma tunedApproximation (L μ p s a n : ℝ) {center : X → E} (hc : Measurable center) :
    MeasurableFamily (approximationTuning ((L + μ) / μ) p a n).calls
      (fun x => tunedApproximationPlan L μ p s a n (center x)) :=
  approximate L μ p s a n _ hc _ _ _ _ _ _

lemma debiased (v : ℝ) (cost : ℕ → ℕ)
    {plans : (ell : ℕ) → X → QueryPlan E E E (cost ell)}
    (hp : ∀ ell, MeasurableFamily (cost ell) (plans ell)) (n : ℕ) :
    MeasurableFamily (cost 0 + cost (n + 1) + cost n)
      (fun x => debiasedPlan v cost (fun ell => plans ell x) n) := by
  unfold debiasedPlan
  apply cast _
  apply bind' (hp 0)
  apply bind' (comp (hp (n + 1)) measurable_fst)
  apply map'
  · exact comp (hp n) measurable_fst.fst
  · unfold debiasedValue
    fun_prop

lemma tunedEnvelope (L μ p s a m v : ℝ) {center : X → E} (hc : Measurable center) (n : ℕ) :
    MeasurableFamily ((approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ 0)).calls +
      (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ (n + 1))).calls +
      (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ n)).calls)
      (fun x => tunedEnvelopePlan L μ p s a m v (center x) n) := by
  unfold tunedEnvelopePlan
  apply map'
  · exact debiased v _ (fun ell => tunedApproximation L μ p s a (m * (2 : ℝ) ^ ell) hc) n
  · fun_prop

end Concrete

end PlanFamily

namespace PlanFamily
universe u
variable {Q R U A : Type u}
variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace U]
section FreshLaw
variable {S Ω : Type u}

def freshEval (cost : ℕ → S → ℕ) (response : ℕ → Q → S × (ℕ → Ω) → R) :
    (k : ℕ) → QueryPlan Q R U k → ℕ → ((ℕ → S) × (ℕ → Ω)) → U
  | 0, plan, _, _ => terminal plan
  | k + 1, plan, call, w => freshEval cost response k
      (next plan (response call (head plan) (w.1 0, w.2))) (call + 1)
      ((fun j => w.1 (j + 1)), fun j => w.2 (cost call (w.1 0) + j))

def idealEval (response : ℕ → Q → S × (ℕ → Ω) → R) :
    (k : ℕ) → QueryPlan Q R U k → ℕ → (ℕ → S × (ℕ → Ω)) → U
  | 0, plan, _, _ => terminal plan
  | k + 1, plan, call, ξ => idealEval response k
      (next plan (response call (head plan) (ξ 0))) (call + 1) (fun j => ξ (j + 1))

variable [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace A]

lemma freshEval_measurable {cost : ℕ → S → ℕ} (hc : ∀ j, Measurable (cost j))
    {response : ℕ → Q → S × (ℕ → Ω) → R}
    (hr : ∀ j, Measurable (Function.uncurry (response j))) {k : ℕ}
    {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan) (call : ℕ) :
    Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) => freshEval cost response k (plan w.1) call w.2) := by
  induction k generalizing A call with
  | zero => exact hp.comp measurable_fst
  | succ k ih =>
      have hhead : Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) => (w.2.1 0, w.2.2)) := by fun_prop
      have hreply := (hr call).comp ((hp.1.comp measurable_fst).prodMk hhead)
      have ht : Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) =>
          ((fun j => w.2.1 (j + 1)), fun j => w.2.2 (cost call (w.2.1 0) + j))) :=
        (by fun_prop : Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) => fun j => w.2.1 (j + 1))).prodMk
          ((StochasticEnvelopeFreshness.measurable_seed_shift (hc call)).comp hhead)
      exact (ih hp.2 (call + 1)).comp ((measurable_fst.prodMk hreply).prodMk ht)

lemma idealEval_measurable {response : ℕ → Q → S × (ℕ → Ω) → R}
    (hr : ∀ j, Measurable (Function.uncurry (response j))) {k : ℕ}
    {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan) (call : ℕ) :
    Measurable (fun w : A × (ℕ → S × (ℕ → Ω)) => idealEval response k (plan w.1) call w.2) := by
  induction k generalizing A call with
  | zero => exact hp.comp measurable_fst
  | succ k ih =>
      exact (ih hp.2 (call + 1)).comp ((measurable_fst.prodMk
        ((hr call).comp ((hp.1.comp measurable_fst).prodMk
          ((measurable_pi_apply 0).comp measurable_snd)))).prodMk (by fun_prop))

open scoped ENNReal
open StochasticEnvelopeFreshness

lemma freshEval_lintegral (P : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {cost : ℕ → S → ℕ} (hc : ∀ j, Measurable (cost j))
    {response : ℕ → Q → S × (ℕ → Ω) → R}
    (hr : ∀ j, Measurable (Function.uncurry (response j)))
    (hd : ∀ call q s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      response call q (s, ξ) = response call q (s, ζ))
    {k : ℕ} {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan)
    (φ : U → ℝ≥0∞) (hφ : Measurable φ) (call : ℕ) (a : A) :
    (∫⁻ w, φ (freshEval cost response k (plan a) call w)
      ∂((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))) =
      ∫⁻ ξ, φ (idealEval response k (plan a) call ξ)
        ∂Measure.infinitePi (fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  induction k generalizing A call with
  | zero => simp [freshEval, idealEval]
  | succ k ih =>
      let F : R × ((ℕ → S) × (ℕ → Ω)) → ℝ≥0∞ :=
        fun w => φ (freshEval cost response k (next (plan a) w.1) (call + 1) w.2)
      have hF : Measurable F := hφ.comp ((freshEval_measurable hc hr hp.2 (call + 1)).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
      have hh := fresh_step_lintegral P p (hc call) (response call (head (plan a)))
        ((hr call).comp measurable_prodMk_left) (hd call (head (plan a))) F hF
      change (∫⁻ (w : (ℕ → S) × (ℕ → Ω)), F (response call (head (plan a)) (w.1 0, w.2),
        ((fun j => w.1 (j + 1)), fun j => w.2 (cost call (w.1 0) + j))) ∂_) = _
      rw [hh]
      have hi : ∀ sample : S × (ℕ → Ω),
          (∫⁻ tails, F (response call (head (plan a)) sample, tails)
            ∂((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))) =
          ∫⁻ ξ, φ (idealEval response k (next (plan a) (response call (head (plan a)) sample))
              (call + 1) ξ)
            ∂Measure.infinitePi (fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p)) :=
        fun sample => ih hp.2 (call + 1) (a, response call (head (plan a)) sample)
      simp only [hi]
      let R₀ := P.prod (Measure.infinitePi fun _ : ℕ => p)
      let F' : (S × (ℕ → Ω)) × (ℕ → S × (ℕ → Ω)) → ℝ≥0∞ :=
        fun w => φ (idealEval response k (next (plan a) (response call (head (plan a)) w.1)) (call + 1) w.2)
      have hF' : Measurable F' := hφ.comp ((idealEval_measurable hr hp.2 (call + 1)).comp
        ((measurable_const.prodMk ((hr call).comp (measurable_const.prodMk measurable_fst))).prodMk measurable_snd))
      have hsplit := (HeavyTailedProductProcess.head_tail_preserving R₀).lintegral_comp hF'
      rw [lintegral_prod F' hF'.aemeasurable] at hsplit
      exact hsplit.symm

lemma freshEval_map_eq (P : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {cost : ℕ → S → ℕ} (hc : ∀ j, Measurable (cost j))
    {response : ℕ → Q → S × (ℕ → Ω) → R}
    (hr : ∀ j, Measurable (Function.uncurry (response j)))
    (hd : ∀ call q s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      response call q (s, ξ) = response call q (s, ζ))
    {k : ℕ} {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan)
    (call : ℕ) (a : A) :
    ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p)).map
      (freshEval cost response k (plan a) call) =
      (Measure.infinitePi (fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p))).map
        (idealEval response k (plan a) call) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hactual : Measurable (freshEval cost response k (plan a) call) :=
    (freshEval_measurable hc hr hp call).comp measurable_prodMk_left
  have hideal : Measurable (idealEval response k (plan a) call) :=
    (idealEval_measurable hr hp call).comp measurable_prodMk_left
  rw [lintegral_map hφ hactual, lintegral_map hφ hideal]
  exact freshEval_lintegral P p hc hr hd hp φ hφ call a

lemma freshEval_identDistrib (P : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {cost : ℕ → S → ℕ} (hc : ∀ j, Measurable (cost j))
    {response : ℕ → Q → S × (ℕ → Ω) → R}
    (hr : ∀ j, Measurable (Function.uncurry (response j)))
    (hd : ∀ call q s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      response call q (s, ξ) = response call q (s, ζ))
    {k : ℕ} {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan)
    (call : ℕ) (a : A) :
    ProbabilityTheory.IdentDistrib (freshEval cost response k (plan a) call)
      (idealEval response k (plan a) call)
      ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.infinitePi (fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p))) :=
  ⟨((freshEval_measurable hc hr hp call).comp measurable_prodMk_left).aemeasurable,
    ((idealEval_measurable hr hp call).comp measurable_prodMk_left).aemeasurable,
    freshEval_map_eq P p hc hr hd hp call a⟩

end FreshLaw

section Operational
variable {S Ω C D : Type u}
open RecursiveEnvelopeExecution

omit [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace U] in
lemma substituted_eval_fresh (cost : ℕ → S → ℕ)
    (child : (j : ℕ) → (s : S) → Q → QueryPlan C D R (cost j s))
    (g : C → Ω → D) (seeds : ℕ → S) (ξ : ℕ → Ω) {k : ℕ}
    (plan : QueryPlan Q R U k) (slot raw : ℕ) :
    evalAt (fun j x => g x (ξ j))
      (substitutePlan (fun j => cost j (seeds j)) (fun j => child j (seeds j)) plan slot) raw =
      freshEval cost (fun j q w => evalAt (fun i x => g x (w.2 i)) (child j w.1 q) 0)
        k plan slot ((fun j => seeds (slot + j)), fun j => ξ (raw + j)) := by
  induction plan generalizing slot raw with
  | done value => rfl
  | @ask k query rest ih =>
      simp only [substitutePlan, slotCalls, evalAt_bind, freshEval, head, next, Nat.add_zero]
      rw [ih]
      have hc := evalAt_shift (fun j x => g x (ξ j)) (child slot (seeds slot) query) raw 0
      simp only [Nat.add_zero] at hc
      rw [hc]
      simp only [Nat.add_comm, Nat.add_left_comm]

omit [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace U] in
lemma ideal_eval_indexed (response : ℕ → Q → S × (ℕ → Ω) → R)
    (samples : ℕ → S × (ℕ → Ω)) {k : ℕ} (plan : QueryPlan Q R U k) (call : ℕ) :
    idealEval response k plan call (fun j => samples (call + j)) =
      evalAt (fun j q => response j q (samples j)) plan call := by
  induction plan generalizing call with
  | done value => rfl
  | ask query rest ih =>
      simp only [idealEval, head, next, evalAt, Nat.add_zero]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (response call query (samples call)) (call + 1)

lemma substituted_family_measurable [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace Ω]
    (cost : ℕ → S → ℕ) (hc : ∀ j, Measurable (cost j))
    (child : (j : ℕ) → (s : S) → Q → QueryPlan C D R (cost j s))
    (g : C → Ω → D)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) =>
      evalAt (fun i x => g x (w.2.2 i)) (child j w.2.1 w.1) 0))
    {k : ℕ} {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan) :
    Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) => evalAt (fun j x => g x (w.2.2 j))
      (substitutePlan (fun j => cost j (w.2.1 j)) (fun j => child j (w.2.1 j)) (plan w.1) 0) 0) := by
  have hh := freshEval_measurable (response := fun j q (w : S × (ℕ → Ω)) =>
    evalAt (fun i x => g x (w.2 i)) (child j w.1 q) 0) hc hr hp 0
  convert hh using 1
  funext w
  simpa only [Nat.zero_add] using substituted_eval_fresh cost child g w.2.1 w.2.2 (plan w.1) 0 0

lemma substituted_family_identDistrib [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure S) (p : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    (cost : ℕ → S → ℕ) (hc : ∀ j, Measurable (cost j))
    (child : (j : ℕ) → (s : S) → Q → QueryPlan C D R (cost j s))
    (g : C → Ω → D)
    (hr : ∀ j, Measurable (fun w : Q × (S × (ℕ → Ω)) =>
      evalAt (fun i x => g x (w.2.2 i)) (child j w.2.1 w.1) 0))
    {k : ℕ} {plan : A → QueryPlan Q R U k} (hp : MeasurableFamily k plan) (a : A) :
    ProbabilityTheory.IdentDistrib
      (fun w : (ℕ → S) × (ℕ → Ω) => evalAt (fun j x => g x (w.2 j))
        (substitutePlan (fun j => cost j (w.1 j)) (fun j => child j (w.1 j)) (plan a) 0) 0)
      (fun samples : ℕ → S × (ℕ → Ω) => evalAt
        (fun j q => evalAt (fun i x => g x ((samples j).2 i)) (child j (samples j).1 q) 0) (plan a) 0)
      ((Measure.infinitePi fun _ : ℕ => P).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.infinitePi (fun _ : ℕ => P.prod (Measure.infinitePi fun _ : ℕ => p))) := by
  let response := fun j q (w : S × (ℕ → Ω)) => evalAt (fun i x => g x (w.2 i)) (child j w.1 q) 0
  have hd : ∀ call q s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      response call q (s, ξ) = response call q (s, ζ) := by
    intro call q s ξ ζ h
    exact child_eval_prefix cost child g call s q ξ ζ h
  have hh := freshEval_identDistrib P p hc hr hd hp 0 a
  convert hh using 1
  · funext w
    simpa only [Nat.zero_add] using substituted_eval_fresh cost child g w.1 w.2 (plan a) 0 0
  · funext samples
    simpa only [Nat.zero_add] using (ideal_eval_indexed response samples (plan a) 0).symm

end Operational
lemma recovery {E X : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace X]
    (L μ p s a U D η : ℝ) {center : X → E} (hc : Measurable center) :
    MeasurableFamily (recoveryTuning L μ p s a U D η).calls
      (fun x => recoveryPlan L μ p s a U D η (center x)) :=
  refine L μ p s a _ measurable_const hc hc _ _ _

end PlanFamily

lemma advance_plan_unfinished (reply : ℕ → Q → R) (q0 : Q) (u0 : U) {k K : ℕ}
    (plan : QueryPlan Q R U k) (hK : K < k) (call : ℕ) :
    QueryPlan.output u0 (StochasticGradient.advance
      (fun n state => QueryPlan.update state (reply n (QueryPlan.query q0 state)))
      K call ⟨k, plan⟩) = u0 := by
  induction plan generalizing K call with
  | done value => omega
  | @ask k q rest ih =>
    cases K with
    | zero => rfl
    | succ K => exact ih (reply call q) (by omega) (call + 1)

lemma execute_capped {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (program : S → Σ k, QueryPlan Q R U k) (O : Oracle Q R) (K : ℕ) (seed : S)
    (ξ : (k : ℕ) → O.Seed k) (reply : ℕ → Q → R)
    (hr : ∀ history query, O.answer history query (ξ history.length) = reply history.length query.2) :
    execute O (algorithm law q0 u0 program) (fun _ => K) seed ξ =
      if (program seed).1 ≤ K then evalAt reply (program seed).2 0 else u0 := by
  by_cases hK : (program seed).1 ≤ K
  · rw [ite_eq_left hK]
    exact execute_complete law q0 u0 program O K seed ξ reply hr hK
  · rw [ite_eq_right hK]
    erw [StochasticGradient.execute_advance_of_answer O (algorithm law q0 u0 program)
      K seed ξ (fun k query => reply k query.2) hr]
    exact advance_plan_unfinished reply q0 u0 (program seed).2 (Nat.lt_of_not_ge hK) 0

end LongTails.Proofs.StochasticEnvelopeExecution
