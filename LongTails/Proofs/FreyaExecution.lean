import LongTails.Template
import LongTails.Proofs.FreyaConditionalCosts
import LongTails.Proofs.FreyaSerialAnalysis
import LongTails.Proofs.ExecutionHistory

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Proofs.FreyaExecution

open LongTails.Setups.FreyaModel LongTails.Proofs.FreyaCollectors
open LongTails.Proofs.FreyaConditionalCosts LongTails.Setups.FreyaIndependence
open LongTails.Algorithms.FreyaInputs LongTails.Algorithms.FreyaRandomness
open LongTails.Algorithms.FreyaCollectors
open LongTails.Algorithms.FreyaPage

noncomputable def serialInput (q : Raw) : SerialRaw where
  d := q.d
  m := q.m
  x0 := q.x0
  η := q.η
  S := q.S
  ρ := q.ρ
  K := q.K

noncomputable def pendingJobs (q : Raw) (s : State q) : Fin q.n → Option (Job q.d q.m) :=
  match s.phase with
  | .halted => fun _ => none
  | .full _ c => c.pending
  | .difference c => c.pending

noncomputable def observedPair (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : Space q.d × Space q.d :=
  let call := (batchEndCall q O seed ω batch).getD 0 - 1
  let s := trace q O seed ω call
  let reply := replyAt q O seed ω call (query q s)
  match s.phase with
  | .full _ c => (s.x, fullResult (LongTails.Algorithms.FreyaCollectors.fullUpdate c reply))
  | .difference c =>
    (s.x, s.g + differenceResult (LongTails.Algorithms.FreyaCollectors.differenceUpdate c reply))
  | .halted => (s.x, s.g)

noncomputable def transitionKernel (q : Raw) (f : Fin q.m → Space q.d → ℝ)
    (pair : Space q.d × Space q.d) (U : Set (Space q.d × Space q.d)) : ℝ≥0∞ := by
  classical
  let x := pair.1 - q.η • pair.2
  exact ENNReal.ofReal q.ρ * (if (x, gradient (objective f) x) ∈ U then 1 else 0) +
    ENNReal.ofReal (1 - q.ρ) * ((q.m : ℝ≥0∞) ^ q.S)⁻¹ *
      (∑ v : Fin q.S → Fin q.m,
        if (x, pair.2 + (q.S : ℝ)⁻¹ •
          (∑ j, (gradient (f (v j)) x - gradient (f (v j)) pair.1))) ∈ U then 1 else 0)

noncomputable def transitionDensity (q : Raw) (f : Fin q.m → Space q.d → ℝ)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (k : ℕ)
    (E : Set (Fin (k + 1) → Space q.d × Space q.d)) (U : Set (Space q.d × Space q.d))
    (z : Seed q.K × ((a : ℕ) → O.Seed a)) : ℝ≥0∞ := by
  classical
  exact if (fun j : Fin (k + 1) => observedPair q O z.1 z.2 j.val) ∈ E then
    transitionKernel q f (observedPair q O z.1 z.2 k) U else 0

theorem run_eq_executeIndexedState (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
    run q O seed ω k = executeIndexedState O (factory q) seed ω k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := executeIndexedState_eq_iterate O (factory q) seed ω (k + 1)
    erw [Function.iterate_succ_apply', ← executeIndexedState_eq_iterate] at h
    rw [h, ← ih]
    rfl

theorem run_length (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
    (run q O seed ω k).2.length = k := by
  rw [run_eq_executeIndexedState]
  exact executeIndexedState_length O (factory q) seed ω k

theorem execute_correspondence (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (N : ℕ) :
    execute O (factory q) (fun _ => N) seed ω = output q (trace q O seed ω N) := by
  let step := fun k (s : State q) => update q s (replyAt q O seed ω k (query q s))
  have h (n k : ℕ) : StochasticGradient.advance step n k (trace q O seed ω k)=
      trace q O seed ω (k+n) := by
    induction n generalizing k with
    | zero => simp only [StochasticGradient.advance,Nat.add_zero]
    | succ n ih =>
      rw [StochasticGradient.advance]
      change StochasticGradient.advance step n (k+1) (trace q O seed ω (k+1))=_
      rw [ih]
      congr 1
      omega
  erw [execute_advance_history]
  have hstep : (fun k s => (factory q).update s
      (executeAnswerAt O (factory q) seed ω k ((factory q).query s))) = step := by
    funext k s
    show (factory q).update s (O.answer (executeIndexedState O (factory q) seed ω k).2
        ((factory q).query s) (ω (executeIndexedState O (factory q) seed ω k).2.length)) =
      update q s (replyAt q O seed ω k (query q s))
    rw [← run_eq_executeIndexedState]
    rfl
  rw [hstep]
  change output q (StochasticGradient.advance step N 0 (trace q O seed ω 0))=_
  rw [h,Nat.zero_add]


theorem execute_pointOnly (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (N : ℕ) :
    execute O (pointOnly q) (fun _ => N) seed ω = (output q (trace q O seed ω N)).1 := by
  have hrun (k : ℕ) : run q O seed ω k = executeIndexedState O (pointOnly q) seed ω k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := executeIndexedState_eq_iterate O (pointOnly q) seed ω (k + 1)
      erw [Function.iterate_succ_apply', ← executeIndexedState_eq_iterate] at h
      rw [h, ← ih]
      rfl
  let step := fun k (s : State q) => update q s (replyAt q O seed ω k (query q s))
  have h (n k : ℕ) : StochasticGradient.advance step n k (trace q O seed ω k)=
      trace q O seed ω (k+n) := by
    induction n generalizing k with
    | zero => simp only [StochasticGradient.advance,Nat.add_zero]
    | succ n ih =>
      rw [StochasticGradient.advance]
      change StochasticGradient.advance step n (k+1) (trace q O seed ω (k+1))=_
      rw [ih]
      congr 1
      omega
  erw [execute_advance_history]
  have hstep : (fun k s => (pointOnly q).update s
      (executeAnswerAt O (pointOnly q) seed ω k ((pointOnly q).query s))) = step := by
    funext k s
    show (pointOnly q).update s (O.answer (executeIndexedState O (pointOnly q) seed ω k).2
        ((pointOnly q).query s) (ω (executeIndexedState O (pointOnly q) seed ω k).2.length)) =
      update q s (replyAt q O seed ω k (query q s))
    rw [← hrun]
    rfl
  rw [hstep]
  change (output q (StochasticGradient.advance step N 0 (trace q O seed ω 0))).1=_
  rw [h,Nat.zero_add]

theorem halt_stability (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (N : ℕ)
    (hhalt : (trace q O seed ω N).phase = .halted) :
    query q (trace q O seed ω N) = (0, none) ∧
      ∀ M, N ≤ M → trace q O seed ω M = trace q O seed ω N := by
  have hu (M : ℕ) (he : trace q O seed ω M=trace q O seed ω N) :
      trace q O seed ω (M+1)=trace q O seed ω N := by
    change update q (trace q O seed ω M) (replyAt q O seed ω M (query q (trace q O seed ω M)))=_
    rw [he]
    dsimp only [update]
    rw [hhalt]
  constructor
  · dsimp only [query]
    rw [hhalt]
  · intro M hM
    induction M,hM using Nat.le_induction with
    | base => rfl
    | succ M hM ih => exact hu M ih


theorem reset_correspondence (q : Raw) (s : State q) (h : s.iteration < rounds q) :
    (advance q s).iteration = s.iteration + 1 ∧ (advance q s).clock = s.clock ∧
      (advance q s).x = s.x - q.η • s.g ∧ (advance q s).g = s.g ∧
      ∀ i job, pendingJobs q (advance q s) i = some job →
        job.started = s.clock ∧ s.nextID ≤ job.id ∧ job.id < s.nextID + q.n := by
  have hjob (kind : JobKind q.d) (clock : ℝ≥0) (id : ℕ)
      (label : Option (Fin q.m)) (job : Job q.d q.m)
      (hj : dispatch kind clock id label=some job) : job.started=clock ∧ job.id=id := by
    cases label with
    | none => cases hj
    | some label =>
      have he := Option.some.inj hj
      cases he
      exact ⟨rfl,rfl⟩
  dsimp only [advance]
  rw [ite_eq_right (Nat.not_le.mpr h)]
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro i job hj
  have hb : s.nextID≤s.nextID+i.val ∧ s.nextID+i.val<s.nextID+q.n :=
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left i.isLt _⟩
  dsimp only [pendingJobs] at hj
  by_cases hr : refreshAt s.seed s.iteration=true
  · rw [ite_eq_left hr] at hj
    dsimp only [fullInitial] at hj
    obtain ⟨ht,hi⟩ := hjob _ _ _ _ job hj
    exact ⟨ht,hi ▸ hb.1,hi ▸ hb.2⟩
  · rw [ite_eq_right hr] at hj
    dsimp only [differenceInitial] at hj
    by_cases hS : q.S=0
    · rw [ite_eq_left hS] at hj
      cases hj
    · rw [ite_eq_right hS] at hj
      obtain ⟨ht,hi⟩ := hjob _ _ _ _ job hj
      exact ⟨ht,hi ▸ hb.1,hi ▸ hb.2⟩


theorem event_budget (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
    (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0, r))) :
    (trace q O seed ω (eventLimit q)).phase = .halted ∧
      ∀ N, eventLimit q ≤ N → query q (trace q O seed ω N) = (0, none) := by
  exact
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 4096 in
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
    open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
    open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    by
      classical
      have freyaPageHaltedUpdate (q : Raw) (s : State q) (reply : Reply q.d q.n)
          (h : active s = false) : update q s reply = s := by
        clear * - q s reply h
        cases hs : s.phase with
        | halted => delta update; rw [hs]
        | full first c =>
          delta active at h
          rw [hs] at h
          contradiction
        | difference c =>
          delta active at h
          rw [hs] at h
          contradiction
      have freyaDifferenceLiveStep {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
          (s : DifferenceState d m n) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i = some j ∧ reply (some r) = some (i,j.id,c,jobValue f j) ∧
              r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i')
          (ha : s.count < s.target)
          (hp : ∀ i, ∃ job, s.pending i = some job ∧ job.started ≤ s.clock ∧
            (s.clock : ℝ≥0∞) ≤ deadline τ job i ∧ job.kind = Sum.inr (s.x,s.y)) :
          ∃ i job c next,
            s.pending i = some job ∧
            differenceQuery s = some ⟨s.clock,s.pending⟩ ∧
            reply (differenceQuery s) = some (i,job.id,c,jobValue f job) ∧
            s.clock ≤ c ∧
            next.id = s.nextID ∧ next.kind = Sum.inr (s.x,s.y) ∧ next.started = c ∧
            labelAt (s.rows s.nextID) m = some next.component ∧
            differenceUpdate s (reply (differenceQuery s)) =
              {s with
                count := s.count+1
                sum := s.sum+jobValue f job
                pending := Function.update s.pending i (some next)
                clock := c
                nextID := s.nextID+1} ∧
            ∀ k, ∃ old, (Function.update s.pending i (some next)) k = some old ∧
              old.started ≤ c ∧ (c : ℝ≥0∞) ≤ deadline τ old k ∧ old.kind = Sum.inr (s.x,s.y) := by
        clear * - d m n hm hn s f τ reply hservice ha hp
        classical
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hlegal : legalRequest τ r := by
          refine ⟨?_,?_⟩
          · obtain ⟨job,hj,_⟩ := hp ⟨0,hn⟩
            exact ⟨⟨0,hn⟩,job,hj⟩
          · intro i job hj
            obtain ⟨old,hold,hs,ht,_⟩ := hp i
            have heq : job=old := Option.some.inj (hj.symm.trans hold)
            subst old
            exact ⟨hs,ht⟩
        have hquery : differenceQuery s = some r := by
          delta differenceQuery
          rw [ite_eq_right (by omega)]
          delta pendingRequest
          have hex : ∃ i, s.pending i ≠ none := by
            obtain ⟨i,job,hj⟩ := hlegal.1
            change s.pending i=some job at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,c,hjob,hreply,hclock,hdeadline⟩ := hservice r hlegal
        change s.pending i=some job at hjob
        change s.clock≤c at hclock
        obtain ⟨b,hb⟩ : ∃ b : Fin m, labelAt (s.rows s.nextID) m = some b := by
          delta labelAt
          simp (config := { iota := false }) only [hm,dite_true]
          exact ⟨_,rfl⟩
        let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
        refine ⟨i,job,c,next,hjob,hquery,?_,hclock,rfl,rfl,rfl,hb,?_,?_⟩
        · rw [hquery]; exact hreply
        · rw [hquery,hreply]
          delta differenceUpdate
          rw [ite_eq_right (by omega)]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
          delta dispatch
          rw [hb]
          rfl
        · intro k
          by_cases hk : k=i
          · subst k
            refine ⟨next,Function.update_self _ _ _,le_rfl,?_,rfl⟩
            change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞)+(2 : ℕ)*τ i
            exact le_add_of_nonneg_right zero_le
          · obtain ⟨old,hold,hstarted,_,hkind⟩ := hp k
            refine ⟨old,?_,hstarted.trans hclock,hdeadline k old hold,hkind⟩
            rw [Function.update_of_ne hk]
            exact hold
      have freyaPageDifferenceQuery (q : Raw) (s : State q)
          (c : DifferenceState q.d q.m q.n) (h : s.phase = Phase.difference c) :
          query q s = (0,differenceQuery c) := by
        clear * - q s c h
        delta query
        rw [h]
        rfl
      have freyaFullPotentialDecrease {d m n : ℕ} (hn : 0<n)
          (labels : List (Fin m)) (s : FullState d m n)
          (horig : s.original=labels) (hne : s.remaining≠[])
          (hbound : ∀ b ∈ s.remaining,b<labels.length)
          (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
          let good (s : FullState d m n) := Finset.univ.filter fun i =>
            ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
          let V (s : FullState d m n) :=
            if s.remaining=[] then 0 else n*(s.remaining.length+1)-(good s).card
          V (fullUpdate s (reply (fullQuery s)))+1≤V s := by
        clear * - d m n hn labels s horig hne hbound f τ reply hr hservice
        classical
        dsimp only
        let good (s : FullState d m n) : Finset (Fin n) := Finset.univ.filter fun i =>
          ∃ job, s.pending i = some job ∧ ∃ b ∈ s.remaining, labels[b]? = some job.component
        let V (s : FullState d m n) : ℕ :=
          if s.remaining = [] then 0 else n * (s.remaining.length + 1) - (good s).card
        have hcard (s : FullState d m n) : (good s).card ≤ n := by
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin n)
        have hselect (rem : List ℕ) (hne : rem ≠ [])
            (hbound : ∀ b ∈ rem, b < labels.length) (row : ChoiceRow) :
            ∃ b, b ∈ rem ∧ ∃ hb : b < labels.length,
              selectedLabel labels rem row = some labels[b] := by
          have hlen : rem.length ≠ 0 := by
            intro hz
            exact hne (List.length_eq_zero_iff.mp hz)
          let j : Fin rem.length := ⟨(row (rem.length-1)).val, by
            have hj := (row (rem.length-1)).isLt
            omega⟩
          have hb := hbound _ (List.get_mem rem j)
          refine ⟨rem.get j, List.get_mem rem j, hb, ?_⟩
          delta selectedLabel chooseRemaining
          rw [dite_eq_right hlen]
          dsimp only
          exact List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
        have hpositive (s : FullState d m n) (hne : s.remaining ≠ []) : 0 < V s := by
          have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
          have hc := hcard s
          have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
          dsimp only [V]
          rw [ite_eq_right hne, Nat.mul_add, Nat.mul_one]
          omega
        change V (fullUpdate s (reply (fullQuery s)))+1≤V s
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hisEmpty : s.remaining.isEmpty = false := by
          cases h : s.remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        have hquery : fullQuery s = some r := by
          delta fullQuery
          simp (config := { iota := false }) only [hisEmpty, Bool.false_eq_true, ite_false]
          delta pendingRequest
          have hex : ∃ i, s.pending i ≠ none := by
            obtain ⟨i, job, hj⟩ := hr.1
            change s.pending i = some job at hj
            exact ⟨i, by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i, job, c, hj, hreply, hc, _⟩ := hservice r hr
        change s.pending i = some job at hj
        change s.clock ≤ c at hc
        let found := s.remaining.find? fun b => decide (s.original[b]? = some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let next := dispatch (Sum.inl s.point) c s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n :=
          { s with
            remaining := rem
            sum := if found.isSome then s.sum + jobValue f job else s.sum
            pending := Function.update s.pending i next
            clock := c
            nextID := s.nextID+1 }
        have hstep : fullUpdate s (reply (fullQuery s)) = t := by
          rw [hquery, hreply]
          delta fullUpdate
          rw [hisEmpty, ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hj]
          dsimp only
          rw [ite_eq_left (And.intro rfl hc)]
        rw [hstep]
        by_cases ht : rem = []
        · have hzero : V t = 0 := by
            dsimp only [V]
            exact ite_eq_left ht
          rw [hzero]
          exact hpositive s hne
        · have hrembound : ∀ b ∈ rem, b < labels.length := by
            cases hf : found with
            | none => simpa (config := { iota := false }) only [rem, hf, Option.elim_none] using hbound
            | some b =>
              intro k hk
              exact hbound k (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem, hf, Option.elim_some] using hk))
          have hgood : i ∈ good t := by
            obtain ⟨b, hb, hbl, hlabel⟩ := hselect rem ht hrembound (s.rows s.nextID)
            simp (config := { iota := false }) only [good, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨⟨labels[b], Sum.inl s.point, c, s.nextID⟩, ?_, b, hb, ?_⟩
            · change Function.update s.pending i next i = _
              rw [Function.update_self]
              change dispatch (Sum.inl s.point) c s.nextID
                (selectedLabel s.original rem (s.rows s.nextID)) = _
              rw [horig, hlabel]
              rfl
            · exact List.getElem?_eq_some_iff.mpr ⟨hbl, rfl⟩
          have hlow : 1 ≤ (good t).card := Finset.card_pos.mpr ⟨i, hgood⟩
          have hcs := hcard s
          have hct := hcard t
          change (if rem = [] then 0 else n*(rem.length+1)-(good t).card)+1 ≤ _
          rw [ite_eq_right ht]
          change n*(rem.length+1)-(good t).card+1 ≤
            if s.remaining = [] then 0 else n*(s.remaining.length+1)-(good s).card
          rw [ite_eq_right hne]
          cases hf : found with
          | some b =>
            have hb : b ∈ s.remaining := List.mem_of_find?_eq_some hf
            have hlen : rem.length+1 = s.remaining.length := by
              dsimp only [rem]
              rw [hf]
              change (s.remaining.erase b).length+1=s.remaining.length
              have hl := List.length_erase_of_mem hb
              have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
              omega
            have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
            have hmul : n ≤ n*s.remaining.length := Nat.le_mul_of_pos_right _ hp
            rw [hlen, Nat.mul_add, Nat.mul_one]
            have calcBound (n a b c : ℕ) (hn : 0<n) (hb : b≤n) (hc : 1≤c)
                (hc' : c≤n) (ha : n≤a) : a-c+1≤a+n-b := by omega
            exact calcBound n (n*s.remaining.length) (good s).card (good t).card hn hcs hlow hct hmul
          | none =>
            have hrem : rem = s.remaining := by simp (config := { iota := false }) only [rem, hf, Option.elim_none]
            have hbad : i ∉ good s := by
              intro hi
              obtain ⟨old, hold, b, hb, hlabel⟩ := (Finset.mem_filter.mp hi).2
              have heq : old = job := Option.some.inj (hold.symm.trans hj)
              subst old
              have hfind := List.find?_eq_none.mp hf b hb
              simp (config := { iota := false }) only [horig, hlabel, decide_true, not_true_eq_false] at hfind
            have hset : good t = insert i (good s) := by
              apply Finset.ext
              intro k
              by_cases hk : k = i
              · subst k
                exact iff_of_true hgood (Finset.mem_insert_self _ _)
              · simp (config := { iota := false }) only [Finset.mem_insert, hk, false_or]
                change (k ∈ Finset.univ.filter fun k =>
                  ∃ old, Function.update s.pending i next k = some old ∧
                    ∃ b ∈ rem, labels[b]? = some old.component) ↔ _
                simp (config := { iota := false }) only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [Function.update_of_ne hk, hrem]
                simp (config := { iota := false }) only [good, Finset.mem_filter, Finset.mem_univ, true_and]
            have hcount : (good t).card = (good s).card+1 := by
              rw [hset, Finset.card_insert_of_notMem hbad]
            rw [hrem, hcount, Nat.mul_add, Nat.mul_one]
            have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
            have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
            have calcBound (n a b : ℕ) (hn : 0<n) (hb : b≤n) (ha : n≤a) :
                a+n-(b+1)+1≤a+n-b := by omega
            exact calcBound n (n*s.remaining.length) (good s).card hn hcs hmul
      have freyaFullSelect {m : ℕ} (labels : List (Fin m)) (rem : List ℕ)
          (hne : rem≠[]) (hbound : ∀ b ∈ rem,b<labels.length) (row : ChoiceRow) :
          ∃ b, b ∈ rem ∧ ∃ hb : b<labels.length, selectedLabel labels rem row=some labels[b] := by
        clear * - m labels rem hne hbound row
        have hlen : rem.length≠0 := by intro hz; exact hne (List.length_eq_zero_iff.mp hz)
        let j : Fin rem.length := ⟨(row (rem.length-1)).val,by
          have hj := (row (rem.length-1)).isLt
          omega⟩
        have hb := hbound _ (List.get_mem rem j)
        refine ⟨rem.get j,List.get_mem rem j,hb,?_⟩
        delta selectedLabel chooseRemaining
        rw [dite_eq_right hlen]
        dsimp only
        exact List.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩
      have freyaFullSafeUpdate {d m n : ℕ} (s : FullState d m n)
          (hne : s.remaining≠[]) (hbound : ∀ b ∈ s.remaining,b<s.original.length)
          (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
          let t := fullUpdate s (reply (fullQuery s))
          t.original=s.original ∧ (∀ b ∈ t.remaining,b<t.original.length) ∧
            (t.remaining≠[] → legalRequest τ ⟨t.clock,t.pending⟩) := by
        clear * - d m n s hne hbound f τ reply hr hservice freyaFullSelect
        classical
        have hisEmpty : s.remaining.isEmpty=false := by
          cases h : s.remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hquery : fullQuery s=some r := by
          delta fullQuery
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          delta pendingRequest
          have hex : ∃ i,s.pending i≠none := by
            obtain ⟨i,job,hj⟩ := hr.1
            change s.pending i=some job at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,time,hjob,hreply,hclock,hdeadline⟩ := hservice r hr
        change s.pending i=some job at hjob
        change s.clock≤time at hclock
        let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let next := dispatch (Sum.inl s.point) time s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n :=
          {s with
            remaining := rem
            sum := if found.isSome then s.sum+jobValue f job else s.sum
            pending := Function.update s.pending i next
            clock := time
            nextID := s.nextID+1}
        have ht : fullUpdate s (reply (fullQuery s))=t := by
          rw [hquery,hreply]
          delta fullUpdate
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
        have hb : ∀ b ∈ rem,b<s.original.length := by
          cases hf : found with
          | none => simpa (config := { iota := false }) only [rem,hf,Option.elim_none] using hbound
          | some a =>
            intro b h
            exact hbound b (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem,hf,Option.elim_some] using h))
        dsimp only
        rw [ht]
        refine ⟨rfl,hb,?_⟩
        intro htne
        obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect s.original rem htne hb (s.rows s.nextID)
        let new : Job d m := ⟨s.original[b],Sum.inl s.point,time,s.nextID⟩
        have hnew : next=some new := by
          dsimp only [next]
          rw [hlabel]
          rfl
        refine ⟨⟨i,new,?_⟩,?_⟩
        · change Function.update s.pending i next i=some new
          rw [Function.update_self,hnew]
        · intro k old hold
          change Function.update s.pending i next k=some old at hold
          by_cases hk : k=i
          · subst k
            rw [Function.update_self,hnew] at hold
            have heq : new=old := Option.some.inj hold
            subst old
            refine ⟨le_rfl,?_⟩
            exact le_add_of_nonneg_right zero_le
          · rw [Function.update_of_ne hk] at hold
            exact ⟨((hr.2 k old hold).1).trans hclock,hdeadline k old hold⟩
      have freyaFullInitialSafe {d m n : ℕ} (hn : 0<n) (labels : List (Fin m))
          (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow)
          (firstID : ℕ) (τ : Fin n → ℝ≥0∞) :
          let s := fullInitial n labels x clock rows firstID
          s.remaining≠[] ∧ (∀ b ∈ s.remaining,b<s.original.length) ∧
            legalRequest τ ⟨s.clock,s.pending⟩ := by
        clear * - d m n hn labels hne x clock rows firstID τ freyaFullSelect
        classical
        let s := fullInitial n labels x clock rows firstID
        have hrem : (List.range labels.length)≠[] := by
          intro h
          have := congrArg List.length h
          simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
          exact hne (List.length_eq_zero_iff.mp this)
        have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
        refine ⟨hrem,hbound,?_,?_⟩
        · let i : Fin n := ⟨0,hn⟩
          obtain ⟨b,_,hb,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
          refine ⟨i,⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_⟩
          change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
          rw [hlabel]
          rfl
        · intro i job hj
          change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=some job at hj
          delta dispatch at hj
          obtain ⟨b,_,heq⟩ := Option.map_eq_some_iff.mp hj
          cases heq
          exact ⟨le_rfl,le_add_of_nonneg_right zero_le⟩
      have freyaFullInitialPotential {d m n : ℕ} (labels : List (Fin m))
          (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
          let good (s : FullState d m n) := Finset.univ.filter fun i =>
            ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
          let V (s : FullState d m n) :=
            if s.remaining=[] then 0 else n*(s.remaining.length+1)-(good s).card
          V (fullInitial n labels x clock rows firstID) ≤ n*labels.length := by
        clear * - d m n labels hne x clock rows firstID freyaFullSelect
        classical
        let s := fullInitial n labels x clock rows firstID
        let good (s : FullState d m n) := Finset.univ.filter fun i =>
          ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
        have hrem : (List.range labels.length)≠[] := by
          intro h
          have := congrArg List.length h
          simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
          exact hne (List.length_eq_zero_iff.mp this)
        have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
        have hg : good s=Finset.univ := by
          apply Finset.ext
          intro i
          simp (config := { iota := false }) only [good,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
          obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
          refine ⟨⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_,b,hbr,?_⟩
          · change dispatch (Sum.inl x) clock (firstID+i.val)
              (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
            rw [hlabel]
            rfl
          · exact List.getElem?_eq_some_iff.mpr ⟨hbl,rfl⟩
        change (if List.range labels.length=[] then 0 else
          n*((List.range labels.length).length+1)-(good s).card)≤n*labels.length
        rw [ite_eq_right hrem,hg,Finset.card_fin,List.length_range,Nat.mul_add,Nat.mul_one]
        omega
      have freyaDifferenceInitialSafe {d m n : ℕ} (hm : 0<m) (S : ℕ) (hS : 0<S)
          (x y : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ)
          (τ : Fin n → ℝ≥0∞) :
          let c : DifferenceState d m n := differenceInitial n S x y clock rows firstID
          ∀ i, ∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
        clear * - d m n hm S hS x y clock rows firstID τ
        dsimp only
        intro i
        obtain ⟨b,hb⟩ : ∃ b : Fin m,labelAt (rows (firstID+i.val)) m=some b := by
          delta labelAt
          simp (config := { iota := false }) only [hm,dite_true]
          exact ⟨_,rfl⟩
        refine ⟨⟨b,Sum.inr (x,y),clock,firstID+i.val⟩,?_,le_rfl,?_,rfl⟩
        · change (if S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
            (labelAt (rows (firstID+i.val)) m))=_
          rw [ite_eq_right (by omega),hb]
          rfl
        · exact le_add_of_nonneg_right zero_le
      have freyaPageFullQuery (q : Raw) (s : State q) (first : Bool)
          (c : FullState q.d q.m q.n) (h : s.phase=Phase.full first c) :
          query q s=(0,fullQuery c) := by
        clear * - q s first c h
        delta query
        rw [h]
        rfl
      have freyaPagePhaseSafety (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          let Safe := fun s : State q =>
            (∀ first c,s.phase=Phase.full first c →
              c.original.length=q.m ∧ c.remaining≠[] ∧
              (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
            (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
              ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
                (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
            s.iteration≤rounds q
          ∀ k,Safe (trace q O seed ω k) := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaDifferenceLiveStep freyaPageDifferenceQuery freyaFullSafeUpdate freyaFullInitialSafe freyaDifferenceInitialSafe freyaPageFullQuery
        classical
        let Safe := fun s : State q =>
            (∀ first c,s.phase=Phase.full first c →
              c.original.length=q.m ∧ c.remaining≠[] ∧
              (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
            (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
              ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
                (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
            s.iteration≤rounds q
        change ∀ k,Safe (trace q O seed ω k)
        have hfull (s : State q) (first : Bool) (c : FullState q.d q.m q.n)
            (hp : s.phase=Phase.full first c) (h1 : c.original.length=q.m) (h2 : c.remaining≠[])
            (h3 : ∀ b ∈ c.remaining,b<c.original.length)
            (h4 : legalRequest τ ⟨c.clock,c.pending⟩) (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first' c' he
            rw [hp] at he
            cases he
            exact ⟨h1,h2,h3,h4⟩
          · intro c' he
            rw [hp] at he
            cases he
        have hdiff (s : State q) (c : DifferenceState q.d q.m q.n)
            (hp : s.phase=Phase.difference c) (h1 : c.target=q.S) (h2 : c.count<c.target)
            (h3 : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y))
            (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first c' he
            rw [hp] at he
            cases he
          · intro c' he
            rw [hp] at he
            cases he
            exact ⟨h1,h2,h3⟩
        have hhalt (s : State q) (hp : s.phase=Phase.halted) (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first c he; rw [hp] at he; cases he
          · intro c he; rw [hp] at he; cases he
        have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
          intro he
          have hh := congrArg List.length he
          simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
          omega
        have hadvance (s : State q) (hi : s.iteration≤rounds q) : Safe (advance q s) := by
          delta advance
          split
          · exact hhalt _ rfl hi
          · rename_i hlt
            dsimp only
            by_cases hrefresh : refreshAt s.seed s.iteration=true
            · rw [ite_eq_left hrefresh]
              have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels
                (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID τ
              apply hfull _ false _ rfl (List.length_ofFn) hf.1 hf.2.1 hf.2.2
              dsimp only
              omega
            · rw [ite_eq_right hrefresh]
              apply hdiff _ _ rfl rfl hS
                (freyaDifferenceInitialSafe hm q.S hS _ _ _ _ _ τ)
              dsimp only
              omega
        have hinit : Safe (initial q seed) := by
          have hp : (initial q seed).phase=Phase.full true
              (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
            delta initial
            dsimp only
            rw [ite_eq_right (by omega)]
          have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels q.x0 0 (seed.1 0) 0 τ
          exact hfull _ true _ hp (List.length_ofFn) hf.1 hf.2.1 hf.2.2 (Nat.zero_le _)
        intro k
        induction k with
        | zero => exact hinit
        | succ k ih =>
          let s := trace q O seed ω k
          change Safe s at ih
          change Safe (update q s (replyAt q O seed ω k (query q s)))
          cases hs : s.phase with
          | halted =>
            have hu : update q s (replyAt q O seed ω k (query q s))=s := by delta update; rw [hs]
            rw [hu]
            exact ih
          | full first c =>
            obtain ⟨hlen,hne,hb,hl⟩ := ih.1 first c hs
            have hquery := freyaPageFullQuery q s first c hs
            rw [hquery]
            let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
            have ht := freyaFullSafeUpdate c hne hb f τ (fun r => replyAt q O seed ω k (0,r)) hl (hservice k).2
            change t.original=c.original ∧ _ at ht
            delta update
            rw [hs]
            dsimp only
            change Safe (if t.remaining.isEmpty then advance q _ else _)
            by_cases he : t.remaining.isEmpty=true
            · rw [ite_eq_left he]
              apply hadvance
              exact ih.2.2
            · rw [ite_eq_right he]
              have htne : t.remaining≠[] := by intro hz; apply he; rw [hz]; rfl
              exact hfull _ first t rfl (ht.1 ▸ hlen) htne ht.2.1 (ht.2.2 htne) ih.2.2
          | difference c =>
            obtain ⟨htarget,hcount,hp⟩ := ih.2.1 c hs
            have hquery := freyaPageDifferenceQuery q s c hs
            rw [hquery]
            obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,hpn⟩ :=
              freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hp
            delta update
            rw [hs]
            dsimp only
            rw [ht]
            dsimp only
            by_cases he : c.target≤c.count+1
            · rw [ite_eq_left he]
              apply hadvance
              exact ih.2.2
            · rw [ite_eq_right he]
              refine hdiff _ _ rfl ?_ ?_ ?_ ?_
              · exact htarget
              · change c.count+1<c.target
                omega
              · exact hpn
              · exact ih.2.2
      have freyaPageEventBudget (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          (trace q O seed ω (eventLimit q)).phase=Phase.halted ∧
            ∀ N,eventLimit q≤N → query q (trace q O seed ω N)=(0,none) := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaPageHaltedUpdate freyaDifferenceLiveStep freyaPageDifferenceQuery freyaFullPotentialDecrease freyaFullSafeUpdate freyaFullInitialPotential freyaPageFullQuery freyaPagePhaseSafety
        classical
        let M := max (q.n*q.m) q.S
        let fullV := fun c : FullState q.d q.m q.n =>
          if c.remaining=[] then 0 else q.n*(c.remaining.length+1)-
            (Finset.univ.filter fun i => ∃ job,c.pending i=some job ∧
              ∃ b ∈ c.remaining,c.original[b]?=some job.component).card
        let R : State q → ℕ := fun s => s.phase.casesOn
          (fun _ c => (rounds q-s.iteration)*M+fullV c)
          (fun c => (rounds q-s.iteration)*M+(c.target-c.count)) 0
        have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
          intro he
          have hh := congrArg List.length he
          simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
          omega
        have hinitV (x : Space q.d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
            fullV (fullInitial q.n (List.ofFn id) x clock rows firstID)≤q.n*q.m := by
          have hh := freyaFullInitialPotential (n:=q.n) (List.ofFn id) hlabels x clock rows firstID
          dsimp only [fullV,fullInitial] at hh ⊢
          simpa (config := { iota := false }) only [List.length_ofFn] using hh
        have hadvance (s : State q) (hi : s.iteration≤rounds q) :
            R (advance q s)≤(rounds q-s.iteration)*M := by
          delta advance
          split
          · exact Nat.zero_le _
          · rename_i hlt
            dsimp only
            by_cases hrefresh : refreshAt s.seed s.iteration=true
            · rw [ite_eq_left hrefresh]
              change (rounds q-(s.iteration+1))*M+
                fullV (fullInitial q.n (List.ofFn id) (s.x-q.η • s.g) s.clock
                  (s.seed.1 (s.iteration+1)) s.nextID)≤(rounds q-s.iteration)*M
              have hb := (hinitV (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID).trans
                (le_max_left (q.n*q.m) q.S)
              have hsub : rounds q-s.iteration=(rounds q-(s.iteration+1))+1 := by omega
              rw [hsub,Nat.add_mul,Nat.one_mul]
              simpa (config := { iota := false }) only [Nat.sub_zero] using Nat.add_le_add_left hb ((rounds q-(s.iteration+1))*M)
            · rw [ite_eq_right hrefresh]
              change (rounds q-(s.iteration+1))*M+(q.S-0)≤(rounds q-s.iteration)*M
              have hb : q.S≤M := le_max_right _ _
              have hsub : rounds q-s.iteration=(rounds q-(s.iteration+1))+1 := by omega
              rw [hsub,Nat.add_mul,Nat.one_mul]
              simpa (config := { iota := false }) only [Nat.sub_zero] using Nat.add_le_add_left hb ((rounds q-(s.iteration+1))*M)
        have hsafe := freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice
        have hdec (k : ℕ) (ha : active (trace q O seed ω k)=true) :
            R (trace q O seed ω (k+1))+1≤R (trace q O seed ω k) := by
          let s := trace q O seed ω k
          have hi := hsafe k
          change R (update q s (replyAt q O seed ω k (query q s)))+1≤R s
          cases hs : s.phase with
          | halted =>
            change active s=true at ha
            delta active at ha
            rw [hs] at ha
            contradiction
          | full first c =>
            obtain ⟨_,hne,hbound,hlegal⟩ := hi.1 first c hs
            have hquery := freyaPageFullQuery q s first c hs
            rw [hquery]
            let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
            have ht := freyaFullSafeUpdate c hne hbound f τ
              (fun r => replyAt q O seed ω k (0,r)) hlegal (hservice k).2
            change t.original=c.original ∧ _ at ht
            have hd := freyaFullPotentialDecrease hn c.original c rfl hne hbound f τ
              (fun r => replyAt q O seed ω k (0,r)) hlegal (hservice k).2
            have hV : fullV t+1≤fullV c := by
              dsimp only [fullV]
              rw [ht.1]
              exact hd
            delta update
            rw [hs]
            dsimp only
            change R (if t.remaining.isEmpty then advance q _ else _)+1≤R s
            by_cases he : t.remaining.isEmpty=true
            · rw [ite_eq_left he]
              have hb := hadvance
                {s with clock:=t.clock,nextID:=t.nextID,phase:=Phase.full first t,g:=fullResult t} hi.2.2
              change _≤(rounds q-s.iteration)*M at hb
              have hr : R s=(rounds q-s.iteration)*M+fullV c := by dsimp only [R]; rw [hs]
              rw [hr]
              change R (advance q {s with
                clock:=t.clock
                nextID:=t.nextID
                phase:=Phase.full first t
                g:=fullResult t})+1≤(rounds q-s.iteration)*M+fullV c
              exact (Nat.add_le_add_right hb 1).trans
                (Nat.add_le_add_left ((Nat.succ_le_succ (Nat.zero_le _)).trans hV) _)
            · rw [ite_eq_right he]
              have hr : R s=(rounds q-s.iteration)*M+fullV c := by dsimp only [R]; rw [hs]
              rw [hr]
              change (rounds q-s.iteration)*M+fullV t+1≤_
              simpa (config := { iota := false }) only [Nat.add_assoc] using Nat.add_le_add_left hV ((rounds q-s.iteration)*M)
          | difference c =>
            obtain ⟨_,hcount,hpending⟩ := hi.2.1 c hs
            have hquery := freyaPageDifferenceQuery q s c hs
            rw [hquery]
            obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,_⟩ := freyaDifferenceLiveStep hm hn c f τ
              (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hpending
            have hr : R s=(rounds q-s.iteration)*M+(c.target-c.count) := by dsimp only [R]; rw [hs]
            rw [hr]
            delta update
            rw [hs]
            dsimp only
            rw [ht]
            dsimp only
            by_cases he : c.target≤c.count+1
            · rw [ite_eq_left he]
              let t : DifferenceState q.d q.m q.n :=
                {c with
                  count:=c.count+1
                  sum:=c.sum+jobValue f job
                  pending:=Function.update c.pending i (some next)
                  clock:=time
                  nextID:=c.nextID+1}
              have hb := hadvance {s with
                clock:=time
                nextID:=c.nextID+1
                phase:=Phase.difference t
                g:=s.g+differenceResult t} hi.2.2
              change R (advance q {s with
                clock:=time
                nextID:=c.nextID+1
                phase:=Phase.difference t
                g:=s.g+differenceResult t})+1≤_
              apply (Nat.add_le_add_right hb 1).trans
              change (rounds q-s.iteration)*M+1≤_
              omega
            · rw [ite_eq_right he]
              change (rounds q-s.iteration)*M+(c.target-(c.count+1))+1≤_
              omega
        have hbound : ∀ k,active (trace q O seed ω k)=true →
            k+R (trace q O seed ω k)≤R (initial q seed) := by
          intro k
          induction k with
          | zero =>
            intro _
            have ht : trace q O seed ω 0=initial q seed := by rfl'
            rw [ht,Nat.zero_add]
          | succ k ih =>
            intro ha
            have hprev : active (trace q O seed ω k)=true := by
              by_contra he
              have hf : active (trace q O seed ω k)=false := Bool.eq_false_of_not_eq_true he
              have hh := freyaPageHaltedUpdate q (trace q O seed ω k)
                (replyAt q O seed ω k (query q (trace q O seed ω k))) hf
              change trace q O seed ω (k+1)=trace q O seed ω k at hh
              rw [hh,hf] at ha
              contradiction
            have hd := hdec k hprev
            have hb := ih hprev
            have calcBound (k next current total : ℕ) (hd : next+1≤current) (hb : k+current≤total) :
                k+1+next≤total := by omega
            exact calcBound k _ _ _ hd hb
        have hrounds : rounds q≤q.K := by delta rounds; split <;> omega
        have hinitBound : R (initial q seed)≤eventLimit q := by
          have hp : (initial q seed).phase=Phase.full true
              (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
            delta initial
            dsimp only
            rw [ite_eq_right (by omega)]
          dsimp only [R]
          rw [hp]
          change (rounds q-0)*M+fullV (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))≤_
          have hv := hinitV q.x0 0 (seed.1 0) 0
          have hm := Nat.mul_le_mul_right M hrounds
          change _≤q.n*q.m+q.K*M
          rw [Nat.sub_zero]
          exact (Nat.add_le_add hm hv).trans_eq (Nat.add_comm _ _)

        have hhalt : (trace q O seed ω (eventLimit q)).phase=Phase.halted := by
          let s := trace q O seed ω (eventLimit q)
          have hi := hsafe (eventLimit q)
          cases hs : s.phase with
          | halted => rfl
          | full first c =>
            have ha : active s=true := by delta active; rw [hs]
            have hb := (hbound (eventLimit q) ha).trans hinitBound
            obtain ⟨_,hne,_,_⟩ := hi.1 first c hs
            have hlen : 0<c.remaining.length := List.length_pos_iff.mpr hne
            have hcard : (Finset.univ.filter fun i => ∃ job,c.pending i=some job ∧
                ∃ b ∈ c.remaining,c.original[b]?=some job.component).card≤q.n := by
              exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin q.n)
            have hmul : q.n≤q.n*c.remaining.length := Nat.le_mul_of_pos_right _ hlen
            have hp : 0<fullV c := by
              dsimp only [fullV]
              rw [ite_eq_right hne,Nat.mul_add,Nat.mul_one]
              omega
            change eventLimit q+R s≤eventLimit q at hb
            dsimp only [R] at hb
            rw [hs] at hb
            dsimp only at hb
            have calcBound (p a b : ℕ) (hp : 0<p) (hb : a+(b+p)≤a) : False := by omega
            exact (calcBound _ _ _ hp hb).elim
          | difference c =>
            have ha : active s=true := by delta active; rw [hs]
            have hb := (hbound (eventLimit q) ha).trans hinitBound
            have hc := (hi.2.1 c hs).2.1
            change eventLimit q+R s≤eventLimit q at hb
            dsimp only [R] at hb
            rw [hs] at hb
            dsimp only at hb
            omega
        refine ⟨hhalt,?_⟩
        have hstable : ∀ N,eventLimit q≤N → trace q O seed ω N=trace q O seed ω (eventLimit q) := by
          intro N hN
          induction N,hN using Nat.le_induction with
          | base => rfl
          | succ N hN ih =>
            change update q (trace q O seed ω N) (replyAt q O seed ω N (query q (trace q O seed ω N)))=_
            rw [ih]
            delta update
            rw [hhalt]
        intro N hN
        rw [hstable N hN]
        delta query
        rw [hhalt]
      exact freyaPageEventBudget q hm hn hS hK f τ O seed ω hservice


theorem prefix_output_law (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
    (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0, r)))
    (N : ℕ) (hN : eventLimit q ≤ N) :
    (execute O (literal q) (fun _ => N) seed ω).1 =
        (execute O (LongTails.Algorithms.FreyaPage.«prefix» q) (fun _ => N) seed ω).1 ∧
      (execute O (LongTails.Algorithms.FreyaPage.«prefix» q) (fun _ => N) seed ω).2 ≤
        (execute O (literal q) (fun _ => N) seed ω).2 := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 4096 in
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    classical
    have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
      clear * - q s

      delta advance
      split <;> rfl
    have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
        (update q s reply).seed = s.seed := by
      clear * - q s reply freyaPageAdvanceSeed

      delta update
      cases hs : s.phase with
      | halted => rfl
      | full first c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
      | difference c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
    have freyaPageTraceSeed (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
        (trace q O seed ω k).seed = seed := by
      clear * - q O seed ω k freyaPageUpdateSeed

      induction k with
      | zero => rfl
      | succ k ih =>
        change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
        rw [freyaPageUpdateSeed,ih]
    have freyaPageHaltedUpdate (q : Raw) (s : State q) (reply : Reply q.d q.n)
        (h : active s = false) : update q s reply = s := by
      clear * - q s reply h

      cases hs : s.phase with
      | halted => delta update; rw [hs]
      | full first c =>
        delta active at h
        rw [hs] at h
        contradiction
      | difference c =>
        delta active at h
        rw [hs] at h
        contradiction
    let freyaClockConsistent {q : Raw} (s : State q) : Prop :=
      s.phase.casesOn (fun _ c => s.clock=c.clock) (fun c => s.clock=c.clock) True
    have freyaAdvanceClock (q : Raw) (s : State q) : (advance q s).clock=s.clock := by
      clear * - q s

      delta advance
      split
      · rfl
      · rfl
    have freyaAdvanceClockConsistent (q : Raw) (s : State q) : freyaClockConsistent (advance q s) := by
      clear * - q s freyaClockConsistent

      delta advance
      split
      · exact True.intro
      · dsimp only [freyaClockConsistent]
        split <;> rfl
    have freyaInitialClockConsistent (q : Raw) (seed : Seed q.K) : freyaClockConsistent (initial q seed) := by
      clear * - q seed freyaClockConsistent

      dsimp only [freyaClockConsistent,initial]
      split
      · exact True.intro
      · rfl
    have freyaUpdateClockConsistent (q : Raw) (s : State q) (r : Reply q.d q.n)
        (h : freyaClockConsistent s) : freyaClockConsistent (update q s r) := by
      clear * - q s r h freyaClockConsistent freyaAdvanceClockConsistent

      delta update
      cases hs : s.phase with
      | halted => exact h
      | full first c =>
        dsimp only
        split
        · exact freyaAdvanceClockConsistent q _
        · rfl
      | difference c =>
        dsimp only
        split
        · exact freyaAdvanceClockConsistent q _
        · rfl
    have freyaTraceClockConsistent (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
        freyaClockConsistent (trace q O seed ω k) := by
      clear * - q O seed ω k freyaClockConsistent freyaInitialClockConsistent freyaUpdateClockConsistent

      induction k with
      | zero => exact freyaInitialClockConsistent q seed
      | succ k ih => exact freyaUpdateClockConsistent q _ _ ih
    let freyaPrefixState (q : Raw) (s : State {q with «prefix»:=false}) : State {q with «prefix»:=true} :=
      ⟨s.seed,s.iteration,s.x,s.g,s.selected,s.clock,s.nextID,s.phase⟩
    let freyaPrefixRelation (q : Raw) (s : State {q with «prefix»:=false})
        (t : State {q with «prefix»:=true}) : Prop :=
      t=freyaPrefixState q s ∨
        t.phase=.halted ∧ q.K≤s.iteration ∧ s.selected=t.selected ∧ t.clock≤s.clock
    have freyaPrefixQuery (q : Raw) (s : State {q with «prefix»:=false}) :
        query {q with «prefix»:=true} (freyaPrefixState q s)=query {q with «prefix»:=false} s := by
      clear * - q s freyaPrefixState

      dsimp only [query,freyaPrefixState]
      cases h : s.phase <;> rfl
    have freyaFullClockMono {d m n : ℕ} (s : FullState d m n) (r : Reply d n) :
        s.clock≤(fullUpdate s r).clock := by
      clear * - d m n s r

      classical
      dsimp only [fullUpdate]
      split
      · exact le_rfl
      · cases r with
        | none => exact le_rfl
        | some r =>
          rcases r with ⟨i,k,t,v⟩
          dsimp only
          cases s.pending i with
          | none => exact le_rfl
          | some job =>
            dsimp only
            split
            · rename_i h
              exact h.2
            · exact le_rfl
    have freyaDifferenceClockMono {d m n : ℕ} (s : DifferenceState d m n) (r : Reply d n) :
        s.clock≤(differenceUpdate s r).clock := by
      clear * - d m n s r

      classical
      dsimp only [differenceUpdate]
      split
      · exact le_rfl
      · cases r with
        | none => exact le_rfl
        | some r =>
          rcases r with ⟨i,k,t,v⟩
          dsimp only
          cases s.pending i with
          | none => exact le_rfl
          | some job =>
            dsimp only
            split
            · rename_i h
              exact h.2
            · exact le_rfl
    have freyaUpdateClockMono (q : Raw) (s : State q) (r : Reply q.d q.n)
        (hs : freyaClockConsistent s) : s.clock≤(update q s r).clock := by
      clear * - q s r hs freyaClockConsistent freyaAdvanceClock freyaFullClockMono freyaDifferenceClockMono

      dsimp only [update]
      cases hp : s.phase with
      | halted => exact le_rfl
      | full first c =>
        have he : s.clock=c.clock := by simpa (config := { iota := false }) only [freyaClockConsistent,hp] using hs
        dsimp only
        split
        · rw [freyaAdvanceClock]
          exact he ▸ freyaFullClockMono c r
        · exact he ▸ freyaFullClockMono c r
      | difference c =>
        have he : s.clock=c.clock := by simpa (config := { iota := false }) only [freyaClockConsistent,hp] using hs
        dsimp only
        split
        · rw [freyaAdvanceClock]
          exact he ▸ freyaDifferenceClockMono c r
        · exact he ▸ freyaDifferenceClockMono c r
    have freyaAdvancePrefixRelation (q : Raw) (s : State {q with «prefix»:=false})
        (hindex : (outputIndex s.seed).val<q.K) :
        freyaPrefixRelation q (advance {q with «prefix»:=false} s)
          (advance {q with «prefix»:=true} (freyaPrefixState q s)) := by
      clear * - q s hindex freyaPrefixState freyaPrefixRelation

      classical
      by_cases hs : q.K≤s.iteration
      · left
        dsimp only [advance,rounds,freyaPrefixState]
        simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true]
        rw [ite_eq_left hs,ite_eq_left (show q.K-1≤s.iteration by omega)]
      · by_cases hp : q.K-1≤s.iteration
        · right
          have he : s.iteration+1=q.K := by omega
          have hi : ¬(outputIndex s.seed).val=s.iteration+1 := by omega
          dsimp only [advance,rounds,freyaPrefixState]
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true]
          rw [ite_eq_right hs,ite_eq_left hp]
          dsimp only
          rw [ite_eq_right hi]
          exact ⟨rfl,by omega,rfl,le_rfl⟩
        · left
          dsimp only [advance,rounds,freyaPrefixState]
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true]
          rw [ite_eq_right hs,ite_eq_right hp]
    have freyaPrefixSameUpdate (q : Raw) (s : State {q with «prefix»:=false})
        (r : Reply q.d q.n) (hindex : (outputIndex s.seed).val<q.K) :
        freyaPrefixRelation q (update {q with «prefix»:=false} s r)
          (update {q with «prefix»:=true} (freyaPrefixState q s) r) := by
      clear * - q s r hindex freyaPrefixState freyaPrefixRelation freyaAdvancePrefixRelation

      dsimp only [update,freyaPrefixState]
      cases hp : s.phase with
      | halted =>
        left
        dsimp only [freyaPrefixState]
        rw [hp]
      | full first c =>
        dsimp only
        split
        · exact freyaAdvancePrefixRelation q
            {s with
              g := fullResult (fullUpdate c r)
              clock := (fullUpdate c r).clock
              nextID := (fullUpdate c r).nextID
              phase := .full first (fullUpdate c r)} hindex
        · exact Or.inl rfl
      | difference c =>
        dsimp only
        split
        · exact freyaAdvancePrefixRelation q
            {s with
              g := s.g+differenceResult (differenceUpdate c r)
              clock := (differenceUpdate c r).clock
              nextID := (differenceUpdate c r).nextID
              phase := .difference (differenceUpdate c r)} hindex
        · exact Or.inl rfl
    have freyaAfterFinalUpdate (q : Raw) (s : State {q with «prefix»:=false})
        (r : Reply q.d q.n) (h : q.K≤s.iteration) :
        q.K≤(update {q with «prefix»:=false} s r).iteration ∧
          (update {q with «prefix»:=false} s r).selected=s.selected := by
      clear * - q s r h

      dsimp only [update]
      cases hp : s.phase with
      | halted => exact ⟨h,rfl⟩
      | full first c =>
        dsimp only
        split
        · dsimp only [advance,rounds]
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false]
          rw [ite_eq_left h]
          exact ⟨h,rfl⟩
        · exact ⟨h,rfl⟩
      | difference c =>
        dsimp only
        split
        · dsimp only [advance,rounds]
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false]
          rw [ite_eq_left h]
          exact ⟨h,rfl⟩
        · exact ⟨h,rfl⟩
    have freyaPrefixTraceRelation (q : Raw) (hK : 0<q.K)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (N : ℕ) :
        freyaPrefixRelation q (trace {q with «prefix»:=false} O seed ω N)
          (trace {q with «prefix»:=true} O seed ω N) := by
      clear * - q hK O hobl seed ω N freyaPageTraceSeed freyaPageHaltedUpdate freyaTraceClockConsistent freyaPrefixState freyaPrefixRelation freyaPrefixQuery freyaUpdateClockMono freyaPrefixSameUpdate freyaAfterFinalUpdate

      have hi : (outputIndex seed).val<q.K := by
        have h := (outputIndex seed).isLt
        simpa (config := { iota := false }) only [max_eq_right (show 1≤q.K by omega)] using h
      induction N with
      | zero => exact Or.inl rfl
      | succ N ih =>
        let s := trace {q with «prefix»:=false} O seed ω N
        let t := trace {q with «prefix»:=true} O seed ω N
        change freyaPrefixRelation q (update {q with «prefix»:=false} s
            (replyAt {q with «prefix»:=false} O seed ω N (query {q with «prefix»:=false} s)))
          (update {q with «prefix»:=true} t
            (replyAt {q with «prefix»:=true} O seed ω N (query {q with «prefix»:=true} t)))
        rw [replyAt_prefix q false O hobl seed seed ω N, replyAt_prefix q true O hobl seed seed ω N]
        rcases ih with he | ⟨ht,hiter,hselected,hclock⟩
        · change t=freyaPrefixState q s at he
          rw [he,freyaPrefixQuery]
          apply freyaPrefixSameUpdate
          have hseed := freyaPageTraceSeed {q with «prefix»:=false} O seed ω N
          change s.seed=seed at hseed
          rw [hseed]
          exact hi
        · right
          change t.phase=.halted at ht
          have htu := freyaPageHaltedUpdate {q with «prefix»:=true} t
            (replyAt q O seed ω N (query {q with «prefix»:=true} t)) (by dsimp only [active]; rw [ht])
          rw [htu]
          have hs := freyaAfterFinalUpdate q s (replyAt q O seed ω N (query {q with «prefix»:=false} s)) hiter
          exact ⟨ht,hs.1,hs.2.trans hselected,hclock.trans
            (freyaUpdateClockMono _ s _ (freyaTraceClockConsistent {q with «prefix»:=false} O seed ω N))⟩
    have freyaPrefixOutputLaw (q : Raw) (hK : 0<q.K)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (N : ℕ) :
        (execute O (literal q) (fun _ => N) seed ω).1=
          (execute O (LongTails.Algorithms.FreyaPage.«prefix» q) (fun _ => N) seed ω).1 ∧
        (execute O (LongTails.Algorithms.FreyaPage.«prefix» q) (fun _ => N) seed ω).2≤
          (execute O (literal q) (fun _ => N) seed ω).2 := by
      clear * - q hK O hobl seed ω N freyaPrefixTraceRelation

      dsimp only [literal,LongTails.Algorithms.FreyaPage.«prefix»]
      erw [LongTails.Proofs.FreyaExecution.execute_correspondence {q with «prefix»:=false} O seed ω N,
        LongTails.Proofs.FreyaExecution.execute_correspondence {q with «prefix»:=true} O seed ω N]
      rcases freyaPrefixTraceRelation q hK O hobl seed ω N with he | ⟨_,_,hs,hc⟩
      · rw [he]
        exact ⟨rfl,le_rfl⟩
      · exact ⟨hs,hc⟩
    have _ := hm
    have _ := hn
    have _ := hS
    have _ := f
    have _ := τ
    have _ := hservice
    have _ := hN
    exact freyaPrefixOutputLaw q hK O hobl seed ω N


theorem conditional_transition (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
    (k : ℕ) (hk : k < rounds q)
    (E : Set (Fin (k + 1) → Space q.d × Space q.d)) (hE : MeasurableSet E)
    (U : Set (Space q.d × Space q.d)) (hU : MeasurableSet U) :
    let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
    P {z | (fun j : Fin (k + 1) => observedPair q O z.1 z.2 j.val) ∈ E ∧
      observedPair q O z.1 z.2 (k + 1) ∈ U} =
        ∫⁻ z, transitionDensity q f O k E U z ∂P := by
  run_tac
    let task ← Lean.Elab.Tactic.TacticM.asTask' do
      withTheReader Lean.Core.Context
          (fun ctx => { ctx with maxHeartbeats := 8000000000, maxRecDepth := 4096 }) do
        match Lean.Parser.runParserCategory (← Lean.getEnv) `tactic r###"exact
by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 4096 in
  exact
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 4096 in
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
    open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
    open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    open LongTails.Proofs.FreyaConditionalCosts LongTails.Proofs.FreyaExecution in
    open LongTails.Setups.FreyaIndependence in
    by
      classical
      let freyaListMeasSpace (α : Type) : MeasurableSpace (List α) := ⊤
      have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
        clear * - q s

        delta advance
        split <;> rfl
      have freyaPageAdvanceIteration (q : Raw) (s : State q) :
          (advance q s).iteration = s.iteration ∨ (advance q s).iteration = s.iteration+1 := by
        clear * - q s

        delta advance
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      have freyaPageHaltedUpdate (q : Raw) (s : State q) (reply : Reply q.d q.n)
          (h : active s = false) : update q s reply = s := by
        clear * - q s reply h

        cases hs : s.phase with
        | halted => delta update; rw [hs]
        | full first c =>
          delta active at h
          rw [hs] at h
          contradiction
        | difference c =>
          delta active at h
          rw [hs] at h
          contradiction
      have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
          (h : (List.range N).find? p = some k) :
          k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
        clear * - N p k h

        obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
        simp (config := { iota := false }) only [List.length_range,List.getElem_range] at hi hik hprev
        subst i
        refine ⟨hi,hp,?_⟩
        intro r hr htrue
        have hh := hprev r hr
        rw [htrue] at hh
        contradiction
      have freyaPageDifferenceInvocation (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
          ∃ call c, batchStartCall q O seed ω batch = some call ∧
            (trace q O seed ω call).phase = Phase.difference c ∧
            c.x=x ∧ c.y=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
        clear * - q O seed ω batch firstID x y clock h

        delta invocation at h
        cases hs : batchStartCall q O seed ω batch with
        | none => rw [hs] at h; cases h
        | some call =>
          rw [hs] at h
          dsimp only [Option.bind] at h
          cases hp : (trace q O seed ω call).phase with
          | halted => rw [hp] at h; cases h
          | full first c => rw [hp] at h; cases h
          | difference c =>
            rw [hp] at h
            have heq := Option.some.inj h
            have hfields : c.x=x ∧ c.y=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
              simpa (config := { iota := false }) only [Prod.mk.injEq,true_and] using heq
            exact ⟨call,c,rfl,hp,hfields⟩
      have freyaPageDifferenceEntryAdvance (q : Raw) (s : State q) (reply : Reply q.d q.n)
          (c : DifferenceState q.d q.m q.n) (hphase : (update q s reply).phase = Phase.difference c)
          (hfresh : ¬(s.iteration = (update q s reply).iteration ∧ active s = true)) :
          ∃ t : State q, t.seed = s.seed ∧ advance q t = update q s reply := by
        clear * - q s reply c hphase hfresh

        delta update at hphase hfresh ⊢
        cases hs : s.phase with
        | halted =>
          rw [hs] at hphase
          change s.phase = Phase.difference c at hphase
          rw [hs] at hphase
          cases hphase
        | full first old =>
          rw [hs] at hphase hfresh
          dsimp only at hphase hfresh ⊢
          by_cases he : (fullUpdate old reply).remaining.isEmpty = true
          · rw [ite_eq_left he]
            exact ⟨{s with
              g := fullResult (fullUpdate old reply)
              clock := (fullUpdate old reply).clock
              nextID := (fullUpdate old reply).nextID
              phase := Phase.full first (fullUpdate old reply)},rfl,rfl⟩
          · rw [ite_eq_right he] at hphase
            cases hphase
        | difference old =>
          rw [hs] at hphase hfresh
          dsimp only at hphase hfresh ⊢
          by_cases he : (differenceUpdate old reply).target ≤ (differenceUpdate old reply).count
          · rw [ite_eq_left he]
            exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate old reply)
              clock := (differenceUpdate old reply).clock
              nextID := (differenceUpdate old reply).nextID
              phase := Phase.difference (differenceUpdate old reply)},rfl,rfl⟩
          · apply False.elim
            rw [ite_eq_right he] at hfresh
            apply hfresh
            constructor
            · rfl
            · delta active
              rw [hs]
      have freyaPageAdvanceDifference (q : Raw) (s : State q)
          (c : DifferenceState q.d q.m q.n)
          (h : (advance q s).phase = Phase.difference c) :
          (advance q s).iteration = s.iteration+1 ∧
            c = differenceInitial q.n q.S (s.x-q.η • s.g) s.x s.clock
              (s.seed.1 (s.iteration+1)) s.nextID := by
        clear * - q s c h

        delta advance at h ⊢
        split at h
        · contradiction
        · rename_i hn
          rw [ite_eq_right hn]
          dsimp only at h ⊢
          split at h
          · contradiction
          · exact ⟨rfl,(Phase.difference.inj h).symm⟩
      have freyaDifferenceLiveStep {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
          (s : DifferenceState d m n) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i = some j ∧ reply (some r) = some (i,j.id,c,jobValue f j) ∧
              r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i')
          (ha : s.count < s.target)
          (hp : ∀ i, ∃ job, s.pending i = some job ∧ job.started ≤ s.clock ∧
            (s.clock : ℝ≥0∞) ≤ deadline τ job i ∧ job.kind = Sum.inr (s.x,s.y)) :
          ∃ i job c next,
            s.pending i = some job ∧
            differenceQuery s = some ⟨s.clock,s.pending⟩ ∧
            reply (differenceQuery s) = some (i,job.id,c,jobValue f job) ∧
            s.clock ≤ c ∧
            next.id = s.nextID ∧ next.kind = Sum.inr (s.x,s.y) ∧ next.started = c ∧
            labelAt (s.rows s.nextID) m = some next.component ∧
            differenceUpdate s (reply (differenceQuery s)) =
              {s with
                count := s.count+1
                sum := s.sum+jobValue f job
                pending := Function.update s.pending i (some next)
                clock := c
                nextID := s.nextID+1} ∧
            ∀ k, ∃ old, (Function.update s.pending i (some next)) k = some old ∧
              old.started ≤ c ∧ (c : ℝ≥0∞) ≤ deadline τ old k ∧ old.kind = Sum.inr (s.x,s.y) := by
        clear * - d m n hm hn s f τ reply hservice ha hp

        classical
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hlegal : legalRequest τ r := by
          refine ⟨?_,?_⟩
          · obtain ⟨job,hj,_⟩ := hp ⟨0,hn⟩
            exact ⟨⟨0,hn⟩,job,hj⟩
          · intro i job hj
            obtain ⟨old,hold,hs,ht,_⟩ := hp i
            have heq : job=old := Option.some.inj (hj.symm.trans hold)
            subst old
            exact ⟨hs,ht⟩
        have hquery : differenceQuery s = some r := by
          delta differenceQuery
          rw [ite_eq_right (by omega)]
          delta pendingRequest
          have hex : ∃ i, s.pending i ≠ none := by
            obtain ⟨i,job,hj⟩ := hlegal.1
            change s.pending i=some job at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,c,hjob,hreply,hclock,hdeadline⟩ := hservice r hlegal
        change s.pending i=some job at hjob
        change s.clock≤c at hclock
        obtain ⟨b,hb⟩ : ∃ b : Fin m, labelAt (s.rows s.nextID) m = some b := by
          delta labelAt
          simp (config := { iota := false }) only [hm,dite_true]
          exact ⟨_,rfl⟩
        let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
        refine ⟨i,job,c,next,hjob,hquery,?_,hclock,rfl,rfl,rfl,hb,?_,?_⟩
        · rw [hquery]; exact hreply
        · rw [hquery,hreply]
          delta differenceUpdate
          rw [ite_eq_right (by omega)]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
          delta dispatch
          rw [hb]
          rfl
        · intro k
          by_cases hk : k=i
          · subst k
            refine ⟨next,Function.update_self _ _ _,le_rfl,?_,rfl⟩
            change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞)+(2 : ℕ)*τ i
            exact le_add_of_nonneg_right zero_le
          · obtain ⟨old,hold,hstarted,_,hkind⟩ := hp k
            refine ⟨old,?_,hstarted.trans hclock,hdeadline k old hold,hkind⟩
            rw [Function.update_of_ne hk]
            exact hold
      have freyaPageDifferenceQuery (q : Raw) (s : State q)
          (c : DifferenceState q.d q.m q.n) (h : s.phase = Phase.difference c) :
          query q s = (0,differenceQuery c) := by
        clear * - q s c h

        delta query
        rw [h]
        rfl
      have freyaPageDifferenceContinue (q : Raw) (s : State q)
          (c : DifferenceState q.d q.m q.n) (reply : Reply q.d q.n)
          (h : s.phase = Phase.difference c)
          (ha : (differenceUpdate c reply).count < (differenceUpdate c reply).target) :
          (update q s reply).phase = Phase.difference (differenceUpdate c reply) ∧
            (update q s reply).iteration = s.iteration := by
        clear * - q s c reply h ha

        delta update
        rw [h]
        dsimp only
        rw [ite_eq_right (by omega)]
        exact ⟨rfl,rfl⟩
      have freyaFullPotentialDecrease {d m n : ℕ} (hn : 0<n)
          (labels : List (Fin m)) (s : FullState d m n)
          (horig : s.original=labels) (hne : s.remaining≠[])
          (hbound : ∀ b ∈ s.remaining,b<labels.length)
          (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
          let good (s : FullState d m n) := Finset.univ.filter fun i =>
            ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
          let V (s : FullState d m n) :=
            if s.remaining=[] then 0 else n*(s.remaining.length+1)-(good s).card
          V (fullUpdate s (reply (fullQuery s)))+1≤V s := by
        clear * - d m n hn labels s horig hne hbound f τ reply hr hservice

        classical
        dsimp only
        let good (s : FullState d m n) : Finset (Fin n) := Finset.univ.filter fun i =>
          ∃ job, s.pending i = some job ∧ ∃ b ∈ s.remaining, labels[b]? = some job.component
        let V (s : FullState d m n) : ℕ :=
          if s.remaining = [] then 0 else n * (s.remaining.length + 1) - (good s).card
        have hcard (s : FullState d m n) : (good s).card ≤ n := by
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin n)
        have hselect (rem : List ℕ) (hne : rem ≠ [])
            (hbound : ∀ b ∈ rem, b < labels.length) (row : ChoiceRow) :
            ∃ b, b ∈ rem ∧ ∃ hb : b < labels.length,
              selectedLabel labels rem row = some labels[b] := by
          have hlen : rem.length ≠ 0 := by
            intro hz
            exact hne (List.length_eq_zero_iff.mp hz)
          let j : Fin rem.length := ⟨(row (rem.length-1)).val, by
            have hj := (row (rem.length-1)).isLt
            omega⟩
          have hb := hbound _ (List.get_mem rem j)
          refine ⟨rem.get j, List.get_mem rem j, hb, ?_⟩
          delta selectedLabel chooseRemaining
          rw [dite_eq_right hlen]
          dsimp only
          exact List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
        have hpositive (s : FullState d m n) (hne : s.remaining ≠ []) : 0 < V s := by
          have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
          have hc := hcard s
          have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
          dsimp only [V]
          rw [ite_eq_right hne, Nat.mul_add, Nat.mul_one]
          omega
        change V (fullUpdate s (reply (fullQuery s)))+1≤V s
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hisEmpty : s.remaining.isEmpty = false := by
          cases h : s.remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        have hquery : fullQuery s = some r := by
          delta fullQuery
          simp (config := { iota := false }) only [hisEmpty, Bool.false_eq_true, ite_false]
          delta pendingRequest
          have hex : ∃ i, s.pending i ≠ none := by
            obtain ⟨i, job, hj⟩ := hr.1
            change s.pending i = some job at hj
            exact ⟨i, by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i, job, c, hj, hreply, hc, _⟩ := hservice r hr
        change s.pending i = some job at hj
        change s.clock ≤ c at hc
        let found := s.remaining.find? fun b => decide (s.original[b]? = some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let next := dispatch (Sum.inl s.point) c s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n :=
          { s with
            remaining := rem
            sum := if found.isSome then s.sum + jobValue f job else s.sum
            pending := Function.update s.pending i next
            clock := c
            nextID := s.nextID+1 }
        have hstep : fullUpdate s (reply (fullQuery s)) = t := by
          rw [hquery, hreply]
          delta fullUpdate
          rw [hisEmpty, ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hj]
          dsimp only
          rw [ite_eq_left (And.intro rfl hc)]
        rw [hstep]
        by_cases ht : rem = []
        · have hzero : V t = 0 := by
            dsimp only [V]
            exact ite_eq_left ht
          rw [hzero]
          exact hpositive s hne
        · have hrembound : ∀ b ∈ rem, b < labels.length := by
            cases hf : found with
            | none => simpa (config := { iota := false }) only [rem, hf, Option.elim_none] using hbound
            | some b =>
              intro k hk
              exact hbound k (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem, hf, Option.elim_some] using hk))
          have hgood : i ∈ good t := by
            obtain ⟨b, hb, hbl, hlabel⟩ := hselect rem ht hrembound (s.rows s.nextID)
            simp (config := { iota := false }) only [good, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨⟨labels[b], Sum.inl s.point, c, s.nextID⟩, ?_, b, hb, ?_⟩
            · change Function.update s.pending i next i = _
              rw [Function.update_self]
              change dispatch (Sum.inl s.point) c s.nextID
                (selectedLabel s.original rem (s.rows s.nextID)) = _
              rw [horig, hlabel]
              rfl
            · exact List.getElem?_eq_some_iff.mpr ⟨hbl, rfl⟩
          have hlow : 1 ≤ (good t).card := Finset.card_pos.mpr ⟨i, hgood⟩
          have hcs := hcard s
          have hct := hcard t
          change (if rem = [] then 0 else n*(rem.length+1)-(good t).card)+1 ≤ _
          rw [ite_eq_right ht]
          change n*(rem.length+1)-(good t).card+1 ≤
            if s.remaining = [] then 0 else n*(s.remaining.length+1)-(good s).card
          rw [ite_eq_right hne]
          cases hf : found with
          | some b =>
            have hb : b ∈ s.remaining := List.mem_of_find?_eq_some hf
            have hlen : rem.length+1 = s.remaining.length := by
              dsimp only [rem]
              rw [hf]
              change (s.remaining.erase b).length+1=s.remaining.length
              have hl := List.length_erase_of_mem hb
              have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
              omega
            have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
            have hmul : n ≤ n*s.remaining.length := Nat.le_mul_of_pos_right _ hp
            rw [hlen, Nat.mul_add, Nat.mul_one]
            have calcBound (n a b c : ℕ) (hn : 0<n) (hb : b≤n) (hc : 1≤c)
                (hc' : c≤n) (ha : n≤a) : a-c+1≤a+n-b := by omega
            exact calcBound n (n*s.remaining.length) (good s).card (good t).card hn hcs hlow hct hmul
          | none =>
            have hrem : rem = s.remaining := by simp (config := { iota := false }) only [rem, hf, Option.elim_none]
            have hbad : i ∉ good s := by
              intro hi
              obtain ⟨old, hold, b, hb, hlabel⟩ := (Finset.mem_filter.mp hi).2
              have heq : old = job := Option.some.inj (hold.symm.trans hj)
              subst old
              have hfind := List.find?_eq_none.mp hf b hb
              simp (config := { iota := false }) only [horig, hlabel, decide_true, not_true_eq_false] at hfind
            have hset : good t = insert i (good s) := by
              apply Finset.ext
              intro k
              by_cases hk : k = i
              · subst k
                exact iff_of_true hgood (Finset.mem_insert_self _ _)
              · simp (config := { iota := false }) only [Finset.mem_insert, hk, false_or]
                change (k ∈ Finset.univ.filter fun k =>
                  ∃ old, Function.update s.pending i next k = some old ∧
                    ∃ b ∈ rem, labels[b]? = some old.component) ↔ _
                simp (config := { iota := false }) only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [Function.update_of_ne hk, hrem]
                simp (config := { iota := false }) only [good, Finset.mem_filter, Finset.mem_univ, true_and]
            have hcount : (good t).card = (good s).card+1 := by
              rw [hset, Finset.card_insert_of_notMem hbad]
            rw [hrem, hcount, Nat.mul_add, Nat.mul_one]
            have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
            have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
            have calcBound (n a b : ℕ) (hn : 0<n) (hb : b≤n) (ha : n≤a) :
                a+n-(b+1)+1≤a+n-b := by omega
            exact calcBound n (n*s.remaining.length) (good s).card hn hcs hmul
      have freyaFullSelect {m : ℕ} (labels : List (Fin m)) (rem : List ℕ)
          (hne : rem≠[]) (hbound : ∀ b ∈ rem,b<labels.length) (row : ChoiceRow) :
          ∃ b, b ∈ rem ∧ ∃ hb : b<labels.length, selectedLabel labels rem row=some labels[b] := by
        clear * - m labels rem hne hbound row

        have hlen : rem.length≠0 := by intro hz; exact hne (List.length_eq_zero_iff.mp hz)
        let j : Fin rem.length := ⟨(row (rem.length-1)).val,by
          have hj := (row (rem.length-1)).isLt
          omega⟩
        have hb := hbound _ (List.get_mem rem j)
        refine ⟨rem.get j,List.get_mem rem j,hb,?_⟩
        delta selectedLabel chooseRemaining
        rw [dite_eq_right hlen]
        dsimp only
        exact List.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩
      have freyaDifferenceInitialSafe {d m n : ℕ} (hm : 0<m) (S : ℕ) (hS : 0<S)
          (x y : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ)
          (τ : Fin n → ℝ≥0∞) :
          let c : DifferenceState d m n := differenceInitial n S x y clock rows firstID
          ∀ i, ∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
        clear * - d m n hm S hS x y clock rows firstID τ

        dsimp only
        intro i
        obtain ⟨b,hb⟩ : ∃ b : Fin m,labelAt (rows (firstID+i.val)) m=some b := by
          delta labelAt
          simp (config := { iota := false }) only [hm,dite_true]
          exact ⟨_,rfl⟩
        refine ⟨⟨b,Sum.inr (x,y),clock,firstID+i.val⟩,?_,le_rfl,?_,rfl⟩
        · change (if S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
            (labelAt (rows (firstID+i.val)) m))=_
          rw [ite_eq_right (by omega),hb]
          rfl
        · exact le_add_of_nonneg_right zero_le
      have freyaPageFullQuery (q : Raw) (s : State q) (first : Bool)
          (c : FullState q.d q.m q.n) (h : s.phase=Phase.full first c) :
          query q s=(0,fullQuery c) := by
        clear * - q s first c h

        delta query
        rw [h]
        rfl
      have freyaPageFullInvocation (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch=some (true,x,y,clock,firstID)) :
          ∃ call first c,batchStartCall q O seed ω batch=some call ∧
            (trace q O seed ω call).phase=Phase.full first c ∧
            c.point=x ∧ c.point=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
        clear * - q O seed ω batch firstID x y clock h

        delta invocation at h
        cases hs : batchStartCall q O seed ω batch with
        | none => rw [hs] at h; cases h
        | some call =>
          rw [hs] at h
          dsimp only [Option.bind] at h
          cases hp : (trace q O seed ω call).phase with
          | halted => rw [hp] at h; cases h
          | difference c => rw [hp] at h; cases h
          | full first c =>
            rw [hp] at h
            have heq := Option.some.inj h
            have hfields : c.point=x ∧ c.point=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
              simpa (config := { iota := false }) only [Prod.mk.injEq,true_and] using heq
            exact ⟨call,first,c,rfl,hp,hfields⟩
      have freyaPageFullEntryAdvance (q : Raw) (s : State q) (reply : Reply q.d q.n)
          (first : Bool) (c : FullState q.d q.m q.n) (hphase : (update q s reply).phase=Phase.full first c)
          (hfresh : ¬(s.iteration=(update q s reply).iteration ∧ active s=true)) :
          ∃ t : State q,t.seed=s.seed ∧ advance q t=update q s reply := by
        clear * - q s reply first c hphase hfresh

        delta update at hphase hfresh ⊢
        cases hs : s.phase with
        | halted =>
          rw [hs] at hphase
          change s.phase=Phase.full first c at hphase
          rw [hs] at hphase
          cases hphase
        | full oldfirst old =>
          rw [hs] at hphase hfresh
          dsimp only at hphase hfresh ⊢
          by_cases he : (fullUpdate old reply).remaining.isEmpty=true
          · rw [ite_eq_left he]
            exact ⟨{s with
              g := fullResult (fullUpdate old reply)
              clock := (fullUpdate old reply).clock
              nextID := (fullUpdate old reply).nextID
              phase := Phase.full oldfirst (fullUpdate old reply)},rfl,rfl⟩
          · apply False.elim
            rw [ite_eq_right he] at hfresh
            apply hfresh
            refine ⟨rfl,?_⟩
            delta active
            rw [hs]
        | difference old =>
          rw [hs] at hphase hfresh
          dsimp only at hphase hfresh ⊢
          by_cases he : (differenceUpdate old reply).target≤(differenceUpdate old reply).count
          · rw [ite_eq_left he]
            exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate old reply)
              clock := (differenceUpdate old reply).clock
              nextID := (differenceUpdate old reply).nextID
              phase := Phase.difference (differenceUpdate old reply)},rfl,rfl⟩
          · rw [ite_eq_right he] at hphase
            cases hphase
      have freyaPageAdvanceFull (q : Raw) (s : State q) (first : Bool)
          (c : FullState q.d q.m q.n) (h : (advance q s).phase=Phase.full first c) :
          (advance q s).iteration=s.iteration+1 ∧ first=false ∧
            c=fullInitial q.n (List.ofFn id) (s.x-q.η • s.g) s.clock
              (s.seed.1 (s.iteration+1)) s.nextID := by
        clear * - q s first c h

        delta advance at h ⊢
        split at h
        · contradiction
        · rename_i hn
          rw [ite_eq_right hn]
          dsimp only at h ⊢
          split at h
          · have he := Phase.full.inj h
            exact ⟨rfl,he.1.symm,he.2.symm⟩
          · contradiction
      have freyaAdvanceLeaves (q : Raw) (s : State q) :
          (advance q s).iteration≠s.iteration ∨ active (advance q s)=false := by
        clear * - q s

        delta advance
        split
        · exact Or.inr rfl
        · exact Or.inl (Nat.succ_ne_self s.iteration)
      have freyaExitAdvance (q : Raw) (s : State q) (r : Reply q.d q.n)
          (ha : active s=true)
          (he : (update q s r).iteration≠s.iteration ∨ active (update q s r)=false) :
          ∃ t : State q,t.iteration=s.iteration ∧ t.seed=s.seed ∧ update q s r=advance q t := by
        clear * - q s r ha he

        cases hp : s.phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := fullResult (fullUpdate c r)
              clock := (fullUpdate c r).clock
              nextID := (fullUpdate c r).nextID
              phase := .full first (fullUpdate c r)},rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
        | difference c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate c r)
              clock := (differenceUpdate c r).clock
              nextID := (differenceUpdate c r).nextID
              phase := .difference (differenceUpdate c r)},rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
      have freyaBatchZeroStart (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hK : 0<q.K)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          batchStartCall q O seed ω 0=some 0 := by
        clear * - q hm hn hK O seed ω

        classical
        dsimp only [batchStartCall]
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨?_,0,?_,?_,?_⟩
        · dsimp only [trace,run,initial,active]
          rw [ite_eq_right (show ¬(q.m=0 ∨ q.n=0 ∨ q.K=0) by omega)]
          rfl
        · simp (config := { iota := false }) only [List.length_range]; omega
        · simp (config := { iota := false }) only [List.getElem_range]
        · intro r hr; omega
      let freyaBatchTag (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (b : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) : ℕ :=
        (invocation q O z.1 z.2 b).elim 2 (fun t => if t.1 then 0 else 1)
      have freyaExitObserved (q : Raw) (s : State q) (r : Reply q.d q.n)
          (ha : active s=true)
          (he : (update q s r).iteration≠s.iteration ∨ active (update q s r)=false) :
          ∃ t : State q,t.iteration=s.iteration ∧ t.seed=s.seed ∧ t.x=s.x ∧ t.selected=s.selected ∧
            t.g=(match s.phase with
              | .full _ c => fullResult (fullUpdate c r)
              | .difference c => s.g+differenceResult (differenceUpdate c r)
              | .halted => s.g) ∧ update q s r=advance q t := by
        clear * - q s r ha he

        cases hp : s.phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := fullResult (fullUpdate c r)
              clock := (fullUpdate c r).clock
              nextID := (fullUpdate c r).nextID
              phase := .full first (fullUpdate c r)},rfl,rfl,rfl,rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
        | difference c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate c r)
              clock := (differenceUpdate c r).clock
              nextID := (differenceUpdate c r).nextID
              phase := .difference (differenceUpdate c r)},rfl,rfl,rfl,rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
      let freyaInside {q : Raw} (s : State q) : Space q.d × Space q.d × Option Bool :=
        (s.x,s.g,Phase.casesOn s.phase (fun first _ => some first) (fun _ => none) none)
      let freyaFullGradientInvariant {d m n : ℕ} (f : Fin m → Space d → ℝ)
          (c : FullState d m n) : Prop :=
        c.sum+(c.remaining.map (contribution f c.original c.point)).sum=
          (c.original.map fun i => gradient (f i) c.point).sum ∧
        ∀ i job,c.pending i=some job → job.kind=Sum.inl c.point
      have freyaObservedFullExit (q : Raw) (s : State q) (r : Reply q.d q.n)
          (first : Bool) (c : FullState q.d q.m q.n) (hp : s.phase=Phase.full first c)
          (he : (update q s r).iteration≠s.iteration ∨ active (update q s r)=false) :
          (fullUpdate c r).remaining=[] := by
        clear * - q s r first c hp he

        by_contra hne
        have hi : (fullUpdate c r).remaining.isEmpty=false := by
          cases h : (fullUpdate c r).remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        dsimp only [update] at he
        rw [hp] at he
        dsimp only at he
        rw [hi,ite_eq_right Bool.false_ne_true] at he
        rcases he with he|he
        · exact he rfl
        · cases he
      let freyaControl {q : Raw} (s : State q) :=
        (s.iteration,s.x,s.g,s.clock,s.nextID,s.phase)
      let freyaHistoryView (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (batch : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :=
        (invocation q O z.1 z.2 batch, fun k : ℕ =>
          if k < (batchStartCall q O z.1 z.2 batch).getD 0 then
            let s := trace q O z.1 z.2 k
            let reply := replyAt q O z.1 z.2 k (query q s)
            some (query q s,reply,collectorPendingAfter q s reply)
          else none)
      have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
          (b : β) (f : α → β) (hf : Measurable f) :
          Measurable (fun o : Option α => o.elim b f) := by
        clear * - α β b f hf

        have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
          apply Measurable.of_comap_le
          delta instMeasurableSpaceOption
          apply le_of_eq
          congr 1
          funext o
          cases o <;> rfl
        have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
        convert hs.comp he using 1
        funext o
        cases o <;> rfl
      have freyaOptionSomeMeas {α : Type} [MeasurableSpace α] :
          Measurable (some : α → Option α) := by
        clear * - α

        delta instMeasurableSpaceOption
        rw [measurable_comap_iff]
        exact measurable_inr
      have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
          (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
          Measurable (fun z => f (g z) z) :=
        (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
          (measurable_id.prodMk hg)
      let freyaFullCode {d m n : ℕ} (s : FullState d m n) :=
        (s.original,s.remaining,s.point,s.sum,s.pending,s.clock,s.rows,s.nextID)
      let freyaFullMeasSpace (d m n : ℕ) : MeasurableSpace (FullState d m n) :=
        MeasurableSpace.comap freyaFullCode inferInstance
      let freyaDifferenceCode {d m n : ℕ} (s : DifferenceState d m n) :=
        (s.target,s.count,s.x,s.y,s.sum,s.pending,s.clock,s.rows,s.nextID)
      let freyaDifferenceMeasSpace (d m n : ℕ) : MeasurableSpace (DifferenceState d m n) :=
        MeasurableSpace.comap freyaDifferenceCode inferInstance
      have freyaJobCodeMeas {d m : ℕ} :
          Measurable (fun j : Job d m => (j.component,j.kind,j.started,j.id)) :=
        Measurable.of_comap_le le_rfl
      let freyaFullReplyJob {d m n : ℕ} (s : FullState d m n)
          (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : FullState d m n := by
        clear * - d m n s r job

        classical
        exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
          let found := s.remaining.find? fun a => decide (s.original[a]?=some job.component)
          let remaining := found.elim s.remaining (fun a => s.remaining.erase a)
          let sum := if found.isSome then s.sum+r.2.2.2 else s.sum
          let next := dispatch (Sum.inl s.point) r.2.2.1 s.nextID
            (selectedLabel s.original remaining (s.rows s.nextID))
          {s with
            remaining:=remaining
            sum:=sum
            pending:=Function.update s.pending r.1 next
            clock:=r.2.2.1
            nextID:=s.nextID+1}
        else s
      let freyaDifferenceReplyJob {d m n : ℕ} (s : DifferenceState d m n)
          (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : DifferenceState d m n := by
        clear * - d m n s r job

        classical
        exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
          let next := dispatch (Sum.inr (s.x,s.y)) r.2.2.1 s.nextID (labelAt (s.rows s.nextID) m)
          {s with
            count:=s.count+1
            sum:=s.sum+r.2.2.2
            pending:=Function.update s.pending r.1 next
            clock:=r.2.2.1
            nextID:=s.nextID+1}
        else s
      let freyaPhaseCode {d m n : ℕ} (p : Phase d m n) :
          Unit ⊕ ((Bool × FullState d m n) ⊕ DifferenceState d m n) :=
        p.casesOn (fun b c => Sum.inr (Sum.inl (b,c))) (fun c => Sum.inr (Sum.inr c)) (Sum.inl ())
      let freyaPhaseMeasSpace (d m n : ℕ) : MeasurableSpace (Phase d m n) :=
        MeasurableSpace.comap freyaPhaseCode inferInstance
      let freyaStateCode {q : Raw} (s : State q) :=
        (s.seed,s.iteration,s.x,s.g,s.selected,s.clock,s.nextID,s.phase)
      let freyaStateMeasSpace (q : Raw) : MeasurableSpace (State q) :=
        MeasurableSpace.comap freyaStateCode inferInstance
      have freyaFindMeas {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          (l : List α) (p : Ω → α → Bool) (hp : ∀ a,Measurable (fun z => p z a)) :
          Measurable (fun z => l.find? (p z)) := by
        clear * - Ω α l p hp

        classical
        induction l with
        | nil => exact measurable_const
        | cons a l ih =>
          have h : Measurable (fun z => if p z a=true then some a else l.find? (p z)) :=
            measurable_const.ite ((hp a) (measurableSet_singleton true)) ih
          convert h using 1
          funext z
          simp (config := { iota := false }) only [List.find?_cons]
          cases p z a <;> rfl
      have freyaInfiniteResample {α : Type} [MeasurableSpace α]
          (μ : Measure α) [IsProbabilityMeasure μ] (i : ℕ) :
          MeasurePreserving (fun z : (ℕ → α) × α => Function.update z.1 i z.2)
            ((Measure.infinitePi fun _ : ℕ => μ).prod μ) (Measure.infinitePi fun _ : ℕ => μ) := by
        clear * - α μ i

        classical
        have hm : Measurable (fun z : (ℕ → α) × α => Function.update z.1 i z.2) := by
          apply Measurable.of_eval
          intro j
          by_cases hj : j=i
          · subst j
            simpa (config := { iota := false }) only [Function.update_self] using
              (measurable_snd : Measurable (fun z : (ℕ → α) × α => z.2))
          · simpa (config := { iota := false }) only [Function.update_of_ne hj,Function.comp_def] using
              ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (ℕ → α) × α => z.1)))
        refine ⟨hm,Measure.eq_infinitePi _ (fun s t ht => ?_)⟩
        rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
        by_cases hi : i∈s
        · have he : (fun z : (ℕ → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi (↑s) t =
              (Set.pi (↑(s.erase i)) t) ×ˢ t i := by
            ext z
            simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Finset.mem_erase]
            constructor
            · intro h
              exact ⟨fun j hj => by simpa (config := { iota := false }) only [Function.update_of_ne hj.1] using h j hj.2,
                by simpa (config := { iota := false }) only [Function.update_self] using h i hi⟩
            · rintro ⟨h,hv⟩ j hj
              by_cases hji : j=i
              · subst j; simpa (config := { iota := false }) only [Function.update_self] using hv
              · simpa (config := { iota := false }) only [Function.update_of_ne hji] using h j ⟨hji,hj⟩
          rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun j _ => ht j)]
          exact Finset.prod_erase_mul s (fun j => μ (t j)) hi
        · have he : (fun z : (ℕ → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi (↑s) t =
              (Set.pi (↑s) t) ×ˢ Set.univ := by
            ext z
            simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Set.mem_univ,and_true]
            apply forall_congr'
            intro j
            apply forall_congr'
            intro hj
            rw [Function.update_of_ne (show j≠i from fun he => hi (he ▸ hj))]
          rw [he,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi _ (fun j _ => ht j)]
      let freyaObservedFinish (q : Raw) (s : State q) (r : Reply q.d q.n) : Space q.d × Space q.d :=
        match s.phase with
        | .full _ c => (s.x,fullResult (fullUpdate c r))
        | .difference c => (s.x,s.g+differenceResult (differenceUpdate c r))
        | .halted => (s.x,s.g)
      have freyaBernoulliMass (ρ : ℝ) (hρ : 0<ρ) (hρone : ρ≤1) :
          (bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one ρ)) {true}=ENNReal.ofReal ρ ∧
          (bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one ρ)) {false}=ENNReal.ofReal (1-ρ) := by
        clear * - ρ hρ hρone

        have hp : Set.projIcc 0 1 zero_le_one ρ=⟨ρ,⟨hρ.le,hρone⟩⟩ :=
          Set.projIcc_of_mem _ ⟨hρ.le,hρone⟩
        constructor
        · rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton true) (by rfl) (by simp (config := { iota := false })),hp]
          exact ENNReal.ofReal_coe_nnreal.symm
        · rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton false) (by simp (config := { iota := false })) (by rfl),hp]
          exact ENNReal.ofReal_coe_nnreal.symm
      let freyaFullNext (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (p : Space q.d × Space q.d) : Space q.d × Space q.d :=
        (p.1-q.η • p.2,gradient (objective f) (p.1-q.η • p.2))
      let freyaDiffNext (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (v : Fin q.S → Fin q.m) (p : Space q.d × Space q.d) : Space q.d × Space q.d :=
        (p.1-q.η • p.2,p.2+(q.S : ℝ)⁻¹ •
          (∑ j : Fin q.S,(gradient (f (v j)) (p.1-q.η • p.2)-gradient (f (v j)) p.1)))
      have freyaGradientMeas (d : ℕ) (f : Space d → ℝ) : Measurable (gradient f) :=
        (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
      let freyaHRPair (d : ℕ) := Space d × Space d
      let freyaHREvent (d m : ℕ) := Unit ⊕ (Fin m × Bool × Space d × Space d)
      let freyaHRFound (m : ℕ) (r : List ℕ) (i : Fin m) : Option ℕ := by
        clear * - m r i

        classical
        exact r.find? fun a => decide ((List.ofFn (fun j : Fin m => j))[a]? = some i)
      let freyaHRCompletedJob {d m n : ℕ} (z : Option (Request d m n) × Reply d n) :
          Option (Job d m)  := by
        clear * - d m n z

        classical
        exact z.1.elim none (fun r => z.2.elim none (fun a =>
          (r.pending a.1).elim none (fun job => if job.id=a.2.1 then some job else none)))
      let freyaHRReplyValue {d n : ℕ} (r : Reply d n) : Space d :=
        r.elim 0 (fun v => v.2.2.2)
      let freyaHRFullKind {d : ℕ} (k : JobKind d) : Bool := k.elim (fun _ => true) (fun _ => false)
      let freyaHRPointOfKind {d : ℕ} (k : JobKind d) : Space d := k.elim id Prod.fst
      let freyaHRHistoryEntry (d m n : ℕ) := Option ((Fin 1 × Option (Request d m n)) ×
        Reply d n × (Fin n → Option (Job d m)))
      have freyaHRDifferenceFields {d m n : ℕ} (c : DifferenceState d m n) (i : Fin n) (j : Job d m)
          (time : ℝ≥0) (v : Space d) (hne : c.count < c.target)
          (hj : c.pending i = some j) (ht : c.clock ≤ time) :
          let c' := differenceUpdate c (some (i,j.id,time,v))
          c'.target = c.target ∧ c'.count = c.count+1 ∧ c'.sum = c.sum+v := by
        clear * - d m n c i j time v hne hj ht

        dsimp only
        delta differenceUpdate
        rw [ite_eq_right (not_le.mpr hne)]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl ht)]
        exact ⟨rfl,rfl,rfl⟩
      have freyaHRDifferencePoint_update {d m n : ℕ} (c : DifferenceState d m n) (r : Reply d n) :
          (differenceUpdate c r).x=c.x := by
        clear * - d m n c r

        delta differenceUpdate
        split
        · rfl
        · cases r with
          | none => rfl
          | some v =>
            rcases v with ⟨i,id,t,v⟩
            dsimp only
            cases h : c.pending i with
            | none => rfl
            | some job =>
              dsimp only
              split <;> rfl
      let freyaHRDifferencePoint {q : Raw} (s : State q) : Prop :=
        ∀ c,s.phase=Phase.difference c → c.x=s.x
      have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
          (update q s reply).seed = s.seed := by
        clear * - q s reply freyaPageAdvanceSeed

        delta update
        cases hs : s.phase with
        | halted => rfl
        | full first c =>
          dsimp only
          split
          · exact freyaPageAdvanceSeed q _
          · rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPageAdvanceSeed q _
          · rfl
      have freyaPageUpdateIteration (q : Raw) (s : State q) (reply : Reply q.d q.n) :
          (update q s reply).iteration = s.iteration ∨
            (update q s reply).iteration = s.iteration+1 := by
        clear * - q s reply freyaPageAdvanceIteration

        delta update
        cases hs : s.phase with
        | halted => exact Or.inl rfl
        | full first c =>
          dsimp only
          split
          · exact freyaPageAdvanceIteration q _
          · exact Or.inl rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPageAdvanceIteration q _
          · exact Or.inl rfl
      have freyaPageBatchStartFacts (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
          (h : batchStartCall q O seed ω batch = some call) :
          call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
            active (trace q O seed ω call) = true ∧
            ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
        clear * - q O seed ω batch call h freyaPageFirstMatch

        delta batchStartCall at h
        obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
        obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
        refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
        intro r hr hh
        apply hprev r hr
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
      have freyaPageCompletedJobEq (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ) (j : Fin q.S)
          (hstart : batchStartCall q O seed ω batch = some call)
          (c : DifferenceState q.d q.m q.n)
          (hphase : (trace q O seed ω (call+j.val)).phase = Phase.difference c)
          (hq : differenceQuery c = some ⟨c.clock,c.pending⟩)
          (i : Fin q.n) (job : Job q.d q.m) (time : ℝ≥0) (value : Space q.d)
          (hj : c.pending i = some job)
          (hr : replyAt q O seed ω (call+j.val) (0,differenceQuery c) =
            some (i,job.id,time,value)) : completedJob q O seed ω batch j = some job := by
        clear * - q O seed ω batch call j hstart c hphase hq i job time value hj hr freyaPageDifferenceQuery

        have hquery := freyaPageDifferenceQuery q _ c hphase
        delta completedJob
        rw [hstart]
        dsimp only [Option.getD]
        rw [hquery]
        dsimp only
        rw [hr,hq]
        dsimp only
        rw [hj]
        dsimp only [Option.bind]
        rw [ite_eq_left rfl]
      have freyaFullSafeUpdate {d m n : ℕ} (s : FullState d m n)
          (hne : s.remaining≠[]) (hbound : ∀ b ∈ s.remaining,b<s.original.length)
          (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
          let t := fullUpdate s (reply (fullQuery s))
          t.original=s.original ∧ (∀ b ∈ t.remaining,b<t.original.length) ∧
            (t.remaining≠[] → legalRequest τ ⟨t.clock,t.pending⟩) := by
        clear * - d m n s hne hbound f τ reply hr hservice freyaFullSelect

        classical
        have hisEmpty : s.remaining.isEmpty=false := by
          cases h : s.remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hquery : fullQuery s=some r := by
          delta fullQuery
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          delta pendingRequest
          have hex : ∃ i,s.pending i≠none := by
            obtain ⟨i,job,hj⟩ := hr.1
            change s.pending i=some job at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,time,hjob,hreply,hclock,hdeadline⟩ := hservice r hr
        change s.pending i=some job at hjob
        change s.clock≤time at hclock
        let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let next := dispatch (Sum.inl s.point) time s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n :=
          {s with
            remaining := rem
            sum := if found.isSome then s.sum+jobValue f job else s.sum
            pending := Function.update s.pending i next
            clock := time
            nextID := s.nextID+1}
        have ht : fullUpdate s (reply (fullQuery s))=t := by
          rw [hquery,hreply]
          delta fullUpdate
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
        have hb : ∀ b ∈ rem,b<s.original.length := by
          cases hf : found with
          | none => simpa (config := { iota := false }) only [rem,hf,Option.elim_none] using hbound
          | some a =>
            intro b h
            exact hbound b (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem,hf,Option.elim_some] using h))
        dsimp only
        rw [ht]
        refine ⟨rfl,hb,?_⟩
        intro htne
        obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect s.original rem htne hb (s.rows s.nextID)
        let new : Job d m := ⟨s.original[b],Sum.inl s.point,time,s.nextID⟩
        have hnew : next=some new := by
          dsimp only [next]
          rw [hlabel]
          rfl
        refine ⟨⟨i,new,?_⟩,?_⟩
        · change Function.update s.pending i next i=some new
          rw [Function.update_self,hnew]
        · intro k old hold
          change Function.update s.pending i next k=some old at hold
          by_cases hk : k=i
          · subst k
            rw [Function.update_self,hnew] at hold
            have heq : new=old := Option.some.inj hold
            subst old
            refine ⟨le_rfl,?_⟩
            exact le_add_of_nonneg_right zero_le
          · rw [Function.update_of_ne hk] at hold
            exact ⟨((hr.2 k old hold).1).trans hclock,hdeadline k old hold⟩
      have freyaFullInitialSafe {d m n : ℕ} (hn : 0<n) (labels : List (Fin m))
          (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow)
          (firstID : ℕ) (τ : Fin n → ℝ≥0∞) :
          let s := fullInitial n labels x clock rows firstID
          s.remaining≠[] ∧ (∀ b ∈ s.remaining,b<s.original.length) ∧
            legalRequest τ ⟨s.clock,s.pending⟩ := by
        clear * - d m n hn labels hne x clock rows firstID τ freyaFullSelect

        classical
        let s := fullInitial n labels x clock rows firstID
        have hrem : (List.range labels.length)≠[] := by
          intro h
          have := congrArg List.length h
          simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
          exact hne (List.length_eq_zero_iff.mp this)
        have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
        refine ⟨hrem,hbound,?_,?_⟩
        · let i : Fin n := ⟨0,hn⟩
          obtain ⟨b,_,hb,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
          refine ⟨i,⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_⟩
          change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
          rw [hlabel]
          rfl
        · intro i job hj
          change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=some job at hj
          delta dispatch at hj
          obtain ⟨b,_,heq⟩ := Option.map_eq_some_iff.mp hj
          cases heq
          exact ⟨le_rfl,le_add_of_nonneg_right zero_le⟩
      have freyaFullInitialPotential {d m n : ℕ} (labels : List (Fin m))
          (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
          let good (s : FullState d m n) := Finset.univ.filter fun i =>
            ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
          let V (s : FullState d m n) :=
            if s.remaining=[] then 0 else n*(s.remaining.length+1)-(good s).card
          V (fullInitial n labels x clock rows firstID) ≤ n*labels.length := by
        clear * - d m n labels hne x clock rows firstID freyaFullSelect

        classical
        let s := fullInitial n labels x clock rows firstID
        let good (s : FullState d m n) := Finset.univ.filter fun i =>
          ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
        have hrem : (List.range labels.length)≠[] := by
          intro h
          have := congrArg List.length h
          simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
          exact hne (List.length_eq_zero_iff.mp this)
        have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
        have hg : good s=Finset.univ := by
          apply Finset.ext
          intro i
          simp (config := { iota := false }) only [good,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
          obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
          refine ⟨⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_,b,hbr,?_⟩
          · change dispatch (Sum.inl x) clock (firstID+i.val)
              (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
            rw [hlabel]
            rfl
          · exact List.getElem?_eq_some_iff.mpr ⟨hbl,rfl⟩
        change (if List.range labels.length=[] then 0 else
          n*((List.range labels.length).length+1)-(good s).card)≤n*labels.length
        rw [ite_eq_right hrem,hg,Finset.card_fin,List.length_range,Nat.mul_add,Nat.mul_one]
        omega
      have freyaBatchEndFromPrefix (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) (batch call N : ℕ) (hN : 0<N)
          (hstart : batchStartCall q O z.1 z.2 batch=some call)
          (hex : (batchEndCall q O z.1 z.2 batch).isSome)
          (hbefore : ∀ a<N,(trace q O z.1 z.2 (call+a)).iteration=batch ∧
            active (trace q O z.1 z.2 (call+a))=true)
          (hend : (trace q O z.1 z.2 (call+N)).iteration≠batch ∨
            active (trace q O z.1 z.2 (call+N))=false) :
          batchEndCall q O z.1 z.2 batch=some (call+N) := by
        clear * - q O z batch call N hN hstart hex hbefore hend freyaPageFirstMatch

        classical
        obtain ⟨last,hlast⟩ : ∃ last,batchEndCall q O z.1 z.2 batch=some last := by
          cases h : batchEndCall q O z.1 z.2 batch with
          | none => rw [h] at hex; cases hex
          | some last => exact ⟨last,rfl⟩
        have hfind := hlast
        dsimp only [batchEndCall] at hfind
        rw [hstart] at hfind
        dsimp only [Option.bind_some] at hfind
        obtain ⟨hlim,htrue,hprev⟩ := freyaPageFirstMatch _ _ last hfind
        have hafter : call<last := by
          have h := htrue
          simp (config := { iota := false }) only [Bool.and_eq_true,decide_eq_true_eq] at h
          exact h.1
        have hlo : call+N≤last := by
          by_contra h
          have ha : last-call<N := by omega
          obtain ⟨hit,hactive⟩ := hbefore (last-call) ha
          have he : call+(last-call)=last := by omega
          rw [he] at hit hactive
          simp (config := { iota := false }) only [hit,hactive,ne_eq,not_true_eq_false,decide_false,Bool.not_true,
            Bool.or_false,Bool.and_false] at htrue
          contradiction
        have hhi : last≤call+N := by
          by_contra h
          apply hprev (call+N) (by omega)
          have hcall : call<call+N := by omega
          simp (config := { iota := false }) only [hcall,decide_true,Bool.true_and,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq]
          exact hend
        have he : last=call+N := by omega
        simpa (config := { iota := false }) only [he] using hlast
      have freyaBatchTagDifference (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (b : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (h : freyaBatchTag q O b z=1) :
          ∃ x y c i,invocation q O z.1 z.2 b=some (false,x,y,c,i) := by
        clear * - q O b z h freyaBatchTag

        dsimp only [freyaBatchTag] at h
        cases hi : invocation q O z.1 z.2 b with
        | none => rw [hi] at h; cases h
        | some t =>
          obtain ⟨bit,x,y,c,i⟩ := t
          cases bit with
          | false => exact ⟨x,y,c,i,rfl⟩
          | true => rw [hi] at h; cases h
      have freyaInsideAdvanceFalse (q : Raw) (s : State q)
          (hi : (advance q s).iteration=s.iteration) (ha : active (advance q s)=true) : False := by
        clear * - q s hi ha freyaAdvanceLeaves

        rcases freyaAdvanceLeaves q s with h|h
        · exact h hi
        · rw [h] at ha
          contradiction
      have freyaFullGradientInitial {d m : ℕ} (n : ℕ) (f : Fin m → Space d → ℝ)
          (labels : List (Fin m)) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
          freyaFullGradientInvariant f (fullInitial n labels x clock rows firstID) := by
        clear * - d m n f labels x clock rows firstID freyaFullGradientInvariant

        constructor
        · change 0+((List.range labels.length).map (contribution f labels x)).sum=
            (labels.map fun i => gradient (f i) x).sum
          rw [zero_add]
          congr 1
          apply List.ext_getElem (by simp (config := { iota := false }))
          intro b hb hb'
          have hbl : b<labels.length := by simpa (config := { iota := false }) only [List.length_map,List.length_range] using hb
          simp (config := { iota := false }) only [List.getElem_map,List.getElem_range]
          dsimp only [contribution]
          rw [getElem?_pos labels b hbl]
          rfl
        · intro i job hj
          change dispatch (Sum.inl x) clock (firstID+i.val) _=some job at hj
          dsimp only [dispatch] at hj
          obtain ⟨j,_,he⟩ := Option.map_eq_some_iff.mp hj
          cases he
          rfl
      have freyaFullGradientUpdate {d m n : ℕ} (s : FullState d m n)
          (hne : s.remaining≠[]) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r,legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i')
          (h : freyaFullGradientInvariant f s) :
          let t := fullUpdate s (reply (fullQuery s))
          t.original=s.original ∧ t.point=s.point ∧ freyaFullGradientInvariant f t := by
        clear * - d m n s hne f τ reply hr hservice h freyaFullGradientInvariant

        classical
        have hisEmpty : s.remaining.isEmpty=false := by
          cases he : s.remaining with
          | nil => exact False.elim (hne he)
          | cons b bs => rfl
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hquery : fullQuery s=some r := by
          dsimp only [fullQuery]
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only [pendingRequest]
          have hex : ∃ i,s.pending i≠none := by
            obtain ⟨i,j,hj⟩ := hr.1
            change s.pending i=some j at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,time,hjob,hreply,hclock,_⟩ := hservice r hr
        change s.pending i=some job at hjob
        change s.clock≤time at hclock
        have hkind := h.2 i job hjob
        have hvalue : jobValue f job=gradient (f job.component) s.point := by
          dsimp only [jobValue]
          rw [hkind]
        let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let total := if found.isSome then s.sum+jobValue f job else s.sum
        have hsum : total+(rem.map (contribution f s.original s.point)).sum=
            (s.original.map fun j => gradient (f j) s.point).sum := by
          cases hf : found with
          | none => simpa (config := { iota := false }) only [rem,total,hf,Option.elim_none,Option.isSome_none,Bool.false_eq_true,ite_false] using h.1
          | some b =>
            have hb : b∈s.remaining := List.mem_of_find?_eq_some hf
            have hlabel : s.original[b]?=some job.component := by
              simpa (config := { iota := false }) only [decide_eq_true_eq] using List.find?_some hf
            have hc : contribution f s.original s.point b=jobValue f job := by
              dsimp only [contribution]
              rw [hlabel]
              exact hvalue.symm
            dsimp only [rem,total]
            rw [hf]
            simp (config := { iota := false }) only [Option.elim_some,Option.isSome_some,ite_true]
            rw [add_assoc,← hc,List.sum_map_erase (contribution f s.original s.point) hb]
            exact h.1
        let next := dispatch (Sum.inl s.point) time s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n := {s with
          remaining := rem
          sum := total
          pending := Function.update s.pending i next
          clock := time
          nextID := s.nextID+1}
        have ht : fullUpdate s (reply (fullQuery s))=t := by
          rw [hquery,hreply]
          delta fullUpdate
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
        dsimp only
        rw [ht]
        refine ⟨rfl,rfl,hsum,?_⟩
        intro k old hold
        change Function.update s.pending i next k=some old at hold
        by_cases hk : k=i
        · subst k
          rw [Function.update_self] at hold
          change dispatch (Sum.inl s.point) time s.nextID _=some old at hold
          dsimp only [dispatch] at hold
          obtain ⟨j,_,he⟩ := Option.map_eq_some_iff.mp hold
          cases he
          rfl
        · rw [Function.update_of_ne hk] at hold
          exact h.2 k old hold
      let freyaPageGradientInvariant (q : Raw) (f : Fin q.m → Space q.d → ℝ) (s : State q) : Prop :=
        ∀ first c,s.phase=Phase.full first c →
          c.original=List.ofFn id ∧ c.point=s.x ∧ freyaFullGradientInvariant f c
      have freyaFullGradientComplete {d m n : ℕ} (f : Fin m → Space d → ℝ)
          (hf : ∀ i,Differentiable ℝ (f i)) (c : FullState d m n)
          (horig : c.original=List.ofFn id) (h : freyaFullGradientInvariant f c)
          (he : c.remaining=[]) : fullResult c=gradient (objective f) c.point := by
        clear * - d m n f hf c horig h he freyaFullGradientInvariant

        have hsum := h.1
        rw [he,List.map_nil,List.sum_nil,add_zero,horig] at hsum
        dsimp only [fullResult]
        rw [horig,List.length_ofFn,hsum]
        rw [List.map_ofFn,List.sum_ofFn]
        exact (LongTails.Proofs.FreyaSerialAnalysis.objective_gradient f hf c.point).symm
      have freyaControlRecord (q : Raw) (s t : State q) (h : freyaControl s=freyaControl t) :
          s={t with seed:=s.seed,selected:=s.selected} := by
        clear * - q s t h freyaControl

        cases s
        cases t
        dsimp only [freyaControl] at h
        simp (config := { iota := false }) only [Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
        rfl
      let freyaPastRelation {q : Raw} (k : ℕ) (s t : State q) : Prop :=
        freyaControl s=freyaControl t ∨ k<s.iteration ∧ k<t.iteration
      have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
          MeasurableSingletonClass (Option α) := by
        clear * - α freyaDevelopmentOptionElimMeas

        constructor
        intro x
        let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
        have he : {x}=encode ⁻¹' {encode x} := by
          ext y
          cases x <;> cases y <;> simp (config := { iota := false }) [encode]
        have hsingleton : MeasurableSet {encode x} := by
          rw [measurableSet_sum_iff]
          cases x <;> constructor <;> simp (config := { iota := false }) [encode]
          · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
            rw [he]
            exact MeasurableSet.empty
          · rename_i b
            have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
            rw [he]
            exact measurableSet_singleton _
        rw [he]
        exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
          hsingleton
      have freyaPageInvocationHistoryMeas (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
          Measurable[historyBefore q O batch]
            (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => invocation q O z.1 z.2 batch) := by
        clear * - q O batch freyaHistoryView

        exact measurable_fst.comp (show Measurable[historyBefore q O batch]
          (freyaHistoryView q O batch) from Measurable.of_comap_le le_rfl)
      have freyaOptionParamMeas {Ω α β : Type} [MeasurableSpace Ω]
          [MeasurableSpace α] [MeasurableSpace β]
          (o : Ω → Option α) (ho : Measurable o) (b : Ω → β) (hb : Measurable b)
          (f : Ω × α → β) (hf : Measurable f) :
          Measurable (fun z => (o z).elim (b z) (fun a => f (z,a))) := by
        clear * - Ω α β o ho b hb f hf freyaDevelopmentOptionElimMeas

        have he := (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr).comp ho
        have hs := ((hb.comp measurable_fst).sumElim hf).comp
          ((MeasurableEquiv.prodSumDistrib Ω Unit α).measurable.comp (measurable_id.prodMk he))
        convert hs using 1
        funext z
        dsimp only [Function.comp_def,id_eq]
        cases o z <;> rfl'
      have freyaFullCodeMeas {d m n : ℕ} : Measurable (@freyaFullCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaDifferenceCodeMeas {d m n : ℕ} : Measurable (@freyaDifferenceCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaPhaseCodeMeas {d m n : ℕ} : Measurable (@freyaPhaseCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaStateCodeMeas (q : Raw) : Measurable (@freyaStateCode q) :=
        Measurable.of_comap_le le_rfl
      have freyaPhaseFullMeas {d m n : ℕ} :
          Measurable (fun z : Bool × FullState d m n => Phase.full z.1 z.2) := by
        clear * - d m n freyaPhaseCode

        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inl
      have freyaPhaseDifferenceMeas {d m n : ℕ} :
          Measurable (Phase.difference : DifferenceState d m n → Phase d m n) := by
        clear * - d m n freyaPhaseCode

        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inr
      have freyaStateConstructMeas {Ω : Type} [MeasurableSpace Ω] (q : Raw)
          (seed : Ω → Seed q.K) (it : Ω → ℕ) (x g selected : Ω → Space q.d)
          (clock : Ω → ℝ≥0) (id : Ω → ℕ) (phase : Ω → Phase q.d q.m q.n)
          (hseed : Measurable seed) (hit : Measurable it) (hx : Measurable x) (hg : Measurable g)
          (hselected : Measurable selected) (hc : Measurable clock) (hid : Measurable id) (hp : Measurable phase) :
          Measurable (fun z => (⟨seed z,it z,x z,g z,selected z,clock z,id z,phase z⟩ : State q)) := by
        clear * - Ω q seed it x g selected clock id phase hseed hit hx hg hselected hc hid hp freyaStateCode

        change Measurable[_,MeasurableSpace.comap freyaStateCode inferInstance] _
        rw [measurable_comap_iff]
        exact hseed.prodMk (hit.prodMk (hx.prodMk (hg.prodMk (hselected.prodMk (hc.prodMk (hid.prodMk hp))))))
      have freyaPendingRequestMeas {d m n : ℕ} :
          Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) => pendingRequest z.1 z.2) := by
        clear * - d m n freyaDevelopmentOptionElimMeas freyaOptionSomeMeas

        classical
        have hc : Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) =>
            (⟨z.1,z.2⟩ : Request d m n)) := by
          change Measurable[_,MeasurableSpace.comap (fun r : Request d m n => (r.clock,r.pending)) inferInstance] _
          rw [measurable_comap_iff]
          exact measurable_id
        have hsome := freyaOptionSomeMeas.comp hc
        have hn : MeasurableSet {o : Option (Job d m) | o ≠ none} := by
          have hi := freyaDevelopmentOptionElimMeas false (fun _ : Job d m => true) measurable_const
          convert hi (measurableSet_singleton true) using 1
          ext o
          cases o <;> simp (config := { iota := false })
        have he : MeasurableSet {z : ℝ≥0 × (Fin n → Option (Job d m)) | ∃ i, z.2 i ≠ none} := by
          convert MeasurableSet.iUnion (fun i : Fin n => hn.preimage ((measurable_pi_apply i).comp measurable_snd)) using 1
          ext z
          simp (config := { iota := false })
        exact hsome.ite he measurable_const
      have freyaFreshTapeEvent {α : Type} [MeasurableSpace α]
          (μ : Measure α) [IsProbabilityMeasure μ] (i : ℕ)
          (E : Set (ℕ → α)) (hE : MeasurableSet E)
          (hinvariant : ∀ t a, Function.update t i a∈E ↔ t∈E)
          (U : Set α) (hU : MeasurableSet U) :
          (Measure.infinitePi fun _ : ℕ => μ) (E∩{t | t i∈U})=
            (Measure.infinitePi fun _ : ℕ => μ) E*μ U := by
        clear * - α μ i E hE hinvariant U hU freyaInfiniteResample

        have hr := freyaInfiniteResample μ i
        have hm : MeasurableSet (E∩{t : ℕ → α | t i∈U}) :=
          hE.inter ((measurable_pi_apply i) hU)
        have he : (fun z : (ℕ → α) × α => Function.update z.1 i z.2) ⁻¹'
            (E∩{t | t i∈U})=E×ˢU := by
          ext z
          simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq,
            Set.mem_prod,Function.update_self,hinvariant]
        conv_lhs => rw [← hr.map_eq]
        rw [Measure.map_apply hr.measurable hm,he,Measure.prod_prod]
      have freyaFullNextMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) : Measurable (freyaFullNext q f) := by
        clear * - q f freyaFullNext freyaGradientMeas

        have hx : Measurable (fun p : Space q.d × Space q.d => p.1-q.η • p.2) :=
          measurable_fst.sub (measurable_snd.const_smul q.η)
        exact hx.prodMk ((freyaGradientMeas q.d (objective f)).comp hx)
      have freyaDiffNextMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (v : Fin q.S → Fin q.m) : Measurable (freyaDiffNext q f v) := by
        clear * - q f v freyaDiffNext freyaGradientMeas

        have hx : Measurable (fun p : Space q.d × Space q.d => p.1-q.η • p.2) :=
          measurable_fst.sub (measurable_snd.const_smul q.η)
        have hsum := Finset.measurable_sum Finset.univ (fun j _ =>
          ((freyaGradientMeas q.d (f (v j))).comp hx).sub
            ((freyaGradientMeas q.d (f (v j))).comp measurable_fst))
        exact hx.prodMk (measurable_snd.add (hsum.const_smul ((q.S : ℝ)⁻¹)))
      let freyaHRReplayState (d _m : ℕ) :=
        List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → freyaHRPair d)
      let freyaHRRemainingAfter (m : ℕ) (r : List ℕ) (i : Fin m) : List ℕ :=
        (freyaHRFound m r i).elim r (fun a => r.erase a)
      let freyaHRAccepts (m : ℕ) (r : List ℕ) (i : Fin m) : Bool := (freyaHRFound m r i).isSome
      let freyaHREventFromJob {d m : ℕ} (j : Job d m) (v : Space d) : freyaHREvent d m :=
        Sum.inr (j.component, freyaHRFullKind j.kind, freyaHRPointOfKind j.kind, v)
      have freyaHRMeasurable_replyValue (d n : ℕ) : Measurable (@freyaHRReplyValue d n) :=
        freyaDevelopmentOptionElimMeas 0 _ measurable_snd.snd.snd
      have freyaHRDifferencePoint_advance (q : Raw) (s : State q) : freyaHRDifferencePoint (advance q s) := by
        clear * - q s freyaHRDifferencePoint

        delta advance
        split
        · intro c h; cases h
        · dsimp only
          cases hbit : refreshAt s.seed s.iteration <;> simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true]
          · intro c h
            have he := Phase.difference.inj h
            rw [← he]
            rfl
          · intro c h; cases h
      have freyaPageTraceSeed (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
          (trace q O seed ω k).seed = seed := by
        clear * - q O seed ω k freyaPageUpdateSeed

        induction k with
        | zero => rfl
        | succ k ih =>
          change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
          rw [freyaPageUpdateSeed,ih]
      have freyaPageIterationMonotone (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          Monotone (fun k => (trace q O seed ω k).iteration) := by
        clear * - q O seed ω freyaPageUpdateIteration

        apply monotone_nat_of_le_succ
        intro k
        have h := freyaPageUpdateIteration q (trace q O seed ω k)
          (replyAt q O seed ω k (query q (trace q O seed ω k)))
        change (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration ∨
          (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration+1 at h
        omega
      have freyaPageBatchProgress (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
          (hS : 0 < q.S) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (batch firstID call : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hstart : batchStartCall q O seed ω batch = some call)
          (hphase : (trace q O seed ω call).phase = Phase.difference
            (differenceInitial q.n q.S x y clock (seed.1 batch) firstID)) :
          let D := fun k : ℕ => if hk : k < q.S then
            (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
              (fun i => gradient (f i) x-gradient (f i) y) else 0
          ∀ a, a < q.S → ∃ c : DifferenceState q.d q.m q.n,
            (trace q O seed ω (call+a)).phase = Phase.difference c ∧
            (trace q O seed ω (call+a)).iteration = batch ∧
            c.target=q.S ∧ c.count=a ∧ c.x=x ∧ c.y=y ∧ c.rows=seed.1 batch ∧
            c.nextID=firstID+q.n+a ∧ c.sum=∑ k ∈ Finset.range a, D k ∧
            ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (x,y) ∧
              batchLabels q seed batch job.id=some job.component := by
        clear * - q hm hn hS f τ O seed ω hservice batch firstID call x y clock hstart hphase freyaDifferenceLiveStep freyaPageDifferenceQuery freyaPageDifferenceContinue freyaPageBatchStartFacts freyaPageCompletedJobEq

        classical
        dsimp only
        let D := fun k : ℕ => if hk : k < q.S then
            (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
              (fun i => gradient (f i) x-gradient (f i) y) else 0
        change ∀ a, a < q.S → ∃ c : DifferenceState q.d q.m q.n,
            (trace q O seed ω (call+a)).phase = Phase.difference c ∧
            (trace q O seed ω (call+a)).iteration = batch ∧
            c.target=q.S ∧ c.count=a ∧ c.x=x ∧ c.y=y ∧ c.rows=seed.1 batch ∧
            c.nextID=firstID+q.n+a ∧ c.sum=∑ k ∈ Finset.range a, D k ∧
            ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (x,y) ∧
              batchLabels q seed batch job.id=some job.component
        intro a
        induction a with
        | zero =>
          intro _
          refine ⟨differenceInitial q.n q.S x y clock (seed.1 batch) firstID,?_,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
          · simpa (config := { iota := false }) only [Nat.add_zero] using hphase
          · simpa (config := { iota := false }) only [Nat.add_zero] using (freyaPageBatchStartFacts q O seed ω batch call hstart).2.1
          · change firstID+q.n=firstID+q.n+0
            omega
          · exact (Finset.sum_range_zero D).symm
          · intro i
            obtain ⟨b,hb⟩ : ∃ b : Fin q.m, labelAt (seed.1 batch (firstID+i.val)) q.m=some b := by
              delta labelAt
              simp (config := { iota := false }) only [hm,dite_true]
              exact ⟨_,rfl⟩
            let job : Job q.d q.m := ⟨b,Sum.inr (x,y),clock,firstID+i.val⟩
            refine ⟨job,?_,le_rfl,?_,rfl,hb⟩
            · change (if q.S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
                (labelAt (seed.1 batch (firstID+i.val)) q.m))=some job
              rw [ite_eq_right (by omega),hb]
              rfl
            · exact le_add_of_nonneg_right zero_le
        | succ a ih =>
          intro ha
          have haS : a<q.S := by omega
          obtain ⟨c,hc,hit,htarget,hcount,hx,hy,hrows,hid,hsum,hpending⟩ := ih haS
          have hp : ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
            intro i
            obtain ⟨job,hj,hs,ht,hk,_⟩ := hpending i
            rw [hx,hy]
            exact ⟨job,hj,hs,ht,hk⟩
          obtain ⟨i,job,time,next,hjob,hquery,hreply,hclock,hnid,hnkind,hnstart,hnlabel,hnext,hpnext⟩ :=
            freyaDifferenceLiveStep hm hn c f τ
              (fun r => replyAt q O seed ω (call+a) (0,r))
              (hservice (call+a)).2 (by omega) hp
          let t := differenceUpdate c (replyAt q O seed ω (call+a) (0,differenceQuery c))
          have ht := hnext
          change t = _ at ht
          have hqueryPage := freyaPageDifferenceQuery q _ c hc
          have hactive : t.count<t.target := by rw [ht]; dsimp only; omega
          have hcontinue := freyaPageDifferenceContinue q _ c
            (replyAt q O seed ω (call+a) (0,differenceQuery c)) hc hactive
          have hupdate : trace q O seed ω (call+(a+1)) =
              update q (trace q O seed ω (call+a))
                (replyAt q O seed ω (call+a) (0,differenceQuery c)) := by
            rw [← Nat.add_assoc]
            rw [trace_succ]
            rw [hqueryPage]
          obtain ⟨old,hold,_,_,hkind,hlabel⟩ := hpending i
          have heq : old=job := Option.some.inj (hold.symm.trans hjob)
          subst old
          have hcompleted := freyaPageCompletedJobEq q O seed ω batch call ⟨a,haS⟩ hstart
            c hc hquery i job time (jobValue f job) hjob hreply
          have hD : D a=jobValue f job := by
            dsimp only [D]
            rw [dite_eq_left haS]
            delta completedLabels
            rw [hcompleted]
            dsimp only [Option.map,Option.elim]
            delta jobValue
            rw [hkind]
          refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · rw [hupdate]; exact hcontinue.1
          · rw [hupdate,hcontinue.2]; exact hit
          · rw [ht]; exact htarget
          · rw [ht]; dsimp only; omega
          · rw [ht]; exact hx
          · rw [ht]; exact hy
          · rw [ht]; exact hrows
          · rw [ht]; dsimp only; omega
          · rw [ht]; dsimp only; rw [hsum,Finset.sum_range_succ,hD]
          · intro k
            obtain ⟨old,hold,hs,htime,hkind'⟩ := hpnext k
            refine ⟨old,?_,?_,?_,?_,?_⟩
            · rw [ht]; exact hold
            · rw [ht]; exact hs
            · rw [ht]; exact htime
            · simpa (config := { iota := false }) only [hx,hy] using hkind'
            · by_cases hk : k=i
              · subst k
                rw [Function.update_self] at hold
                have heq : next=old := Option.some.inj hold
                subst old
                change labelAt (seed.1 batch next.id) q.m=some next.component
                rw [hnid,← hrows]
                exact hnlabel
              · rw [Function.update_of_ne hk] at hold
                obtain ⟨old',hold',_,_,_,hl⟩ := hpending k
                have heq : old=old' := Option.some.inj (hold.symm.trans hold')
                subst old'
                exact hl
      have freyaPagePhaseSafety (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          let Safe := fun s : State q =>
            (∀ first c,s.phase=Phase.full first c →
              c.original.length=q.m ∧ c.remaining≠[] ∧
              (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
            (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
              ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
                (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
            s.iteration≤rounds q
          ∀ k,Safe (trace q O seed ω k) := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaDifferenceLiveStep freyaPageDifferenceQuery freyaDifferenceInitialSafe freyaPageFullQuery freyaFullSafeUpdate freyaFullInitialSafe

        classical
        let Safe := fun s : State q =>
            (∀ first c,s.phase=Phase.full first c →
              c.original.length=q.m ∧ c.remaining≠[] ∧
              (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
            (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
              ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
                (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
            s.iteration≤rounds q
        change ∀ k,Safe (trace q O seed ω k)
        have hfull (s : State q) (first : Bool) (c : FullState q.d q.m q.n)
            (hp : s.phase=Phase.full first c) (h1 : c.original.length=q.m) (h2 : c.remaining≠[])
            (h3 : ∀ b ∈ c.remaining,b<c.original.length)
            (h4 : legalRequest τ ⟨c.clock,c.pending⟩) (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first' c' he
            rw [hp] at he
            cases he
            exact ⟨h1,h2,h3,h4⟩
          · intro c' he
            rw [hp] at he
            cases he
        have hdiff (s : State q) (c : DifferenceState q.d q.m q.n)
            (hp : s.phase=Phase.difference c) (h1 : c.target=q.S) (h2 : c.count<c.target)
            (h3 : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y))
            (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first c' he
            rw [hp] at he
            cases he
          · intro c' he
            rw [hp] at he
            cases he
            exact ⟨h1,h2,h3⟩
        have hhalt (s : State q) (hp : s.phase=Phase.halted) (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first c he; rw [hp] at he; cases he
          · intro c he; rw [hp] at he; cases he
        have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
          intro he
          have hh := congrArg List.length he
          simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
          omega
        have hadvance (s : State q) (hi : s.iteration≤rounds q) : Safe (advance q s) := by
          delta advance
          split
          · exact hhalt _ rfl hi
          · rename_i hlt
            dsimp only
            by_cases hrefresh : refreshAt s.seed s.iteration=true
            · rw [ite_eq_left hrefresh]
              have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels
                (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID τ
              apply hfull _ false _ rfl (List.length_ofFn) hf.1 hf.2.1 hf.2.2
              dsimp only
              omega
            · rw [ite_eq_right hrefresh]
              apply hdiff _ _ rfl rfl hS
                (freyaDifferenceInitialSafe hm q.S hS _ _ _ _ _ τ)
              dsimp only
              omega
        have hinit : Safe (initial q seed) := by
          have hp : (initial q seed).phase=Phase.full true
              (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
            delta initial
            dsimp only
            rw [ite_eq_right (by omega)]
          have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels q.x0 0 (seed.1 0) 0 τ
          exact hfull _ true _ hp (List.length_ofFn) hf.1 hf.2.1 hf.2.2 (Nat.zero_le _)
        intro k
        induction k with
        | zero => exact hinit
        | succ k ih =>
          let s := trace q O seed ω k
          change Safe s at ih
          change Safe (update q s (replyAt q O seed ω k (query q s)))
          cases hs : s.phase with
          | halted =>
            have hu : update q s (replyAt q O seed ω k (query q s))=s := by delta update; rw [hs]
            rw [hu]
            exact ih
          | full first c =>
            obtain ⟨hlen,hne,hb,hl⟩ := ih.1 first c hs
            have hquery := freyaPageFullQuery q s first c hs
            rw [hquery]
            let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
            have ht := freyaFullSafeUpdate c hne hb f τ (fun r => replyAt q O seed ω k (0,r)) hl (hservice k).2
            change t.original=c.original ∧ _ at ht
            delta update
            rw [hs]
            dsimp only
            change Safe (if t.remaining.isEmpty then advance q _ else _)
            by_cases he : t.remaining.isEmpty=true
            · rw [ite_eq_left he]
              apply hadvance
              exact ih.2.2
            · rw [ite_eq_right he]
              have htne : t.remaining≠[] := by intro hz; apply he; rw [hz]; rfl
              exact hfull _ first t rfl (ht.1 ▸ hlen) htne ht.2.1 (ht.2.2 htne) ih.2.2
          | difference c =>
            obtain ⟨htarget,hcount,hp⟩ := ih.2.1 c hs
            have hquery := freyaPageDifferenceQuery q s c hs
            rw [hquery]
            obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,hpn⟩ :=
              freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hp
            delta update
            rw [hs]
            dsimp only
            rw [ht]
            dsimp only
            by_cases he : c.target≤c.count+1
            · rw [ite_eq_left he]
              apply hadvance
              exact ih.2.2
            · rw [ite_eq_right he]
              refine hdiff _ _ rfl ?_ ?_ ?_ ?_
              · exact htarget
              · change c.count+1<c.target
                omega
              · exact hpn
              · exact ih.2.2
      have freyaBatchEndFacts (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          a<e ∧ e≤eventLimit q ∧
            (∀ r,a≤r → r<e → (trace q O seed ω r).iteration=b ∧ active (trace q O seed ω r)=true) ∧
            ((trace q O seed ω e).iteration≠b ∨ active (trace q O seed ω e)=false) := by
        clear * - q O seed ω b a e hs he freyaPageFirstMatch freyaPageBatchStartFacts

        have hstart := freyaPageBatchStartFacts q O seed ω b a hs
        dsimp only [batchEndCall] at he
        rw [hs] at he
        dsimp only [Option.bind_some] at he
        obtain ⟨hlim,htrue,hprev⟩ := freyaPageFirstMatch _ _ e he
        have hafter : a<e := by
          have hh := htrue
          simp (config := { iota := false }) only [Bool.and_eq_true,decide_eq_true_eq] at hh
          exact hh.1
        refine ⟨hafter,by omega,?_,?_⟩
        · intro r har hre
          by_cases hr : r=a
          · subst r; exact ⟨hstart.2.1,hstart.2.2.1⟩
          · have hlt : a<r := by omega
            have hh := hprev r hre
            have hit : (trace q O seed ω r).iteration=b := by
              by_contra h
              apply hh
              have hd : decide ((trace q O seed ω r).iteration≠b)=true := decide_eq_true_eq.mpr h
              simp (config := { iota := false }) only [hlt,hd,decide_true,Bool.true_and,Bool.true_or]
            refine ⟨hit,?_⟩
            cases ha : active (trace q O seed ω r) with
            | false =>
              apply False.elim
              apply hh
              simp (config := { iota := false }) only [hlt,decide_true,Bool.true_and,ha,Bool.not_false,Bool.or_true]
            | true => rfl
        · simpa (config := { iota := false }) only [hafter,decide_true,Bool.true_and,Bool.or_eq_true,
            Bool.not_eq_true',decide_eq_true_eq] using htrue
      have freyaInvocationOfStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a : ℕ)
          (hs : batchStartCall q O seed ω b=some a) :
          ∃ full x y clock firstID,invocation q O seed ω b=some (full,x,y,clock,firstID) := by
        clear * - q O seed ω b a hs freyaPageBatchStartFacts

        have ha := (freyaPageBatchStartFacts q O seed ω b a hs).2.2.1
        dsimp only [invocation]
        rw [hs]
        dsimp only [Option.bind_some]
        cases hp : (trace q O seed ω a).phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c => exact ⟨true,c.point,c.point,c.clock,c.nextID-q.n,rfl⟩
        | difference c => exact ⟨false,c.x,c.y,c.clock,c.nextID-q.n,rfl⟩
      have freyaInsideUpdate (q : Raw) (s : State q) (r : Reply q.d q.n)
          (hi : (update q s r).iteration=s.iteration) (ha : active (update q s r)=true) :
          freyaInside (update q s r)=freyaInside s := by
        clear * - q s r hi ha freyaInside freyaInsideAdvanceFalse

        dsimp only [update] at hi ha ⊢
        cases hp : s.phase with
        | halted => rfl
        | full first c =>
          rw [hp] at hi ha
          dsimp only at hi ha ⊢
          by_cases he : (fullUpdate c r).remaining.isEmpty=true
          · rw [ite_eq_left he] at hi ha ⊢
            exact False.elim (freyaInsideAdvanceFalse q _ hi ha)
          · rw [ite_eq_right he]
            dsimp only [freyaInside]
            rw [hp]
        | difference c =>
          rw [hp] at hi ha
          dsimp only at hi ha ⊢
          by_cases he : (differenceUpdate c r).target≤(differenceUpdate c r).count
          · rw [ite_eq_left he] at hi ha ⊢
            exact False.elim (freyaInsideAdvanceFalse q _ hi ha)
          · rw [ite_eq_right he]
            dsimp only [freyaInside]
            rw [hp]
      have freyaPageGradientAdvance (q : Raw) (f : Fin q.m → Space q.d → ℝ) (s : State q) :
          freyaPageGradientInvariant q f (advance q s) := by
        clear * - q f s freyaFullGradientInitial freyaPageGradientInvariant

        intro first c hp
        dsimp only [advance] at hp ⊢
        split at hp
        · contradiction
        · rename_i hi
          rw [ite_eq_right hi]
          dsimp only at hp ⊢
          split at hp
          · have he := Phase.full.inj hp
            rw [← he.2]
            exact ⟨rfl,rfl,freyaFullGradientInitial q.n f _ _ _ _ _⟩
          · contradiction
      have freyaPageGradientInitial (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (seed : Seed q.K) : freyaPageGradientInvariant q f (initial q seed) := by
        clear * - q f seed freyaFullGradientInitial freyaPageGradientInvariant

        intro first c hp
        dsimp only [initial] at hp ⊢
        split at hp
        · contradiction
        · have he := Phase.full.inj hp
          rw [← he.2]
          exact ⟨rfl,rfl,freyaFullGradientInitial q.n f _ _ _ _ _⟩
      have freyaQueryControl (q : Raw) (s t : State q) (h : freyaControl s=freyaControl t) :
          query q s=query q t := by
        clear * - q s t h freyaControl freyaControlRecord

        rw [freyaControlRecord q s t h]
        rfl
      have freyaPastAdvance (q : Raw) (k : ℕ) (s : State q)
          (new : Seed q.K) (p : Space q.d) (hrows : new.1=s.seed.1)
          (hbits : ∀ j<k,new.2.1 j=s.seed.2.1 j) :
          freyaPastRelation k (advance q {s with seed:=new,selected:=p}) (advance q s) := by
        clear * - q k s new p hrows hbits freyaControl freyaPastRelation

        dsimp only [freyaPastRelation,advance]
        by_cases hstop : rounds q≤s.iteration
        · rw [ite_eq_left hstop,ite_eq_left hstop]; exact Or.inl rfl
        · rw [ite_eq_right hstop,ite_eq_right hstop]
          by_cases hi : s.iteration<k
          · left
            have hb : refreshAt new s.iteration=refreshAt s.seed s.iteration := hbits _ hi
            dsimp only [freyaControl]
            rw [hb,hrows]
          · right
            dsimp only
            constructor <;> omega
      have freyaLabelAtMeas (m : ℕ) : Measurable (fun row : ChoiceRow => labelAt row m) := by
        clear * - m freyaOptionSingleton

        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        by_cases hm : 0<m
        · let g : Fin (m-1+1) → Option (Fin m) := fun i => some ⟨i.val,by have := i.isLt; omega⟩
          have hg : Measurable g := measurable_of_countable g
          have he : Measurable (fun row : ChoiceRow => row (m-1)) := measurable_pi_apply (m-1)
          convert hg.comp he using 1
          funext row
          delta labelAt
          rw [dite_eq_left hm]
          rfl
        · delta labelAt
          simp (config := { iota := false }) only [hm,dite_false]
          exact measurable_const
      have freyaDispatchMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (kind : Ω → JobKind d) (clock : Ω → ℝ≥0) (id : Ω → ℕ)
          (label : Ω → Option (Fin m)) (hk : Measurable kind) (hc : Measurable clock)
          (hi : Measurable id) (hl : Measurable label) :
          Measurable (fun z => dispatch (kind z) (clock z) (id z) (label z)) := by
        clear * - Ω d m kind clock id label hk hc hi hl freyaOptionSomeMeas freyaOptionParamMeas

        have hb : Measurable (fun z : Ω × Fin m =>
            some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) := by
          apply freyaOptionSomeMeas.comp
          change Measurable[_,MeasurableSpace.comap
            (fun j : Job d m => (j.component,j.kind,j.started,j.id)) inferInstance]
            (fun z : Ω × Fin m => (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m))
          rw [measurable_comap_iff]
          exact (measurable_snd.prodMk ((hk.comp measurable_fst).prodMk
            ((hc.comp measurable_fst).prodMk (hi.comp measurable_fst))))
        have h := freyaOptionParamMeas label hl (fun _ => none) measurable_const
          (fun z : Ω × Fin m => some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) hb
        convert h using 1
        funext z
        delta dispatch
        cases label z <;> rfl
      have freyaSelectedLabelFixedMeas {m : ℕ} (labels : List (Fin m)) (rem : List ℕ) :
          Measurable (fun row : ChoiceRow => selectedLabel labels rem row) := by
        clear * - m labels rem freyaOptionSingleton

        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        cases rem with
        | nil => exact measurable_const
        | cons a rem =>
          let g := fun i : Fin (rem.length+1) => labels[(a::rem).get i]?
          have he : Measurable (fun row : ChoiceRow => row rem.length) := measurable_pi_apply rem.length
          have h := (measurable_of_countable g).comp he
          convert h using 1
          funext row
          delta selectedLabel chooseRemaining
          simp (config := { iota := false }) only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,dite_false,
            Option.bind_some]
          rfl
      have freyaPhaseParamMeas {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {d m n : ℕ}
          (p : Ω → Phase d m n) (hp : Measurable p) (b : Ω → β) (hb : Measurable b)
          (full : Ω × (Bool × FullState d m n) → β) (hfull : Measurable full)
          (diff : Ω × DifferenceState d m n → β) (hdiff : Measurable diff) :
          Measurable (fun z => (p z).casesOn (motive := fun _ => β) (fun first c => full (z,first,c))
            (fun c => diff (z,c)) (b z)) := by
        clear * - Ω β d m n p hp b hb full hfull diff hdiff freyaPhaseCodeMeas

        have hi := (hfull.sumElim hdiff).comp
          (MeasurableEquiv.prodSumDistrib Ω (Bool × FullState d m n) (DifferenceState d m n)).measurable
        have ho := ((hb.comp measurable_fst).sumElim hi).comp
          (MeasurableEquiv.prodSumDistrib Ω Unit ((Bool × FullState d m n) ⊕ DifferenceState d m n)).measurable
        have h := ho.comp (measurable_id.prodMk (freyaPhaseCodeMeas.comp hp))
        convert h using 1
        funext z
        dsimp only [Function.comp_def,id_eq]
        cases p z <;> rfl'
      have freyaActiveMeas (q : Raw) : Measurable (active : State q → Bool) := by
        clear * - q freyaPhaseCode freyaPhaseCodeMeas freyaStateCodeMeas

        have hphase := (freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd
        have h : Measurable (fun s : State q => Sum.elim (fun _ : Unit => false)
          (fun _ : (Bool × FullState q.d q.m q.n) ⊕ DifferenceState q.d q.m q.n => true)
            (freyaPhaseCode s.phase)) :=
          (measurable_const.sumElim measurable_const).comp (freyaPhaseCodeMeas.comp hphase)
        convert h using 1
        funext s
        dsimp only [active]
        cases s.phase <;> rfl
      have freyaFreshTapeEventProd {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
          (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
          (i : ℕ) (E : Set ((ℕ → α) × β)) (hE : MeasurableSet E)
          (hinvariant : ∀ t b a, (Function.update t i a,b)∈E ↔ (t,b)∈E)
          (U : Set α) (hU : MeasurableSet U) :
          ((Measure.infinitePi fun _ : ℕ => μ).prod ν) (E∩{z | z.1 i∈U})=
            ((Measure.infinitePi fun _ : ℕ => μ).prod ν) E*μ U := by
        clear * - α β μ ν i E hE hinvariant U hU freyaFreshTapeEvent

        have hm : MeasurableSet (E∩{z : (ℕ → α) × β | z.1 i∈U}) :=
          hE.inter (((measurable_pi_apply i).comp measurable_fst) hU)
        rw [Measure.prod_apply_symm hm]
        have he (b : β) : (Measure.infinitePi fun _ : ℕ => μ)
            ((fun t => (t,b)) ⁻¹' (E∩{z | z.1 i∈U}))=
            (Measure.infinitePi fun _ : ℕ => μ) ((fun t => (t,b)) ⁻¹' E)*μ U :=
          freyaFreshTapeEvent μ i ((fun t => (t,b)) ⁻¹' E)
            (hE.preimage (measurable_id.prodMk measurable_const))
            (fun t a => hinvariant t b a) U hU
        simp_rw [he]
        rw [lintegral_mul_const' _ _ (measure_ne_top μ U),← Measure.prod_apply_symm hE]
      have freyaPageDifferenceHistoryMeas (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
          MeasurableSet[historyBefore q O batch]
            {z | LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch} := by
        clear * - q O batch freyaDevelopmentOptionElimMeas freyaPageInvocationHistoryMeas

        let tag := fun a : Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) =>
          a.elim false (fun t => !t.1)
        have ht : Measurable tag := freyaDevelopmentOptionElimMeas false _
          ((measurable_of_countable (fun b : Bool => !b)).comp measurable_fst)
        have hi := ht.comp (freyaPageInvocationHistoryMeas q O batch)
        have he : {z | LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch}=
            {z : Seed q.K × ((k : ℕ) → O.Seed k) | tag (invocation q O z.1 z.2 batch)=true} := by
          ext z
          dsimp only [LongTails.Setups.FreyaIndependence.isDifferenceBatch,Set.mem_ofPred_eq]
          cases h : invocation q O z.1 z.2 batch with
          | none => simp (config := { iota := false }) [tag]
          | some a =>
            obtain ⟨b,x,y,t,id⟩ := a
            cases b <;> simp (config := { iota := false }) [tag]
        rw [he]
        exact hi (measurableSet_singleton true)
      have freyaDifferenceTagIff (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((a : ℕ) → O.Seed a)) (b : ℕ) :
          LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z b ↔ freyaBatchTag q O b z=1 := by
        clear * - q O z b freyaBatchTag freyaBatchTagDifference

        constructor
        · rintro ⟨x,y,c,i,h⟩
          dsimp only [freyaBatchTag]
          rw [h]
          rfl
        · exact freyaBatchTagDifference q O b z
      let freyaHRFinish {d m : ℕ} (s : freyaHRReplayState d m) (p : freyaHRPair d) : freyaHRReplayState d m :=
        (List.range m, 0, 0, p.2, s.2.2.2.2.1 + 1,
          Function.update s.2.2.2.2.2 s.2.2.2.2.1 p)
      let freyaHRReplayInitial (d m : ℕ) : freyaHRReplayState d m :=
        (List.range m, 0, 0, 0, 0, fun _ => (0, 0))
      have freyaCompletedFromMeas {d m n : ℕ} :
          Measurable (fun z : Option (Request d m n) × Reply d n =>
            z.1.elim none (fun r => z.2.elim none (fun a =>
              (r.pending a.1).elim none (fun job => if job.id=a.2.1 then some job else none)))) := by
        clear * - d m n freyaOptionSomeMeas freyaMeasurableSelect freyaJobCodeMeas freyaOptionParamMeas

        classical
        let Ω := Option (Request d m n) × Reply d n
        have hj : Measurable (fun z : ((Ω × Request d m n) × (Fin n × ℕ × ℝ≥0 × Space d)) × Job d m =>
            if z.2.id=z.1.2.2.1 then some z.2 else none) :=
          (freyaOptionSomeMeas.comp measurable_snd).ite
            (measurableSet_eq_fun (freyaJobCodeMeas.snd.snd.snd.comp measurable_snd) measurable_fst.snd.snd.fst)
            measurable_const
        have hr : Measurable (fun r : Request d m n => (r.clock,r.pending)) :=
          Measurable.of_comap_le le_rfl
        have hp : Measurable (fun z : (Ω × Request d m n) × (Fin n × ℕ × ℝ≥0 × Space d) => z.1.2.pending z.2.1) :=
          freyaMeasurableSelect _ measurable_snd.fst _
            (fun i => (measurable_pi_apply i).comp (hr.snd.comp measurable_fst.snd))
        have hi := freyaOptionParamMeas _ hp (fun _ => (none : Option (Job d m))) measurable_const _ hj
        have hm := freyaOptionParamMeas (fun z : Ω × Request d m n => z.1.2) measurable_fst.snd
          (fun _ => (none : Option (Job d m))) measurable_const _ hi
        have ho := freyaOptionParamMeas (fun z : Ω => z.1) measurable_fst
          (fun _ => (none : Option (Job d m))) measurable_const _ hm
        exact ho
      have freyaHRMeasurable_eventFromJob (d m : ℕ) :
          Measurable (fun z : Job d m × Space d => freyaHREventFromJob z.1 z.2) := by
        clear * - d m freyaJobCodeMeas freyaHRFullKind freyaHRPointOfKind freyaHREventFromJob

        have hf : Measurable (@freyaHRFullKind d) := measurable_const.sumElim measurable_const
        have hp : Measurable (@freyaHRPointOfKind d) := measurable_id.sumElim measurable_fst
        have hc := freyaJobCodeMeas.comp (measurable_fst : Measurable (fun z : Job d m × Space d => z.1))
        exact measurable_inr.comp (hc.fst.prodMk
          ((hf.comp hc.snd.fst).prodMk ((hp.comp hc.snd.fst).prodMk measurable_snd)))
      let freyaHRRawEvent {d m n : ℕ} (z : Option (Request d m n) × Reply d n) : freyaHREvent d m :=
        (freyaHRCompletedJob z).elim (Sum.inl ()) (fun j => freyaHREventFromJob j (freyaHRReplyValue z.2))
      let freyaHRCore {q : Raw} (s : State q) (path : ℕ → freyaHRPair q.d) : freyaHRReplayState q.d q.m :=
        Phase.casesOn s.phase
          (fun _ c => (c.remaining,0,c.sum,s.g,s.iteration,path))
          (fun c => (List.range q.m,c.count,c.sum,s.g,s.iteration,path))
          (List.range q.m,0,0,s.g,s.iteration,path)
      have freyaHRFullFields {d m n : ℕ} (c : FullState d m n) (i : Fin n) (j : Job d m)
          (time : ℝ≥0) (v : Space d) (ho : c.original = List.ofFn (fun i : Fin m => i))
          (hne : c.remaining ≠ []) (hj : c.pending i = some j) (ht : c.clock ≤ time) :
          let c' := fullUpdate c (some (i,j.id,time,v))
          c'.original = c.original ∧ c'.remaining = freyaHRRemainingAfter m c.remaining j.component ∧
            c'.sum = if freyaHRAccepts m c.remaining j.component then c.sum+v else c.sum := by
        clear * - d m n c i j time v ho hne hj ht freyaHRRemainingAfter freyaHRAccepts

        have he : c.remaining.isEmpty = false := by
          cases hr : c.remaining with
          | nil => exact False.elim (hne hr)
          | cons b bs => rfl
        dsimp only
        delta fullUpdate
        rw [he,ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl ht)]
        refine ⟨rfl,?_,?_⟩ <;> dsimp only
        · rw [ho]
        · rw [ho]
      have freyaHRDifferencePoint_trace (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (a : ℕ) :
          freyaHRDifferencePoint (trace q O seed ω a) := by
        clear * - q O seed ω a freyaHRDifferencePoint_update freyaHRDifferencePoint freyaHRDifferencePoint_advance

        induction a with
        | zero =>
          intro c h
          dsimp only [trace,run,initial] at h
          split at h <;> cases h
        | succ a ih =>
          change freyaHRDifferencePoint (update q (trace q O seed ω a) (replyAt q O seed ω a (query q (trace q O seed ω a))))
          dsimp only [update]
          cases hp : (trace q O seed ω a).phase with
          | halted => exact ih
          | full first c =>
            dsimp only
            split
            · exact freyaHRDifferencePoint_advance q _
            · intro c' h; cases h
          | difference c =>
            dsimp only
            split
            · exact freyaHRDifferencePoint_advance q _
            · intro c' h
              have he := Phase.difference.inj h
              rw [← he,freyaHRDifferencePoint_update]
              exact ih c hp
      have freyaPageFreshDifference (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
          ∃ call, batchStartCall q O seed ω batch = some call ∧
            (trace q O seed ω call).phase = Phase.difference
              (differenceInitial q.n q.S x y clock (seed.1 batch) firstID) := by
        clear * - q O seed ω batch firstID x y clock h freyaPageDifferenceInvocation freyaPageDifferenceEntryAdvance freyaPageAdvanceDifference freyaPageBatchStartFacts freyaPageTraceSeed

        obtain ⟨call,c,hstart,hphase,hx,hy,hclock,hid⟩ :=
          freyaPageDifferenceInvocation q O seed ω batch firstID x y clock h
        have hfacts := freyaPageBatchStartFacts q O seed ω batch call hstart
        cases call with
        | zero =>
          change (initial q seed).phase = Phase.difference c at hphase
          delta initial at hphase
          dsimp only at hphase
          split at hphase <;> contradiction
        | succ k =>
          have hprev := hfacts.2.2.2 k (Nat.lt_succ_self k)
          rw [← hfacts.2.1] at hprev
          obtain ⟨t,htseed,ht⟩ := freyaPageDifferenceEntryAdvance q
            (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))) c hphase hprev
          have httrace : advance q t = trace q O seed ω (k+1) := ht
          have htc : (advance q t).phase = Phase.difference c := by rw [httrace]; exact hphase
          obtain ⟨hit,hc⟩ := freyaPageAdvanceDifference q t c htc
          have hbatch : t.iteration+1 = batch := by rw [← hit,httrace]; exact hfacts.2.1
          have hseed : t.seed = seed := htseed.trans (freyaPageTraceSeed q O seed ω k)
          rw [hc] at hx hy hclock hid
          dsimp only [differenceInitial] at hx hy hclock hid
          have hfirst : t.nextID = firstID := by omega
          refine ⟨k+1,hstart,?_⟩
          rw [hphase,hc,hx,hy,hclock,hseed,hbatch,hfirst]
      have freyaPageEventBudget (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          (trace q O seed ω (eventLimit q)).phase=Phase.halted ∧
            ∀ N,eventLimit q≤N → query q (trace q O seed ω N)=(0,none) := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaPageHaltedUpdate freyaDifferenceLiveStep freyaPageDifferenceQuery freyaFullPotentialDecrease freyaPageFullQuery freyaFullSafeUpdate freyaFullInitialPotential freyaPagePhaseSafety

        classical
        let M := max (q.n*q.m) q.S
        let fullV := fun c : FullState q.d q.m q.n =>
          if c.remaining=[] then 0 else q.n*(c.remaining.length+1)-
            (Finset.univ.filter fun i => ∃ job,c.pending i=some job ∧
              ∃ b ∈ c.remaining,c.original[b]?=some job.component).card
        let R : State q → ℕ := fun s => s.phase.casesOn
          (fun _ c => (rounds q-s.iteration)*M+fullV c)
          (fun c => (rounds q-s.iteration)*M+(c.target-c.count)) 0
        have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
          intro he
          have hh := congrArg List.length he
          simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
          omega
        have hinitV (x : Space q.d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
            fullV (fullInitial q.n (List.ofFn id) x clock rows firstID)≤q.n*q.m := by
          have hh := freyaFullInitialPotential (n:=q.n) (List.ofFn id) hlabels x clock rows firstID
          dsimp only [fullV,fullInitial] at hh ⊢
          simpa (config := { iota := false }) only [List.length_ofFn] using hh
        have hadvance (s : State q) (hi : s.iteration≤rounds q) :
            R (advance q s)≤(rounds q-s.iteration)*M := by
          delta advance
          split
          · exact Nat.zero_le _
          · rename_i hlt
            dsimp only
            by_cases hrefresh : refreshAt s.seed s.iteration=true
            · rw [ite_eq_left hrefresh]
              change (rounds q-(s.iteration+1))*M+
                fullV (fullInitial q.n (List.ofFn id) (s.x-q.η • s.g) s.clock
                  (s.seed.1 (s.iteration+1)) s.nextID)≤(rounds q-s.iteration)*M
              have hb := (hinitV (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID).trans
                (le_max_left (q.n*q.m) q.S)
              have hsub : rounds q-s.iteration=(rounds q-(s.iteration+1))+1 := by omega
              rw [hsub,Nat.add_mul,Nat.one_mul]
              simpa (config := { iota := false }) only [Nat.sub_zero] using Nat.add_le_add_left hb ((rounds q-(s.iteration+1))*M)
            · rw [ite_eq_right hrefresh]
              change (rounds q-(s.iteration+1))*M+(q.S-0)≤(rounds q-s.iteration)*M
              have hb : q.S≤M := le_max_right _ _
              have hsub : rounds q-s.iteration=(rounds q-(s.iteration+1))+1 := by omega
              rw [hsub,Nat.add_mul,Nat.one_mul]
              simpa (config := { iota := false }) only [Nat.sub_zero] using Nat.add_le_add_left hb ((rounds q-(s.iteration+1))*M)
        have hsafe := freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice
        have hdec (k : ℕ) (ha : active (trace q O seed ω k)=true) :
            R (trace q O seed ω (k+1))+1≤R (trace q O seed ω k) := by
          let s := trace q O seed ω k
          have hi := hsafe k
          change R (update q s (replyAt q O seed ω k (query q s)))+1≤R s
          cases hs : s.phase with
          | halted =>
            change active s=true at ha
            delta active at ha
            rw [hs] at ha
            contradiction
          | full first c =>
            obtain ⟨_,hne,hbound,hlegal⟩ := hi.1 first c hs
            have hquery := freyaPageFullQuery q s first c hs
            rw [hquery]
            let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
            have ht := freyaFullSafeUpdate c hne hbound f τ
              (fun r => replyAt q O seed ω k (0,r)) hlegal (hservice k).2
            change t.original=c.original ∧ _ at ht
            have hd := freyaFullPotentialDecrease hn c.original c rfl hne hbound f τ
              (fun r => replyAt q O seed ω k (0,r)) hlegal (hservice k).2
            have hV : fullV t+1≤fullV c := by
              dsimp only [fullV]
              rw [ht.1]
              exact hd
            delta update
            rw [hs]
            dsimp only
            change R (if t.remaining.isEmpty then advance q _ else _)+1≤R s
            by_cases he : t.remaining.isEmpty=true
            · rw [ite_eq_left he]
              have hb := hadvance
                {s with clock:=t.clock,nextID:=t.nextID,phase:=Phase.full first t,g:=fullResult t} hi.2.2
              change _≤(rounds q-s.iteration)*M at hb
              have hr : R s=(rounds q-s.iteration)*M+fullV c := by dsimp only [R]; rw [hs]
              rw [hr]
              change R (advance q {s with
                clock:=t.clock
                nextID:=t.nextID
                phase:=Phase.full first t
                g:=fullResult t})+1≤(rounds q-s.iteration)*M+fullV c
              exact (Nat.add_le_add_right hb 1).trans
                (Nat.add_le_add_left ((Nat.succ_le_succ (Nat.zero_le _)).trans hV) _)
            · rw [ite_eq_right he]
              have hr : R s=(rounds q-s.iteration)*M+fullV c := by dsimp only [R]; rw [hs]
              rw [hr]
              change (rounds q-s.iteration)*M+fullV t+1≤_
              simpa (config := { iota := false }) only [Nat.add_assoc] using Nat.add_le_add_left hV ((rounds q-s.iteration)*M)
          | difference c =>
            obtain ⟨_,hcount,hpending⟩ := hi.2.1 c hs
            have hquery := freyaPageDifferenceQuery q s c hs
            rw [hquery]
            obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,_⟩ := freyaDifferenceLiveStep hm hn c f τ
              (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hpending
            have hr : R s=(rounds q-s.iteration)*M+(c.target-c.count) := by dsimp only [R]; rw [hs]
            rw [hr]
            delta update
            rw [hs]
            dsimp only
            rw [ht]
            dsimp only
            by_cases he : c.target≤c.count+1
            · rw [ite_eq_left he]
              let t : DifferenceState q.d q.m q.n :=
                {c with
                  count:=c.count+1
                  sum:=c.sum+jobValue f job
                  pending:=Function.update c.pending i (some next)
                  clock:=time
                  nextID:=c.nextID+1}
              have hb := hadvance {s with
                clock:=time
                nextID:=c.nextID+1
                phase:=Phase.difference t
                g:=s.g+differenceResult t} hi.2.2
              change R (advance q {s with
                clock:=time
                nextID:=c.nextID+1
                phase:=Phase.difference t
                g:=s.g+differenceResult t})+1≤_
              apply (Nat.add_le_add_right hb 1).trans
              change (rounds q-s.iteration)*M+1≤_
              omega
            · rw [ite_eq_right he]
              change (rounds q-s.iteration)*M+(c.target-(c.count+1))+1≤_
              omega
        have hbound : ∀ k,active (trace q O seed ω k)=true →
            k+R (trace q O seed ω k)≤R (initial q seed) := by
          intro k
          induction k with
          | zero =>
            intro _
            have ht : trace q O seed ω 0=initial q seed := by rfl'
            rw [ht,Nat.zero_add]
          | succ k ih =>
            intro ha
            have hprev : active (trace q O seed ω k)=true := by
              by_contra he
              have hf : active (trace q O seed ω k)=false := Bool.eq_false_of_not_eq_true he
              have hh := freyaPageHaltedUpdate q (trace q O seed ω k)
                (replyAt q O seed ω k (query q (trace q O seed ω k))) hf
              change trace q O seed ω (k+1)=trace q O seed ω k at hh
              rw [hh,hf] at ha
              contradiction
            have hd := hdec k hprev
            have hb := ih hprev
            have calcBound (k next current total : ℕ) (hd : next+1≤current) (hb : k+current≤total) :
                k+1+next≤total := by omega
            exact calcBound k _ _ _ hd hb
        have hrounds : rounds q≤q.K := by delta rounds; split <;> omega
        have hinitBound : R (initial q seed)≤eventLimit q := by
          have hp : (initial q seed).phase=Phase.full true
              (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
            delta initial
            dsimp only
            rw [ite_eq_right (by omega)]
          dsimp only [R]
          rw [hp]
          change (rounds q-0)*M+fullV (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))≤_
          have hv := hinitV q.x0 0 (seed.1 0) 0
          have hm := Nat.mul_le_mul_right M hrounds
          change _≤q.n*q.m+q.K*M
          rw [Nat.sub_zero]
          exact (Nat.add_le_add hm hv).trans_eq (Nat.add_comm _ _)

        have hhalt : (trace q O seed ω (eventLimit q)).phase=Phase.halted := by
          let s := trace q O seed ω (eventLimit q)
          have hi := hsafe (eventLimit q)
          cases hs : s.phase with
          | halted => rfl
          | full first c =>
            have ha : active s=true := by delta active; rw [hs]
            have hb := (hbound (eventLimit q) ha).trans hinitBound
            obtain ⟨_,hne,_,_⟩ := hi.1 first c hs
            have hlen : 0<c.remaining.length := List.length_pos_iff.mpr hne
            have hcard : (Finset.univ.filter fun i => ∃ job,c.pending i=some job ∧
                ∃ b ∈ c.remaining,c.original[b]?=some job.component).card≤q.n := by
              exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin q.n)
            have hmul : q.n≤q.n*c.remaining.length := Nat.le_mul_of_pos_right _ hlen
            have hp : 0<fullV c := by
              dsimp only [fullV]
              rw [ite_eq_right hne,Nat.mul_add,Nat.mul_one]
              omega
            change eventLimit q+R s≤eventLimit q at hb
            dsimp only [R] at hb
            rw [hs] at hb
            dsimp only at hb
            have calcBound (p a b : ℕ) (hp : 0<p) (hb : a+(b+p)≤a) : False := by omega
            exact (calcBound _ _ _ hp hb).elim
          | difference c =>
            have ha : active s=true := by delta active; rw [hs]
            have hb := (hbound (eventLimit q) ha).trans hinitBound
            have hc := (hi.2.1 c hs).2.1
            change eventLimit q+R s≤eventLimit q at hb
            dsimp only [R] at hb
            rw [hs] at hb
            dsimp only at hb
            omega
        refine ⟨hhalt,?_⟩
        have hstable : ∀ N,eventLimit q≤N → trace q O seed ω N=trace q O seed ω (eventLimit q) := by
          intro N hN
          induction N,hN using Nat.le_induction with
          | base => rfl
          | succ N hN ih =>
            change update q (trace q O seed ω N) (replyAt q O seed ω N (query q (trace q O seed ω N)))=_
            rw [ih]
            delta update
            rw [hhalt]
        intro N hN
        rw [hstable N hN]
        delta query
        rw [hhalt]
      have freyaPageFreshFull (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch=some (true,x,y,clock,firstID)) :
          y=x ∧ ∃ call first,batchStartCall q O seed ω batch=some call ∧
            (trace q O seed ω call).phase=Phase.full first
              (fullInitial q.n (List.ofFn id) x clock (seed.1 batch) firstID) := by
        clear * - q O seed ω batch firstID x y clock h freyaPageFullInvocation freyaPageFullEntryAdvance freyaPageAdvanceFull freyaPageBatchStartFacts freyaPageTraceSeed

        obtain ⟨call,first,c,hstart,hphase,hx,hy,hclock,hid⟩ :=
          freyaPageFullInvocation q O seed ω batch firstID x y clock h
        refine ⟨hy.symm.trans hx,?_⟩
        have hfacts := freyaPageBatchStartFacts q O seed ω batch call hstart
        cases call with
        | zero =>
          have hbatch : batch=0 := hfacts.2.1.symm
          change (initial q seed).phase=Phase.full first c at hphase
          have hc : first=true ∧ c=fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0) := by
            delta initial at hphase
            dsimp only at hphase
            split at hphase
            · contradiction
            · have he := Phase.full.inj hphase
              exact ⟨he.1.symm,he.2.symm⟩
          rw [hc.2] at hx hclock hid
          dsimp only [fullInitial] at hx hclock hid
          have hfirst : firstID=0 := by omega
          refine ⟨0,first,hstart,?_⟩
          change (initial q seed).phase=_
          rw [hphase,hc.2,hx,← hclock,hbatch,hfirst]
        | succ k =>
          have hprev := hfacts.2.2.2 k (Nat.lt_succ_self k)
          rw [← hfacts.2.1] at hprev
          obtain ⟨t,htseed,ht⟩ := freyaPageFullEntryAdvance q
            (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))) first c hphase hprev
          have httrace : advance q t=trace q O seed ω (k+1) := ht
          have htc : (advance q t).phase=Phase.full first c := by rw [httrace]; exact hphase
          obtain ⟨hit,_,hc⟩ := freyaPageAdvanceFull q t first c htc
          have hbatch : t.iteration+1=batch := by rw [← hit,httrace]; exact hfacts.2.1
          have hseed : t.seed=seed := htseed.trans (freyaPageTraceSeed q O seed ω k)
          rw [hc] at hx hclock hid
          dsimp only [fullInitial] at hx hclock hid
          have hfirst : t.nextID=firstID := by omega
          refine ⟨k+1,first,hstart,?_⟩
          rw [hphase,hc,hx,hclock,hseed,hbatch,hfirst]
      have freyaBatchExitState (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          ∃ t : State q,t.iteration=b ∧ t.seed=seed ∧ trace q O seed ω e=advance q t := by
        clear * - q O seed ω b a e hs he freyaExitAdvance freyaPageTraceSeed freyaBatchEndFacts

        obtain ⟨ha,_,hbefore,hexit⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hepos : 0<e := by omega
        have hed : e-1+1=e := by omega
        have hp := hbefore (e-1) (by omega) (by omega)
        have hx : (update q (trace q O seed ω (e-1))
            (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1))))).iteration≠
              (trace q O seed ω (e-1)).iteration ∨
            active (update q (trace q O seed ω (e-1))
              (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1)))))=false := by
          change (trace q O seed ω (e-1+1)).iteration≠(trace q O seed ω (e-1)).iteration ∨
            active (trace q O seed ω (e-1+1))=false
          rw [hed,hp.1]
          exact hexit
        obtain ⟨t,hti,hts,hout⟩ := freyaExitAdvance q _ _ hp.2 hx
        refine ⟨t,hti.trans hp.1,hts.trans (freyaPageTraceSeed q O seed ω (e-1)),?_⟩
        change trace q O seed ω (e-1+1)=advance q t at hout
        rwa [hed] at hout
      have freyaEndOfStart (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r)))
          (b a : ℕ) (hs : batchStartCall q O seed ω b=some a) :
          ∃ e,batchEndCall q O seed ω b=some e := by
        clear * - q hm hn hS hK f τ O seed ω hservice b a hs freyaInvocationOfStart

        obtain ⟨full,x,y,clock,firstID,hi⟩ := freyaInvocationOfStart q O seed ω b a hs
        have hh := (restart_coupling q hm hn hS hK f τ O (seed,ω) hservice b firstID full x y clock hi).1
        cases he : batchEndCall q O seed ω b with
        | none => rw [he] at hh; cases hh
        | some e => exact ⟨e,rfl⟩
      have freyaBatchExitObserved (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          ∃ t : State q,t.iteration=b ∧ t.seed=seed ∧ (t.x,t.g)=observedPair q O seed ω b ∧
            t.selected=(trace q O seed ω (e-1)).selected ∧ trace q O seed ω e=advance q t := by
        clear * - q O seed ω b a e hs he freyaExitObserved freyaPageTraceSeed freyaBatchEndFacts

        obtain ⟨ha,_,hbefore,hexit⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hepos : 0<e := by omega
        have hed : e-1+1=e := by omega
        have hp := hbefore (e-1) (by omega) (by omega)
        have hx : (update q (trace q O seed ω (e-1))
            (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1))))).iteration≠
              (trace q O seed ω (e-1)).iteration ∨
            active (update q (trace q O seed ω (e-1))
              (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1)))))=false := by
          change (trace q O seed ω (e-1+1)).iteration≠(trace q O seed ω (e-1)).iteration ∨
            active (trace q O seed ω (e-1+1))=false
          rw [hed,hp.1]
          exact hexit
        obtain ⟨t,hti,hts,htx,htsel,htg,hout⟩ := freyaExitObserved q _ _ hp.2 hx
        refine ⟨t,hti.trans hp.1,hts.trans (freyaPageTraceSeed q O seed ω (e-1)),?_,htsel,?_⟩
        · dsimp only [observedPair]
          rw [he]
          dsimp only [Option.getD_some]
          rw [htx,htg]
          cases hphase : (trace q O seed ω (e-1)).phase <;> rfl
        · change trace q O seed ω (e-1+1)=advance q t at hout
          rwa [hed] at hout
      have freyaInsideBatch (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e) :
          ∀ r,a≤r → r<e → freyaInside (trace q O seed ω r)=freyaInside (trace q O seed ω a) := by
        clear * - q O seed ω b a e hs he freyaInside freyaBatchEndFacts freyaInsideUpdate

        obtain ⟨_,_,hb,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        intro r har
        induction r,har using Nat.le_induction with
        | base => intro _; rfl
        | succ r har ih =>
          intro hre
          have hi : (trace q O seed ω (r+1)).iteration=(trace q O seed ω r).iteration :=
            (hb (r+1) (by omega) hre).1.trans (hb r har (by omega)).1.symm
          have h := freyaInsideUpdate q (trace q O seed ω r)
            (replyAt q O seed ω r (query q (trace q O seed ω r))) hi (hb (r+1) (by omega) hre).2
          exact h.trans (ih (by omega))
      have freyaPageGradientTrace (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) (a : ℕ) :
          freyaPageGradientInvariant q f (trace q O seed ω a) := by
        clear * - q hm hn hS hK f τ O seed ω hservice a freyaPageFullQuery freyaFullGradientUpdate freyaPageGradientInvariant freyaPagePhaseSafety freyaPageGradientAdvance freyaPageGradientInitial

        induction a with
        | zero => exact freyaPageGradientInitial q f seed
        | succ a ih =>
          let s := trace q O seed ω a
          change freyaPageGradientInvariant q f (update q s (replyAt q O seed ω a (query q s)))
          cases hp : s.phase with
          | halted => dsimp only [update]; rw [hp]; exact ih
          | full first c =>
            obtain ⟨horig,hpoint,hgrad⟩ := ih first c hp
            obtain ⟨_,hne,_,hlegal⟩ :=
              (freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice a).1 first c hp
            have hg := freyaFullGradientUpdate c hne f τ
              (fun r => replyAt q O seed ω a (0,r)) hlegal (hservice a).2 hgrad
            rw [freyaPageFullQuery q s first c hp]
            dsimp only [update]
            rw [hp]
            dsimp only
            split
            · exact freyaPageGradientAdvance q f _
            · intro first' c' hp'
              have he := Phase.full.inj hp'
              rw [← he.2]
              exact ⟨hg.1.trans horig,hg.2.1.trans hpoint,hg.2.2⟩
          | difference c =>
            dsimp only [update]
            rw [hp]
            dsimp only
            split
            · exact freyaPageGradientAdvance q f _
            · intro first' c' hp'
              cases hp'
      have freyaPastUpdate (q : Raw) (k : ℕ) (s : State q)
          (new : Seed q.K) (p : Space q.d) (r : Reply q.d q.n) (hrows : new.1=s.seed.1)
          (hbits : ∀ j<k,new.2.1 j=s.seed.2.1 j) :
          freyaPastRelation k (update q {s with seed:=new,selected:=p} r) (update q s r) := by
        clear * - q k s new p r hrows hbits freyaControl freyaPastRelation freyaPastAdvance

        dsimp only [update]
        cases hp : s.phase with
        | halted => left; dsimp only [freyaControl]; rw [hp]
        | full first c =>
          dsimp only
          split
          · exact freyaPastAdvance q k {s with
              g:=fullResult (fullUpdate c r)
              clock:=(fullUpdate c r).clock
              nextID:=(fullUpdate c r).nextID
              phase:=.full first (fullUpdate c r)} new p hrows hbits
          · exact Or.inl rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPastAdvance q k {s with
              g:=s.g+differenceResult (differenceUpdate c r)
              clock:=(differenceUpdate c r).clock
              nextID:=(differenceUpdate c r).nextID
              phase:=.difference (differenceUpdate c r)} new p hrows hbits
          · exact Or.inl rfl
      have freyaFullInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (n : ℕ) (labels : List (Fin m)) (x : Ω → Space d) (clock : Ω → ℝ≥0)
          (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
          (hx : Measurable x) (hc : Measurable clock) (hr : Measurable rows) (hf : Measurable first) :
          Measurable (fun z => fullInitial n labels (x z) (clock z) (rows z) (first z)) := by
        clear * - Ω d m n labels x clock rows first hx hc hr hf freyaMeasurableSelect freyaFullCode freyaDispatchMeas freyaSelectedLabelFixedMeas

        have hp (i : Fin n) : Measurable (fun z =>
            dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
              (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))) :=
          freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hc (hf.add_const i.val)
            ((freyaSelectedLabelFixedMeas labels (List.range labels.length)).comp
              (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
        change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
        rw [measurable_comap_iff]
        change Measurable (fun z => (labels,List.range labels.length,x z,(0 : Space d),
          (fun i : Fin n => dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
            (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))),
          clock z,rows z,first z+n))
        exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk
          (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n)))))))
      have freyaDifferenceInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (n S : ℕ) (x y : Ω → Space d) (clock : Ω → ℝ≥0)
          (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
          (hx : Measurable x) (hy : Measurable y) (hc : Measurable clock)
          (hr : Measurable rows) (hf : Measurable first) :
          Measurable (fun z => differenceInitial (m:=m) n S (x z) (y z) (clock z) (rows z) (first z)) := by
        clear * - Ω d m n S x y clock rows first hx hy hc hr hf freyaMeasurableSelect freyaDifferenceCode freyaLabelAtMeas freyaDispatchMeas

        have hp (i : Fin n) : Measurable (fun z => if S=0 then none else
            dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
              (labelAt (rows z (first z+i.val)) m)) := by
          by_cases hS : S=0
          · simp (config := { iota := false }) only [hS,ite_true]; exact measurable_const
          · simp (config := { iota := false }) only [hS,ite_false]
            exact freyaDispatchMeas _ _ _ _ (measurable_inr.comp (hx.prodMk hy)) hc (hf.add_const i.val)
              ((freyaLabelAtMeas m).comp
                (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
        change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
        rw [measurable_comap_iff]
        change Measurable (fun z => (S,(0 : ℕ),x z,y z,(0 : Space d),
          (fun i : Fin n => if S=0 then none else dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
            (labelAt (rows z (first z+i.val)) m)),clock z,rows z,first z+n))
        exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk (hy.prodMk
          (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n))))))))
      have freyaFullReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
          (s : Ω → FullState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
          (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
          Measurable (fun z => freyaFullReplyJob (s z) (r z) (job z)) := by
        clear * - Ω d m n s r job hs hr hj freyaMeasurableSelect freyaFullCode freyaJobCodeMeas freyaFullReplyJob freyaOptionSingleton freyaFullCodeMeas freyaDispatchMeas freyaSelectedLabelFixedMeas

        classical
        let : MeasurableSingletonClass (Option ℕ) := freyaOptionSingleton
        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        have hcode := freyaFullCodeMeas.comp hs
        have hjcode := freyaJobCodeMeas.comp hj
        have ho : Measurable (fun z => (s z).original) := hcode.fst
        have hrem : Measurable (fun z => (s z).remaining) := hcode.snd.fst
        have hx : Measurable (fun z => (s z).point) := hcode.snd.snd.fst
        have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.fst
        have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.fst
        have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.fst
        have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd
        let found := fun z => (s z).remaining.find? fun a => decide ((s z).original[a]?=some (job z).component)
        let rem := fun z => (found z).elim (s z).remaining (fun a => (s z).remaining.erase a)
        let sum := fun z => if (found z).isSome then (s z).sum+(r z).2.2.2 else (s z).sum
        let next := fun z => dispatch (Sum.inl (s z).point) (r z).2.2.1 (s z).nextID
          (selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID))
        have hf : Measurable found :=
          (measurable_of_countable (fun p : List (Fin m) × List ℕ × Fin m =>
            p.2.1.find? fun a => decide (p.1[a]?=some p.2.2))).comp (ho.prodMk (hrem.prodMk hjcode.fst))
        have hrem' : Measurable rem :=
          (measurable_of_countable (fun p : List ℕ × Option ℕ => p.2.elim p.1 (fun a => p.1.erase a))).comp
            (hrem.prodMk hf)
        have hsum' : Measurable sum := (hsum.add hr.snd.snd.snd).ite
          (((measurable_of_countable (fun o : Option ℕ => o.isSome)).comp hf) (measurableSet_singleton true)) hsum
        have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
          freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
        have hlabel : Measurable (fun z => selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID)) :=
          freyaMeasurableSelect _ (ho.prodMk hrem') _
            (fun p => (freyaSelectedLabelFixedMeas p.1 p.2).comp hrow)
        have hnext : Measurable next := freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hr.snd.snd.fst hid hlabel
        have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
          freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
        have hnew : Measurable (fun z => {s z with
            remaining:=rem z
            sum:=sum z
            pending:=Function.update (s z).pending (r z).1 (next z)
            clock:=(r z).2.2.1
            nextID:=(s z).nextID+1}) := by
          change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
          rw [measurable_comap_iff]
          exact ho.prodMk (hrem'.prodMk (hx.prodMk (hsum'.prodMk
            (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1)))))))
        exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
          (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
      have freyaDifferenceReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
          (s : Ω → DifferenceState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
          (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
          Measurable (fun z => freyaDifferenceReplyJob (s z) (r z) (job z)) := by
        clear * - Ω d m n s r job hs hr hj freyaMeasurableSelect freyaDifferenceCode freyaJobCodeMeas freyaDifferenceReplyJob freyaDifferenceCodeMeas freyaLabelAtMeas freyaDispatchMeas

        classical
        have hcode := freyaDifferenceCodeMeas.comp hs
        have hjcode := freyaJobCodeMeas.comp hj
        have ht : Measurable (fun z => (s z).target) := hcode.fst
        have hcount : Measurable (fun z => (s z).count) := hcode.snd.fst
        have hx : Measurable (fun z => (s z).x) := hcode.snd.snd.fst
        have hy : Measurable (fun z => (s z).y) := hcode.snd.snd.snd.fst
        have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.snd.fst
        have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.snd.fst
        have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.snd.fst
        have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd.snd
        let next := fun z => dispatch (Sum.inr ((s z).x,(s z).y)) (r z).2.2.1 (s z).nextID
          (labelAt ((s z).rows (s z).nextID) m)
        have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
          freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
        have hnext : Measurable next := freyaDispatchMeas _ _ _ _
          (measurable_inr.comp (hx.prodMk hy)) hr.snd.snd.fst hid ((freyaLabelAtMeas m).comp hrow)
        have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
          freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
        have hnew : Measurable (fun z => {s z with
            count:=(s z).count+1
            sum:=(s z).sum+(r z).2.2.2
            pending:=Function.update (s z).pending (r z).1 (next z)
            clock:=(r z).2.2.1
            nextID:=(s z).nextID+1}) := by
          change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
          rw [measurable_comap_iff]
          exact ht.prodMk ((hcount.add_const 1).prodMk (hx.prodMk (hy.prodMk ((hsum.add hr.snd.snd.snd).prodMk
            (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1))))))))
        exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
          (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
      have freyaPageQueryMeas (q : Raw) : Measurable (query q) := by
        clear * - q freyaFullCode freyaDifferenceCode freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPendingRequestMeas freyaPhaseParamMeas

        classical
        have hfull : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) =>
            if z.2.2.remaining.isEmpty then none else pendingRequest z.2.2.clock z.2.2.pending) := by
          have hc : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) => freyaFullCode z.2.2) :=
            freyaFullCodeMeas.comp measurable_snd.snd
          exact measurable_const.ite
            (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst) (measurableSet_singleton true))
            (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.fst))
        have hdiff : Measurable (fun z : State q × DifferenceState q.d q.m q.n =>
            if z.2.target≤z.2.count then none else pendingRequest z.2.clock z.2.pending) := by
          have hc : Measurable (fun z : State q × DifferenceState q.d q.m q.n => freyaDifferenceCode z.2) :=
            freyaDifferenceCodeMeas.comp measurable_snd
          exact measurable_const.ite (measurableSet_le hc.fst hc.snd.fst)
            (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.snd.fst))
        have hp := freyaPhaseParamMeas (fun s : State q => s.phase)
          ((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd)
          (fun _ => (none : Option (Request q.d q.m q.n))) measurable_const _ hfull _ hdiff
        have h : Measurable (fun s : State q => ((0 : Fin 1), s.phase.casesOn
            (motive:=fun _ => Option (Request q.d q.m q.n))
            (fun _ c => if c.remaining.isEmpty then none else pendingRequest c.clock c.pending)
            (fun c => if c.target≤c.count then none else pendingRequest c.clock c.pending) none)) :=
          measurable_const.prodMk hp
        convert h using 1
        funext s
        delta query
        cases s.phase <;> rfl
      have freyaFreshTapeEventProdProd {α β γ : Type}
          [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
          (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
          (ξ : Measure γ) [IsProbabilityMeasure ξ]
          (i : ℕ) (E : Set (((ℕ → α) × β) × γ)) (hE : MeasurableSet E)
          (hinvariant : ∀ t b c a, ((Function.update t i a,b),c)∈E ↔ ((t,b),c)∈E)
          (U : Set α) (hU : MeasurableSet U) :
          (((Measure.infinitePi fun _ : ℕ => μ).prod ν).prod ξ) (E∩{z | z.1.1 i∈U})=
            (((Measure.infinitePi fun _ : ℕ => μ).prod ν).prod ξ) E*μ U := by
        clear * - α β γ μ ν ξ i E hE hinvariant U hU freyaFreshTapeEventProd

        let e : (((ℕ → α) × β) × γ) ≃ᵐ ((ℕ → α) × β × γ) := MeasurableEquiv.prodAssoc
        have hp := measurePreserving_prodAssoc (Measure.infinitePi fun _ : ℕ => μ) ν ξ
        have h := freyaFreshTapeEventProd μ (ν.prod ξ) i (e.symm ⁻¹' E)
          (hE.preimage e.symm.measurable)
          (fun t b a => hinvariant t b.1 b.2 a) U hU
        have hm : MeasurableSet ((e.symm ⁻¹' E)∩{z : (ℕ → α) × β × γ | z.1 i∈U}) :=
          (hE.preimage e.symm.measurable).inter (((measurable_pi_apply i).comp measurable_fst) hU)
        rw [← hp.map_eq,Measure.map_apply hp.measurable hm,
          Measure.map_apply hp.measurable (hE.preimage e.symm.measurable)] at h
        exact h
      let freyaHRStep (d m S : ℕ) (s : freyaHRReplayState d m) (e : freyaHREvent d m) : freyaHRReplayState d m := e.elim (fun _ => s) fun v =>
          if v.2.1 then
            let remaining := freyaHRRemainingAfter m s.1 v.1
            let acc := if freyaHRAccepts m s.1 v.1 then s.2.2.1 + v.2.2.2 else s.2.2.1
            if remaining = [] then freyaHRFinish (m:=m) s (v.2.2.1, (m : ℝ)⁻¹ • acc)
            else (remaining, 0, acc, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2)
          else
            let count := s.2.1 + 1
            let acc := s.2.2.1 + v.2.2.2
            if S ≤ count then freyaHRFinish (m:=m) s (v.2.2.1, s.2.2.2.1 + (S : ℝ)⁻¹ • acc)
            else (s.1, count, acc, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2)
      have freyaHRMeasurable_finish (d m : ℕ) :
          Measurable (fun z : freyaHRReplayState d m × freyaHRPair d => freyaHRFinish (m:=m) z.1 z.2) := by
        clear * - d m freyaHRPair freyaHRReplayState freyaHRFinish

        dsimp only [freyaHRReplayState,freyaHRPair]
        unfold freyaHRFinish
        apply Measurable.prodMk measurable_const
        apply Measurable.prodMk measurable_const
        apply Measurable.prodMk measurable_const
        apply Measurable.prodMk (by fun_prop)
        apply Measurable.prodMk (by fun_prop)
        apply Measurable.of_eval
        intro k
        simp (config := { iota := false }) only [Function.update_apply]
        refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
        exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
      have freyaHRMeasurable_rawEvent (d m n : ℕ) : Measurable (@freyaHRRawEvent d m n) := by
        clear * - d m n freyaHRReplyValue freyaOptionParamMeas freyaHREventFromJob freyaHRMeasurable_replyValue freyaCompletedFromMeas freyaHRMeasurable_eventFromJob freyaHRRawEvent

        have hj : Measurable (fun z : (Option (Request d m n) × Reply d n) × Job d m =>
            freyaHREventFromJob z.2 (freyaHRReplyValue z.1.2)) :=
          (freyaHRMeasurable_eventFromJob d m).comp
            (measurable_snd.prodMk ((freyaHRMeasurable_replyValue d n).comp measurable_fst.snd))
        exact freyaOptionParamMeas _ freyaCompletedFromMeas _ measurable_const _ hj
      let freyaHRDecodeEntry {d m n : ℕ} (e : freyaHRHistoryEntry d m n) : freyaHREvent d m :=
        e.elim (Sum.inl ()) (fun t => freyaHRRawEvent (t.1.2,t.2.1))
      have freyaHRCore_advance (q : Raw) (s : State q) (path : ℕ → freyaHRPair q.d)
          (hb : s.iteration < rounds q) :
          freyaHRCore (advance q s) path = (List.range q.m, 0, 0, s.g, s.iteration+1, path)  := by
        clear * - q s path hb freyaHRPair freyaHRCore

        delta advance
        rw [ite_eq_right (not_le.mpr hb)]
        dsimp only
        cases hbit : refreshAt s.seed s.iteration <;>
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true] <;>
          dsimp only [freyaHRCore,fullInitial,differenceInitial] <;>
          simp (config := { iota := false }) only [List.length_ofFn]
      have freyaHRRawEvent_matching {d m n : ℕ} (r : Request d m n) (i : Fin n)
          (j : Job d m) (c : ℝ≥0) (v : Space d) (hj : r.pending i = some j) :
          freyaHRRawEvent (some r, some (i,j.id,c,v)) = freyaHREventFromJob j v := by
        clear * - d m n r i j c v hj freyaHRCompletedJob freyaHRReplyValue freyaHREventFromJob freyaHRRawEvent

        simp (config := { iota := false }) [freyaHRRawEvent, freyaHRCompletedJob, hj, freyaHRReplyValue]
      have freyaHRCore_initial (q : Raw) (seed : Seed q.K) (hm : 0<q.m) (hn : 0<q.n) (hK : 0<q.K) :
          freyaHRCore (initial q seed) (fun _ => (0,0)) = freyaHRReplayInitial q.d q.m  := by
        clear * - q seed hm hn hK freyaHRReplayInitial freyaHRCore

        delta initial
        rw [ite_eq_right (show ¬ (q.m=0 ∨ q.n=0 ∨ q.K=0) by omega)]
        dsimp only [freyaHRCore,fullInitial,freyaHRReplayInitial]
        simp (config := { iota := false }) only [List.length_ofFn]
      let freyaHRActualEvents (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) (a : ℕ) : freyaHREvent q.d q.m :=
        let s := trace q O z.1 z.2 a
        freyaHRRawEvent ((query q s).2, replyAt q O z.1 z.2 a (query q s))
      have freyaHRCore_path {q : Raw} (s : State q) (p : ℕ → freyaHRPair q.d) :
          (freyaHRCore s p).2.2.2.2.2 = p  := by
        clear * - q s p freyaHRPair freyaHRCore

        dsimp only [freyaHRCore]
        cases s.phase <;> rfl
      have freyaBatchEndExists (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID : ℕ) (full : Bool) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O z.1 z.2 batch=some (full,x,y,clock,firstID)) :
          (batchEndCall q O z.1 z.2 batch).isSome := by
        clear * - q hm hn hS hK f τ O z hs batch firstID full x y clock hi freyaPageBatchStartFacts freyaPageEventBudget

        classical
        obtain ⟨first,hfirst⟩ : ∃ first,batchStartCall q O z.1 z.2 batch=some first := by
          cases h : batchStartCall q O z.1 z.2 batch with
          | none =>
            dsimp only [invocation] at hi
            rw [h] at hi
            cases hi
          | some first => exact ⟨first,rfl⟩
        have hf := freyaPageBatchStartFacts q O z.1 z.2 batch first hfirst
        have hhalt := (freyaPageEventBudget q hm hn hS hK f τ O z.1 z.2 hs).1
        have hlt : first<eventLimit q := by
          by_contra h
          have he : first=eventLimit q := by omega
          have ha := hf.2.2.1
          rw [he] at ha
          dsimp only [active] at ha
          rw [hhalt] at ha
          contradiction
        let p := fun a : ℕ =>
          let s := trace q O z.1 z.2 a
          decide (first<a) && (decide (s.iteration≠batch) || !(active s))
        have hp : p (eventLimit q)=true := by
          dsimp only [p,active]
          rw [hhalt]
          dsimp only
          simp (config := { iota := false }) only [Bool.not_false,Bool.or_true,Bool.and_true,decide_eq_true_eq]
          exact hlt
        have hm : eventLimit q∈List.range (eventLimit q+1) := List.mem_range.mpr (by omega)
        dsimp only [batchEndCall]
        rw [hfirst]
        dsimp only [Option.bind_some]
        change ((List.range (eventLimit q+1)).find? p).isSome
        cases he : (List.range (eventLimit q+1)).find? p with
        | some a => rfl
        | none =>
          have hz := List.find?_eq_none.mp he (eventLimit q) hm
          rw [hp] at hz
          contradiction
      have freyaBatchNextStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hb : b<rounds q) (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          batchStartCall q O seed ω (b+1)=some e := by
        clear * - q O seed ω b a e hb hs he freyaPageBatchStartFacts freyaPageIterationMonotone freyaBatchEndFacts freyaBatchExitState

        classical
        obtain ⟨ha,hlim,hbefore,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        obtain ⟨t,hti,hts,hout⟩ := freyaBatchExitState q O seed ω b a e hs he
        have hnot : ¬rounds q≤t.iteration := by omega
        have hp : (trace q O seed ω e).iteration=b+1 ∧ active (trace q O seed ω e)=true := by
          rw [hout]
          dsimp only [advance]
          rw [ite_eq_right hnot]
          dsimp only
          constructor
          · rw [hti]
          · by_cases hbit : refreshAt t.seed t.iteration=true
            · rw [ite_eq_left hbit]; rfl
            · rw [ite_eq_right hbit]; rfl
        have hprev : ∀ r<e,(trace q O seed ω r).iteration≠b+1 := by
          intro r hr heq
          by_cases hra : r<a
          · have hmono := freyaPageIterationMonotone q O seed ω (Nat.le_of_lt hra)
            change (trace q O seed ω r).iteration≤(trace q O seed ω a).iteration at hmono
            have hit := (freyaPageBatchStartFacts q O seed ω b a hs).2.1
            omega
          · have hit := (hbefore r (by omega) hr).1
            omega
        dsimp only [batchStartCall]
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨?_,e,?_,?_,?_⟩
        · simp (config := { iota := false }) only [hp.1,hp.2,decide_true,Bool.and_self]
        · simpa (config := { iota := false }) only [List.length_range] using (show e<eventLimit q+1 by omega)
        · simp (config := { iota := false }) only [List.getElem_range]
        · intro r hr
          simp (config := { iota := false }) only [List.getElem_range,hprev r hr,decide_false,Bool.false_and,Bool.not_false]
      have freyaObservedPosition (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e) :
          (observedPair q O seed ω b).1=(trace q O seed ω a).x ∧
            (trace q O seed ω (e-1)).g=(trace q O seed ω a).g := by
        clear * - q O seed ω b a e hs he freyaBatchEndFacts freyaInsideBatch

        have hlt := (freyaBatchEndFacts q O seed ω b a e hs he).1
        have h := freyaInsideBatch q O seed ω b a e hs he (e-1) (by omega) (by omega)
        have hx := congrArg Prod.fst h
        have hg := congrArg (fun z => z.2.1) h
        refine ⟨?_,hg⟩
        dsimp only [observedPair]
        rw [he]
        dsimp only [Option.getD_some]
        cases hp : (trace q O seed ω (e-1)).phase <;> exact hx
      have freyaObservedFull (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (hf : ∀ i,Differentiable ℝ (f i)) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (b firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hinv : invocation q O seed ω b=some (true,x,y,clock,firstID)) :
          (observedPair q O seed ω b).2=gradient (objective f) (observedPair q O seed ω b).1 := by
        clear * - q hm hn hS hK f hf τ O seed ω hservice b firstID x y clock hinv freyaPageFullQuery freyaInside freyaObservedFullExit freyaFullGradientUpdate freyaFullGradientComplete freyaPagePhaseSafety freyaBatchEndFacts freyaPageFreshFull freyaEndOfStart freyaInsideBatch freyaPageGradientTrace

        obtain ⟨_,a,first,hs,hphase⟩ := freyaPageFreshFull q O seed ω b firstID x y clock hinv
        obtain ⟨e,he⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice b a hs
        obtain ⟨ha,_,hbefore,hexit⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hp := hbefore (e-1) (by omega) (by omega)
        have hinside := freyaInsideBatch q O seed ω b a e hs he (e-1) (by omega) (by omega)
        have htag := congrArg (fun z => z.2.2) hinside
        dsimp only [freyaInside] at htag
        rw [hphase] at htag
        obtain ⟨c,hc⟩ : ∃ c,(trace q O seed ω (e-1)).phase=Phase.full first c := by
          cases h : (trace q O seed ω (e-1)).phase with
          | halted => rw [h] at htag; cases htag
          | difference c => rw [h] at htag; cases htag
          | full first' c =>
            rw [h] at htag
            have hfirst : first'=first := Option.some.inj htag
            subst first'
            exact ⟨c,rfl⟩
        have hed : e-1+1=e := by omega
        have hleave : (update q (trace q O seed ω (e-1))
            (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1))))).iteration≠
              (trace q O seed ω (e-1)).iteration ∨
            active (update q (trace q O seed ω (e-1))
              (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1)))))=false := by
          change (trace q O seed ω (e-1+1)).iteration≠(trace q O seed ω (e-1)).iteration ∨
            active (trace q O seed ω (e-1+1))=false
          rw [hed,hp.1]
          exact hexit
        have hempty := freyaObservedFullExit q _ _ first c hc hleave
        obtain ⟨horig,hpoint,hgrad⟩ := freyaPageGradientTrace q hm hn hS hK f τ O seed ω hservice (e-1) first c hc
        obtain ⟨_,hne,_,hlegal⟩ :=
          (freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice (e-1)).1 first c hc
        have hquery := freyaPageFullQuery q _ first c hc
        rw [hquery] at hempty
        have hnew := freyaFullGradientUpdate c hne f τ
          (fun r => replyAt q O seed ω (e-1) (0,r)) hlegal (hservice (e-1)).2 hgrad
        have hresult := freyaFullGradientComplete f hf _ (hnew.1.trans horig) hnew.2.2 hempty
        rw [hnew.2.1,hpoint] at hresult
        dsimp only [observedPair]
        rw [he]
        dsimp only [Option.getD_some]
        rw [hc]
        exact (by rw [hquery]; exact hresult)
      have freyaPastTrace (q : Raw) (k : ℕ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (a : ℕ) → O.Seed a)
          (hrows : new.1=seed.1) (hbits : ∀ j<k,new.2.1 j=seed.2.1 j) :
          ∀ a,freyaPastRelation k (trace q O new ω a) (trace q O seed ω a) := by
        clear * - q k O seed new ω hrows hbits freyaControl freyaPageUpdateIteration freyaControlRecord freyaPastRelation freyaPageTraceSeed freyaQueryControl freyaPastUpdate hobl

        intro a
        induction a with
        | zero => left; dsimp only [trace,run,initial,freyaControl]; rw [hrows]
        | succ a ih =>
          rcases ih with ih|⟨hnew,hold⟩
          · have hs : trace q O new ω a={trace q O seed ω a with
                seed:=new,selected:=(trace q O new ω a).selected} := by
              have h := freyaControlRecord q _ _ ih
              rwa [freyaPageTraceSeed q O new ω a] at h
            have hq := freyaQueryControl q _ _ ih
            change freyaPastRelation k (update q (trace q O new ω a)
              (replyAt q O new ω a (query q (trace q O new ω a)))) _
            rw [replyAt_seed q O hobl new seed ω a,hq,hs]
            exact freyaPastUpdate q k _ _ _ _
              (by rw [freyaPageTraceSeed]; exact hrows)
              (by rw [freyaPageTraceSeed]; exact hbits)
          · right
            have hn := freyaPageUpdateIteration q (trace q O new ω a)
              (replyAt q O new ω a (query q (trace q O new ω a)))
            have ho := freyaPageUpdateIteration q (trace q O seed ω a)
              (replyAt q O seed ω a (query q (trace q O seed ω a)))
            change k<(update q (trace q O new ω a) (replyAt q O new ω a (query q (trace q O new ω a)))).iteration ∧
              k<(update q (trace q O seed ω a) (replyAt q O seed ω a (query q (trace q O seed ω a)))).iteration
            constructor <;> omega
      have freyaFullUpdateMeas {d m n : ℕ} :
          Measurable (fun z : FullState d m n × Reply d n => fullUpdate z.1 z.2) := by
        clear * - d m n freyaMeasurableSelect freyaFullReplyJob freyaOptionParamMeas freyaFullCodeMeas freyaFullReplyJobMeas

        classical
        have hc := freyaFullCodeMeas (d:=d) (m:=m) (n:=n)
        have hsome : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            ((z.1).pending z.2.1).elim z.1 (fun job => freyaFullReplyJob z.1 z.2 job)) := by
          have hp : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
              z.1.pending z.2.1) :=
            freyaMeasurableSelect _ measurable_snd.fst _
              (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.fst.comp measurable_fst))
          exact freyaOptionParamMeas _ hp _ measurable_fst _
            (freyaFullReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
        have hoption : Measurable (fun z : FullState d m n × Reply d n =>
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
          freyaOptionParamMeas _ measurable_snd _ measurable_fst _
            (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
        have he : MeasurableSet {z : FullState d m n × Reply d n | z.1.remaining.isEmpty=true} :=
          ((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp
            (hc.snd.fst.comp measurable_fst)) (measurableSet_singleton true)
        have hh : Measurable (fun z : FullState d m n × Reply d n =>
            if z.1.remaining.isEmpty then z.1 else
              z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
          measurable_fst.ite he hoption
        convert hh using 1
        funext z
        delta fullUpdate
        dsimp only
        by_cases hempty : z.1.remaining.isEmpty=true
        · simp (config := { iota := false }) only [ite_eq_left hempty]
        · simp (config := { iota := false }) only [ite_eq_right hempty]
          cases hr : z.2 with
          | none => rfl
          | some r =>
            obtain ⟨i,id,t,value⟩ := r
            dsimp only [Option.elim_some]
            cases hp : z.1.pending i <;> rfl
      have freyaDifferenceUpdateMeas {d m n : ℕ} :
          Measurable (fun z : DifferenceState d m n × Reply d n => differenceUpdate z.1 z.2) := by
        set_option maxHeartbeats 8000000 in
          clear * - d m n freyaMeasurableSelect freyaDifferenceReplyJob freyaOptionParamMeas freyaDifferenceCodeMeas freyaDifferenceReplyJobMeas
          classical
          have hc := freyaDifferenceCodeMeas (d:=d) (m:=m) (n:=n)
          have hsome : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
              ((z.1).pending z.2.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 z.2 job)) := by
            have hp : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
                z.1.pending z.2.1) :=
              freyaMeasurableSelect _ measurable_snd.fst _
                (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.snd.fst.comp measurable_fst))
            have hjob := freyaDifferenceReplyJobMeas
              (Ω := (DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d)) × Job d m)
              (d:=d) (m:=m) (n:=n)
              (fun z => z.1.1) (fun z => z.1.2) (fun z => z.2)
              measurable_fst.fst measurable_fst.snd measurable_snd
            have hop := freyaOptionParamMeas
              (Ω := DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d))
              (α := Job d m) (β := DifferenceState d m n)
              (fun z => z.1.pending z.2.1) hp Prod.fst measurable_fst
              (fun z => freyaDifferenceReplyJob z.1.1 z.1.2 z.2) hjob
            exact hop
          have hoption : Measurable (fun z : DifferenceState d m n × Reply d n =>
              z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
            freyaOptionParamMeas
              (Ω := DifferenceState d m n × Reply d n)
              (α := Fin n × ℕ × ℝ≥0 × Space d) (β := DifferenceState d m n)
              Prod.snd measurable_snd Prod.fst measurable_fst
              (fun z => (z.1.1.pending z.2.1).elim z.1.1 (fun job => freyaDifferenceReplyJob z.1.1 z.2 job))
              (hsome.comp
                (show Measurable (fun z : (DifferenceState d m n × Reply d n) ×
                    (Fin n × ℕ × ℝ≥0 × Space d) => (z.1.1,z.2)) from
                  measurable_fst.fst.prodMk measurable_snd))
          have he : MeasurableSet {z : DifferenceState d m n × Reply d n | z.1.target≤z.1.count} :=
            measurableSet_le (hc.fst.comp measurable_fst) (hc.snd.fst.comp measurable_fst)
          have hh : Measurable (fun z : DifferenceState d m n × Reply d n =>
              if z.1.target≤z.1.count then z.1 else
                z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
            measurable_fst.ite he hoption
          have hfun : (fun z : DifferenceState d m n × Reply d n => differenceUpdate z.1 z.2) =
              (fun z : DifferenceState d m n × Reply d n =>
                if z.1.target≤z.1.count then z.1 else
                  z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) := by
            funext z
            delta differenceUpdate
            dsimp only
            by_cases hstop : z.1.target≤z.1.count
            · simp (config := { iota := false }) only [ite_eq_left hstop]
            · simp (config := { iota := false }) only [ite_eq_right hstop]
              cases hr : z.2 with
              | none => rfl
              | some r =>
                obtain ⟨i,id,t,value⟩ := r
                dsimp only [Option.elim_some]
                cases hp : z.1.pending i <;> rfl
          rw [hfun]
          exact hh
      have freyaPageInitialMeas (q : Raw) : Measurable (initial q) := by
        clear * - q freyaPhaseFullMeas freyaStateConstructMeas freyaFullInitialMeas

        have hp : Measurable (fun seed : Seed q.K =>
            if q.m=0 ∨ q.n=0 ∨ q.K=0 then (Phase.halted : Phase q.d q.m q.n) else
              Phase.full true (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))) := by
          by_cases hbad : q.m=0 ∨ q.n=0 ∨ q.K=0
          · simp (config := { iota := false }) only [hbad,ite_true]; exact measurable_const
          · simp (config := { iota := false }) only [hbad,ite_false]
            exact freyaPhaseFullMeas.comp (measurable_const.prodMk
              (freyaFullInitialMeas q.n (List.ofFn id) (fun _ => q.x0) (fun _ => 0)
                (fun seed : Seed q.K => seed.1 0) (fun _ => 0) measurable_const measurable_const
                ((measurable_pi_apply 0).comp measurable_fst) measurable_const))
        exact freyaStateConstructMeas q id (fun _ => 0) (fun _ => q.x0) (fun _ => 0) (fun _ => q.x0)
          (fun _ => 0) (fun _ => q.n) _ measurable_id measurable_const measurable_const measurable_const
            measurable_const measurable_const measurable_const hp
      have freyaPageAdvanceMeas (q : Raw) : Measurable (advance q) := by
        clear * - q freyaMeasurableSelect freyaStateCodeMeas freyaPhaseFullMeas freyaPhaseDifferenceMeas freyaStateConstructMeas freyaFullInitialMeas freyaDifferenceInitialMeas

        classical
        have hc := freyaStateCodeMeas q
        have hseed : Measurable (fun s : State q => s.seed) := hc.fst
        have hit : Measurable (fun s : State q => s.iteration) := hc.snd.fst
        have hx : Measurable (fun s : State q => s.x) := hc.snd.snd.fst
        have hg : Measurable (fun s : State q => s.g) := hc.snd.snd.snd.fst
        have hsel : Measurable (fun s : State q => s.selected) := hc.snd.snd.snd.snd.fst
        have hclock : Measurable (fun s : State q => s.clock) := hc.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun s : State q => s.nextID) := hc.snd.snd.snd.snd.snd.snd.fst
        let x := fun s : State q => s.x-q.η • s.g
        let batch := fun s : State q => s.iteration+1
        have hnewx : Measurable x := hx.sub (hg.const_smul q.η)
        have hbatch : Measurable batch := hit.add_const 1
        have hrows : Measurable (fun s : State q => s.seed.1 (batch s)) :=
          freyaMeasurableSelect _ hbatch _ (fun k => (measurable_pi_apply k).comp hseed.fst)
        have hrefresh : Measurable (fun s : State q => refreshAt s.seed s.iteration) :=
          freyaMeasurableSelect _ hit _ (fun k => (measurable_pi_apply k).comp hseed.snd.fst)
        have hfull := (freyaPhaseFullMeas (m:=q.m)).comp ((measurable_const (a:=false)).prodMk
          (freyaFullInitialMeas (m:=q.m) q.n (List.ofFn id) x (fun s => s.clock) _ (fun s => s.nextID)
            hnewx hclock hrows hid))
        have hdiff := freyaPhaseDifferenceMeas.comp
          (freyaDifferenceInitialMeas (m:=q.m) q.n q.S x (fun s => s.x) (fun s => s.clock) _
            (fun s => s.nextID) hnewx hx hclock hrows hid)
        have hphase : Measurable (fun s : State q => if refreshAt s.seed s.iteration then
            Phase.full false (fullInitial q.n (List.ofFn id) (x s) s.clock (s.seed.1 (batch s)) s.nextID)
          else Phase.difference (differenceInitial q.n q.S (x s) s.x s.clock (s.seed.1 (batch s)) s.nextID)) :=
          hfull.ite (hrefresh (measurableSet_singleton true)) hdiff
        have hindex : Measurable (fun s : State q => (outputIndex s.seed).val) :=
          (measurable_of_countable (fun i : Fin (max 1 q.K) => i.val)).comp hseed.snd.snd
        have hselected : Measurable (fun s : State q =>
            if (outputIndex s.seed).val=batch s then x s else s.selected) :=
          hnewx.ite (measurableSet_eq_fun hindex hbatch) hsel
        have hnext := freyaStateConstructMeas q _ batch x _ _ _ _ _
          hseed hbatch hnewx hg hselected hclock (hid.add_const q.n) hphase
        have hstop := freyaStateConstructMeas q _ _ _ _ _ _ _ (fun _ => Phase.halted)
          hseed hit hx hg hsel hclock hid measurable_const
        exact hstop.ite (measurableSet_le measurable_const hit) hnext
      have freyaHRMeasurable_step (d m S : ℕ) :
          Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × freyaHREvent d m => freyaHRStep d m S z.1 z.2) := by
        clear * - d m S freyaHREvent freyaHRRemainingAfter freyaHRAccepts freyaHRFinish freyaHRStep freyaHRMeasurable_finish

        classical

        have hrem : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) => freyaHRRemainingAfter m z.1.1 z.2.1) :=
          (measurable_of_countable (fun p : List ℕ × Fin m => freyaHRRemainingAfter m p.1 p.2)).comp
            (measurable_fst.fst.prodMk measurable_snd.fst)
        have hmemBool : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) => freyaHRAccepts m z.1.1 z.2.1) :=
          (measurable_of_countable (fun p : Fin m × List ℕ => freyaHRAccepts m p.2 p.1)).comp
            (measurable_snd.fst.prodMk measurable_fst.fst)
        have hmem : MeasurableSet {z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) | freyaHRAccepts m z.1.1 z.2.1} := by
          simpa (config := { iota := false }) only [decide_eq_true_eq] using measurableSet_eq_fun hmemBool (measurable_const (a := true))
        have hacc : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) =>
            if freyaHRAccepts m z.1.1 z.2.1 then z.1.2.2.1 + z.2.2.2.2 else z.1.2.2.1) :=
          Measurable.ite hmem (by fun_prop) (by fun_prop)
        have hfull : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) =>
            if freyaHRRemainingAfter m z.1.1 z.2.1 = [] then
              freyaHRFinish (m:=m) z.1 (z.2.2.2.1, (m : ℝ)⁻¹ •
                (if freyaHRAccepts m z.1.1 z.2.1 then z.1.2.2.1 + z.2.2.2.2 else z.1.2.2.1))
            else (freyaHRRemainingAfter m z.1.1 z.2.1, 0,
              (if freyaHRAccepts m z.1.1 z.2.1 then z.1.2.2.1 + z.2.2.2.2 else z.1.2.2.1),
              z.1.2.2.2.1, z.1.2.2.2.2.1, z.1.2.2.2.2.2)) := by
          refine Measurable.ite (measurableSet_eq_fun hrem measurable_const) ?_ ?_
          · exact (freyaHRMeasurable_finish d m).comp
              (measurable_fst.prodMk (measurable_snd.snd.snd.fst.prodMk (hacc.const_smul ((m : ℝ)⁻¹))))
          · exact hrem.prodMk (measurable_const.prodMk (hacc.prodMk
              (measurable_fst.snd.snd.snd.fst.prodMk (measurable_fst.snd.snd.snd.snd.fst.prodMk measurable_fst.snd.snd.snd.snd.snd))))
        have hdiff : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) =>
            if S ≤ z.1.2.1 + 1 then
              freyaHRFinish (m:=m) z.1 (z.2.2.2.1, z.1.2.2.2.1 + (S : ℝ)⁻¹ • (z.1.2.2.1 + z.2.2.2.2))
            else (z.1.1, z.1.2.1 + 1, z.1.2.2.1 + z.2.2.2.2,
              z.1.2.2.2.1, z.1.2.2.2.2.1, z.1.2.2.2.2.2)) := by
          refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) ?_ ?_
          · have hh : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) => (z.1, (z.2.2.2.1, z.1.2.2.2.1 + (S : ℝ)⁻¹ • (z.1.2.2.1 + z.2.2.2.2)))) := by fun_prop
            exact (freyaHRMeasurable_finish d m).comp hh
          · fun_prop
        have hsome : Measurable (fun z : (List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d))) × (Fin m × Bool × Space d × Space d) =>
            if z.2.2.1 then
              let remaining := freyaHRRemainingAfter m z.1.1 z.2.1
              let acc := if freyaHRAccepts m z.1.1 z.2.1 then z.1.2.2.1 + z.2.2.2.2 else z.1.2.2.1
              if remaining = [] then freyaHRFinish (m:=m) z.1 (z.2.2.2.1, (m : ℝ)⁻¹ • acc)
              else (remaining, 0, acc, z.1.2.2.2.1, z.1.2.2.2.2.1, z.1.2.2.2.2.2)
            else
              let count := z.1.2.1 + 1
              let acc := z.1.2.2.1 + z.2.2.2.2
              if S ≤ count then freyaHRFinish (m:=m) z.1 (z.2.2.2.1, z.1.2.2.2.1 + (S : ℝ)⁻¹ • acc)
              else (z.1.1, count, acc, z.1.2.2.2.1, z.1.2.2.2.2.1, z.1.2.2.2.2.2)) :=
          Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) hfull hdiff
        have h := (measurable_fst.sumElim hsome).comp
          (MeasurableEquiv.prodSumDistrib ((List ℕ × ℕ × Space d × Space d × ℕ × (ℕ → (Space d × Space d)))) Unit (Fin m × Bool × Space d × Space d)).measurable
        convert h using 1
        funext z
        rcases z with ⟨s,e⟩
        cases e <;> rfl
      let freyaHRReplay (d m S : ℕ) (events : ℕ → freyaHREvent d m) : ℕ → freyaHRReplayState d m :=
        Nat.rec (freyaHRReplayInitial d m) (fun t s => freyaHRStep d m S s (events t))
      have freyaHRMeasurable_decodeEntry (d m n : ℕ) : Measurable (@freyaHRDecodeEntry d m n) :=
        freyaDevelopmentOptionElimMeas _ _ ((freyaHRMeasurable_rawEvent d m n).comp
          (measurable_fst.snd.prodMk measurable_snd.fst))
      let freyaHRHistoryEvents (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) (a : ℕ) : freyaHREvent q.d q.m :=
        freyaHRDecodeEntry (if a < (batchStartCall q O z.1 z.2 b).getD 0 then
          let s := trace q O z.1 z.2 a
          let r := replyAt q O z.1 z.2 a (query q s)
          some (query q s, r, collectorPendingAfter q s r)
        else none)
      have freyaHRFullCoreStep (q : Raw) (s : State q) (path : ℕ → freyaHRPair q.d)
          (first : Bool) (c : FullState q.d q.m q.n) (hp : s.phase = .full first c)
          (i : Fin q.n) (j : Job q.d q.m) (time : ℝ≥0) (v : Space q.d)
          (ho : c.original = List.ofFn (fun i : Fin q.m => i)) (hne : c.remaining ≠ [])
          (hj : c.pending i = some j) (ht : c.clock ≤ time) (hb : s.iteration < rounds q) :
          let c' := fullUpdate c (some (i,j.id,time,v))
          freyaHRStep q.d q.m q.S (freyaHRCore s path) (Sum.inr (j.component,true,s.x,v)) =
            freyaHRCore (update q s (some (i,j.id,time,v)))
              (if c'.remaining = [] then Function.update path s.iteration (s.x,fullResult c') else path) := by
        clear * - q s path first c hp i j time v ho hne hj ht hb freyaHRPair freyaHRRemainingAfter freyaHRAccepts freyaHRFinish freyaHRCore freyaHRFullFields freyaHRStep freyaHRCore_advance

        dsimp only
        obtain ⟨hor,hr,ha⟩ := freyaHRFullFields c i j time v ho hne hj ht
        have hv : fullResult (fullUpdate c (some (i,j.id,time,v))) =
            (q.m : ℝ)⁻¹ • (if freyaHRAccepts q.m c.remaining j.component then c.sum+v else c.sum) := by
          dsimp only [fullResult]
          rw [hor,ho,ha]
          simp (config := { iota := false }) only [List.length_ofFn]
        dsimp only [update]
        rw [hp]
        dsimp only
        by_cases he : (fullUpdate c (some (i,j.id,time,v))).remaining=[]
        · rw [ite_eq_left (by simpa (config := { iota := false }) only [List.isEmpty_iff] using he),ite_eq_left he]
          rw [freyaHRCore_advance q _ _ (by exact hb)]
          dsimp only [freyaHRCore]
          rw [hp]
          simp (config := { iota := false }) only [freyaHRStep,freyaHRFinish,Sum.elim_inr,ite_true]
          have he' : freyaHRRemainingAfter q.m c.remaining j.component=[] := hr.symm.trans he
          rw [ite_eq_left he',hv]
        · rw [ite_eq_right (by simpa (config := { iota := false }) only [List.isEmpty_iff] using he),ite_eq_right he]
          dsimp only [freyaHRCore,freyaHRStep]
          rw [hp]
          simp (config := { iota := false }) only [Sum.elim_inr,ite_true]
          have he' : freyaHRRemainingAfter q.m c.remaining j.component≠[] := by simpa (config := { iota := false }) only [hr] using he
          rw [ite_eq_right he',hr,ha]
      have freyaHRDifferenceCoreStep (q : Raw) (s : State q) (path : ℕ → freyaHRPair q.d)
          (c : DifferenceState q.d q.m q.n) (hp : s.phase = .difference c)
          (i : Fin q.n) (j : Job q.d q.m) (time : ℝ≥0) (v : Space q.d)
          (ho : c.target = q.S) (hne : c.count < c.target)
          (hj : c.pending i = some j) (ht : c.clock ≤ time) (hb : s.iteration < rounds q) :
          let c' := differenceUpdate c (some (i,j.id,time,v))
          freyaHRStep q.d q.m q.S (freyaHRCore s path) (Sum.inr (j.component,false,s.x,v)) =
            freyaHRCore (update q s (some (i,j.id,time,v)))
              (if q.S ≤ c'.count then Function.update path s.iteration (s.x,s.g+differenceResult c') else path) := by
        clear * - q s path c hp i j time v ho hne hj ht hb freyaHRPair freyaHRDifferenceFields freyaHRFinish freyaHRCore freyaHRStep freyaHRCore_advance

        dsimp only
        obtain ⟨hor,hr,ha⟩ := freyaHRDifferenceFields c i j time v hne hj ht
        have htarget := hor.trans ho
        have hv : differenceResult (differenceUpdate c (some (i,j.id,time,v))) =
            (q.S : ℝ)⁻¹ • (c.sum+v) := by
          dsimp only [differenceResult]
          rw [htarget,ha]
        dsimp only [update]
        rw [hp]
        dsimp only
        rw [htarget]
        by_cases he : q.S ≤ (differenceUpdate c (some (i,j.id,time,v))).count
        · rw [ite_eq_left he,ite_eq_left he]
          rw [freyaHRCore_advance q _ _ (by exact hb)]
          dsimp only [freyaHRCore]
          rw [hp]
          simp (config := { iota := false }) only [freyaHRStep,freyaHRFinish,Sum.elim_inr,Bool.false_eq_true,ite_false]
          have he' : q.S ≤ c.count+1 := by simpa (config := { iota := false }) only [hr] using he
          rw [ite_eq_left he',hv]
        · rw [ite_eq_right he,ite_eq_right he]
          dsimp only [freyaHRCore,freyaHRStep]
          rw [hp]
          simp (config := { iota := false }) only [Sum.elim_inr,Bool.false_eq_true,ite_false]
          have he' : ¬ q.S ≤ c.count+1 := by simpa (config := { iota := false }) only [hr] using he
          rw [ite_eq_right he',hr,ha]
      have freyaHRRawEvent_full {d m n : ℕ} (r : Request d m n) (i : Fin n)
          (j : Job d m) (c : ℝ≥0) (v x : Space d) (hj : r.pending i = some j)
          (hk : j.kind = Sum.inl x) :
          freyaHRRawEvent (some r, some (i,j.id,c,v)) = Sum.inr (j.component,true,x,v) := by
        clear * - d m n r i j c v x hj hk freyaHRFullKind freyaHRPointOfKind freyaHREventFromJob freyaHRRawEvent freyaHRRawEvent_matching

        rw [freyaHRRawEvent_matching r i j c v hj]
        simp (config := { iota := false }) [freyaHREventFromJob,freyaHRFullKind,freyaHRPointOfKind,hk]
      have freyaHRRawEvent_difference {d m n : ℕ} (r : Request d m n) (i : Fin n)
          (j : Job d m) (c : ℝ≥0) (v x y : Space d) (hj : r.pending i = some j)
          (hk : j.kind = Sum.inr (x,y)) :
          freyaHRRawEvent (some r, some (i,j.id,c,v)) = Sum.inr (j.component,false,x,v) := by
        clear * - d m n r i j c v x y hj hk freyaHRFullKind freyaHRPointOfKind freyaHREventFromJob freyaHRRawEvent freyaHRRawEvent_matching

        rw [freyaHRRawEvent_matching r i j c v hj]
        simp (config := { iota := false }) [freyaHREventFromJob,freyaHRFullKind,freyaHRPointOfKind,hk]
      have freyaAllBatchBoundaries (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r))) :
          ∀ b,b≤rounds q → ∃ a e,batchStartCall q O seed ω b=some a ∧ batchEndCall q O seed ω b=some e := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaBatchZeroStart freyaEndOfStart freyaBatchNextStart

        intro b
        induction b with
        | zero =>
          intro _
          have hs := freyaBatchZeroStart q hm hn hK O seed ω
          obtain ⟨e,he⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice 0 0 hs
          exact ⟨0,e,hs,he⟩
        | succ b ih =>
          intro hb
          obtain ⟨a,e,hs,he⟩ := ih (by omega)
          have hnext := freyaBatchNextStart q O seed ω b a e (by omega) hs he
          obtain ⟨e',he'⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice (b+1) e hnext
          exact ⟨e,e',hnext,he'⟩
      have freyaObservedNextStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ) (hb : b<rounds q)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e) :
          batchStartCall q O seed ω (b+1)=some e ∧
            (trace q O seed ω e).x=(observedPair q O seed ω b).1-q.η • (observedPair q O seed ω b).2 ∧
            (trace q O seed ω e).g=(observedPair q O seed ω b).2 := by
        clear * - q O seed ω b a e hb hs he freyaBatchExitObserved freyaBatchNextStart

        refine ⟨freyaBatchNextStart q O seed ω b a e hb hs he,?_⟩
        obtain ⟨t,hti,_,hpair,_,hout⟩ := freyaBatchExitObserved q O seed ω b a e hs he
        rw [hout]
        dsimp only [advance]
        rw [ite_eq_right (show ¬rounds q≤t.iteration by omega)]
        dsimp only
        rw [← hpair]
        exact ⟨rfl,rfl⟩
      have freyaObservedDifferenceEnd (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (b firstID a : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hinv : invocation q O seed ω b=some (false,x,y,clock,firstID))
          (hs : batchStartCall q O seed ω b=some a) :
          batchEndCall q O seed ω b=some (a+q.S) ∧
            (observedPair q O seed ω b).2=(trace q O seed ω a).g+batchResult q O seed ω b := by
        clear * - q hm hn hS hK f τ O seed ω hservice b firstID a x y clock hinv hs freyaDifferenceLiveStep freyaPageDifferenceQuery freyaAdvanceLeaves freyaBatchEndFromPrefix freyaPageBatchProgress freyaPageFreshDifference freyaBatchEndExists freyaObservedPosition

        obtain ⟨a',hs',hphase⟩ := freyaPageFreshDifference q O seed ω b firstID x y clock hinv
        have heq : a'=a := Option.some.inj (hs'.symm.trans hs)
        subst a'
        have hlt : q.S-1<q.S := by omega
        obtain ⟨c,hc,hit,ht,hcount,hx,hy,_,_,_,hpending⟩ :=
          freyaPageBatchProgress q hm hn hS f τ O seed ω hservice b firstID a x y clock hs hphase (q.S-1) hlt
        have hlegal : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
          intro i
          obtain ⟨job,hj,hb,he,hk,_⟩ := hpending i
          exact ⟨job,hj,hb,he,by simpa (config := { iota := false }) only [hx,hy] using hk⟩
        obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,hu,_⟩ :=
          freyaDifferenceLiveStep hm hn c f τ
            (fun r => replyAt q O seed ω (a+(q.S-1)) (0,r))
            (hservice (a+(q.S-1))).2 (by omega) hlegal
        let cnew := differenceUpdate c
          (replyAt q O seed ω (a+(q.S-1)) (0,differenceQuery c))
        let t : State q := {trace q O seed ω (a+(q.S-1)) with
          g := (trace q O seed ω (a+(q.S-1))).g+differenceResult cnew
          clock := cnew.clock
          nextID := cnew.nextID
          phase := Phase.difference cnew}
        have hfinal : trace q O seed ω (a+q.S)=advance q t := by
          have hSS : q.S-1+1=q.S := by omega
          rw [← hSS,← Nat.add_assoc]
          change update q (trace q O seed ω (a+(q.S-1)))
            (replyAt q O seed ω (a+(q.S-1)) (query q (trace q O seed ω (a+(q.S-1)))))=_
          rw [freyaPageDifferenceQuery q _ c hc]
          dsimp only [update]
          rw [hc]
          dsimp only
          rw [ite_eq_left (show cnew.target≤cnew.count by dsimp only [cnew]; rw [hu]; dsimp only; omega)]
        have hend : batchEndCall q O seed ω b=some (a+q.S) := by
          apply freyaBatchEndFromPrefix q O (seed,ω) b a q.S hS hs
            (freyaBatchEndExists q hm hn hS hK f τ O (seed,ω) hservice b firstID false x y clock hinv)
          · intro j hj
            obtain ⟨c,hc,hit,_⟩ := freyaPageBatchProgress q hm hn hS f τ O seed ω hservice
              b firstID a x y clock hs hphase j hj
            exact ⟨hit,by dsimp only [active]; rw [hc]⟩
          · rw [hfinal]
            have htit : t.iteration=b := hit
            rw [← htit]
            exact freyaAdvanceLeaves q t
        refine ⟨hend,?_⟩
        have hsub : a+q.S-1=a+(q.S-1) := by omega
        have hg := (freyaObservedPosition q O seed ω b a (a+q.S) hs hend).2
        rw [hsub] at hg
        dsimp only [observedPair,batchResult]
        rw [hend,ite_eq_right (show q.S≠0 by omega),hs]
        dsimp only [Option.getD_some]
        rw [hsub,hc,hg]
      have freyaPastStart (q : Raw) (k : ℕ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (a : ℕ) → O.Seed a)
          (hrows : new.1=seed.1) (hbits : ∀ j<k,new.2.1 j=seed.2.1 j) (b : ℕ) (hb : b≤k) :
          batchStartCall q O new ω b=batchStartCall q O seed ω b := by
        clear * - q k O seed new ω hrows hbits b hb freyaControlRecord freyaPastTrace hobl

        apply congrArg (fun p => (List.range (eventLimit q+1)).find? p)
        funext a
        rcases freyaPastTrace q k O hobl seed new ω hrows hbits a with h|⟨hn,ho⟩
        · rw [freyaControlRecord q _ _ h]
          rfl
        · have hne : (trace q O new ω a).iteration≠b := by omega
          have hoe : (trace q O seed ω a).iteration≠b := by omega
          simp (config := { iota := false }) only [hne,hoe,decide_false,Bool.false_and]
      have freyaPageUpdateMeas (q : Raw) :
          Measurable (fun z : State q × Reply q.d q.n => update q z.1 z.2) := by
        clear * - q freyaStateCode freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPhaseFullMeas freyaPhaseDifferenceMeas freyaStateConstructMeas freyaPhaseParamMeas freyaFullUpdateMeas freyaDifferenceUpdateMeas freyaPageAdvanceMeas

        classical
        have hfull : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            let c := fullUpdate z.2.2 z.1.2
            let s := {z.1.1 with
              clock:=c.clock
              nextID:=c.nextID
              phase:=Phase.full z.2.1 c}
            if c.remaining.isEmpty then advance q {s with g:=fullResult c} else s) := by
          have hs : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              fullUpdate z.2.2 z.1.2) := freyaFullUpdateMeas.comp (measurable_snd.snd.prodMk measurable_fst.snd)
          have hc := freyaFullCodeMeas.comp hu
          have hp := freyaPhaseFullMeas.comp (measurable_snd.fst.prodMk hu)
          have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp
          have hg := ((measurable_of_countable (fun l : List (Fin q.m) => (l.length : ℝ)⁻¹)).comp hc.fst).smul
            hc.snd.snd.snd.fst
          have hnext := (freyaPageAdvanceMeas q).comp
            (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
              hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
              hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp)
          exact hnext.ite (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst)
            (measurableSet_singleton true)) hbase
        have hdiff : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            let c := differenceUpdate z.2 z.1.2
            let s := {z.1.1 with
              clock:=c.clock
              nextID:=c.nextID
              phase:=Phase.difference c}
            if c.target≤c.count then advance q {s with g:=s.g+differenceResult c} else s) := by
          have hs : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              differenceUpdate z.2 z.1.2) := freyaDifferenceUpdateMeas.comp (measurable_snd.prodMk measurable_fst.snd)
          have hc := freyaDifferenceCodeMeas.comp hu
          have hp := freyaPhaseDifferenceMeas.comp hu
          have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp
          have hg := hs.snd.snd.snd.fst.add
            (((measurable_of_countable (fun a : ℕ => (a : ℝ)⁻¹)).comp hc.fst).smul hc.snd.snd.snd.snd.fst)
          have hnext := (freyaPageAdvanceMeas q).comp
            (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
              hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
              hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp)
          exact hnext.ite (measurableSet_le hc.fst hc.snd.fst) hbase
        have h := freyaPhaseParamMeas (fun z : State q × Reply q.d q.n => z.1.phase)
          (((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd).comp measurable_fst)
          Prod.fst measurable_fst _ hfull _ hdiff
        convert h using 1
        funext z
        delta update
        cases z.1.phase <;> rfl
      have freyaObservedFinishMeas (q : Raw) :
          Measurable (fun z : State q × Reply q.d q.n => freyaObservedFinish q z.1 z.2) := by
        clear * - q freyaStateCode freyaObservedFinish freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPhaseParamMeas freyaFullUpdateMeas freyaDifferenceUpdateMeas

        have hs : Measurable (fun z : State q × Reply q.d q.n => freyaStateCode z.1) :=
          (freyaStateCodeMeas q).comp measurable_fst
        have hfull : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            (z.1.1.x,fullResult (fullUpdate z.2.2 z.1.2))) := by
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              fullUpdate z.2.2 z.1.2) := freyaFullUpdateMeas.comp (measurable_snd.snd.prodMk measurable_fst.snd)
          have hc := freyaFullCodeMeas.comp hu
          have hsize := (measurable_of_countable (fun l : List (Fin q.m) => (l.length : ℝ)⁻¹)).comp hc.fst
          exact (hs.snd.snd.fst.comp measurable_fst).prodMk (hsize.smul hc.snd.snd.snd.fst)
        have hdiff : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            (z.1.1.x,z.1.1.g+differenceResult (differenceUpdate z.2 z.1.2))) := by
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              differenceUpdate z.2 z.1.2) := freyaDifferenceUpdateMeas.comp (measurable_snd.prodMk measurable_fst.snd)
          have hc := freyaDifferenceCodeMeas.comp hu
          have hsize := (measurable_of_countable (fun a : ℕ => (a : ℝ)⁻¹)).comp hc.fst
          exact (hs.snd.snd.fst.comp measurable_fst).prodMk
            ((hs.snd.snd.snd.fst.comp measurable_fst).add (hsize.smul hc.snd.snd.snd.snd.fst))
        have h := freyaPhaseParamMeas (fun z : State q × Reply q.d q.n => z.1.phase)
          hs.snd.snd.snd.snd.snd.snd.snd (fun z => (z.1.x,z.1.g))
          (hs.snd.snd.fst.prodMk hs.snd.snd.snd.fst) _ hfull _ hdiff
        convert h using 1
        funext z
        dsimp only [freyaObservedFinish]
        cases z.1.phase <;> rfl
      have freyaHRMeasurable_replay (d m S t : ℕ) :
          Measurable (fun events : ℕ → freyaHREvent d m => freyaHRReplay d m S events t) := by
        clear * - d m S t freyaHREvent freyaHRMeasurable_step freyaHRReplay

        induction t with
        | zero => exact measurable_const
        | succ t ih =>
          exact (freyaHRMeasurable_step d m S).comp (ih.prodMk (measurable_pi_apply t))
      have freyaHRMeasurable_historyEvents (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ) :
          Measurable[historyBefore q O b] (freyaHRHistoryEvents q O b) := by
        clear * - q O b freyaHRMeasurable_decodeEntry freyaHRHistoryEvents

        let : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k)) := historyBefore q O b
        have hh : Measurable[historyBefore q O b] (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
            (invocation q O z.1 z.2 b, fun a : ℕ =>
              if a < (batchStartCall q O z.1 z.2 b).getD 0 then
                let s := trace q O z.1 z.2 a
                let r := replyAt q O z.1 z.2 a (query q s)
                some (query q s, r, collectorPendingAfter q s r)
              else none)) := Measurable.of_comap_le le_rfl
        apply Measurable.of_eval
        intro a
        exact (freyaHRMeasurable_decodeEntry q.d q.m q.n).comp ((measurable_pi_apply a).comp hh.snd)
      have freyaHRReplay_truncate (d m S : ℕ) (events : ℕ → freyaHREvent d m) (cut t : ℕ) :
          freyaHRReplay d m S (fun a => if a<cut then events a else Sum.inl ()) t =
            freyaHRReplay d m S events (min t cut) := by
        clear * - d m S events cut t freyaHREvent freyaHRStep freyaHRReplay

        induction t with
        | zero => rfl
        | succ t ih =>
          change freyaHRStep d m S (freyaHRReplay d m S (fun a => if a<cut then events a else Sum.inl ()) t)
            (if t<cut then events t else Sum.inl ()) = _
          rw [ih]
          by_cases h : t<cut
          · rw [ite_eq_left h,Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]
          · rw [ite_eq_right h,Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
            rfl
      have freyaHRHistoryEvents_truncate (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
          freyaHRHistoryEvents q O b z = fun a =>
            if a<(batchStartCall q O z.1 z.2 b).getD 0 then freyaHRActualEvents q O z a else Sum.inl () := by
        clear * - q O b z freyaHRActualEvents freyaHRHistoryEvents

        funext a
        unfold freyaHRHistoryEvents
        split <;> rfl
      have freyaHRFullCoreStep_iteration (q : Raw) (s : State q) (path : ℕ → freyaHRPair q.d)
          (first : Bool) (c : FullState q.d q.m q.n) (hp : s.phase = .full first c)
          (i : Fin q.n) (j : Job q.d q.m) (time : ℝ≥0) (v : Space q.d)
          (ho : c.original = List.ofFn (fun i : Fin q.m => i)) (hne : c.remaining ≠ [])
          (hj : c.pending i = some j) (ht : c.clock ≤ time) (hb : s.iteration < rounds q) :
          let t := update q s (some (i,j.id,time,v))
          freyaHRStep q.d q.m q.S (freyaHRCore s path) (Sum.inr (j.component,true,s.x,v)) =
            freyaHRCore t (if t.iteration=s.iteration then path else Function.update path s.iteration (s.x,t.g)) := by
        clear * - q s path first c hp i j time v ho hne hj ht hb freyaHRPair freyaHRCore freyaHRStep freyaHRFullCoreStep

        dsimp only
        rw [freyaHRFullCoreStep q s path first c hp i j time v ho hne hj ht hb]
        by_cases he : (fullUpdate c (some (i,j.id,time,v))).remaining=[]
        · rw [ite_eq_left he]
          have hi : (update q s (some (i,j.id,time,v))).iteration=s.iteration+1 := by
            delta update
            rw [hp]
            dsimp only
            dsimp only [advance]
            simp (config := { iota := false }) [he,not_le.mpr hb]
          have hg : (update q s (some (i,j.id,time,v))).g=fullResult (fullUpdate c (some (i,j.id,time,v))) := by
            delta update
            rw [hp]
            dsimp only
            dsimp only [advance]
            simp (config := { iota := false }) [he,not_le.mpr hb]
          rw [hi,ite_eq_right (by omega),hg]
        · rw [ite_eq_right he]
          have hi : (update q s (some (i,j.id,time,v))).iteration=s.iteration := by
            delta update
            rw [hp]
            dsimp only
            simp (config := { iota := false }) [List.isEmpty_iff,he]
          rw [hi,ite_eq_left rfl]
      have freyaHRDifferenceCoreStep_iteration (q : Raw) (s : State q) (path : ℕ → freyaHRPair q.d)
          (c : DifferenceState q.d q.m q.n) (hp : s.phase = .difference c)
          (i : Fin q.n) (j : Job q.d q.m) (time : ℝ≥0) (v : Space q.d)
          (ho : c.target = q.S) (hne : c.count < c.target)
          (hj : c.pending i = some j) (ht : c.clock ≤ time) (hb : s.iteration < rounds q) :
          let t := update q s (some (i,j.id,time,v))
          freyaHRStep q.d q.m q.S (freyaHRCore s path) (Sum.inr (j.component,false,s.x,v)) =
            freyaHRCore t (if t.iteration=s.iteration then path else Function.update path s.iteration (s.x,t.g)) := by
        clear * - q s path c hp i j time v ho hne hj ht hb freyaHRPair freyaHRDifferenceFields freyaHRCore freyaHRStep freyaHRDifferenceCoreStep

        dsimp only
        rw [freyaHRDifferenceCoreStep q s path c hp i j time v ho hne hj ht hb]
        have htarget := (freyaHRDifferenceFields c i j time v hne hj ht).1.trans ho
        by_cases he : q.S ≤ (differenceUpdate c (some (i,j.id,time,v))).count
        · rw [ite_eq_left he]
          have hi : (update q s (some (i,j.id,time,v))).iteration=s.iteration+1 := by
            delta update
            rw [hp]
            dsimp only
            dsimp only [advance]
            simp (config := { iota := false }) [htarget,he,not_le.mpr hb]
          have hg : (update q s (some (i,j.id,time,v))).g=s.g+differenceResult (differenceUpdate c (some (i,j.id,time,v))) := by
            delta update
            rw [hp]
            dsimp only
            dsimp only [advance]
            simp (config := { iota := false }) [htarget,he,not_le.mpr hb]
          rw [hi,ite_eq_right (by omega),hg]
        · rw [ite_eq_right he]
          have hi : (update q s (some (i,j.id,time,v))).iteration=s.iteration := by
            delta update
            rw [hp]
            dsimp only
            simp (config := { iota := false }) [htarget,he]
          rw [hi,ite_eq_left rfl]
      have freyaBatchNextTag (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hservice : servicePath f τ (fun k r => replyAt q O z.1 z.2 k (0,r)))
          (b : ℕ) (hb : b<rounds q) :
          freyaBatchTag q O (b+1) z=if refreshAt z.1 b then 0 else 1 := by
        clear * - q hm hn hS hK f τ O z hservice b hb freyaBatchTag freyaBatchExitState freyaBatchNextStart freyaAllBatchBoundaries

        obtain ⟨a,e,hs,he⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O z.1 z.2 hservice b (by omega)
        have hnext := freyaBatchNextStart q O z.1 z.2 b a e hb hs he
        obtain ⟨t,hti,hts,hout⟩ := freyaBatchExitState q O z.1 z.2 b a e hs he
        dsimp only [freyaBatchTag,invocation]
        rw [hnext]
        dsimp only [Option.bind_some]
        rw [hout]
        dsimp only [advance]
        rw [ite_eq_right (show ¬rounds q≤t.iteration by omega)]
        dsimp only
        rw [hti,hts]
        cases hbit : refreshAt z.1 b <;> rfl
      have freyaObservedDifference (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (b firstID a : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hinv : invocation q O seed ω b=some (false,x,y,clock,firstID))
          (hs : batchStartCall q O seed ω b=some a) :
          (observedPair q O seed ω b).2=(trace q O seed ω a).g+
            (q.S : ℝ)⁻¹ • (∑ j : Fin q.S,(completedLabels q O seed ω b j).elim 0
              (fun i => gradient (f i) x-gradient (f i) y)) := by
        clear * - q hm hn hS hK f τ O seed ω hservice b firstID a x y clock hinv hs freyaObservedDifferenceEnd

        rw [(freyaObservedDifferenceEnd q hm hn hS hK f τ O seed ω hservice b firstID a x y clock hinv hs).2]
        rw [difference_average q hm hn hS hK f τ O seed ω hservice b firstID x y clock hinv]
      have freyaPastEnd (q : Raw) (k : ℕ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (a : ℕ) → O.Seed a)
          (hrows : new.1=seed.1) (hbits : ∀ j<k,new.2.1 j=seed.2.1 j) (b : ℕ) (hb : b≤k) :
          batchEndCall q O new ω b=batchEndCall q O seed ω b := by
        clear * - q k O seed new ω hrows hbits b hb freyaControlRecord freyaPastTrace freyaPastStart hobl

        dsimp only [batchEndCall]
        rw [freyaPastStart q k O hobl seed new ω hrows hbits b hb]
        congr 1
        funext first
        congr 1
        funext a
        rcases freyaPastTrace q k O hobl seed new ω hrows hbits a with h|⟨hn,ho⟩
        · rw [freyaControlRecord q _ _ h]
          rfl
        · have hne : (trace q O new ω a).iteration≠b := by omega
          have hoe : (trace q O seed ω a).iteration≠b := by omega
          rw [show decide ((trace q O new ω a).iteration≠b)=true from decide_eq_true_eq.mpr hne,
            show decide ((trace q O seed ω a).iteration≠b)=true from decide_eq_true_eq.mpr hoe]
          simp (config := { iota := false }) only [Bool.true_or]
      have freyaPageTraceMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (k : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => trace q O z.1 z.2 k) := by
        clear * - q f τ O hservice k freyaPageQueryMeas freyaPageInitialMeas freyaPageUpdateMeas

        exact (measurable_trajectory q O hservice.1.2 (freyaPageInitialMeas q)
          (freyaPageUpdateMeas q) (freyaPageQueryMeas q) k).1
      have freyaHRMeasurable_savedPath {Ω : Type} [MeasurableSpace Ω]
          (d m S t k : ℕ) (events : Ω → ℕ → freyaHREvent d m) (he : Measurable events) :
          Measurable (fun z => fun j : Fin k => (freyaHRReplay d m S (events z) t).2.2.2.2.2 j.val) := by
        clear * - Ω d m S t k events he freyaHREvent freyaHRReplay freyaHRMeasurable_replay

        apply Measurable.of_eval
        intro j
        exact (measurable_pi_apply j.val).comp
          (((freyaHRMeasurable_replay d m S t).comp he).snd.snd.snd.snd.snd)
      have freyaHRReplay_history_cutoff (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hc : (batchStartCall q O z.1 z.2 b).getD 0 ≤ eventLimit q+1) :
          freyaHRReplay q.d q.m q.S (freyaHRHistoryEvents q O b z) (eventLimit q+1) =
            freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O z) ((batchStartCall q O z.1 z.2 b).getD 0) := by
        clear * - q O b z hc freyaHRActualEvents freyaHRReplay freyaHRHistoryEvents freyaHRReplay_truncate freyaHRHistoryEvents_truncate

        rw [freyaHRHistoryEvents_truncate]
        have h := freyaHRReplay_truncate q.d q.m q.S (freyaHRActualEvents q O z)
          ((batchStartCall q O z.1 z.2 b).getD 0) (eventLimit q+1)
        rw [Nat.min_eq_right hc] at h
        exact h
      have freyaHRCore_trace_step (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (a : ℕ) (path : ℕ → freyaHRPair q.d) (ha : active (trace q O seed ω a)=true)
          (hb : (trace q O seed ω a).iteration<rounds q) :
          freyaHRStep q.d q.m q.S (freyaHRCore (trace q O seed ω a) path) (freyaHRActualEvents q O (seed,ω) a) =
            freyaHRCore (trace q O seed ω (a+1))
              (if (trace q O seed ω (a+1)).iteration=(trace q O seed ω a).iteration then path
              else Function.update path (trace q O seed ω a).iteration
                ((trace q O seed ω a).x,(trace q O seed ω (a+1)).g)) := by
        clear * - q hm hn hS hK f τ O seed ω hservice a path ha hb freyaPageDifferenceQuery freyaPageFullQuery freyaHRPair freyaPagePhaseSafety freyaHRRawEvent freyaHRCore freyaHRDifferencePoint_trace freyaPageGradientTrace freyaHRStep freyaHRActualEvents freyaHRRawEvent_full freyaHRRawEvent_difference freyaHRFullCoreStep_iteration freyaHRDifferenceCoreStep_iteration

        let s := trace q O seed ω a
        change freyaHRStep q.d q.m q.S (freyaHRCore s path) (freyaHRRawEvent ((query q s).2,replyAt q O seed ω a (query q s))) =
          freyaHRCore (update q s (replyAt q O seed ω a (query q s)))
            (if (update q s (replyAt q O seed ω a (query q s))).iteration=s.iteration then path
            else Function.update path s.iteration (s.x,(update q s (replyAt q O seed ω a (query q s))).g))
        cases hp : s.phase with
        | halted => change active s=true at ha; delta active at ha; rw [hp] at ha; contradiction
        | full first c =>
          obtain ⟨horig,hpoint,hgrad⟩ := freyaPageGradientTrace q hm hn hS hK f τ O seed ω hservice a first c hp
          obtain ⟨_,hne,_,hlegal⟩ := (freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice a).1 first c hp
          have hex : ∃ i,c.pending i≠none := by
            obtain ⟨i,j,hj⟩ := hlegal.1
            change c.pending i=some j at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          have hquery : query q s=(0,some ⟨c.clock,c.pending⟩) := by
            rw [freyaPageFullQuery q s first c hp]
            delta fullQuery pendingRequest
            simp (config := { iota := false }) only [List.isEmpty_iff,hne,ite_false,hex,ite_true]
          obtain ⟨i,j,time,hj,hr,ht,_⟩ := (hservice a).2 ⟨c.clock,c.pending⟩ hlegal
          change c.pending i=some j at hj
          change replyAt q O seed ω a (0,some ⟨c.clock,c.pending⟩)=some (i,j.id,time,jobValue f j) at hr
          change c.clock≤time at ht
          have hk : j.kind=Sum.inl s.x := (hgrad.2 i j hj).trans (congrArg Sum.inl hpoint)
          rw [hquery,hr]
          rw [freyaHRRawEvent_full _ i j time (jobValue f j) s.x hj hk]
          exact freyaHRFullCoreStep_iteration q s path first c hp i j time (jobValue f j) horig hne hj ht hb
        | difference c =>
          obtain ⟨htarget,hcount,hpending⟩ := (freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice a).2.1 c hp
          have hx := freyaHRDifferencePoint_trace q O seed ω a c hp
          have hlegal : legalRequest τ ⟨c.clock,c.pending⟩ := by
            constructor
            · obtain ⟨j,hj,_⟩ := hpending ⟨0,hn⟩
              exact ⟨⟨0,hn⟩,j,hj⟩
            · intro i j hj
              obtain ⟨j',hj',hstart,hend,_⟩ := hpending i
              have he : j'=j := Option.some.inj (hj'.symm.trans hj)
              subst j'
              exact ⟨hstart,hend⟩
          have hex : ∃ i,c.pending i≠none := by
            obtain ⟨i,j,hj⟩ := hlegal.1
            change c.pending i=some j at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          have hquery : query q s=(0,some ⟨c.clock,c.pending⟩) := by
            rw [freyaPageDifferenceQuery q s c hp]
            delta differenceQuery pendingRequest
            simp (config := { iota := false }) only [not_le.mpr hcount,ite_false,hex,ite_true]
          obtain ⟨i,j,time,hj,hr,ht,_⟩ := (hservice a).2 ⟨c.clock,c.pending⟩ hlegal
          change c.pending i=some j at hj
          change replyAt q O seed ω a (0,some ⟨c.clock,c.pending⟩)=some (i,j.id,time,jobValue f j) at hr
          change c.clock≤time at ht
          have hk : j.kind=Sum.inr (s.x,c.y) := by
            obtain ⟨j',hj',_,_,hkind⟩ := hpending i
            have he : j'=j := Option.some.inj (hj'.symm.trans hj)
            subst j'
            simpa (config := { iota := false }) only [hx] using hkind
          rw [hquery,hr]
          rw [freyaHRRawEvent_difference _ i j time (jobValue f j) s.x c.y hj hk]
          exact freyaHRDifferenceCoreStep_iteration q s path c hp i j time (jobValue f j) htarget hcount hj ht hb
      have freyaObservedTransition (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (hf : ∀ i,Differentiable ℝ (f i)) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (b : ℕ) (hb : b<rounds q) :
          let pair := observedPair q O seed ω b
          let x := pair.1-q.η • pair.2
          observedPair q O seed ω (b+1)=
            if refreshAt seed b then (x,gradient (objective f) x) else
              (x,pair.2+(q.S : ℝ)⁻¹ • (∑ j : Fin q.S,(completedLabels q O seed ω (b+1) j).elim 0
                (fun i => gradient (f i) x-gradient (f i) pair.1))) := by
        clear * - q hm hn hS hK f hf τ O seed ω hservice b hb freyaEndOfStart freyaBatchExitObserved freyaObservedPosition freyaObservedFull freyaAllBatchBoundaries freyaObservedNextStart freyaObservedDifference

        obtain ⟨a,e,hs,he⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O seed ω hservice b hb.le
        obtain ⟨hnext,hxnext,hgnext⟩ := freyaObservedNextStart q O seed ω b a e hb hs he
        obtain ⟨e',he'⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice (b+1) e hnext
        have hx := (freyaObservedPosition q O seed ω (b+1) e e' hnext he').1.trans hxnext
        obtain ⟨t,hti,htseed,hpair,_,hout⟩ := freyaBatchExitObserved q O seed ω b a e hs he
        have hstop : ¬rounds q≤t.iteration := by omega
        have hpoint : t.x-q.η • t.g=(observedPair q O seed ω b).1-q.η • (observedPair q O seed ω b).2 := by
          rw [← hpair]
        have hi : invocation q O seed ω (b+1)=
            if refreshAt seed b then some (true,t.x-q.η • t.g,t.x-q.η • t.g,t.clock,t.nextID) else
              some (false,t.x-q.η • t.g,t.x,t.clock,t.nextID) := by
          dsimp only [invocation]
          rw [hnext]
          dsimp only [Option.bind_some]
          rw [hout]
          dsimp only [advance]
          rw [ite_eq_right hstop]
          dsimp only
          rw [htseed,hti]
          cases refreshAt seed b <;>
            simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true] <;>
            dsimp only [fullInitial,differenceInitial] <;>
            simp (config := { iota := false }) only [Nat.add_sub_cancel_right]
        dsimp only
        by_cases hbit : refreshAt seed b=true
        · rw [ite_eq_left hbit] at hi ⊢
          apply Prod.ext hx
          have hg := freyaObservedFull q hm hn hS hK f hf τ O seed ω hservice
            (b+1) t.nextID _ _ t.clock hi
          exact hg.trans (congrArg (gradient (objective f)) hx)
        · rw [ite_eq_right hbit] at hi ⊢
          apply Prod.ext hx
          have hg := freyaObservedDifference q hm hn hS hK f τ O seed ω hservice
            (b+1) t.nextID e _ _ t.clock hi hnext
          rw [hgnext,hpoint,show t.x=(observedPair q O seed ω b).1 from congrArg Prod.fst hpair] at hg
          exact hg
      have freyaPastObserved (q : Raw) (k : ℕ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (a : ℕ) → O.Seed a)
          (hrows : new.1=seed.1) (hbits : ∀ j<k,new.2.1 j=seed.2.1 j)
          (b a e : ℕ) (hb : b≤k) (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          observedPair q O new ω b=observedPair q O seed ω b := by
        clear * - q k O seed new ω hrows hbits b a e hb hs he freyaControl freyaControlRecord freyaBatchEndFacts freyaQueryControl freyaPastTrace freyaPastEnd hobl

        obtain ⟨ha,_,hbefore,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hp := hbefore (e-1) (by omega) (by omega)
        have hc : freyaControl (trace q O new ω (e-1))=freyaControl (trace q O seed ω (e-1)) := by
          rcases freyaPastTrace q k O hobl seed new ω hrows hbits (e-1) with h|h
          · exact h
          · omega
        dsimp only [observedPair]
        simp only [replyAt_seed q O hobl new seed ω]
        rw [freyaPastEnd q k O hobl seed new ω hrows hbits b hb,he]
        dsimp only [Option.getD_some]
        rw [freyaQueryControl q _ _ hc,freyaControlRecord q _ _ hc]
      have freyaPageBatchStartMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (batch : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchStartCall q O z.1 z.2 batch) := by
        clear * - q f τ O hservice batch freyaFindMeas freyaStateCodeMeas freyaActiveMeas freyaPageTraceMeas

        apply freyaFindMeas
        intro k
        have hs := freyaPageTraceMeas q f τ O hservice k
        have hi := ((freyaStateCodeMeas q).comp hs).snd.fst
        have hb := (freyaActiveMeas q).comp hs
        exact (measurable_of_countable (fun p : ℕ × Bool => decide (p.1=batch) && p.2)).comp (hi.prodMk hb)
      have freyaHRMeasurable_historySavedPath (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ) :
          Measurable[historyBefore q O b] (fun z => fun j : Fin b =>
            (freyaHRReplay q.d q.m q.S (freyaHRHistoryEvents q O b z) (eventLimit q + 1)).2.2.2.2.2 j.val) := by
        clear * - q O b freyaHRReplay freyaHRHistoryEvents freyaHRMeasurable_historyEvents freyaHRMeasurable_savedPath

        exact @freyaHRMeasurable_savedPath _ (historyBefore q O b) q.d q.m q.S
          (eventLimit q + 1) b (freyaHRHistoryEvents q O b) (freyaHRMeasurable_historyEvents q O b)
      have freyaHRReplay_batch (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (b a e : ℕ) (hb : b<rounds q)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e)
          (path : ℕ → freyaHRPair q.d)
          (hbegin : freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O (seed,ω)) a=freyaHRCore (trace q O seed ω a) path) :
          freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O (seed,ω)) e =
            freyaHRCore (trace q O seed ω e) (Function.update path b (observedPair q O seed ω b)) := by
        clear * - q hm hn hS hK f τ O seed ω hservice b a e hb hs he path hbegin freyaHRPair freyaPageBatchStartFacts freyaBatchEndFacts freyaHRCore freyaHRStep freyaHRActualEvents freyaHRReplay freyaObservedNextStart freyaHRCore_trace_step

        obtain ⟨ha,_,hbefore,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hpre : ∀ t,a≤t → t<e →
            freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O (seed,ω)) t=freyaHRCore (trace q O seed ω t) path := by
          intro t hat
          induction t,hat using Nat.le_induction with
          | base => intro _; exact hbegin
          | succ t hat ih =>
            intro hte
            have ht := hbefore t hat (by omega)
            have ht' := hbefore (t+1) (by omega) hte
            change freyaHRStep q.d q.m q.S (freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O (seed,ω)) t)
              (freyaHRActualEvents q O (seed,ω) t) = _
            rw [ih (by omega),freyaHRCore_trace_step q hm hn hS hK f τ O seed ω hservice t path ht.2 (by omega)]
            rw [ht.1,ht'.1,ite_eq_left rfl]
        have hed : e-1+1=e := by omega
        have ht := hbefore (e-1) (by omega) (by omega)
        have hnext := freyaObservedNextStart q O seed ω b a e hb hs he
        have hnextIt := (freyaPageBatchStartFacts q O seed ω (b+1) e hnext.1).2.1
        have hx : (trace q O seed ω (e-1)).x=(observedPair q O seed ω b).1 := by
          dsimp only [observedPair]
          rw [he]
          dsimp only [Option.getD_some]
          cases hp : (trace q O seed ω (e-1)).phase <;> rfl
        conv_lhs => rw [← hed]
        change freyaHRStep q.d q.m q.S (freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O (seed,ω)) (e-1))
          (freyaHRActualEvents q O (seed,ω) (e-1)) = _
        rw [hpre (e-1) (by omega) (by omega),
          freyaHRCore_trace_step q hm hn hS hK f τ O seed ω hservice (e-1) path ht.2 (by omega),hed]
        rw [ht.1,hnextIt,ite_eq_right (by omega),hx,hnext.2.2]
      have freyaPastObservedTotal (q : Raw) (k : ℕ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (a : ℕ) → O.Seed a)
          (hrows : new.1=seed.1) (hbits : ∀ j<k,new.2.1 j=seed.2.1 j) (b : ℕ) (hb : b≤k) :
          observedPair q O new ω b=observedPair q O seed ω b := by
        clear * - q k O seed new ω hrows hbits b hb freyaControl freyaControlRecord freyaQueryControl freyaPastEnd freyaPastObserved hobl

        cases he : batchEndCall q O seed ω b with
        | none =>
          dsimp only [observedPair]
          rw [freyaPastEnd q k O hobl seed new ω hrows hbits b hb,he]
          dsimp only [Option.getD_none,Nat.zero_sub]
          have hc : freyaControl (trace q O new ω 0)=freyaControl (trace q O seed ω 0) := by
            dsimp only [trace,run,initial,freyaControl]
            rw [hrows]
          rw [replyAt_seed q O hobl new seed ω,freyaQueryControl q _ _ hc,freyaControlRecord q _ _ hc]
        | some e =>
          cases hs : batchStartCall q O seed ω b with
          | none => dsimp only [batchEndCall] at he; rw [hs] at he; cases he
          | some a => exact freyaPastObserved q k O hobl seed new ω hrows hbits b a e hb hs he
      have freyaBatchEndMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchEndCall q O z.1 z.2 b) := by
        clear * - q f τ O hservice b freyaFindMeas freyaOptionParamMeas freyaStateCodeMeas freyaActiveMeas freyaPageTraceMeas freyaPageBatchStartMeas

        classical
        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        have hp (a : ℕ) : Measurable (fun z : Ω × ℕ => decide (z.2<a) &&
            (decide ((trace q O z.1.1 z.1.2 a).iteration≠b) || !active (trace q O z.1.1 z.1.2 a))) := by
          have ht : Measurable (fun z : Ω × ℕ => trace q O z.1.1 z.1.2 a) :=
            (freyaPageTraceMeas q f τ O hservice a).comp measurable_fst
          have hi := ((freyaStateCodeMeas q).comp ht).snd.fst
          have ha := (freyaActiveMeas q).comp ht
          exact (measurable_of_countable (fun t : ℕ × ℕ × Bool =>
            decide (t.1<a) && (decide (t.2.1≠b) || !t.2.2))).comp
              (measurable_snd.prodMk (hi.prodMk ha))
        have hb := freyaFindMeas (List.range (eventLimit q+1)) _ hp
        have h := freyaOptionParamMeas _ (freyaPageBatchStartMeas q f τ O hservice b)
          (fun _ : Ω => (none : Option ℕ)) measurable_const _ hb
        convert h using 1
        funext z
        dsimp only [batchEndCall]
        cases batchStartCall q O z.1 z.2 b <;> rfl
      have freyaHRReplay_at_start (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          ∀ b,b≤rounds q → ∀ a,batchStartCall q O seed ω b=some a →
            ∃ path : ℕ → freyaHRPair q.d,
              freyaHRReplay q.d q.m q.S (freyaHRActualEvents q O (seed,ω)) a=freyaHRCore (trace q O seed ω a) path ∧
              ∀ j,j<b → path j=observedPair q O seed ω j := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaBatchZeroStart freyaHRPair freyaHRCore freyaHRCore_initial freyaHRActualEvents freyaBatchNextStart freyaHRReplay freyaAllBatchBoundaries freyaHRReplay_batch

        intro b
        induction b with
        | zero =>
          intro _ a hs
          have ha : a=0 := Option.some.inj (hs.symm.trans (freyaBatchZeroStart q hm hn hK O seed ω))
          subst a
          refine ⟨fun _ => (0,0),?_,?_⟩
          · exact (freyaHRCore_initial q seed hm hn hK).symm
          · intro j hj; omega
        | succ b ih =>
          intro hb a hs
          obtain ⟨a0,e,hstart,hend⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O seed ω hservice b (by omega)
          obtain ⟨path,hbegin,hpath⟩ := ih (by omega) a0 hstart
          have hnext := freyaBatchNextStart q O seed ω b a0 e (by omega) hstart hend
          have heq : a=e := Option.some.inj (hs.symm.trans hnext)
          subst a
          refine ⟨Function.update path b (observedPair q O seed ω b),?_,?_⟩
          · exact freyaHRReplay_batch q hm hn hS hK f τ O seed ω hservice b a0 e (by omega) hstart hend path hbegin
          · intro j hj
            by_cases he : j=b
            · subst j; exact Function.update_self _ _ _
            · rw [Function.update_of_ne he]
              exact hpath j (by omega)
      have freyaObservedPairMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((a : ℕ) → O.Seed a) => observedPair q O z.1 z.2 b) := by
        clear * - q f τ O hservice b freyaDevelopmentOptionElimMeas freyaMeasurableSelect freyaObservedFinish freyaPageQueryMeas freyaObservedFinishMeas freyaPageTraceMeas freyaBatchEndMeas freyaPageInitialMeas freyaPageUpdateMeas

        let Ω := Seed q.K × ((a : ℕ) → O.Seed a)
        have hcall : Measurable (fun z : Ω => (batchEndCall q O z.1 z.2 b).getD 0-1) := by
          have h := (measurable_of_countable (fun a : ℕ => a-1)).comp
            ((freyaDevelopmentOptionElimMeas (0 : ℕ) id measurable_id).comp
              (freyaBatchEndMeas q f τ O hservice b))
          convert h using 1
          funext z
          dsimp only [Function.comp_def]
          cases batchEndCall q O z.1 z.2 b <;> rfl
        have hf (a : ℕ) : Measurable (fun z : Ω => freyaObservedFinish q (trace q O z.1 z.2 a)
            (replyAt q O z.1 z.2 a (query q (trace q O z.1 z.2 a)))) := by
          have ht := freyaPageTraceMeas q f τ O hservice a
          exact (freyaObservedFinishMeas q).comp (ht.prodMk (measurable_replyAt q O hservice.1.2 (freyaPageInitialMeas q) (freyaPageUpdateMeas q)
              (freyaPageQueryMeas q) a measurable_id
            ((freyaPageQueryMeas q).comp ht)))
        exact freyaMeasurableSelect _ hcall _ hf
      have freyaHRHistory_savedPath_eq (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) (b : ℕ) (hb : b≤rounds q) :
          (fun j : Fin b => (freyaHRReplay q.d q.m q.S (freyaHRHistoryEvents q O b (seed,ω))
            (eventLimit q+1)).2.2.2.2.2 j.val) =
              fun j : Fin b => observedPair q O seed ω j.val := by
        clear * - q hm hn hS hK f τ O seed ω hservice b hb freyaPageBatchStartFacts freyaHRCore_path freyaHRReplay freyaHRHistoryEvents freyaAllBatchBoundaries freyaHRReplay_history_cutoff freyaHRReplay_at_start

        obtain ⟨a,e,hs,_⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O seed ω hservice b hb
        have hlim := (freyaPageBatchStartFacts q O seed ω b a hs).1
        have hc : (batchStartCall q O seed ω b).getD 0 ≤ eventLimit q+1 := by
          rw [hs]
          dsimp only [Option.getD_some]
          omega
        rw [freyaHRReplay_history_cutoff q O b (seed,ω) hc,hs]
        dsimp only [Option.getD_some]
        obtain ⟨path,heq,hpath⟩ := freyaHRReplay_at_start q hm hn hS hK f τ O seed ω hservice b hb a hs
        rw [heq,freyaHRCore_path]
        funext j
        exact hpath j.val j.isLt
      have freyaPathCoin (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (k : ℕ)
          (E : Set (Fin (k+1) → Space q.d × Space q.d)) (hE : MeasurableSet E)
          (U : Set Bool) (hU : MeasurableSet U) :
          (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
            {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧ refreshAt z.1 k∈U}=
          (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
            {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E}*
            (bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ)) U := by
        clear * - q f τ O hservice k E hE U hU freyaFreshTapeEventProdProd freyaPastObservedTotal freyaObservedPairMeas

        classical
        let : NeZero (max 1 q.K) := ⟨by omega⟩
        let Ω := (a : ℕ) → O.Seed a
        let Rows := ℕ → ℕ → ChoiceRow
        let β := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ)
        let B := Measure.infinitePi (fun _ : ℕ => β)
        let R : Measure Rows := Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => (rowLaw : Measure ChoiceRow)))
        let I := (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
        let ξ := (O.law : Measure Ω)
        let Z := (((ℕ → Bool) × (Rows × Fin (max 1 q.K))) × Ω)
        let Q : Measure Z := (B.prod (R.prod I)).prod ξ
        let P := (executionLaw q O : Measure (Seed q.K × Ω))
        let decode : Z → Seed q.K × Ω := fun z => ((z.1.2.1,(z.1.1,z.1.2.2)),z.2)
        have hd : Measurable decode :=
          (measurable_fst.snd.fst.prodMk (measurable_fst.fst.prodMk measurable_fst.snd.snd)).prodMk measurable_snd
        have hm : MeasurePreserving (fun z : Seed q.K × Ω => ((z.1.2.1,(z.1.1,z.1.2.2)),z.2)) P Q := by
          have ha := (measurePreserving_prodAssoc R B I).symm MeasurableEquiv.prodAssoc
          have hb := (Measure.measurePreserving_swap (μ:=R) (ν:=B)).prod (MeasurePreserving.id I)
          exact ((measurePreserving_prodAssoc B R I).comp (hb.comp ha)).prod (MeasurePreserving.id ξ)
        let C : Set Z := {z | (fun j : Fin (k+1) => observedPair q O (decode z).1 (decode z).2 j.val)∈E}
        have hC : MeasurableSet C := hE.preimage (Measurable.of_eval (fun j =>
          (freyaObservedPairMeas q f τ O hservice j.val).comp hd))
        have hinv : ∀ t r ω bit,((Function.update t k bit,r),ω)∈C ↔ ((t,r),ω)∈C := by
          intro t r ω bit
          change (fun j : Fin (k+1) => observedPair q O (r.1,(Function.update t k bit,r.2)) ω j.val)∈E ↔
            (fun j : Fin (k+1) => observedPair q O (r.1,(t,r.2)) ω j.val)∈E
          have he : (fun j : Fin (k+1) => observedPair q O (r.1,(Function.update t k bit,r.2)) ω j.val)=
              (fun j : Fin (k+1) => observedPair q O (r.1,(t,r.2)) ω j.val) := by
            funext j
            apply freyaPastObservedTotal q k O hservice.1.1 (r.1,(t,r.2)) (r.1,(Function.update t k bit,r.2)) ω rfl
            · intro a ha
              exact Function.update_of_ne (show a≠k by omega) bit t
            · omega
          rw [he]
        have h := freyaFreshTapeEventProdProd β (R.prod I) ξ k C hC hinv U hU
        have hCU : MeasurableSet (C∩{z : Z | z.1.1 k∈U}) :=
          hC.inter (((measurable_pi_apply k).comp measurable_fst.fst) hU)
        change Q (C∩{z : Z | z.1.1 k∈U})=Q C*β U at h
        rw [← hm.map_eq,Measure.map_apply hm.measurable hCU,Measure.map_apply hm.measurable hC] at h
        exact h
      have freyaTransitionIntegral (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (k : ℕ)
          (E : Set (Fin (k+1) → Space q.d × Space q.d)) (hE : MeasurableSet E)
          (U : Set (Space q.d × Space q.d)) (hU : MeasurableSet U) :
          let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
          (∫⁻ z,transitionDensity q f O k E U z ∂P)=
            ENNReal.ofReal q.ρ*P {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧
              freyaFullNext q f (observedPair q O z.1 z.2 k)∈U}+
            (ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹)*
              ∑ v : Fin q.S → Fin q.m,P {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧
                freyaDiffNext q f v (observedPair q O z.1 z.2 k)∈U} := by
        clear * - q f τ O hservice k E hE U hU freyaFullNext freyaDiffNext freyaFullNextMeas freyaDiffNextMeas freyaObservedPairMeas

        classical
        let Ω := Seed q.K × ((a : ℕ) → O.Seed a)
        let P := (executionLaw q O : Measure Ω)
        let F : Set Ω := {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧
          freyaFullNext q f (observedPair q O z.1 z.2 k)∈U}
        let D (v : Fin q.S → Fin q.m) : Set Ω :=
          {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧
            freyaDiffNext q f v (observedPair q O z.1 z.2 k)∈U}
        have hp : Measurable (fun z : Ω => fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val) :=
          Measurable.of_eval (fun j => freyaObservedPairMeas q f τ O hservice j.val)
        have hF : MeasurableSet F := (hE.preimage hp).inter
          (hU.preimage ((freyaFullNextMeas q f).comp (freyaObservedPairMeas q f τ O hservice k)))
        have hD (v : Fin q.S → Fin q.m) : MeasurableSet (D v) := (hE.preimage hp).inter
          (hU.preimage ((freyaDiffNextMeas q f v).comp (freyaObservedPairMeas q f τ O hservice k)))
        have he : transitionDensity q f O k E U=(fun z =>
            ENNReal.ofReal q.ρ*F.indicator (fun _ => (1 : ℝ≥0∞)) z+
            (ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹)*
              ∑ v : Fin q.S → Fin q.m,(D v).indicator (fun _ => (1 : ℝ≥0∞)) z) := by
          funext z
          by_cases h : (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E
          · dsimp only [transitionDensity]
            rw [ite_eq_left h]
            dsimp only [transitionKernel,freyaFullNext,freyaDiffNext,F,D,Set.indicator]
            simp (config := { iota := false }) only [Set.mem_ofPred_eq,h,true_and]
          · dsimp only [transitionDensity]
            rw [ite_eq_right h]
            dsimp only [F,D,Set.indicator]
            simp (config := { iota := false }) only [Set.mem_ofPred_eq,h,false_and,ite_false,Finset.sum_const_zero,mul_zero,add_zero]
        change (∫⁻ z,transitionDensity q f O k E U z ∂P)=_
        have hiF : Measurable (F.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hF
        have hiD (v : Fin q.S → Fin q.m) : Measurable ((D v).indicator (fun _ => (1 : ℝ≥0∞))) :=
          measurable_const.indicator (hD v)
        have hmul : Measurable (fun z => ENNReal.ofReal q.ρ*F.indicator (fun _ => (1 : ℝ≥0∞)) z) :=
          measurable_const.mul hiF
        have hmeasure (A : Set Ω) (hA : MeasurableSet A) :
            (∫⁻ z,A.indicator (fun _ => (1 : ℝ≥0∞)) z ∂P)=P A :=
          lintegral_indicator_one hA
        rw [he]
        dsimp only
        rw [lintegral_add_left hmul,
          lintegral_const_mul _ hiF,
          lintegral_const_mul _ (Finset.measurable_sum Finset.univ (fun v _ => hiD v)),
          hmeasure F hF,
          lintegral_finsetSum Finset.univ (fun v _ => hiD v)]
        exact congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal q.ρ*P F+
          (ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹)*a)
            (Finset.sum_congr rfl (fun v _ => hmeasure (D v) (hD v)))
      have freyaHRHistory_measurable_version (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) (hb : b≤rounds q) :
          ∃ Y : (Seed q.K × ((k : ℕ) → O.Seed k)) → Fin b → freyaHRPair q.d,
            Measurable[historyBefore q O b] Y ∧
            Y =ᵐ[(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))]
              (fun z => fun j : Fin b => observedPair q O z.1 z.2 j.val) := by
        clear * - q hm hn hS hK f τ O hservice b hb freyaHRPair freyaHRReplay freyaHRHistoryEvents freyaHRMeasurable_historySavedPath freyaHRHistory_savedPath_eq

        refine ⟨fun z => fun j : Fin b => (freyaHRReplay q.d q.m q.S (freyaHRHistoryEvents q O b z)
          (eventLimit q+1)).2.2.2.2.2 j.val,freyaHRMeasurable_historySavedPath q O b,?_⟩
        have hs : ∀ᵐ z ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))),
            servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        filter_upwards [hs] with z hz
        exact freyaHRHistory_savedPath_eq q hm hn hS hK f τ O z.1 z.2 hz b hb
      have freyaLabelsPastEvent (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (hρ : 0<q.ρ) (hρone : q.ρ≤1)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O)
          (hind : LongTails.Setups.FreyaIndependence.batchScheduleIndependent q f τ O)
          (k : ℕ) (hk : k<rounds q)
          (Y : (Seed q.K × ((a : ℕ) → O.Seed a)) → Fin (k+1) → Space q.d × Space q.d)
          (hY : Measurable[historyBefore q O (k+1)] Y)
          (heq : Y=ᵐ[(executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))]
            (fun z => fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val))
          (E : Set (Fin (k+1) → Space q.d × Space q.d)) (hE : MeasurableSet E)
          (v : Fin q.S → Fin q.m) :
          (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
            {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧ refreshAt z.1 k=false ∧
              completedLabels q O z.1 z.2 (k+1)=fun j => some (v j)}=
            (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
              {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E}*
                ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹ := by
        clear * - q hm hn hS hK hρ hρone f τ O hservice hind k hk Y hY heq E hE v freyaBernoulliMass freyaPageDifferenceHistoryMeas freyaDifferenceTagIff freyaBatchNextTag freyaPathCoin

        let Ω := Seed q.K × ((a : ℕ) → O.Seed a)
        let P := (executionLaw q O : Measure Ω)
        let D : Set Ω := {z | Y z∈E ∧ LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z (k+1)}
        have hD : MeasurableSet[historyBefore q O (k+1)] D :=
          (hE.preimage hY).inter (freyaPageDifferenceHistoryMeas q O (k+1))
        have hl := (completed_labels_iid q hm hn hS hK hρ hρone f τ O hservice hind (k+1)).2.2 D hD
          (fun z hz => hz.2) v
        have hpaths : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        have hbranch : ∀ᵐ z ∂P,LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z (k+1) ↔
            refreshAt z.1 k=false := by
          filter_upwards [hpaths] with z hz
          rw [freyaDifferenceTagIff,freyaBatchNextTag q hm hn hS hK f τ O z hz k hk]
          cases refreshAt z.1 k <;> simp (config := { iota := false })
        have hmass : P D=P {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧ refreshAt z.1 k=false} := by
          apply measure_congr
          filter_upwards [heq,hbranch] with z hy hb
          apply propext
          change (Y z∈E ∧ _) ↔ _
          rw [hy,hb]
        have hleft : P {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧ refreshAt z.1 k=false ∧
              completedLabels q O z.1 z.2 (k+1)=fun j => some (v j)}=
            P (D∩{z | completedLabels q O z.1 z.2 (k+1)=fun j => some (v j)}) := by
          apply measure_congr
          filter_upwards [heq,hbranch] with z hy hb
          apply propext
          change (_∧_∧_) ↔ ((Y z∈E ∧ _) ∧ _)
          rw [hy,hb]
          exact and_assoc.symm
        change P _=P _*_*_
        rw [hleft,hl,hmass]
        have hc := freyaPathCoin q f τ O hservice k E hE {false} (measurableSet_singleton false)
        rw [(freyaBernoulliMass q.ρ hρ hρone).2] at hc
        exact congrArg (fun a : ℝ≥0∞ => a*((q.m : ℝ≥0∞)^q.S)⁻¹) hc
      have freyaTransitionFromHistory (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (hρ : 0<q.ρ) (hρone : q.ρ≤1)
          (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i,Differentiable ℝ (f i)) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O)
          (hind : LongTails.Setups.FreyaIndependence.batchScheduleIndependent q f τ O)
          (k : ℕ) (hk : k<rounds q)
          (Y : (Seed q.K × ((a : ℕ) → O.Seed a)) → Fin (k+1) → Space q.d × Space q.d)
          (hY : Measurable[historyBefore q O (k+1)] Y)
          (heq : Y=ᵐ[(executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))]
            (fun z => fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val))
          (E : Set (Fin (k+1) → Space q.d × Space q.d)) (hE : MeasurableSet E)
          (U : Set (Space q.d × Space q.d)) (hU : MeasurableSet U) :
          let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
          P {z | (fun j : Fin (k+1) => observedPair q O z.1 z.2 j.val)∈E ∧
            observedPair q O z.1 z.2 (k+1)∈U}=(∫⁻ z,transitionDensity q f O k E U z ∂P) := by
        clear * - q hm hn hS hK hρ hρone f hf τ O hservice hind k hk Y hY heq E hE U hU freyaBernoulliMass freyaFullNext freyaDiffNext freyaOptionSingleton freyaFullNextMeas freyaDiffNextMeas freyaDifferenceTagIff freyaBatchNextTag freyaObservedTransition freyaObservedPairMeas freyaPathCoin freyaTransitionIntegral freyaLabelsPastEvent

        classical
        let Ω := Seed q.K × ((a : ℕ) → O.Seed a)
        let P := (executionLaw q O : Measure Ω)
        let path : Ω → Fin (k+1) → Space q.d × Space q.d :=
          fun z j => observedPair q O z.1 z.2 j.val
        let last : Fin (k+1) := ⟨k,by omega⟩
        let F : Set (Fin (k+1) → Space q.d × Space q.d) :=
          {w | w∈E ∧ freyaFullNext q f (w last)∈U}
        let D (v : Fin q.S → Fin q.m) : Set (Fin (k+1) → Space q.d × Space q.d) :=
          {w | w∈E ∧ freyaDiffNext q f v (w last)∈U}
        let CF : Set Ω := {z | path z∈F ∧ refreshAt z.1 k=true}
        let CD (v : Fin q.S → Fin q.m) : Set Ω :=
          {z | path z∈D v ∧ refreshAt z.1 k=false ∧ completedLabels q O z.1 z.2 (k+1)=fun j => some (v j)}
        have hF : MeasurableSet F := hE.inter (hU.preimage ((freyaFullNextMeas q f).comp (measurable_pi_apply last)))
        have hD (v : Fin q.S → Fin q.m) : MeasurableSet (D v) :=
          hE.inter (hU.preimage ((freyaDiffNextMeas q f v).comp (measurable_pi_apply last)))
        have hp : Measurable path := Measurable.of_eval (fun j => freyaObservedPairMeas q f τ O hservice j.val)
        have hbit : Measurable (fun z : Ω => refreshAt z.1 k) :=
          (measurable_pi_apply k).comp measurable_fst.snd.fst
        obtain ⟨hlabels,hall,hlaw⟩ := completed_labels_iid q hm hn hS hK hρ hρone f τ O hservice hind (k+1)
        have _ := hlaw
        let : MeasurableSingletonClass (Option (Fin q.m)) := freyaOptionSingleton
        have hCD (v : Fin q.S → Fin q.m) : MeasurableSet (CD v) :=
          (hD v |>.preimage hp).inter ((hbit (measurableSet_singleton false)).inter
            (hlabels (measurableSet_singleton (fun j => some (v j)))))
        have hdisj : Disjoint CF (⋃ v,CD v) := by
          apply Set.disjoint_left.mpr
          intro z hz hz'
          obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz'
          have h1 : refreshAt z.1 k=true := hz.2
          have h2 : refreshAt z.1 k=false := hv.2.1
          rw [h1] at h2
          cases h2
        have hpair : Pairwise (fun v w => Disjoint (CD v) (CD w)) := by
          intro v w hvw
          apply Set.disjoint_left.mpr
          intro z hz hw
          apply hvw
          have h := hz.2.2.symm.trans hw.2.2
          funext j
          exact Option.some.inj (congrFun h j)
        have hpaths : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        have hevent : {z | path z∈E ∧ observedPair q O z.1 z.2 (k+1)∈U}=ᵐ[P] CF∪⋃ v,CD v := by
          filter_upwards [hpaths,hall] with z hs hl
          apply propext
          change (_∧_) ↔ ((path z∈F ∧ refreshAt z.1 k=true) ∨ z∈⋃ v,CD v)
          rw [Set.mem_iUnion]
          have ht := freyaObservedTransition q hm hn hS hK f hf τ O z.1 z.2 hs k hk
          cases hb : refreshAt z.1 k with
          | true =>
            have hnxt : observedPair q O z.1 z.2 (k+1)=freyaFullNext q f (path z last) := by
              simpa (config := { iota := false }) only [hb,ite_true,freyaFullNext,path,last] using ht
            constructor
            · intro hz
              left
              refine ⟨⟨hz.1,?_⟩,rfl⟩
              rw [← hnxt]
              exact hz.2
            · rintro (h|⟨v,hv⟩)
              · exact ⟨h.1.1,by rw [hnxt]; exact h.1.2⟩
              · have hfalse : refreshAt z.1 k=false := hv.2.1
                rw [hb] at hfalse
                cases hfalse
          | false =>
            have hd : LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z (k+1) := by
              rw [freyaDifferenceTagIff,freyaBatchNextTag q hm hn hS hK f τ O z hs k hk]
              rw [hb]
              rfl
            have hex (j : Fin q.S) : ∃ i,completedLabels q O z.1 z.2 (k+1) j=some i :=
              Option.isSome_iff_exists.mp (hl hd j)
            choose v hv using hex
            have hv : completedLabels q O z.1 z.2 (k+1)=fun j => some (v j) := funext hv
            have hnxt (w : Fin q.S → Fin q.m)
                (hw : completedLabels q O z.1 z.2 (k+1)=fun j => some (w j)) :
                observedPair q O z.1 z.2 (k+1)=freyaDiffNext q f w (path z last) := by
              simpa (config := { iota := false }) only [hb,Bool.false_eq_true,ite_false,hw,Option.elim_some,freyaDiffNext,path,last] using ht
            constructor
            · intro hz
              right
              refine ⟨v,⟨hz.1,?_⟩,hb,hv⟩
              rw [← hnxt v hv]
              exact hz.2
            · rintro (h|⟨w,hw⟩)
              · have htrue := h.2
                cases htrue
              · exact ⟨hw.1.1,by rw [hnxt w hw.2.2]; exact hw.1.2⟩
        have hmF : P CF=P {z | path z∈F}*ENNReal.ofReal q.ρ := by
          have h := freyaPathCoin q f τ O hservice k F hF {true} (measurableSet_singleton true)
          rw [(freyaBernoulliMass q.ρ hρ hρone).1] at h
          exact h
        have hmD (v : Fin q.S → Fin q.m) :
            P (CD v)=P {z | path z∈D v}*ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹ :=
          freyaLabelsPastEvent q hm hn hS hK hρ hρone f τ O hservice hind k hk Y hY heq (D v) (hD v) v
        change P {z | path z∈E ∧ observedPair q O z.1 z.2 (k+1)∈U}=_
        rw [measure_congr hevent,measure_union hdisj (MeasurableSet.iUnion hCD),measure_iUnion hpair hCD,
          tsum_fintype,hmF]
        simp_rw [hmD]
        rw [← Finset.sum_mul,← Finset.sum_mul]
        rw [freyaTransitionIntegral q f τ O hservice k E hE U hU]
        change P {z | path z∈F}*ENNReal.ofReal q.ρ+
          (∑ v,P {z | path z∈D v})*ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹=
            ENNReal.ofReal q.ρ*P {z | path z∈F}+
            (ENNReal.ofReal (1-q.ρ)*((q.m : ℝ≥0∞)^q.S)⁻¹)*(∑ v,P {z | path z∈D v})
        ring
      have freyaConditionalTransition (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
          (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
          (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
          (k : ℕ) (hk : k < rounds q)
          (E : Set (Fin (k + 1) → Space q.d × Space q.d)) (hE : MeasurableSet E)
          (U : Set (Space q.d × Space q.d)) (hU : MeasurableSet U) :
          let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
          P {z | (fun j : Fin (k + 1) => observedPair q O z.1 z.2 j.val) ∈ E ∧
            observedPair q O z.1 z.2 (k + 1) ∈ U} =
              ∫⁻ z, transitionDensity q f O k E U z ∂P  := by
        clear * - q hm hn hS hK hρ hρone f hf τ O hservice hind k hk E hE U hU freyaHRHistory_measurable_version freyaTransitionFromHistory

        obtain ⟨Y,hY,heq⟩ := freyaHRHistory_measurable_version q hm hn hS hK f τ O hservice (k+1) (by omega)
        exact freyaTransitionFromHistory q hm hn hS hK hρ hρone f hf τ O hservice hind k hk Y hY heq E hE U hU
      exact freyaConditionalTransition q hm hn hS hK hρ hρone f hf τ O hservice hind k hk E hE U hU
"### with
        | .error message => throwError message
        | .ok tactic => Lean.Elab.Tactic.evalTactic tactic
    task.get


theorem scheduled_page_law (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
    (N : ℕ) (hN : eventLimit q ≤ N) :
    let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
    let Q := (LongTails.Algorithms.FreyaSerial.canonicalLaw (serialInput q) :
      Measure (LongTails.Algorithms.FreyaSerial.CanonicalSeed (serialInput q)))
    HasLaw (fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
      ((fun j : Fin q.K => observedPair q O z.1 z.2 j.val), outputIndex z.1))
      (Q.map fun w => ((fun j : Fin q.K =>
        LongTails.Algorithms.FreyaSerial.idealTrace (serialInput q) f w j.val), w.2.2)) P ∧
      HasLaw (fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
        (execute O (factory q) (fun _ => N) z.1 z.2).1)
        (Q.map (LongTails.Algorithms.FreyaSerial.idealOutput (serialInput q) f)) P := by
  exact
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 4096 in
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
    open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
    open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    open LongTails.Proofs.FreyaConditionalCosts LongTails.Proofs.FreyaExecution in
    open LongTails.Setups.FreyaIndependence in
    open LongTails.Algorithms.FreyaSerial (CanonicalSeed idealTrace canonicalLaw componentLaw) in
    by
      classical
      let freyaListMeasSpace (α : Type) : MeasurableSpace (List α) := ⊤
      have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
        clear * - q s

        delta advance
        split <;> rfl
      have freyaPageAdvanceIteration (q : Raw) (s : State q) :
          (advance q s).iteration = s.iteration ∨ (advance q s).iteration = s.iteration+1 := by
        clear * - q s

        delta advance
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
          (h : (List.range N).find? p = some k) :
          k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
        clear * - N p k h

        obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
        simp (config := { iota := false }) only [List.length_range,List.getElem_range] at hi hik hprev
        subst i
        refine ⟨hi,hp,?_⟩
        intro r hr htrue
        have hh := hprev r hr
        rw [htrue] at hh
        contradiction
      have freyaDifferenceLiveStep {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
          (s : DifferenceState d m n) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i = some j ∧ reply (some r) = some (i,j.id,c,jobValue f j) ∧
              r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i')
          (ha : s.count < s.target)
          (hp : ∀ i, ∃ job, s.pending i = some job ∧ job.started ≤ s.clock ∧
            (s.clock : ℝ≥0∞) ≤ deadline τ job i ∧ job.kind = Sum.inr (s.x,s.y)) :
          ∃ i job c next,
            s.pending i = some job ∧
            differenceQuery s = some ⟨s.clock,s.pending⟩ ∧
            reply (differenceQuery s) = some (i,job.id,c,jobValue f job) ∧
            s.clock ≤ c ∧
            next.id = s.nextID ∧ next.kind = Sum.inr (s.x,s.y) ∧ next.started = c ∧
            labelAt (s.rows s.nextID) m = some next.component ∧
            differenceUpdate s (reply (differenceQuery s)) =
              {s with
                count := s.count+1
                sum := s.sum+jobValue f job
                pending := Function.update s.pending i (some next)
                clock := c
                nextID := s.nextID+1} ∧
            ∀ k, ∃ old, (Function.update s.pending i (some next)) k = some old ∧
              old.started ≤ c ∧ (c : ℝ≥0∞) ≤ deadline τ old k ∧ old.kind = Sum.inr (s.x,s.y) := by
        clear * - d m n hm hn s f τ reply hservice ha hp

        classical
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hlegal : legalRequest τ r := by
          refine ⟨?_,?_⟩
          · obtain ⟨job,hj,_⟩ := hp ⟨0,hn⟩
            exact ⟨⟨0,hn⟩,job,hj⟩
          · intro i job hj
            obtain ⟨old,hold,hs,ht,_⟩ := hp i
            have heq : job=old := Option.some.inj (hj.symm.trans hold)
            subst old
            exact ⟨hs,ht⟩
        have hquery : differenceQuery s = some r := by
          delta differenceQuery
          rw [ite_eq_right (by omega)]
          delta pendingRequest
          have hex : ∃ i, s.pending i ≠ none := by
            obtain ⟨i,job,hj⟩ := hlegal.1
            change s.pending i=some job at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,c,hjob,hreply,hclock,hdeadline⟩ := hservice r hlegal
        change s.pending i=some job at hjob
        change s.clock≤c at hclock
        obtain ⟨b,hb⟩ : ∃ b : Fin m, labelAt (s.rows s.nextID) m = some b := by
          delta labelAt
          simp (config := { iota := false }) only [hm,dite_true]
          exact ⟨_,rfl⟩
        let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
        refine ⟨i,job,c,next,hjob,hquery,?_,hclock,rfl,rfl,rfl,hb,?_,?_⟩
        · rw [hquery]; exact hreply
        · rw [hquery,hreply]
          delta differenceUpdate
          rw [ite_eq_right (by omega)]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
          delta dispatch
          rw [hb]
          rfl
        · intro k
          by_cases hk : k=i
          · subst k
            refine ⟨next,Function.update_self _ _ _,le_rfl,?_,rfl⟩
            change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞)+(2 : ℕ)*τ i
            exact le_add_of_nonneg_right zero_le
          · obtain ⟨old,hold,hstarted,_,hkind⟩ := hp k
            refine ⟨old,?_,hstarted.trans hclock,hdeadline k old hold,hkind⟩
            rw [Function.update_of_ne hk]
            exact hold
      have freyaPageDifferenceQuery (q : Raw) (s : State q)
          (c : DifferenceState q.d q.m q.n) (h : s.phase = Phase.difference c) :
          query q s = (0,differenceQuery c) := by
        clear * - q s c h

        delta query
        rw [h]
        rfl
      have freyaFullSelect {m : ℕ} (labels : List (Fin m)) (rem : List ℕ)
          (hne : rem≠[]) (hbound : ∀ b ∈ rem,b<labels.length) (row : ChoiceRow) :
          ∃ b, b ∈ rem ∧ ∃ hb : b<labels.length, selectedLabel labels rem row=some labels[b] := by
        clear * - m labels rem hne hbound row

        have hlen : rem.length≠0 := by intro hz; exact hne (List.length_eq_zero_iff.mp hz)
        let j : Fin rem.length := ⟨(row (rem.length-1)).val,by
          have hj := (row (rem.length-1)).isLt
          omega⟩
        have hb := hbound _ (List.get_mem rem j)
        refine ⟨rem.get j,List.get_mem rem j,hb,?_⟩
        delta selectedLabel chooseRemaining
        rw [dite_eq_right hlen]
        dsimp only
        exact List.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩
      have freyaDifferenceInitialSafe {d m n : ℕ} (hm : 0<m) (S : ℕ) (hS : 0<S)
          (x y : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ)
          (τ : Fin n → ℝ≥0∞) :
          let c : DifferenceState d m n := differenceInitial n S x y clock rows firstID
          ∀ i, ∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
        clear * - d m n hm S hS x y clock rows firstID τ

        dsimp only
        intro i
        obtain ⟨b,hb⟩ : ∃ b : Fin m,labelAt (rows (firstID+i.val)) m=some b := by
          delta labelAt
          simp (config := { iota := false }) only [hm,dite_true]
          exact ⟨_,rfl⟩
        refine ⟨⟨b,Sum.inr (x,y),clock,firstID+i.val⟩,?_,le_rfl,?_,rfl⟩
        · change (if S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
            (labelAt (rows (firstID+i.val)) m))=_
          rw [ite_eq_right (by omega),hb]
          rfl
        · exact le_add_of_nonneg_right zero_le
      have freyaPageFullQuery (q : Raw) (s : State q) (first : Bool)
          (c : FullState q.d q.m q.n) (h : s.phase=Phase.full first c) :
          query q s=(0,fullQuery c) := by
        clear * - q s first c h

        delta query
        rw [h]
        rfl
      have freyaPageFullInvocation (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch=some (true,x,y,clock,firstID)) :
          ∃ call first c,batchStartCall q O seed ω batch=some call ∧
            (trace q O seed ω call).phase=Phase.full first c ∧
            c.point=x ∧ c.point=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
        clear * - q O seed ω batch firstID x y clock h

        delta invocation at h
        cases hs : batchStartCall q O seed ω batch with
        | none => rw [hs] at h; cases h
        | some call =>
          rw [hs] at h
          dsimp only [Option.bind] at h
          cases hp : (trace q O seed ω call).phase with
          | halted => rw [hp] at h; cases h
          | difference c => rw [hp] at h; cases h
          | full first c =>
            rw [hp] at h
            have heq := Option.some.inj h
            have hfields : c.point=x ∧ c.point=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
              simpa (config := { iota := false }) only [Prod.mk.injEq,true_and] using heq
            exact ⟨call,first,c,rfl,hp,hfields⟩
      have freyaPageFullEntryAdvance (q : Raw) (s : State q) (reply : Reply q.d q.n)
          (first : Bool) (c : FullState q.d q.m q.n) (hphase : (update q s reply).phase=Phase.full first c)
          (hfresh : ¬(s.iteration=(update q s reply).iteration ∧ active s=true)) :
          ∃ t : State q,t.seed=s.seed ∧ advance q t=update q s reply := by
        clear * - q s reply first c hphase hfresh

        delta update at hphase hfresh ⊢
        cases hs : s.phase with
        | halted =>
          rw [hs] at hphase
          change s.phase=Phase.full first c at hphase
          rw [hs] at hphase
          cases hphase
        | full oldfirst old =>
          rw [hs] at hphase hfresh
          dsimp only at hphase hfresh ⊢
          by_cases he : (fullUpdate old reply).remaining.isEmpty=true
          · rw [ite_eq_left he]
            exact ⟨{s with
              g := fullResult (fullUpdate old reply)
              clock := (fullUpdate old reply).clock
              nextID := (fullUpdate old reply).nextID
              phase := Phase.full oldfirst (fullUpdate old reply)},rfl,rfl⟩
          · apply False.elim
            rw [ite_eq_right he] at hfresh
            apply hfresh
            refine ⟨rfl,?_⟩
            delta active
            rw [hs]
        | difference old =>
          rw [hs] at hphase hfresh
          dsimp only at hphase hfresh ⊢
          by_cases he : (differenceUpdate old reply).target≤(differenceUpdate old reply).count
          · rw [ite_eq_left he]
            exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate old reply)
              clock := (differenceUpdate old reply).clock
              nextID := (differenceUpdate old reply).nextID
              phase := Phase.difference (differenceUpdate old reply)},rfl,rfl⟩
          · rw [ite_eq_right he] at hphase
            cases hphase
      have freyaPageAdvanceFull (q : Raw) (s : State q) (first : Bool)
          (c : FullState q.d q.m q.n) (h : (advance q s).phase=Phase.full first c) :
          (advance q s).iteration=s.iteration+1 ∧ first=false ∧
            c=fullInitial q.n (List.ofFn id) (s.x-q.η • s.g) s.clock
              (s.seed.1 (s.iteration+1)) s.nextID := by
        clear * - q s first c h

        delta advance at h ⊢
        split at h
        · contradiction
        · rename_i hn
          rw [ite_eq_right hn]
          dsimp only at h ⊢
          split at h
          · have he := Phase.full.inj h
            exact ⟨rfl,he.1.symm,he.2.symm⟩
          · contradiction
      have freyaAdvanceLeaves (q : Raw) (s : State q) :
          (advance q s).iteration≠s.iteration ∨ active (advance q s)=false := by
        clear * - q s

        delta advance
        split
        · exact Or.inr rfl
        · exact Or.inl (Nat.succ_ne_self s.iteration)
      have freyaExitAdvance (q : Raw) (s : State q) (r : Reply q.d q.n)
          (ha : active s=true)
          (he : (update q s r).iteration≠s.iteration ∨ active (update q s r)=false) :
          ∃ t : State q,t.iteration=s.iteration ∧ t.seed=s.seed ∧ update q s r=advance q t := by
        clear * - q s r ha he

        cases hp : s.phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := fullResult (fullUpdate c r)
              clock := (fullUpdate c r).clock
              nextID := (fullUpdate c r).nextID
              phase := .full first (fullUpdate c r)},rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
        | difference c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate c r)
              clock := (differenceUpdate c r).clock
              nextID := (differenceUpdate c r).nextID
              phase := .difference (differenceUpdate c r)},rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
      have freyaBatchZeroStart (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hK : 0<q.K)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          batchStartCall q O seed ω 0=some 0 := by
        clear * - q hm hn hK O seed ω

        classical
        dsimp only [batchStartCall]
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨?_,0,?_,?_,?_⟩
        · dsimp only [trace,run,initial,active]
          rw [ite_eq_right (show ¬(q.m=0 ∨ q.n=0 ∨ q.K=0) by omega)]
          rfl
        · simp (config := { iota := false }) only [List.length_range]; omega
        · simp (config := { iota := false }) only [List.getElem_range]
        · intro r hr; omega
      let freyaInside {q : Raw} (s : State q) : Space q.d × Space q.d × Option Bool :=
        (s.x,s.g,Phase.casesOn s.phase (fun first _ => some first) (fun _ => none) none)
      let freyaFullGradientInvariant {d m n : ℕ} (f : Fin m → Space d → ℝ)
          (c : FullState d m n) : Prop :=
        c.sum+(c.remaining.map (contribution f c.original c.point)).sum=
          (c.original.map fun i => gradient (f i) c.point).sum ∧
        ∀ i job,c.pending i=some job → job.kind=Sum.inl c.point
      have freyaObservedFullExit (q : Raw) (s : State q) (r : Reply q.d q.n)
          (first : Bool) (c : FullState q.d q.m q.n) (hp : s.phase=Phase.full first c)
          (he : (update q s r).iteration≠s.iteration ∨ active (update q s r)=false) :
          (fullUpdate c r).remaining=[] := by
        clear * - q s r first c hp he

        by_contra hne
        have hi : (fullUpdate c r).remaining.isEmpty=false := by
          cases h : (fullUpdate c r).remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        dsimp only [update] at he
        rw [hp] at he
        dsimp only at he
        rw [hi,ite_eq_right Bool.false_ne_true] at he
        rcases he with he|he
        · exact he rfl
        · cases he
      let freyaControl {q : Raw} (s : State q) :=
        (s.iteration,s.x,s.g,s.clock,s.nextID,s.phase)
      have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
          (b : β) (f : α → β) (hf : Measurable f) :
          Measurable (fun o : Option α => o.elim b f) := by
        clear * - α β b f hf

        have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
          apply Measurable.of_comap_le
          delta instMeasurableSpaceOption
          apply le_of_eq
          congr 1
          funext o
          cases o <;> rfl
        have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
        convert hs.comp he using 1
        funext o
        cases o <;> rfl
      have freyaOptionSomeMeas {α : Type} [MeasurableSpace α] :
          Measurable (some : α → Option α) := by
        clear * - α

        delta instMeasurableSpaceOption
        rw [measurable_comap_iff]
        exact measurable_inr
      have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
          (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
          Measurable (fun z => f (g z) z) :=
        (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
          (measurable_id.prodMk hg)
      let freyaFullCode {d m n : ℕ} (s : FullState d m n) :=
        (s.original,s.remaining,s.point,s.sum,s.pending,s.clock,s.rows,s.nextID)
      let freyaFullMeasSpace (d m n : ℕ) : MeasurableSpace (FullState d m n) :=
        MeasurableSpace.comap freyaFullCode inferInstance
      let freyaDifferenceCode {d m n : ℕ} (s : DifferenceState d m n) :=
        (s.target,s.count,s.x,s.y,s.sum,s.pending,s.clock,s.rows,s.nextID)
      let freyaDifferenceMeasSpace (d m n : ℕ) : MeasurableSpace (DifferenceState d m n) :=
        MeasurableSpace.comap freyaDifferenceCode inferInstance
      have freyaJobCodeMeas {d m : ℕ} :
          Measurable (fun j : Job d m => (j.component,j.kind,j.started,j.id)) :=
        Measurable.of_comap_le le_rfl
      let freyaFullReplyJob {d m n : ℕ} (s : FullState d m n)
          (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : FullState d m n := by
        clear * - d m n s r job

        classical
        exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
          let found := s.remaining.find? fun a => decide (s.original[a]?=some job.component)
          let remaining := found.elim s.remaining (fun a => s.remaining.erase a)
          let sum := if found.isSome then s.sum+r.2.2.2 else s.sum
          let next := dispatch (Sum.inl s.point) r.2.2.1 s.nextID
            (selectedLabel s.original remaining (s.rows s.nextID))
          {s with
            remaining:=remaining
            sum:=sum
            pending:=Function.update s.pending r.1 next
            clock:=r.2.2.1
            nextID:=s.nextID+1}
        else s
      let freyaDifferenceReplyJob {d m n : ℕ} (s : DifferenceState d m n)
          (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : DifferenceState d m n := by
        clear * - d m n s r job

        classical
        exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
          let next := dispatch (Sum.inr (s.x,s.y)) r.2.2.1 s.nextID (labelAt (s.rows s.nextID) m)
          {s with
            count:=s.count+1
            sum:=s.sum+r.2.2.2
            pending:=Function.update s.pending r.1 next
            clock:=r.2.2.1
            nextID:=s.nextID+1}
        else s
      let freyaPhaseCode {d m n : ℕ} (p : Phase d m n) :
          Unit ⊕ ((Bool × FullState d m n) ⊕ DifferenceState d m n) :=
        p.casesOn (fun b c => Sum.inr (Sum.inl (b,c))) (fun c => Sum.inr (Sum.inr c)) (Sum.inl ())
      let freyaPhaseMeasSpace (d m n : ℕ) : MeasurableSpace (Phase d m n) :=
        MeasurableSpace.comap freyaPhaseCode inferInstance
      let freyaStateCode {q : Raw} (s : State q) :=
        (s.seed,s.iteration,s.x,s.g,s.selected,s.clock,s.nextID,s.phase)
      let freyaStateMeasSpace (q : Raw) : MeasurableSpace (State q) :=
        MeasurableSpace.comap freyaStateCode inferInstance
      have freyaFindMeas {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          (l : List α) (p : Ω → α → Bool) (hp : ∀ a,Measurable (fun z => p z a)) :
          Measurable (fun z => l.find? (p z)) := by
        clear * - Ω α l p hp

        classical
        induction l with
        | nil => exact measurable_const
        | cons a l ih =>
          have h : Measurable (fun z => if p z a=true then some a else l.find? (p z)) :=
            measurable_const.ite ((hp a) (measurableSet_singleton true)) ih
          convert h using 1
          funext z
          simp (config := { iota := false }) only [List.find?_cons]
          cases p z a <;> rfl
      let freyaObservedFinish (q : Raw) (s : State q) (r : Reply q.d q.n) : Space q.d × Space q.d :=
        match s.phase with
        | .full _ c => (s.x,fullResult (fullUpdate c r))
        | .difference c => (s.x,s.g+differenceResult (differenceUpdate c r))
        | .halted => (s.x,s.g)
      have freyaSelectedAdvance (q : Raw) (s : State q)
          (h : (outputIndex s.seed).val=s.iteration → s.selected=s.x) :
          (outputIndex (advance q s).seed).val=(advance q s).iteration →
            (advance q s).selected=(advance q s).x := by
        clear * - q s h

        dsimp only [advance]
        split
        · exact h
        · dsimp only
          intro hi
          rw [ite_eq_left hi]
      have freyaSelectedAdvanceStable (q : Raw) (s : State q)
          (h : (outputIndex s.seed).val≤s.iteration) : (advance q s).selected=s.selected := by
        clear * - q s h

        dsimp only [advance]
        split
        · rfl
        · dsimp only
          rw [ite_eq_right (show ¬(outputIndex s.seed).val=s.iteration+1 by omega)]
      have freyaSelectorProduct {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
          [MeasurableSpace γ] (μ : Measure α) [IsProbabilityMeasure μ]
          (ν : Measure β) [IsProbabilityMeasure ν] (b0 : β) (X : α × β → γ)
          (hX : Measurable X) (hinv : ∀ a b, X (a,b)=X (a,b0)) :
          (μ.prod ν).map (fun z => (X z,z.2))=((μ.prod ν).map X).prod ν := by
        clear * - α β γ μ ν b0 X hX hinv

        let f : α → γ := fun a => X (a,b0)
        have hf : Measurable f := hX.comp (measurable_id.prodMk measurable_const)
        have h : MeasurePreserving f μ (μ.map f) := ⟨hf,rfl⟩
        have hpair := (h.prod (MeasurePreserving.id ν)).map_eq
        have hproj := (h.comp (measurePreserving_fst (μ:=μ) (ν:=ν))).map_eq
        have he : X=f ∘ Prod.fst := funext (fun z => hinv z.1 z.2)
        rw [he]
        rw [hproj]
        exact hpair
      have freyaIdealSelectorInvariant (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
          (z : CanonicalSeed q) (i : Fin (max 1 q.K)) (a : ℕ) :
          idealTrace q f (z.1,z.2.1,i) a=idealTrace q f z a := by
        clear * - q f z i a

        have hrec (z : CanonicalSeed q) (a : ℕ) : idealTrace q f z (a+1)=
            idealTrace._sunfold q f z (a+1) := by
          conv_lhs => delta idealTrace
          refine (Nat.brecOn.eq (motive:=fun _ => Space q.d × Space q.d) (a+1)
            (idealTrace._f q f z)).trans ?_
          delta idealTrace._sunfold idealTrace._f idealTrace
          rfl
        induction a with
        | zero => rfl
        | succ a ih =>
          rw [hrec,hrec]
          delta idealTrace._sunfold
          dsimp only
          rw [ih]
      let freyaSPPathPrefix {Ω α : Type} (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) : Fin n → α :=
        fun j => X j.val ω
      let freyaSPAppend {α : Type} {n : ℕ} (z : (Fin n → α) × α) : Fin (n+1) → α :=
        Fin.lastCases z.2 z.1
      have freyaSPRectangle_map_eq {Ω Ξ α β : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
          [MeasurableSpace α] [MeasurableSpace β] (P : Measure Ω) (Q : Measure Ξ)
          [IsFiniteMeasure P] (X : Ω → α) (X' : Ω → β) (Y : Ξ → α) (Y' : Ξ → β)
          (hX : Measurable X) (hX' : Measurable X') (hY : Measurable Y) (hY' : Measurable Y')
          (h : ∀ E U,MeasurableSet E → MeasurableSet U →
            P {ω | X ω∈E ∧ X' ω∈U}=Q {ω | Y ω∈E ∧ Y' ω∈U}) :
          P.map (fun ω => (X ω,X' ω))=Q.map (fun ω => (Y ω,Y' ω)) := by
        clear * - Ω Ξ α β P Q X X' Y Y' hX hX' hY hY' h

        apply Measure.ext_prod
        intro E U hE hU
        rw [Measure.map_apply (hX.prodMk hX') (hE.prod hU),
          Measure.map_apply (hY.prodMk hY') (hE.prod hU)]
        exact h E U hE hU
      have freyaDevelopmentResample {ι α : Type} [Fintype ι] [DecidableEq ι]
          [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
          MeasurePreserving (fun z : (ι → α) × α => Function.update z.1 i z.2)
            ((Measure.pi fun _ : ι => μ).prod μ) (Measure.pi fun _ : ι => μ) := by
        clear * - ι α μ i

        classical
        have hm : Measurable (fun z : (ι → α) × α => Function.update z.1 i z.2) := by
          apply Measurable.of_eval
          intro j
          by_cases hj : j = i
          · subst j
            simpa (config := { iota := false }) only [Function.update_self] using
              (measurable_snd : Measurable (fun z : (ι → α) × α => z.2))
          · simpa (config := { iota := false }) only [Function.update_of_ne hj, Function.comp_def] using
              ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (ι → α) × α => z.1)))
        refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
        rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
        have he : (fun z : (ι → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi Set.univ s =
            (Set.pi (↑(Finset.univ.erase i) : Set ι) s) ×ˢ s i := by
          ext z
          simp (config := { iota := false }) only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
            Set.mem_prod, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · intro h
            constructor
            · intro j hj
              simpa (config := { iota := false }) only [Function.update_of_ne hj] using h j
            · simpa (config := { iota := false }) only [Function.update_self] using h i
          · rintro ⟨h, hi⟩ j
            by_cases hj : j = i
            · subst j
              simpa (config := { iota := false }) only [Function.update_self] using hi
            · simpa (config := { iota := false }) only [Function.update_of_ne hj] using h j hj
        rw [he, Measure.prod_prod, Measure.pi_pi_finset]
        exact Finset.prod_erase_mul (Finset.univ : Finset ι) (fun j => μ (s j)) (Finset.mem_univ i)
      have freyaDevelopmentPastInvariant (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
          (k : Fin q.K) (z : CanonicalSeed q) (b : Bool) (r : Fin q.S → Option (Fin q.m))
          (a : ℕ) (ha : a ≤ k.val) :
          idealTrace q f (Function.update z.1 k b, Function.update z.2.1 k r, z.2.2) a =
            idealTrace q f z a := by
        clear * - q f k z b r a ha

        have hrec (z : CanonicalSeed q) (a : ℕ) : idealTrace q f z (a+1) =
            idealTrace._sunfold q f z (a+1) := by
          conv_lhs => delta idealTrace
          refine (Nat.brecOn.eq (motive := fun _ => Space q.d × Space q.d) (a+1)
            (idealTrace._f q f z)).trans ?_
          delta idealTrace._sunfold idealTrace._f idealTrace
          rfl
        induction a with
        | zero => rfl
        | succ a ih =>
          rw [hrec, hrec]
          delta idealTrace._sunfold
          dsimp only
          rw [ih (by omega)]
          have hak : a < q.K := by omega
          rw [dite_eq_left hak, dite_eq_left hak]
          have hne : (⟨a, hak⟩ : Fin q.K) ≠ k := by
            intro he
            have := congrArg Fin.val he
            dsimp only at this
            omega
          simp (config := { iota := false }) only [Function.update_of_ne hne]
      have freyaSPBernoulli_lintegral (ρ : ℝ) (hρ : 0≤ρ) (hρone : ρ≤1) (F : Bool → ℝ≥0∞) :
          (∫⁻ b,F b ∂bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one ρ)) =
            ENNReal.ofReal ρ*F true+ENNReal.ofReal (1-ρ)*F false := by
        clear * - ρ hρ hρone F

        have hp : ((Set.projIcc 0 1 zero_le_one ρ : unitInterval) : ℝ)=ρ :=
          congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hρ,hρone⟩)
        rw [bernoulliMeasure_def,lintegral_add_measure]
        rw [lintegral_smul_measure,lintegral_smul_measure]
        simp (config := { iota := false }) only [lintegral_dirac]
        change (↑(unitInterval.toNNReal (Set.projIcc 0 1 zero_le_one ρ)) : ℝ≥0∞)*F true+
          (↑(unitInterval.toNNReal (unitInterval.symm (Set.projIcc 0 1 zero_le_one ρ))) : ℝ≥0∞)*F false=_
        rw [←ENNReal.ofReal_coe_nnreal,←ENNReal.ofReal_coe_nnreal]
        change ENNReal.ofReal ((Set.projIcc 0 1 zero_le_one ρ : unitInterval) : ℝ)*F true+
          ENNReal.ofReal (1-((Set.projIcc 0 1 zero_le_one ρ : unitInterval) : ℝ))*F false=_
        rw [hp]
      have freyaSPKernel_measurable (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (U : Set (Space q.d × Space q.d)) (hU : MeasurableSet U) :
          Measurable (fun p => transitionKernel q f p U) := by
        clear * - q f U hU

        have hg (g : Space q.d → ℝ) : Measurable (gradient g) :=
          (InnerProductSpace.toDual ℝ (Space q.d)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
        have hx : Measurable (fun p : Space q.d × Space q.d => p.1-q.η • p.2) :=
          measurable_fst.sub (measurable_snd.const_smul q.η)
        have hfull : Measurable (fun p : Space q.d × Space q.d =>
            (p.1-q.η • p.2,gradient (objective f) (p.1-q.η • p.2))) :=
          hx.prodMk ((hg (objective f)).comp hx)
        have hdiff (v : Fin q.S → Fin q.m) : Measurable (fun p : Space q.d × Space q.d =>
            (p.1-q.η • p.2,p.2+(q.S : ℝ)⁻¹ •
              ∑ j : Fin q.S,(gradient (f (v j)) (p.1-q.η • p.2)-gradient (f (v j)) p.1))) := by
          have hsum := Finset.measurable_sum Finset.univ (fun j _ =>
            ((hg (f (v j))).comp hx).sub ((hg (f (v j))).comp measurable_fst))
          exact hx.prodMk (measurable_snd.add (hsum.const_smul ((q.S : ℝ)⁻¹)))
        unfold transitionKernel
        exact (measurable_const.mul (Measurable.ite (hU.preimage hfull) measurable_const measurable_const)).add
          (measurable_const.mul (Finset.measurable_sum Finset.univ (fun v _ =>
            Measurable.ite (hU.preimage (hdiff v)) measurable_const measurable_const)))
      have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
          (update q s reply).seed = s.seed := by
        clear * - q s reply freyaPageAdvanceSeed

        delta update
        cases hs : s.phase with
        | halted => rfl
        | full first c =>
          dsimp only
          split
          · exact freyaPageAdvanceSeed q _
          · rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPageAdvanceSeed q _
          · rfl
      have freyaPageUpdateIteration (q : Raw) (s : State q) (reply : Reply q.d q.n) :
          (update q s reply).iteration = s.iteration ∨
            (update q s reply).iteration = s.iteration+1 := by
        clear * - q s reply freyaPageAdvanceIteration

        delta update
        cases hs : s.phase with
        | halted => exact Or.inl rfl
        | full first c =>
          dsimp only
          split
          · exact freyaPageAdvanceIteration q _
          · exact Or.inl rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPageAdvanceIteration q _
          · exact Or.inl rfl
      have freyaPageBatchStartFacts (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
          (h : batchStartCall q O seed ω batch = some call) :
          call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
            active (trace q O seed ω call) = true ∧
            ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
        clear * - q O seed ω batch call h freyaPageFirstMatch

        delta batchStartCall at h
        obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
        obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
        refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
        intro r hr hh
        apply hprev r hr
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
      have freyaFullSafeUpdate {d m n : ℕ} (s : FullState d m n)
          (hne : s.remaining≠[]) (hbound : ∀ b ∈ s.remaining,b<s.original.length)
          (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r, legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
          let t := fullUpdate s (reply (fullQuery s))
          t.original=s.original ∧ (∀ b ∈ t.remaining,b<t.original.length) ∧
            (t.remaining≠[] → legalRequest τ ⟨t.clock,t.pending⟩) := by
        clear * - d m n s hne hbound f τ reply hr hservice freyaFullSelect

        classical
        have hisEmpty : s.remaining.isEmpty=false := by
          cases h : s.remaining with
          | nil => exact False.elim (hne h)
          | cons b bs => rfl
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hquery : fullQuery s=some r := by
          delta fullQuery
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          delta pendingRequest
          have hex : ∃ i,s.pending i≠none := by
            obtain ⟨i,job,hj⟩ := hr.1
            change s.pending i=some job at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,time,hjob,hreply,hclock,hdeadline⟩ := hservice r hr
        change s.pending i=some job at hjob
        change s.clock≤time at hclock
        let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let next := dispatch (Sum.inl s.point) time s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n :=
          {s with
            remaining := rem
            sum := if found.isSome then s.sum+jobValue f job else s.sum
            pending := Function.update s.pending i next
            clock := time
            nextID := s.nextID+1}
        have ht : fullUpdate s (reply (fullQuery s))=t := by
          rw [hquery,hreply]
          delta fullUpdate
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
        have hb : ∀ b ∈ rem,b<s.original.length := by
          cases hf : found with
          | none => simpa (config := { iota := false }) only [rem,hf,Option.elim_none] using hbound
          | some a =>
            intro b h
            exact hbound b (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem,hf,Option.elim_some] using h))
        dsimp only
        rw [ht]
        refine ⟨rfl,hb,?_⟩
        intro htne
        obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect s.original rem htne hb (s.rows s.nextID)
        let new : Job d m := ⟨s.original[b],Sum.inl s.point,time,s.nextID⟩
        have hnew : next=some new := by
          dsimp only [next]
          rw [hlabel]
          rfl
        refine ⟨⟨i,new,?_⟩,?_⟩
        · change Function.update s.pending i next i=some new
          rw [Function.update_self,hnew]
        · intro k old hold
          change Function.update s.pending i next k=some old at hold
          by_cases hk : k=i
          · subst k
            rw [Function.update_self,hnew] at hold
            have heq : new=old := Option.some.inj hold
            subst old
            refine ⟨le_rfl,?_⟩
            exact le_add_of_nonneg_right zero_le
          · rw [Function.update_of_ne hk] at hold
            exact ⟨((hr.2 k old hold).1).trans hclock,hdeadline k old hold⟩
      have freyaFullInitialSafe {d m n : ℕ} (hn : 0<n) (labels : List (Fin m))
          (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow)
          (firstID : ℕ) (τ : Fin n → ℝ≥0∞) :
          let s := fullInitial n labels x clock rows firstID
          s.remaining≠[] ∧ (∀ b ∈ s.remaining,b<s.original.length) ∧
            legalRequest τ ⟨s.clock,s.pending⟩ := by
        clear * - d m n hn labels hne x clock rows firstID τ freyaFullSelect

        classical
        let s := fullInitial n labels x clock rows firstID
        have hrem : (List.range labels.length)≠[] := by
          intro h
          have := congrArg List.length h
          simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
          exact hne (List.length_eq_zero_iff.mp this)
        have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
        refine ⟨hrem,hbound,?_,?_⟩
        · let i : Fin n := ⟨0,hn⟩
          obtain ⟨b,_,hb,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
          refine ⟨i,⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_⟩
          change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
          rw [hlabel]
          rfl
        · intro i job hj
          change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=some job at hj
          delta dispatch at hj
          obtain ⟨b,_,heq⟩ := Option.map_eq_some_iff.mp hj
          cases heq
          exact ⟨le_rfl,le_add_of_nonneg_right zero_le⟩
      have freyaInsideAdvanceFalse (q : Raw) (s : State q)
          (hi : (advance q s).iteration=s.iteration) (ha : active (advance q s)=true) : False := by
        clear * - q s hi ha freyaAdvanceLeaves

        rcases freyaAdvanceLeaves q s with h|h
        · exact h hi
        · rw [h] at ha
          contradiction
      have freyaFullGradientInitial {d m : ℕ} (n : ℕ) (f : Fin m → Space d → ℝ)
          (labels : List (Fin m)) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
          freyaFullGradientInvariant f (fullInitial n labels x clock rows firstID) := by
        clear * - d m n f labels x clock rows firstID freyaFullGradientInvariant

        constructor
        · change 0+((List.range labels.length).map (contribution f labels x)).sum=
            (labels.map fun i => gradient (f i) x).sum
          rw [zero_add]
          congr 1
          apply List.ext_getElem (by simp (config := { iota := false }))
          intro b hb hb'
          have hbl : b<labels.length := by simpa (config := { iota := false }) only [List.length_map,List.length_range] using hb
          simp (config := { iota := false }) only [List.getElem_map,List.getElem_range]
          dsimp only [contribution]
          rw [getElem?_pos labels b hbl]
          rfl
        · intro i job hj
          change dispatch (Sum.inl x) clock (firstID+i.val) _=some job at hj
          dsimp only [dispatch] at hj
          obtain ⟨j,_,he⟩ := Option.map_eq_some_iff.mp hj
          cases he
          rfl
      have freyaFullGradientUpdate {d m n : ℕ} (s : FullState d m n)
          (hne : s.remaining≠[]) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
          (reply : Option (Request d m n) → Reply d n)
          (hr : legalRequest τ ⟨s.clock,s.pending⟩)
          (hservice : ∀ r,legalRequest τ r → ∃ i j c,
            r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
            r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i')
          (h : freyaFullGradientInvariant f s) :
          let t := fullUpdate s (reply (fullQuery s))
          t.original=s.original ∧ t.point=s.point ∧ freyaFullGradientInvariant f t := by
        clear * - d m n s hne f τ reply hr hservice h freyaFullGradientInvariant

        classical
        have hisEmpty : s.remaining.isEmpty=false := by
          cases he : s.remaining with
          | nil => exact False.elim (hne he)
          | cons b bs => rfl
        let r : Request d m n := ⟨s.clock,s.pending⟩
        have hquery : fullQuery s=some r := by
          dsimp only [fullQuery]
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only [pendingRequest]
          have hex : ∃ i,s.pending i≠none := by
            obtain ⟨i,j,hj⟩ := hr.1
            change s.pending i=some j at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
          rw [ite_eq_left hex]
        obtain ⟨i,job,time,hjob,hreply,hclock,_⟩ := hservice r hr
        change s.pending i=some job at hjob
        change s.clock≤time at hclock
        have hkind := h.2 i job hjob
        have hvalue : jobValue f job=gradient (f job.component) s.point := by
          dsimp only [jobValue]
          rw [hkind]
        let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
        let rem := found.elim s.remaining (fun b => s.remaining.erase b)
        let total := if found.isSome then s.sum+jobValue f job else s.sum
        have hsum : total+(rem.map (contribution f s.original s.point)).sum=
            (s.original.map fun j => gradient (f j) s.point).sum := by
          cases hf : found with
          | none => simpa (config := { iota := false }) only [rem,total,hf,Option.elim_none,Option.isSome_none,Bool.false_eq_true,ite_false] using h.1
          | some b =>
            have hb : b∈s.remaining := List.mem_of_find?_eq_some hf
            have hlabel : s.original[b]?=some job.component := by
              simpa (config := { iota := false }) only [decide_eq_true_eq] using List.find?_some hf
            have hc : contribution f s.original s.point b=jobValue f job := by
              dsimp only [contribution]
              rw [hlabel]
              exact hvalue.symm
            dsimp only [rem,total]
            rw [hf]
            simp (config := { iota := false }) only [Option.elim_some,Option.isSome_some,ite_true]
            rw [add_assoc,← hc,List.sum_map_erase (contribution f s.original s.point) hb]
            exact h.1
        let next := dispatch (Sum.inl s.point) time s.nextID
          (selectedLabel s.original rem (s.rows s.nextID))
        let t : FullState d m n := {s with
          remaining := rem
          sum := total
          pending := Function.update s.pending i next
          clock := time
          nextID := s.nextID+1}
        have ht : fullUpdate s (reply (fullQuery s))=t := by
          rw [hquery,hreply]
          delta fullUpdate
          rw [hisEmpty,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hjob]
          dsimp only
          rw [ite_eq_left (And.intro rfl hclock)]
        dsimp only
        rw [ht]
        refine ⟨rfl,rfl,hsum,?_⟩
        intro k old hold
        change Function.update s.pending i next k=some old at hold
        by_cases hk : k=i
        · subst k
          rw [Function.update_self] at hold
          change dispatch (Sum.inl s.point) time s.nextID _=some old at hold
          dsimp only [dispatch] at hold
          obtain ⟨j,_,he⟩ := Option.map_eq_some_iff.mp hold
          cases he
          rfl
        · rw [Function.update_of_ne hk] at hold
          exact h.2 k old hold
      let freyaPageGradientInvariant (q : Raw) (f : Fin q.m → Space q.d → ℝ) (s : State q) : Prop :=
        ∀ first c,s.phase=Phase.full first c →
          c.original=List.ofFn id ∧ c.point=s.x ∧ freyaFullGradientInvariant f c
      have freyaFullGradientComplete {d m n : ℕ} (f : Fin m → Space d → ℝ)
          (hf : ∀ i,Differentiable ℝ (f i)) (c : FullState d m n)
          (horig : c.original=List.ofFn id) (h : freyaFullGradientInvariant f c)
          (he : c.remaining=[]) : fullResult c=gradient (objective f) c.point := by
        clear * - d m n f hf c horig h he freyaFullGradientInvariant

        have hsum := h.1
        rw [he,List.map_nil,List.sum_nil,add_zero,horig] at hsum
        dsimp only [fullResult]
        rw [horig,List.length_ofFn,hsum]
        rw [List.map_ofFn,List.sum_ofFn]
        exact (LongTails.Proofs.FreyaSerialAnalysis.objective_gradient f hf c.point).symm
      have freyaControlRecord (q : Raw) (s t : State q) (h : freyaControl s=freyaControl t) :
          s={t with seed:=s.seed,selected:=s.selected} := by
        clear * - q s t h freyaControl

        cases s
        cases t
        dsimp only [freyaControl] at h
        simp (config := { iota := false }) only [Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
        rfl
      have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
          MeasurableSingletonClass (Option α) := by
        clear * - α freyaDevelopmentOptionElimMeas

        constructor
        intro x
        let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
        have he : {x}=encode ⁻¹' {encode x} := by
          ext y
          cases x <;> cases y <;> simp (config := { iota := false }) [encode]
        have hsingleton : MeasurableSet {encode x} := by
          rw [measurableSet_sum_iff]
          cases x <;> constructor <;> simp (config := { iota := false }) [encode]
          · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
            rw [he]
            exact MeasurableSet.empty
          · rename_i b
            have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
            rw [he]
            exact measurableSet_singleton _
        rw [he]
        exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
          hsingleton
      have freyaOptionParamMeas {Ω α β : Type} [MeasurableSpace Ω]
          [MeasurableSpace α] [MeasurableSpace β]
          (o : Ω → Option α) (ho : Measurable o) (b : Ω → β) (hb : Measurable b)
          (f : Ω × α → β) (hf : Measurable f) :
          Measurable (fun z => (o z).elim (b z) (fun a => f (z,a))) := by
        clear * - Ω α β o ho b hb f hf freyaDevelopmentOptionElimMeas

        have he := (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr).comp ho
        have hs := ((hb.comp measurable_fst).sumElim hf).comp
          ((MeasurableEquiv.prodSumDistrib Ω Unit α).measurable.comp (measurable_id.prodMk he))
        convert hs using 1
        funext z
        dsimp only [Function.comp_def,id_eq]
        cases o z <;> rfl'
      have freyaFullCodeMeas {d m n : ℕ} : Measurable (@freyaFullCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaDifferenceCodeMeas {d m n : ℕ} : Measurable (@freyaDifferenceCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaPhaseCodeMeas {d m n : ℕ} : Measurable (@freyaPhaseCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaStateCodeMeas (q : Raw) : Measurable (@freyaStateCode q) :=
        Measurable.of_comap_le le_rfl
      have freyaPhaseFullMeas {d m n : ℕ} :
          Measurable (fun z : Bool × FullState d m n => Phase.full z.1 z.2) := by
        clear * - d m n freyaPhaseCode

        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inl
      have freyaPhaseDifferenceMeas {d m n : ℕ} :
          Measurable (Phase.difference : DifferenceState d m n → Phase d m n) := by
        clear * - d m n freyaPhaseCode

        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inr
      have freyaStateConstructMeas {Ω : Type} [MeasurableSpace Ω] (q : Raw)
          (seed : Ω → Seed q.K) (it : Ω → ℕ) (x g selected : Ω → Space q.d)
          (clock : Ω → ℝ≥0) (id : Ω → ℕ) (phase : Ω → Phase q.d q.m q.n)
          (hseed : Measurable seed) (hit : Measurable it) (hx : Measurable x) (hg : Measurable g)
          (hselected : Measurable selected) (hc : Measurable clock) (hid : Measurable id) (hp : Measurable phase) :
          Measurable (fun z => (⟨seed z,it z,x z,g z,selected z,clock z,id z,phase z⟩ : State q)) := by
        clear * - Ω q seed it x g selected clock id phase hseed hit hx hg hselected hc hid hp freyaStateCode

        change Measurable[_,MeasurableSpace.comap freyaStateCode inferInstance] _
        rw [measurable_comap_iff]
        exact hseed.prodMk (hit.prodMk (hx.prodMk (hg.prodMk (hselected.prodMk (hc.prodMk (hid.prodMk hp))))))
      have freyaPendingRequestMeas {d m n : ℕ} :
          Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) => pendingRequest z.1 z.2) := by
        clear * - d m n freyaDevelopmentOptionElimMeas freyaOptionSomeMeas

        classical
        have hc : Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) =>
            (⟨z.1,z.2⟩ : Request d m n)) := by
          change Measurable[_,MeasurableSpace.comap (fun r : Request d m n => (r.clock,r.pending)) inferInstance] _
          rw [measurable_comap_iff]
          exact measurable_id
        have hsome := freyaOptionSomeMeas.comp hc
        have hn : MeasurableSet {o : Option (Job d m) | o ≠ none} := by
          have hi := freyaDevelopmentOptionElimMeas false (fun _ : Job d m => true) measurable_const
          convert hi (measurableSet_singleton true) using 1
          ext o
          cases o <;> simp (config := { iota := false })
        have he : MeasurableSet {z : ℝ≥0 × (Fin n → Option (Job d m)) | ∃ i, z.2 i ≠ none} := by
          convert MeasurableSet.iUnion (fun i : Fin n => hn.preimage ((measurable_pi_apply i).comp measurable_snd)) using 1
          ext z
          simp (config := { iota := false })
        exact hsome.ite he measurable_const
      have freyaSelectedUpdate (q : Raw) (s : State q) (r : Reply q.d q.n)
          (h : (outputIndex s.seed).val=s.iteration → s.selected=s.x) :
          (outputIndex (update q s r).seed).val=(update q s r).iteration →
            (update q s r).selected=(update q s r).x := by
        clear * - q s r h freyaSelectedAdvance

        cases hp : s.phase with
        | halted => dsimp only [update]; rw [hp]; exact h
        | full first c =>
          dsimp only [update]; rw [hp]; dsimp only
          split
          · exact freyaSelectedAdvance q _ h
          · exact h
        | difference c =>
          dsimp only [update]; rw [hp]; dsimp only
          split
          · exact freyaSelectedAdvance q _ h
          · exact h
      have freyaSelectedUpdateStable (q : Raw) (s : State q) (r : Reply q.d q.n)
          (h : (outputIndex s.seed).val≤s.iteration) : (update q s r).selected=s.selected := by
        clear * - q s r h freyaSelectedAdvanceStable

        cases hp : s.phase with
        | halted => dsimp only [update]; rw [hp]
        | full first c =>
          dsimp only [update]; rw [hp]; dsimp only
          split
          · exact freyaSelectedAdvanceStable q _ h
          · rfl
        | difference c =>
          dsimp only [update]; rw [hp]; dsimp only
          split
          · exact freyaSelectedAdvanceStable q _ h
          · rfl
      have freyaAdvanceControl (q : Raw) (s : State q) (new : Seed q.K) (p : Space q.d)
          (hrows : new.1=s.seed.1) (hbits : new.2.1=s.seed.2.1) :
          freyaControl (advance q {s with seed:=new,selected:=p})=freyaControl (advance q s) := by
        clear * - q s new p hrows hbits freyaControl

        dsimp only [advance]
        by_cases hstop : rounds q≤s.iteration
        · rw [ite_eq_left hstop,ite_eq_left hstop]
        · rw [ite_eq_right hstop,ite_eq_right hstop]
          have hr : refreshAt new s.iteration=refreshAt s.seed s.iteration :=
            congrArg (fun t : ℕ → Bool => t s.iteration) hbits
          dsimp only [freyaControl]
          rw [hr,hrows]
      have freyaIdealSelectorProduct (q : SerialRaw) [NeZero (max 1 q.K)]
          [MeasurableSingletonClass (Option (Fin q.m))]
          (f : Fin q.m → Space q.d → ℝ) :
          let Q := (canonicalLaw q : Measure (CanonicalSeed q))
          let X := fun z : CanonicalSeed q => fun j : Fin q.K => idealTrace q f z j.val
          Q.map (fun z => (X z,z.2.2))=
            (Q.map X).prod (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure := by
        clear * - q f freyaSelectorProduct freyaIdealSelectorInvariant

        classical
        let B := Measure.pi (fun _ : Fin q.K =>
          bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ))
        let R := Measure.pi (fun _ : Fin q.K =>
          Measure.pi (fun _ : Fin q.S => (componentLaw q.m : Measure (Option (Fin q.m)))))
        let I := (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
        let Q := (canonicalLaw q : Measure (CanonicalSeed q))
        let decode : (((Fin q.K → Bool) × (Fin q.K → Fin q.S → Option (Fin q.m))) ×
            Fin (max 1 q.K)) → CanonicalSeed q := fun z => (z.1.1,z.1.2,z.2)
        have hd : Measurable decode := measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
        have hm : MeasurePreserving decode ((B.prod R).prod I) Q := measurePreserving_prodAssoc B R I
        let X := fun z : CanonicalSeed q => fun j : Fin q.K => idealTrace q f z j.val
        have hX : Measurable X := measurable_of_countable _
        have hinv : ∀ a b, (X ∘ decode) (a,b)=(X ∘ decode) (a,(⟨0,by omega⟩ : Fin (max 1 q.K))) := by
          intro a b
          funext j
          exact freyaIdealSelectorInvariant q f (a.1,a.2,⟨0,by omega⟩) b j.val
        have h := freyaSelectorProduct (B.prod R) I (⟨0,by omega⟩ : Fin (max 1 q.K))
          (X ∘ decode) (hX.comp hd) hinv
        dsimp only
        change Q.map (fun z => (X z,z.2.2))=(Q.map X).prod I
        rw [← hm.map_eq,Measure.map_map (hX.prodMk measurable_snd.snd) hd,Measure.map_map hX hd]
        exact h
      have freyaSPMeasurable_prefix {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          (X : ℕ → Ω → α) (hX : ∀ k,Measurable (X k)) (n : ℕ) : Measurable (freyaSPPathPrefix X n) :=
        Measurable.of_eval (fun j => hX j.val)
      have freyaSPMeasurable_append {α : Type} [MeasurableSpace α] (n : ℕ) :
          Measurable (@freyaSPAppend α n) := by
        clear * - α n freyaSPAppend

        apply Measurable.of_eval
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa (config := { iota := false }) only [freyaSPAppend,Fin.lastCases_last] using
            (measurable_snd : Measurable (fun z : (Fin n → α) × α => z.2))
        · simpa (config := { iota := false }) only [freyaSPAppend,Fin.lastCases_castSucc,Function.comp_def] using
            ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (Fin n → α) × α => z.1)))
      have freyaSPAppend_prefix {Ω α : Type} (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
          freyaSPAppend (freyaSPPathPrefix X n ω,X n ω)=freyaSPPathPrefix X (n+1) ω := by
        clear * - Ω α X n ω freyaSPPathPrefix freyaSPAppend

        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp (config := { iota := false }) [freyaSPAppend,freyaSPPathPrefix]
        · simp (config := { iota := false }) [freyaSPAppend,freyaSPPathPrefix]
      have freyaSPResample_lintegral {ι α : Type} [Fintype ι] [DecidableEq ι]
          [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
          (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) (F : (ι → α) → ℝ≥0∞) :
          (∫⁻ z, F z ∂(Measure.pi fun _ : ι => μ)) =
            ∫⁻ z, ∫⁻ a, F (Function.update z i a) ∂μ ∂(Measure.pi fun _ : ι => μ) := by
        clear * - ι α μ i F freyaDevelopmentResample

        have h := freyaDevelopmentResample μ i
        have law : HasLaw (fun z : (ι → α) × α => Function.update z.1 i z.2)
            (Measure.pi fun _ : ι => μ) ((Measure.pi fun _ : ι => μ).prod μ) :=
          ⟨h.measurable.aemeasurable, h.map_eq⟩
        rw [← law.lintegral_comp (measurable_of_countable F).aemeasurable]
        exact lintegral_prod _ (measurable_of_countable _).aemeasurable
      have freyaPageTraceSeed (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
          (trace q O seed ω k).seed = seed := by
        clear * - q O seed ω k freyaPageUpdateSeed

        induction k with
        | zero => rfl
        | succ k ih =>
          change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
          rw [freyaPageUpdateSeed,ih]
      have freyaPageIterationMonotone (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          Monotone (fun k => (trace q O seed ω k).iteration) := by
        clear * - q O seed ω freyaPageUpdateIteration

        apply monotone_nat_of_le_succ
        intro k
        have h := freyaPageUpdateIteration q (trace q O seed ω k)
          (replyAt q O seed ω k (query q (trace q O seed ω k)))
        change (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration ∨
          (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration+1 at h
        omega
      have freyaPagePhaseSafety (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          let Safe := fun s : State q =>
            (∀ first c,s.phase=Phase.full first c →
              c.original.length=q.m ∧ c.remaining≠[] ∧
              (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
            (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
              ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
                (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
            s.iteration≤rounds q
          ∀ k,Safe (trace q O seed ω k) := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaDifferenceLiveStep freyaPageDifferenceQuery freyaDifferenceInitialSafe freyaPageFullQuery freyaFullSafeUpdate freyaFullInitialSafe

        classical
        let Safe := fun s : State q =>
            (∀ first c,s.phase=Phase.full first c →
              c.original.length=q.m ∧ c.remaining≠[] ∧
              (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
            (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
              ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
                (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
            s.iteration≤rounds q
        change ∀ k,Safe (trace q O seed ω k)
        have hfull (s : State q) (first : Bool) (c : FullState q.d q.m q.n)
            (hp : s.phase=Phase.full first c) (h1 : c.original.length=q.m) (h2 : c.remaining≠[])
            (h3 : ∀ b ∈ c.remaining,b<c.original.length)
            (h4 : legalRequest τ ⟨c.clock,c.pending⟩) (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first' c' he
            rw [hp] at he
            cases he
            exact ⟨h1,h2,h3,h4⟩
          · intro c' he
            rw [hp] at he
            cases he
        have hdiff (s : State q) (c : DifferenceState q.d q.m q.n)
            (hp : s.phase=Phase.difference c) (h1 : c.target=q.S) (h2 : c.count<c.target)
            (h3 : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y))
            (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first c' he
            rw [hp] at he
            cases he
          · intro c' he
            rw [hp] at he
            cases he
            exact ⟨h1,h2,h3⟩
        have hhalt (s : State q) (hp : s.phase=Phase.halted) (hi : s.iteration≤rounds q) : Safe s := by
          refine ⟨?_,?_,hi⟩
          · intro first c he; rw [hp] at he; cases he
          · intro c he; rw [hp] at he; cases he
        have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
          intro he
          have hh := congrArg List.length he
          simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
          omega
        have hadvance (s : State q) (hi : s.iteration≤rounds q) : Safe (advance q s) := by
          delta advance
          split
          · exact hhalt _ rfl hi
          · rename_i hlt
            dsimp only
            by_cases hrefresh : refreshAt s.seed s.iteration=true
            · rw [ite_eq_left hrefresh]
              have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels
                (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID τ
              apply hfull _ false _ rfl (List.length_ofFn) hf.1 hf.2.1 hf.2.2
              dsimp only
              omega
            · rw [ite_eq_right hrefresh]
              apply hdiff _ _ rfl rfl hS
                (freyaDifferenceInitialSafe hm q.S hS _ _ _ _ _ τ)
              dsimp only
              omega
        have hinit : Safe (initial q seed) := by
          have hp : (initial q seed).phase=Phase.full true
              (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
            delta initial
            dsimp only
            rw [ite_eq_right (by omega)]
          have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels q.x0 0 (seed.1 0) 0 τ
          exact hfull _ true _ hp (List.length_ofFn) hf.1 hf.2.1 hf.2.2 (Nat.zero_le _)
        intro k
        induction k with
        | zero => exact hinit
        | succ k ih =>
          let s := trace q O seed ω k
          change Safe s at ih
          change Safe (update q s (replyAt q O seed ω k (query q s)))
          cases hs : s.phase with
          | halted =>
            have hu : update q s (replyAt q O seed ω k (query q s))=s := by delta update; rw [hs]
            rw [hu]
            exact ih
          | full first c =>
            obtain ⟨hlen,hne,hb,hl⟩ := ih.1 first c hs
            have hquery := freyaPageFullQuery q s first c hs
            rw [hquery]
            let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
            have ht := freyaFullSafeUpdate c hne hb f τ (fun r => replyAt q O seed ω k (0,r)) hl (hservice k).2
            change t.original=c.original ∧ _ at ht
            delta update
            rw [hs]
            dsimp only
            change Safe (if t.remaining.isEmpty then advance q _ else _)
            by_cases he : t.remaining.isEmpty=true
            · rw [ite_eq_left he]
              apply hadvance
              exact ih.2.2
            · rw [ite_eq_right he]
              have htne : t.remaining≠[] := by intro hz; apply he; rw [hz]; rfl
              exact hfull _ first t rfl (ht.1 ▸ hlen) htne ht.2.1 (ht.2.2 htne) ih.2.2
          | difference c =>
            obtain ⟨htarget,hcount,hp⟩ := ih.2.1 c hs
            have hquery := freyaPageDifferenceQuery q s c hs
            rw [hquery]
            obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,hpn⟩ :=
              freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hp
            delta update
            rw [hs]
            dsimp only
            rw [ht]
            dsimp only
            by_cases he : c.target≤c.count+1
            · rw [ite_eq_left he]
              apply hadvance
              exact ih.2.2
            · rw [ite_eq_right he]
              refine hdiff _ _ rfl ?_ ?_ ?_ ?_
              · exact htarget
              · change c.count+1<c.target
                omega
              · exact hpn
              · exact ih.2.2
      have freyaBatchEndFacts (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          a<e ∧ e≤eventLimit q ∧
            (∀ r,a≤r → r<e → (trace q O seed ω r).iteration=b ∧ active (trace q O seed ω r)=true) ∧
            ((trace q O seed ω e).iteration≠b ∨ active (trace q O seed ω e)=false) := by
        clear * - q O seed ω b a e hs he freyaPageFirstMatch freyaPageBatchStartFacts

        have hstart := freyaPageBatchStartFacts q O seed ω b a hs
        dsimp only [batchEndCall] at he
        rw [hs] at he
        dsimp only [Option.bind_some] at he
        obtain ⟨hlim,htrue,hprev⟩ := freyaPageFirstMatch _ _ e he
        have hafter : a<e := by
          have hh := htrue
          simp (config := { iota := false }) only [Bool.and_eq_true,decide_eq_true_eq] at hh
          exact hh.1
        refine ⟨hafter,by omega,?_,?_⟩
        · intro r har hre
          by_cases hr : r=a
          · subst r; exact ⟨hstart.2.1,hstart.2.2.1⟩
          · have hlt : a<r := by omega
            have hh := hprev r hre
            have hit : (trace q O seed ω r).iteration=b := by
              by_contra h
              apply hh
              have hd : decide ((trace q O seed ω r).iteration≠b)=true := decide_eq_true_eq.mpr h
              simp (config := { iota := false }) only [hlt,hd,decide_true,Bool.true_and,Bool.true_or]
            refine ⟨hit,?_⟩
            cases ha : active (trace q O seed ω r) with
            | false =>
              apply False.elim
              apply hh
              simp (config := { iota := false }) only [hlt,decide_true,Bool.true_and,ha,Bool.not_false,Bool.or_true]
            | true => rfl
        · simpa (config := { iota := false }) only [hafter,decide_true,Bool.true_and,Bool.or_eq_true,
            Bool.not_eq_true',decide_eq_true_eq] using htrue
      have freyaInvocationOfStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a : ℕ)
          (hs : batchStartCall q O seed ω b=some a) :
          ∃ full x y clock firstID,invocation q O seed ω b=some (full,x,y,clock,firstID) := by
        clear * - q O seed ω b a hs freyaPageBatchStartFacts

        have ha := (freyaPageBatchStartFacts q O seed ω b a hs).2.2.1
        dsimp only [invocation]
        rw [hs]
        dsimp only [Option.bind_some]
        cases hp : (trace q O seed ω a).phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c => exact ⟨true,c.point,c.point,c.clock,c.nextID-q.n,rfl⟩
        | difference c => exact ⟨false,c.x,c.y,c.clock,c.nextID-q.n,rfl⟩
      have freyaInsideUpdate (q : Raw) (s : State q) (r : Reply q.d q.n)
          (hi : (update q s r).iteration=s.iteration) (ha : active (update q s r)=true) :
          freyaInside (update q s r)=freyaInside s := by
        clear * - q s r hi ha freyaInside freyaInsideAdvanceFalse

        dsimp only [update] at hi ha ⊢
        cases hp : s.phase with
        | halted => rfl
        | full first c =>
          rw [hp] at hi ha
          dsimp only at hi ha ⊢
          by_cases he : (fullUpdate c r).remaining.isEmpty=true
          · rw [ite_eq_left he] at hi ha ⊢
            exact False.elim (freyaInsideAdvanceFalse q _ hi ha)
          · rw [ite_eq_right he]
            dsimp only [freyaInside]
            rw [hp]
        | difference c =>
          rw [hp] at hi ha
          dsimp only at hi ha ⊢
          by_cases he : (differenceUpdate c r).target≤(differenceUpdate c r).count
          · rw [ite_eq_left he] at hi ha ⊢
            exact False.elim (freyaInsideAdvanceFalse q _ hi ha)
          · rw [ite_eq_right he]
            dsimp only [freyaInside]
            rw [hp]
      have freyaPageGradientAdvance (q : Raw) (f : Fin q.m → Space q.d → ℝ) (s : State q) :
          freyaPageGradientInvariant q f (advance q s) := by
        clear * - q f s freyaFullGradientInitial freyaPageGradientInvariant

        intro first c hp
        dsimp only [advance] at hp ⊢
        split at hp
        · contradiction
        · rename_i hi
          rw [ite_eq_right hi]
          dsimp only at hp ⊢
          split at hp
          · have he := Phase.full.inj hp
            rw [← he.2]
            exact ⟨rfl,rfl,freyaFullGradientInitial q.n f _ _ _ _ _⟩
          · contradiction
      have freyaPageGradientInitial (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (seed : Seed q.K) : freyaPageGradientInvariant q f (initial q seed) := by
        clear * - q f seed freyaFullGradientInitial freyaPageGradientInvariant

        intro first c hp
        dsimp only [initial] at hp ⊢
        split at hp
        · contradiction
        · have he := Phase.full.inj hp
          rw [← he.2]
          exact ⟨rfl,rfl,freyaFullGradientInitial q.n f _ _ _ _ _⟩
      have freyaQueryControl (q : Raw) (s t : State q) (h : freyaControl s=freyaControl t) :
          query q s=query q t := by
        clear * - q s t h freyaControl freyaControlRecord

        rw [freyaControlRecord q s t h]
        rfl
      have freyaLabelAtMeas (m : ℕ) : Measurable (fun row : ChoiceRow => labelAt row m) := by
        clear * - m freyaOptionSingleton

        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        by_cases hm : 0<m
        · let g : Fin (m-1+1) → Option (Fin m) := fun i => some ⟨i.val,by have := i.isLt; omega⟩
          have hg : Measurable g := measurable_of_countable g
          have he : Measurable (fun row : ChoiceRow => row (m-1)) := measurable_pi_apply (m-1)
          convert hg.comp he using 1
          funext row
          delta labelAt
          rw [dite_eq_left hm]
          rfl
        · delta labelAt
          simp (config := { iota := false }) only [hm,dite_false]
          exact measurable_const
      have freyaDispatchMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (kind : Ω → JobKind d) (clock : Ω → ℝ≥0) (id : Ω → ℕ)
          (label : Ω → Option (Fin m)) (hk : Measurable kind) (hc : Measurable clock)
          (hi : Measurable id) (hl : Measurable label) :
          Measurable (fun z => dispatch (kind z) (clock z) (id z) (label z)) := by
        clear * - Ω d m kind clock id label hk hc hi hl freyaOptionSomeMeas freyaOptionParamMeas

        have hb : Measurable (fun z : Ω × Fin m =>
            some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) := by
          apply freyaOptionSomeMeas.comp
          change Measurable[_,MeasurableSpace.comap
            (fun j : Job d m => (j.component,j.kind,j.started,j.id)) inferInstance]
            (fun z : Ω × Fin m => (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m))
          rw [measurable_comap_iff]
          exact (measurable_snd.prodMk ((hk.comp measurable_fst).prodMk
            ((hc.comp measurable_fst).prodMk (hi.comp measurable_fst))))
        have h := freyaOptionParamMeas label hl (fun _ => none) measurable_const
          (fun z : Ω × Fin m => some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) hb
        convert h using 1
        funext z
        delta dispatch
        cases label z <;> rfl
      have freyaSelectedLabelFixedMeas {m : ℕ} (labels : List (Fin m)) (rem : List ℕ) :
          Measurable (fun row : ChoiceRow => selectedLabel labels rem row) := by
        clear * - m labels rem freyaOptionSingleton

        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        cases rem with
        | nil => exact measurable_const
        | cons a rem =>
          let g := fun i : Fin (rem.length+1) => labels[(a::rem).get i]?
          have he : Measurable (fun row : ChoiceRow => row rem.length) := measurable_pi_apply rem.length
          have h := (measurable_of_countable g).comp he
          convert h using 1
          funext row
          delta selectedLabel chooseRemaining
          simp (config := { iota := false }) only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,dite_false,
            Option.bind_some]
          rfl
      have freyaPhaseParamMeas {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {d m n : ℕ}
          (p : Ω → Phase d m n) (hp : Measurable p) (b : Ω → β) (hb : Measurable b)
          (full : Ω × (Bool × FullState d m n) → β) (hfull : Measurable full)
          (diff : Ω × DifferenceState d m n → β) (hdiff : Measurable diff) :
          Measurable (fun z => (p z).casesOn (motive := fun _ => β) (fun first c => full (z,first,c))
            (fun c => diff (z,c)) (b z)) := by
        clear * - Ω β d m n p hp b hb full hfull diff hdiff freyaPhaseCodeMeas

        have hi := (hfull.sumElim hdiff).comp
          (MeasurableEquiv.prodSumDistrib Ω (Bool × FullState d m n) (DifferenceState d m n)).measurable
        have ho := ((hb.comp measurable_fst).sumElim hi).comp
          (MeasurableEquiv.prodSumDistrib Ω Unit ((Bool × FullState d m n) ⊕ DifferenceState d m n)).measurable
        have h := ho.comp (measurable_id.prodMk (freyaPhaseCodeMeas.comp hp))
        convert h using 1
        funext z
        dsimp only [Function.comp_def,id_eq]
        cases p z <;> rfl'
      have freyaActiveMeas (q : Raw) : Measurable (active : State q → Bool) := by
        clear * - q freyaPhaseCode freyaPhaseCodeMeas freyaStateCodeMeas

        have hphase := (freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd
        have h : Measurable (fun s : State q => Sum.elim (fun _ : Unit => false)
          (fun _ : (Bool × FullState q.d q.m q.n) ⊕ DifferenceState q.d q.m q.n => true)
            (freyaPhaseCode s.phase)) :=
          (measurable_const.sumElim measurable_const).comp (freyaPhaseCodeMeas.comp hphase)
        convert h using 1
        funext s
        dsimp only [active]
        cases s.phase <;> rfl
      have freyaUpdateControl (q : Raw) (s : State q) (new : Seed q.K) (p : Space q.d)
          (r : Reply q.d q.n) (hrows : new.1=s.seed.1) (hbits : new.2.1=s.seed.2.1) :
          freyaControl (update q {s with seed:=new,selected:=p} r)=freyaControl (update q s r) := by
        clear * - q s new p r hrows hbits freyaControl freyaAdvanceControl

        dsimp only [update]
        cases hp : s.phase with
        | halted => dsimp only [freyaControl]; rw [hp]
        | full first c =>
          dsimp only
          split
          · exact freyaAdvanceControl q {s with
              g:=fullResult (fullUpdate c r)
              clock:=(fullUpdate c r).clock
              nextID:=(fullUpdate c r).nextID
              phase:=.full first (fullUpdate c r)} new p hrows hbits
          · rfl
        | difference c =>
          dsimp only
          split
          · exact freyaAdvanceControl q {s with
              g:=s.g+differenceResult (differenceUpdate c r)
              clock:=(differenceUpdate c r).clock
              nextID:=(differenceUpdate c r).nextID
              phase:=.difference (differenceUpdate c r)} new p hrows hbits
          · rfl
      have freyaSPPrefix_map_step {Ω Ξ α : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
          [MeasurableSpace α] (P : Measure Ω) (Q : Measure Ξ)
          [IsFiniteMeasure P] (X : ℕ → Ω → α) (Y : ℕ → Ξ → α)
          (hX : ∀ k,Measurable (X k)) (hY : ∀ k,Measurable (Y k)) (n : ℕ)
          (hrect : ∀ E U,MeasurableSet E → MeasurableSet U →
            P {ω | freyaSPPathPrefix X n ω∈E ∧ X n ω∈U}=Q {ω | freyaSPPathPrefix Y n ω∈E ∧ Y n ω∈U}) :
          P.map (freyaSPPathPrefix X (n+1))=Q.map (freyaSPPathPrefix Y (n+1)) := by
        clear * - Ω Ξ α P Q X Y hX hY n hrect freyaSPPathPrefix freyaSPAppend freyaSPRectangle_map_eq freyaSPMeasurable_prefix freyaSPMeasurable_append freyaSPAppend_prefix

        have h := freyaSPRectangle_map_eq P Q (freyaSPPathPrefix X n) (X n) (freyaSPPathPrefix Y n) (Y n)
          (freyaSPMeasurable_prefix X hX n) (hX n) (freyaSPMeasurable_prefix Y hY n) (hY n) hrect
        have hh := congrArg (Measure.map (@freyaSPAppend α n)) h
        rw [Measure.map_map (freyaSPMeasurable_append n) ((freyaSPMeasurable_prefix X hX n).prodMk (hX n)),
          Measure.map_map (freyaSPMeasurable_append n) ((freyaSPMeasurable_prefix Y hY n).prodMk (hY n))] at hh
        simpa (config := { iota := false }) only [Function.comp_def,freyaSPAppend_prefix] using hh
      have freyaSPDouble_resample {ι α β γ : Type} [Fintype ι] [DecidableEq ι]
          [Fintype α] [Fintype β] [Fintype γ]
          [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
          [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
          (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
          [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
          (i : ι) (F : (ι → α) → (ι → β) → γ → ℝ≥0∞) :
          (∫⁻ b, ∫⁻ r, ∫⁻ j, F b r j ∂ξ ∂(Measure.pi fun _ : ι => ν) ∂(Measure.pi fun _ : ι => μ)) =
            ∫⁻ b, ∫⁻ r, ∫⁻ j, ∫⁻ a, ∫⁻ t, F (Function.update b i a) (Function.update r i t) j
              ∂ν ∂μ ∂ξ ∂(Measure.pi fun _ : ι => ν) ∂(Measure.pi fun _ : ι => μ) := by
        clear * - ι α β γ μ ν ξ i F freyaSPResample_lintegral

        rw [freyaSPResample_lintegral μ i]
        apply lintegral_congr
        intro b
        calc
          (∫⁻ a, ∫⁻ r, ∫⁻ j, F (Function.update b i a) r j ∂ξ ∂(Measure.pi fun _ : ι => ν) ∂μ) =
              ∫⁻ a, ∫⁻ r, ∫⁻ t, ∫⁻ j, F (Function.update b i a) (Function.update r i t) j
                ∂ξ ∂ν ∂(Measure.pi fun _ : ι => ν) ∂μ := by
            apply lintegral_congr
            intro a
            exact freyaSPResample_lintegral ν i _
          _ = ∫⁻ r, ∫⁻ a, ∫⁻ t, ∫⁻ j, F (Function.update b i a) (Function.update r i t) j
                ∂ξ ∂ν ∂μ ∂(Measure.pi fun _ : ι => ν) :=
            lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
          _ = _ := by
            apply lintegral_congr
            intro r
            calc
              (∫⁻ a, ∫⁻ t, ∫⁻ j, F (Function.update b i a) (Function.update r i t) j ∂ξ ∂ν ∂μ) =
                  ∫⁻ a, ∫⁻ j, ∫⁻ t, F (Function.update b i a) (Function.update r i t) j ∂ν ∂ξ ∂μ := by
                apply lintegral_congr
                intro a
                exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
              _ = _ := lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
      have freyaSPOption_singleton (m : ℕ) : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
      have freyaPageFreshFull (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch=some (true,x,y,clock,firstID)) :
          y=x ∧ ∃ call first,batchStartCall q O seed ω batch=some call ∧
            (trace q O seed ω call).phase=Phase.full first
              (fullInitial q.n (List.ofFn id) x clock (seed.1 batch) firstID) := by
        clear * - q O seed ω batch firstID x y clock h freyaPageFullInvocation freyaPageFullEntryAdvance freyaPageAdvanceFull freyaPageBatchStartFacts freyaPageTraceSeed

        obtain ⟨call,first,c,hstart,hphase,hx,hy,hclock,hid⟩ :=
          freyaPageFullInvocation q O seed ω batch firstID x y clock h
        refine ⟨hy.symm.trans hx,?_⟩
        have hfacts := freyaPageBatchStartFacts q O seed ω batch call hstart
        cases call with
        | zero =>
          have hbatch : batch=0 := hfacts.2.1.symm
          change (initial q seed).phase=Phase.full first c at hphase
          have hc : first=true ∧ c=fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0) := by
            delta initial at hphase
            dsimp only at hphase
            split at hphase
            · contradiction
            · have he := Phase.full.inj hphase
              exact ⟨he.1.symm,he.2.symm⟩
          rw [hc.2] at hx hclock hid
          dsimp only [fullInitial] at hx hclock hid
          have hfirst : firstID=0 := by omega
          refine ⟨0,first,hstart,?_⟩
          change (initial q seed).phase=_
          rw [hphase,hc.2,hx,← hclock,hbatch,hfirst]
        | succ k =>
          have hprev := hfacts.2.2.2 k (Nat.lt_succ_self k)
          rw [← hfacts.2.1] at hprev
          obtain ⟨t,htseed,ht⟩ := freyaPageFullEntryAdvance q
            (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))) first c hphase hprev
          have httrace : advance q t=trace q O seed ω (k+1) := ht
          have htc : (advance q t).phase=Phase.full first c := by rw [httrace]; exact hphase
          obtain ⟨hit,_,hc⟩ := freyaPageAdvanceFull q t first c htc
          have hbatch : t.iteration+1=batch := by rw [← hit,httrace]; exact hfacts.2.1
          have hseed : t.seed=seed := htseed.trans (freyaPageTraceSeed q O seed ω k)
          rw [hc] at hx hclock hid
          dsimp only [fullInitial] at hx hclock hid
          have hfirst : t.nextID=firstID := by omega
          refine ⟨k+1,first,hstart,?_⟩
          rw [hphase,hc,hx,hclock,hseed,hbatch,hfirst]
      have freyaBatchExitState (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          ∃ t : State q,t.iteration=b ∧ t.seed=seed ∧ trace q O seed ω e=advance q t := by
        clear * - q O seed ω b a e hs he freyaExitAdvance freyaPageTraceSeed freyaBatchEndFacts

        obtain ⟨ha,_,hbefore,hexit⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hepos : 0<e := by omega
        have hed : e-1+1=e := by omega
        have hp := hbefore (e-1) (by omega) (by omega)
        have hx : (update q (trace q O seed ω (e-1))
            (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1))))).iteration≠
              (trace q O seed ω (e-1)).iteration ∨
            active (update q (trace q O seed ω (e-1))
              (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1)))))=false := by
          change (trace q O seed ω (e-1+1)).iteration≠(trace q O seed ω (e-1)).iteration ∨
            active (trace q O seed ω (e-1+1))=false
          rw [hed,hp.1]
          exact hexit
        obtain ⟨t,hti,hts,hout⟩ := freyaExitAdvance q _ _ hp.2 hx
        refine ⟨t,hti.trans hp.1,hts.trans (freyaPageTraceSeed q O seed ω (e-1)),?_⟩
        change trace q O seed ω (e-1+1)=advance q t at hout
        rwa [hed] at hout
      have freyaEndOfStart (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r)))
          (b a : ℕ) (hs : batchStartCall q O seed ω b=some a) :
          ∃ e,batchEndCall q O seed ω b=some e := by
        clear * - q hm hn hS hK f τ O seed ω hservice b a hs freyaInvocationOfStart

        obtain ⟨full,x,y,clock,firstID,hi⟩ := freyaInvocationOfStart q O seed ω b a hs
        have hh := (restart_coupling q hm hn hS hK f τ O (seed,ω) hservice b firstID full x y clock hi).1
        cases he : batchEndCall q O seed ω b with
        | none => rw [he] at hh; cases hh
        | some e => exact ⟨e,rfl⟩
      have freyaInsideBatch (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e) :
          ∀ r,a≤r → r<e → freyaInside (trace q O seed ω r)=freyaInside (trace q O seed ω a) := by
        clear * - q O seed ω b a e hs he freyaInside freyaBatchEndFacts freyaInsideUpdate

        obtain ⟨_,_,hb,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        intro r har
        induction r,har using Nat.le_induction with
        | base => intro _; rfl
        | succ r har ih =>
          intro hre
          have hi : (trace q O seed ω (r+1)).iteration=(trace q O seed ω r).iteration :=
            (hb (r+1) (by omega) hre).1.trans (hb r har (by omega)).1.symm
          have h := freyaInsideUpdate q (trace q O seed ω r)
            (replyAt q O seed ω r (query q (trace q O seed ω r))) hi (hb (r+1) (by omega) hre).2
          exact h.trans (ih (by omega))
      have freyaPageGradientTrace (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) (a : ℕ) :
          freyaPageGradientInvariant q f (trace q O seed ω a) := by
        clear * - q hm hn hS hK f τ O seed ω hservice a freyaPageFullQuery freyaFullGradientUpdate freyaPageGradientInvariant freyaPagePhaseSafety freyaPageGradientAdvance freyaPageGradientInitial

        induction a with
        | zero => exact freyaPageGradientInitial q f seed
        | succ a ih =>
          let s := trace q O seed ω a
          change freyaPageGradientInvariant q f (update q s (replyAt q O seed ω a (query q s)))
          cases hp : s.phase with
          | halted => dsimp only [update]; rw [hp]; exact ih
          | full first c =>
            obtain ⟨horig,hpoint,hgrad⟩ := ih first c hp
            obtain ⟨_,hne,_,hlegal⟩ :=
              (freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice a).1 first c hp
            have hg := freyaFullGradientUpdate c hne f τ
              (fun r => replyAt q O seed ω a (0,r)) hlegal (hservice a).2 hgrad
            rw [freyaPageFullQuery q s first c hp]
            dsimp only [update]
            rw [hp]
            dsimp only
            split
            · exact freyaPageGradientAdvance q f _
            · intro first' c' hp'
              have he := Phase.full.inj hp'
              rw [← he.2]
              exact ⟨hg.1.trans horig,hg.2.1.trans hpoint,hg.2.2⟩
          | difference c =>
            dsimp only [update]
            rw [hp]
            dsimp only
            split
            · exact freyaPageGradientAdvance q f _
            · intro first' c' hp'
              cases hp'
      have freyaFullInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (n : ℕ) (labels : List (Fin m)) (x : Ω → Space d) (clock : Ω → ℝ≥0)
          (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
          (hx : Measurable x) (hc : Measurable clock) (hr : Measurable rows) (hf : Measurable first) :
          Measurable (fun z => fullInitial n labels (x z) (clock z) (rows z) (first z)) := by
        clear * - Ω d m n labels x clock rows first hx hc hr hf freyaMeasurableSelect freyaFullCode freyaDispatchMeas freyaSelectedLabelFixedMeas

        have hp (i : Fin n) : Measurable (fun z =>
            dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
              (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))) :=
          freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hc (hf.add_const i.val)
            ((freyaSelectedLabelFixedMeas labels (List.range labels.length)).comp
              (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
        change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
        rw [measurable_comap_iff]
        change Measurable (fun z => (labels,List.range labels.length,x z,(0 : Space d),
          (fun i : Fin n => dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
            (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))),
          clock z,rows z,first z+n))
        exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk
          (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n)))))))
      have freyaDifferenceInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (n S : ℕ) (x y : Ω → Space d) (clock : Ω → ℝ≥0)
          (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
          (hx : Measurable x) (hy : Measurable y) (hc : Measurable clock)
          (hr : Measurable rows) (hf : Measurable first) :
          Measurable (fun z => differenceInitial (m:=m) n S (x z) (y z) (clock z) (rows z) (first z)) := by
        clear * - Ω d m n S x y clock rows first hx hy hc hr hf freyaMeasurableSelect freyaDifferenceCode freyaLabelAtMeas freyaDispatchMeas

        have hp (i : Fin n) : Measurable (fun z => if S=0 then none else
            dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
              (labelAt (rows z (first z+i.val)) m)) := by
          by_cases hS : S=0
          · simp (config := { iota := false }) only [hS,ite_true]; exact measurable_const
          · simp (config := { iota := false }) only [hS,ite_false]
            exact freyaDispatchMeas _ _ _ _ (measurable_inr.comp (hx.prodMk hy)) hc (hf.add_const i.val)
              ((freyaLabelAtMeas m).comp
                (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
        change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
        rw [measurable_comap_iff]
        change Measurable (fun z => (S,(0 : ℕ),x z,y z,(0 : Space d),
          (fun i : Fin n => if S=0 then none else dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
            (labelAt (rows z (first z+i.val)) m)),clock z,rows z,first z+n))
        exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk (hy.prodMk
          (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n))))))))
      have freyaFullReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
          (s : Ω → FullState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
          (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
          Measurable (fun z => freyaFullReplyJob (s z) (r z) (job z)) := by
        clear * - Ω d m n s r job hs hr hj freyaMeasurableSelect freyaFullCode freyaJobCodeMeas freyaFullReplyJob freyaOptionSingleton freyaFullCodeMeas freyaDispatchMeas freyaSelectedLabelFixedMeas

        classical
        let : MeasurableSingletonClass (Option ℕ) := freyaOptionSingleton
        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        have hcode := freyaFullCodeMeas.comp hs
        have hjcode := freyaJobCodeMeas.comp hj
        have ho : Measurable (fun z => (s z).original) := hcode.fst
        have hrem : Measurable (fun z => (s z).remaining) := hcode.snd.fst
        have hx : Measurable (fun z => (s z).point) := hcode.snd.snd.fst
        have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.fst
        have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.fst
        have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.fst
        have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd
        let found := fun z => (s z).remaining.find? fun a => decide ((s z).original[a]?=some (job z).component)
        let rem := fun z => (found z).elim (s z).remaining (fun a => (s z).remaining.erase a)
        let sum := fun z => if (found z).isSome then (s z).sum+(r z).2.2.2 else (s z).sum
        let next := fun z => dispatch (Sum.inl (s z).point) (r z).2.2.1 (s z).nextID
          (selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID))
        have hf : Measurable found :=
          (measurable_of_countable (fun p : List (Fin m) × List ℕ × Fin m =>
            p.2.1.find? fun a => decide (p.1[a]?=some p.2.2))).comp (ho.prodMk (hrem.prodMk hjcode.fst))
        have hrem' : Measurable rem :=
          (measurable_of_countable (fun p : List ℕ × Option ℕ => p.2.elim p.1 (fun a => p.1.erase a))).comp
            (hrem.prodMk hf)
        have hsum' : Measurable sum := (hsum.add hr.snd.snd.snd).ite
          (((measurable_of_countable (fun o : Option ℕ => o.isSome)).comp hf) (measurableSet_singleton true)) hsum
        have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
          freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
        have hlabel : Measurable (fun z => selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID)) :=
          freyaMeasurableSelect _ (ho.prodMk hrem') _
            (fun p => (freyaSelectedLabelFixedMeas p.1 p.2).comp hrow)
        have hnext : Measurable next := freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hr.snd.snd.fst hid hlabel
        have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
          freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
        have hnew : Measurable (fun z => {s z with
            remaining:=rem z
            sum:=sum z
            pending:=Function.update (s z).pending (r z).1 (next z)
            clock:=(r z).2.2.1
            nextID:=(s z).nextID+1}) := by
          change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
          rw [measurable_comap_iff]
          exact ho.prodMk (hrem'.prodMk (hx.prodMk (hsum'.prodMk
            (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1)))))))
        exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
          (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
      have freyaDifferenceReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
          (s : Ω → DifferenceState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
          (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
          Measurable (fun z => freyaDifferenceReplyJob (s z) (r z) (job z)) := by
        clear * - Ω d m n s r job hs hr hj freyaMeasurableSelect freyaDifferenceCode freyaJobCodeMeas freyaDifferenceReplyJob freyaDifferenceCodeMeas freyaLabelAtMeas freyaDispatchMeas

        classical
        have hcode := freyaDifferenceCodeMeas.comp hs
        have hjcode := freyaJobCodeMeas.comp hj
        have ht : Measurable (fun z => (s z).target) := hcode.fst
        have hcount : Measurable (fun z => (s z).count) := hcode.snd.fst
        have hx : Measurable (fun z => (s z).x) := hcode.snd.snd.fst
        have hy : Measurable (fun z => (s z).y) := hcode.snd.snd.snd.fst
        have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.snd.fst
        have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.snd.fst
        have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.snd.fst
        have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd.snd
        let next := fun z => dispatch (Sum.inr ((s z).x,(s z).y)) (r z).2.2.1 (s z).nextID
          (labelAt ((s z).rows (s z).nextID) m)
        have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
          freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
        have hnext : Measurable next := freyaDispatchMeas _ _ _ _
          (measurable_inr.comp (hx.prodMk hy)) hr.snd.snd.fst hid ((freyaLabelAtMeas m).comp hrow)
        have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
          freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
        have hnew : Measurable (fun z => {s z with
            count:=(s z).count+1
            sum:=(s z).sum+(r z).2.2.2
            pending:=Function.update (s z).pending (r z).1 (next z)
            clock:=(r z).2.2.1
            nextID:=(s z).nextID+1}) := by
          change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
          rw [measurable_comap_iff]
          exact ht.prodMk ((hcount.add_const 1).prodMk (hx.prodMk (hy.prodMk ((hsum.add hr.snd.snd.snd).prodMk
            (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1))))))))
        exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
          (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
      have freyaPageQueryMeas (q : Raw) : Measurable (query q) := by
        clear * - q freyaFullCode freyaDifferenceCode freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPendingRequestMeas freyaPhaseParamMeas

        classical
        have hfull : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) =>
            if z.2.2.remaining.isEmpty then none else pendingRequest z.2.2.clock z.2.2.pending) := by
          have hc : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) => freyaFullCode z.2.2) :=
            freyaFullCodeMeas.comp measurable_snd.snd
          exact measurable_const.ite
            (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst) (measurableSet_singleton true))
            (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.fst))
        have hdiff : Measurable (fun z : State q × DifferenceState q.d q.m q.n =>
            if z.2.target≤z.2.count then none else pendingRequest z.2.clock z.2.pending) := by
          have hc : Measurable (fun z : State q × DifferenceState q.d q.m q.n => freyaDifferenceCode z.2) :=
            freyaDifferenceCodeMeas.comp measurable_snd
          exact measurable_const.ite (measurableSet_le hc.fst hc.snd.fst)
            (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.snd.fst))
        have hp := freyaPhaseParamMeas (fun s : State q => s.phase)
          ((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd)
          (fun _ => (none : Option (Request q.d q.m q.n))) measurable_const _ hfull _ hdiff
        have h : Measurable (fun s : State q => ((0 : Fin 1), s.phase.casesOn
            (motive:=fun _ => Option (Request q.d q.m q.n))
            (fun _ c => if c.remaining.isEmpty then none else pendingRequest c.clock c.pending)
            (fun c => if c.target≤c.count then none else pendingRequest c.clock c.pending) none)) :=
          measurable_const.prodMk hp
        convert h using 1
        funext s
        delta query
        cases s.phase <;> rfl
      have freyaSelectedTrace (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (a : ℕ) :
          (outputIndex seed).val=(trace q O seed ω a).iteration →
            (trace q O seed ω a).selected=(trace q O seed ω a).x := by
        clear * - q O seed ω a freyaSelectedUpdate freyaPageTraceSeed

        induction a with
        | zero => intro _; rfl
        | succ a ih =>
          have h := freyaSelectedUpdate q (trace q O seed ω a)
            (replyAt q O seed ω a (query q (trace q O seed ω a)))
          rw [freyaPageTraceSeed] at h
          have ht := h ih
          change (outputIndex (trace q O seed ω (a+1)).seed).val=_ → _ at ht
          rwa [freyaPageTraceSeed] at ht
      have freyaSelectedTraceStable (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (a N : ℕ) (haN : a≤N)
          (hi : (outputIndex seed).val≤(trace q O seed ω a).iteration) :
          (trace q O seed ω N).selected=(trace q O seed ω a).selected := by
        clear * - q O seed ω a N haN hi freyaSelectedUpdateStable freyaPageTraceSeed freyaPageIterationMonotone

        induction N,haN using Nat.le_induction with
        | base => rfl
        | succ N haN ih =>
          have hmono := freyaPageIterationMonotone q O seed ω haN
          change (trace q O seed ω a).iteration≤(trace q O seed ω N).iteration at hmono
          have h := freyaSelectedUpdateStable q (trace q O seed ω N)
            (replyAt q O seed ω N (query q (trace q O seed ω N)))
          rw [freyaPageTraceSeed] at h
          exact (h (hi.trans hmono)).trans ih
      have freyaSelectorTraceInvariant (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hrows : new.1=seed.1) (hbits : new.2.1=seed.2.1) :
          ∀ a,freyaControl (trace q O new ω a)=freyaControl (trace q O seed ω a) := by
        clear * - q O seed new ω hrows hbits freyaControl freyaControlRecord freyaPageTraceSeed freyaQueryControl freyaUpdateControl hobl

        intro a
        induction a with
        | zero => dsimp only [trace,run,initial,freyaControl]; rw [hrows]
        | succ a ih =>
          have hs : trace q O new ω a={trace q O seed ω a with
              seed:=new,selected:=(trace q O new ω a).selected} := by
            have h := freyaControlRecord q _ _ ih
            rwa [freyaPageTraceSeed q O new ω a] at h
          have hq := freyaQueryControl q _ _ ih
          change freyaControl (update q (trace q O new ω a) (replyAt q O new ω a (query q (trace q O new ω a))))=_
          rw [replyAt_seed q O hobl new seed ω a,hq,hs]
          exact freyaUpdateControl q _ _ _ _
            (by rw [freyaPageTraceSeed]; exact hrows)
            (by rw [freyaPageTraceSeed]; exact hbits)
      have freyaSPSame_transition_prefix_law {Ω Ξ α : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
          [MeasurableSpace α] (P : Measure Ω) (Q : Measure Ξ)
          [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
          (X : ℕ → Ω → α) (Y : ℕ → Ξ → α)
          (hX : ∀ k,Measurable (X k)) (hY : ∀ k,Measurable (Y k))
          (K : ℕ) (hK : 0<K) (hzero : P.map (X 0)=Q.map (Y 0))
          (kernel : (k : ℕ) → (Fin (k+1) → α) → Set α → ℝ≥0∞)
          (hm : ∀ k U,MeasurableSet U → Measurable (fun p => kernel k p U))
          (hPX : ∀ k,k+1<K → ∀ E U,MeasurableSet E → MeasurableSet U →
            P {ω | freyaSPPathPrefix X (k+1) ω∈E ∧ X (k+1) ω∈U}=
              ∫⁻ ω,if freyaSPPathPrefix X (k+1) ω∈E then kernel k (freyaSPPathPrefix X (k+1) ω) U else 0 ∂P)
          (hQY : ∀ k,k+1<K → ∀ E U,MeasurableSet E → MeasurableSet U →
            Q {ω | freyaSPPathPrefix Y (k+1) ω∈E ∧ Y (k+1) ω∈U}=
              ∫⁻ ω,if freyaSPPathPrefix Y (k+1) ω∈E then kernel k (freyaSPPathPrefix Y (k+1) ω) U else 0 ∂Q) :
          HasLaw (freyaSPPathPrefix X K) (Q.map (freyaSPPathPrefix Y K)) P := by
        clear * - Ω Ξ α P Q X Y hX hY K hK hzero kernel hm hPX hQY freyaSPPathPrefix freyaSPMeasurable_prefix freyaSPPrefix_map_step

        classical
        have hbase : P.map (freyaSPPathPrefix X 1)=Q.map (freyaSPPathPrefix Y 1) := by
          let const : α → Fin 1 → α := fun x _ => x
          have hc : Measurable const := Measurable.of_eval (fun _ => measurable_id)
          have h := congrArg (Measure.map const) hzero
          rw [Measure.map_map hc (hX 0),Measure.map_map hc (hY 0)] at h
          have hx : const ∘ X 0=freyaSPPathPrefix X 1 := by
            funext ω j
            have hj : j.val=0 := by omega
            simp (config := { iota := false }) only [freyaSPPathPrefix,hj]
            rfl
          have hy : const ∘ Y 0=freyaSPPathPrefix Y 1 := by
            funext ω j
            have hj : j.val=0 := by omega
            simp (config := { iota := false }) only [freyaSPPathPrefix,hj]
            rfl
          rwa [hx,hy] at h
        have hrec : ∀ k,k<K → P.map (freyaSPPathPrefix X (k+1))=Q.map (freyaSPPathPrefix Y (k+1)) := by
          intro k
          induction k with
          | zero => intro _; exact hbase
          | succ k ih =>
            intro hk
            have hold := ih (by omega)
            apply freyaSPPrefix_map_step P Q X Y hX hY (k+1)
            intro E U hE hU
            rw [hPX k hk E U hE hU,hQY k hk E U hE hU]
            let F : (Fin (k+1) → α) → ℝ≥0∞ := fun p => if p∈E then kernel k p U else 0
            have hF : Measurable F := Measurable.ite hE (hm k U hU) measurable_const
            have hLX : HasLaw (freyaSPPathPrefix X (k+1)) (Q.map (freyaSPPathPrefix Y (k+1))) P :=
              ⟨(freyaSPMeasurable_prefix X hX (k+1)).aemeasurable,hold⟩
            have hLY : HasLaw (freyaSPPathPrefix Y (k+1)) (Q.map (freyaSPPathPrefix Y (k+1))) Q :=
              ⟨(freyaSPMeasurable_prefix Y hY (k+1)).aemeasurable,rfl⟩
            exact (hLX.lintegral_comp hF.aemeasurable).trans (hLY.lintegral_comp hF.aemeasurable).symm
        refine ⟨(freyaSPMeasurable_prefix X hX K).aemeasurable,?_⟩
        have hh := hrec (K-1) (by omega)
        have he : K-1+1=K := by omega
        rw [he] at hh
        exact hh
      have freyaSPRow_lintegral (m S : ℕ) (hm : 0<m)
          (F : (Fin S → Option (Fin m)) → ℝ≥0∞) :
          (∫⁻ r,F r ∂(Measure.pi fun _ : Fin S => (componentLaw m : Measure (Option (Fin m))))) =
            ((m : ℝ≥0∞)^S)⁻¹ * ∑ v : Fin S → Fin m,F (fun j => some (v j)) := by
        clear * - m S hm F freyaSPOption_singleton

        classical
        have : NeZero m := ⟨hm.ne'⟩
        have : MeasurableSingletonClass (Option (Fin m)) := freyaSPOption_singleton m
        let μ := (PMF.uniformOfFintype (Fin m)).toMeasure
        have hsome : MeasurePreserving (some : Fin m → Option (Fin m)) μ (componentLaw m) := by
          refine ⟨measurable_of_countable _, ?_⟩
          delta componentLaw
          erw [dite_eq_left hm]
          exact PMF.toMeasure_map (some : Fin m → Option (Fin m))
            (PMF.uniformOfFintype (Fin m)) (measurable_of_countable _)
        have hprod := measurePreserving_pi (fun _ : Fin S => μ)
          (fun _ : Fin S => (componentLaw m : Measure (Option (Fin m)))) (fun _ => hsome)
        have hlaw : HasLaw (fun v : Fin S → Fin m => fun j => some (v j))
            (Measure.pi fun _ : Fin S => (componentLaw m : Measure (Option (Fin m))))
            (Measure.pi fun _ : Fin S => μ) := ⟨hprod.measurable.aemeasurable,hprod.map_eq⟩
        rw [←hlaw.lintegral_comp (measurable_of_countable F).aemeasurable,lintegral_fintype]
        have hw (v : Fin S → Fin m) :
            (Measure.pi fun _ : Fin S => μ) {v}=((m : ℝ≥0∞)^S)⁻¹ := by
          simp (config := { iota := false }) [Measure.pi_singleton,μ,PMF.uniformOfFintype_apply,ENNReal.inv_pow]
        simp_rw [hw]
        rw [←Finset.sum_mul,mul_comm]
      have freyaBatchNextStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hb : b<rounds q) (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          batchStartCall q O seed ω (b+1)=some e := by
        clear * - q O seed ω b a e hb hs he freyaPageBatchStartFacts freyaPageIterationMonotone freyaBatchEndFacts freyaBatchExitState

        classical
        obtain ⟨ha,hlim,hbefore,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        obtain ⟨t,hti,hts,hout⟩ := freyaBatchExitState q O seed ω b a e hs he
        have hnot : ¬rounds q≤t.iteration := by omega
        have hp : (trace q O seed ω e).iteration=b+1 ∧ active (trace q O seed ω e)=true := by
          rw [hout]
          dsimp only [advance]
          rw [ite_eq_right hnot]
          dsimp only
          constructor
          · rw [hti]
          · by_cases hbit : refreshAt t.seed t.iteration=true
            · rw [ite_eq_left hbit]; rfl
            · rw [ite_eq_right hbit]; rfl
        have hprev : ∀ r<e,(trace q O seed ω r).iteration≠b+1 := by
          intro r hr heq
          by_cases hra : r<a
          · have hmono := freyaPageIterationMonotone q O seed ω (Nat.le_of_lt hra)
            change (trace q O seed ω r).iteration≤(trace q O seed ω a).iteration at hmono
            have hit := (freyaPageBatchStartFacts q O seed ω b a hs).2.1
            omega
          · have hit := (hbefore r (by omega) hr).1
            omega
        dsimp only [batchStartCall]
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨?_,e,?_,?_,?_⟩
        · simp (config := { iota := false }) only [hp.1,hp.2,decide_true,Bool.and_self]
        · simpa (config := { iota := false }) only [List.length_range] using (show e<eventLimit q+1 by omega)
        · simp (config := { iota := false }) only [List.getElem_range]
        · intro r hr
          simp (config := { iota := false }) only [List.getElem_range,hprev r hr,decide_false,Bool.false_and,Bool.not_false]
      have freyaObservedPosition (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e) :
          (observedPair q O seed ω b).1=(trace q O seed ω a).x ∧
            (trace q O seed ω (e-1)).g=(trace q O seed ω a).g := by
        clear * - q O seed ω b a e hs he freyaBatchEndFacts freyaInsideBatch

        have hlt := (freyaBatchEndFacts q O seed ω b a e hs he).1
        have h := freyaInsideBatch q O seed ω b a e hs he (e-1) (by omega) (by omega)
        have hx := congrArg Prod.fst h
        have hg := congrArg (fun z => z.2.1) h
        refine ⟨?_,hg⟩
        dsimp only [observedPair]
        rw [he]
        dsimp only [Option.getD_some]
        cases hp : (trace q O seed ω (e-1)).phase <;> exact hx
      have freyaObservedFull (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (hf : ∀ i,Differentiable ℝ (f i)) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (b firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hinv : invocation q O seed ω b=some (true,x,y,clock,firstID)) :
          (observedPair q O seed ω b).2=gradient (objective f) (observedPair q O seed ω b).1 := by
        clear * - q hm hn hS hK f hf τ O seed ω hservice b firstID x y clock hinv freyaPageFullQuery freyaInside freyaObservedFullExit freyaFullGradientUpdate freyaFullGradientComplete freyaPagePhaseSafety freyaBatchEndFacts freyaPageFreshFull freyaEndOfStart freyaInsideBatch freyaPageGradientTrace

        obtain ⟨_,a,first,hs,hphase⟩ := freyaPageFreshFull q O seed ω b firstID x y clock hinv
        obtain ⟨e,he⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice b a hs
        obtain ⟨ha,_,hbefore,hexit⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hp := hbefore (e-1) (by omega) (by omega)
        have hinside := freyaInsideBatch q O seed ω b a e hs he (e-1) (by omega) (by omega)
        have htag := congrArg (fun z => z.2.2) hinside
        dsimp only [freyaInside] at htag
        rw [hphase] at htag
        obtain ⟨c,hc⟩ : ∃ c,(trace q O seed ω (e-1)).phase=Phase.full first c := by
          cases h : (trace q O seed ω (e-1)).phase with
          | halted => rw [h] at htag; cases htag
          | difference c => rw [h] at htag; cases htag
          | full first' c =>
            rw [h] at htag
            have hfirst : first'=first := Option.some.inj htag
            subst first'
            exact ⟨c,rfl⟩
        have hed : e-1+1=e := by omega
        have hleave : (update q (trace q O seed ω (e-1))
            (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1))))).iteration≠
              (trace q O seed ω (e-1)).iteration ∨
            active (update q (trace q O seed ω (e-1))
              (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1)))))=false := by
          change (trace q O seed ω (e-1+1)).iteration≠(trace q O seed ω (e-1)).iteration ∨
            active (trace q O seed ω (e-1+1))=false
          rw [hed,hp.1]
          exact hexit
        have hempty := freyaObservedFullExit q _ _ first c hc hleave
        obtain ⟨horig,hpoint,hgrad⟩ := freyaPageGradientTrace q hm hn hS hK f τ O seed ω hservice (e-1) first c hc
        obtain ⟨_,hne,_,hlegal⟩ :=
          (freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice (e-1)).1 first c hc
        have hquery := freyaPageFullQuery q _ first c hc
        rw [hquery] at hempty
        have hnew := freyaFullGradientUpdate c hne f τ
          (fun r => replyAt q O seed ω (e-1) (0,r)) hlegal (hservice (e-1)).2 hgrad
        have hresult := freyaFullGradientComplete f hf _ (hnew.1.trans horig) hnew.2.2 hempty
        rw [hnew.2.1,hpoint] at hresult
        dsimp only [observedPair]
        rw [he]
        dsimp only [Option.getD_some]
        rw [hc]
        exact (by rw [hquery]; exact hresult)
      have freyaFullUpdateMeas {d m n : ℕ} :
          Measurable (fun z : FullState d m n × Reply d n => fullUpdate z.1 z.2) := by
        clear * - d m n freyaMeasurableSelect freyaFullReplyJob freyaOptionParamMeas freyaFullCodeMeas freyaFullReplyJobMeas

        classical
        have hc := freyaFullCodeMeas (d:=d) (m:=m) (n:=n)
        have hsome : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            ((z.1).pending z.2.1).elim z.1 (fun job => freyaFullReplyJob z.1 z.2 job)) := by
          have hp : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
              z.1.pending z.2.1) :=
            freyaMeasurableSelect _ measurable_snd.fst _
              (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.fst.comp measurable_fst))
          exact freyaOptionParamMeas _ hp _ measurable_fst _
            (freyaFullReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
        have hoption : Measurable (fun z : FullState d m n × Reply d n =>
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
          freyaOptionParamMeas _ measurable_snd _ measurable_fst _
            (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
        have he : MeasurableSet {z : FullState d m n × Reply d n | z.1.remaining.isEmpty=true} :=
          ((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp
            (hc.snd.fst.comp measurable_fst)) (measurableSet_singleton true)
        have hh : Measurable (fun z : FullState d m n × Reply d n =>
            if z.1.remaining.isEmpty then z.1 else
              z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
          measurable_fst.ite he hoption
        convert hh using 1
        funext z
        delta fullUpdate
        dsimp only
        by_cases hempty : z.1.remaining.isEmpty=true
        · simp (config := { iota := false }) only [ite_eq_left hempty]
        · simp (config := { iota := false }) only [ite_eq_right hempty]
          cases hr : z.2 with
          | none => rfl
          | some r =>
            obtain ⟨i,id,t,value⟩ := r
            dsimp only [Option.elim_some]
            cases hp : z.1.pending i <;> rfl
      have freyaDifferenceUpdateMeas {d m n : ℕ} :
          Measurable (fun z : DifferenceState d m n × Reply d n => differenceUpdate z.1 z.2) := by
        clear * - d m n freyaMeasurableSelect freyaDifferenceReplyJob freyaOptionParamMeas freyaDifferenceCodeMeas freyaDifferenceReplyJobMeas

        classical
        have hc := freyaDifferenceCodeMeas (d:=d) (m:=m) (n:=n)
        have hsome : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            ((z.1).pending z.2.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 z.2 job)) := by
          have hp : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
              z.1.pending z.2.1) :=
            freyaMeasurableSelect _ measurable_snd.fst _
              (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.snd.fst.comp measurable_fst))
          exact freyaOptionParamMeas _ hp _ measurable_fst _
            (freyaDifferenceReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
        have hoption : Measurable (fun z : DifferenceState d m n × Reply d n =>
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
          freyaOptionParamMeas _ measurable_snd _ measurable_fst _
            (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
        have he : MeasurableSet {z : DifferenceState d m n × Reply d n | z.1.target≤z.1.count} :=
          measurableSet_le (hc.fst.comp measurable_fst) (hc.snd.fst.comp measurable_fst)
        have hh : Measurable (fun z : DifferenceState d m n × Reply d n =>
            if z.1.target≤z.1.count then z.1 else
              z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
          measurable_fst.ite he hoption
        convert hh using 1
        funext z
        delta differenceUpdate
        dsimp only
        by_cases hstop : z.1.target≤z.1.count
        · simp (config := { iota := false }) only [ite_eq_left hstop]
        · simp (config := { iota := false }) only [ite_eq_right hstop]
          cases hr : z.2 with
          | none => rfl
          | some r =>
            obtain ⟨i,id,t,value⟩ := r
            dsimp only [Option.elim_some]
            cases hp : z.1.pending i <;> rfl
      have freyaPageInitialMeas (q : Raw) : Measurable (initial q) := by
        clear * - q freyaPhaseFullMeas freyaStateConstructMeas freyaFullInitialMeas

        have hp : Measurable (fun seed : Seed q.K =>
            if q.m=0 ∨ q.n=0 ∨ q.K=0 then (Phase.halted : Phase q.d q.m q.n) else
              Phase.full true (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))) := by
          by_cases hbad : q.m=0 ∨ q.n=0 ∨ q.K=0
          · simp (config := { iota := false }) only [hbad,ite_true]; exact measurable_const
          · simp (config := { iota := false }) only [hbad,ite_false]
            exact freyaPhaseFullMeas.comp (measurable_const.prodMk
              (freyaFullInitialMeas q.n (List.ofFn id) (fun _ => q.x0) (fun _ => 0)
                (fun seed : Seed q.K => seed.1 0) (fun _ => 0) measurable_const measurable_const
                ((measurable_pi_apply 0).comp measurable_fst) measurable_const))
        exact freyaStateConstructMeas q id (fun _ => 0) (fun _ => q.x0) (fun _ => 0) (fun _ => q.x0)
          (fun _ => 0) (fun _ => q.n) _ measurable_id measurable_const measurable_const measurable_const
            measurable_const measurable_const measurable_const hp
      have freyaPageAdvanceMeas (q : Raw) : Measurable (advance q) := by
        clear * - q freyaMeasurableSelect freyaStateCodeMeas freyaPhaseFullMeas freyaPhaseDifferenceMeas freyaStateConstructMeas freyaFullInitialMeas freyaDifferenceInitialMeas

        classical
        have hc := freyaStateCodeMeas q
        have hseed : Measurable (fun s : State q => s.seed) := hc.fst
        have hit : Measurable (fun s : State q => s.iteration) := hc.snd.fst
        have hx : Measurable (fun s : State q => s.x) := hc.snd.snd.fst
        have hg : Measurable (fun s : State q => s.g) := hc.snd.snd.snd.fst
        have hsel : Measurable (fun s : State q => s.selected) := hc.snd.snd.snd.snd.fst
        have hclock : Measurable (fun s : State q => s.clock) := hc.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun s : State q => s.nextID) := hc.snd.snd.snd.snd.snd.snd.fst
        let x := fun s : State q => s.x-q.η • s.g
        let batch := fun s : State q => s.iteration+1
        have hnewx : Measurable x := hx.sub (hg.const_smul q.η)
        have hbatch : Measurable batch := hit.add_const 1
        have hrows : Measurable (fun s : State q => s.seed.1 (batch s)) :=
          freyaMeasurableSelect _ hbatch _ (fun k => (measurable_pi_apply k).comp hseed.fst)
        have hrefresh : Measurable (fun s : State q => refreshAt s.seed s.iteration) :=
          freyaMeasurableSelect _ hit _ (fun k => (measurable_pi_apply k).comp hseed.snd.fst)
        have hfull := (freyaPhaseFullMeas (m:=q.m)).comp ((measurable_const (a:=false)).prodMk
          (freyaFullInitialMeas (m:=q.m) q.n (List.ofFn id) x (fun s => s.clock) _ (fun s => s.nextID)
            hnewx hclock hrows hid))
        have hdiff := freyaPhaseDifferenceMeas.comp
          (freyaDifferenceInitialMeas (m:=q.m) q.n q.S x (fun s => s.x) (fun s => s.clock) _
            (fun s => s.nextID) hnewx hx hclock hrows hid)
        have hphase : Measurable (fun s : State q => if refreshAt s.seed s.iteration then
            Phase.full false (fullInitial q.n (List.ofFn id) (x s) s.clock (s.seed.1 (batch s)) s.nextID)
          else Phase.difference (differenceInitial q.n q.S (x s) s.x s.clock (s.seed.1 (batch s)) s.nextID)) :=
          hfull.ite (hrefresh (measurableSet_singleton true)) hdiff
        have hindex : Measurable (fun s : State q => (outputIndex s.seed).val) :=
          (measurable_of_countable (fun i : Fin (max 1 q.K) => i.val)).comp hseed.snd.snd
        have hselected : Measurable (fun s : State q =>
            if (outputIndex s.seed).val=batch s then x s else s.selected) :=
          hnewx.ite (measurableSet_eq_fun hindex hbatch) hsel
        have hnext := freyaStateConstructMeas q _ batch x _ _ _ _ _
          hseed hbatch hnewx hg hselected hclock (hid.add_const q.n) hphase
        have hstop := freyaStateConstructMeas q _ _ _ _ _ _ _ (fun _ => Phase.halted)
          hseed hit hx hg hsel hclock hid measurable_const
        exact hstop.ite (measurableSet_le measurable_const hit) hnext
      have freyaSelectorStartInvariant (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hrows : new.1=seed.1) (hbits : new.2.1=seed.2.1) (b : ℕ) :
          batchStartCall q O new ω b=batchStartCall q O seed ω b := by
        clear * - q O seed new ω hrows hbits b freyaControlRecord freyaSelectorTraceInvariant hobl

        have hs := freyaSelectorTraceInvariant q O hobl seed new ω hrows hbits
        have hp : (fun a => decide ((trace q O new ω a).iteration=b) && active (trace q O new ω a))=
            (fun a => decide ((trace q O seed ω a).iteration=b) && active (trace q O seed ω a)) := by
          funext a
          rw [freyaControlRecord q _ _ (hs a)]
          rfl
        exact congrArg (fun p => (List.range (eventLimit q+1)).find? p) hp
      have freyaSPCanonical_transition (q : Raw) (hm : 0<q.m) (hρ : 0≤q.ρ) (hρone : q.ρ≤1)
          (f : Fin q.m → Space q.d → ℝ) (k : ℕ) (hk : k<q.K)
          (E : Set (Fin (k+1) → Space q.d × Space q.d))
          (U : Set (Space q.d × Space q.d)) :
          let s := serialInput q
          let Q := (canonicalLaw s : Measure (CanonicalSeed s))
          Q {z | (fun j : Fin (k+1) => idealTrace s f z j.val)∈E ∧ idealTrace s f z (k+1)∈U} =
            ∫⁻ z,if (fun j : Fin (k+1) => idealTrace s f z j.val)∈E then
              transitionKernel q f (idealTrace s f z k) U else 0 ∂Q := by
        clear * - q hm hρ hρone f k hk E U freyaDevelopmentPastInvariant freyaSPBernoulli_lintegral freyaSPDouble_resample freyaSPOption_singleton freyaSPRow_lintegral

        classical
        let s : SerialRaw := ⟨q.d,q.m,q.x0,q.η,q.S,q.ρ,q.K⟩
        let Q := (canonicalLaw s : Measure (CanonicalSeed s))
        have : MeasurableSingletonClass (Option (Fin s.m)) := freyaSPOption_singleton s.m
        have : NeZero (max 1 s.K) := ⟨by omega⟩
        let μ := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one s.ρ)
        let ν := Measure.pi (fun _ : Fin s.S => (componentLaw s.m : Measure (Option (Fin s.m))))
        let ξ := (PMF.uniformOfFintype (Fin (max 1 s.K))).toMeasure
        let κ : Fin s.K := ⟨k,hk⟩
        let fresh (z : CanonicalSeed s) (b : Bool) (r : Fin s.S → Option (Fin s.m)) : CanonicalSeed s :=
          (Function.update z.1 κ b,Function.update z.2.1 κ r,z.2.2)
        let past (z : CanonicalSeed s) : Fin (k+1) → Space q.d × Space q.d :=
          fun j => idealTrace s f z j.val
        let F (z : CanonicalSeed s) : ℝ≥0∞ :=
          if past z∈E ∧ idealTrace s f z (k+1)∈U then 1 else 0
        have hprod (G : CanonicalSeed s → ℝ≥0∞) :
            (∫⁻ z,G z ∂Q)=∫⁻ b,∫⁻ r,∫⁻ j,G (b,r,j) ∂ξ
              ∂(Measure.pi fun _ : Fin s.K => ν) ∂(Measure.pi fun _ : Fin s.K => μ) := by
          change (∫⁻ z,G z ∂(Measure.pi fun _ : Fin s.K => μ).prod
            ((Measure.pi fun _ : Fin s.K => ν).prod ξ))=_
          rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
          apply lintegral_congr
          intro b
          exact lintegral_prod _ (measurable_of_countable _).aemeasurable
        have hres : (∫⁻ z,F z ∂Q)=∫⁻ z,∫⁻ b,∫⁻ r,F (fresh z b r) ∂ν ∂μ ∂Q := by
          rw [hprod,hprod]
          exact freyaSPDouble_resample μ ν ξ κ (fun b r j => F (b,r,j))
        have hpast (z : CanonicalSeed s) (b : Bool) (r : Fin s.S → Option (Fin s.m)) :
            past (fresh z b r)=past z := by
          funext j
          exact freyaDevelopmentPastInvariant s f κ z b r j.val (by dsimp only [κ]; omega)
        have hrec (z : CanonicalSeed s) (a : ℕ) : idealTrace s f z (a+1)=
            idealTrace._sunfold s f z (a+1) := by
          conv_lhs => delta idealTrace
          refine (Nat.brecOn.eq (motive := fun _ => Space s.d × Space s.d) (a+1)
            (idealTrace._f s f z)).trans ?_
          delta idealTrace._sunfold idealTrace._f idealTrace
          rfl
        have heval (z : CanonicalSeed s) (b : Bool) (r : Fin s.S → Option (Fin s.m)) :
            idealTrace s f (fresh z b r) (k+1)=
              let p := idealTrace s f z k
              let x := p.1-q.η • p.2
              if b then (x,gradient (objective f) x) else
                (x,p.2+(s.S : ℝ)⁻¹ • ∑ j : Fin s.S,Option.elim' (0 : Space s.d)
                  (fun i => gradient (f i) x-gradient (f i) p.1) (r j)) := by
          rw [hrec]
          delta idealTrace._sunfold
          dsimp only
          rw [dite_eq_left hk,freyaDevelopmentPastInvariant s f κ z b r k (le_refl k)]
          dsimp only [fresh,κ]
          simp (config := { iota := false }) only [Function.update_self]
          cases b with
          | false =>
            simp (config := { iota := false }) only [Bool.false_eq_true,ite_false]
            congr 3
            apply Finset.sum_congr rfl
            intro j _
            cases r j <;> rfl
          | true => rfl
        have hstep (z : CanonicalSeed s) :
            (∫⁻ b,∫⁻ r,F (fresh z b r) ∂ν ∂μ)=
              if past z∈E then transitionKernel q f (idealTrace s f z k) U else 0 := by
          have hev (b : Bool) (r : Fin s.S → Option (Fin s.m)) :
              F (fresh z b r)=
                if past z∈E ∧
                  (let p := idealTrace s f z k
                   let x := p.1-q.η • p.2
                   if b then (x,gradient (objective f) x) else
                     (x,p.2+(s.S : ℝ)⁻¹ • ∑ j : Fin s.S,Option.elim' (0 : Space s.d)
                       (fun i => gradient (f i) x-gradient (f i) p.1) (r j)))∈U then 1 else 0 := by
            dsimp only [F]
            rw [hpast,heval]
          simp_rw [hev]
          change (∫⁻ b,_ ∂bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ))=_
          rw [freyaSPBernoulli_lintegral q.ρ hρ hρone]
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false,ite_true,lintegral_const,measure_univ,mul_one]
          rw [freyaSPRow_lintegral q.m q.S hm]
          by_cases h : past z∈E
          · rw [ite_eq_left h]
            simp (config := { iota := false }) only [h,true_and,Option.elim'_some]
            dsimp only [transitionKernel]
            rw [mul_assoc]
          · simp (config := { iota := false }) only [h,false_and,ite_false,Finset.sum_const_zero,mul_zero,add_zero]
        change Q {z | past z∈E ∧ idealTrace s f z (k+1)∈U}=_
        have hset : MeasurableSet {z : CanonicalSeed s | past z∈E ∧ idealTrace s f z (k+1)∈U} :=
          Set.Countable.measurableSet (Set.to_countable _)
        have hint : (∫⁻ z,F z ∂Q)=Q {z | past z∈E ∧ idealTrace s f z (k+1)∈U} := by
          simpa (config := { iota := false }) only [F,Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
            (lintegral_indicator_one (μ := Q) hset)
        rw [←hint,hres]
        exact lintegral_congr hstep
      have freyaAllBatchBoundaries (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r))) :
          ∀ b,b≤rounds q → ∃ a e,batchStartCall q O seed ω b=some a ∧ batchEndCall q O seed ω b=some e := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaBatchZeroStart freyaEndOfStart freyaBatchNextStart

        intro b
        induction b with
        | zero =>
          intro _
          have hs := freyaBatchZeroStart q hm hn hK O seed ω
          obtain ⟨e,he⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice 0 0 hs
          exact ⟨0,e,hs,he⟩
        | succ b ih =>
          intro hb
          obtain ⟨a,e,hs,he⟩ := ih (by omega)
          have hnext := freyaBatchNextStart q O seed ω b a e (by omega) hs he
          obtain ⟨e',he'⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice (b+1) e hnext
          exact ⟨e,e',hnext,he'⟩
      have freyaPageUpdateMeas (q : Raw) :
          Measurable (fun z : State q × Reply q.d q.n => update q z.1 z.2) := by
        clear * - q freyaStateCode freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPhaseFullMeas freyaPhaseDifferenceMeas freyaStateConstructMeas freyaPhaseParamMeas freyaFullUpdateMeas freyaDifferenceUpdateMeas freyaPageAdvanceMeas

        classical
        have hfull : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            let c := fullUpdate z.2.2 z.1.2
            let s := {z.1.1 with
              clock:=c.clock
              nextID:=c.nextID
              phase:=Phase.full z.2.1 c}
            if c.remaining.isEmpty then advance q {s with g:=fullResult c} else s) := by
          have hs : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              fullUpdate z.2.2 z.1.2) := freyaFullUpdateMeas.comp (measurable_snd.snd.prodMk measurable_fst.snd)
          have hc := freyaFullCodeMeas.comp hu
          have hp := freyaPhaseFullMeas.comp (measurable_snd.fst.prodMk hu)
          have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp
          have hg := ((measurable_of_countable (fun l : List (Fin q.m) => (l.length : ℝ)⁻¹)).comp hc.fst).smul
            hc.snd.snd.snd.fst
          have hnext := (freyaPageAdvanceMeas q).comp
            (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
              hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
              hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp)
          exact hnext.ite (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst)
            (measurableSet_singleton true)) hbase
        have hdiff : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            let c := differenceUpdate z.2 z.1.2
            let s := {z.1.1 with
              clock:=c.clock
              nextID:=c.nextID
              phase:=Phase.difference c}
            if c.target≤c.count then advance q {s with g:=s.g+differenceResult c} else s) := by
          have hs : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              differenceUpdate z.2 z.1.2) := freyaDifferenceUpdateMeas.comp (measurable_snd.prodMk measurable_fst.snd)
          have hc := freyaDifferenceCodeMeas.comp hu
          have hp := freyaPhaseDifferenceMeas.comp hu
          have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp
          have hg := hs.snd.snd.snd.fst.add
            (((measurable_of_countable (fun a : ℕ => (a : ℝ)⁻¹)).comp hc.fst).smul hc.snd.snd.snd.snd.fst)
          have hnext := (freyaPageAdvanceMeas q).comp
            (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
              hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
              hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp)
          exact hnext.ite (measurableSet_le hc.fst hc.snd.fst) hbase
        have h := freyaPhaseParamMeas (fun z : State q × Reply q.d q.n => z.1.phase)
          (((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd).comp measurable_fst)
          Prod.fst measurable_fst _ hfull _ hdiff
        convert h using 1
        funext z
        delta update
        cases z.1.phase <;> rfl
      have freyaObservedFinishMeas (q : Raw) :
          Measurable (fun z : State q × Reply q.d q.n => freyaObservedFinish q z.1 z.2) := by
        clear * - q freyaStateCode freyaObservedFinish freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPhaseParamMeas freyaFullUpdateMeas freyaDifferenceUpdateMeas

        have hs : Measurable (fun z : State q × Reply q.d q.n => freyaStateCode z.1) :=
          (freyaStateCodeMeas q).comp measurable_fst
        have hfull : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            (z.1.1.x,fullResult (fullUpdate z.2.2 z.1.2))) := by
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              fullUpdate z.2.2 z.1.2) := freyaFullUpdateMeas.comp (measurable_snd.snd.prodMk measurable_fst.snd)
          have hc := freyaFullCodeMeas.comp hu
          have hsize := (measurable_of_countable (fun l : List (Fin q.m) => (l.length : ℝ)⁻¹)).comp hc.fst
          exact (hs.snd.snd.fst.comp measurable_fst).prodMk (hsize.smul hc.snd.snd.snd.fst)
        have hdiff : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            (z.1.1.x,z.1.1.g+differenceResult (differenceUpdate z.2 z.1.2))) := by
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              differenceUpdate z.2 z.1.2) := freyaDifferenceUpdateMeas.comp (measurable_snd.prodMk measurable_fst.snd)
          have hc := freyaDifferenceCodeMeas.comp hu
          have hsize := (measurable_of_countable (fun a : ℕ => (a : ℝ)⁻¹)).comp hc.fst
          exact (hs.snd.snd.fst.comp measurable_fst).prodMk
            ((hs.snd.snd.snd.fst.comp measurable_fst).add (hsize.smul hc.snd.snd.snd.snd.fst))
        have h := freyaPhaseParamMeas (fun z : State q × Reply q.d q.n => z.1.phase)
          hs.snd.snd.snd.snd.snd.snd.snd (fun z => (z.1.x,z.1.g))
          (hs.snd.snd.fst.prodMk hs.snd.snd.snd.fst) _ hfull _ hdiff
        convert h using 1
        funext z
        dsimp only [freyaObservedFinish]
        cases z.1.phase <;> rfl
      have freyaObservedInitial (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (hf : ∀ i,Differentiable ℝ (f i)) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
          observedPair q O seed ω 0=(q.x0,gradient (objective f) q.x0) := by
        clear * - q hm hn hS hK f hf τ O seed ω hservice freyaBatchZeroStart freyaEndOfStart freyaObservedPosition freyaObservedFull

        have hs := freyaBatchZeroStart q hm hn hK O seed ω
        have hi : invocation q O seed ω 0=some (true,q.x0,q.x0,0,0) := by
          dsimp only [invocation]
          rw [hs]
          dsimp only [Option.bind_some,trace,run,initial]
          rw [ite_eq_right (show ¬(q.m=0 ∨ q.n=0 ∨ q.K=0) by omega)]
          dsimp only [fullInitial]
          rw [Nat.zero_add,Nat.sub_self]
        obtain ⟨e,he⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice 0 0 hs
        have hx := (freyaObservedPosition q O seed ω 0 0 e hs he).1
        change (observedPair q O seed ω 0).1=q.x0 at hx
        have hg := freyaObservedFull q hm hn hS hK f hf τ O seed ω hservice 0 0 q.x0 q.x0 0 hi
        exact Prod.ext hx (hg.trans (congrArg (gradient (objective f)) hx))
      have freyaSelectorEndInvariant (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hrows : new.1=seed.1) (hbits : new.2.1=seed.2.1) (b : ℕ) :
          batchEndCall q O new ω b=batchEndCall q O seed ω b := by
        clear * - q O seed new ω hrows hbits b freyaControlRecord freyaSelectorTraceInvariant freyaSelectorStartInvariant hobl

        dsimp only [batchEndCall]
        rw [freyaSelectorStartInvariant q O hobl seed new ω hrows hbits b]
        congr 1
        funext first
        congr 1
        funext a
        rw [freyaControlRecord q _ _ (freyaSelectorTraceInvariant q O hobl seed new ω hrows hbits a)]
        rfl
      have freyaSPObserved_prefix_law (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (hρ : 0<q.ρ) (hρone : q.ρ≤1)
          (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i,Differentiable ℝ (f i))
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
          (hObs : ∀ b,Measurable (fun z : Seed q.K × ((a : ℕ) → O.Seed a) => observedPair q O z.1 z.2 b))
          (hzero : (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a))).map
            (fun z => observedPair q O z.1 z.2 0) =
            (canonicalLaw (serialInput q) : Measure (CanonicalSeed (serialInput q))).map
              (fun z => idealTrace (serialInput q) f z 0)) :
          HasLaw (fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
            fun j : Fin q.K => observedPair q O z.1 z.2 j.val)
            ((canonicalLaw (serialInput q) : Measure (CanonicalSeed (serialInput q))).map
              (fun z => fun j : Fin q.K => idealTrace (serialInput q) f z j.val))
            (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a))) := by
        clear * - q hm hn hS hK hρ hρone f hf τ O hservice hind hObs hzero freyaSPKernel_measurable freyaSPOption_singleton freyaSPSame_transition_prefix_law freyaSPCanonical_transition

        have : MeasurableSingletonClass (Option (Fin q.m)) := freyaSPOption_singleton q.m
        let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
        let s : SerialRaw := ⟨q.d,q.m,q.x0,q.η,q.S,q.ρ,q.K⟩
        let Q := (canonicalLaw s : Measure (CanonicalSeed s))
        let X (b : ℕ) (z : Seed q.K × ((a : ℕ) → O.Seed a)) := observedPair q O z.1 z.2 b
        let Y (b : ℕ) (z : CanonicalSeed s) := idealTrace s f z b
        have hY (b : ℕ) : Measurable (Y b) := measurable_of_countable _
        refine freyaSPSame_transition_prefix_law P Q X Y hObs hY q.K hK hzero
          (fun k p U => transitionKernel q f (p (Fin.last k)) U) ?_ ?_ ?_
        · intro k U hU
          exact (freyaSPKernel_measurable q f U hU).comp (measurable_pi_apply (Fin.last k))
        · intro k hk E U hE hU
          have hround : k<rounds q := by
            unfold rounds
            split <;> omega
          exact conditional_transition q hm hn hS hK hρ hρone f hf τ O hservice hind k hround E hE U hU
        · intro k hk E U _ _
          exact freyaSPCanonical_transition q hm hρ.le hρone f k (by omega) E U
      have freyaPageTraceMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (k : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => trace q O z.1 z.2 k) := by
        clear * - q f τ O hservice k freyaPageQueryMeas freyaPageInitialMeas freyaPageUpdateMeas

        exact (measurable_trajectory q O hservice.1.2 (freyaPageInitialMeas q)
          (freyaPageUpdateMeas q) (freyaPageQueryMeas q) k).1
      have freyaObservedOutput (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
          (N : ℕ) (hN : eventLimit q≤N) :
          (execute O (factory q) (fun _ => N) seed ω).1=
            (observedPair q O seed ω (outputIndex seed).val).1 := by
        clear * - q hm hn hS hK f τ O seed ω hservice N hN freyaBatchEndFacts freyaSelectedTrace freyaSelectedTraceStable freyaAllBatchBoundaries

        have hi : (outputIndex seed).val<q.K := by
          have h := (outputIndex seed).isLt
          simpa (config := { iota := false }) only [max_eq_right (show 1≤q.K by omega)] using h
        have hir : (outputIndex seed).val≤rounds q := by
          dsimp only [rounds]
          split <;> omega
        obtain ⟨a,e,hs,he⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O seed ω hservice
          (outputIndex seed).val hir
        obtain ⟨ha,heN,hbefore,_⟩ := freyaBatchEndFacts q O seed ω _ a e hs he
        have hp := hbefore (e-1) (by omega) (by omega)
        have hsel := freyaSelectedTrace q O seed ω (e-1) hp.1.symm
        rw [execute_correspondence]
        change (trace q O seed ω N).selected=_
        rw [freyaSelectedTraceStable q O seed ω (e-1) N (by omega) (by omega),hsel]
        dsimp only [observedPair]
        rw [he]
        dsimp only [Option.getD_some]
        cases hphase : (trace q O seed ω (e-1)).phase <;> rfl
      have freyaSelectorObservedInvariant (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
          (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hrows : new.1=seed.1) (hbits : new.2.1=seed.2.1) (b : ℕ) :
          observedPair q O new ω b=observedPair q O seed ω b := by
        clear * - q O seed new ω hrows hbits b freyaControlRecord freyaQueryControl freyaSelectorTraceInvariant freyaSelectorEndInvariant hobl

        dsimp only [observedPair]
        simp only [replyAt_seed q O hobl new seed ω]
        rw [freyaSelectorEndInvariant q O hobl seed new ω hrows hbits b]
        have hs := freyaSelectorTraceInvariant q O hobl seed new ω hrows hbits
          ((batchEndCall q O seed ω b).getD 0-1)
        rw [freyaQueryControl q _ _ hs,freyaControlRecord q _ _ hs]
      have freyaPageBatchStartMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (batch : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchStartCall q O z.1 z.2 batch) := by
        clear * - q f τ O hservice batch freyaFindMeas freyaStateCodeMeas freyaActiveMeas freyaPageTraceMeas

        apply freyaFindMeas
        intro k
        have hs := freyaPageTraceMeas q f τ O hservice k
        have hi := ((freyaStateCodeMeas q).comp hs).snd.fst
        have hb := (freyaActiveMeas q).comp hs
        exact (measurable_of_countable (fun p : ℕ × Bool => decide (p.1=batch) && p.2)).comp (hi.prodMk hb)
      have freyaBatchEndMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchEndCall q O z.1 z.2 b) := by
        clear * - q f τ O hservice b freyaFindMeas freyaOptionParamMeas freyaStateCodeMeas freyaActiveMeas freyaPageTraceMeas freyaPageBatchStartMeas

        classical
        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        have hp (a : ℕ) : Measurable (fun z : Ω × ℕ => decide (z.2<a) &&
            (decide ((trace q O z.1.1 z.1.2 a).iteration≠b) || !active (trace q O z.1.1 z.1.2 a))) := by
          have ht : Measurable (fun z : Ω × ℕ => trace q O z.1.1 z.1.2 a) :=
            (freyaPageTraceMeas q f τ O hservice a).comp measurable_fst
          have hi := ((freyaStateCodeMeas q).comp ht).snd.fst
          have ha := (freyaActiveMeas q).comp ht
          exact (measurable_of_countable (fun t : ℕ × ℕ × Bool =>
            decide (t.1<a) && (decide (t.2.1≠b) || !t.2.2))).comp
              (measurable_snd.prodMk (hi.prodMk ha))
        have hb := freyaFindMeas (List.range (eventLimit q+1)) _ hp
        have h := freyaOptionParamMeas _ (freyaPageBatchStartMeas q f τ O hservice b)
          (fun _ : Ω => (none : Option ℕ)) measurable_const _ hb
        convert h using 1
        funext z
        dsimp only [batchEndCall]
        cases batchStartCall q O z.1 z.2 b <;> rfl
      have freyaObservedPairMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((a : ℕ) → O.Seed a) => observedPair q O z.1 z.2 b) := by
        clear * - q f τ O hservice b freyaDevelopmentOptionElimMeas freyaMeasurableSelect freyaObservedFinish freyaPageQueryMeas freyaObservedFinishMeas freyaPageTraceMeas freyaBatchEndMeas freyaPageInitialMeas freyaPageUpdateMeas

        let Ω := Seed q.K × ((a : ℕ) → O.Seed a)
        have hcall : Measurable (fun z : Ω => (batchEndCall q O z.1 z.2 b).getD 0-1) := by
          have h := (measurable_of_countable (fun a : ℕ => a-1)).comp
            ((freyaDevelopmentOptionElimMeas (0 : ℕ) id measurable_id).comp
              (freyaBatchEndMeas q f τ O hservice b))
          convert h using 1
          funext z
          dsimp only [Function.comp_def]
          cases batchEndCall q O z.1 z.2 b <;> rfl
        have hf (a : ℕ) : Measurable (fun z : Ω => freyaObservedFinish q (trace q O z.1 z.2 a)
            (replyAt q O z.1 z.2 a (query q (trace q O z.1 z.2 a)))) := by
          have ht := freyaPageTraceMeas q f τ O hservice a
          exact (freyaObservedFinishMeas q).comp (ht.prodMk (measurable_replyAt q O hservice.1.2 (freyaPageInitialMeas q) (freyaPageUpdateMeas q)
              (freyaPageQueryMeas q) a measurable_id
            ((freyaPageQueryMeas q).comp ht)))
        exact freyaMeasurableSelect _ hcall _ hf
      have freyaActualSelectorProduct (q : Raw) [NeZero (max 1 q.K)] (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) :
          let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
          let X := fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
            fun j : Fin q.K => observedPair q O z.1 z.2 j.val
          P.map (fun z => (X z,outputIndex z.1))=
            (P.map X).prod (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure := by
        clear * - q f τ O hservice freyaSelectorProduct freyaSelectorObservedInvariant freyaObservedPairMeas

        classical
        let Ω := (a : ℕ) → O.Seed a
        let Rows := ℕ → ℕ → ChoiceRow
        let B := Measure.infinitePi (fun _ : ℕ =>
          bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ))
        let R : Measure Rows := Measure.infinitePi (fun _ : ℕ =>
          Measure.infinitePi (fun _ : ℕ => (rowLaw : Measure ChoiceRow)))
        let I := (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
        let ξ := (O.law : Measure Ω)
        let P := (executionLaw q O : Measure (Seed q.K × Ω))
        let μ := (R.prod B).prod ξ
        let decode : (((Rows × (ℕ → Bool)) × Ω) × Fin (max 1 q.K)) → Seed q.K × Ω :=
          fun z => ((z.1.1.1,(z.1.1.2,z.2)),z.1.2)
        have hd : Measurable decode :=
          (measurable_fst.fst.fst.prodMk (measurable_fst.fst.snd.prodMk measurable_snd)).prodMk measurable_fst.snd
        have hm : MeasurePreserving decode (μ.prod I) P := by
          have ha := measurePreserving_prodAssoc (R.prod B) ξ I
          have hb := (MeasurePreserving.id (R.prod B)).prod (Measure.measurePreserving_swap (μ:=ξ) (ν:=I))
          have hc := (measurePreserving_prodAssoc (R.prod B) I ξ).symm MeasurableEquiv.prodAssoc
          have hh := (measurePreserving_prodAssoc R B I).prod (MeasurePreserving.id ξ)
          exact hh.comp (hc.comp (hb.comp ha))
        let X := fun z : Seed q.K × Ω => fun j : Fin q.K => observedPair q O z.1 z.2 j.val
        have hX : Measurable X := Measurable.of_eval (fun j => freyaObservedPairMeas q f τ O hservice j.val)
        have hinv : ∀ a b, (X ∘ decode) (a,b)=(X ∘ decode) (a,(⟨0,by omega⟩ : Fin (max 1 q.K))) := by
          intro a b
          funext j
          exact freyaSelectorObservedInvariant q O hservice.1.1
            (a.1.1,(a.1.2,⟨0,by omega⟩)) (a.1.1,(a.1.2,b)) a.2 rfl rfl j.val
        have h := freyaSelectorProduct μ I (⟨0,by omega⟩ : Fin (max 1 q.K))
          (X ∘ decode) (hX.comp hd) hinv
        dsimp only
        change P.map (fun z => (X z,outputIndex z.1))=(P.map X).prod I
        dsimp only [outputIndex]
        rw [← hm.map_eq,Measure.map_map (hX.prodMk (measurable_fst.snd.snd)) hd,
          Measure.map_map hX hd]
        exact h
      have freyaScheduledLaw (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
          (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
          (f : Fin q.m → Space q.d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
          (N : ℕ) (hN : eventLimit q ≤ N) :
          let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
          let Q := (LongTails.Algorithms.FreyaSerial.canonicalLaw (serialInput q) :
            Measure (LongTails.Algorithms.FreyaSerial.CanonicalSeed (serialInput q)))
          HasLaw (fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
            ((fun j : Fin q.K => observedPair q O z.1 z.2 j.val), outputIndex z.1))
            (Q.map fun w => ((fun j : Fin q.K =>
              LongTails.Algorithms.FreyaSerial.idealTrace (serialInput q) f w j.val), w.2.2)) P ∧
            HasLaw (fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
              (execute O (factory q) (fun _ => N) z.1 z.2).1)
              (Q.map (LongTails.Algorithms.FreyaSerial.idealOutput (serialInput q) f)) P := by
        clear * - q hm hn hS hK hρ hρone f hf τ O hservice hind N hN freyaMeasurableSelect freyaOptionSingleton freyaIdealSelectorProduct freyaObservedInitial freyaSPObserved_prefix_law freyaObservedOutput freyaObservedPairMeas freyaActualSelectorProduct

        classical
        let : NeZero (max 1 q.K) := ⟨by omega⟩
        let : MeasurableSingletonClass (Option (Fin q.m)) := freyaOptionSingleton
        let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
        let s : SerialRaw := ⟨q.d,q.m,q.x0,q.η,q.S,q.ρ,q.K⟩
        let Q := (canonicalLaw s : Measure (CanonicalSeed s))
        let X := fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
          fun j : Fin q.K => observedPair q O z.1 z.2 j.val
        let Y := fun z : CanonicalSeed s => fun j : Fin q.K => idealTrace s f z j.val
        have hX : Measurable X := Measurable.of_eval (fun j => freyaObservedPairMeas q f τ O hservice j.val)
        have hY : Measurable Y := measurable_of_countable _
        have hpaths : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        have hzero : P.map (fun z => observedPair q O z.1 z.2 0)=
            Q.map (fun z => idealTrace s f z 0) := by
          have he : (fun z => observedPair q O z.1 z.2 0)=ᵐ[P]
              (fun _ => (q.x0,gradient (objective f) q.x0)) := by
            filter_upwards [hpaths] with z hz
            exact freyaObservedInitial q hm hn hS hK f hf τ O z.1 z.2 hz
          rw [Measure.map_congr he]
          change P.map (fun _ => (q.x0,gradient (objective f) q.x0))=
            Q.map (fun _ => (q.x0,gradient (objective f) q.x0))
          simp (config := { iota := false }) only [Measure.map_const,measure_univ,one_smul]
        have hpath : HasLaw X (Q.map Y) P :=
          freyaSPObserved_prefix_law q hm hn hS hK hρ hρone f hf τ O hservice hind
            (fun b => freyaObservedPairMeas q f τ O hservice b) hzero
        have hjoint : HasLaw (fun z => (X z,outputIndex z.1))
            (Q.map (fun z => (Y z,z.2.2))) P := by
          refine ⟨(hX.prodMk (measurable_fst.snd.snd)).aemeasurable,?_⟩
          rw [freyaActualSelectorProduct q f τ O hservice,freyaIdealSelectorProduct s f,hpath.map_eq]
        refine ⟨hjoint,?_⟩
        let index : Fin (max 1 q.K) → Fin q.K := fun i => ⟨i.val,by
          have hi := i.isLt
          simpa (config := { iota := false }) only [max_eq_right (show 1≤q.K by omega)] using hi⟩
        let pick : (Fin q.K → Space q.d × Space q.d) × Fin (max 1 q.K) → Space q.d :=
          fun z => (z.1 (index z.2)).1
        have hpick : Measurable pick :=
          (freyaMeasurableSelect (fun z : (Fin q.K → Space q.d × Space q.d) × Fin (max 1 q.K) => z.2)
            measurable_snd (fun i z => z.1 (index i))
            (fun i => (measurable_pi_apply (index i)).comp measurable_fst)).fst
        have hl : HasLaw pick (Q.map (LongTails.Algorithms.FreyaSerial.idealOutput s f))
            (Q.map (fun z => (Y z,z.2.2))) := by
          refine ⟨hpick.aemeasurable,?_⟩
          rw [Measure.map_map hpick (hY.prodMk measurable_snd.snd)]
          rfl
        apply (hl.comp hjoint).congr
        filter_upwards [hpaths] with z hz
        exact freyaObservedOutput q hm hn hS hK f τ O z.1 z.2 hz N hN
      exact freyaScheduledLaw q hm hn hS hK hρ hρone f hf τ O hservice hind N hN


theorem selected_gradient_integrable (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hL : 0 ≤ Lminus) (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
    (N : ℕ) (hN : eventLimit q ≤ N) :
    Integrable (fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
      ‖gradient (objective f) (execute O (factory q) (fun _ => N) z.1 z.2).1‖ ^ 2)
      (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a))) := by
  open LongTails.Algorithms.FreyaSerial in
    classical
    have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (b : β) (f : α → β) (hf : Measurable f) :
        Measurable (fun o : Option α => o.elim b f) := by
      have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
        apply Measurable.of_comap_le
        delta instMeasurableSpaceOption
        apply le_of_eq
        congr 1
        funext o
        cases o <;> rfl
      have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
      convert hs.comp he using 1
      funext o
      cases o <;> rfl
    have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
        MeasurableSingletonClass (Option α) := by
      constructor
      intro x
      let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
      have he : {x}=encode ⁻¹' {encode x} := by
        ext y
        cases x <;> cases y <;> simp (config := { iota := false }) [encode]
      have hsingleton : MeasurableSet {encode x} := by
        rw [measurableSet_sum_iff]
        cases x <;> constructor <;> simp (config := { iota := false }) [encode]
        · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
          rw [he]
          exact MeasurableSet.empty
        · rename_i b
          have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
          rw [he]
          exact measurableSet_singleton _
      rw [he]
      exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
        hsingleton
    let : MeasurableSingletonClass (Option (Fin (serialInput q).m)) := freyaOptionSingleton
    have hlip : LipschitzWith ⟨Lminus,hL⟩ (gradient (objective f)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change ‖gradient (objective f) x-gradient (objective f) y‖≤Lminus*‖x-y‖
      exact hreg.smooth x y
    have hG : Continuous (fun x : Space q.d => ‖gradient (objective f) x‖^2) :=
      hlip.continuous.norm.pow 2
    have hout : Measurable (idealOutput (serialInput q) f) := measurable_of_countable _
    have hi : Integrable (fun x : Space q.d => ‖gradient (objective f) x‖^2)
        ((canonicalLaw (serialInput q) : Measure (CanonicalSeed (serialInput q))).map
          (idealOutput (serialInput q) f)) :=
      (integrable_map_measure hG.aestronglyMeasurable hout.aemeasurable).mpr Integrable.of_finite
    exact (scheduled_page_law q hm hn hS hK hρ hρone f hreg.differentiable τ O hservice hind N hN).2.integrable_comp hi


theorem cost_composition (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (N : ℕ) (hN : eventLimit q ≤ N) :
    let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
    let elapsed := fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
      ((execute O (factory q) (fun _ => N) z.1 z.2).2 : ℝ≥0∞)
    Measurable elapsed ∧
      (∫⁻ z, elapsed z ∂P) ≤ multisetTimeBound τ q.m + (rounds q : ℝ≥0∞) *
        (ENNReal.ofReal q.ρ * multisetTimeBound τ q.m +
          ENNReal.ofReal (1 - q.ρ) * (4 * equilibriumTime τ q.S)) ∧
      (largeSample q.m q.n →
        (∫⁻ z, elapsed z ∂P) ≤ 5 * equilibriumTime τ q.m + (rounds q : ℝ≥0∞) *
          (ENNReal.ofReal q.ρ * (5 * equilibriumTime τ q.m) +
            ENNReal.ofReal (1 - q.ρ) * (4 * equilibriumTime τ q.S))) := by
  exact
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 4096 in
    open scoped BigOperators ENNReal NNReal in
    open MeasureTheory ProbabilityTheory OracleTemplate in
    open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
    open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
    open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    open LongTails.Proofs.FreyaConditionalCosts LongTails.Proofs.FreyaExecution in
    by
      classical
      have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
        clear * - q s

        delta advance
        split <;> rfl
      have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
          (update q s reply).seed = s.seed := by
        clear * - q s reply freyaPageAdvanceSeed

        delta update
        cases hs : s.phase with
        | halted => rfl
        | full first c =>
          dsimp only
          split
          · exact freyaPageAdvanceSeed q _
          · rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPageAdvanceSeed q _
          · rfl
      have freyaPageTraceSeed (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
          (trace q O seed ω k).seed = seed := by
        clear * - q O seed ω k freyaPageUpdateSeed

        induction k with
        | zero => rfl
        | succ k ih =>
          change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
          rw [freyaPageUpdateSeed,ih]
      have freyaPageAdvanceIteration (q : Raw) (s : State q) :
          (advance q s).iteration = s.iteration ∨ (advance q s).iteration = s.iteration+1 := by
        clear * - q s

        delta advance
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      have freyaPageUpdateIteration (q : Raw) (s : State q) (reply : Reply q.d q.n) :
          (update q s reply).iteration = s.iteration ∨
            (update q s reply).iteration = s.iteration+1 := by
        clear * - q s reply freyaPageAdvanceIteration

        delta update
        cases hs : s.phase with
        | halted => exact Or.inl rfl
        | full first c =>
          dsimp only
          split
          · exact freyaPageAdvanceIteration q _
          · exact Or.inl rfl
        | difference c =>
          dsimp only
          split
          · exact freyaPageAdvanceIteration q _
          · exact Or.inl rfl
      have freyaPageIterationMonotone (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          Monotone (fun k => (trace q O seed ω k).iteration) := by
        clear * - q O seed ω freyaPageUpdateIteration

        apply monotone_nat_of_le_succ
        intro k
        have h := freyaPageUpdateIteration q (trace q O seed ω k)
          (replyAt q O seed ω k (query q (trace q O seed ω k)))
        change (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration ∨
          (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration+1 at h
        omega
      have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
          (h : (List.range N).find? p = some k) :
          k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
        clear * - N p k h

        obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
        simp (config := { iota := false }) only [List.length_range,List.getElem_range] at hi hik hprev
        subst i
        refine ⟨hi,hp,?_⟩
        intro r hr htrue
        have hh := hprev r hr
        rw [htrue] at hh
        contradiction
      have freyaPageBatchStartFacts (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
          (h : batchStartCall q O seed ω batch = some call) :
          call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
            active (trace q O seed ω call) = true ∧
            ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
        clear * - q O seed ω batch call h freyaPageFirstMatch

        delta batchStartCall at h
        obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
        obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
        refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
        intro r hr hh
        apply hprev r hr
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
      let freyaClockConsistent {q : Raw} (s : State q) : Prop :=
        s.phase.casesOn (fun _ c => s.clock=c.clock) (fun c => s.clock=c.clock) True
      have freyaAdvanceClock (q : Raw) (s : State q) : (advance q s).clock=s.clock := by
        clear * - q s

        delta advance
        split
        · rfl
        · rfl
      have freyaAdvanceClockConsistent (q : Raw) (s : State q) : freyaClockConsistent (advance q s) := by
        clear * - q s freyaClockConsistent

        delta advance
        split
        · exact True.intro
        · dsimp only [freyaClockConsistent]
          split <;> rfl
      have freyaInitialClockConsistent (q : Raw) (seed : Seed q.K) : freyaClockConsistent (initial q seed) := by
        clear * - q seed freyaClockConsistent

        dsimp only [freyaClockConsistent,initial]
        split
        · exact True.intro
        · rfl
      have freyaUpdateClockConsistent (q : Raw) (s : State q) (r : Reply q.d q.n)
          (h : freyaClockConsistent s) : freyaClockConsistent (update q s r) := by
        clear * - q s r h freyaClockConsistent freyaAdvanceClockConsistent

        delta update
        cases hs : s.phase with
        | halted => exact h
        | full first c =>
          dsimp only
          split
          · exact freyaAdvanceClockConsistent q _
          · rfl
        | difference c =>
          dsimp only
          split
          · exact freyaAdvanceClockConsistent q _
          · rfl
      have freyaTraceClockConsistent (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
          freyaClockConsistent (trace q O seed ω k) := by
        clear * - q O seed ω k freyaClockConsistent freyaInitialClockConsistent freyaUpdateClockConsistent

        induction k with
        | zero => exact freyaInitialClockConsistent q seed
        | succ k ih => exact freyaUpdateClockConsistent q _ _ ih
      have freyaFullClockMono {d m n : ℕ} (s : FullState d m n) (r : Reply d n) :
          s.clock≤(fullUpdate s r).clock := by
        clear * - d m n s r

        classical
        dsimp only [fullUpdate]
        split
        · exact le_rfl
        · cases r with
          | none => exact le_rfl
          | some r =>
            rcases r with ⟨i,k,t,v⟩
            dsimp only
            cases s.pending i with
            | none => exact le_rfl
            | some job =>
              dsimp only
              split
              · rename_i h
                exact h.2
              · exact le_rfl
      have freyaDifferenceClockMono {d m n : ℕ} (s : DifferenceState d m n) (r : Reply d n) :
          s.clock≤(differenceUpdate s r).clock := by
        clear * - d m n s r

        classical
        dsimp only [differenceUpdate]
        split
        · exact le_rfl
        · cases r with
          | none => exact le_rfl
          | some r =>
            rcases r with ⟨i,k,t,v⟩
            dsimp only
            cases s.pending i with
            | none => exact le_rfl
            | some job =>
              dsimp only
              split
              · rename_i h
                exact h.2
              · exact le_rfl
      have freyaUpdateClockMono (q : Raw) (s : State q) (r : Reply q.d q.n)
          (hs : freyaClockConsistent s) : s.clock≤(update q s r).clock := by
        clear * - q s r hs freyaClockConsistent freyaAdvanceClock freyaFullClockMono freyaDifferenceClockMono

        dsimp only [update]
        cases hp : s.phase with
        | halted => exact le_rfl
        | full first c =>
          have he : s.clock=c.clock := by simpa (config := { iota := false }) only [freyaClockConsistent,hp] using hs
          dsimp only
          split
          · rw [freyaAdvanceClock]
            exact he ▸ freyaFullClockMono c r
          · exact he ▸ freyaFullClockMono c r
        | difference c =>
          have he : s.clock=c.clock := by simpa (config := { iota := false }) only [freyaClockConsistent,hp] using hs
          dsimp only
          split
          · rw [freyaAdvanceClock]
            exact he ▸ freyaDifferenceClockMono c r
          · exact he ▸ freyaDifferenceClockMono c r
      let freyaHistoryView (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (batch : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :=
        (invocation q O z.1 z.2 batch, fun k : ℕ =>
          if k < (batchStartCall q O z.1 z.2 batch).getD 0 then
            let s := trace q O z.1 z.2 k
            let reply := replyAt q O z.1 z.2 k (query q s)
            some (query q s,reply,collectorPendingAfter q s reply)
          else none)
      have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
          (b : β) (f : α → β) (hf : Measurable f) :
          Measurable (fun o : Option α => o.elim b f) := by
        clear * - α β b f hf

        have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
          apply Measurable.of_comap_le
          delta instMeasurableSpaceOption
          apply le_of_eq
          congr 1
          funext o
          cases o <;> rfl
        have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
        convert hs.comp he using 1
        funext o
        cases o <;> rfl
      have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
          MeasurableSingletonClass (Option α) := by
        clear * - α freyaDevelopmentOptionElimMeas

        constructor
        intro x
        let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
        have he : {x}=encode ⁻¹' {encode x} := by
          ext y
          cases x <;> cases y <;> simp (config := { iota := false }) [encode]
        have hsingleton : MeasurableSet {encode x} := by
          rw [measurableSet_sum_iff]
          cases x <;> constructor <;> simp (config := { iota := false }) [encode]
          · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
            rw [he]
            exact MeasurableSet.empty
          · rename_i b
            have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
            rw [he]
            exact measurableSet_singleton _
        rw [he]
        exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
          hsingleton
      have freyaOptionSomeMeas {α : Type} [MeasurableSpace α] :
          Measurable (some : α → Option α) := by
        clear * - α

        delta instMeasurableSpaceOption
        rw [measurable_comap_iff]
        exact measurable_inr
      have freyaLabelAtMeas (m : ℕ) : Measurable (fun row : ChoiceRow => labelAt row m) := by
        clear * - m freyaOptionSingleton

        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        by_cases hm : 0<m
        · let g : Fin (m-1+1) → Option (Fin m) := fun i => some ⟨i.val,by have := i.isLt; omega⟩
          have hg : Measurable g := measurable_of_countable g
          have he : Measurable (fun row : ChoiceRow => row (m-1)) := measurable_pi_apply (m-1)
          convert hg.comp he using 1
          funext row
          delta labelAt
          rw [dite_eq_left hm]
          rfl
        · delta labelAt
          simp (config := { iota := false }) only [hm,dite_false]
          exact measurable_const
      have freyaPageInvocationHistoryMeas (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
          Measurable[historyBefore q O batch]
            (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => invocation q O z.1 z.2 batch) := by
        clear * - q O batch freyaHistoryView

        exact measurable_fst.comp (show Measurable[historyBefore q O batch]
          (freyaHistoryView q O batch) from Measurable.of_comap_le le_rfl)
      have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
          (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
          Measurable (fun z => f (g z) z) :=
        (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
          (measurable_id.prodMk hg)
      have freyaOptionParamMeas {Ω α β : Type} [MeasurableSpace Ω]
          [MeasurableSpace α] [MeasurableSpace β]
          (o : Ω → Option α) (ho : Measurable o) (b : Ω → β) (hb : Measurable b)
          (f : Ω × α → β) (hf : Measurable f) :
          Measurable (fun z => (o z).elim (b z) (fun a => f (z,a))) := by
        clear * - Ω α β o ho b hb f hf freyaDevelopmentOptionElimMeas

        have he := (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr).comp ho
        have hs := ((hb.comp measurable_fst).sumElim hf).comp
          ((MeasurableEquiv.prodSumDistrib Ω Unit α).measurable.comp (measurable_id.prodMk he))
        convert hs using 1
        funext z
        dsimp only [Function.comp_def,id_eq]
        cases o z <;> rfl'
      let freyaListMeasSpace (α : Type) : MeasurableSpace (List α) := ⊤
      let freyaFullCode {d m n : ℕ} (s : FullState d m n) :=
        (s.original,s.remaining,s.point,s.sum,s.pending,s.clock,s.rows,s.nextID)
      let freyaDifferenceCode {d m n : ℕ} (s : DifferenceState d m n) :=
        (s.target,s.count,s.x,s.y,s.sum,s.pending,s.clock,s.rows,s.nextID)
      let freyaFullMeasSpace (d m n : ℕ) : MeasurableSpace (FullState d m n) :=
        MeasurableSpace.comap freyaFullCode inferInstance
      let freyaDifferenceMeasSpace (d m n : ℕ) : MeasurableSpace (DifferenceState d m n) :=
        MeasurableSpace.comap freyaDifferenceCode inferInstance
      have freyaFullCodeMeas {d m n : ℕ} : Measurable (@freyaFullCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaDifferenceCodeMeas {d m n : ℕ} : Measurable (@freyaDifferenceCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaJobCodeMeas {d m : ℕ} :
          Measurable (fun j : Job d m => (j.component,j.kind,j.started,j.id)) :=
        Measurable.of_comap_le le_rfl
      have freyaDispatchMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (kind : Ω → JobKind d) (clock : Ω → ℝ≥0) (id : Ω → ℕ)
          (label : Ω → Option (Fin m)) (hk : Measurable kind) (hc : Measurable clock)
          (hi : Measurable id) (hl : Measurable label) :
          Measurable (fun z => dispatch (kind z) (clock z) (id z) (label z)) := by
        clear * - Ω d m kind clock id label hk hc hi hl freyaOptionSomeMeas freyaOptionParamMeas

        have hb : Measurable (fun z : Ω × Fin m =>
            some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) := by
          apply freyaOptionSomeMeas.comp
          change Measurable[_,MeasurableSpace.comap
            (fun j : Job d m => (j.component,j.kind,j.started,j.id)) inferInstance]
            (fun z : Ω × Fin m => (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m))
          rw [measurable_comap_iff]
          exact (measurable_snd.prodMk ((hk.comp measurable_fst).prodMk
            ((hc.comp measurable_fst).prodMk (hi.comp measurable_fst))))
        have h := freyaOptionParamMeas label hl (fun _ => none) measurable_const
          (fun z : Ω × Fin m => some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) hb
        convert h using 1
        funext z
        delta dispatch
        cases label z <;> rfl
      have freyaSelectedLabelFixedMeas {m : ℕ} (labels : List (Fin m)) (rem : List ℕ) :
          Measurable (fun row : ChoiceRow => selectedLabel labels rem row) := by
        clear * - m labels rem freyaOptionSingleton

        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        cases rem with
        | nil => exact measurable_const
        | cons a rem =>
          let g := fun i : Fin (rem.length+1) => labels[(a::rem).get i]?
          have he : Measurable (fun row : ChoiceRow => row rem.length) := measurable_pi_apply rem.length
          have h := (measurable_of_countable g).comp he
          convert h using 1
          funext row
          delta selectedLabel chooseRemaining
          simp (config := { iota := false }) only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,dite_false,
            Option.bind_some]
          rfl
      have freyaFullInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (n : ℕ) (labels : List (Fin m)) (x : Ω → Space d) (clock : Ω → ℝ≥0)
          (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
          (hx : Measurable x) (hc : Measurable clock) (hr : Measurable rows) (hf : Measurable first) :
          Measurable (fun z => fullInitial n labels (x z) (clock z) (rows z) (first z)) := by
        clear * - Ω d m n labels x clock rows first hx hc hr hf freyaMeasurableSelect freyaFullCode freyaDispatchMeas freyaSelectedLabelFixedMeas

        have hp (i : Fin n) : Measurable (fun z =>
            dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
              (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))) :=
          freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hc (hf.add_const i.val)
            ((freyaSelectedLabelFixedMeas labels (List.range labels.length)).comp
              (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
        change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
        rw [measurable_comap_iff]
        change Measurable (fun z => (labels,List.range labels.length,x z,(0 : Space d),
          (fun i : Fin n => dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
            (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))),
          clock z,rows z,first z+n))
        exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk
          (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n)))))))
      have freyaDifferenceInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
          (n S : ℕ) (x y : Ω → Space d) (clock : Ω → ℝ≥0)
          (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
          (hx : Measurable x) (hy : Measurable y) (hc : Measurable clock)
          (hr : Measurable rows) (hf : Measurable first) :
          Measurable (fun z => differenceInitial (m:=m) n S (x z) (y z) (clock z) (rows z) (first z)) := by
        clear * - Ω d m n S x y clock rows first hx hy hc hr hf freyaLabelAtMeas freyaMeasurableSelect freyaDifferenceCode freyaDispatchMeas

        have hp (i : Fin n) : Measurable (fun z => if S=0 then none else
            dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
              (labelAt (rows z (first z+i.val)) m)) := by
          by_cases hS : S=0
          · simp (config := { iota := false }) only [hS,ite_true]; exact measurable_const
          · simp (config := { iota := false }) only [hS,ite_false]
            exact freyaDispatchMeas _ _ _ _ (measurable_inr.comp (hx.prodMk hy)) hc (hf.add_const i.val)
              ((freyaLabelAtMeas m).comp
                (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
        change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
        rw [measurable_comap_iff]
        change Measurable (fun z => (S,(0 : ℕ),x z,y z,(0 : Space d),
          (fun i : Fin n => if S=0 then none else dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
            (labelAt (rows z (first z+i.val)) m)),clock z,rows z,first z+n))
        exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk (hy.prodMk
          (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n))))))))
      let freyaFullReplyJob {d m n : ℕ} (s : FullState d m n)
          (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : FullState d m n := by
        classical
        exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
          let found := s.remaining.find? fun a => decide (s.original[a]?=some job.component)
          let remaining := found.elim s.remaining (fun a => s.remaining.erase a)
          let sum := if found.isSome then s.sum+r.2.2.2 else s.sum
          let next := dispatch (Sum.inl s.point) r.2.2.1 s.nextID
            (selectedLabel s.original remaining (s.rows s.nextID))
          {s with
            remaining:=remaining
            sum:=sum
            pending:=Function.update s.pending r.1 next
            clock:=r.2.2.1
            nextID:=s.nextID+1}
        else s
      have freyaFullReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
          (s : Ω → FullState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
          (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
          Measurable (fun z => freyaFullReplyJob (s z) (r z) (job z)) := by
        clear * - Ω d m n s r job hs hr hj freyaOptionSingleton freyaMeasurableSelect freyaFullCode freyaFullCodeMeas freyaJobCodeMeas freyaDispatchMeas freyaSelectedLabelFixedMeas freyaFullReplyJob

        classical
        let : MeasurableSingletonClass (Option ℕ) := freyaOptionSingleton
        let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
        have hcode := freyaFullCodeMeas.comp hs
        have hjcode := freyaJobCodeMeas.comp hj
        have ho : Measurable (fun z => (s z).original) := hcode.fst
        have hrem : Measurable (fun z => (s z).remaining) := hcode.snd.fst
        have hx : Measurable (fun z => (s z).point) := hcode.snd.snd.fst
        have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.fst
        have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.fst
        have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.fst
        have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd
        let found := fun z => (s z).remaining.find? fun a => decide ((s z).original[a]?=some (job z).component)
        let rem := fun z => (found z).elim (s z).remaining (fun a => (s z).remaining.erase a)
        let sum := fun z => if (found z).isSome then (s z).sum+(r z).2.2.2 else (s z).sum
        let next := fun z => dispatch (Sum.inl (s z).point) (r z).2.2.1 (s z).nextID
          (selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID))
        have hf : Measurable found :=
          (measurable_of_countable (fun p : List (Fin m) × List ℕ × Fin m =>
            p.2.1.find? fun a => decide (p.1[a]?=some p.2.2))).comp (ho.prodMk (hrem.prodMk hjcode.fst))
        have hrem' : Measurable rem :=
          (measurable_of_countable (fun p : List ℕ × Option ℕ => p.2.elim p.1 (fun a => p.1.erase a))).comp
            (hrem.prodMk hf)
        have hsum' : Measurable sum := (hsum.add hr.snd.snd.snd).ite
          (((measurable_of_countable (fun o : Option ℕ => o.isSome)).comp hf) (measurableSet_singleton true)) hsum
        have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
          freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
        have hlabel : Measurable (fun z => selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID)) :=
          freyaMeasurableSelect _ (ho.prodMk hrem') _
            (fun p => (freyaSelectedLabelFixedMeas p.1 p.2).comp hrow)
        have hnext : Measurable next := freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hr.snd.snd.fst hid hlabel
        have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
          freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
        have hnew : Measurable (fun z => {s z with
            remaining:=rem z
            sum:=sum z
            pending:=Function.update (s z).pending (r z).1 (next z)
            clock:=(r z).2.2.1
            nextID:=(s z).nextID+1}) := by
          change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
          rw [measurable_comap_iff]
          exact ho.prodMk (hrem'.prodMk (hx.prodMk (hsum'.prodMk
            (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1)))))))
        exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
          (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
      have freyaFullUpdateMeas {d m n : ℕ} :
          Measurable (fun z : FullState d m n × Reply d n => fullUpdate z.1 z.2) := by
        clear * - d m n freyaMeasurableSelect freyaOptionParamMeas freyaFullCodeMeas freyaFullReplyJob freyaFullReplyJobMeas

        classical
        have hc := freyaFullCodeMeas (d:=d) (m:=m) (n:=n)
        have hsome : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            ((z.1).pending z.2.1).elim z.1 (fun job => freyaFullReplyJob z.1 z.2 job)) := by
          have hp : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
              z.1.pending z.2.1) :=
            freyaMeasurableSelect _ measurable_snd.fst _
              (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.fst.comp measurable_fst))
          exact freyaOptionParamMeas _ hp _ measurable_fst _
            (freyaFullReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
        have hoption : Measurable (fun z : FullState d m n × Reply d n =>
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
          freyaOptionParamMeas _ measurable_snd _ measurable_fst _
            (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
        have he : MeasurableSet {z : FullState d m n × Reply d n | z.1.remaining.isEmpty=true} :=
          ((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp
            (hc.snd.fst.comp measurable_fst)) (measurableSet_singleton true)
        have hh : Measurable (fun z : FullState d m n × Reply d n =>
            if z.1.remaining.isEmpty then z.1 else
              z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
          measurable_fst.ite he hoption
        convert hh using 1
        funext z
        delta fullUpdate
        dsimp only
        by_cases hempty : z.1.remaining.isEmpty=true
        · simp (config := { iota := false }) only [ite_eq_left hempty]
        · simp (config := { iota := false }) only [ite_eq_right hempty]
          cases hr : z.2 with
          | none => rfl
          | some r =>
            obtain ⟨i,id,t,value⟩ := r
            dsimp only [Option.elim_some]
            cases hp : z.1.pending i <;> rfl
      let freyaDifferenceReplyJob {d m n : ℕ} (s : DifferenceState d m n)
          (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : DifferenceState d m n := by
        classical
        exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
          let next := dispatch (Sum.inr (s.x,s.y)) r.2.2.1 s.nextID (labelAt (s.rows s.nextID) m)
          {s with
            count:=s.count+1
            sum:=s.sum+r.2.2.2
            pending:=Function.update s.pending r.1 next
            clock:=r.2.2.1
            nextID:=s.nextID+1}
        else s
      have freyaDifferenceReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
          (s : Ω → DifferenceState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
          (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
          Measurable (fun z => freyaDifferenceReplyJob (s z) (r z) (job z)) := by
        clear * - Ω d m n s r job hs hr hj freyaLabelAtMeas freyaMeasurableSelect freyaDifferenceCode freyaDifferenceCodeMeas freyaJobCodeMeas freyaDispatchMeas freyaDifferenceReplyJob

        classical
        have hcode := freyaDifferenceCodeMeas.comp hs
        have hjcode := freyaJobCodeMeas.comp hj
        have ht : Measurable (fun z => (s z).target) := hcode.fst
        have hcount : Measurable (fun z => (s z).count) := hcode.snd.fst
        have hx : Measurable (fun z => (s z).x) := hcode.snd.snd.fst
        have hy : Measurable (fun z => (s z).y) := hcode.snd.snd.snd.fst
        have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.snd.fst
        have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.snd.fst
        have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.snd.fst
        have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd.snd
        let next := fun z => dispatch (Sum.inr ((s z).x,(s z).y)) (r z).2.2.1 (s z).nextID
          (labelAt ((s z).rows (s z).nextID) m)
        have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
          freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
        have hnext : Measurable next := freyaDispatchMeas _ _ _ _
          (measurable_inr.comp (hx.prodMk hy)) hr.snd.snd.fst hid ((freyaLabelAtMeas m).comp hrow)
        have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
          freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
        have hnew : Measurable (fun z => {s z with
            count:=(s z).count+1
            sum:=(s z).sum+(r z).2.2.2
            pending:=Function.update (s z).pending (r z).1 (next z)
            clock:=(r z).2.2.1
            nextID:=(s z).nextID+1}) := by
          change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
          rw [measurable_comap_iff]
          exact ht.prodMk ((hcount.add_const 1).prodMk (hx.prodMk (hy.prodMk ((hsum.add hr.snd.snd.snd).prodMk
            (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1))))))))
        exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
          (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
      have freyaDifferenceUpdateMeas {d m n : ℕ} :
          Measurable (fun z : DifferenceState d m n × Reply d n => differenceUpdate z.1 z.2) := by
        clear * - d m n freyaMeasurableSelect freyaOptionParamMeas freyaDifferenceCodeMeas freyaDifferenceReplyJob freyaDifferenceReplyJobMeas

        classical
        have hc := freyaDifferenceCodeMeas (d:=d) (m:=m) (n:=n)
        have hsome : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            ((z.1).pending z.2.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 z.2 job)) := by
          have hp : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
              z.1.pending z.2.1) :=
            freyaMeasurableSelect _ measurable_snd.fst _
              (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.snd.fst.comp measurable_fst))
          exact freyaOptionParamMeas _ hp _ measurable_fst _
            (freyaDifferenceReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
        have hoption : Measurable (fun z : DifferenceState d m n × Reply d n =>
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
          freyaOptionParamMeas _ measurable_snd _ measurable_fst _
            (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
        have he : MeasurableSet {z : DifferenceState d m n × Reply d n | z.1.target≤z.1.count} :=
          measurableSet_le (hc.fst.comp measurable_fst) (hc.snd.fst.comp measurable_fst)
        have hh : Measurable (fun z : DifferenceState d m n × Reply d n =>
            if z.1.target≤z.1.count then z.1 else
              z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
          measurable_fst.ite he hoption
        convert hh using 1
        funext z
        delta differenceUpdate
        dsimp only
        by_cases hstop : z.1.target≤z.1.count
        · simp (config := { iota := false }) only [ite_eq_left hstop]
        · simp (config := { iota := false }) only [ite_eq_right hstop]
          cases hr : z.2 with
          | none => rfl
          | some r =>
            obtain ⟨i,id,t,value⟩ := r
            dsimp only [Option.elim_some]
            cases hp : z.1.pending i <;> rfl
      let freyaPhaseCode {d m n : ℕ} (p : Phase d m n) :
          Unit ⊕ ((Bool × FullState d m n) ⊕ DifferenceState d m n) :=
        p.casesOn (fun b c => Sum.inr (Sum.inl (b,c))) (fun c => Sum.inr (Sum.inr c)) (Sum.inl ())
      let freyaPhaseMeasSpace (d m n : ℕ) : MeasurableSpace (Phase d m n) :=
        MeasurableSpace.comap freyaPhaseCode inferInstance
      let freyaStateCode {q : Raw} (s : State q) :=
        (s.seed,s.iteration,s.x,s.g,s.selected,s.clock,s.nextID,s.phase)
      let freyaStateMeasSpace (q : Raw) : MeasurableSpace (State q) :=
        MeasurableSpace.comap freyaStateCode inferInstance
      have freyaPhaseCodeMeas {d m n : ℕ} : Measurable (@freyaPhaseCode d m n) :=
        Measurable.of_comap_le le_rfl
      have freyaStateCodeMeas (q : Raw) : Measurable (@freyaStateCode q) :=
        Measurable.of_comap_le le_rfl
      have freyaPhaseFullMeas {d m n : ℕ} :
          Measurable (fun z : Bool × FullState d m n => Phase.full z.1 z.2) := by
        clear * - d m n freyaPhaseCode

        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inl
      have freyaPhaseDifferenceMeas {d m n : ℕ} :
          Measurable (Phase.difference : DifferenceState d m n → Phase d m n) := by
        clear * - d m n freyaPhaseCode

        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inr
      have freyaPhaseParamMeas {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {d m n : ℕ}
          (p : Ω → Phase d m n) (hp : Measurable p) (b : Ω → β) (hb : Measurable b)
          (full : Ω × (Bool × FullState d m n) → β) (hfull : Measurable full)
          (diff : Ω × DifferenceState d m n → β) (hdiff : Measurable diff) :
          Measurable (fun z => (p z).casesOn (motive := fun _ => β) (fun first c => full (z,first,c))
            (fun c => diff (z,c)) (b z)) := by
        clear * - Ω β d m n p hp b hb full hfull diff hdiff freyaPhaseCodeMeas

        have hi := (hfull.sumElim hdiff).comp
          (MeasurableEquiv.prodSumDistrib Ω (Bool × FullState d m n) (DifferenceState d m n)).measurable
        have ho := ((hb.comp measurable_fst).sumElim hi).comp
          (MeasurableEquiv.prodSumDistrib Ω Unit ((Bool × FullState d m n) ⊕ DifferenceState d m n)).measurable
        have h := ho.comp (measurable_id.prodMk (freyaPhaseCodeMeas.comp hp))
        convert h using 1
        funext z
        dsimp only [Function.comp_def,id_eq]
        cases p z <;> rfl'
      have freyaStateConstructMeas {Ω : Type} [MeasurableSpace Ω] (q : Raw)
          (seed : Ω → Seed q.K) (it : Ω → ℕ) (x g selected : Ω → Space q.d)
          (clock : Ω → ℝ≥0) (id : Ω → ℕ) (phase : Ω → Phase q.d q.m q.n)
          (hseed : Measurable seed) (hit : Measurable it) (hx : Measurable x) (hg : Measurable g)
          (hselected : Measurable selected) (hc : Measurable clock) (hid : Measurable id) (hp : Measurable phase) :
          Measurable (fun z => (⟨seed z,it z,x z,g z,selected z,clock z,id z,phase z⟩ : State q)) := by
        clear * - Ω q seed it x g selected clock id phase hseed hit hx hg hselected hc hid hp freyaStateCode

        change Measurable[_,MeasurableSpace.comap freyaStateCode inferInstance] _
        rw [measurable_comap_iff]
        exact hseed.prodMk (hit.prodMk (hx.prodMk (hg.prodMk (hselected.prodMk (hc.prodMk (hid.prodMk hp))))))
      have freyaPageInitialMeas (q : Raw) : Measurable (initial q) := by
        clear * - q freyaFullInitialMeas freyaPhaseFullMeas freyaStateConstructMeas

        have hp : Measurable (fun seed : Seed q.K =>
            if q.m=0 ∨ q.n=0 ∨ q.K=0 then (Phase.halted : Phase q.d q.m q.n) else
              Phase.full true (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))) := by
          by_cases hbad : q.m=0 ∨ q.n=0 ∨ q.K=0
          · simp (config := { iota := false }) only [hbad,ite_true]; exact measurable_const
          · simp (config := { iota := false }) only [hbad,ite_false]
            exact freyaPhaseFullMeas.comp (measurable_const.prodMk
              (freyaFullInitialMeas q.n (List.ofFn id) (fun _ => q.x0) (fun _ => 0)
                (fun seed : Seed q.K => seed.1 0) (fun _ => 0) measurable_const measurable_const
                ((measurable_pi_apply 0).comp measurable_fst) measurable_const))
        exact freyaStateConstructMeas q id (fun _ => 0) (fun _ => q.x0) (fun _ => 0) (fun _ => q.x0)
          (fun _ => 0) (fun _ => q.n) _ measurable_id measurable_const measurable_const measurable_const
            measurable_const measurable_const measurable_const hp
      have freyaPageAdvanceMeas (q : Raw) : Measurable (advance q) := by
        clear * - q freyaMeasurableSelect freyaFullInitialMeas freyaDifferenceInitialMeas freyaStateCodeMeas freyaPhaseFullMeas freyaPhaseDifferenceMeas freyaStateConstructMeas

        classical
        have hc := freyaStateCodeMeas q
        have hseed : Measurable (fun s : State q => s.seed) := hc.fst
        have hit : Measurable (fun s : State q => s.iteration) := hc.snd.fst
        have hx : Measurable (fun s : State q => s.x) := hc.snd.snd.fst
        have hg : Measurable (fun s : State q => s.g) := hc.snd.snd.snd.fst
        have hsel : Measurable (fun s : State q => s.selected) := hc.snd.snd.snd.snd.fst
        have hclock : Measurable (fun s : State q => s.clock) := hc.snd.snd.snd.snd.snd.fst
        have hid : Measurable (fun s : State q => s.nextID) := hc.snd.snd.snd.snd.snd.snd.fst
        let x := fun s : State q => s.x-q.η • s.g
        let batch := fun s : State q => s.iteration+1
        have hnewx : Measurable x := hx.sub (hg.const_smul q.η)
        have hbatch : Measurable batch := hit.add_const 1
        have hrows : Measurable (fun s : State q => s.seed.1 (batch s)) :=
          freyaMeasurableSelect _ hbatch _ (fun k => (measurable_pi_apply k).comp hseed.fst)
        have hrefresh : Measurable (fun s : State q => refreshAt s.seed s.iteration) :=
          freyaMeasurableSelect _ hit _ (fun k => (measurable_pi_apply k).comp hseed.snd.fst)
        have hfull := (freyaPhaseFullMeas (m:=q.m)).comp ((measurable_const (a:=false)).prodMk
          (freyaFullInitialMeas (m:=q.m) q.n (List.ofFn id) x (fun s => s.clock) _ (fun s => s.nextID)
            hnewx hclock hrows hid))
        have hdiff := freyaPhaseDifferenceMeas.comp
          (freyaDifferenceInitialMeas (m:=q.m) q.n q.S x (fun s => s.x) (fun s => s.clock) _
            (fun s => s.nextID) hnewx hx hclock hrows hid)
        have hphase : Measurable (fun s : State q => if refreshAt s.seed s.iteration then
            Phase.full false (fullInitial q.n (List.ofFn id) (x s) s.clock (s.seed.1 (batch s)) s.nextID)
          else Phase.difference (differenceInitial q.n q.S (x s) s.x s.clock (s.seed.1 (batch s)) s.nextID)) :=
          hfull.ite (hrefresh (measurableSet_singleton true)) hdiff
        have hindex : Measurable (fun s : State q => (outputIndex s.seed).val) :=
          (measurable_of_countable (fun i : Fin (max 1 q.K) => i.val)).comp hseed.snd.snd
        have hselected : Measurable (fun s : State q =>
            if (outputIndex s.seed).val=batch s then x s else s.selected) :=
          hnewx.ite (measurableSet_eq_fun hindex hbatch) hsel
        have hnext := freyaStateConstructMeas q _ batch x _ _ _ _ _
          hseed hbatch hnewx hg hselected hclock (hid.add_const q.n) hphase
        have hstop := freyaStateConstructMeas q _ _ _ _ _ _ _ (fun _ => Phase.halted)
          hseed hit hx hg hsel hclock hid measurable_const
        exact hstop.ite (measurableSet_le measurable_const hit) hnext
      have freyaPageUpdateMeas (q : Raw) :
          Measurable (fun z : State q × Reply q.d q.n => update q z.1 z.2) := by
        clear * - q freyaFullCodeMeas freyaDifferenceCodeMeas freyaFullUpdateMeas freyaDifferenceUpdateMeas freyaStateCode freyaStateCodeMeas freyaPhaseFullMeas freyaPhaseDifferenceMeas freyaPhaseParamMeas freyaStateConstructMeas freyaPageAdvanceMeas

        classical
        have hfull : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            let c := fullUpdate z.2.2 z.1.2
            let s := {z.1.1 with
              clock:=c.clock
              nextID:=c.nextID
              phase:=Phase.full z.2.1 c}
            if c.remaining.isEmpty then advance q {s with g:=fullResult c} else s) := by
          have hs : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
              fullUpdate z.2.2 z.1.2) := freyaFullUpdateMeas.comp (measurable_snd.snd.prodMk measurable_fst.snd)
          have hc := freyaFullCodeMeas.comp hu
          have hp := freyaPhaseFullMeas.comp (measurable_snd.fst.prodMk hu)
          have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp
          have hg := ((measurable_of_countable (fun l : List (Fin q.m) => (l.length : ℝ)⁻¹)).comp hc.fst).smul
            hc.snd.snd.snd.fst
          have hnext := (freyaPageAdvanceMeas q).comp
            (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
              hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
              hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp)
          exact hnext.ite (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst)
            (measurableSet_singleton true)) hbase
        have hdiff : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            let c := differenceUpdate z.2 z.1.2
            let s := {z.1.1 with
              clock:=c.clock
              nextID:=c.nextID
              phase:=Phase.difference c}
            if c.target≤c.count then advance q {s with g:=s.g+differenceResult c} else s) := by
          have hs : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
          have hu : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
              differenceUpdate z.2 z.1.2) := freyaDifferenceUpdateMeas.comp (measurable_snd.prodMk measurable_fst.snd)
          have hc := freyaDifferenceCodeMeas.comp hu
          have hp := freyaPhaseDifferenceMeas.comp hu
          have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp
          have hg := hs.snd.snd.snd.fst.add
            (((measurable_of_countable (fun a : ℕ => (a : ℝ)⁻¹)).comp hc.fst).smul hc.snd.snd.snd.snd.fst)
          have hnext := (freyaPageAdvanceMeas q).comp
            (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
              hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
              hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp)
          exact hnext.ite (measurableSet_le hc.fst hc.snd.fst) hbase
        have h := freyaPhaseParamMeas (fun z : State q × Reply q.d q.n => z.1.phase)
          (((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd).comp measurable_fst)
          Prod.fst measurable_fst _ hfull _ hdiff
        convert h using 1
        funext z
        delta update
        cases z.1.phase <;> rfl
      have freyaPendingRequestMeas {d m n : ℕ} :
          Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) => pendingRequest z.1 z.2) := by
        clear * - d m n freyaDevelopmentOptionElimMeas freyaOptionSomeMeas

        classical
        have hc : Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) =>
            (⟨z.1,z.2⟩ : Request d m n)) := by
          change Measurable[_,MeasurableSpace.comap (fun r : Request d m n => (r.clock,r.pending)) inferInstance] _
          rw [measurable_comap_iff]
          exact measurable_id
        have hsome := freyaOptionSomeMeas.comp hc
        have hn : MeasurableSet {o : Option (Job d m) | o ≠ none} := by
          have hi := freyaDevelopmentOptionElimMeas false (fun _ : Job d m => true) measurable_const
          convert hi (measurableSet_singleton true) using 1
          ext o
          cases o <;> simp (config := { iota := false })
        have he : MeasurableSet {z : ℝ≥0 × (Fin n → Option (Job d m)) | ∃ i, z.2 i ≠ none} := by
          convert MeasurableSet.iUnion (fun i : Fin n => hn.preimage ((measurable_pi_apply i).comp measurable_snd)) using 1
          ext z
          simp (config := { iota := false })
        exact hsome.ite he measurable_const
      have freyaPageQueryMeas (q : Raw) : Measurable (query q) := by
        clear * - q freyaFullCode freyaDifferenceCode freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCodeMeas freyaPhaseParamMeas freyaPendingRequestMeas

        classical
        have hfull : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) =>
            if z.2.2.remaining.isEmpty then none else pendingRequest z.2.2.clock z.2.2.pending) := by
          have hc : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) => freyaFullCode z.2.2) :=
            freyaFullCodeMeas.comp measurable_snd.snd
          exact measurable_const.ite
            (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst) (measurableSet_singleton true))
            (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.fst))
        have hdiff : Measurable (fun z : State q × DifferenceState q.d q.m q.n =>
            if z.2.target≤z.2.count then none else pendingRequest z.2.clock z.2.pending) := by
          have hc : Measurable (fun z : State q × DifferenceState q.d q.m q.n => freyaDifferenceCode z.2) :=
            freyaDifferenceCodeMeas.comp measurable_snd
          exact measurable_const.ite (measurableSet_le hc.fst hc.snd.fst)
            (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.snd.fst))
        have hp := freyaPhaseParamMeas (fun s : State q => s.phase)
          ((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd)
          (fun _ => (none : Option (Request q.d q.m q.n))) measurable_const _ hfull _ hdiff
        have h : Measurable (fun s : State q => ((0 : Fin 1), s.phase.casesOn
            (motive:=fun _ => Option (Request q.d q.m q.n))
            (fun _ c => if c.remaining.isEmpty then none else pendingRequest c.clock c.pending)
            (fun c => if c.target≤c.count then none else pendingRequest c.clock c.pending) none)) :=
          measurable_const.prodMk hp
        convert h using 1
        funext s
        delta query
        cases s.phase <;> rfl
      have freyaPageTraceMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (k : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => trace q O z.1 z.2 k) := by
        clear * - q f τ O hservice k freyaPageInitialMeas freyaPageUpdateMeas freyaPageQueryMeas

        exact (measurable_trajectory q O hservice.1.2 (freyaPageInitialMeas q)
          (freyaPageUpdateMeas q) (freyaPageQueryMeas q) k).1
      have freyaFindMeas {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          (l : List α) (p : Ω → α → Bool) (hp : ∀ a,Measurable (fun z => p z a)) :
          Measurable (fun z => l.find? (p z)) := by
        clear * - Ω α l p hp

        classical
        induction l with
        | nil => exact measurable_const
        | cons a l ih =>
          have h : Measurable (fun z => if p z a=true then some a else l.find? (p z)) :=
            measurable_const.ite ((hp a) (measurableSet_singleton true)) ih
          convert h using 1
          funext z
          simp (config := { iota := false }) only [List.find?_cons]
          cases p z a <;> rfl
      have freyaActiveMeas (q : Raw) : Measurable (active : State q → Bool) := by
        clear * - q freyaPhaseCode freyaPhaseCodeMeas freyaStateCodeMeas

        have hphase := (freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd
        have h : Measurable (fun s : State q => Sum.elim (fun _ : Unit => false)
          (fun _ : (Bool × FullState q.d q.m q.n) ⊕ DifferenceState q.d q.m q.n => true)
            (freyaPhaseCode s.phase)) :=
          (measurable_const.sumElim measurable_const).comp (freyaPhaseCodeMeas.comp hphase)
        convert h using 1
        funext s
        dsimp only [active]
        cases s.phase <;> rfl
      have freyaPageBatchStartMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (batch : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchStartCall q O z.1 z.2 batch) := by
        clear * - q f τ O hservice batch freyaStateCodeMeas freyaPageTraceMeas freyaFindMeas freyaActiveMeas

        apply freyaFindMeas
        intro k
        have hs := freyaPageTraceMeas q f τ O hservice k
        have hi := ((freyaStateCodeMeas q).comp hs).snd.fst
        have hb := (freyaActiveMeas q).comp hs
        exact (measurable_of_countable (fun p : ℕ × Bool => decide (p.1=batch) && p.2)).comp (hi.prodMk hb)
      have freyaPageInvocationMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (batch : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => invocation q O z.1 z.2 batch) := by
        clear * - q f τ O hservice batch freyaOptionSomeMeas freyaMeasurableSelect freyaOptionParamMeas freyaFullCode freyaDifferenceCode freyaFullCodeMeas freyaDifferenceCodeMeas freyaStateCode freyaStateCodeMeas freyaPhaseParamMeas freyaPageTraceMeas freyaPageBatchStartMeas

        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        let V := Bool × Space q.d × Space q.d × ℝ≥0 × ℕ
        have ht : Measurable (fun z : Ω × ℕ => trace q O z.1.1 z.1.2 z.2) :=
          freyaMeasurableSelect _ measurable_snd _ (fun k =>
            (freyaPageTraceMeas q f τ O hservice k).comp measurable_fst)
        have hp := ((freyaStateCodeMeas q).comp ht).snd.snd.snd.snd.snd.snd.snd
        have hf : Measurable (fun z : (Ω × ℕ) × (Bool × FullState q.d q.m q.n) =>
            some (true,z.2.2.point,z.2.2.point,z.2.2.clock,z.2.2.nextID-q.n)) := by
          have hc : Measurable (fun z : (Ω × ℕ) × (Bool × FullState q.d q.m q.n) => freyaFullCode z.2.2) :=
            freyaFullCodeMeas.comp measurable_snd.snd
          exact freyaOptionSomeMeas.comp (measurable_const.prodMk (hc.snd.snd.fst.prodMk
            (hc.snd.snd.fst.prodMk (hc.snd.snd.snd.snd.snd.fst.prodMk
              ((measurable_of_countable (fun a : ℕ => a-q.n)).comp hc.snd.snd.snd.snd.snd.snd.snd)))))
        have hd : Measurable (fun z : (Ω × ℕ) × DifferenceState q.d q.m q.n =>
            some (false,z.2.x,z.2.y,z.2.clock,z.2.nextID-q.n)) := by
          have hc : Measurable (fun z : (Ω × ℕ) × DifferenceState q.d q.m q.n => freyaDifferenceCode z.2) :=
            freyaDifferenceCodeMeas.comp measurable_snd
          exact freyaOptionSomeMeas.comp (measurable_const.prodMk (hc.snd.snd.fst.prodMk
            (hc.snd.snd.snd.fst.prodMk (hc.snd.snd.snd.snd.snd.snd.fst.prodMk
              ((measurable_of_countable (fun a : ℕ => a-q.n)).comp hc.snd.snd.snd.snd.snd.snd.snd.snd)))))
        have hbody := freyaPhaseParamMeas _ hp (fun _ => (none : Option V)) measurable_const _ hf _ hd
        have h := freyaOptionParamMeas _ (freyaPageBatchStartMeas q f τ O hservice batch)
          (fun _ : Ω => (none : Option V)) measurable_const _ hbody
        convert h using 1
        funext z
        dsimp only [invocation]
        cases batchStartCall q O z.1 z.2 batch with
        | none => rfl
        | some k =>
          dsimp only [Option.bind_some,Option.elim_some,freyaStateCode,Function.comp_def]
          cases (trace q O z.1 z.2 k).phase <;> rfl
      have freyaPendingAfterMeas (q : Raw) :
          Measurable (fun z : State q × Reply q.d q.n => collectorPendingAfter q z.1 z.2) := by
        clear * - q freyaFullCodeMeas freyaDifferenceCodeMeas freyaFullUpdateMeas freyaDifferenceUpdateMeas freyaStateCodeMeas freyaPhaseParamMeas

        have hp : Measurable (fun z : State q × Reply q.d q.n => z.1.phase) :=
          ((freyaStateCodeMeas q).comp measurable_fst).snd.snd.snd.snd.snd.snd.snd
        have hf : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            (fullUpdate z.2.2 z.1.2).pending) :=
          (freyaFullCodeMeas.comp (freyaFullUpdateMeas.comp
            (measurable_snd.snd.prodMk measurable_fst.snd))).snd.snd.snd.snd.fst
        have hd : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            (differenceUpdate z.2 z.1.2).pending) :=
          (freyaDifferenceCodeMeas.comp (freyaDifferenceUpdateMeas.comp
            (measurable_snd.prodMk measurable_fst.snd))).snd.snd.snd.snd.snd.fst
        have h := freyaPhaseParamMeas _ hp (fun _ => fun _ => (none : Option (Job q.d q.m))) measurable_const _ hf _ hd
        convert h using 1
        funext z
        dsimp only [collectorPendingAfter]
        cases z.1.phase <;> rfl
      have freyaHistoryAmbient (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (batch : ℕ) :
          historyBefore q O batch≤(inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))) := by
        clear * - q f τ O hservice batch freyaDevelopmentOptionElimMeas freyaOptionSomeMeas freyaPageQueryMeas freyaPageTraceMeas freyaPageBatchStartMeas freyaPageInvocationMeas freyaPendingAfterMeas freyaPageInitialMeas freyaPageUpdateMeas

        have hcall := (freyaDevelopmentOptionElimMeas (0 : ℕ) id measurable_id).comp
          (freyaPageBatchStartMeas q f τ O hservice batch)
        have hview : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
            (invocation q O z.1 z.2 batch,fun k : ℕ =>
              if k<(batchStartCall q O z.1 z.2 batch).getD 0 then
                let s := trace q O z.1 z.2 k
                let reply := replyAt q O z.1 z.2 k (query q s)
                some (query q s,reply,collectorPendingAfter q s reply)
              else none)) := by
          apply (freyaPageInvocationMeas q f τ O hservice batch).prodMk
          apply Measurable.of_eval
          intro k
          have hs := freyaPageTraceMeas q f τ O hservice k
          have hq := (freyaPageQueryMeas q).comp hs
          have hr := measurable_replyAt q O hservice.1.2 (freyaPageInitialMeas q) (freyaPageUpdateMeas q)
              (freyaPageQueryMeas q) k measurable_id hq
          have hp := (freyaPendingAfterMeas q).comp (hs.prodMk hr)
          apply (freyaOptionSomeMeas.comp (hq.prodMk (hr.prodMk hp))).ite _ measurable_const
          have he : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
              (batchStartCall q O z.1 z.2 batch).getD 0) := by
            convert hcall using 1
            funext z
            dsimp only [Function.comp_def]
            cases batchStartCall q O z.1 z.2 batch <;> rfl
          exact measurableSet_lt measurable_const he
        exact hview.comap_le
      have freyaExitAdvance (q : Raw) (s : State q) (r : Reply q.d q.n)
          (ha : active s=true)
          (he : (update q s r).iteration≠s.iteration ∨ active (update q s r)=false) :
          ∃ t : State q,t.iteration=s.iteration ∧ t.seed=s.seed ∧ update q s r=advance q t := by
        clear * - q s r ha he

        cases hp : s.phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := fullResult (fullUpdate c r)
              clock := (fullUpdate c r).clock
              nextID := (fullUpdate c r).nextID
              phase := .full first (fullUpdate c r)},rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
        | difference c =>
          dsimp only [update] at he ⊢
          rw [hp] at he ⊢
          dsimp only at he ⊢
          split
          · exact ⟨{s with
              g := s.g+differenceResult (differenceUpdate c r)
              clock := (differenceUpdate c r).clock
              nextID := (differenceUpdate c r).nextID
              phase := .difference (differenceUpdate c r)},rfl,rfl,rfl⟩
          · rename_i h
            rw [ite_eq_right h] at he
            rcases he with he|he
            · exact False.elim (he rfl)
            · cases he
      have freyaBatchEndFacts (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          a<e ∧ e≤eventLimit q ∧
            (∀ r,a≤r → r<e → (trace q O seed ω r).iteration=b ∧ active (trace q O seed ω r)=true) ∧
            ((trace q O seed ω e).iteration≠b ∨ active (trace q O seed ω e)=false) := by
        clear * - q O seed ω b a e hs he freyaPageFirstMatch freyaPageBatchStartFacts

        have hstart := freyaPageBatchStartFacts q O seed ω b a hs
        dsimp only [batchEndCall] at he
        rw [hs] at he
        dsimp only [Option.bind_some] at he
        obtain ⟨hlim,htrue,hprev⟩ := freyaPageFirstMatch _ _ e he
        have hafter : a<e := by
          have hh := htrue
          simp (config := { iota := false }) only [Bool.and_eq_true,decide_eq_true_eq] at hh
          exact hh.1
        refine ⟨hafter,by omega,?_,?_⟩
        · intro r har hre
          by_cases hr : r=a
          · subst r; exact ⟨hstart.2.1,hstart.2.2.1⟩
          · have hlt : a<r := by omega
            have hh := hprev r hre
            have hit : (trace q O seed ω r).iteration=b := by
              by_contra h
              apply hh
              have hd : decide ((trace q O seed ω r).iteration≠b)=true := decide_eq_true_eq.mpr h
              simp (config := { iota := false }) only [hlt,hd,decide_true,Bool.true_and,Bool.true_or]
            refine ⟨hit,?_⟩
            cases ha : active (trace q O seed ω r) with
            | false =>
              apply False.elim
              apply hh
              simp (config := { iota := false }) only [hlt,decide_true,Bool.true_and,ha,Bool.not_false,Bool.or_true]
            | true => rfl
        · simpa (config := { iota := false }) only [hafter,decide_true,Bool.true_and,Bool.or_eq_true,
            Bool.not_eq_true',decide_eq_true_eq] using htrue
      have freyaBatchExitState (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          ∃ t : State q,t.iteration=b ∧ t.seed=seed ∧ trace q O seed ω e=advance q t := by
        clear * - q O seed ω b a e hs he freyaPageTraceSeed freyaExitAdvance freyaBatchEndFacts

        obtain ⟨ha,_,hbefore,hexit⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        have hepos : 0<e := by omega
        have hed : e-1+1=e := by omega
        have hp := hbefore (e-1) (by omega) (by omega)
        have hx : (update q (trace q O seed ω (e-1))
            (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1))))).iteration≠
              (trace q O seed ω (e-1)).iteration ∨
            active (update q (trace q O seed ω (e-1))
              (replyAt q O seed ω (e-1) (query q (trace q O seed ω (e-1)))))=false := by
          change (trace q O seed ω (e-1+1)).iteration≠(trace q O seed ω (e-1)).iteration ∨
            active (trace q O seed ω (e-1+1))=false
          rw [hed,hp.1]
          exact hexit
        obtain ⟨t,hti,hts,hout⟩ := freyaExitAdvance q _ _ hp.2 hx
        refine ⟨t,hti.trans hp.1,hts.trans (freyaPageTraceSeed q O seed ω (e-1)),?_⟩
        change trace q O seed ω (e-1+1)=advance q t at hout
        rwa [hed] at hout
      have freyaBatchNextStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hb : b<rounds q) (hs : batchStartCall q O seed ω b=some a)
          (he : batchEndCall q O seed ω b=some e) :
          batchStartCall q O seed ω (b+1)=some e := by
        clear * - q O seed ω b a e hb hs he freyaPageIterationMonotone freyaPageBatchStartFacts freyaBatchEndFacts freyaBatchExitState

        classical
        obtain ⟨ha,hlim,hbefore,_⟩ := freyaBatchEndFacts q O seed ω b a e hs he
        obtain ⟨t,hti,hts,hout⟩ := freyaBatchExitState q O seed ω b a e hs he
        have hnot : ¬rounds q≤t.iteration := by omega
        have hp : (trace q O seed ω e).iteration=b+1 ∧ active (trace q O seed ω e)=true := by
          rw [hout]
          dsimp only [advance]
          rw [ite_eq_right hnot]
          dsimp only
          constructor
          · rw [hti]
          · by_cases hbit : refreshAt t.seed t.iteration=true
            · rw [ite_eq_left hbit]; rfl
            · rw [ite_eq_right hbit]; rfl
        have hprev : ∀ r<e,(trace q O seed ω r).iteration≠b+1 := by
          intro r hr heq
          by_cases hra : r<a
          · have hmono := freyaPageIterationMonotone q O seed ω (Nat.le_of_lt hra)
            change (trace q O seed ω r).iteration≤(trace q O seed ω a).iteration at hmono
            have hit := (freyaPageBatchStartFacts q O seed ω b a hs).2.1
            omega
          · have hit := (hbefore r (by omega) hr).1
            omega
        dsimp only [batchStartCall]
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨?_,e,?_,?_,?_⟩
        · simp (config := { iota := false }) only [hp.1,hp.2,decide_true,Bool.and_self]
        · simpa (config := { iota := false }) only [List.length_range] using (show e<eventLimit q+1 by omega)
        · simp (config := { iota := false }) only [List.getElem_range]
        · intro r hr
          simp (config := { iota := false }) only [List.getElem_range,hprev r hr,decide_false,Bool.false_and,Bool.not_false]
      have freyaBatchLastHalted (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (a e : ℕ)
          (hs : batchStartCall q O seed ω (rounds q)=some a)
          (he : batchEndCall q O seed ω (rounds q)=some e) :
          (trace q O seed ω e).phase=.halted := by
        clear * - q O seed ω a e hs he freyaBatchExitState

        obtain ⟨t,hti,_,hout⟩ := freyaBatchExitState q O seed ω (rounds q) a e hs he
        rw [hout]
        dsimp only [advance]
        rw [ite_eq_left (show rounds q≤t.iteration by omega)]
      have freyaBatchZeroStart (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hK : 0<q.K)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          batchStartCall q O seed ω 0=some 0 := by
        clear * - q hm hn hK O seed ω

        classical
        dsimp only [batchStartCall]
        apply List.find?_eq_some_iff_getElem.mpr
        refine ⟨?_,0,?_,?_,?_⟩
        · dsimp only [trace,run,initial,active]
          rw [ite_eq_right (show ¬(q.m=0 ∨ q.n=0 ∨ q.K=0) by omega)]
          rfl
        · simp (config := { iota := false }) only [List.length_range]; omega
        · simp (config := { iota := false }) only [List.getElem_range]
        · intro r hr; omega
      have freyaInvocationOfStart (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a : ℕ)
          (hs : batchStartCall q O seed ω b=some a) :
          ∃ full x y clock firstID,invocation q O seed ω b=some (full,x,y,clock,firstID) := by
        clear * - q O seed ω b a hs freyaPageBatchStartFacts

        have ha := (freyaPageBatchStartFacts q O seed ω b a hs).2.2.1
        dsimp only [invocation]
        rw [hs]
        dsimp only [Option.bind_some]
        cases hp : (trace q O seed ω a).phase with
        | halted => dsimp only [active] at ha; rw [hp] at ha; contradiction
        | full first c => exact ⟨true,c.point,c.point,c.clock,c.nextID-q.n,rfl⟩
        | difference c => exact ⟨false,c.x,c.y,c.clock,c.nextID-q.n,rfl⟩
      have freyaEndOfStart (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r)))
          (b a : ℕ) (hs : batchStartCall q O seed ω b=some a) :
          ∃ e,batchEndCall q O seed ω b=some e := by
        clear * - q hm hn hS hK f τ O seed ω hservice b a hs freyaInvocationOfStart

        obtain ⟨full,x,y,clock,firstID,hi⟩ := freyaInvocationOfStart q O seed ω b a hs
        have hh := (restart_coupling q hm hn hS hK f τ O (seed,ω) hservice b firstID full x y clock hi).1
        cases he : batchEndCall q O seed ω b with
        | none => rw [he] at hh; cases hh
        | some e => exact ⟨e,rfl⟩
      have freyaAllBatchBoundaries (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r))) :
          ∀ b,b≤rounds q → ∃ a e,batchStartCall q O seed ω b=some a ∧ batchEndCall q O seed ω b=some e := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaBatchNextStart freyaBatchZeroStart freyaEndOfStart

        intro b
        induction b with
        | zero =>
          intro _
          have hs := freyaBatchZeroStart q hm hn hK O seed ω
          obtain ⟨e,he⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice 0 0 hs
          exact ⟨0,e,hs,he⟩
        | succ b ih =>
          intro hb
          obtain ⟨a,e,hs,he⟩ := ih (by omega)
          have hnext := freyaBatchNextStart q O seed ω b a e (by omega) hs he
          obtain ⟨e',he'⟩ := freyaEndOfStart q hm hn hS hK f τ O seed ω hservice (b+1) e hnext
          exact ⟨e,e',hnext,he'⟩
      have freyaTraceClockMono (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
          Monotone (fun a => (trace q O seed ω a).clock) := by
        clear * - q O seed ω freyaTraceClockConsistent freyaUpdateClockMono

        apply monotone_nat_of_le_succ
        intro a
        exact freyaUpdateClockMono q _ _ (freyaTraceClockConsistent q O seed ω a)
      have freyaElapsedAtBoundary (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (b a e : ℕ)
          (hs : batchStartCall q O seed ω b=some a) (he : batchEndCall q O seed ω b=some e) :
          batchElapsed q O seed ω b=(trace q O seed ω e).clock-(trace q O seed ω a).clock := by
        clear * - q O seed ω b a e hs he

        dsimp only [batchElapsed,batchClock]
        rw [he,hs]
        rfl
      have freyaBatchClockSum (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r))) :
          ∀ b,b≤rounds q → ∀ a e,batchStartCall q O seed ω b=some a →
            batchEndCall q O seed ω b=some e →
            (∑ j∈Finset.range (b+1),batchElapsed q O seed ω j)=(trace q O seed ω e).clock := by
        clear * - q hm hn hS hK f τ O seed ω hservice freyaBatchEndFacts freyaBatchNextStart freyaBatchZeroStart freyaAllBatchBoundaries freyaTraceClockMono freyaElapsedAtBoundary

        intro b
        induction b with
        | zero =>
          intro _ a e hs he
          have ha : a=0 := Option.some.inj (hs.symm.trans (freyaBatchZeroStart q hm hn hK O seed ω))
          subst a
          rw [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,freyaElapsedAtBoundary q O seed ω 0 0 e hs he]
          change (trace q O seed ω e).clock-0=(trace q O seed ω e).clock
          exact tsub_zero _
        | succ b ih =>
          intro hb a e hs he
          obtain ⟨a',e',hs',he'⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O seed ω hservice b (by omega)
          have hnext := freyaBatchNextStart q O seed ω b a' e' (by omega) hs' he'
          have ha : a=e' := Option.some.inj (hs.symm.trans hnext)
          subst a
          rw [Finset.sum_range_succ,ih (by omega) a' e' hs' he',freyaElapsedAtBoundary q O seed ω (b+1) e' e hs he]
          have hle := freyaTraceClockMono q O seed ω (Nat.le_of_lt (freyaBatchEndFacts q O seed ω (b+1) e' e hs he).1)
          change (trace q O seed ω e').clock≤(trace q O seed ω e).clock at hle
          simpa (config := { iota := false }) only [add_comm] using tsub_add_cancel_of_le hle
      have freyaElapsedClockSum (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
          (hservice : servicePath f τ (fun k r => replyAt q O seed ω k (0,r)))
          (N : ℕ) (hN : eventLimit q≤N) :
          (execute O (factory q) (fun _ => N) seed ω).2=
            ∑ j∈Finset.range (rounds q+1),batchElapsed q O seed ω j := by
        clear * - q hm hn hS hK f τ O seed ω hservice N hN freyaBatchEndFacts freyaBatchLastHalted freyaAllBatchBoundaries freyaBatchClockSum

        obtain ⟨a,e,hs,he⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O seed ω hservice (rounds q) le_rfl
        have hhalt := freyaBatchLastHalted q O seed ω a e hs he
        have hlim := (freyaBatchEndFacts q O seed ω (rounds q) a e hs he).2.1
        have hstable := (halt_stability q O seed ω e hhalt).2 N (hlim.trans hN)
        rw [execute_correspondence]
        change (trace q O seed ω N).clock=_
        rw [hstable]
        exact (freyaBatchClockSum q hm hn hS hK f τ O seed ω hservice (rounds q) le_rfl a e hs he).symm
      let freyaBatchTag (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (b : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) : ℕ :=
        (invocation q O z.1 z.2 b).elim 2 (fun t => if t.1 then 0 else 1)
      have freyaBatchTagFull (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (b : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (h : freyaBatchTag q O b z=0) :
          ∃ x c i,invocation q O z.1 z.2 b=some (true,x,x,c,i) := by
        clear * - q O b z h freyaBatchTag

        dsimp only [freyaBatchTag,invocation] at h ⊢
        cases hs : batchStartCall q O z.1 z.2 b with
        | none => rw [hs] at h; cases h
        | some a =>
          rw [hs] at h
          dsimp only [Option.bind_some] at h ⊢
          cases hp : (trace q O z.1 z.2 a).phase with
          | halted => rw [hp] at h; cases h
          | full first c => exact ⟨c.point,c.clock,c.nextID-q.n,rfl⟩
          | difference c => rw [hp] at h; cases h
      have freyaBatchTagDifference (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (b : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (h : freyaBatchTag q O b z=1) :
          ∃ x y c i,invocation q O z.1 z.2 b=some (false,x,y,c,i) := by
        clear * - q O b z h freyaBatchTag

        dsimp only [freyaBatchTag] at h
        cases hi : invocation q O z.1 z.2 b with
        | none => rw [hi] at h; cases h
        | some t =>
          obtain ⟨bit,x,y,c,i⟩ := t
          cases bit with
          | false => exact ⟨x,y,c,i,rfl⟩
          | true => rw [hi] at h; cases h
      have freyaBatchZeroTag (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hK : 0<q.K)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) : freyaBatchTag q O 0 z=0 := by
        clear * - q hm hn hK O z freyaBatchZeroStart freyaBatchTag

        dsimp only [freyaBatchTag,invocation]
        rw [freyaBatchZeroStart q hm hn hK O z.1 z.2]
        dsimp only [Option.bind_some,trace,run,initial]
        rw [ite_eq_right (show ¬(q.m=0 ∨ q.n=0 ∨ q.K=0) by omega)]
        rfl
      have freyaBatchNextTag (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hservice : servicePath f τ (fun k r => replyAt q O z.1 z.2 k (0,r)))
          (b : ℕ) (hb : b<rounds q) :
          freyaBatchTag q O (b+1) z=if refreshAt z.1 b then 0 else 1 := by
        clear * - q hm hn hS hK f τ O z hservice b hb freyaBatchExitState freyaBatchNextStart freyaAllBatchBoundaries freyaBatchTag

        obtain ⟨a,e,hs,he⟩ := freyaAllBatchBoundaries q hm hn hS hK f τ O z.1 z.2 hservice b (by omega)
        have hnext := freyaBatchNextStart q O z.1 z.2 b a e hb hs he
        obtain ⟨t,hti,hts,hout⟩ := freyaBatchExitState q O z.1 z.2 b a e hs he
        dsimp only [freyaBatchTag,invocation]
        rw [hnext]
        dsimp only [Option.bind_some]
        rw [hout]
        dsimp only [advance]
        rw [ite_eq_right (show ¬rounds q≤t.iteration by omega)]
        dsimp only
        rw [hti,hts]
        cases hbit : refreshAt z.1 b <;> rfl
      have freyaBatchTagHistoryMeas (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ) :
          Measurable[historyBefore q O b] (freyaBatchTag q O b) := by
        clear * - q O b freyaDevelopmentOptionElimMeas freyaPageInvocationHistoryMeas freyaBatchTag

        have ht : Measurable (fun t : Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) =>
            t.elim (2 : ℕ) (fun a => if a.1 then 0 else 1)) :=
          freyaDevelopmentOptionElimMeas 2 _
            ((measurable_of_countable (fun b : Bool => if b then (0 : ℕ) else 1)).comp measurable_fst)
        exact ht.comp (freyaPageInvocationHistoryMeas q O b)
      have freyaBatchEndMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchEndCall q O z.1 z.2 b) := by
        clear * - q f τ O hservice b freyaOptionParamMeas freyaStateCodeMeas freyaPageTraceMeas freyaFindMeas freyaActiveMeas freyaPageBatchStartMeas

        classical
        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        have hp (a : ℕ) : Measurable (fun z : Ω × ℕ => decide (z.2<a) &&
            (decide ((trace q O z.1.1 z.1.2 a).iteration≠b) || !active (trace q O z.1.1 z.1.2 a))) := by
          have ht : Measurable (fun z : Ω × ℕ => trace q O z.1.1 z.1.2 a) :=
            (freyaPageTraceMeas q f τ O hservice a).comp measurable_fst
          have hi := ((freyaStateCodeMeas q).comp ht).snd.fst
          have ha := (freyaActiveMeas q).comp ht
          exact (measurable_of_countable (fun t : ℕ × ℕ × Bool =>
            decide (t.1<a) && (decide (t.2.1≠b) || !t.2.2))).comp
              (measurable_snd.prodMk (hi.prodMk ha))
        have hb := freyaFindMeas (List.range (eventLimit q+1)) _ hp
        have h := freyaOptionParamMeas _ (freyaPageBatchStartMeas q f τ O hservice b)
          (fun _ : Ω => (none : Option ℕ)) measurable_const _ hb
        convert h using 1
        funext z
        dsimp only [batchEndCall]
        cases batchStartCall q O z.1 z.2 b <;> rfl
      have freyaBatchClockMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => (batchClock q O z.1 z.2 b).getD 0) := by
        clear * - q f τ O hservice b freyaMeasurableSelect freyaOptionParamMeas freyaStateCodeMeas freyaPageTraceMeas freyaPageBatchStartMeas

        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        have ht : Measurable (fun z : Ω × ℕ => trace q O z.1.1 z.1.2 z.2) :=
          freyaMeasurableSelect _ measurable_snd _ (fun a =>
            (freyaPageTraceMeas q f τ O hservice a).comp measurable_fst)
        have hc := ((freyaStateCodeMeas q).comp ht).snd.snd.snd.snd.snd.fst
        have h := freyaOptionParamMeas _ (freyaPageBatchStartMeas q f τ O hservice b)
          (fun _ : Ω => (0 : ℝ≥0)) measurable_const _ hc
        convert h using 1
        funext z
        dsimp only [batchClock]
        cases batchStartCall q O z.1 z.2 b <;> rfl
      have freyaBatchElapsedMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => (batchElapsed q O z.1 z.2 b : ℝ≥0∞)) := by
        clear * - q f τ O hservice b freyaMeasurableSelect freyaOptionParamMeas freyaStateCodeMeas freyaPageTraceMeas freyaBatchEndMeas freyaBatchClockMeas

        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        have ht : Measurable (fun z : Ω × ℕ => trace q O z.1.1 z.1.2 z.2) :=
          freyaMeasurableSelect _ measurable_snd _ (fun a =>
            (freyaPageTraceMeas q f τ O hservice a).comp measurable_fst)
        have hc := ((freyaStateCodeMeas q).comp ht).snd.snd.snd.snd.snd.fst
        have hstart : Measurable (fun z : Ω × ℕ => (batchClock q O z.1.1 z.1.2 b).getD 0) :=
          (freyaBatchClockMeas q f τ O hservice b).comp measurable_fst
        have h := freyaOptionParamMeas _ (freyaBatchEndMeas q f τ O hservice b)
          (fun _ : Ω => (0 : ℝ≥0)) measurable_const _ (hc.sub hstart)
        have he : Measurable (fun z : Ω => batchElapsed q O z.1 z.2 b) := by
          convert h using 1
          funext z
          dsimp only [batchElapsed]
          cases batchEndCall q O z.1 z.2 b <;> rfl
        exact ENNReal.continuous_coe.measurable.comp he
      have freyaExecutionElapsedMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (N : ℕ) :
          Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
            ((execute O (factory q) (fun _ => N) z.1 z.2).2 : ℝ≥0∞)) := by
        clear * - q f τ O hservice N freyaStateCodeMeas freyaPageTraceMeas

        have ht := freyaPageTraceMeas q f τ O hservice N
        have hc := ((freyaStateCodeMeas q).comp ht).snd.snd.snd.snd.snd.fst
        have he := ENNReal.continuous_coe.measurable.comp hc
        convert he using 1
        funext z
        rw [execute_correspondence]
        rfl
      have freyaRefreshMarginal (q : Raw) (hρ : 0<q.ρ) (hρone : q.ρ≤1)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (b : ℕ) :
          (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) {z | refreshAt z.1 b=true}=
            ENNReal.ofReal q.ρ ∧
          (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) {z | refreshAt z.1 b=false}=
            ENNReal.ofReal (1-q.ρ) := by
        clear * - q hρ hρone O b

        classical
        let : NeZero (max 1 q.K) := ⟨by omega⟩
        let β := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one q.ρ)
        have hseed : MeasurePreserving (fun z : Seed q.K => z.2.1)
            (seedLaw q.ρ q.K : Measure (Seed q.K)) (refreshLaw q.ρ : Measure (ℕ → Bool)) :=
          measurePreserving_fst.comp measurePreserving_snd
        have hrows : MeasurePreserving (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => z.1.2.1)
            (executionLaw q O : Measure _) (Measure.infinitePi (fun _ : ℕ => β)) :=
          hseed.comp measurePreserving_fst
        have hb := (measurePreserving_eval_infinitePi (fun _ : ℕ => β) b).comp hrows
        have ht := hb.measure_preimage (measurableSet_singleton true).nullMeasurableSet
        have hf := hb.measure_preimage (measurableSet_singleton false).nullMeasurableSet
        have hp : Set.projIcc 0 1 zero_le_one q.ρ=⟨q.ρ,⟨hρ.le,hρone⟩⟩ :=
          Set.projIcc_of_mem _ ⟨hρ.le,hρone⟩
        constructor
        · calc
            _ = β {true} := ht
            _ = (unitInterval.toNNReal (Set.projIcc 0 1 zero_le_one q.ρ) : ℝ≥0∞) :=
              bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton true) (by rfl) (by simp (config := { iota := false }))
            _ = ENNReal.ofReal q.ρ := by rw [hp]; exact ENNReal.ofReal_coe_nnreal.symm
        · calc
            _ = β {false} := hf
            _ = (unitInterval.toNNReal (unitInterval.symm (Set.projIcc 0 1 zero_le_one q.ρ)) : ℝ≥0∞) :=
              bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton false) (by simp (config := { iota := false })) (by rfl)
            _ = ENNReal.ofReal (1-q.ρ) := by rw [hp]; exact ENNReal.ofReal_coe_nnreal.symm
      have freyaBatchTagMass (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (hρ : 0<q.ρ) (hρone : q.ρ≤1) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (b : ℕ) (hb : b<rounds q) :
          (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) {z | freyaBatchTag q O (b+1) z=0}=
            ENNReal.ofReal q.ρ ∧
          (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) {z | freyaBatchTag q O (b+1) z=1}=
            ENNReal.ofReal (1-q.ρ) := by
        clear * - q hm hn hS hK hρ hρone f τ O hservice b hb freyaBatchTag freyaBatchNextTag freyaRefreshMarginal

        have hpaths : ∀ᵐ z ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))),
            servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        have h0 : {z | freyaBatchTag q O (b+1) z=0}=ᵐ[(executionLaw q O : Measure _)]
            {z | refreshAt z.1 b=true} := by
          filter_upwards [hpaths] with z hz
          apply propext
          rw [freyaBatchNextTag q hm hn hS hK f τ O z hz b hb]
          cases refreshAt z.1 b <;> simp (config := { iota := false })
        have h1 : {z | freyaBatchTag q O (b+1) z=1}=ᵐ[(executionLaw q O : Measure _)]
            {z | refreshAt z.1 b=false} := by
          filter_upwards [hpaths] with z hz
          apply propext
          rw [freyaBatchNextTag q hm hn hS hK f τ O z hz b hb]
          cases refreshAt z.1 b <;> simp (config := { iota := false })
        exact ⟨(measure_congr h0).trans (freyaRefreshMarginal q hρ hρone O b).1,
          (measure_congr h1).trans (freyaRefreshMarginal q hρ hρone O b).2⟩
      have freyaCostCompositionBound (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (hρ : 0<q.ρ) (hρone : q.ρ≤1) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (N : ℕ) (hN : eventLimit q≤N) (C : ℝ≥0∞)
          (hC : ∀ (b : ℕ) (E : Set (Seed q.K × ((k : ℕ) → O.Seed k))),
            MeasurableSet[InvocationHistory q O b] E →
            (∀ z∈E,∃ x c i,invocation q O z.1 z.2 b=some (true,x,x,c,i)) →
            (∫⁻ z in E,(batchElapsed q O z.1 z.2 b : ℝ≥0∞) ∂(executionLaw q O : Measure _))≤
              C*(executionLaw q O : Measure _) E) :
          (∫⁻ z,((execute O (factory q) (fun _ => N) z.1 z.2).2 : ℝ≥0∞)
            ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))))≤
            C+(rounds q : ℝ≥0∞)*(ENNReal.ofReal q.ρ*C+ENNReal.ofReal (1-q.ρ)*(4*equilibriumTime τ q.S)) := by
        clear * - q hm hn hS hK hρ hρone f τ hmono O hservice N hN C hC freyaHistoryAmbient freyaElapsedClockSum freyaBatchTag freyaBatchTagFull freyaBatchTagDifference freyaBatchZeroTag freyaBatchNextTag freyaBatchTagHistoryMeas freyaBatchElapsedMeas freyaBatchTagMass

        classical
        let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
        let P := (executionLaw q O : Measure Ω)
        let c : ℕ → Ω → ℝ≥0∞ := fun b z => (batchElapsed q O z.1 z.2 b : ℝ≥0∞)
        let M := ENNReal.ofReal q.ρ*C+ENNReal.ofReal (1-q.ρ)*(4*equilibriumTime τ q.S)
        have hc (b : ℕ) : Measurable (c b) := freyaBatchElapsedMeas q f τ O hservice b
        have hpaths : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        have hzero : (∫⁻ z,c 0 z ∂P)≤C := by
          have hh := hC 0 Set.univ MeasurableSet.univ (fun z _ =>
            freyaBatchTagFull q O 0 z (freyaBatchZeroTag q hm hn hK O z))
          simpa (config := { iota := false }) only [Measure.restrict_univ,measure_univ,mul_one] using hh
        have hstep (b : ℕ) (hb : b<rounds q) : (∫⁻ z,c (b+1) z ∂P)≤M := by
          let F : Set Ω := {z | freyaBatchTag q O (b+1) z=0}
          let D : Set Ω := {z | freyaBatchTag q O (b+1) z=1}
          have hFH : MeasurableSet[InvocationHistory q O (b+1)] F :=
            (freyaBatchTagHistoryMeas q O (b+1)) (measurableSet_singleton 0)
          have hDH : MeasurableSet[InvocationHistory q O (b+1)] D :=
            (freyaBatchTagHistoryMeas q O (b+1)) (measurableSet_singleton 1)
          have hF : MeasurableSet F := freyaHistoryAmbient q f τ O hservice (b+1) F hFH
          have hD : MeasurableSet D := freyaHistoryAmbient q f τ O hservice (b+1) D hDH
          have hfc := hC (b+1) F hFH (fun z hz => freyaBatchTagFull q O (b+1) z hz)
          have hdc := conditional_difference_cost q hm hn hS hK f τ hmono O hservice (b+1) D hDH
            (fun z hz => freyaBatchTagDifference q O (b+1) z hz)
          have he : c (b+1)=ᵐ[P] fun z => F.indicator (c (b+1)) z+D.indicator (c (b+1)) z := by
            filter_upwards [hpaths] with z hz
            have ht := freyaBatchNextTag q hm hn hS hK f τ O z hz b hb
            cases hbit : refreshAt z.1 b with
            | true =>
              have htag : freyaBatchTag q O (b+1) z=0 := by simpa (config := { iota := false }) only [hbit,ite_true] using ht
              have hzF : z∈F := htag
              have hzD : z∉D := by change freyaBatchTag q O (b+1) z≠1; omega
              rw [Set.indicator_of_mem hzF,Set.indicator_of_notMem hzD,add_zero]
            | false =>
              have htag : freyaBatchTag q O (b+1) z=1 := by simpa (config := { iota := false }) only [hbit,Bool.false_eq_true,ite_false] using ht
              have hzD : z∈D := htag
              have hzF : z∉F := by change freyaBatchTag q O (b+1) z≠0; omega
              rw [Set.indicator_of_notMem hzF,Set.indicator_of_mem hzD,zero_add]
          have hmass := freyaBatchTagMass q hm hn hS hK hρ hρone f τ O hservice b hb
          rw [lintegral_congr_ae he,lintegral_add_left ((hc (b+1)).indicator hF),
            lintegral_indicator hF,lintegral_indicator hD]
          have hh := add_le_add hfc hdc
          change (∫⁻ z in F,c (b+1) z ∂P)+(∫⁻ z in D,c (b+1) z ∂P)≤
            C*P F+(4*equilibriumTime τ q.S)*P D at hh
          rw [show P F=ENNReal.ofReal q.ρ from hmass.1,show P D=ENNReal.ofReal (1-q.ρ) from hmass.2] at hh
          simpa (config := { iota := false }) only [M,mul_comm] using hh
        have hsum : ∀ r,r≤rounds q →
            (∑ b∈Finset.range (r+1),∫⁻ z,c b z ∂P)≤C+(r : ℝ≥0∞)*M := by
          intro r
          induction r with
          | zero => intro _; simpa (config := { iota := false }) using hzero
          | succ r ih =>
            intro hr
            rw [Finset.sum_range_succ]
            have hh := add_le_add (ih (by omega)) (hstep r (by omega))
            simpa (config := { iota := false }) only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc] using hh
        have he : (fun z : Ω => ((execute O (factory q) (fun _ => N) z.1 z.2).2 : ℝ≥0∞))=ᵐ[P]
            (fun z => ∑ b∈Finset.range (rounds q+1),c b z) := by
          filter_upwards [hpaths] with z hz
          have hh := freyaElapsedClockSum q hm hn hS hK f τ O z.1 z.2 hz N hN
          dsimp only [c]
          exact_mod_cast hh
        rw [lintegral_congr_ae he,lintegral_finsetSum (Finset.range (rounds q+1)) (fun b _ => hc b)]
        exact hsum (rounds q) le_rfl
      have freyaCostComposition (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S) (hK : 0<q.K)
          (hρ : 0<q.ρ) (hρone : q.ρ≤1) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (N : ℕ) (hN : eventLimit q≤N) :
          let P := (executionLaw q O : Measure (Seed q.K × ((a : ℕ) → O.Seed a)))
          let elapsed := fun z : Seed q.K × ((a : ℕ) → O.Seed a) =>
            ((execute O (factory q) (fun _ => N) z.1 z.2).2 : ℝ≥0∞)
          Measurable elapsed ∧
            (∫⁻ z,elapsed z ∂P)≤multisetTimeBound τ q.m+(rounds q : ℝ≥0∞)*
              (ENNReal.ofReal q.ρ*multisetTimeBound τ q.m+ENNReal.ofReal (1-q.ρ)*(4*equilibriumTime τ q.S)) ∧
            (largeSample q.m q.n →
              (∫⁻ z,elapsed z ∂P)≤5*equilibriumTime τ q.m+(rounds q : ℝ≥0∞)*
                (ENNReal.ofReal q.ρ*(5*equilibriumTime τ q.m)+ENNReal.ofReal (1-q.ρ)*(4*equilibriumTime τ q.S))) := by
        clear * - q hm hn hS hK hρ hρone f τ hmono O hservice N hN freyaExecutionElapsedMeas freyaCostCompositionBound

        refine ⟨freyaExecutionElapsedMeas q f τ O hservice N,?_,?_⟩
        · exact freyaCostCompositionBound q hm hn hS hK hρ hρone f τ hmono O hservice N hN _
            (conditional_full_cost q hm hn hS hK f τ hmono O hservice)
        · intro hlarge
          exact freyaCostCompositionBound q hm hn hS hK hρ hρone f τ hmono O hservice N hN _
            (conditional_full_cost_sharp q hm hn hS hK hlarge f τ hmono O hservice)
      exact freyaCostComposition q hm hn hS hK hρ hρone f τ hmono O hservice N hN


end LongTails.Proofs.FreyaExecution
