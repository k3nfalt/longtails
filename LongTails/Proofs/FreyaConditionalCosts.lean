import LongTails.Template
import LongTails.Proofs.FreyaCollectors
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped ENNReal NNReal

namespace LongTails.Proofs.FreyaConditionalCosts

open LongTails.Setups.FreyaModel LongTails.Proofs.FreyaCollectors
open LongTails.Algorithms.FreyaInputs LongTails.Algorithms.FreyaRandomness
open LongTails.Algorithms.FreyaPage

noncomputable abbrev InvocationHistory (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
    MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k)) := historyBefore q O batch

noncomputable def restrictedProbability {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (E : Set Ω) (hE : (P : Measure Ω) E ≠ 0) :
    ProbabilityMeasure Ω :=
  ⟨ProbabilityTheory.cond (P : Measure Ω) E, ProbabilityTheory.cond_isProbabilityMeasure hE⟩

noncomputable def invocationData (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ)
    (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
    Bool × Space q.d × Space q.d × ℝ≥0 × ℕ :=
  (invocation q O z.1 z.2 batch).getD (true, 0, 0, 0, 0)

noncomputable def restartedRows (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ)
    (z : Seed q.K × ((k : ℕ) → O.Seed k)) (a : ℕ) : ChoiceRow :=
  z.1.1 batch ((invocationData q O batch z).2.2.2.2 + a)

noncomputable def liftRequest (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ)
    (z : Seed q.K × ((k : ℕ) → O.Seed k)) (request : Option (Request q.d q.m q.n)) :
    Option (Request q.d q.m q.n) :=
  let data := invocationData q O batch z
  request.map fun r =>
    { clock := data.2.2.2.1 + r.clock
      pending := fun i => (r.pending i).map fun job =>
        { job with
          kind := match job.kind with
            | Sum.inl _ => Sum.inl data.2.1
            | Sum.inr _ => Sum.inr (data.2.1, data.2.2.1)
          started := data.2.2.2.1 + job.started
          id := data.2.2.2.2 + job.id } }

noncomputable def restartAnswer (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
    (request : Option (Request q.d q.m q.n))
    (z : Seed q.K × ((k : ℕ) → O.Seed k)) : Reply q.d q.n :=
  let data := invocationData q O batch z
  let call := (batchStartCall q O z.1 z.2 batch).getD 0 + a
  (replyAt q O z.1 z.2 call (0, liftRequest q O batch z request)).map
    fun (i, id, clock, _) => (i, id - data.2.2.2.2, clock - data.2.2.2.1, 0)

noncomputable def restartOracle (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ)
    (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
    (hE : (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) E ≠ 0) :
    Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1 where
  Seed := fun _ => Seed q.K × ((k : ℕ) → O.Seed k)
  law := (restrictedProbability (executionLaw q O) E hE).map (fun z => fun _ : ℕ => z)
  answer := fun history request z => restartAnswer q O batch history.length request.2 z

noncomputable def batchEndCall (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : Option ℕ :=
  (batchStartCall q O seed ω batch).bind fun first =>
    (List.range (eventLimit q + 1)).find? fun a =>
      let s := trace q O seed ω a
      decide (first < a) && (decide (s.iteration ≠ batch) || !(active s))

noncomputable def batchElapsed (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : ℝ≥0 :=
  ((batchEndCall q O seed ω batch).map fun a =>
    (trace q O seed ω a).clock - (batchClock q O seed ω batch).getD 0).getD 0

theorem restart_coupling (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (z : Seed q.K × ((k : ℕ) → O.Seed k))
    (hservice : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0, r)))
    (batch firstID : ℕ) (full : Bool) (x y : Space q.d) (clock : ℝ≥0)
    (hinvoke : invocation q O z.1 z.2 batch = some (full, x, y, clock, firstID)) :
    (batchEndCall q O z.1 z.2 batch).isSome ∧
      (if full then
        (fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) (q.n * q.m)).clock
      else
        (differenceTrace q.n q.S (0 : Space q.d) 0 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) q.S).clock) =
        batchElapsed q O z.1 z.2 batch := by
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
      have freyaPageFreshDifference (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
          ∃ call, batchStartCall q O seed ω batch = some call ∧
            (trace q O seed ω call).phase = Phase.difference
              (differenceInitial q.n q.S x y clock (seed.1 batch) firstID) := by
        clear * - q O seed ω batch firstID x y clock h freyaPageTraceSeed freyaPageBatchStartFacts freyaPageDifferenceInvocation freyaPageDifferenceEntryAdvance freyaPageAdvanceDifference
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
        clear * - q hm hn hS f τ O seed ω hservice batch firstID call x y clock hstart hphase freyaPageBatchStartFacts freyaDifferenceLiveStep freyaPageDifferenceQuery freyaPageDifferenceContinue freyaPageCompletedJobEq
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
      let freyaLiftJob {d m : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ) (j : Job d m) : Job d m :=
        { j with kind := Sum.elim (fun _ => Sum.inl x) (fun _ => Sum.inr (x,y)) j.kind
                 started := clock+j.started
                 id := first+j.id }
      let freyaLiftRequest {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
          (r : Request d m n) : Request d m n :=
        ⟨clock+r.clock,fun i => (r.pending i).map (freyaLiftJob x y clock first)⟩
      have freyaLiftDeadline {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
          (τ : Fin n → ℝ≥0∞) (j : Job d m) (i : Fin n) :
          deadline τ (freyaLiftJob x y clock first j) i=clock+deadline τ j i := by
        clear * - d m n x y clock first τ j i freyaLiftJob
        dsimp [deadline,freyaLiftJob,jobWork]
        cases j.kind <;> dsimp only [Sum.elim] <;> simp (config := { iota := false }) [add_assoc]
      have freyaLiftLegal {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
          (τ : Fin n → ℝ≥0∞) (r : Request d m n) (hr : legalRequest τ r) :
          legalRequest τ (freyaLiftRequest x y clock first r) := by
        clear * - d m n x y clock first τ r hr freyaLiftJob freyaLiftRequest freyaLiftDeadline
        obtain ⟨⟨i,j,hj⟩,hr⟩ := hr
        constructor
        · exact ⟨i,freyaLiftJob x y clock first j,by simp (config := { iota := false }) [freyaLiftRequest,hj]⟩
        · intro i j hj
          obtain ⟨k,hk,rfl⟩ := Option.map_eq_some_iff.mp hj
          obtain ⟨hstart,hend⟩ := hr i k hk
          constructor
          · exact add_le_add le_rfl hstart
          · rw [freyaLiftDeadline]
            change ((clock+r.clock : ℝ≥0) : ℝ≥0∞)≤(clock : ℝ≥0∞)+deadline τ k i
            rw [ENNReal.coe_add]
            exact add_le_add le_rfl hend
      have freyaZeroJobValue {d m : ℕ} (j : Job d m) :
          jobValue (fun (_ : Fin m) (_ : Space d) => (0 : ℝ)) j=0 := by
        clear * - d m j
        dsimp [jobValue]
        cases j.kind <;> dsimp only <;> simp (config := { iota := false })
      have freyaRestartServicePath (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r))) (batch : ℕ) :
          servicePath (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ
            (fun a r => restartAnswer q O batch a r z) := by
        clear * - q f τ O z hs batch freyaLiftJob freyaLiftRequest freyaLiftDeadline freyaLiftLegal freyaZeroJobValue
        intro a
        let data := invocationData q O batch z
        let call := (batchStartCall q O z.1 z.2 batch).getD 0+a
        have hlift (r : Request q.d q.m q.n) : liftRequest q O batch z (some r)=
            some (freyaLiftRequest data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 r) := by
          dsimp only [liftRequest,Option.map_some,freyaLiftRequest]
          congr 2
          funext i
          cases r.pending i with
          | none => rfl
          | some j =>
            dsimp only [Option.map_some,freyaLiftJob]
            cases j.kind <;> rfl
        constructor
        · have hnone := (hs call).1
          change replyAt q O z.1 z.2 call (0,none)=none at hnone
          change Option.map _ (replyAt q O z.1 z.2 call (0,none))=none
          rw [hnone]
          rfl
        · intro r hr
          let R := freyaLiftRequest data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 r
          obtain ⟨i,j,c,hj,ha,hc,hend⟩ := (hs call).2 R
            (freyaLiftLegal _ _ _ _ τ r hr)
          obtain ⟨k,hk,hkj⟩ := Option.map_eq_some_iff.mp hj
          subst j
          change data.2.2.2.1+r.clock≤c at hc
          change replyAt q O z.1 z.2 call (0,some R)=some
            (i,data.2.2.2.2+k.id,c,jobValue f (freyaLiftJob data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 k)) at ha
          have ht : data.2.2.2.1≤c := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤r.clock from bot_le)).trans hc
          refine ⟨i,k,c-data.2.2.2.1,hk,?_,?_,?_⟩
          · change Option.map (fun t : Fin q.n × ℕ × ℝ≥0 × Space q.d =>
              (t.1,t.2.1-data.2.2.2.2,t.2.2.1-data.2.2.2.1,(0 : Space q.d)))
              (replyAt q O z.1 z.2 call (0,liftRequest q O batch z (some r)))=_
            rw [hlift]
            change Option.map _ (replyAt q O z.1 z.2 call (0,some R))=_
            rw [ha]
            dsimp only [Option.map_some]
            rw [Nat.add_sub_cancel_left,freyaZeroJobValue]
          · exact (le_tsub_iff_right ht).mpr (by simpa (config := { iota := false }) only [add_comm] using hc)
          · intro i' k' hk'
            have h := hend i' (freyaLiftJob data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 k')
              (by simp (config := { iota := false }) [R,freyaLiftRequest,hk'])
            rw [freyaLiftDeadline] at h
            have he : (c : ℝ≥0∞)=data.2.2.2.1+(c-data.2.2.2.1 : ℝ≥0) := by
              rw [← ENNReal.coe_add,add_tsub_cancel_of_le ht]
            rw [he] at h
            exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).mp h
      let freyaFullCorresponds {d m n : ℕ} (x : Space d) (t : ℝ≥0) (b : ℕ)
          (s c : FullState d m n) : Prop :=
        s.original=c.original ∧ s.remaining=c.remaining ∧ s.point=x ∧
          s.pending=(fun i => (c.pending i).map (freyaLiftJob x x t b)) ∧
          s.clock=t+c.clock ∧ (∀ k,c.rows k=s.rows (b+k)) ∧ s.nextID=b+c.nextID
      have freyaLiftDispatch {d m : ℕ} (x y : Space d) (t u : ℝ≥0) (b k : ℕ)
          (label : Option (Fin m)) :
          (dispatch (Sum.inl y) u k label).map (freyaLiftJob x x t b)=
            dispatch (Sum.inl x) (t+u) (b+k) label := by
        clear * - d m x y t u b k label freyaLiftJob
        cases label <;> rfl
      have freyaFullInitialCorresponds {d m : ℕ} (n : ℕ) (labels : List (Fin m))
          (x : Space d) (t : ℝ≥0) (rows : ℕ → ChoiceRow) (b : ℕ) :
          freyaFullCorresponds x t b (fullInitial n labels x t rows b)
            (fullInitial n labels (0 : Space d) 0 (fun k => rows (b+k))) := by
        clear * - d m n labels x t rows b freyaFullCorresponds freyaLiftDispatch
        refine ⟨rfl,rfl,rfl,?_,by dsimp only [fullInitial]; simp (config := { iota := false }),?_,by dsimp only [fullInitial]; simp (config := { iota := false })⟩
        · funext i
          dsimp only [fullInitial]
          rw [freyaLiftDispatch]
          simp (config := { iota := false }) only [Nat.zero_add,add_zero]
        · intro k
          rfl
      have freyaFullUpdateCorresponds {d m n : ℕ} (x : Space d) (t : ℝ≥0) (b : ℕ)
          (s c : FullState d m n) (h : freyaFullCorresponds x t b s c)
          (i : Fin n) (j : Job d m) (u : ℝ≥0) (v : Space d)
          (hj : c.pending i=some j) (hu : t+c.clock≤u) :
          freyaFullCorresponds x t b
            (fullUpdate s (some (i,b+j.id,u,v)))
            (fullUpdate c (some (i,j.id,u-t,0))) := by
        clear * - d m n x t b s c h i j u v hj hu freyaLiftJob freyaFullCorresponds freyaLiftDispatch
        classical
        obtain ⟨ho,hr,hx,hp,hc,hrows,hid⟩ := h
        have ht : t≤u := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤c.clock from bot_le)).trans hu
        have hcu : c.clock≤u-t := (le_tsub_iff_right ht).mpr (by simpa (config := { iota := false }) only [add_comm] using hu)
        have hsjob : s.pending i=some (freyaLiftJob x x t b j) := by
          rw [hp]
          dsimp only
          rw [hj]
          rfl
        by_cases he : c.remaining.isEmpty=true
        · have hse : s.remaining.isEmpty=true := hr ▸ he
          dsimp only [fullUpdate]
          rw [ite_eq_left he,ite_eq_left hse]
          exact ⟨ho,hr,hx,hp,hc,hrows,hid⟩
        · have hse : s.remaining.isEmpty≠true := hr ▸ he
          have hacc : b+j.id=(freyaLiftJob x x t b j).id ∧ s.clock≤u := ⟨rfl,hc ▸ hu⟩
          have hacc' : j.id=j.id ∧ c.clock≤u-t := ⟨rfl,hcu⟩
          dsimp only [fullUpdate]
          rw [ite_eq_right hse,ite_eq_right he,hsjob,hj]
          dsimp only
          rw [ite_eq_left hacc,ite_eq_left hacc']
          have hfound : (s.remaining.find? fun a => decide (s.original[a]?=some (freyaLiftJob x x t b j).component))=
              (c.remaining.find? fun a => decide (c.original[a]?=some j.component)) := by
            change (s.remaining.find? fun a => decide (s.original[a]?=some j.component))=_
            rw [hr,ho]
          dsimp only [freyaFullCorresponds]
          rw [hfound,hr,ho]
          refine ⟨rfl,rfl,hx,?_,?_,hrows,?_⟩
          · funext k
            by_cases hk : k=i
            · subst k
              simp (config := { iota := false }) only [Function.update_self]
              rw [freyaLiftDispatch,hx,hid,hrows,add_tsub_cancel_of_le ht]
            · simp (config := { iota := false }) only [Function.update_of_ne hk]
              exact congrFun hp k
          · exact (add_tsub_cancel_of_le ht).symm
          · omega
      let freyaDifferenceCorresponds {d m n : ℕ} (x y : Space d) (t : ℝ≥0) (b : ℕ)
          (s c : DifferenceState d m n) : Prop :=
        s.target=c.target ∧ s.count=c.count ∧ s.x=x ∧ s.y=y ∧
          s.pending=(fun i => (c.pending i).map (freyaLiftJob x y t b)) ∧
          s.clock=t+c.clock ∧ (∀ k,c.rows k=s.rows (b+k)) ∧ s.nextID=b+c.nextID
      have freyaLiftDifferenceDispatch {d m : ℕ} (x y u v : Space d) (t c : ℝ≥0) (b k : ℕ)
          (label : Option (Fin m)) :
          (dispatch (Sum.inr (u,v)) c k label).map (freyaLiftJob x y t b)=
            dispatch (Sum.inr (x,y)) (t+c) (b+k) label := by
        clear * - d m x y u v t c b k label freyaLiftJob
        cases label <;> rfl
      have freyaDifferenceInitialCorresponds {d m : ℕ} (n S : ℕ)
          (x y : Space d) (t : ℝ≥0) (rows : ℕ → ChoiceRow) (b : ℕ) :
          freyaDifferenceCorresponds (m:=m) x y t b (differenceInitial n S x y t rows b)
            (differenceInitial n S (0 : Space d) 0 0 (fun k => rows (b+k))) := by
        clear * - d m n S x y t rows b freyaDifferenceCorresponds freyaLiftDifferenceDispatch
        refine ⟨rfl,rfl,rfl,rfl,?_,by dsimp only [differenceInitial]; simp (config := { iota := false }),?_,by dsimp only [differenceInitial]; simp (config := { iota := false })⟩
        · funext i
          dsimp only [differenceInitial]
          by_cases he : S=0
          · simp (config := { iota := false }) only [ite_eq_left he,Option.map_none]
          · rw [ite_eq_right he,ite_eq_right he,freyaLiftDifferenceDispatch]
            simp (config := { iota := false }) only [Nat.zero_add,add_zero]
        · intro k
          rfl
      have freyaDifferenceUpdateCorresponds {d m n : ℕ} (x y : Space d) (t : ℝ≥0) (b : ℕ)
          (s c : DifferenceState d m n) (h : freyaDifferenceCorresponds x y t b s c)
          (i : Fin n) (j : Job d m) (u : ℝ≥0) (v : Space d)
          (hj : c.pending i=some j) (hu : t+c.clock≤u) :
          freyaDifferenceCorresponds x y t b
            (differenceUpdate s (some (i,b+j.id,u,v)))
            (differenceUpdate c (some (i,j.id,u-t,0))) := by
        clear * - d m n x y t b s c h i j u v hj hu freyaLiftJob freyaDifferenceCorresponds freyaLiftDifferenceDispatch
        classical
        obtain ⟨htarget,hcount,hx,hy,hp,hc,hrows,hid⟩ := h
        have ht : t≤u := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤c.clock from bot_le)).trans hu
        have hcu : c.clock≤u-t := (le_tsub_iff_right ht).mpr (by simpa (config := { iota := false }) only [add_comm] using hu)
        have hsjob : s.pending i=some (freyaLiftJob x y t b j) := by
          rw [hp]
          dsimp only
          rw [hj]
          rfl
        by_cases he : c.target≤c.count
        · have hse : s.target≤s.count := by rwa [htarget,hcount]
          dsimp only [differenceUpdate]
          rw [ite_eq_left he,ite_eq_left hse]
          exact ⟨htarget,hcount,hx,hy,hp,hc,hrows,hid⟩
        · have hse : ¬s.target≤s.count := by rwa [htarget,hcount]
          have hacc : b+j.id=(freyaLiftJob x y t b j).id ∧ s.clock≤u := ⟨rfl,hc ▸ hu⟩
          have hacc' : j.id=j.id ∧ c.clock≤u-t := ⟨rfl,hcu⟩
          dsimp only [differenceUpdate]
          rw [ite_eq_right hse,ite_eq_right he,hsjob,hj]
          dsimp only
          rw [ite_eq_left hacc,ite_eq_left hacc']
          dsimp only [freyaDifferenceCorresponds]
          refine ⟨htarget,by omega,hx,hy,?_,?_,hrows,by omega⟩
          · funext k
            by_cases hk : k=i
            · subst k
              simp (config := { iota := false }) only [Function.update_self]
              rw [freyaLiftDifferenceDispatch,hx,hy,hid,hrows,add_tsub_cancel_of_le ht]
            · simp (config := { iota := false }) only [Function.update_of_ne hk]
              exact congrFun hp k
          · exact (add_tsub_cancel_of_le ht).symm
      have freyaPendingRequestLift {d m n : ℕ} (x y : Space d) (t c : ℝ≥0) (b : ℕ)
          (p : Fin n → Option (Job d m)) :
          pendingRequest (t+c) (fun i => (p i).map (freyaLiftJob x y t b))=
            (pendingRequest c p).map (freyaLiftRequest x y t b) := by
        clear * - d m n x y t c b p freyaLiftJob freyaLiftRequest
        classical
        have he : (∃ i,(p i).map (freyaLiftJob x y t b)≠none) ↔ ∃ i,p i≠none := by simp (config := { iota := false })
        dsimp only [pendingRequest]
        by_cases hp : ∃ i,p i≠none
        · rw [ite_eq_left (he.mpr hp),ite_eq_left hp]
          rfl
        · rw [ite_eq_right (fun h => hp (he.mp h)),ite_eq_right hp]
          rfl
      have freyaFullQueryCorresponds {d m n : ℕ} (x : Space d) (t : ℝ≥0) (b : ℕ)
          (s c : FullState d m n) (h : freyaFullCorresponds x t b s c) :
          fullQuery s=(fullQuery c).map (freyaLiftRequest x x t b) := by
        clear * - d m n x t b s c h freyaLiftRequest freyaFullCorresponds freyaPendingRequestLift
        classical
        obtain ⟨_,hr,_,hp,hc,_,_⟩ := h
        dsimp only [fullQuery]
        rw [hr]
        by_cases he : c.remaining.isEmpty=true
        · rw [ite_eq_left he,ite_eq_left he]
          rfl
        · rw [ite_eq_right he,ite_eq_right he,hc,hp,freyaPendingRequestLift]
      have freyaDifferenceQueryCorresponds {d m n : ℕ} (x y : Space d) (t : ℝ≥0) (b : ℕ)
          (s c : DifferenceState d m n) (h : freyaDifferenceCorresponds x y t b s c) :
          differenceQuery s=(differenceQuery c).map (freyaLiftRequest x y t b) := by
        clear * - d m n x y t b s c h freyaLiftRequest freyaDifferenceCorresponds freyaPendingRequestLift
        classical
        obtain ⟨ht,hcount,_,_,hp,hc,_,_⟩ := h
        dsimp only [differenceQuery]
        rw [ht,hcount]
        by_cases he : c.target≤c.count
        · rw [ite_eq_left he,ite_eq_left he]
          rfl
        · rw [ite_eq_right he,ite_eq_right he,hc,hp,freyaPendingRequestLift]
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
      have freyaPageFreshFull (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (x y : Space q.d) (clock : ℝ≥0)
          (h : invocation q O seed ω batch=some (true,x,y,clock,firstID)) :
          y=x ∧ ∃ call first,batchStartCall q O seed ω batch=some call ∧
            (trace q O seed ω call).phase=Phase.full first
              (fullInitial q.n (List.ofFn id) x clock (seed.1 batch) firstID) := by
        clear * - q O seed ω batch firstID x y clock h freyaPageTraceSeed freyaPageBatchStartFacts freyaPageFullInvocation freyaPageFullEntryAdvance freyaPageAdvanceFull
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
      have freyaInvocationClock (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
          (full : Bool) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O seed ω batch=some (full,x,y,clock,firstID)) :
          (batchClock q O seed ω batch).getD 0=clock := by
        clear * - q O seed ω batch firstID full x y clock hi freyaClockConsistent freyaTraceClockConsistent
        delta invocation at hi
        cases hc : batchStartCall q O seed ω batch with
        | none => rw [hc] at hi; cases hi
        | some call =>
          rw [hc] at hi
          dsimp only [Option.bind_some] at hi
          have hs := freyaTraceClockConsistent q O seed ω call
          dsimp only [batchClock]
          rw [hc]
          dsimp only [Option.map_some,Option.getD_some]
          dsimp only [freyaClockConsistent] at hs
          cases hp : (trace q O seed ω call).phase with
          | halted => rw [hp] at hi; cases hi
          | full first c =>
            rw [hp] at hi hs
            cases hi
            exact hs
          | difference c =>
            rw [hp] at hi hs
            cases hi
            exact hs
      have freyaRestartReply (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) (batch firstID call a : ℕ)
          (full : Bool) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O z.1 z.2 batch=some (full,x,y,clock,firstID))
          (hc : batchStartCall q O z.1 z.2 batch=some call)
          (request : Option (Request q.d q.m q.n)) (i : Fin q.n) (id : ℕ)
          (time : ℝ≥0) (value : Space q.d)
          (hr : replyAt q O z.1 z.2 (call+a) (0,request.map (freyaLiftRequest x y clock firstID))=some (i,firstID+id,time,value)) :
          restartAnswer q O batch a request z=some (i,id,time-clock,0) := by
        clear * - q O z batch firstID call a full x y clock hi hc request i id time value hr freyaLiftJob freyaLiftRequest
        have hd : invocationData q O batch z=(full,x,y,clock,firstID) := by
          dsimp only [invocationData]
          rw [hi]
          rfl
        have hl : liftRequest q O batch z request=request.map (freyaLiftRequest x y clock firstID) := by
          dsimp only [liftRequest]
          rw [hd]
          cases request with
          | none => rfl
          | some r =>
            dsimp only [Option.map_some,freyaLiftRequest]
            congr 2
            funext k
            cases r.pending k with
            | none => rfl
            | some j =>
              dsimp only [Option.map_some,freyaLiftJob]
              cases j.kind <;> rfl
        dsimp only [restartAnswer]
        rw [hd,hc]
        dsimp only [Option.getD_some]
        rw [hl,hr]
        simp (config := { iota := false }) only [Option.map_some,Nat.add_sub_cancel_left]
        rfl
      have freyaRestartRowsAt (q : Raw)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k)) (batch firstID : ℕ)
          (full : Bool) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O z.1 z.2 batch=some (full,x,y,clock,firstID)) :
          restartedRows q O batch z=fun k => z.1.1 batch (firstID+k) := by
        clear * - q O z batch firstID full x y clock hi
        funext k
        dsimp only [restartedRows,invocationData]
        rw [hi]
        rfl
      have freyaDifferenceBatchCorresponds (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID call : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O z.1 z.2 batch=some (false,x,y,clock,firstID))
          (hstart : batchStartCall q O z.1 z.2 batch=some call)
          (hphase : (trace q O z.1 z.2 call).phase=Phase.difference
            (differenceInitial q.n q.S x y clock (z.1.1 batch) firstID)) :
          ∀ a, a<q.S → ∃ c,
            (trace q O z.1 z.2 (call+a)).phase=Phase.difference c ∧
            freyaDifferenceCorresponds x y clock firstID c
              (differenceTrace q.n q.S 0 0 0 (restartedRows q O batch z)
                (fun a r => restartAnswer q O batch a r z) a) := by
        clear * - q hm hn hS f τ O z hs batch firstID call x y clock hi hstart hphase freyaDifferenceLiveStep freyaPageDifferenceQuery freyaPageDifferenceContinue freyaPageBatchProgress freyaLiftJob freyaDifferenceCorresponds freyaDifferenceInitialCorresponds freyaDifferenceUpdateCorresponds freyaDifferenceQueryCorresponds freyaRestartReply freyaRestartRowsAt
        intro a
        induction a with
        | zero =>
          intro _
          refine ⟨_,by simpa (config := { iota := false }) only [Nat.add_zero] using hphase,?_⟩
          dsimp only [differenceTrace]
          rw [freyaRestartRowsAt q O z batch firstID false x y clock hi]
          exact freyaDifferenceInitialCorresponds q.n q.S x y clock (z.1.1 batch) firstID
        | succ a ih =>
          intro ha
          obtain ⟨s,hp,hcorr⟩ := ih (by omega)
          obtain ⟨s',hp',hit,ht,hcount,hx,hy,_,_,_,hpending⟩ :=
            freyaPageBatchProgress q hm hn hS f τ O z.1 z.2 hs batch firstID call x y clock
              hstart hphase a (by omega)
          have he : s'=s := Phase.difference.inj (hp'.symm.trans hp)
          subst s'
          have hlegal : ∀ i,∃ j,s.pending i=some j ∧ j.started≤s.clock ∧
            (s.clock : ℝ≥0∞)≤deadline τ j i ∧ j.kind=Sum.inr (s.x,s.y) := by
            intro i
            obtain ⟨j,hj,hb,he,hk,_⟩ := hpending i
            exact ⟨j,hj,hb,he,by simpa (config := { iota := false }) only [hx,hy] using hk⟩
          obtain ⟨i,j,time,next,hj,hquery,hr,htime,_,_,_,_,hu,_⟩ :=
            freyaDifferenceLiveStep hm hn s f τ
              (fun r => replyAt q O z.1 z.2 (call+a) (0,r)) (hs (call+a)).2 (by omega) hlegal
          let c := differenceTrace q.n q.S 0 0 0 (restartedRows q O batch z)
            (fun a r => restartAnswer q O batch a r z) a
          change freyaDifferenceCorresponds x y clock firstID s c at hcorr
          have hjmap : (c.pending i).map (freyaLiftJob x y clock firstID)=some j := by
            rw [← hj]
            exact (congrFun hcorr.2.2.2.2.1 i).symm
          obtain ⟨j',hj',he⟩ := Option.map_eq_some_iff.mp hjmap
          subst j
          have hquerycorr := freyaDifferenceQueryCorresponds x y clock firstID s c hcorr
          have hrestart := freyaRestartReply q O z batch firstID call a false x y clock hi hstart
            (differenceQuery c) i j'.id time (jobValue f (freyaLiftJob x y clock firstID j'))
            (by rw [← hquerycorr]; exact hr)
          have hucorr := freyaDifferenceUpdateCorresponds x y clock firstID s c hcorr i j' time
            (jobValue f (freyaLiftJob x y clock firstID j')) hj'
            (by rw [← hcorr.2.2.2.2.2.1]; exact htime)
          let snew := differenceUpdate s (replyAt q O z.1 z.2 (call+a) (0,differenceQuery s))
          have hcont := freyaPageDifferenceContinue q _ s
            (replyAt q O z.1 z.2 (call+a) (0,differenceQuery s)) hp
            (by rw [hu]; dsimp only; omega)
          refine ⟨snew,?_,?_⟩
          · rw [← Nat.add_assoc]
            change (update q (trace q O z.1 z.2 (call+a))
              (replyAt q O z.1 z.2 (call+a) (query q (trace q O z.1 z.2 (call+a))))).phase=_
            rw [freyaPageDifferenceQuery q _ s hp]
            exact hcont.1
          · change freyaDifferenceCorresponds x y clock firstID snew
              (differenceUpdate c (restartAnswer q O batch a (differenceQuery c) z))
            dsimp only [snew]
            rw [hr,hrestart]
            exact hucorr
      have freyaAdvanceLeaves (q : Raw) (s : State q) :
          (advance q s).iteration≠s.iteration ∨ active (advance q s)=false := by
        clear * - q s
        delta advance
        split
        · exact Or.inr rfl
        · exact Or.inl (Nat.succ_ne_self s.iteration)
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
      have freyaDifferenceBatchElapsed (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O z.1 z.2 batch=some (false,x,y,clock,firstID)) :
          (differenceTrace q.n q.S 0 0 0 (restartedRows q O batch z)
            (fun a r => restartAnswer q O batch a r z) q.S).clock=batchElapsed q O z.1 z.2 batch := by
        clear * - q hm hn hS hK f τ O z hs batch firstID x y clock hi freyaPageFreshDifference freyaDifferenceLiveStep freyaPageDifferenceQuery freyaPageBatchProgress freyaLiftJob freyaDifferenceCorresponds freyaDifferenceUpdateCorresponds freyaDifferenceQueryCorresponds freyaBatchEndExists freyaAdvanceClock freyaInvocationClock freyaRestartReply freyaDifferenceBatchCorresponds freyaAdvanceLeaves freyaBatchEndFromPrefix
        classical
        obtain ⟨call,hstart,hphase⟩ := freyaPageFreshDifference q O z.1 z.2 batch firstID x y clock hi
        let a := q.S-1
        have ha : a<q.S := by dsimp only [a]; omega
        have haS : a+1=q.S := by dsimp only [a]; omega
        obtain ⟨s,hp,hcorr⟩ := freyaDifferenceBatchCorresponds q hm hn hS f τ O z hs
          batch firstID call x y clock hi hstart hphase a ha
        obtain ⟨s',hp',hit,ht,hcount,hx,hy,_,_,_,hpending⟩ :=
          freyaPageBatchProgress q hm hn hS f τ O z.1 z.2 hs batch firstID call x y clock
            hstart hphase a ha
        have he : s'=s := Phase.difference.inj (hp'.symm.trans hp)
        subst s'
        have hlegal : ∀ i,∃ j,s.pending i=some j ∧ j.started≤s.clock ∧
          (s.clock : ℝ≥0∞)≤deadline τ j i ∧ j.kind=Sum.inr (s.x,s.y) := by
          intro i
          obtain ⟨j,hj,hb,he,hk,_⟩ := hpending i
          exact ⟨j,hj,hb,he,by simpa (config := { iota := false }) only [hx,hy] using hk⟩
        obtain ⟨i,j,time,next,hj,hquery,hr,htime,_,_,_,_,hu,_⟩ :=
          freyaDifferenceLiveStep hm hn s f τ
            (fun r => replyAt q O z.1 z.2 (call+a) (0,r)) (hs (call+a)).2 (by omega) hlegal
        let c := differenceTrace q.n q.S 0 0 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) a
        change freyaDifferenceCorresponds x y clock firstID s c at hcorr
        have hjmap : (c.pending i).map (freyaLiftJob x y clock firstID)=some j := by
          rw [← hj]
          exact (congrFun hcorr.2.2.2.2.1 i).symm
        obtain ⟨j',hj',he⟩ := Option.map_eq_some_iff.mp hjmap
        subst j
        have hquerycorr := freyaDifferenceQueryCorresponds x y clock firstID s c hcorr
        have hrestart := freyaRestartReply q O z batch firstID call a false x y clock hi hstart
          (differenceQuery c) i j'.id time (jobValue f (freyaLiftJob x y clock firstID j'))
          (by rw [← hquerycorr]; exact hr)
        have hucorr := freyaDifferenceUpdateCorresponds x y clock firstID s c hcorr i j' time
          (jobValue f (freyaLiftJob x y clock firstID j')) hj'
          (by rw [← hcorr.2.2.2.2.2.1]; exact htime)
        let snew := differenceUpdate s (replyAt q O z.1 z.2 (call+a) (0,differenceQuery s))
        let cnew := differenceTrace q.n q.S 0 0 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) q.S
        have hcnew : freyaDifferenceCorresponds x y clock firstID snew cnew := by
          dsimp only [cnew]
          nth_rw 2 [← haS]
          change freyaDifferenceCorresponds x y clock firstID snew
            (differenceUpdate c (restartAnswer q O batch a (differenceQuery c) z))
          dsimp only [snew]
          rw [hr,hrestart]
          exact hucorr
        let t : State q := {trace q O z.1 z.2 (call+a) with
          g := (trace q O z.1 z.2 (call+a)).g+differenceResult snew
          clock := snew.clock
          nextID := snew.nextID
          phase := Phase.difference snew}
        have hfinal : trace q O z.1 z.2 (call+q.S)=advance q t := by
          rw [← haS,← Nat.add_assoc]
          change update q (trace q O z.1 z.2 (call+a))
            (replyAt q O z.1 z.2 (call+a) (query q (trace q O z.1 z.2 (call+a))))=_
          rw [freyaPageDifferenceQuery q _ s hp]
          dsimp only [update]
          rw [hp]
          dsimp only
          rw [ite_eq_left (show snew.target≤snew.count by dsimp only [snew]; rw [hu]; dsimp only; omega)]
        have hend : batchEndCall q O z.1 z.2 batch=some (call+q.S) := by
          apply freyaBatchEndFromPrefix q O z batch call q.S hS hstart
            (freyaBatchEndExists q hm hn hS hK f τ O z hs batch firstID false x y clock hi)
          · intro k hk
            obtain ⟨s,hp,hit,_⟩ := freyaPageBatchProgress q hm hn hS f τ O z.1 z.2 hs
              batch firstID call x y clock hstart hphase k hk
            exact ⟨hit,by dsimp only [active]; rw [hp]⟩
          · rw [hfinal]
            have htit : t.iteration=batch := hit
            rw [← htit]
            exact freyaAdvanceLeaves q t
        dsimp only [batchElapsed]
        rw [hend,freyaInvocationClock q O z.1 z.2 batch firstID false x y clock hi]
        dsimp only [Option.map_some,Option.getD_some]
        rw [hfinal,freyaAdvanceClock]
        change cnew.clock=snew.clock-clock
        rw [hcnew.2.2.2.2.2.1,add_tsub_cancel_left]
      have freyaFullBatchStep (q : Raw) (hn : 0<q.n)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID call a : ℕ) (x : Space q.d) (clock : ℝ≥0) (first : Bool)
          (hi : invocation q O z.1 z.2 batch=some (true,x,x,clock,firstID))
          (hstart : batchStartCall q O z.1 z.2 batch=some call)
          (s : FullState q.d q.m q.n)
          (hp : (trace q O z.1 z.2 (call+a)).phase=Phase.full first s)
          (hit : (trace q O z.1 z.2 (call+a)).iteration=batch)
          (hcorr : freyaFullCorresponds x clock firstID s
            (fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
              (fun a r => restartAnswer q O batch a r z) a))
          (hne : s.remaining≠[]) :
          ∃ snew,freyaFullCorresponds x clock firstID snew
              (fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
                (fun a r => restartAnswer q O batch a r z) (a+1)) ∧
            (trace q O z.1 z.2 (call+(a+1))).clock=snew.clock ∧
            (snew.remaining≠[] → (trace q O z.1 z.2 (call+(a+1))).phase=Phase.full first snew ∧
              (trace q O z.1 z.2 (call+(a+1))).iteration=batch) ∧
            (snew.remaining=[] → (trace q O z.1 z.2 (call+(a+1))).iteration≠batch ∨
              active (trace q O z.1 z.2 (call+(a+1)))=false) := by
        clear * - q hn f τ O z hs batch firstID call a x clock first hi hstart s hp hit hcorr hne freyaPageFullQuery freyaLiftJob freyaLiftRequest freyaLiftLegal freyaRestartServicePath freyaFullCorresponds freyaFullUpdateCorresponds freyaFullQueryCorresponds freyaAdvanceClock freyaRestartReply freyaAdvanceLeaves
        classical
        let c := fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) a
        change freyaFullCorresponds x clock firstID s c at hcorr
        have hcne : c.remaining≠[] := by rwa [← hcorr.2.1]
        have hcs := full_invariant q.n hn (List.ofFn id) (0 : Space q.d) 0
          (restartedRows q O batch z) (fun (_ : Fin q.m) (_ : Space q.d) => (0 : ℝ)) τ
          (fun a r => restartAnswer q O batch a r z) (freyaRestartServicePath q f τ O z hs batch) a
        have hclegal : legalRequest τ ⟨c.clock,c.pending⟩ := hcs.2.2.2.2.1 hcne
        have hcquery : fullQuery c=some ⟨c.clock,c.pending⟩ := by
          dsimp only [fullQuery]
          rw [ite_eq_right (by simpa (config := { iota := false }) only [List.isEmpty_iff] using hcne)]
          dsimp only [pendingRequest]
          rw [ite_eq_left (by
            obtain ⟨i,j,hj⟩ := hclegal.1
            change c.pending i=some j at hj
            exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩)]
        let R := freyaLiftRequest x x clock firstID ⟨c.clock,c.pending⟩
        obtain ⟨i,j,time,hj,hr,htime,_⟩ := (hs (call+a)).2 R
          (freyaLiftLegal x x clock firstID τ _ hclegal)
        obtain ⟨k,hk,he⟩ := Option.map_eq_some_iff.mp hj
        subst j
        have hquerycorr := freyaFullQueryCorresponds x clock firstID s c hcorr
        have hr' : replyAt q O z.1 z.2 (call+a) (0,fullQuery s)=
            some (i,firstID+k.id,time,jobValue f (freyaLiftJob x x clock firstID k)) := by
          rw [hquerycorr,hcquery]
          exact hr
        have hrestart := freyaRestartReply q O z batch firstID call a true x x clock hi hstart
          (fullQuery c) i k.id time (jobValue f (freyaLiftJob x x clock firstID k))
          (by rw [← hquerycorr]; exact hr')
        have hucorr := freyaFullUpdateCorresponds x clock firstID s c hcorr i k time
          (jobValue f (freyaLiftJob x x clock firstID k)) hk htime
        let snew := fullUpdate s (replyAt q O z.1 z.2 (call+a) (0,fullQuery s))
        have hcnew : freyaFullCorresponds x clock firstID snew
            (fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
              (fun a r => restartAnswer q O batch a r z) (a+1)) := by
          change freyaFullCorresponds x clock firstID snew
            (fullUpdate c (restartAnswer q O batch a (fullQuery c) z))
          dsimp only [snew]
          rw [hr',hrestart]
          exact hucorr
        let t : State q := {trace q O z.1 z.2 (call+a) with
          clock := snew.clock
          nextID := snew.nextID
          phase := Phase.full first snew}
        have hstep : trace q O z.1 z.2 (call+(a+1))=
            if snew.remaining.isEmpty then advance q {t with g := fullResult snew} else t := by
          rw [← Nat.add_assoc]
          change update q (trace q O z.1 z.2 (call+a))
            (replyAt q O z.1 z.2 (call+a) (query q (trace q O z.1 z.2 (call+a))))=_
          rw [freyaPageFullQuery q _ first s hp]
          dsimp only [update]
          rw [hp]
        refine ⟨snew,hcnew,?_,?_,?_⟩
        · rw [hstep]
          split
          · exact freyaAdvanceClock q _
          · rfl
        · intro hne
          rw [hstep,ite_eq_right (by simpa (config := { iota := false }) only [List.isEmpty_iff] using hne)]
          exact ⟨rfl,hit⟩
        · intro he
          rw [hstep,ite_eq_left (by rw [he]; rfl)]
          have htit : ({t with g := fullResult snew} : State q).iteration=batch := hit
          exact (freyaAdvanceLeaves q {t with g := fullResult snew}).imp
            (fun h he => h (he.trans htit.symm)) id
      have freyaFullBatchPrefix (q : Raw) (hn : 0<q.n)
          (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID call N : ℕ) (x : Space q.d) (clock : ℝ≥0) (first : Bool)
          (hi : invocation q O z.1 z.2 batch=some (true,x,x,clock,firstID))
          (hstart : batchStartCall q O z.1 z.2 batch=some call)
          (hphase : (trace q O z.1 z.2 call).phase=Phase.full first
            (fullInitial q.n (List.ofFn id) x clock (z.1.1 batch) firstID))
          (hnon : ∀ a<N,(fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
            (fun a r => restartAnswer q O batch a r z) a).remaining≠[]) :
          ∀ a<N,∃ s,(trace q O z.1 z.2 (call+a)).phase=Phase.full first s ∧
            (trace q O z.1 z.2 (call+a)).iteration=batch ∧
            freyaFullCorresponds x clock firstID s
              (fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
                (fun a r => restartAnswer q O batch a r z) a) := by
        clear * - q hn f τ O z hs batch firstID call N x clock first hi hstart hphase hnon freyaPageBatchStartFacts freyaFullCorresponds freyaFullInitialCorresponds freyaRestartRowsAt freyaFullBatchStep
        intro a
        induction a with
        | zero =>
          intro _
          refine ⟨_,by simpa (config := { iota := false }) only [Nat.add_zero] using hphase,?_,?_⟩
          · simpa (config := { iota := false }) only [Nat.add_zero] using (freyaPageBatchStartFacts q O z.1 z.2 batch call hstart).2.1
          · dsimp only [fullTrace]
            rw [freyaRestartRowsAt q O z batch firstID true x x clock hi]
            exact freyaFullInitialCorresponds q.n (List.ofFn id) x clock (z.1.1 batch) firstID
        | succ a ih =>
          intro ha
          obtain ⟨s,hp,hit,hcorr⟩ := ih (by omega)
          have hne : s.remaining≠[] := by rw [hcorr.2.1]; exact hnon a (by omega)
          obtain ⟨snew,hcorrnew,_,hcont,_⟩ := freyaFullBatchStep q hn f τ O z hs
            batch firstID call a x clock first hi hstart s hp hit hcorr hne
          have hnewne : snew.remaining≠[] := by rw [hcorrnew.2.1]; exact hnon (a+1) ha
          exact ⟨snew,(hcont hnewne).1,(hcont hnewne).2,hcorrnew⟩
      have freyaFullTraceStable {d m : ℕ} (n : ℕ) (labels : List (Fin m))
          (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
          (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ)
          (h : (fullTrace n labels x start rows answer a).remaining=[]) (b : ℕ) :
          fullTrace n labels x start rows answer (a+b)=fullTrace n labels x start rows answer a := by
        clear * - d m n labels x start rows answer a h b
        induction b with
        | zero => rfl
        | succ b ih =>
          rw [← Nat.add_assoc]
          change fullUpdate (fullTrace n labels x start rows answer (a+b))
            (answer (a+b) (fullQuery (fullTrace n labels x start rows answer (a+b))))=_
          rw [ih]
          dsimp only [fullUpdate]
          rw [ite_eq_left (by rw [h]; rfl)]
      have freyaFullBatchElapsed (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
          (hi : invocation q O z.1 z.2 batch=some (true,x,y,clock,firstID)) :
          (fullTrace q.n (List.ofFn id) 0 0 (restartedRows q O batch z)
            (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock=batchElapsed q O z.1 z.2 batch := by
        clear * - q hm hn hS hK f τ O z hs batch firstID x y clock hi freyaRestartServicePath freyaBatchEndExists freyaPageFreshFull freyaInvocationClock freyaBatchEndFromPrefix freyaFullBatchStep freyaFullBatchPrefix freyaFullTraceStable
        classical
        obtain ⟨hy,call,first,hstart,hphase⟩ := freyaPageFreshFull q O z.1 z.2 batch firstID x y clock hi
        subst y
        let C := fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z)
        have hfinish : (C (q.n*q.m)).remaining=[] := by
          have h := (full_event_bound q.n hn (List.ofFn id) (0 : Space q.d) 0
            (restartedRows q O batch z) (fun (_ : Fin q.m) (_ : Space q.d) => (0 : ℝ)) τ
            (fun a r => restartAnswer q O batch a r z) (freyaRestartServicePath q f τ O z hs batch)).1
          simpa (config := { iota := false }) only [List.length_ofFn] using h
        have hex : ∃ a,(C a).remaining=[] := ⟨q.n*q.m,hfinish⟩
        let N := Nat.find hex
        have hdone : (C N).remaining=[] := Nat.find_spec hex
        have hnon : ∀ a<N,(C a).remaining≠[] := fun a ha => Nat.find_min hex ha
        have hN : 0<N := by
          by_contra hn
          have he : N=0 := by omega
          rw [he] at hdone
          have hlen := congrArg List.length hdone
          dsimp only [C,fullTrace,fullInitial] at hlen
          simp (config := { iota := false }) only [List.length_range,List.length_ofFn,List.length_nil] at hlen
          omega
        have hNle : N≤q.n*q.m := Nat.find_min' hex hfinish
        have hprefix := freyaFullBatchPrefix q hn f τ O z hs batch firstID call N x clock first
          hi hstart hphase hnon
        let a := N-1
        have ha : a<N := Nat.sub_lt hN Nat.zero_lt_one
        have haN : a+1=N := Nat.sub_add_cancel hN
        obtain ⟨s,hp,hit,hcorr⟩ := hprefix a ha
        have hne : s.remaining≠[] := by rw [hcorr.2.1]; exact hnon a ha
        obtain ⟨snew,hcorrnew,hclock,hcont,hleave⟩ := freyaFullBatchStep q hn f τ O z hs
          batch firstID call a x clock first hi hstart s hp hit hcorr hne
        rw [haN] at hcorrnew hclock hcont hleave
        have hnewdone : snew.remaining=[] := hcorrnew.2.1.trans hdone
        have hend : batchEndCall q O z.1 z.2 batch=some (call+N) := by
          apply freyaBatchEndFromPrefix q O z batch call N hN hstart
            (freyaBatchEndExists q hm hn hS hK f τ O z hs batch firstID true x x clock hi)
          · intro k hk
            obtain ⟨s,hp,hit,_⟩ := hprefix k hk
            exact ⟨hit,by dsimp only [active]; rw [hp]⟩
          · exact hleave hnewdone
        have hstable : C (q.n*q.m)=C N := by
          have h := freyaFullTraceStable q.n (List.ofFn id) (0 : Space q.d) 0
            (restartedRows q O batch z) (fun a r => restartAnswer q O batch a r z) N hdone (q.n*q.m-N)
          simpa (config := { iota := false }) only [Nat.add_sub_of_le hNle] using h
        change (C (q.n*q.m)).clock=_
        rw [hstable]
        dsimp only [batchElapsed]
        rw [hend,freyaInvocationClock q O z.1 z.2 batch firstID true x x clock hi]
        dsimp only [Option.map_some,Option.getD_some]
        rw [hclock,hcorrnew.2.2.2.2.1,add_tsub_cancel_left]
      have freyaRestartCoupling (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hservice : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)))
          (batch firstID : ℕ) (full : Bool) (x y : Space q.d) (clock : ℝ≥0)
          (hinvoke : invocation q O z.1 z.2 batch=some (full,x,y,clock,firstID)) :
          (batchEndCall q O z.1 z.2 batch).isSome ∧
            (if full then
              (fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
                (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock
            else
              (differenceTrace q.n q.S (0 : Space q.d) 0 0 (restartedRows q O batch z)
                (fun a r => restartAnswer q O batch a r z) q.S).clock)=
              batchElapsed q O z.1 z.2 batch := by
        clear * - q hm hn hS hK f τ O z hservice batch firstID full x y clock hinvoke freyaBatchEndExists freyaDifferenceBatchElapsed freyaFullBatchElapsed
        refine ⟨freyaBatchEndExists q hm hn hS hK f τ O z hservice batch firstID full x y clock hinvoke,?_⟩
        cases full with
        | false => exact freyaDifferenceBatchElapsed q hm hn hS hK f τ O z hservice batch firstID x y clock hinvoke
        | true => exact freyaFullBatchElapsed q hm hn hS hK f τ O z hservice batch firstID x y clock hinvoke
      exact freyaRestartCoupling q hm hn hS hK f τ O z hservice batch firstID full x y clock hinvoke


theorem restart_service (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (batch : ℕ)
    (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
    (hEmeas : MeasurableSet[InvocationHistory q O batch] E)
    (hinvoke : ∀ z ∈ E, (invocation q O z.1 z.2 batch).isSome)
    (hE : (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) E ≠ 0) :
    PrimitiveService (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ (restartOracle q O batch E hE) ∧
      LiveService τ (restartOracle q O batch E hE) ∧
      InvocationHistory q O batch ≤
        (inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))) ∧
      Measurable[InvocationHistory q O batch] (invocationData q O batch) ∧
      FullFresh (restrictedProbability (executionLaw q O) E hE)
        q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch)
        (restartAnswer q O batch) := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 4096 in
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    run_tac
      let env ← Lean.getEnv
      let parsed := Lean.Parser.runParserCategory env `tactic r#"all_goals
  classical
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
  have freyaInvocationDataHistoryMeas (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
      Measurable[InvocationHistory q O batch] (invocationData q O batch) := by
    clear * - q O batch freyaDevelopmentOptionElimMeas freyaPageInvocationHistoryMeas

    have h := (freyaDevelopmentOptionElimMeas (true,(0 : Space q.d),0,(0 : ℝ≥0),(0 : ℕ))
      id measurable_id).comp (freyaPageInvocationHistoryMeas q O batch)
    convert h using 1
    funext z
    dsimp only [invocationData,Function.comp_def]
    cases invocation q O z.1 z.2 batch <;> rfl
  let freyaLiftJob {d m : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ) (j : Job d m) : Job d m :=
    { j with kind := Sum.elim (fun _ => Sum.inl x) (fun _ => Sum.inr (x,y)) j.kind
             started := clock+j.started
             id := first+j.id }
  let freyaLiftRequest {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
      (r : Request d m n) : Request d m n :=
    ⟨clock+r.clock,fun i => (r.pending i).map (freyaLiftJob x y clock first)⟩
  have freyaLiftDeadline {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
      (τ : Fin n → ℝ≥0∞) (j : Job d m) (i : Fin n) :
      deadline τ (freyaLiftJob x y clock first j) i=clock+deadline τ j i := by
    clear * - d m n x y clock first τ j i freyaLiftJob

    dsimp [deadline,freyaLiftJob,jobWork]
    cases j.kind <;> dsimp only [Sum.elim] <;> simp (config := { iota := false }) [add_assoc]
  have freyaLiftLegal {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
      (τ : Fin n → ℝ≥0∞) (r : Request d m n) (hr : legalRequest τ r) :
      legalRequest τ (freyaLiftRequest x y clock first r) := by
    clear * - d m n x y clock first τ r hr freyaLiftJob freyaLiftRequest freyaLiftDeadline

    obtain ⟨⟨i,j,hj⟩,hr⟩ := hr
    constructor
    · exact ⟨i,freyaLiftJob x y clock first j,by simp (config := { iota := false }) [freyaLiftRequest,hj]⟩
    · intro i j hj
      obtain ⟨k,hk,rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨hstart,hend⟩ := hr i k hk
      constructor
      · exact add_le_add le_rfl hstart
      · rw [freyaLiftDeadline]
        change ((clock+r.clock : ℝ≥0) : ℝ≥0∞)≤(clock : ℝ≥0∞)+deadline τ k i
        rw [ENNReal.coe_add]
        exact add_le_add le_rfl hend
  have freyaZeroJobValue {d m : ℕ} (j : Job d m) :
      jobValue (fun (_ : Fin m) (_ : Space d) => (0 : ℝ)) j=0 := by
    clear * - d m j

    dsimp [jobValue]
    cases j.kind <;> dsimp only <;> simp (config := { iota := false })
  have freyaRestartServicePath (q : Raw) (f : Fin q.m → Space q.d → ℝ)
      (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (z : Seed q.K × ((k : ℕ) → O.Seed k))
      (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r))) (batch : ℕ) :
      servicePath (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ
        (fun a r => restartAnswer q O batch a r z) := by
    clear * - q f τ O z hs batch freyaLiftJob freyaLiftRequest freyaLiftDeadline freyaLiftLegal freyaZeroJobValue

    intro a
    let data := invocationData q O batch z
    let call := (batchStartCall q O z.1 z.2 batch).getD 0+a
    have hlift (r : Request q.d q.m q.n) : liftRequest q O batch z (some r)=
        some (freyaLiftRequest data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 r) := by
      dsimp only [liftRequest,Option.map_some,freyaLiftRequest]
      congr 2
      funext i
      cases r.pending i with
      | none => rfl
      | some j =>
        dsimp only [Option.map_some,freyaLiftJob]
        cases j.kind <;> rfl
    constructor
    · have hnone := (hs call).1
      change replyAt q O z.1 z.2 call (0,none)=none at hnone
      change Option.map _ (replyAt q O z.1 z.2 call (0,none))=none
      rw [hnone]
      rfl
    · intro r hr
      let R := freyaLiftRequest data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 r
      obtain ⟨i,j,c,hj,ha,hc,hend⟩ := (hs call).2 R
        (freyaLiftLegal _ _ _ _ τ r hr)
      obtain ⟨k,hk,hkj⟩ := Option.map_eq_some_iff.mp hj
      subst j
      change data.2.2.2.1+r.clock≤c at hc
      change replyAt q O z.1 z.2 call (0,some R)=some
        (i,data.2.2.2.2+k.id,c,jobValue f (freyaLiftJob data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 k)) at ha
      have ht : data.2.2.2.1≤c := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤r.clock from bot_le)).trans hc
      refine ⟨i,k,c-data.2.2.2.1,hk,?_,?_,?_⟩
      · change Option.map (fun t : Fin q.n × ℕ × ℝ≥0 × Space q.d =>
          (t.1,t.2.1-data.2.2.2.2,t.2.2.1-data.2.2.2.1,(0 : Space q.d)))
          (replyAt q O z.1 z.2 call (0,liftRequest q O batch z (some r)))=_
        rw [hlift]
        change Option.map _ (replyAt q O z.1 z.2 call (0,some R))=_
        rw [ha]
        dsimp only [Option.map_some]
        rw [Nat.add_sub_cancel_left,freyaZeroJobValue]
      · exact (le_tsub_iff_right ht).mpr (by simpa (config := { iota := false }) only [add_comm] using hc)
      · intro i' k' hk'
        have h := hend i' (freyaLiftJob data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 k')
          (by simp (config := { iota := false }) [R,freyaLiftRequest,hk'])
        rw [freyaLiftDeadline] at h
        have he : (c : ℝ≥0∞)=data.2.2.2.1+(c-data.2.2.2.1 : ℝ≥0) := by
          rw [← ENNReal.coe_add,add_tsub_cancel_of_le ht]
        rw [he] at h
        exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).mp h
  have freyaLiftJobMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
      (x y : Ω → Space d) (t : Ω → ℝ≥0) (b : Ω → ℕ) (j : Ω → Job d m)
      (hx : Measurable x) (hy : Measurable y) (ht : Measurable t) (hb : Measurable b)
      (hj : Measurable j) : Measurable (fun z => freyaLiftJob (x z) (y z) (t z) (b z) (j z)) := by
    clear * - Ω d m x y t b j hx hy ht hb hj freyaJobCodeMeas freyaLiftJob

    have hc := freyaJobCodeMeas.comp hj
    have hf : Measurable (fun z : Ω × Space d => (Sum.inl (x z.1) : JobKind d)) :=
      measurable_inl.comp (hx.comp measurable_fst)
    have hd : Measurable (fun z : Ω × (Space d × Space d) => (Sum.inr (x z.1,y z.1) : JobKind d)) :=
      measurable_inr.comp ((hx.comp measurable_fst).prodMk (hy.comp measurable_fst))
    have hk := ((hf.sumElim hd).comp
      (MeasurableEquiv.prodSumDistrib Ω (Space d) (Space d × Space d)).measurable).comp
        (measurable_id.prodMk hc.snd.fst)
    change Measurable[_,MeasurableSpace.comap (fun j : Job d m => (j.component,j.kind,j.started,j.id)) inferInstance] _
    rw [measurable_comap_iff]
    let G := fun z : Ω => ((j z).component,
      Sum.elim (fun _ : Space d => Sum.inl (x z))
        (fun _ : Space d × Space d => Sum.inr (x z,y z)) (j z).kind,
      t z+(j z).started,b z+(j z).id)
    have he : ((fun j : Job d m => (j.component,j.kind,j.started,j.id)) ∘
        fun z => freyaLiftJob (x z) (y z) (t z) (b z) (j z))=G := by
      funext z
      dsimp only [G,Function.comp_def,freyaLiftJob]
      cases (j z).kind <;> rfl
    rw [he]
    have hk' : Measurable (fun z => Sum.elim (fun _ : Space d => Sum.inl (x z))
        (fun _ : Space d × Space d => Sum.inr (x z,y z)) (j z).kind) := by
      convert hk using 1
      funext z
      dsimp only [Function.comp_def]
      cases (j z).kind <;> rfl
    exact hc.fst.prodMk (hk'.prodMk ((ht.add hc.snd.snd.fst).prodMk (hb.add hc.snd.snd.snd)))
  have freyaLiftRequestMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
      (x y : Ω → Space d) (t : Ω → ℝ≥0) (b : Ω → ℕ) (r : Ω → Request d m n)
      (hx : Measurable x) (hy : Measurable y) (ht : Measurable t) (hb : Measurable b)
      (hr : Measurable r) : Measurable (fun z => freyaLiftRequest (x z) (y z) (t z) (b z) (r z)) := by
    clear * - Ω d m n x y t b r hx hy ht hb hr freyaOptionSomeMeas freyaOptionParamMeas freyaLiftJob freyaLiftRequest freyaLiftJobMeas

    have hc : Measurable (fun z => ((r z).clock,(r z).pending)) :=
      (show Measurable (fun r : Request d m n => (r.clock,r.pending)) from
        Measurable.of_comap_le le_rfl).comp hr
    have hp : Measurable (fun z => fun i => ((r z).pending i).map (freyaLiftJob (x z) (y z) (t z) (b z))) := by
      apply Measurable.of_eval
      intro i
      have h := freyaOptionParamMeas _ ((measurable_pi_apply i).comp hc.snd)
        (fun _ : Ω => (none : Option (Job d m))) measurable_const
        (fun z : Ω × Job d m => some (freyaLiftJob (x z.1) (y z.1) (t z.1) (b z.1) z.2))
        (freyaOptionSomeMeas.comp (freyaLiftJobMeas _ _ _ _ _
          (hx.comp measurable_fst) (hy.comp measurable_fst) (ht.comp measurable_fst)
          (hb.comp measurable_fst) measurable_snd))
      convert h using 1
      funext z
      dsimp only [Function.comp_def]
      cases (r z).pending i <;> rfl
    change Measurable[_,MeasurableSpace.comap (fun r : Request d m n => (r.clock,r.pending)) inferInstance] _
    rw [measurable_comap_iff]
    exact (ht.add hc.fst).prodMk hp
  have freyaRestartRowsMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch : ℕ) : Measurable (restartedRows q O batch) := by
    clear * - q f τ O hservice batch freyaMeasurableSelect freyaHistoryAmbient freyaInvocationDataHistoryMeas

    have hd := (freyaInvocationDataHistoryMeas q O batch).mono
      (freyaHistoryAmbient q f τ O hservice batch) le_rfl
    apply Measurable.of_eval
    intro a
    dsimp only [restartedRows]
    apply freyaMeasurableSelect _ (hd.snd.snd.snd.snd.add_const a) (fun k z => z.1.1 batch k)
    intro k
    exact (measurable_pi_apply k).comp ((measurable_pi_apply batch).comp measurable_fst.fst)
  have freyaLiftRequestAmbientMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch : ℕ) :
      Measurable (fun z : Option (Request q.d q.m q.n) × (Seed q.K × ((k : ℕ) → O.Seed k)) =>
        liftRequest q O batch z.2 z.1) := by
    clear * - q f τ O hservice batch freyaOptionSomeMeas freyaOptionParamMeas freyaHistoryAmbient freyaInvocationDataHistoryMeas freyaLiftJob freyaLiftRequest freyaLiftRequestMeas

    let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
    have hd := ((freyaInvocationDataHistoryMeas q O batch).mono
      (freyaHistoryAmbient q f τ O hservice batch) le_rfl).comp
        (measurable_snd : Measurable (Prod.snd : Option (Request q.d q.m q.n) × Ω → Ω))
    have h := freyaOptionParamMeas _ measurable_fst
      (fun _ : Option (Request q.d q.m q.n) × Ω => (none : Option (Request q.d q.m q.n))) measurable_const
      (fun z : (Option (Request q.d q.m q.n) × Ω) × Request q.d q.m q.n =>
        some (freyaLiftRequest (invocationData q O batch z.1.2).2.1
          (invocationData q O batch z.1.2).2.2.1 (invocationData q O batch z.1.2).2.2.2.1
          (invocationData q O batch z.1.2).2.2.2.2 z.2))
      (freyaOptionSomeMeas.comp (freyaLiftRequestMeas _ _ _ _ _
        (hd.snd.fst.comp measurable_fst) (hd.snd.snd.fst.comp measurable_fst)
        (hd.snd.snd.snd.fst.comp measurable_fst) (hd.snd.snd.snd.snd.comp measurable_fst) measurable_snd))
    convert h using 1
    funext z
    dsimp only [liftRequest]
    cases z.1 with
    | none => rfl
    | some r =>
      dsimp only [Option.map_some,Option.elim_some,freyaLiftRequest]
      congr 2
      funext i
      cases r.pending i with
      | none => rfl
      | some j => dsimp only [Option.map_some,freyaLiftJob]; cases j.kind <;> rfl
  have freyaRestartAnswerMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) :
      Measurable (fun z : Option (Request q.d q.m q.n) × (Seed q.K × ((k : ℕ) → O.Seed k)) =>
        restartAnswer q O batch a z.1 z.2) := by
    clear * - q f τ O hservice batch a freyaDevelopmentOptionElimMeas freyaOptionSomeMeas freyaMeasurableSelect freyaOptionParamMeas freyaPageBatchStartMeas freyaHistoryAmbient freyaInvocationDataHistoryMeas freyaLiftRequestAmbientMeas freyaPageInitialMeas freyaPageUpdateMeas freyaPageQueryMeas

    let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
    let T := Option (Request q.d q.m q.n) × Ω
    have hd := ((freyaInvocationDataHistoryMeas q O batch).mono
      (freyaHistoryAmbient q f τ O hservice batch) le_rfl).comp
        (measurable_snd : Measurable (Prod.snd : T → Ω))
    have hcall : Measurable (fun z : T => (batchStartCall q O z.2.1 z.2.2 batch).getD 0+a) := by
      have h := ((freyaDevelopmentOptionElimMeas (0 : ℕ) id measurable_id).comp
        ((freyaPageBatchStartMeas q f τ O hservice batch).comp
          (measurable_snd : Measurable (Prod.snd : T → Ω)))).add_const a
      convert h using 1
      funext z
      dsimp only [Function.comp_def]
      cases batchStartCall q O z.2.1 z.2.2 batch <;> rfl
    have hr : Measurable (fun z : T =>
        let k := (batchStartCall q O z.2.1 z.2.2 batch).getD 0+a
        replyAt q O z.2.1 z.2.2 k (0,liftRequest q O batch z.2 z.1)) := by
      apply freyaMeasurableSelect _ hcall (fun k z => replyAt q O z.2.1 z.2.2 k (0,liftRequest q O batch z.2 z.1))
      intro k
      exact measurable_replyAt q O hservice.1.2 (freyaPageInitialMeas q) (freyaPageUpdateMeas q)
          (freyaPageQueryMeas q) k measurable_snd
          (measurable_const.prodMk (freyaLiftRequestAmbientMeas q f τ O hservice batch))
    have hbody : Measurable (fun z : T × (Fin q.n × ℕ × ℝ≥0 × Space q.d) =>
        some (z.2.1,z.2.2.1-(invocationData q O batch z.1.2).2.2.2.2,
          z.2.2.2.1-(invocationData q O batch z.1.2).2.2.2.1,(0 : Space q.d))) :=
      freyaOptionSomeMeas.comp (measurable_snd.fst.prodMk
        ((measurable_snd.snd.fst.sub (hd.snd.snd.snd.snd.comp measurable_fst)).prodMk
          ((measurable_snd.snd.snd.fst.sub (hd.snd.snd.snd.fst.comp measurable_fst)).prodMk measurable_const)))
    have h := freyaOptionParamMeas _ hr (fun _ : T => (none : Reply q.d q.n)) measurable_const _ hbody
    let F : T → Reply q.d q.n := fun z =>
      (replyAt q O z.2.1 z.2.2 ((batchStartCall q O z.2.1 z.2.2 batch).getD 0+a) (0,liftRequest q O batch z.2 z.1)).elim none
        (fun t => some (t.1,t.2.1-(invocationData q O batch z.2).2.2.2.2,
          t.2.2.1-(invocationData q O batch z.2).2.2.2.1,0))
    have he : (fun z : T => restartAnswer q O batch a z.1 z.2)=F := by
      funext z
      dsimp only [restartAnswer,F]
      cases replyAt q O z.2.1 z.2.2 ((batchStartCall q O z.2.1 z.2.2 batch).getD 0+a) (0,liftRequest q O batch z.2 z.1) <;> rfl
    rw [he]
    exact h
  have freyaRestartPrimitive (q : Raw) (f : Fin q.m → Space q.d → ℝ)
      (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch : ℕ)
      (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
      (hE : (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))) E≠0) :
      PrimitiveService (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ (restartOracle q O batch E hE) ∧
        LiveService τ (restartOracle q O batch E hE) := by
    clear * - q f τ O hservice batch E hE freyaRestartServicePath freyaRestartAnswerMeas

    let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
    let P := (executionLaw q O : Measure Ω)
    let Q := restrictedProbability (executionLaw q O) E hE
    let R := restartOracle q O batch E hE
    have hs : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
      (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
    have hz : ∀ᵐ z ∂P,servicePath (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ
        (fun a r => restartAnswer q O batch a r z) := by
      filter_upwards [hs] with z hz
      exact freyaRestartServicePath q f τ O z hz batch
    have hrestricted : ∀ᵐ z ∂(Q : Measure Ω),servicePath (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ
        (fun a r => restartAnswer q O batch a r z) :=
      Measure.ae_smul_measure (ae_restrict_of_ae hz) (P E)⁻¹
    have heval (k : ℕ) : (((Q : Measure Ω).map (fun z => fun _ : ℕ => z)).map (fun ω => ω k))=(Q : Measure Ω) := by
      have hdiag : Measurable (fun z : Ω => fun _ : ℕ => z) := Measurable.of_eval (fun _ => measurable_id)
      exact (Measure.map_map (measurable_pi_apply k) hdiag).trans Measure.map_id
    have hprimitive : PrimitiveService (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ R := by
      refine ⟨⟨?_,fun k => ?_⟩,?_⟩
      · intro history other x ω hlen
        change restartAnswer q O batch history.length x.2 (ω history.length)=
          restartAnswer q O batch other.length x.2 (ω other.length)
        rw [hlen]
      · have hg : Measurable (fun z : (HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) k ×
            (Fin 1 × Option (Request q.d q.m q.n))) × Ω => (z.1.2.2, z.2)) :=
          measurable_fst.snd.snd.prodMk measurable_snd
        have h := (freyaRestartAnswerMeas q f τ O hservice batch k).comp hg
        have he : (fun z : (HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) k ×
            (Fin 1 × Option (Request q.d q.m q.n))) × Ω => answerAt R k z.1.1 z.1.2 z.2)=
            (fun z : Option (Request q.d q.m q.n) × Ω => restartAnswer q O batch k z.1 z.2) ∘
              (fun z => (z.1.2.2, z.2)) := by
          funext z
          obtain ⟨⟨⟨history,hlen⟩,x⟩,w⟩ := z
          subst hlen
          rfl
        exact (congrArg Measurable he).mpr h
      · have hk : ∀ k,∀ᵐ ω ∂((Q : Measure Ω).map (fun z => fun _ : ℕ => z)),
            ∀ history : List ((Fin 1 × Option (Request q.d q.m q.n)) × Reply q.d q.n),
              history.length=k →
              restartAnswer q O batch history.length none (ω history.length)=none ∧
              ∀ r,legalRequest τ r → ∃ i j c,r.pending i=some j ∧
                restartAnswer q O batch history.length (some r) (ω history.length)=
                  some (i,j.id,c,jobValue (fun (_ : Fin q.m) (_ : Space q.d) => 0) j) ∧
                r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i' := by
          intro k
          have h : ∀ᵐ z ∂(((Q : Measure Ω).map (fun z => fun _ : ℕ => z)).map (fun ω => ω k)),
              restartAnswer q O batch k none z=none ∧
                ∀ r,legalRequest τ r → ∃ i j c,r.pending i=some j ∧
                  restartAnswer q O batch k (some r) z=
                    some (i,j.id,c,jobValue (fun (_ : Fin q.m) (_ : Space q.d) => 0) j) ∧
                  r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i' := by
            erw [heval k]
            filter_upwards [hrestricted] with z hz
            exact hz k
          filter_upwards [ae_of_ae_map (measurable_pi_apply k).aemeasurable h] with ω hω history hlen
          subst hlen
          exact hω
        filter_upwards [ae_all_iff.mpr hk] with ω hω history
        exact hω history.length history rfl
    exact ⟨hprimitive,finite_completion _ τ R hprimitive⟩
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
  have freyaPageAdvanceSeedCongruence (q : Raw) (s : State q) (new : Seed q.K)
      (batch : ℕ) (hbits : new.2=s.seed.2)
      (hrows : ∀ i,i<batch → new.1 i=s.seed.1 i)
      (hbound : (advance q s).iteration<batch) :
      advance q {s with seed:=new}={advance q s with seed:=new} := by
    clear * - q s new batch hbits hrows hbound

    delta advance at hbound ⊢
    dsimp only
    by_cases hstop : rounds q≤s.iteration
    · simp (config := { iota := false }) only [ite_eq_left hstop]
    · simp (config := { iota := false }) only [ite_eq_right hstop] at hbound ⊢
      have hr : refreshAt new s.iteration=refreshAt s.seed s.iteration :=
        congrArg (fun t => t.1 s.iteration) hbits
      have ho : outputIndex new=outputIndex s.seed := congrArg Prod.snd hbits
      simp (config := { iota := false }) only [hr,ho,hrows (s.iteration+1) hbound]
  have freyaPageUpdateSeedCongruence (q : Raw) (s : State q) (new : Seed q.K)
      (reply : Reply q.d q.n) (batch : ℕ) (hbits : new.2=s.seed.2)
      (hrows : ∀ i,i<batch → new.1 i=s.seed.1 i)
      (hbound : (update q s reply).iteration<batch) :
      update q {s with seed:=new} reply={update q s reply with seed:=new} := by
    clear * - q s new reply batch hbits hrows hbound freyaPageAdvanceSeedCongruence

    delta update at hbound ⊢
    cases hs : s.phase with
    | halted => dsimp only; simp (config := { iota := false }) only [hs]
    | full first c =>
      rw [hs] at hbound
      dsimp only at hbound ⊢
      by_cases he : (fullUpdate c reply).remaining.isEmpty=true
      · simp (config := { iota := false }) only [ite_eq_left he] at hbound ⊢
        exact freyaPageAdvanceSeedCongruence q {s with
          g:=fullResult (fullUpdate c reply)
          clock:=(fullUpdate c reply).clock
          nextID:=(fullUpdate c reply).nextID
          phase:=Phase.full first (fullUpdate c reply)} new batch hbits hrows hbound
      · simp (config := { iota := false }) only [ite_eq_right he]
    | difference c =>
      rw [hs] at hbound
      dsimp only at hbound ⊢
      by_cases he : (differenceUpdate c reply).target≤(differenceUpdate c reply).count
      · simp (config := { iota := false }) only [ite_eq_left he] at hbound ⊢
        exact freyaPageAdvanceSeedCongruence q {s with
          g:=s.g+differenceResult (differenceUpdate c reply)
          clock:=(differenceUpdate c reply).clock
          nextID:=(differenceUpdate c reply).nextID
          phase:=Phase.difference (differenceUpdate c reply)} new batch hbits hrows hbound
      · simp (config := { iota := false }) only [ite_eq_right he]
  have freyaPageInitialSeedCongruence (q : Raw) (seed new : Seed q.K)
      (hrows : new.1 0=seed.1 0) :
      initial q new={initial q seed with seed:=new} := by
    clear * - q seed new hrows

    delta initial
    rw [hrows]
  have freyaPageSeedQuery (q : Raw) (s : State q) (new : Seed q.K) :
      query q {s with seed:=new}=query q s := by
    clear * - q s new
    rfl
  have freyaPageEarlierActive (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (a b : ℕ) (hab : a≤b)
      (hb : active (trace q O seed ω b)=true) : active (trace q O seed ω a)=true := by
    clear * - q O seed ω a b hab hb freyaPageHaltedUpdate

    by_contra h
    have ha : active (trace q O seed ω a)=false := Bool.eq_false_of_not_eq_true h
    have hs : ∀ k,a≤k → trace q O seed ω k=trace q O seed ω a := by
      intro k hk
      induction k,hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        change update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))=_
        rw [ih]
        exact freyaPageHaltedUpdate q _ _ ha
    rw [hs b hab,ha] at hb
    contradiction
  have freyaPagePreBatchIteration (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
      (hstart : batchStartCall q O seed ω batch=some call) :
      ∀ k,k<call → (trace q O seed ω k).iteration<batch := by
    clear * - q O seed ω batch call hstart freyaPageBatchStartFacts freyaPageIterationMonotone freyaPageEarlierActive

    obtain ⟨_,hit,hactive,hprev⟩ := freyaPageBatchStartFacts q O seed ω batch call hstart
    intro k hk
    have hle := freyaPageIterationMonotone q O seed ω (Nat.le_of_lt hk)
    dsimp only at hle
    rw [hit] at hle
    have hka := freyaPageEarlierActive q O seed ω k call (Nat.le_of_lt hk) hactive
    have hne : (trace q O seed ω k).iteration≠batch := by
      intro he
      exact hprev k hk ⟨he,hka⟩
    omega
  have freyaPageRunBeforeBatch (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
      (hstart : batchStartCall q O seed ω batch=some call)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      ∀ k,k<call → trace q O new ω k={trace q O seed ω k with seed:=new} ∧
        (run q O new ω k).2=(run q O seed ω k).2 := by
    clear * - q O seed new ω batch call hstart hbits hrows freyaPageTraceSeed freyaPageUpdateSeedCongruence freyaPageInitialSeedCongruence freyaPageSeedQuery freyaPagePreBatchIteration

    have hpre := freyaPagePreBatchIteration q O seed ω batch call hstart
    intro k
    induction k with
    | zero =>
      intro hk
      have hb : 0<batch := hpre 0 hk
      have hleft : trace q O new ω 0=initial q new := by rfl'
      have hright : trace q O seed ω 0=initial q seed := by rfl'
      rw [hleft,hright]
      exact ⟨freyaPageInitialSeedCongruence q seed new (hrows 0 hb),rfl⟩
    | succ k ih =>
      intro hk
      have hkcall : k<call := by omega
      obtain ⟨hs,hh⟩ := ih hkcall
      have hseed := freyaPageTraceSeed q O seed ω k
      have hquery : query q (trace q O new ω k)=query q (trace q O seed ω k) := by
        rw [hs,freyaPageSeedQuery]
      have hreply : replyAt q O new ω k (query q (trace q O new ω k))=
          replyAt q O seed ω k (query q (trace q O seed ω k)) := by
        rw [hquery]
        show O.answer (run q O new ω k).2 _ (ω (run q O new ω k).2.length)=
          O.answer (run q O seed ω k).2 _ (ω (run q O seed ω k).2.length)
        rw [hh]
      refine ⟨?_,?_⟩
      · change update q (trace q O new ω k) (replyAt q O new ω k (query q (trace q O new ω k)))=_
        rw [hreply,hs]
        exact freyaPageUpdateSeedCongruence q _ new _ batch
          (by rw [hseed]; exact hbits) (by rw [hseed]; exact hrows) (hpre (k+1) hk)
      · change (run q O new ω k).2++[(query q (trace q O new ω k),
            replyAt q O new ω k (query q (trace q O new ω k)))]=
          (run q O seed ω k).2++[(query q (trace q O seed ω k),
            replyAt q O seed ω k (query q (trace q O seed ω k)))]
        rw [hreply,hh,hquery]
  have freyaPageTraceBeforeBatch (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
      (hstart : batchStartCall q O seed ω batch=some call)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      ∀ k,k<call → trace q O new ω k={trace q O seed ω k with seed:=new} :=
    fun k hk => (freyaPageRunBeforeBatch q O seed new ω batch call hstart hbits hrows k hk).1
  have freyaPageReplyBeforeBatch (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
      (hstart : batchStartCall q O seed ω batch=some call)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      ∀ k,k<call → ∀ x,replyAt q O new ω k x=replyAt q O seed ω k x := by
    clear * - q O seed new ω batch call hstart hbits hrows freyaPageTraceSeed freyaPageUpdateSeedCongruence freyaPageInitialSeedCongruence freyaPageSeedQuery freyaPagePreBatchIteration freyaPageRunBeforeBatch

    intro k hk x
    show O.answer (run q O new ω k).2 x (ω (run q O new ω k).2.length)=
      O.answer (run q O seed ω k).2 x (ω (run q O seed ω k).2.length)
    rw [(freyaPageRunBeforeBatch q O seed new ω batch call hstart hbits hrows k hk).2]
  let freyaEntryView (q : Raw) (s : State q) :
      ℕ × Bool × Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) :=
    (s.iteration, active s, s.phase.casesOn
      (fun _ c => some (true,c.point,c.point,c.clock,c.nextID-q.n))
      (fun c => some (false,c.x,c.y,c.clock,c.nextID-q.n)) none)
  have freyaPageAdvanceEntry (q : Raw) (s : State q) (new : Seed q.K)
      (hbits : new.2=s.seed.2) :
      freyaEntryView q (advance q {s with seed:=new})=freyaEntryView q (advance q s) := by
    clear * - q s new hbits freyaEntryView

    have hr : refreshAt new s.iteration=refreshAt s.seed s.iteration :=
      congrArg (fun t => t.1 s.iteration) hbits
    delta advance
    dsimp only
    by_cases hstop : rounds q≤s.iteration
    · simp (config := { iota := false }) only [ite_eq_left hstop]; rfl
    · simp (config := { iota := false }) only [ite_eq_right hstop,hr]
      cases refreshAt s.seed s.iteration <;> rfl
  have freyaPageUpdateEntry (q : Raw) (s : State q) (new : Seed q.K)
      (reply : Reply q.d q.n) (hbits : new.2=s.seed.2) :
      freyaEntryView q (update q {s with seed:=new} reply)=freyaEntryView q (update q s reply) := by
    clear * - q s new reply hbits freyaEntryView freyaPageAdvanceEntry

    delta update
    cases hs : s.phase with
    | halted => dsimp only [freyaEntryView,active]; rw [hs]
    | full first c =>
      dsimp only
      split
      · exact freyaPageAdvanceEntry q {s with
          g:=fullResult (fullUpdate c reply)
          clock:=(fullUpdate c reply).clock
          nextID:=(fullUpdate c reply).nextID
          phase:=Phase.full first (fullUpdate c reply)} new hbits
      · rfl
    | difference c =>
      dsimp only
      split
      · exact freyaPageAdvanceEntry q {s with
          g:=s.g+differenceResult (differenceUpdate c reply)
          clock:=(differenceUpdate c reply).clock
          nextID:=(differenceUpdate c reply).nextID
          phase:=Phase.difference (differenceUpdate c reply)} new hbits
      · rfl
  have freyaPageInitialEntry (q : Raw) (seed new : Seed q.K) :
      freyaEntryView q (initial q new)=freyaEntryView q (initial q seed) := by
    clear * - q seed new freyaEntryView

    dsimp only [initial,freyaEntryView]
    by_cases hbad : q.m=0 ∨ q.n=0 ∨ q.K=0
    · simp (config := { iota := false }) only [ite_eq_left hbad]; rfl
    · simp (config := { iota := false }) only [ite_eq_right hbad]; rfl
  have freyaPageBoundaryEntry (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
      (hstart : batchStartCall q O seed ω batch=some call)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      freyaEntryView q (trace q O new ω call)=freyaEntryView q (trace q O seed ω call) := by
    clear * - q O seed new ω batch call hstart hbits hrows freyaPageTraceSeed freyaPageSeedQuery freyaPageTraceBeforeBatch freyaEntryView freyaPageUpdateEntry freyaPageInitialEntry freyaPageReplyBeforeBatch

    cases call with
    | zero => exact freyaPageInitialEntry q seed new
    | succ k =>
      have hs := freyaPageTraceBeforeBatch q O seed new ω batch (k+1) hstart hbits hrows k (by omega)
      change freyaEntryView q (update q (trace q O new ω k)
        (replyAt q O new ω k (query q (trace q O new ω k))))=_
      rw [freyaPageReplyBeforeBatch q O seed new ω batch (k+1) hstart hbits hrows k (by omega),
        hs,freyaPageSeedQuery]
      exact freyaPageUpdateEntry q _ new _ (by rw [freyaPageTraceSeed]; exact hbits)
  have freyaPageFirstMatchConverse (N : ℕ) (p : ℕ → Bool) (k : ℕ)
      (hk : k<N) (hp : p k=true) (hprev : ∀ r<k,p r≠true) :
      (List.range N).find? p=some k := by
    clear * - N p k hk hp hprev

    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨hp,k,by simpa (config := { iota := false }) only [List.length_range] using hk,?_,?_⟩
    · simp (config := { iota := false }) only [List.getElem_range]
    · intro j hj
      simp (config := { iota := false }) only [List.getElem_range,Bool.eq_false_of_not_eq_true (hprev j hj),Bool.not_false]
  have freyaPageBatchStartTransport (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
      (hstart : batchStartCall q O seed ω batch=some call)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      batchStartCall q O new ω batch=some call := by
    clear * - q O seed new ω batch call hstart hbits hrows freyaPageBatchStartFacts freyaPageTraceBeforeBatch freyaPageBoundaryEntry freyaPageFirstMatchConverse freyaPageReplyBeforeBatch

    obtain ⟨hcall,hit,ha,hprev⟩ := freyaPageBatchStartFacts q O seed ω batch call hstart
    have he := freyaPageBoundaryEntry q O seed new ω batch call hstart hbits hrows
    have hi : (trace q O new ω call).iteration=batch := (congrArg Prod.fst he).trans hit
    have haa : active (trace q O new ω call)=true :=
      (congrArg (fun v => v.2.1) he).trans ha
    delta batchStartCall
    apply freyaPageFirstMatchConverse _ _ call (by omega)
    · exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hi,haa⟩
    · intro r hr ht
      have hs := freyaPageTraceBeforeBatch q O seed new ω batch call hstart hbits hrows r hr
      obtain ⟨hti,hta⟩ := Bool.and_eq_true_iff.mp ht
      apply hprev r hr
      rw [hs] at hti hta
      exact ⟨of_decide_eq_true hti,hta⟩
  have freyaPageBatchStartInvariant (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      batchStartCall q O new ω batch=batchStartCall q O seed ω batch := by
    clear * - q O seed new ω batch hbits hrows freyaPageBatchStartTransport

    cases hs : batchStartCall q O seed ω batch with
    | some call => exact freyaPageBatchStartTransport q O seed new ω batch call hs hbits hrows
    | none =>
      cases hn : batchStartCall q O new ω batch with
      | none => rfl
      | some call =>
        have hh := freyaPageBatchStartTransport q O new seed ω batch call hn hbits.symm
          (fun i hi => (hrows i hi).symm)
        rw [hs] at hh
        contradiction
  have freyaPageInvocationInvariant (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      invocation q O new ω batch=invocation q O seed ω batch := by
    clear * - q O seed new ω batch hbits hrows freyaEntryView freyaPageBoundaryEntry freyaPageBatchStartInvariant

    have he := freyaPageBatchStartInvariant q O seed new ω batch hbits hrows
    delta invocation
    rw [he]
    cases hs : batchStartCall q O seed ω batch with
    | none => rfl
    | some call =>
      have hh := congrArg (fun v => v.2.2)
        (freyaPageBoundaryEntry q O seed new ω batch call hs hbits hrows)
      dsimp only [Option.bind]
      dsimp only [freyaEntryView] at hh
      generalize (trace q O new ω call).phase = pn at hh ⊢
      generalize (trace q O seed ω call).phase = ps at hh ⊢
      cases pn <;> cases ps <;> exact hh
  have freyaFullUpdateRows {d m n : ℕ} (s : FullState d m n) (r : Reply d n) :
      (fullUpdate s r).rows=s.rows := by
    clear * - d m n s r

    classical
    dsimp only [fullUpdate]
    split
    · rfl
    · cases r with
      | none => rfl
      | some r =>
        rcases r with ⟨i,k,t,v⟩
        dsimp only
        cases s.pending i with
        | none => rfl
        | some j => dsimp only; split <;> rfl
  have freyaFullUpdateNext {d m n : ℕ} (s : FullState d m n) (r : Reply d n) :
      (fullUpdate s r).nextID≤s.nextID+1 := by
    clear * - d m n s r

    classical
    dsimp only [fullUpdate]
    split
    · exact Nat.le_succ _
    · cases r with
      | none => exact Nat.le_succ _
      | some r =>
        rcases r with ⟨i,k,t,v⟩
        dsimp only
        cases s.pending i with
        | none => exact Nat.le_succ _
        | some j =>
          dsimp only
          split
          · exact le_rfl
          · exact Nat.le_succ _
  have freyaFullUpdateRowChange {d m n : ℕ} (s : FullState d m n) (r : Reply d n)
      (rows : ℕ → ChoiceRow) (hrow : rows s.nextID=s.rows s.nextID) :
      fullUpdate {s with rows := rows} r={fullUpdate s r with rows := rows} := by
    clear * - d m n s r rows hrow

    classical
    dsimp only [fullUpdate]
    split
    · rfl
    · cases r with
      | none => rfl
      | some r =>
        rcases r with ⟨i,k,t,v⟩
        dsimp only
        cases s.pending i with
        | none => rfl
        | some j =>
          dsimp only
          split
          · rw [hrow]
          · rfl
  have freyaFullQueryRowChange {d m n : ℕ} (s : FullState d m n) (rows : ℕ → ChoiceRow) :
      fullQuery {s with rows := rows}=fullQuery s := rfl
  have freyaFullInitialRowChange {d m : ℕ} (n : ℕ) (labels : List (Fin m))
      (x : Space d) (start : ℝ≥0) (rows new : ℕ → ChoiceRow)
      (hrows : ∀ k<n,new k=rows k) :
      fullInitial n labels x start new={fullInitial n labels x start rows with rows := new} := by
    clear * - d m n labels x start rows new hrows

    have hp : (fullInitial n labels x start new).pending=(fullInitial n labels x start rows).pending := by
      funext i
      dsimp only [fullInitial,Nat.zero_add]
      simp (config := { iota := false }) only [Nat.zero_add]
      rw [hrows i.val i.isLt]
    cases h : fullInitial n labels x start rows
    dsimp only [fullInitial] at h hp ⊢
    cases h
    rw [hp]
  have freyaFullTraceRowsNext {d m : ℕ} (n : ℕ) (labels : List (Fin m))
      (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
      (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
      (fullTrace n labels x start rows answer a).rows=rows ∧
        (fullTrace n labels x start rows answer a).nextID≤n+a := by
    clear * - d m n labels x start rows answer a freyaFullUpdateRows freyaFullUpdateNext

    induction a with
    | zero => exact ⟨rfl,by dsimp only [fullTrace,fullInitial]; simp (config := { iota := false }) only [Nat.zero_add,Nat.add_zero]; exact le_rfl⟩
    | succ a ih =>
      constructor
      · exact (freyaFullUpdateRows _ _).trans ih.1
      · exact (freyaFullUpdateNext _ _).trans (Nat.add_le_add_right ih.2 1)
  have freyaFullTraceRowChange {d m : ℕ} (n : ℕ) (labels : List (Fin m))
      (x : Space d) (start : ℝ≥0) (rows new : ℕ → ChoiceRow)
      (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ)
      (hrows : ∀ k<n+a,new k=rows k) :
      fullTrace n labels x start new answer a=
        {fullTrace n labels x start rows answer a with rows := new} := by
    clear * - d m n labels x start rows new answer a hrows freyaFullUpdateRowChange freyaFullQueryRowChange freyaFullInitialRowChange freyaFullTraceRowsNext

    induction a with
    | zero => exact freyaFullInitialRowChange n labels x start rows new (by simpa (config := { iota := false }) only [Nat.add_zero] using hrows)
    | succ a ih =>
      have hprev := ih (fun k hk => hrows k (by omega))
      dsimp only [fullTrace]
      rw [hprev,freyaFullQueryRowChange]
      apply freyaFullUpdateRowChange
      have hs := freyaFullTraceRowsNext n labels x start rows answer a
      rw [hs.1]
      exact hrows _ (by omega)
  have freyaFullUpdateSummaryRowChange {d m n : ℕ} (s : FullState d m n) (r : Reply d n)
      (rows : ℕ → ChoiceRow) :
      (fullUpdate {s with rows := rows} r).remaining=(fullUpdate s r).remaining ∧
        (fullUpdate {s with rows := rows} r).clock=(fullUpdate s r).clock := by
    clear * - d m n s r rows

    classical
    dsimp only [fullUpdate]
    split
    · exact ⟨rfl,rfl⟩
    · cases r with
      | none => exact ⟨rfl,rfl⟩
      | some r =>
        rcases r with ⟨i,k,t,v⟩
        dsimp only
        cases s.pending i with
        | none => exact ⟨rfl,rfl⟩
        | some j => dsimp only; split <;> exact ⟨rfl,rfl⟩
  have freyaDispatchContextRowChange {d m : ℕ} (n : ℕ) (labels : List (Fin m))
      (x : Space d) (start : ℝ≥0) (rows new : ℕ → ChoiceRow)
      (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ)
      (hrows : ∀ k<a,new k=rows k) :
      dispatchContext n labels x start new answer a=dispatchContext n labels x start rows answer a := by
    clear * - d m n labels x start rows new answer a hrows freyaFullQueryRowChange freyaFullTraceRowChange freyaFullUpdateSummaryRowChange

    classical
    dsimp only [dispatchContext]
    by_cases ha : a<n
    · rw [dite_eq_left ha,dite_eq_left ha]
      congr 1
      congr 1
      funext i
      by_cases hi : i.val<a
      · rw [ite_eq_left hi,ite_eq_left hi]
        dsimp only [fullInitial]
        simp (config := { iota := false }) only [Nat.zero_add]
        rw [hrows i.val hi]
      · rw [ite_eq_right hi,ite_eq_right hi]
    · rw [dite_eq_right ha,dite_eq_right ha]
      have he := freyaFullTraceRowChange n labels x start rows new answer (a-n)
        (fun k hk => hrows k (by omega))
      rw [he,freyaFullQueryRowChange]
      cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
      | none =>
        have hs := freyaFullUpdateSummaryRowChange (fullTrace n labels x start rows answer (a-n)) none new
        dsimp only
        rw [hs.1,hs.2]
      | some rep =>
        rcases rep with ⟨i,k,t,v⟩
        have hs := freyaFullUpdateSummaryRowChange (fullTrace n labels x start rows answer (a-n)) (some (i,k,t,v)) new
        dsimp only
        rw [hs.1,hs.2]
  let freyaMask (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) : Seed q.K × ((k : ℕ) → O.Seed k) :=
    ((Function.update z.1.1 batch (fun k =>
        if k<(invocationData q O batch z).2.2.2.2+a then z.1.1 batch k else fun _ => 0),z.1.2),z.2)
  have freyaMaskInvocation (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      invocation q O (freyaMask q O batch a z).1 (freyaMask q O batch a z).2 batch=
        invocation q O z.1 z.2 batch := by
    clear * - q O batch a z freyaPageInvocationInvariant freyaMask

    apply freyaPageInvocationInvariant q O z.1 (freyaMask q O batch a z).1 z.2 batch rfl
    intro j hj
    exact Function.update_of_ne (by omega : j≠batch) _ _
  have freyaMaskData (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      invocationData q O batch (freyaMask q O batch a z)=invocationData q O batch z := by
    clear * - q O batch a z freyaMask freyaMaskInvocation

    dsimp only [invocationData]
    rw [freyaMaskInvocation]
  have freyaMaskCall (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      batchStartCall q O (freyaMask q O batch a z).1 (freyaMask q O batch a z).2 batch=
        batchStartCall q O z.1 z.2 batch := by
    clear * - q O batch a z freyaPageBatchStartInvariant freyaMask

    apply freyaPageBatchStartInvariant q O z.1 (freyaMask q O batch a z).1 z.2 batch rfl
    intro j hj
    exact Function.update_of_ne (by omega : j≠batch) _ _
  have freyaMaskAnswer (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a k : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) (r : Option (Request q.d q.m q.n))
      (hobl : HistoryOblivious O) :
      restartAnswer q O batch k r (freyaMask q O batch a z)=restartAnswer q O batch k r z := by
    clear * - q O batch a k z r hobl freyaMask freyaMaskData freyaMaskCall

    dsimp only [restartAnswer,liftRequest]
    rw [freyaMaskData,freyaMaskCall]
    congr 1
    exact hobl _ _ _ z.2 (by rw [run_length,run_length])
  have freyaMaskRows (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) (k : ℕ) (hk : k<a) :
      restartedRows q O batch (freyaMask q O batch a z) k=restartedRows q O batch z k := by
    clear * - q O batch a z k hk freyaMask freyaMaskData

    dsimp only [restartedRows]
    rw [freyaMaskData]
    dsimp only [freyaMask]
    rw [Function.update_self,ite_eq_left (Nat.add_lt_add_left hk _)]
  have freyaMaskContext (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
      (batch a : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0
          (restartedRows q O batch (freyaMask q O batch a z))
          (fun k r => restartAnswer q O batch k r (freyaMask q O batch a z)) a=
        dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun k r => restartAnswer q O batch k r z) a := by
    clear * - q O hobl batch a z freyaDispatchContextRowChange freyaMask freyaMaskAnswer freyaMaskRows

    have ha : (fun k r => restartAnswer q O batch k r (freyaMask q O batch a z))=
        (fun k r => restartAnswer q O batch k r z) := by
      funext k r
      exact freyaMaskAnswer q O batch a k z r hobl
    rw [ha]
    exact freyaDispatchContextRowChange q.n (List.ofFn id) 0 0 _ _ _ a
      (fun k hk => freyaMaskRows q O batch a z k hk)
  have freyaMaskCompose (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a b : ℕ)
      (hab : a≤b) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      freyaMask q O batch a (freyaMask q O batch b z)=freyaMask q O batch a z := by
    clear * - q O batch a b hab z freyaMask freyaMaskData

    have hd := freyaMaskData q O batch b z
    unfold freyaMask at hd ⊢
    rw [hd]
    apply Prod.ext
    · apply Prod.ext
      · funext j k
        by_cases hj : j=batch
        · subst j
          simp (config := { iota := false }) only [Function.update_self]
          by_cases hk : k<(invocationData q O batch z).2.2.2.2+a
          · rw [ite_eq_left hk,ite_eq_left hk,ite_eq_left (by omega)]
          · rw [ite_eq_right hk,ite_eq_right hk]
        · simp (config := { iota := false }) only [Function.update_of_ne hj]
      · rfl
    · rfl
  have freyaMaskMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) : Measurable (freyaMask q O batch a) := by
    clear * - q f τ O hservice batch a freyaHistoryAmbient freyaInvocationDataHistoryMeas freyaMask

    have hd := (freyaInvocationDataHistoryMeas q O batch).mono
      (freyaHistoryAmbient q f τ O hservice batch) le_rfl
    apply Measurable.prodMk _ measurable_snd
    apply Measurable.prodMk _ measurable_fst.snd
    apply Measurable.of_eval
    intro j
    by_cases hj : j=batch
    · subst j
      apply Measurable.of_eval
      intro k
      have hm : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => z.1.1 batch k) :=
        (measurable_pi_apply k).comp ((measurable_pi_apply batch).comp measurable_fst.fst)
      have he : MeasurableSet {z | k<(invocationData q O batch z).2.2.2.2+a} :=
        measurableSet_lt measurable_const (hd.snd.snd.snd.snd.add_const a)
      change Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
        (Function.update z.1.1 batch (fun k =>
          if k<(invocationData q O batch z).2.2.2.2+a then z.1.1 batch k else fun _ => 0)) batch k)
      simpa (config := { iota := false }) only [Function.update_self] using hm.ite he
        (measurable_const : Measurable (fun _ : Seed q.K × ((k : ℕ) → O.Seed k) => (fun k => (0 : Fin (k+1)))))
    · change Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
        (Function.update z.1.1 batch (fun k =>
          if k<(invocationData q O batch z).2.2.2.2+a then z.1.1 batch k else fun _ => 0)) j)
      have hm : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => z.1.1 j) :=
        (measurable_pi_apply j).comp measurable_fst.fst
      simpa (config := { iota := false }) only [Function.update_of_ne hj] using hm
  let freyaMaskHistory (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ) :
      MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k)) :=
    MeasurableSpace.comap (freyaMask q O batch a) inferInstance
  have freyaMaskHistoryAmbient (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) :
      freyaMaskHistory q O batch a≤(inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))) :=
    (freyaMaskMeas q f τ O hservice batch a).comap_le
  have freyaMaskHistoryMonotone (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch : ℕ) : Monotone (freyaMaskHistory q O batch) := by
    clear * - q f τ O hservice batch freyaMask freyaMaskCompose freyaMaskMeas freyaMaskHistory

    intro a b hab
    have hb : Measurable[freyaMaskHistory q O batch b] (freyaMask q O batch b) :=
      Measurable.of_comap_le le_rfl
    have h : Measurable[freyaMaskHistory q O batch b]
        (fun z => freyaMask q O batch a (freyaMask q O batch b z)) :=
      (freyaMaskMeas q f τ O hservice batch a).comp hb
    have he : (fun z => freyaMask q O batch a (freyaMask q O batch b z))=freyaMask q O batch a := by
      funext z
      exact freyaMaskCompose q O batch a b hab z
    rw [he] at h
    exact h.comap_le
  have freyaMaskFactorMeas (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch a : ℕ)
      {α : Type} [MeasurableSpace α] (g : Seed q.K × ((k : ℕ) → O.Seed k) → α)
      (hg : Measurable g) (hinv : ∀ z,g (freyaMask q O batch a z)=g z) :
      Measurable[freyaMaskHistory q O batch a] g := by
    clear * - q O batch a α g hg hinv freyaMask freyaMaskHistory

    have hm : Measurable[freyaMaskHistory q O batch a] (freyaMask q O batch a) :=
      Measurable.of_comap_le le_rfl
    have h : Measurable[freyaMaskHistory q O batch a] (fun z => g (freyaMask q O batch a z)) := hg.comp hm
    have he : (fun z => g (freyaMask q O batch a z))=g := funext hinv
    rwa [he] at h
  have freyaMaskContextOfLe (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
      (batch a b : ℕ)
      (hab : a≤b) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0
          (restartedRows q O batch (freyaMask q O batch b z))
          (fun k r => restartAnswer q O batch k r (freyaMask q O batch b z)) a=
        dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun k r => restartAnswer q O batch k r z) a := by
    clear * - q O hobl batch a b hab z freyaDispatchContextRowChange freyaMask freyaMaskAnswer freyaMaskRows

    have ha : (fun k r => restartAnswer q O batch k r (freyaMask q O batch b z))=
        (fun k r => restartAnswer q O batch k r z) := by
      funext k r
      exact freyaMaskAnswer q O batch b k z r hobl
    rw [ha]
    exact freyaDispatchContextRowChange q.n (List.ofFn id) 0 0 _ _ _ a
      (fun k hk => freyaMaskRows q O batch b z k (hk.trans_le hab))
  have freyaMaskChoice (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (hobl : HistoryOblivious O)
      (batch a : ℕ)
      (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
      assignmentChoice q.n (List.ofFn id) (0 : Space q.d) 0
          (restartedRows q O batch (freyaMask q O batch (a+1) z))
          (fun k r => restartAnswer q O batch k r (freyaMask q O batch (a+1) z)) a=
        assignmentChoice q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun k r => restartAnswer q O batch k r z) a := by
    clear * - q O hobl batch a z freyaMask freyaMaskRows freyaMaskContextOfLe

    dsimp only [assignmentChoice]
    rw [freyaMaskContextOfLe q O hobl batch a (a+1) (Nat.le_succ a) z,
      freyaMaskRows q O batch (a+1) z a (Nat.lt_succ_self a)]
  have freyaFullQueryMeas {d m n : ℕ} : Measurable (@fullQuery d m n) := by
    clear * - d m n freyaFullCodeMeas freyaPendingRequestMeas

    classical
    have hc := @freyaFullCodeMeas d m n
    exact measurable_const.ite
      (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst) (measurableSet_singleton true))
      (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.fst))
  have freyaRestartFullTraceMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) :
      Measurable (fun z => fullTrace q.n (List.ofFn id) (0 : Space q.d) 0
        (restartedRows q O batch z) (fun k r => restartAnswer q O batch k r z) a) := by
    clear * - q f τ O hservice batch a freyaFullInitialMeas freyaFullUpdateMeas freyaRestartRowsMeas freyaRestartAnswerMeas freyaFullQueryMeas

    induction a with
    | zero =>
      exact freyaFullInitialMeas q.n (List.ofFn id) (fun _ => 0) (fun _ => 0)
        (restartedRows q O batch) (fun _ => 0) measurable_const measurable_const
        (freyaRestartRowsMeas q f τ O hservice batch) measurable_const
    | succ a ih =>
      exact freyaFullUpdateMeas.comp (ih.prodMk ((freyaRestartAnswerMeas q f τ O hservice batch a).comp
        ((freyaFullQueryMeas.comp ih).prodMk measurable_id)))
  have freyaRestartContextMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) :
      Measurable (fun z => dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0
        (restartedRows q O batch z) (fun k r => restartAnswer q O batch k r z) a) := by
    clear * - q f τ O hservice batch a freyaOptionSomeMeas freyaOptionParamMeas freyaFullCodeMeas freyaFullUpdateMeas freyaRestartAnswerMeas freyaFullQueryMeas freyaRestartFullTraceMeas

    classical
    let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
    by_cases ha : a<q.n
    · have hs := freyaFullCodeMeas.comp (freyaRestartFullTraceMeas q f τ O hservice batch 0)
      have hp : Measurable (fun z : Ω => fun i : Fin q.n => if i.val<a then
          (fullInitial (m:=q.m) q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)).pending i else none) := by
        apply Measurable.of_eval
        intro i
        by_cases hi : i.val<a
        · simp (config := { iota := false }) only [ite_eq_left hi]
          exact (measurable_pi_apply i).comp hs.snd.snd.snd.snd.fst
        · simp (config := { iota := false }) only [ite_eq_right hi]
          exact measurable_const
      dsimp only [dispatchContext]
      simp (config := { iota := false }) only [dite_eq_left ha]
      exact measurable_const.prodMk (hp.prodMk (measurable_const.prodMk measurable_const))
    · let s := fun z : Ω => fullTrace q.n (List.ofFn id) (0 : Space q.d) 0
        (restartedRows q O batch z) (fun k r => restartAnswer q O batch k r z) (a-q.n)
      let r := fun z : Ω => restartAnswer q O batch (a-q.n) (fullQuery (s z)) z
      let t := fun z : Ω => fullUpdate (s z) (r z)
      have hs : Measurable s := freyaRestartFullTraceMeas q f τ O hservice batch (a-q.n)
      have hr : Measurable r := (freyaRestartAnswerMeas q f τ O hservice batch (a-q.n)).comp
        ((freyaFullQueryMeas.comp hs).prodMk measurable_id)
      have ht : Measurable t := freyaFullUpdateMeas.comp (hs.prodMk hr)
      have hsc := freyaFullCodeMeas.comp hs
      have htc := freyaFullCodeMeas.comp ht
      have hnone : Measurable (fun z : Ω => ((t z).remaining,(s z).pending,
          (none : Option (Fin q.n)),(t z).clock)) :=
        htc.snd.fst.prodMk (hsc.snd.snd.snd.snd.fst.prodMk
          (measurable_const.prodMk htc.snd.snd.snd.snd.snd.fst))
      have hsome : Measurable (fun z : Ω × (Fin q.n × ℕ × ℝ≥0 × Space q.d) =>
          ((t z.1).remaining,Function.update (s z.1).pending z.2.1 none,
            (if (t z.1).remaining.isEmpty then none else some z.2.1),(t z.1).clock)) := by
        have hp : Measurable (fun z : Ω × (Fin q.n × ℕ × ℝ≥0 × Space q.d) =>
            Function.update (s z.1).pending z.2.1 (none : Option (Job q.d q.m))) := by
          apply Measurable.of_eval
          intro i
          have hb : Measurable (fun z : Ω × (Fin q.n × ℕ × ℝ≥0 × Space q.d) => (s z.1).pending i) :=
            ((measurable_pi_apply i).comp hsc.snd.snd.snd.snd.fst).comp measurable_fst
          have h : Measurable (fun z : Ω × (Fin q.n × ℕ × ℝ≥0 × Space q.d) =>
              if i=z.2.1 then (none : Option (Job q.d q.m)) else (s z.1).pending i) :=
            measurable_const.ite (measurableSet_eq_fun measurable_const measurable_snd.fst) hb
          convert h using 1
          funext z
          simp (config := { iota := false }) only [Function.update_apply]
        have hi : Measurable (fun z : Ω × (Fin q.n × ℕ × ℝ≥0 × Space q.d) =>
            if (t z.1).remaining.isEmpty then (none : Option (Fin q.n)) else some z.2.1) := by
          exact measurable_const.ite
            (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp
              (htc.snd.fst.comp measurable_fst)) (measurableSet_singleton true))
            (freyaOptionSomeMeas.comp measurable_snd.fst)
        exact (htc.snd.fst.comp measurable_fst).prodMk (hp.prodMk
          (hi.prodMk (htc.snd.snd.snd.snd.snd.fst.comp measurable_fst)))
      have h := freyaOptionParamMeas r hr _ hnone _ hsome
      convert h using 1
      funext z
      dsimp only [dispatchContext]
      rw [dite_eq_right ha]
      cases hrz : r z with
      | none =>
        dsimp only [r,s,t] at hrz ⊢
        simp (config := { iota := false }) only [hrz,Option.elim_none]
        rfl
      | some v =>
        rcases v with ⟨i,k,u,v⟩
        dsimp only [r,s,t] at hrz ⊢
        simp (config := { iota := false }) only [hrz,Option.elim_some]
        rfl
  have freyaChooseRemainingMeas (l : List ℕ) : Measurable (fun row : ChoiceRow => chooseRemaining row l) := by
    clear * - l

    by_cases hl : l.length=0
    · dsimp only [chooseRemaining]
      simp (config := { iota := false }) only [dite_eq_left hl]
      exact measurable_const
    · have hn : l.length-1+1=l.length := by omega
      have he : (fun row : ChoiceRow => chooseRemaining row l)=
          (fun i : Fin (l.length-1+1) => some (l.get (Fin.cast hn i))) ∘ (fun row => row (l.length-1)) := by
        funext row
        dsimp only [chooseRemaining,Function.comp_def]
        rw [dite_eq_right hl]
        rfl
      rw [he]
      exact (measurable_of_countable _).comp (measurable_pi_apply _)
  have freyaFullUpdateNodup {d m n : ℕ} (s : FullState d m n) (r : Reply d n)
      (hs : s.remaining.Nodup) : (fullUpdate s r).remaining.Nodup := by
    clear * - d m n s r hs

    classical
    dsimp only [fullUpdate]
    split
    · exact hs
    · cases r with
      | none => exact hs
      | some r =>
        rcases r with ⟨i,k,t,v⟩
        dsimp only
        cases s.pending i with
        | none => exact hs
        | some job =>
          dsimp only
          split
          · dsimp only
            cases s.remaining.find? (fun b => decide (s.original[b]?=some job.component)) with
            | none => exact hs
            | some b => exact hs.erase b
          · exact hs
  have freyaFullTraceNodup {d m : ℕ} (n : ℕ) (labels : List (Fin m))
      (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
      (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
      (fullTrace n labels x start rows answer a).remaining.Nodup := by
    clear * - d m n labels x start rows answer a freyaFullUpdateNodup

    induction a with
    | zero => exact List.nodup_range
    | succ a ih => exact freyaFullUpdateNodup _ _ ih
  have freyaDispatchContextNodup {d m : ℕ} (n : ℕ) (labels : List (Fin m))
      (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
      (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
      (dispatchContext n labels x start rows answer a).1.Nodup := by
    clear * - d m n labels x start rows answer a freyaFullUpdateNodup freyaFullTraceNodup

    classical
    dsimp only [dispatchContext]
    split
    · exact List.nodup_range
    · cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
      | none => exact freyaFullUpdateNodup _ _ (freyaFullTraceNodup n labels x start rows answer (a-n))
      | some rep =>
        rcases rep with ⟨i,k,t,v⟩
        exact freyaFullUpdateNodup _ _ (freyaFullTraceNodup n labels x start rows answer (a-n))
  have freyaRestartChoiceMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) :
      Measurable (fun z => assignmentChoice q.n (List.ofFn id) (0 : Space q.d) 0
        (restartedRows q O batch z) (fun k r => restartAnswer q O batch k r z) a) := by
    clear * - q f τ O hservice batch a freyaOptionSingleton freyaMeasurableSelect freyaRestartRowsMeas freyaRestartContextMeas freyaChooseRemainingMeas

    let : MeasurableSingletonClass (Option ℕ) := freyaOptionSingleton
    have hc := (freyaRestartContextMeas q f τ O hservice batch a).fst
    have hr := (measurable_pi_apply a).comp (freyaRestartRowsMeas q f τ O hservice batch)
    exact (measurable_of_countable (fun v : Option ℕ => v.getD 0)).comp
      (freyaMeasurableSelect _ hc (fun l z => chooseRemaining (restartedRows q O batch z a) l)
        (fun l => (freyaChooseRemainingMeas l).comp hr))
  have freyaRestartContextHistoryMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a : ℕ) :
      Measurable[freyaMaskHistory q O batch a] (fun z =>
        dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0
          (restartedRows q O batch z) (fun k r => restartAnswer q O batch k r z) a) :=
    freyaMaskFactorMeas q O batch a _ (freyaRestartContextMeas q f τ O hservice batch a)
      (freyaMaskContext q O hservice.1.1 batch a)
  have freyaInfiniteResampleIndex {ι : Type} [DecidableEq ι] {α : Type} [MeasurableSpace α]
      (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
      MeasurePreserving (fun z : (ι → α) × α => Function.update z.1 i z.2)
        ((Measure.infinitePi fun _ : ι => μ).prod μ) (Measure.infinitePi fun _ : ι => μ) := by
    clear * - ι α μ i

    classical
    have hm : Measurable (fun z : (ι → α) × α => Function.update z.1 i z.2) := by
      apply Measurable.of_eval
      intro j
      by_cases hj : j=i
      · subst j
        simpa (config := { iota := false }) only [Function.update_self] using
          (measurable_snd : Measurable (fun z : (ι → α) × α => z.2))
      · simpa (config := { iota := false }) only [Function.update_of_ne hj,Function.comp_def] using
          ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (ι → α) × α => z.1)))
    refine ⟨hm,Measure.eq_infinitePi _ (fun s t ht => ?_)⟩
    rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
    by_cases hi : i∈s
    · have he : (fun z : (ι → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi (↑s) t =
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
    · have he : (fun z : (ι → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi (↑s) t =
          (Set.pi (↑s) t) ×ˢ Set.univ := by
        ext z
        simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Set.mem_univ,and_true]
        apply forall_congr'
        intro j
        apply forall_congr'
        intro hj
        rw [Function.update_of_ne (show j≠i from fun he => hi (he ▸ hj))]
      rw [he,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi _ (fun j _ => ht j)]
  have freyaFreshTapeEventIndex {ι : Type} [DecidableEq ι] {α : Type} [MeasurableSpace α]
      (μ : Measure α) [IsProbabilityMeasure μ] (i : ι)
      (E : Set (ι → α)) (hE : MeasurableSet E)
      (hinvariant : ∀ t a, Function.update t i a∈E ↔ t∈E)
      (U : Set α) (hU : MeasurableSet U) :
      (Measure.infinitePi fun _ : ι => μ) (E∩{t | t i∈U})=
        (Measure.infinitePi fun _ : ι => μ) E*μ U := by
    clear * - ι α μ i E hE hinvariant U hU freyaInfiniteResampleIndex

    have hr := freyaInfiniteResampleIndex μ i
    have hm : MeasurableSet (E∩{t : ι → α | t i∈U}) :=
      hE.inter ((measurable_pi_apply i) hU)
    have he : (fun z : (ι → α) × α => Function.update z.1 i z.2) ⁻¹'
        (E∩{t | t i∈U})=E×ˢU := by
      ext z
      simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq,
        Set.mem_prod,Function.update_self,hinvariant]
    conv_lhs => rw [← hr.map_eq]
    rw [Measure.map_apply hr.measurable hm,he,Measure.prod_prod]
  have freyaFreshTapeEventProdIndex {ι : Type} [DecidableEq ι] {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
      (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
      (i : ι) (E : Set ((ι → α) × β)) (hE : MeasurableSet E)
      (hinvariant : ∀ t b a, (Function.update t i a,b)∈E ↔ (t,b)∈E)
      (U : Set α) (hU : MeasurableSet U) :
      ((Measure.infinitePi fun _ : ι => μ).prod ν) (E∩{z | z.1 i∈U})=
        ((Measure.infinitePi fun _ : ι => μ).prod ν) E*μ U := by
    clear * - ι α β μ ν i E hE hinvariant U hU freyaFreshTapeEventIndex

    have hm : MeasurableSet (E∩{z : (ι → α) × β | z.1 i∈U}) :=
      hE.inter (((measurable_pi_apply i).comp measurable_fst) hU)
    rw [Measure.prod_apply_symm hm]
    have he (b : β) : (Measure.infinitePi fun _ : ι => μ)
        ((fun t => (t,b)) ⁻¹' (E∩{z | z.1 i∈U}))=
        (Measure.infinitePi fun _ : ι => μ) ((fun t => (t,b)) ⁻¹' E)*μ U :=
      freyaFreshTapeEventIndex μ i ((fun t => (t,b)) ⁻¹' E)
        (hE.preimage (measurable_id.prodMk measurable_const))
        (fun t a => hinvariant t b a) U hU
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (measure_ne_top μ U),← Measure.prod_apply_symm hE]
  have freyaFreshTapeEventProdProdIndex {ι : Type} [DecidableEq ι] {α β γ : Type}
      [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
      (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
      (ξ : Measure γ) [IsProbabilityMeasure ξ]
      (i : ι) (E : Set (((ι → α) × β) × γ)) (hE : MeasurableSet E)
      (hinvariant : ∀ t b c a, ((Function.update t i a,b),c)∈E ↔ ((t,b),c)∈E)
      (U : Set α) (hU : MeasurableSet U) :
      (((Measure.infinitePi fun _ : ι => μ).prod ν).prod ξ) (E∩{z | z.1.1 i∈U})=
        (((Measure.infinitePi fun _ : ι => μ).prod ν).prod ξ) E*μ U := by
    clear * - ι α β γ μ ν ξ i E hE hinvariant U hU freyaFreshTapeEventProdIndex

    let e : (((ι → α) × β) × γ) ≃ᵐ ((ι → α) × β × γ) := MeasurableEquiv.prodAssoc
    have hp := measurePreserving_prodAssoc (Measure.infinitePi fun _ : ι => μ) ν ξ
    have h := freyaFreshTapeEventProdIndex μ (ν.prod ξ) i (e.symm ⁻¹' E)
      (hE.preimage e.symm.measurable)
      (fun t b a => hinvariant t b.1 b.2 a) U hU
    have hm : MeasurableSet ((e.symm ⁻¹' E)∩{z : (ι → α) × β × γ | z.1 i∈U}) :=
      (hE.preimage e.symm.measurable).inter (((measurable_pi_apply i).comp measurable_fst) hU)
    rw [← hp.map_eq,Measure.map_apply hp.measurable hm,
      Measure.map_apply hp.measurable (hE.preimage e.symm.measurable)] at h
    exact h
  have freyaFreshCoordinateEvent {α β γ : Type}
      [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
      (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
      (ξ : Measure γ) [IsProbabilityMeasure ξ]
      (batch k : ℕ) (E : Set (((ℕ → ℕ → α) × β) × γ)) (hE : MeasurableSet E)
      (hinvariant : ∀ t b c v,
        ((Function.update t batch (Function.update (t batch) k v),b),c)∈E ↔ ((t,b),c)∈E)
      (U : Set α) (hU : MeasurableSet U) :
      (((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μ).prod ν).prod ξ)
          (E∩{z | z.1.1 batch k∈U})=
        (((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μ).prod ν).prod ξ) E*μ U := by
    clear * - α β γ μ ν ξ batch k E hE hinvariant U hU freyaFreshTapeEventProdProdIndex

    classical
    let e := MeasurableEquiv.curry ℕ ℕ α
    have hp : MeasurePreserving e (Measure.infinitePi fun _ : ℕ × ℕ => μ)
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => μ) :=
      ⟨e.measurable,Measure.infinitePi_map_curry (fun _ _ : ℕ => μ)⟩
    let g : (((ℕ × ℕ → α) × β) × γ) → (((ℕ → ℕ → α) × β) × γ) := Prod.map (Prod.map e id) id
    have hg := (hp.prod (MeasurePreserving.id ν)).prod (MeasurePreserving.id ξ)
    have he (t : ℕ × ℕ → α) (v : α) :
        e (Function.update t (batch,k) v)=Function.update (e t) batch (Function.update (e t batch) k v) := by
      funext b j
      change Function.update t (batch,k) v (b,j)=
        Function.update (fun b j => t (b,j)) batch (Function.update (fun j => t (batch,j)) k v) b j
      by_cases hb : b=batch
      · subst b
        by_cases hj : j=k
        · subst j; simp (config := { iota := false }) only [Function.update_self]
        · simp (config := { iota := false }) [hj]
      · simp (config := { iota := false }) [hb]
    have h := freyaFreshTapeEventProdProdIndex μ ν ξ (batch,k) (g ⁻¹' E)
      (hE.preimage hg.measurable) (fun t b c v => by
        change ((e (Function.update t (batch,k) v),b),c)∈E ↔ ((e t,b),c)∈E
        rw [he]
        exact hinvariant (e t) b c v) U hU
    have hm : MeasurableSet (E∩{z : ((ℕ → ℕ → α) × β) × γ | z.1.1 batch k∈U}) :=
      hE.inter (((measurable_pi_apply k).comp ((measurable_pi_apply batch).comp measurable_fst.fst)) hU)
    rw [← hg.map_eq,Measure.map_apply hg.measurable hm,Measure.map_apply hg.measurable hE]
    exact h
  have freyaPageSeedPendingAfter (q : Raw) (s : State q) (new : Seed q.K)
      (reply : Reply q.d q.n) :
      collectorPendingAfter q {s with seed:=new} reply=collectorPendingAfter q s reply := by
    clear * - q s new reply
    rfl
  have freyaPageHistoryInvariant (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
      freyaHistoryView q O batch (new,ω)=freyaHistoryView q O batch (seed,ω) := by
    clear * - q O seed new ω batch hbits hrows freyaHistoryView freyaPageSeedQuery freyaPageTraceBeforeBatch freyaPageBatchStartInvariant freyaPageInvocationInvariant freyaPageSeedPendingAfter freyaPageReplyBeforeBatch

    apply Prod.ext
    · exact freyaPageInvocationInvariant q O seed new ω batch hbits hrows
    · funext k
      have he := freyaPageBatchStartInvariant q O seed new ω batch hbits hrows
      dsimp only [freyaHistoryView]
      rw [he]
      cases hs : batchStartCall q O seed ω batch with
      | none => simp (config := { iota := false }) only [Option.getD_none,Nat.not_lt_zero,ite_false]
      | some call =>
        dsimp only [Option.getD]
        by_cases hk : k<call
        · simp (config := { iota := false }) only [ite_eq_left hk]
          have ht := freyaPageTraceBeforeBatch q O seed new ω batch call hs hbits hrows k hk
          rw [freyaPageReplyBeforeBatch q O seed new ω batch call hs hbits hrows k hk,
            ht,freyaPageSeedQuery,freyaPageSeedPendingAfter]
        · simp (config := { iota := false }) only [ite_eq_right hk]
  have freyaPageHistoryEventInvariant (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
      (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i)
      (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
      (hE : MeasurableSet[historyBefore q O batch] E) :
      (new,ω)∈E ↔ (seed,ω)∈E := by
    clear * - q O seed new ω batch hbits hrows E hE freyaHistoryView freyaPageHistoryInvariant

    change MeasurableSet[MeasurableSpace.comap (freyaHistoryView q O batch) inferInstance] E at hE
    obtain ⟨U,_,hU⟩ := hE
    rw [← hU]
    change freyaHistoryView q O batch (new,ω)∈U ↔ freyaHistoryView q O batch (seed,ω)∈U
    rw [freyaPageHistoryInvariant q O seed new ω batch hbits hrows]
  have freyaDataReplace (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (batch : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) (rows : ℕ → ChoiceRow) :
      invocationData q O batch ((Function.update z.1.1 batch rows,z.1.2),z.2)=invocationData q O batch z := by
    clear * - q O batch z rows freyaPageInvocationInvariant

    dsimp only [invocationData]
    rw [freyaPageInvocationInvariant q O z.1 (Function.update z.1.1 batch rows,z.1.2) z.2 batch rfl
      (fun j hj => Function.update_of_ne (by omega : j≠batch) rows z.1.1)]
  have freyaMaskReplaceCoordinate (q : Raw)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (batch a i : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) (row : ChoiceRow)
      (hi : (invocationData q O batch z).2.2.2.2=i) :
      freyaMask q O batch a ((Function.update z.1.1 batch (Function.update (z.1.1 batch) (i+a) row),z.1.2),z.2)=
        freyaMask q O batch a z := by
    clear * - q O batch a i z row hi freyaMask freyaDataReplace

    dsimp only [freyaMask]
    rw [freyaDataReplace,hi]
    apply Prod.ext
    · apply Prod.ext
      · funext b k
        by_cases hb : b=batch
        · subst b
          simp (config := { iota := false }) only [Function.update_self]
          by_cases hk : k < i+a
          · rw [ite_eq_left hk,ite_eq_left hk,Function.update_of_ne (by omega : k≠i+a)]
          · rw [ite_eq_right hk,ite_eq_right hk]
        · simp (config := { iota := false }) only [Function.update_of_ne hb]
      · rfl
    · rfl
  have freyaMaskCellFresh (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch a i : ℕ)
      (E F : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
      (hE : MeasurableSet[InvocationHistory q O batch] E)
      (hF : MeasurableSet[freyaMaskHistory q O batch a] F)
      (U : Set ChoiceRow) (hU : MeasurableSet U) :
      (executionLaw q O : Measure _)
        ((E∩F∩{z | (invocationData q O batch z).2.2.2.2=i})∩{z | z.1.1 batch (i+a)∈U})=
        (executionLaw q O : Measure _) (E∩F∩{z | (invocationData q O batch z).2.2.2.2=i})*
          (rowLaw : Measure ChoiceRow) U := by
    clear * - q f τ O hservice batch a i E F hE hF U hU freyaHistoryAmbient freyaInvocationDataHistoryMeas freyaMask freyaMaskHistory freyaMaskHistoryAmbient freyaFreshCoordinateEvent freyaPageHistoryEventInvariant freyaDataReplace freyaMaskReplaceCoordinate

    classical
    have : NeZero (max 1 q.K) := ⟨by omega⟩
    let ν := (refreshLaw q.ρ : Measure (ℕ → Bool)).prod
      (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
    have hν : IsProbabilityMeasure ν := by dsimp only [ν]; infer_instance
    have hH := freyaHistoryAmbient q f τ O hservice batch
    have hM := freyaMaskHistoryAmbient q f τ O hservice batch a
    have hd := (freyaInvocationDataHistoryMeas q O batch).mono hH le_rfl
    have hcell : MeasurableSet (E∩F∩{z | (invocationData q O batch z).2.2.2.2=i}) :=
      ((hH _ hE).inter (hM _ hF)).inter ((hd.snd.snd.snd.snd) (measurableSet_singleton i))
    apply freyaFreshCoordinateEvent (rowLaw : Measure ChoiceRow) ν (O.law : Measure _) batch (i+a)
      _ hcell _ U hU
    intro t b ω row
    let z : Seed q.K × ((k : ℕ) → O.Seed k) := ((t,b),ω)
    let new : Seed q.K × ((k : ℕ) → O.Seed k) :=
      ((Function.update t batch (Function.update (t batch) (i+a) row),b),ω)
    have hd' : invocationData q O batch new=invocationData q O batch z := freyaDataReplace q O batch z _
    have he : new∈E ↔ z∈E := freyaPageHistoryEventInvariant q O z.1 new.1 ω batch rfl
      (fun j hj => Function.update_of_ne (by omega : j≠batch) _ t) E hE
    change (new∈E ∧ new∈F) ∧ (invocationData q O batch new).2.2.2.2=i ↔
      (z∈E ∧ z∈F) ∧ (invocationData q O batch z).2.2.2.2=i
    rw [hd',he]
    by_cases hi : (invocationData q O batch z).2.2.2.2=i
    · have hm : freyaMask q O batch a new=freyaMask q O batch a z :=
        freyaMaskReplaceCoordinate q O batch a i z row hi
      obtain ⟨V,hV,hFV⟩ := hF
      have hf : new∈F ↔ z∈F := by
        rw [← hFV]
        change freyaMask q O batch a new∈V ↔ freyaMask q O batch a z∈V
        rw [hm]
      rw [hf]
    · simp (config := { iota := false }) only [hi,and_false]
  have freyaChooseRemainingUniform (l : List ℕ) (hl : l.Nodup) (j : ℕ) :
      (rowLaw : Measure ChoiceRow) {row | chooseRemaining row l=some j}=
        if j∈l then (l.length : ℝ≥0∞)⁻¹ else 0 := by
    clear * - l hl j

    classical
    by_cases hj : j∈l
    · rw [ite_eq_left hj]
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hj
      have hlen : l.length≠0 := by have h := i.isLt; omega
      have hn : l.length-1+1=l.length := by omega
      let k : Fin (l.length-1+1) := Fin.cast hn.symm i
      have hchoice (row : ChoiceRow) : chooseRemaining row l=
          some (l.get (Fin.cast hn (row (l.length-1)))) := by
        dsimp only [chooseRemaining]
        rw [dite_eq_right hlen]
        rfl
      have he : {row : ChoiceRow | chooseRemaining row l=some j}=
          {row | row (l.length-1)=k} := by
        ext row
        simp (config := { iota := false }) only [Set.mem_ofPred_eq,hchoice,Option.some.injEq]
        constructor
        · intro h
          have hi' := hl.injective_get (h.trans hi.symm)
          apply Fin.ext
          change (row (l.length-1)).val=i.val
          exact congrArg (fun j : Fin l.length => j.val) hi'
        · intro h
          rw [h]
          exact hi
      rw [he]
      have hp := measurePreserving_eval_infinitePi
        (fun a : ℕ => (PMF.uniformOfFintype (Fin (a+1))).toMeasure) (l.length-1)
      have h := congrArg (fun μ => μ {k}) hp.map_eq
      rw [Measure.map_apply hp.measurable (measurableSet_singleton k)] at h
      change (rowLaw : Measure ChoiceRow) {row | row (l.length-1)=k}=_ at h
      rw [h]
      simp (config := { iota := false }) [PMF.uniformOfFintype_apply,hn]
    · rw [ite_eq_right hj]
      have he : {row : ChoiceRow | chooseRemaining row l=some j}=∅ := by
        ext row
        constructor
        · intro hrow
          change chooseRemaining row l=some j at hrow
          dsimp only [chooseRemaining] at hrow
          split at hrow
          · cases hrow
          · have he := Option.some.inj hrow
            exact hj (he ▸ List.get_mem l _)
        · intro hrow
          cases hrow
      rw [he,measure_empty]
  have freyaIntegralPartition {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
      [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : Measure Ω) (u : Ω → ι) (hu : Measurable u) (g : Ω → ℝ≥0∞) :
      (∫⁻ z,g z ∂P)=∑' i,∫⁻ z in {z | u z=i},g z ∂P := by
    clear * - Ω ι P u hu g

    have hm (i : ι) : MeasurableSet {z | u z=i} := hu (measurableSet_singleton i)
    have hd : Pairwise (fun i j : ι => Disjoint {z | u z=i} {z | u z=j}) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro z hi hj
      exact hij (hi.symm.trans hj)
    have he : (⋃ i : ι,{z | u z=i})=Set.univ := by
      ext z
      simp (config := { iota := false }) only [Set.mem_iUnion,Set.mem_ofPred_eq,exists_eq',Set.mem_univ]
    have h := lintegral_iUnion (μ:=P) hm hd g
    rw [he,Measure.restrict_univ] at h
    exact h
  have freyaChooseEventEq (l : List ℕ) (j : ℕ) :
      {row : ChoiceRow | l.toFinset.Nonempty ∧ (chooseRemaining row l).getD 0=j}=
        {row | chooseRemaining row l=some j} := by
    clear * - l j

    classical
    ext row
    by_cases hl : l=[]
    · subst l
      dsimp only [chooseRemaining]
      simp (config := { iota := false })
    · have hlen : l.length≠0 := fun h => hl (List.length_eq_zero_iff.mp h)
      have hn : l.toFinset.Nonempty := by
        cases l with
        | nil => exact (hl rfl).elim
        | cons v vs => exact ⟨v,List.mem_toFinset.mpr (List.mem_cons_self)⟩
      simp (config := { iota := false }) only [Set.mem_ofPred_eq]
      dsimp only [chooseRemaining]
      rw [dite_eq_right hlen]
      simp (config := { iota := false }) only [hn,true_and,Option.getD_some,Option.some.injEq]
  have freyaUniformByCells {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (I : Ω → ℕ) (L : Ω → List ℕ) (R : Ω → ℕ → ChoiceRow)
      (hI : Measurable I) (hL : Measurable L) (hR : Measurable R)
      (hnd : ∀ z,(L z).Nodup) (E : Set Ω) (hE : MeasurableSet E) (j : ℕ)
      (hind : ∀ i l U, MeasurableSet U →
        P ((E∩{z | I z=i ∧ L z=l})∩{z | R z i∈U})=
          P (E∩{z | I z=i ∧ L z=l})*(rowLaw : Measure ChoiceRow) U) :
      (∫⁻ z in E,if (L z).toFinset.Nonempty ∧ (chooseRemaining (R z (I z)) (L z)).getD 0=j
        then 1 else 0 ∂P)=
        ∫⁻ z in E,if j∈(L z).toFinset then ((L z).toFinset.card : ℝ≥0∞)⁻¹ else 0 ∂P := by
    clear * - Ω P I L R hI hL hR hnd E hE j hind freyaOptionSingleton freyaChooseRemainingMeas freyaChooseRemainingUniform freyaIntegralPartition freyaChooseEventEq

    classical
    let : MeasurableSingletonClass (Option ℕ) := freyaOptionSingleton
    rw [freyaIntegralPartition (P.restrict E) (fun z => (I z,L z)) (hI.prodMk hL),
      freyaIntegralPartition (P.restrict E) (fun z => (I z,L z)) (hI.prodMk hL)]
    apply tsum_congr
    rintro ⟨i,l⟩
    let A := E∩{z | I z=i ∧ L z=l}
    have hcell : MeasurableSet {z | (I z,L z)=(i,l)} := (hI.prodMk hL) (measurableSet_singleton (i,l))
    have hmeasure : (P.restrict E).restrict {z | (I z,L z)=(i,l)}=P.restrict A := by
      rw [Measure.restrict_restrict hcell]
      congr 1
      ext z
      simp (config := { iota := false }) only [A,Set.mem_inter_iff,Set.mem_ofPred_eq,Prod.mk.injEq,and_comm]
    rw [hmeasure]
    have hmA : MeasurableSet A := hE.inter
      ((hI (measurableSet_singleton i)).inter (hL (measurableSet_singleton l)))
    by_cases hAz : A.Nonempty
    · obtain ⟨w,hw⟩ := hAz
      have hl : l.Nodup := hw.2.2 ▸ hnd w
      have hleft : (∫⁻ z in A,if (L z).toFinset.Nonempty ∧
          (chooseRemaining (R z (I z)) (L z)).getD 0=j then 1 else 0 ∂P)=
          P (A∩{z | chooseRemaining (R z i) l=some j}) := by
        have he : (fun z => if (L z).toFinset.Nonempty ∧
            (chooseRemaining (R z (I z)) (L z)).getD 0=j then (1 : ℝ≥0∞) else 0)=ᵐ[P.restrict A]
            (fun z => if chooseRemaining (R z i) l=some j then 1 else 0) := by
          filter_upwards [ae_restrict_mem hmA] with z hz
          rw [hz.2.1,hz.2.2]
          have h := Set.ext_iff.mp (freyaChooseEventEq l j) (R z i)
          simp (config := { iota := false }) only [Set.mem_ofPred_eq] at h
          simp (config := { iota := false }) only [h]
        rw [lintegral_congr_ae he]
        have hs : MeasurableSet {z | chooseRemaining (R z i) l=some j} :=
          ((freyaChooseRemainingMeas l).comp ((measurable_pi_apply i).comp hR)) (measurableSet_singleton (some j))
        have hindicator : (fun z => if chooseRemaining (R z i) l=some j then (1 : ℝ≥0∞) else 0)=
            {z | chooseRemaining (R z i) l=some j}.indicator (fun _ => 1) := by
          funext z
          simp (config := { iota := false }) only [Set.indicator_apply,Set.mem_ofPred_eq]
        rw [hindicator,lintegral_indicator hs,lintegral_const,Measure.restrict_apply_univ,Measure.restrict_apply hs]
        simp (config := { iota := false }) only [one_mul,Set.inter_comm]
      have hprob := hind i l {row | chooseRemaining row l=some j}
        ((freyaChooseRemainingMeas l) (measurableSet_singleton (some j)))
      change P (A∩{z | chooseRemaining (R z i) l=some j})=
        P A*(rowLaw : Measure ChoiceRow) {row | chooseRemaining row l=some j} at hprob
      rw [hleft,hprob,freyaChooseRemainingUniform l hl j]
      have he : (fun z => if j∈(L z).toFinset then ((L z).toFinset.card : ℝ≥0∞)⁻¹ else 0)=ᵐ[P.restrict A]
          (fun _ => if j∈l then (l.length : ℝ≥0∞)⁻¹ else 0) := by
        filter_upwards [ae_restrict_mem hmA] with z hz
        rw [hz.2.2,List.toFinset_card_of_nodup hl]
        simp (config := { iota := false }) only [List.mem_toFinset]
      rw [lintegral_congr_ae he,lintegral_const,Measure.restrict_apply_univ,mul_comm]
    · have he : A=∅ := Set.not_nonempty_iff_eq_empty.mp hAz
      rw [he,Measure.restrict_empty]
      simp (config := { iota := false }) only [lintegral_zero_measure]
  have freyaConditionIntegralEq {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
      (E F : Set Ω) (hE : (P : Measure Ω) E≠0) (hF : MeasurableSet F)
      (g h : Ω → ℝ≥0∞)
      (he : (∫⁻ z in E∩F,g z ∂(P : Measure Ω))=∫⁻ z in E∩F,h z ∂(P : Measure Ω)) :
      (∫⁻ z in F,g z ∂(restrictedProbability P E hE : Measure Ω))=
        ∫⁻ z in F,h z ∂(restrictedProbability P E hE : Measure Ω) := by
    clear * - Ω P E F hE hF g h he

    change (∫⁻ z in F,g z ∂((P : Measure Ω) E)⁻¹ • (P : Measure Ω).restrict E)=
      ∫⁻ z in F,h z ∂((P : Measure Ω) E)⁻¹ • (P : Measure Ω).restrict E
    rw [Measure.restrict_smul,lintegral_smul_measure,lintegral_smul_measure,
      Measure.restrict_restrict hF,Set.inter_comm F E,he]
  have freyaRestartFullFresh (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
      (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
      (hservice : PrimitiveService f τ O) (batch : ℕ)
      (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
      (hEmeas : MeasurableSet[InvocationHistory q O batch] E)
      (hE : (executionLaw q O : Measure _) E≠0) :
      FullFresh (restrictedProbability (executionLaw q O) E hE)
        q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch) (restartAnswer q O batch) := by
    clear * - q f τ O hservice batch E hEmeas hE freyaHistoryAmbient freyaInvocationDataHistoryMeas freyaMaskHistory freyaMaskHistoryAmbient freyaMaskHistoryMonotone freyaMaskFactorMeas freyaMaskChoice freyaRestartContextMeas freyaDispatchContextNodup freyaRestartChoiceMeas freyaRestartContextHistoryMeas freyaMaskCellFresh freyaUniformByCells freyaConditionIntegralEq

    classical
    let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
    let H := freyaMaskHistory q O batch
    let C (a : ℕ) (z : Ω) := dispatchContext q.n (List.ofFn id) (0 : Space q.d) 0
      (restartedRows q O batch z) (fun k r => restartAnswer q O batch k r z) a
    let I (z : Ω) := (invocationData q O batch z).2.2.2.2
    have hCH (a : ℕ) : Measurable[H a] (C a) := freyaRestartContextHistoryMeas q f τ O hservice batch a
    have hCA (a : ℕ) : Measurable (C a) := freyaRestartContextMeas q f τ O hservice batch a
    have hMA (a : ℕ) : H a≤(inferInstance : MeasurableSpace Ω) := freyaMaskHistoryAmbient q f τ O hservice batch a
    have hHA := freyaHistoryAmbient q f τ O hservice batch
    have hIA : Measurable I := ((freyaInvocationDataHistoryMeas q O batch).mono hHA le_rfl).snd.snd.snd.snd
    have hEA : MeasurableSet E := hHA _ hEmeas
    refine ⟨H,freyaMaskHistoryMonotone q f τ O hservice batch,?_,?_,?_⟩
    · intro a
      refine ⟨hMA a,(measurable_of_countable (fun l : List ℕ => l.toFinset)).comp (hCH a).fst,
        freyaRestartChoiceMeas q f τ O hservice batch a,?_⟩
      intro F hF j
      have hFA : MeasurableSet F := hMA a _ hF
      let R (z : Ω) (i : ℕ) := z.1.1 batch (i+a)
      have hR : Measurable R := Measurable.of_eval fun i =>
        (measurable_pi_apply (i+a)).comp ((measurable_pi_apply batch).comp measurable_fst.fst)
      have hfresh := freyaUniformByCells (executionLaw q O : Measure Ω) I (fun z => (C a z).1) R
        hIA (hCA a).fst hR (fun z => freyaDispatchContextNodup q.n (List.ofFn id) 0 0 _ _ a)
        (E∩F) (hEA.inter hFA) j (by
          intro i l U hU
          have hL : MeasurableSet[H a] {z : Ω | (C a z).1=l} := (hCH a).fst (measurableSet_singleton l)
          have hc := freyaMaskCellFresh q f τ O hservice batch a i E (F∩{z | (C a z).1=l})
            hEmeas (hF.inter hL) U hU
          have hs : (E∩(F∩{z : Ω | (C a z).1=l})∩{z | (invocationData q O batch z).2.2.2.2=i})=
              ((E∩F)∩{z | I z=i ∧ (C a z).1=l}) := by
            ext z
            simp (config := { iota := false }) only [Set.mem_inter_iff,Set.mem_ofPred_eq,I]
            tauto
          rw [hs] at hc
          exact hc)
      have h := freyaConditionIntegralEq (executionLaw q O) E F hE hFA _ _ hfresh
      exact h
    · intro a
      exact ((measurable_of_countable (fun l : List ℕ => l.toFinset)).comp (hCH a).fst).prodMk
        ((hCH a).snd.fst.prodMk ((hCH a).snd.snd.fst.prodMk (hCH a).snd.snd.snd))
    · intro a
      exact freyaMaskFactorMeas q O batch (a+1) _ (freyaRestartChoiceMeas q f τ O hservice batch a)
        (freyaMaskChoice q O hservice.1.1 batch a)
  have _ := hm
  have _ := hn
  have _ := hS
  have _ := hK
  have _ := hinvoke
  have hp := freyaRestartPrimitive q f τ O hservice batch E hE
  exact ⟨hp.1,hp.2,freyaHistoryAmbient q f τ O hservice batch,
    freyaInvocationDataHistoryMeas q O batch,freyaRestartFullFresh q f τ O hservice batch E hEmeas hE⟩"#
      let parsedStx ← match parsed with
        | .ok stx => pure stx
        | .error msg => Lean.throwError msg
      withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := 8000000000 }) do
        Lean.Elab.Tactic.evalTactic parsedStx
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing


theorem conditional_full_cost (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (batch : ℕ)
    (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
    (hEmeas : MeasurableSet[InvocationHistory q O batch] E)
    (hfull : ∀ z ∈ E, ∃ x clock firstID,
      invocation q O z.1 z.2 batch = some (true, x, x, clock, firstID)) :
    let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
    (∫⁻ z in E, (batchElapsed q O z.1 z.2 batch : ℝ≥0∞) ∂P) ≤
      multisetTimeBound τ q.m * P E := by
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    classical
    dsimp only
    have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
        [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
        (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
        Measurable (fun z => f (g z) z) :=
      (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
        (measurable_id.prodMk hg)
    have freyaCondLIntegralLe {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        (E : Set Ω) (hE : (P : Measure Ω) E≠0) (g : Ω → ℝ≥0∞) (C : ℝ≥0∞)
        (h : (∫⁻ z,g z ∂(restrictedProbability P E hE : Measure Ω))≤C) :
        (∫⁻ z in E,g z ∂(P : Measure Ω))≤C*(P : Measure Ω) E := by
      change (∫⁻ z,g z ∂((P : Measure Ω) E)⁻¹ • (P : Measure Ω).restrict E)≤C at h
      rw [lintegral_smul_measure] at h
      simp (config := { iota := false }) only [smul_eq_mul] at h
      have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞)≤(P : Measure Ω) E from bot_le)
      rw [← mul_assoc,ENNReal.mul_inv_cancel hE (measure_ne_top _ _),one_mul] at hh
      simpa (config := { iota := false }) only [mul_comm] using hh
    by_cases hE : (executionLaw q O : Measure _) E=0
    · rw [Measure.restrict_eq_zero.mpr hE,lintegral_zero_measure]
      exact bot_le
    · have hi : ∀ z∈E,(invocation q O z.1 z.2 batch).isSome := by
        intro z hz
        obtain ⟨x,c,i,h⟩ := hfull z hz
        rw [h]; rfl
      obtain ⟨hprimitive,_,hambient,hdata,hfresh⟩ :=
        restart_service q hm hn hS hK f τ O hservice batch E hEmeas hi hE
      dsimp only [PrimitiveService, restartOracle] at hprimitive
      have hd := hdata.mono hambient le_rfl
      have hr : Measurable (restartedRows q O batch) := by
        apply Measurable.of_eval
        intro a
        exact freyaMeasurableSelect _ (hd.snd.snd.snd.snd.add_const a) (fun k z => z.1.1 batch k)
          (fun k => (measurable_pi_apply k).comp ((measurable_pi_apply batch).comp measurable_fst.fst))
      have ha (a : ℕ) : Measurable (fun z : Option (Request q.d q.m q.n) × (Seed q.K × ((k : ℕ) → O.Seed k)) =>
          restartAnswer q O batch a z.1 z.2) := by
        let h0 : HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) a :=
          ⟨List.replicate a ((0, none), none), List.length_replicate⟩
        have h := (hprimitive.1.2 a).comp (f := fun z : Option (Request q.d q.m q.n) ×
          (Seed q.K × ((k : ℕ) → O.Seed k)) => ((h0, ((0 : Fin 1), z.1)), z.2))
          ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
        convert h using 1
        funext z
        simp [answerAt, h0]
      have hdiag : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => fun _ : ℕ => z) :=
        Measurable.of_eval (fun _ => measurable_id)
      have hp := (ae_of_ae_map hdiag.aemeasurable hprimitive.2).mono fun z hz a => by
        simpa only [List.length_replicate] using hz (List.replicate a ((0, none), none))
      have hb := (full_gradient_time (restrictedProbability (executionLaw q O) E hE) hm q.n hn
        (0 : Space q.d) 0 (restartedRows q O batch) (fun (_ : Fin q.m) (_ : Space q.d) => 0)
        τ hmono (restartAnswer q O batch) hr ha hp hfresh).2
      have hz : (fun z => (((fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock - 0 : ℝ≥0) : ℝ≥0∞))=
          (fun z => ((fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
            (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock : ℝ≥0∞)) := by
        funext z
        exact congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (tsub_zero _)
      rw [hz] at hb
      let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
      have hEm := hambient E hEmeas
      have hpaths : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
        (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
      have he : (fun z => ((fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock : ℝ≥0∞))=ᵐ[
            (restrictedProbability (executionLaw q O) E hE : Measure _)]
          (fun z => (batchElapsed q O z.1 z.2 batch : ℝ≥0∞)) := by
        apply Measure.ae_smul_measure _ (P E)⁻¹
        filter_upwards [ae_restrict_of_ae hpaths,ae_restrict_mem hEm] with z hz hze
        obtain ⟨x,c,i,h⟩ := hfull z hze
        have hc := (restart_coupling q hm hn hS hK f τ O z hz batch i true x x c h).2
        simp (config := { iota := false }) only [ite_true] at hc
        exact congrArg (fun u : ℝ≥0 => (u : ℝ≥0∞)) hc
      rw [lintegral_congr_ae he] at hb
      exact freyaCondLIntegralLe (executionLaw q O) E hE _ _ hb


theorem conditional_full_cost_sharp (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hlarge : largeSample q.m q.n)
    (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (batch : ℕ)
    (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
    (hEmeas : MeasurableSet[InvocationHistory q O batch] E)
    (hfull : ∀ z ∈ E, ∃ x clock firstID,
      invocation q O z.1 z.2 batch = some (true, x, x, clock, firstID)) :
    let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
    (∫⁻ z in E, (batchElapsed q O z.1 z.2 batch : ℝ≥0∞) ∂P) ≤
      5 * equilibriumTime τ q.m * P E := by
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors in
    classical
    dsimp only
    have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
        [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
        (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
        Measurable (fun z => f (g z) z) :=
      (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
        (measurable_id.prodMk hg)
    have freyaCondLIntegralLe {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        (E : Set Ω) (hE : (P : Measure Ω) E≠0) (g : Ω → ℝ≥0∞) (C : ℝ≥0∞)
        (h : (∫⁻ z,g z ∂(restrictedProbability P E hE : Measure Ω))≤C) :
        (∫⁻ z in E,g z ∂(P : Measure Ω))≤C*(P : Measure Ω) E := by
      change (∫⁻ z,g z ∂((P : Measure Ω) E)⁻¹ • (P : Measure Ω).restrict E)≤C at h
      rw [lintegral_smul_measure] at h
      simp (config := { iota := false }) only [smul_eq_mul] at h
      have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞)≤(P : Measure Ω) E from bot_le)
      rw [← mul_assoc,ENNReal.mul_inv_cancel hE (measure_ne_top _ _),one_mul] at hh
      simpa (config := { iota := false }) only [mul_comm] using hh
    by_cases hE : (executionLaw q O : Measure _) E=0
    · rw [Measure.restrict_eq_zero.mpr hE,lintegral_zero_measure]
      exact bot_le
    · have hi : ∀ z∈E,(invocation q O z.1 z.2 batch).isSome := by
        intro z hz
        obtain ⟨x,c,i,h⟩ := hfull z hz
        rw [h]; rfl
      obtain ⟨hprimitive,_,hambient,hdata,hfresh⟩ :=
        restart_service q hm hn hS hK f τ O hservice batch E hEmeas hi hE
      dsimp only [PrimitiveService, restartOracle] at hprimitive
      have hd := hdata.mono hambient le_rfl
      have hr : Measurable (restartedRows q O batch) := by
        apply Measurable.of_eval
        intro a
        exact freyaMeasurableSelect _ (hd.snd.snd.snd.snd.add_const a) (fun k z => z.1.1 batch k)
          (fun k => (measurable_pi_apply k).comp ((measurable_pi_apply batch).comp measurable_fst.fst))
      have ha (a : ℕ) : Measurable (fun z : Option (Request q.d q.m q.n) × (Seed q.K × ((k : ℕ) → O.Seed k)) =>
          restartAnswer q O batch a z.1 z.2) := by
        let h0 : HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) a :=
          ⟨List.replicate a ((0, none), none), List.length_replicate⟩
        have h := (hprimitive.1.2 a).comp (f := fun z : Option (Request q.d q.m q.n) ×
          (Seed q.K × ((k : ℕ) → O.Seed k)) => ((h0, ((0 : Fin 1), z.1)), z.2))
          ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
        convert h using 1
        funext z
        simp [answerAt, h0]
      have hdiag : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => fun _ : ℕ => z) :=
        Measurable.of_eval (fun _ => measurable_id)
      have hp := (ae_of_ae_map hdiag.aemeasurable hprimitive.2).mono fun z hz a => by
        simpa only [List.length_replicate] using hz (List.replicate a ((0, none), none))
      have hb := full_gradient_time_sharp (restrictedProbability (executionLaw q O) E hE) hm q.n hn hlarge
        (0 : Space q.d) 0 (restartedRows q O batch) (fun (_ : Fin q.m) (_ : Space q.d) => 0)
        τ hmono (restartAnswer q O batch) hr ha hp hfresh
      have hz : (fun z => (((fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock - 0 : ℝ≥0) : ℝ≥0∞))=
          (fun z => ((fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
            (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock : ℝ≥0∞)) := by
        funext z
        exact congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (tsub_zero _)
      rw [hz] at hb
      let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
      have hEm := hambient E hEmeas
      have hpaths : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
        (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
      have he : (fun z => ((fullTrace q.n (List.ofFn id) (0 : Space q.d) 0 (restartedRows q O batch z)
          (fun a r => restartAnswer q O batch a r z) (q.n*q.m)).clock : ℝ≥0∞))=ᵐ[
            (restrictedProbability (executionLaw q O) E hE : Measure _)]
          (fun z => (batchElapsed q O z.1 z.2 batch : ℝ≥0∞)) := by
        apply Measure.ae_smul_measure _ (P E)⁻¹
        filter_upwards [ae_restrict_of_ae hpaths,ae_restrict_mem hEm] with z hz hze
        obtain ⟨x,c,i,h⟩ := hfull z hze
        have hc := (restart_coupling q hm hn hS hK f τ O z hz batch i true x x c h).2
        simp (config := { iota := false }) only [ite_true] at hc
        exact congrArg (fun u : ℝ≥0 => (u : ℝ≥0∞)) hc
      rw [lintegral_congr_ae he] at hb
      exact freyaCondLIntegralLe (executionLaw q O) E hE _ _ hb


theorem conditional_difference_cost (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (batch : ℕ)
    (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
    (hEmeas : MeasurableSet[InvocationHistory q O batch] E)
    (hdiff : ∀ z ∈ E, ∃ x y clock firstID,
      invocation q O z.1 z.2 batch = some (false, x, y, clock, firstID)) :
    let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
    (∫⁻ z in E, (batchElapsed q O z.1 z.2 batch : ℝ≥0∞) ∂P) ≤
      4 * equilibriumTime τ q.S * P E := by
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
      have freyaOptionSomeMeas {α : Type} [MeasurableSpace α] :
          Measurable (some : α → Option α) := by
        delta instMeasurableSpaceOption
        rw [measurable_comap_iff]
        exact measurable_inr
      have freyaLabelAtMeas (m : ℕ) : Measurable (fun row : ChoiceRow => labelAt row m) := by
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
        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inl
      have freyaPhaseDifferenceMeas {d m n : ℕ} :
          Measurable (Phase.difference : DifferenceState d m n → Phase d m n) := by
        change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_inr.comp measurable_inr
      have freyaPhaseParamMeas {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {d m n : ℕ}
          (p : Ω → Phase d m n) (hp : Measurable p) (b : Ω → β) (hb : Measurable b)
          (full : Ω × (Bool × FullState d m n) → β) (hfull : Measurable full)
          (diff : Ω × DifferenceState d m n → β) (hdiff : Measurable diff) :
          Measurable (fun z => (p z).casesOn (motive := fun _ => β) (fun first c => full (z,first,c))
            (fun c => diff (z,c)) (b z)) := by
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
        change Measurable[_,MeasurableSpace.comap freyaStateCode inferInstance] _
        rw [measurable_comap_iff]
        exact hseed.prodMk (hit.prodMk (hx.prodMk (hg.prodMk (hselected.prodMk (hc.prodMk (hid.prodMk hp))))))
      have freyaPageInitialMeas (q : Raw) : Measurable (initial q) := by
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
        exact (measurable_trajectory q O hservice.1.2 (freyaPageInitialMeas q)
          (freyaPageUpdateMeas q) (freyaPageQueryMeas q) k).1
      have freyaFindMeas {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α]
          (l : List α) (p : Ω → α → Bool) (hp : ∀ a,Measurable (fun z => p z a)) :
          Measurable (fun z => l.find? (p z)) := by
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
      let freyaLiftJob {d m : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ) (j : Job d m) : Job d m :=
        { j with kind := Sum.elim (fun _ => Sum.inl x) (fun _ => Sum.inr (x,y)) j.kind
                 started := clock+j.started
                 id := first+j.id }
      let freyaLiftRequest {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
          (r : Request d m n) : Request d m n :=
        ⟨clock+r.clock,fun i => (r.pending i).map (freyaLiftJob x y clock first)⟩
      have freyaLiftDeadline {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
          (τ : Fin n → ℝ≥0∞) (j : Job d m) (i : Fin n) :
          deadline τ (freyaLiftJob x y clock first j) i=clock+deadline τ j i := by
        dsimp [deadline,freyaLiftJob,jobWork]
        cases j.kind <;> dsimp only [Sum.elim] <;> simp (config := { iota := false }) [add_assoc]
      have freyaLiftLegal {d m n : ℕ} (x y : Space d) (clock : ℝ≥0) (first : ℕ)
          (τ : Fin n → ℝ≥0∞) (r : Request d m n) (hr : legalRequest τ r) :
          legalRequest τ (freyaLiftRequest x y clock first r) := by
        obtain ⟨⟨i,j,hj⟩,hr⟩ := hr
        constructor
        · exact ⟨i,freyaLiftJob x y clock first j,by simp (config := { iota := false }) [freyaLiftRequest,hj]⟩
        · intro i j hj
          obtain ⟨k,hk,rfl⟩ := Option.map_eq_some_iff.mp hj
          obtain ⟨hstart,hend⟩ := hr i k hk
          constructor
          · exact add_le_add le_rfl hstart
          · rw [freyaLiftDeadline]
            change ((clock+r.clock : ℝ≥0) : ℝ≥0∞)≤(clock : ℝ≥0∞)+deadline τ k i
            rw [ENNReal.coe_add]
            exact add_le_add le_rfl hend
      have freyaZeroJobValue {d m : ℕ} (j : Job d m) :
          jobValue (fun (_ : Fin m) (_ : Space d) => (0 : ℝ)) j=0 := by
        dsimp [jobValue]
        cases j.kind <;> dsimp only <;> simp (config := { iota := false })
      have freyaRestartServicePath (q : Raw) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (z : Seed q.K × ((k : ℕ) → O.Seed k))
          (hs : servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r))) (batch : ℕ) :
          servicePath (fun (_ : Fin q.m) (_ : Space q.d) => 0) τ
            (fun a r => restartAnswer q O batch a r z) := by
        intro a
        let data := invocationData q O batch z
        let call := (batchStartCall q O z.1 z.2 batch).getD 0+a
        have hlift (r : Request q.d q.m q.n) : liftRequest q O batch z (some r)=
            some (freyaLiftRequest data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 r) := by
          dsimp only [liftRequest,Option.map_some,freyaLiftRequest]
          congr 2
          funext i
          cases r.pending i with
          | none => rfl
          | some j =>
            dsimp only [Option.map_some,freyaLiftJob]
            cases j.kind <;> rfl
        constructor
        · have hnone := (hs call).1
          change replyAt q O z.1 z.2 call (0,none)=none at hnone
          change Option.map _ (replyAt q O z.1 z.2 call (0,none))=none
          rw [hnone]
          rfl
        · intro r hr
          let R := freyaLiftRequest data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 r
          obtain ⟨i,j,c,hj,ha,hc,hend⟩ := (hs call).2 R
            (freyaLiftLegal _ _ _ _ τ r hr)
          obtain ⟨k,hk,hkj⟩ := Option.map_eq_some_iff.mp hj
          subst j
          change data.2.2.2.1+r.clock≤c at hc
          change replyAt q O z.1 z.2 call (0,some R)=some
            (i,data.2.2.2.2+k.id,c,jobValue f (freyaLiftJob data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 k)) at ha
          have ht : data.2.2.2.1≤c := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤r.clock from bot_le)).trans hc
          refine ⟨i,k,c-data.2.2.2.1,hk,?_,?_,?_⟩
          · change Option.map (fun t : Fin q.n × ℕ × ℝ≥0 × Space q.d =>
              (t.1,t.2.1-data.2.2.2.2,t.2.2.1-data.2.2.2.1,(0 : Space q.d)))
              (replyAt q O z.1 z.2 call (0,liftRequest q O batch z (some r)))=_
            rw [hlift]
            change Option.map _ (replyAt q O z.1 z.2 call (0,some R))=_
            rw [ha]
            dsimp only [Option.map_some]
            rw [Nat.add_sub_cancel_left,freyaZeroJobValue]
          · exact (le_tsub_iff_right ht).mpr (by simpa (config := { iota := false }) only [add_comm] using hc)
          · intro i' k' hk'
            have h := hend i' (freyaLiftJob data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2 k')
              (by simp (config := { iota := false }) [R,freyaLiftRequest,hk'])
            rw [freyaLiftDeadline] at h
            have he : (c : ℝ≥0∞)=data.2.2.2.1+(c-data.2.2.2.1 : ℝ≥0) := by
              rw [← ENNReal.coe_add,add_tsub_cancel_of_le ht]
            rw [he] at h
            exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).mp h
      have freyaConditionalDifferenceCost (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
          (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
          (τ : Fin q.n → ℝ≥0∞) (hmono : Monotone τ)
          (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
          (hservice : PrimitiveService f τ O) (batch : ℕ)
          (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
          (hEmeas : MeasurableSet[InvocationHistory q O batch] E)
          (hdiff : ∀ z∈E,∃ x y clock firstID,
            invocation q O z.1 z.2 batch=some (false,x,y,clock,firstID)) :
          (∫⁻ z in E,(batchElapsed q O z.1 z.2 batch : ℝ≥0∞) ∂(executionLaw q O : Measure _))≤
            4*equilibriumTime τ q.S*(executionLaw q O : Measure _) E := by
        let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
        have hEm : MeasurableSet E := freyaHistoryAmbient q f τ O hservice batch E hEmeas
        have hs : ∀ᵐ z ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
          (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
        have hbound : ∀ᵐ z ∂P.restrict E,
            (batchElapsed q O z.1 z.2 batch : ℝ≥0∞)≤4*equilibriumTime τ q.S := by
          filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem hEm] with z hz hze
          obtain ⟨x,y,clock,firstID,hi⟩ := hdiff z hze
          have hcouple := (restart_coupling q hm hn hS hK f τ O z hz batch firstID false x y clock hi).2
          simp (config := { iota := false }) only [Bool.false_eq_true,ite_false] at hcouple
          have ht := difference_time hm q.n q.S hn hS (0 : Space q.d) 0 0
            (restartedRows q O batch z) (fun (_ : Fin q.m) (_ : Space q.d) => (0 : ℝ)) τ hmono
            (fun a r => restartAnswer q O batch a r z) (freyaRestartServicePath q f τ O z hz batch)
          simpa (config := { iota := false }) only [tsub_zero,hcouple] using ht
        have h := lintegral_mono_ae hbound
        simpa (config := { iota := false }) only [lintegral_const,Measure.restrict_apply_univ] using h
      exact freyaConditionalDifferenceCost q hm hn hS hK f τ hmono O hservice batch E hEmeas hdiff


end LongTails.Proofs.FreyaConditionalCosts
