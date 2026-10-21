import outputs.Proofs.SingleOracleCounted
import outputs.Proofs.RennalaTiming
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory

namespace OracleTemplate.Rennala

noncomputable def skeleton (p : Public) (tau : Fin p.n → ℝ) (r : ℕ) : State p :=
  workerState p tau (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r

def acceptedSlot (p : Public) (tau : Fin p.n → ℝ) (r : ℕ) : Prop :=
  let s := skeleton p tau r
  match eventAnswer p tau (fun _ (_ : Unit) => 0) (some s.jobs) () with
  | none => False
  | some (_, _, tag, _) => tag = s.iteration

noncomputable def sampleIndex (p : Public) (tau : Fin p.n → ℝ) (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ r, acceptedSlot p tau r ∧
      (skeleton p tau r).iteration * batchSize p.v p.eps + (skeleton p tau r).count = k
    then Nat.find h else 0

noncomputable def completionIndex (p : Public) (tau : Fin p.n → ℝ) (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ r, (skeleton p tau r).iteration = k then Nat.find h else 0

noncomputable def completionClock (p : Public) (tau : Fin p.n → ℝ) (k : ℕ) : ℝ :=
  (skeleton p tau (completionIndex p tau k)).clock

lemma schedule_deterministic (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) {Ω : Type} (g : Point p.d → Ω → Point p.d)
    (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω) (r : ℕ) :
    let s := workerState p tau g j seeds r
    let z := skeleton p tau r
    s.iteration = z.iteration ∧ s.count = z.count ∧ s.clock = z.clock ∧
      ∀ i, (s.jobs i).started = (z.jobs i).started ∧ (s.jobs i).tag = (z.jobs i).tag := by
  classical
  induction r with
  | zero =>
    exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | succ r ih =>
    let s := workerState p tau g j seeds r
    let z := skeleton p tau r
    rcases ih with ⟨hiter, hcount, hclock, hjobs⟩
    change s.iteration = z.iteration at hiter
    change s.count = z.count at hcount
    change ∀ i, (s.jobs i).started = (z.jobs i).started ∧ (s.jobs i).tag = (z.jobs i).tag at hjobs
    have hstarts : (fun a => (s.jobs a).started) = (fun a => (z.jobs a).started) :=
      funext (fun a => (hjobs a).1)
    obtain ⟨i, hi, hmin⟩ := (schedule_invariants p hn tau htau
      (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r).2.2.2.2
    change nextWorker tau (fun a => (z.jobs a).started) (List.finRange p.n) = some i at hi
    change let s' := updateCore p s (eventAnswer p tau g (some s.jobs) (seeds r))
           let z' := updateCore p z (eventAnswer p tau (fun _ (_ : Unit) => 0) (some z.jobs) ())
           s'.iteration = z'.iteration ∧ s'.count = z'.count ∧ s'.clock = z'.clock ∧
             ∀ a, (s'.jobs a).started = (z'.jobs a).started ∧ (s'.jobs a).tag = (z'.jobs a).tag
    dsimp only [eventAnswer]
    rw [hstarts, hi]
    dsimp only [updateCore]
    simp only [(hjobs i).1, (hjobs i).2, hiter, hcount]
    split_ifs <;> refine ⟨rfl, rfl, rfl, ?_⟩ <;> intro a
    all_goals
      by_cases ha : a = i
      · subst a
        simp [Function.update, hiter]
      · simpa [Function.update, ha] using hjobs a


lemma fresh_batch_law (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) {Ω : Type} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω))) (g : Point p.d → Ω → Point p.d) :
    Function.Injective (sampleIndex p tau) ∧
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ (sampleIndex p tau k))
      (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
    ∀ (k : ℕ) (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω),
      (workerState p tau g j seeds (completionIndex p tau k)).point =
        iterate g (stepSize p.L p.v p.eps) (batchSize p.v p.eps) p.x0
          (fun a => seeds (sampleIndex p tau a)) k := by
  classical
  let S := batchSize p.v p.eps
  have hSdef : batchSize p.v p.eps = S := rfl
  let z := skeleton p tau
  let counter := fun r => (z r).iteration * S + (z r).count
  have hS : 0 < S := by dsimp [S, batchSize]; omega
  have hexiter : ∀ k, ∃ r, (z r).iteration = k := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨q, _, _, hq, _⟩ := batch_event_bound p hn tau htau
        (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r
      exact ⟨q, hq.trans (congrArg (fun a => a + 1) hr)⟩
  have hcstep : ∀ r, counter (r + 1) = counter r + if acceptedSlot p tau r then 1 else 0 := by
    intro r
    have hs := schedule_invariants p hn tau htau
      (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r
    obtain ⟨i, hi, _⟩ := hs.2.2.2.2
    change nextWorker tau (fun a => ((z r).jobs a).started) (List.finRange p.n) = some i at hi
    have ha : acceptedSlot p tau r ↔ ((z r).jobs i).tag = (z r).iteration := by
      dsimp only [acceptedSlot, eventAnswer]
      rw [hi]
    have heq : z (r + 1) = updateCore p (z r)
        (some (i, ((z r).jobs i).started + tau i, ((z r).jobs i).tag, 0)) := by
      dsimp only [z, skeleton, workerState, eventAnswer] at hi ⊢
      rw [hi]
    by_cases htag : ((z r).jobs i).tag = (z r).iteration
    · have har : acceptedSlot p tau r := ha.mpr htag
      by_cases hfull : (z r).count + 1 = S
      · dsimp only [counter]
        rw [heq]
        dsimp only [updateCore]
        simp only [htag, ite_true, hSdef, hfull, har, Nat.add_mul, Nat.one_mul]
        omega
      · dsimp only [counter]
        rw [heq]
        dsimp only [updateCore]
        simp only [htag, ite_true, hSdef, hfull, ite_false, har]
        omega
    · have har : ¬acceptedSlot p tau r := fun h => htag (ha.mp h)
      have hfull : (z r).count ≠ S := Nat.ne_of_lt hs.2.1
      dsimp only [counter]
      rw [heq]
      dsimp only [updateCore]
      simp only [htag, ite_false, hSdef, hfull, har]
      omega
  have hmono : Monotone counter := monotone_nat_of_le_succ (fun r => by rw [hcstep]; omega)
  have hexslot : ∀ k, ∃ r, acceptedSlot p tau r ∧ counter r = k := by
    intro k
    obtain ⟨t, ht⟩ := hexiter (k + 1)
    have hex : ∃ t, k < counter t := by
      refine ⟨t, ?_⟩
      dsimp only [counter]
      rw [ht]
      nlinarith
    let t := Nat.find hex
    have ht : k < counter t := Nat.find_spec hex
    have htpos : 0 < t := by
      by_contra hh
      have htzero : t = 0 := by omega
      have hc0 : counter 0 = 0 := by dsimp only [counter, z, skeleton, workerState, initialState]; omega
      rw [htzero, hc0] at ht
      omega
    have hprev : counter (t - 1) ≤ k := by
      have hh := Nat.find_min hex (show t - 1 < t by omega)
      omega
    have hnext := hcstep (t - 1)
    have hteq : t - 1 + 1 = t := by omega
    rw [hteq] at hnext
    by_cases ha : acceptedSlot p tau (t - 1)
    · refine ⟨t - 1, ha, ?_⟩
      simp only [ha, ite_true] at hnext
      omega
    · simp only [ha, ite_false] at hnext
      omega
  have hslot_unique : ∀ r t, acceptedSlot p tau r → acceptedSlot p tau t → counter r = counter t → r = t := by
    intro r t hr ht heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh := hmono (show r + 1 ≤ t by omega)
      rw [hcstep, ite_eq_left hr] at hh
      omega
    · have hh := hmono (show t + 1 ≤ r by omega)
      rw [hcstep, ite_eq_left ht] at hh
      omega
  have hsample_spec : ∀ k, acceptedSlot p tau (sampleIndex p tau k) ∧ counter (sampleIndex p tau k) = k := by
    intro k
    have he := hexslot k
    change ∃ r, acceptedSlot p tau r ∧ (skeleton p tau r).iteration * batchSize p.v p.eps +
      (skeleton p tau r).count = k at he
    dsimp only [sampleIndex]
    rw [dite_eq_left he]
    exact Nat.find_spec he
  have hsample : ∀ r, acceptedSlot p tau r → sampleIndex p tau (counter r) = r := by
    intro r hr
    have hs := hsample_spec (counter r)
    exact hslot_unique _ r hs.1 hr hs.2
  have hinj : Function.Injective (sampleIndex p tau) := by
    intro a b hab
    exact (hsample_spec a).2.symm.trans ((congrArg counter hab).trans (hsample_spec b).2)
  refine ⟨hinj, ⟨fun k => hiid.measurable _, hiid.independent.precomp hinj, fun k => hiid.marginal _⟩, ?_⟩
  intro k j seeds
  let X := iterate g (stepSize p.L p.v p.eps) S p.x0 (fun a => seeds (sampleIndex p tau a))
  let F := fun k c => (1 / (S : ℝ)) • ∑ a ∈ Finset.range c, g (X k) (seeds (sampleIndex p tau (k * S + a)))
  have hpath : ∀ r, let s := workerState p tau g j seeds r
      s.point = X s.iteration ∧ s.accumulator = F s.iteration s.count := by
    intro r
    induction r with
    | zero => dsimp only [workerState, initialState, X, iterate, F]; simp
    | succ r ih =>
      let s := workerState p tau g j seeds r
      have hs := schedule_invariants p hn tau htau g j seeds r
      have hd := schedule_deterministic p hn tau htau g j seeds r
      obtain ⟨i, hi, _⟩ := hs.2.2.2.2
      change nextWorker tau (fun a => (s.jobs a).started) (List.finRange p.n) = some i at hi
      have heq : workerState p tau g j seeds (r + 1) = updateCore p s
          (some (i, (s.jobs i).started + tau i, (s.jobs i).tag, g (s.jobs i).point (seeds r))) := by
        change updateCore p s (eventAnswer p tau g (some s.jobs) (seeds r)) = _
        dsimp only [eventAnswer]
        rw [hi]
      change s.point = X s.iteration ∧ s.accumulator = F s.iteration s.count at ih
      have hstarts : (fun a => (s.jobs a).started) = (fun a => ((z r).jobs a).started) :=
        funext (fun a => (hd.2.2.2 a).1)
      have hznext : nextWorker tau (fun a => ((z r).jobs a).started) (List.finRange p.n) = some i := by
        rw [← hstarts]
        exact hi
      by_cases htag : (s.jobs i).tag = s.iteration
      · have hzaccepted : acceptedSlot p tau r := by
          dsimp only [acceptedSlot, eventAnswer]
          rw [hznext]
          exact (hd.2.2.2 i).2.symm.trans (htag.trans hd.1)
        have hind : sampleIndex p tau (s.iteration * S + s.count) = r := by
          rw [hd.1, hd.2.1]
          exact hsample r hzaccepted
        have hpoint : (s.jobs i).point = X s.iteration := (hs.2.2.1 i).2.2.2 htag |>.trans ih.1
        have hadd : s.accumulator + (1 / (S : ℝ)) • g (s.jobs i).point (seeds r) = F s.iteration (s.count + 1) := by
          rw [ih.2, hpoint]
          simp only [F, Finset.sum_range_succ, smul_add, hind]
        by_cases hfull : s.count + 1 = S
        · have hnext : X (s.iteration + 1) = X s.iteration - stepSize p.L p.v p.eps • F s.iteration S := by
            dsimp only [X, iterate, batchEstimator, F]
            exact congrArg
              (fun v : Point p.d => X s.iteration - stepSize p.L p.v p.eps • ((1 / (S : ℝ)) • v))
              (Fin.sum_univ_eq_sum_range (fun a => g (X s.iteration)
                (seeds (sampleIndex p tau (s.iteration * S + a)))) S)
          rw [heq]
          dsimp only [updateCore]
          simp only [htag, ite_true, hSdef, hfull, hadd]
          constructor
          · rw [ih.1, ← hnext]
          · simp [F]
        · rw [heq]
          dsimp only [updateCore]
          simp only [htag, ite_true, hSdef, hfull, ite_false]
          exact ⟨ih.1, hadd⟩
      · have hfull : s.count ≠ S := Nat.ne_of_lt hs.2.1
        rw [heq]
        dsimp only [updateCore]
        simp only [htag, ite_false, hSdef, hfull]
        exact ih
  have he := hexiter k
  change ∃ r, (skeleton p tau r).iteration = k at he
  have hcompletion : (skeleton p tau (completionIndex p tau k)).iteration = k := by
    dsimp only [completionIndex]
    rw [dite_eq_left he]
    exact Nat.find_spec he
  have hp := (hpath (completionIndex p tau k)).1
  rw [(schedule_deterministic p hn tau htau g j seeds (completionIndex p tau k)).1, hcompletion] at hp
  exact hp


lemma execute_prefix (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (B : ℕ) (hB : p.horizon * (batchSize p.v p.eps + p.n) ≤ B)
    (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω) :
    executeCounted (eventOracle p tau P g) (algorithm p) B j seeds =
      ((iterate g (stepSize p.L p.v p.eps) (batchSize p.v p.eps) p.x0
          (fun a => seeds (sampleIndex p tau a)) j.val,
        completionClock p tau p.horizon), B) := by
  classical
  let st := workerState p tau g j seeds
  let X := iterate g (stepSize p.L p.v p.eps) (batchSize p.v p.eps) p.x0
    (fun a => seeds (sampleIndex p tau a))
  let μ₀ : ProbabilityMeasure Ω := ⟨Measure.dirac (seeds 0), inferInstance⟩
  let P₀ : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.infinitePi (fun _ : ℕ => (μ₀ : Measure Ω)), inferInstance⟩
  have hiid₀ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
      (μ₀ : Measure Ω) (P₀ : Measure (ℕ → Ω)) := by
    refine ⟨fun k => measurable_pi_apply k, ?_, ?_⟩
    · exact ProbabilityTheory.iIndepFun_infinitePi (X := fun _ (ω : Ω) => ω) (fun _ => measurable_id)
    · intro k
      exact Measure.infinitePi_map_eval _ _
  have hpoint : ∀ k, (st (completionIndex p tau k)).point = X k :=
    fun k => (fresh_batch_law p hn tau htau μ₀ P₀ hiid₀ g).2.2 k j seeds
  have hex : ∀ k, ∃ r, (skeleton p tau r).iteration = k ∧
      r ≤ k * (batchSize p.v p.eps + p.n) := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr, hbound⟩ := ih
      obtain ⟨q, _, hq, hiter, _⟩ := batch_event_bound p hn tau htau
        (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r
      change (skeleton p tau q).iteration = (skeleton p tau r).iteration + 1 at hiter
      refine ⟨q, by simpa [hr] using hiter, ?_⟩
      nlinarith
  have hcomplete : ∀ k, (st (completionIndex p tau k)).iteration = k ∧
      completionIndex p tau k ≤ k * (batchSize p.v p.eps + p.n) := by
    intro k
    obtain ⟨r, hr, hb⟩ := hex k
    have he : ∃ r, (skeleton p tau r).iteration = k := ⟨r, hr⟩
    have hspec : (skeleton p tau (completionIndex p tau k)).iteration = k := by
      dsimp only [completionIndex]
      rw [dite_eq_left he]
      exact Nat.find_spec he
    refine ⟨(schedule_deterministic p hn tau htau g j seeds _).1.trans hspec, ?_⟩
    dsimp only [completionIndex]
    rw [dite_eq_left he]
    exact (Nat.find_min' he hr).trans hb
  have hchosen : ∀ r, (st r).chosenIndex = j := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      change (updateCore p (st r) (eventAnswer p tau g (some (st r).jobs) (seeds r))).chosenIndex = j
      cases ha : eventAnswer p tau g (some (st r).jobs) (seeds r) with
      | none => exact ih
      | some answer =>
        rcases answer with ⟨i, t, tag, value⟩
        dsimp only [updateCore]
        split_ifs <;> exact ih
  have htrans : ∀ r,
      ((st (r + 1)).iteration = (st r).iteration ∧ (st (r + 1)).selected = (st r).selected) ∨
      ((st (r + 1)).iteration = (st r).iteration + 1 ∧
        (st (r + 1)).selected = if j.val = (st r).iteration + 1 then (st (r + 1)).point else (st r).selected) := by
    intro r
    change let s' := updateCore p (st r) (eventAnswer p tau g (some (st r).jobs) (seeds r))
           (s'.iteration = (st r).iteration ∧ s'.selected = (st r).selected) ∨
           (s'.iteration = (st r).iteration + 1 ∧
             s'.selected = if j.val = (st r).iteration + 1 then s'.point else (st r).selected)
    cases ha : eventAnswer p tau g (some (st r).jobs) (seeds r) with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some answer =>
      rcases answer with ⟨i, t, tag, value⟩
      dsimp only [updateCore]
      simp only [hchosen]
      split_ifs <;> simp_all
  have hmono : Monotone (fun r => (st r).iteration) :=
    monotone_nat_of_le_succ (fun r => by rcases htrans r with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  have hfirst : ∀ r, (st (r + 1)).iteration = (st r).iteration + 1 →
      completionIndex p tau (st (r + 1)).iteration = r + 1 := by
    intro r hr
    let k := (st (r + 1)).iteration
    have he : ∃ t, (skeleton p tau t).iteration = k :=
      ⟨r + 1, (schedule_deterministic p hn tau htau g j seeds (r + 1)).1.symm⟩
    have hle : completionIndex p tau k ≤ r + 1 := by
      dsimp only [completionIndex]
      rw [dite_eq_left he]
      exact Nat.find_min' he (schedule_deterministic p hn tau htau g j seeds (r + 1)).1.symm
    have hc := (hcomplete k).1
    have hnot : ¬completionIndex p tau k ≤ r := by
      intro h
      have hh := hmono h
      change (st (completionIndex p tau k)).iteration ≤ (st r).iteration at hh
      rw [hc] at hh
      have hk : k = (st r).iteration + 1 := hr
      omega
    change completionIndex p tau k = r + 1
    omega
  have hselected : ∀ r, j.val ≤ (st r).iteration → (st r).selected = X j.val := by
    intro r
    induction r with
    | zero =>
      intro hj
      have hj0 : j.val = 0 := by change j.val ≤ 0 at hj; omega
      rw [hj0]
      rfl
    | succ r ih =>
      intro hj
      rcases htrans r with ⟨hiter, hsel⟩ | ⟨hiter, hsel⟩
      · exact hsel.trans (ih (by omega))
      · by_cases hjnext : j.val = (st r).iteration + 1
        · rw [hsel, ite_eq_left hjnext]
          have hp := hpoint (st (r + 1)).iteration
          rw [hfirst r hiter] at hp
          simpa only [hiter, ← hjnext] using hp
        · rw [hsel, ite_eq_right hjnext]
          exact ih (by omega)
  let T := completionIndex p tau p.horizon
  have hT : (st T).iteration = p.horizon := (hcomplete _).1
  have hTB : T ≤ B := (hcomplete _).2.trans hB
  have hbefore : ∀ r, r < T → (st r).iteration < p.horizon := by
    intro r hr
    have hle : (st r).iteration ≤ p.horizon := (hmono (le_of_lt hr)).trans_eq hT
    have hne : (st r).iteration ≠ p.horizon := by
      intro hh
      obtain ⟨u, hu, _⟩ := hex p.horizon
      have he : ∃ u, (skeleton p tau u).iteration = p.horizon := ⟨u, hu⟩
      have hmin : T ≤ r := by
        dsimp only [T]
        dsimp only [completionIndex]
        rw [dite_eq_left he]
        exact Nat.find_min' he ((schedule_deterministic p hn tau htau g j seeds r).1.symm.trans hh)
      omega
    omega
  let stopped := fun r => if r < T then st r else st T
  let step := fun r (s : State p) => (algorithm p).update s
    ((eventOracle p tau P g).answer r ((algorithm p).query s) (seeds r))
  have hstopped : ∀ r, step r (stopped r) = stopped (r + 1) := by
    intro r
    by_cases hr : r < T
    · have hi : ¬p.horizon ≤ (st r).iteration := by have := hbefore r hr; omega
      have hnext : step r (stopped r) = st (r + 1) := by
        dsimp only [step, algorithm, eventOracle, update]
        simp only [stopped, hr, ite_true, hi, ite_false]
        rfl
      rw [hnext]
      by_cases hrnext : r + 1 < T
      · simp only [stopped, hrnext, ite_true] <;> rfl
      · have heq : r + 1 = T := by omega
        simp [stopped, heq] <;> rfl
    · have hi : p.horizon ≤ (st T).iteration := le_of_eq hT.symm
      have hrnext : ¬r + 1 < T := by omega
      dsimp only [step, algorithm, eventOracle, update]
      simp only [stopped, hr, hrnext, ite_false, hi, ite_true]
  have hadvance : ∀ K r, StochasticGradient.advance step K r (stopped r) = stopped (r + K) := by
    intro K
    induction K with
    | zero => intro r; rfl
    | succ K ih =>
      intro r
      change StochasticGradient.advance step K (r + 1) (step r (stopped r)) = stopped (r + (K + 1))
      rw [hstopped, ih]
      congr 1
      omega
  have hinit : (algorithm p).initial j = stopped 0 := by
    by_cases h0 : 0 < T
    · simp only [stopped, h0, ite_true]
      rfl
    · have hT0 : T = 0 := by omega
      simp only [stopped, h0, ite_false, hT0]
      rfl
  have hexe := executeCounted_advance (eventOracle p tau P g) (algorithm p) B j seeds
  change executeCounted (eventOracle p tau P g) (algorithm p) B j seeds =
    ((algorithm p).output (StochasticGradient.advance step B 0 ((algorithm p).initial j)), B) at hexe
  have hav : StochasticGradient.advance step B 0 ((algorithm p).initial j) = stopped (0 + B) := by
    rw [hinit]
    exact hadvance B 0
  have hexe2 := hexe.trans (congrArg (fun s : State p => ((algorithm p).output s, B)) hav)
  have hstopB : stopped (0 + B) = st T := by simp only [zero_add, stopped, not_lt.mpr hTB, ite_false]
  rw [hstopB] at hexe2
  calc
    _ = ((algorithm p).output (st T), B) := hexe2
    _ = _ := by
      change (((st T).selected, (st T).clock), B) = ((X j.val, completionClock p tau p.horizon), B)
      have hsel : (st T).selected = X j.val := hselected T (by have := j.isLt; omega)
      have hclock : (st T).clock = completionClock p tau p.horizon :=
        (schedule_deterministic p hn tau htau g j seeds T).2.2.1
      rw [hsel, hclock]


lemma execution_cost (p : Public) (hn : 0 < p.n) (tau : Fin p.n → ℝ)
    (htau : ∀ i, 0 < tau i) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d) :
    completionIndex p tau p.horizon ≤ p.horizon * (batchSize p.v p.eps + p.n) ∧
    p.n + completionIndex p tau p.horizon ≤ p.n + p.horizon * (batchSize p.v p.eps + p.n) ∧
    p.n + 2 * completionIndex p tau p.horizon ≤ p.n + 2 * p.horizon * (batchSize p.v p.eps + p.n) ∧
    ∀ (B : ℕ) (j : Fin (p.horizon + 1)) (seeds : ℕ → Ω),
      (executeCounted (eventOracle p tau P g) (algorithm p) B j seeds).2 = B := by
  classical
  have hex : ∀ k, ∃ r, (skeleton p tau r).iteration = k ∧
      r ≤ k * (batchSize p.v p.eps + p.n) := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr, hbound⟩ := ih
      obtain ⟨q, hrq, hq, hiter, hpref⟩ := batch_event_bound p hn tau htau
        (fun _ (_ : Unit) => 0) ⟨0, Nat.succ_pos _⟩ (fun _ => ()) r
      change (skeleton p tau q).iteration = (skeleton p tau r).iteration + 1 at hiter
      refine ⟨q, by simpa [hr] using hiter, ?_⟩
      calc
        q ≤ r + (batchSize p.v p.eps + p.n) := hq
        _ ≤ k * (batchSize p.v p.eps + p.n) + (batchSize p.v p.eps + p.n) := by omega
        _ = (k + 1) * (batchSize p.v p.eps + p.n) := by ring
  have hbound : completionIndex p tau p.horizon ≤ p.horizon * (batchSize p.v p.eps + p.n) := by
    obtain ⟨r, hr, hb⟩ := hex p.horizon
    have he : ∃ r, (skeleton p tau r).iteration = p.horizon := ⟨r, hr⟩
    dsimp only [completionIndex]
    rw [dite_eq_left he]
    exact (Nat.find_min' he hr).trans hb
  refine ⟨hbound, by omega, by nlinarith, ?_⟩
  intro B j seeds
  exact congrArg Prod.snd (executeCounted_advance (eventOracle p tau P g) (algorithm p) B j seeds)


end OracleTemplate.Rennala
