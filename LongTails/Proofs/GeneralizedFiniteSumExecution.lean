import LongTails.Proofs.GeneralizedFiniteSumConvergence
import LongTails.Proofs.Execution

namespace OracleTemplate.GeneralizedFiniteSum

open LongTails.Setups.GeneralizedSmoothFiniteSum

noncomputable def localStep (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p) : LocalState p :=
  let q := localQuery p s
  localUpdate p s (f q.1 q.2, g q.1 q.2)

lemma localStep_absorbing (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p) (h : s.phase = 4) :
    localStep p f g s = s := by
  simp [localStep, localUpdate, h]

lemma local_cache_queries (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p) :
    (localStep p f g)^[p.n] {s with phase := 1, index := 0} =
      {s with phase := 2, index := 0, cached := fun i => g i s.snapshot} := by
  classical
  let cache := fun j : ℕ => fun i : Fin p.n =>
    if i.val < j then g i s.snapshot else s.cached i
  have hi : ∀ j, j ≤ p.n →
      (localStep p f g)^[j] {s with phase := 1, index := 0} =
        {s with
          phase := (if j < p.n then 1 else 2)
          index := (if j < p.n then j else 0)
          cached := cache j} := by
    intro j hj
    induction j with
    | zero => simp [cache, NeZero.pos p.n]
    | succ j ih =>
      have hjn : j < p.n := by omega
      have hc : Function.update (cache j) ⟨j % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩
          (g ⟨j % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ s.snapshot) = cache (j + 1) := by
        funext i
        by_cases he : i.val = j
        · have hei : i = ⟨j % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ := by
            apply Fin.ext
            simpa [Nat.mod_eq_of_lt hjn] using he
          subst i
          simp [cache, Nat.mod_eq_of_lt hjn]
        · have hei : i ≠ ⟨j % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ := by
            intro hh
            exact he (by simpa [Nat.mod_eq_of_lt hjn] using congrArg Fin.val hh)
          simp only [Function.update_of_ne hei, cache]
          split_ifs <;> first | rfl | omega
      rw [Function.iterate_succ_apply', ih (by omega)]
      simp only [ite_eq_left hjn]
      by_cases hnext : j + 1 < p.n <;>
        simp [localStep, localQuery, localUpdate, hnext, hc]
  rw [hi p.n le_rfl]
  have hc : cache p.n = fun i => g i s.snapshot := by
    funext i
    simp [cache, i.isLt]
  simp [hc]

noncomputable def coreState (p : Params) (s : LocalState p) (c : LocalCore p)
    (seeds : List (Fin ((2 * p.n).factorial))) (cache : Fin p.n → p.E) : LocalState p :=
  {s with
    phase := (if c.epoch < epochCount p then (if c.index = 0 then 1 else 2) else 3)
    index := c.index, epoch := c.epoch, samples := seeds, snapshot := c.snapshot,
    dual := c.dual, cached := cache, accumulated := c.outputs.sum}

lemma local_inner_query (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p) (c : LocalCore p)
    (seed : Fin ((2 * p.n).factorial)) (tail : List (Fin ((2 * p.n).factorial)))
    (he : c.epoch < epochCount p) :
    localStep p f g {coreState p s c (seed :: tail) (fun i => g i c.snapshot) with phase := 2} =
      coreState p s (coreStep p g c seed) tail (fun i => g i c.snapshot) := by
  classical
  by_cases h : c.index + 1 < p.n
  · simp [localStep, localQuery, localUpdate, coreState, coreStep, h, he,
      List.sum_cons, add_comm]
  · simp [localStep, localQuery, localUpdate, coreState, coreStep, h,
      List.sum_cons, add_comm]
    rfl


noncomputable def coreCalls (p : Params) (g : Fin p.n → p.E → p.E) :
    (k : ℕ) → LocalCore p → (Fin k → Fin ((2 * p.n).factorial)) → ℕ
  | 0, _, _ => 0
  | k + 1, c, ξ => (if c.index = 0 then p.n else 0) + 1 +
      coreCalls p g k (coreStep p g c (ξ 0)) (fun j => ξ j.succ)

def coreTime (p : Params) (c : LocalCore p) : ℕ :=
  2 * (c.epoch * p.n) + if c.index = 0 then 0 else p.n + c.index

lemma coreStep_time (p : Params) (g : Fin p.n → p.E → p.E)
    (c : LocalCore p) (hc : CoreValid p c) (seed : Fin ((2 * p.n).factorial)) :
    coreTime p (coreStep p g c seed) =
      coreTime p c + (if c.index = 0 then p.n else 0) + 1 := by
  have hn := NeZero.pos p.n
  have hi := hc.1
  by_cases h : c.index + 1 < p.n
  · simp only [coreStep, h, ite_true, coreTime]
    split_ifs <;> simp_all only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false] <;> omega
  · simp only [coreStep, h, ite_false, coreTime, Nat.add_mul]
    split_ifs <;> omega

lemma coreCalls_time (p : Params) (g : Fin p.n → p.E → p.E)
    (k : ℕ) (c : LocalCore p) (hc : CoreValid p c)
    (ξ : Fin k → Fin ((2 * p.n).factorial)) :
    coreTime p (coreRun p g k c ξ) = coreTime p c + coreCalls p g k c ξ := by
  induction k generalizing c with
  | zero => simp [coreRun, coreCalls]
  | succ k ih =>
    rw [coreRun, ih _ (coreStep_valid p g c hc _) _, coreStep_time p g c hc]
    simp [coreCalls, Nat.add_assoc]

lemma coreCalls_initial (p : Params) (g : Fin p.n → p.E → p.E)
    (ξ : Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial)) :
    coreCalls p g (epochCount p * p.n) (initialCore p) ξ = 2 * p.n * epochCount p := by
  have h := coreCalls_time p g _ (initialCore p) (initialCore_valid p) ξ
  have ht := coreRun_terminal p g (epochCount p) ξ
  simp only [coreTime, ht.1, ht.2] at h
  simpa [initialCore, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.symm


lemma core_queries (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p) (k : ℕ)
    (c : LocalCore p) (hc : CoreValid p c)
    (ξ : Fin k → Fin ((2 * p.n).factorial))
    (tail : List (Fin ((2 * p.n).factorial))) (cache : Fin p.n → p.E)
    (hcache : c.index ≠ 0 → cache = fun i => g i c.snapshot)
    (hbound : c.epoch * p.n + c.index + k ≤ epochCount p * p.n) :
    ∃ cache', (localStep p f g)^[coreCalls p g k c ξ]
        (coreState p s c (List.ofFn ξ ++ tail) cache) =
      coreState p s (coreRun p g k c ξ) tail cache' := by
  induction k generalizing c cache with
  | zero => exact ⟨cache, by simp [coreCalls, coreRun]⟩
  | succ k ih =>
    have he : c.epoch < epochCount p := by
      by_contra h
      have hm := Nat.mul_le_mul_right p.n (Nat.le_of_not_gt h)
      omega
    let c' := coreStep p g c (ξ 0)
    let cache' := fun i => g i c.snapshot
    have hfirst : (localStep p f g)^[(if c.index = 0 then p.n else 0) + 1]
        (coreState p s c (List.ofFn ξ ++ tail) cache) =
        coreState p s c' (List.ofFn (fun j : Fin k => ξ j.succ) ++ tail) cache' := by
      rw [List.ofFn_succ, List.cons_append]
      by_cases hi : c.index = 0
      · simp only [ite_eq_left hi]
        rw [Nat.add_comm p.n 1, Function.iterate_add_apply]
        have hs : coreState p s c (ξ 0 :: (List.ofFn (fun j : Fin k => ξ j.succ) ++ tail)) cache =
            {coreState p s c (ξ 0 :: (List.ofFn (fun j : Fin k => ξ j.succ) ++ tail)) cache with phase := 1, index := 0} := by
          simp [coreState, he, hi]
        rw [hs, local_cache_queries]
        simpa [coreState, hi, c', cache'] using
          local_inner_query p f g s c (ξ 0) (List.ofFn (fun j : Fin k => ξ j.succ) ++ tail) he
      · simp only [ite_eq_right hi, zero_add, Function.iterate_one]
        rw [hcache hi]
        have hs : coreState p s c (ξ 0 :: (List.ofFn (fun j : Fin k => ξ j.succ) ++ tail)) (fun i => g i c.snapshot) =
            {coreState p s c (ξ 0 :: (List.ofFn (fun j : Fin k => ξ j.succ) ++ tail)) (fun i => g i c.snapshot) with phase := 2} := by
          simp [coreState, he, hi]
        rw [hs]
        exact local_inner_query p f g s c (ξ 0) _ he
    have hc' : CoreValid p c' := coreStep_valid p g c hc _
    have hb' : c'.epoch * p.n + c'.index + k ≤ epochCount p * p.n := by
      have hh := coreStep_clock p g c hc (ξ 0)
      change c'.epoch * p.n + c'.index = _ at hh
      omega
    have hcache' : c'.index ≠ 0 → cache' = fun i => g i c'.snapshot := by
      dsimp [c', coreStep]
      split_ifs <;> simp [cache']
    obtain ⟨lastCache, hh⟩ := ih c' hc' (fun j => ξ j.succ) cache' hcache' hb'
    refine ⟨lastCache, ?_⟩
    rw [coreCalls, Nat.add_comm _ (coreCalls p g k _ _), Function.iterate_add_apply, hfirst]
    exact hh


lemma local_value_prefix (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p)
    (hp : s.phase = 0 ∨ s.phase = 3) (hi : s.index = 0) (hv : s.values = 0)
    (j : ℕ) (hj : j < p.n) :
    (localStep p f g)^[j] s =
      {s with index := j, values := (∑ q ∈ Finset.range j, f ⟨q % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ (if s.phase = 0 then p.x0 else s.snapshot))} := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero_apply, Finset.range_zero, Finset.sum_empty]
    rw [← hi, ← hv]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    rcases hp with hp | hp <;>
      simp [localStep, localQuery, localUpdate, hp, hj, Finset.sum_range_succ]

lemma local_value_queries (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p)
    (hp : s.phase = 3) (hi : s.index = 0) (hv : s.values = 0)
    (hb : s.bestValue = LongTails.Setups.FiniteSumSmoothAndConvex.objective f s.best) :
    ∃ t, (localStep p f g)^[p.n] s = beginTrial p t ∧ t.trials = s.trials ∧
      t.best = (if LongTails.Setups.FiniteSumSmoothAndConvex.objective f s.snapshot <
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f s.best then s.snapshot else s.best) ∧
      t.bestValue = LongTails.Setups.FiniteSumSmoothAndConvex.objective f t.best := by
  classical
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let v := fun q : ℕ => f ⟨q % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ s.snapshot
  let t := {s with index := p.n - 1, values := ∑ q ∈ Finset.range (p.n - 1), v q}
  have hn : p.n - 1 + 1 = p.n := by have := NeZero.pos p.n; omega
  have hs : ((∑ q ∈ Finset.range (p.n - 1), v q) + v (p.n - 1)) / p.n = F s.snapshot := by
    rw [← Finset.sum_range_succ, hn]
    have hh : (∑ q ∈ Finset.range p.n, v q) = ∑ i : Fin p.n, f i s.snapshot := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp [v, Nat.mod_eq_of_lt i.isLt]
    rw [hh]
    simp [F, LongTails.Setups.FiniteSumSmoothAndConvex.objective, div_eq_mul_inv, mul_comm]
  let t' := if F s.snapshot < F s.best then {t with best := s.snapshot, bestValue := F s.snapshot} else t
  refine ⟨t', ?_, ?_, ?_, ?_⟩
  · rw [← hn, Function.iterate_succ_apply', local_value_prefix p f g s (Or.inr hp) hi hv _ (by omega)]
    have hs' := hs
    simp only [v, Nat.mod_eq_of_lt (show p.n - 1 < p.n by omega)] at hs'
    simp [localStep, localQuery, localUpdate, hp, hn, hb, t, t', v, F, hs']
  · dsimp [t']
    split_ifs <;> rfl
  · dsimp [t']
    split_ifs <;> rfl
  · dsimp [t']
    split_ifs <;> simp [t, hb, F]


lemma local_trial_queries (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p)
    (ξ : Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial))
    (tail : List (List (Fin ((2 * p.n).factorial))))
    (ht : s.trials = List.ofFn ξ :: tail)
    (hb : s.bestValue = LongTails.Setups.FiniteSumSmoothAndConvex.objective f s.best) :
    ∃ t, (localStep p f g)^[2 * p.n * epochCount p + p.n] (beginTrial p s) = beginTrial p t ∧
      t.trials = tail ∧
      t.best = (if LongTails.Setups.FiniteSumSmoothAndConvex.objective f (trialOutput p g ξ) <
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f s.best then trialOutput p g ξ else s.best) ∧
      t.bestValue = LongTails.Setups.FiniteSumSmoothAndConvex.objective f t.best := by
  let base := {s with trials := tail, values := 0}
  have hs : beginTrial p s = coreState p base (initialCore p) (List.ofFn ξ) (fun _ => 0) := by
    by_cases hz : epochCount p = 0 <;>
      simp [beginTrial, ht, coreState, initialCore, base, hz, Nat.pos_of_ne_zero]
  obtain ⟨cache, hc⟩ := core_queries p f g base (epochCount p * p.n) (initialCore p)
    (initialCore_valid p) ξ [] (fun _ => 0) (by simp [initialCore]) (by simp [initialCore])
  rw [coreCalls_initial] at hc
  simp only [List.append_nil] at hc
  let c := coreRun p g (epochCount p * p.n) (initialCore p) ξ
  have hend := coreRun_terminal p g (epochCount p) ξ
  have hep : c.epoch = epochCount p := hend.1
  have hei : c.index = 0 := hend.2
  obtain ⟨t, hstep, htail, hbest, hvalue⟩ := local_value_queries p f g
    (coreState p base c [] cache) (by simp [coreState, hep]) (by simp [coreState, hei])
    (by simp [coreState, base]) (by simpa [coreState, base] using hb)
  refine ⟨t, ?_, htail, hbest, hvalue⟩
  rw [Nat.add_comm, Function.iterate_add_apply, hs, hc]
  exact hstep


lemma local_trials_queries (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (m : ℕ) (s : LocalState p)
    (ξ : Fin m → Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial))
    (ht : s.trials = List.ofFn (fun j => List.ofFn (ξ j)))
    (hb : s.bestValue = LongTails.Setups.FiniteSumSmoothAndConvex.objective f s.best) :
    let final := (localStep p f g)^[m * (2 * p.n * epochCount p + p.n)] (beginTrial p s)
    final.phase = 4 ∧ final.best =
      selectBest (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) s.best
        (List.ofFn (fun j => trialOutput p g (ξ j))) := by
  induction m generalizing s with
  | zero => simp [beginTrial, ht, selectBest]
  | succ m ih =>
    have ht' : s.trials = List.ofFn (ξ 0) :: List.ofFn (fun j : Fin m => List.ofFn (ξ j.succ)) := by
      simpa only [List.ofFn_succ] using ht
    obtain ⟨t, hstep, htail, hbest, hvalue⟩ := local_trial_queries p f g s (ξ 0) _ ht' hb
    have hh := ih t (fun j => ξ j.succ) htail hvalue
    dsimp only at hh ⊢
    rw [Nat.succ_mul, Function.iterate_add_apply, hstep]
    simpa only [List.ofFn_succ, selectBest, hbest] using hh


lemma local_initial_queries (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p)
    (hp : s.phase = 0) (hi : s.index = 0) (hv : s.values = 0) :
    ∃ t, (localStep p f g)^[p.n] s = beginTrial p t ∧ t.trials = s.trials ∧
      t.best = s.best ∧ t.bestValue = LongTails.Setups.FiniteSumSmoothAndConvex.objective f p.x0 := by
  classical
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let v := fun q : ℕ => f ⟨q % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ p.x0
  have hn : p.n - 1 + 1 = p.n := by have := NeZero.pos p.n; omega
  have hs : ((∑ q ∈ Finset.range (p.n - 1), v q) + v (p.n - 1)) / p.n = F p.x0 := by
    rw [← Finset.sum_range_succ, hn]
    have hh : (∑ q ∈ Finset.range p.n, v q) = ∑ i : Fin p.n, f i p.x0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp [v, Nat.mod_eq_of_lt i.isLt]
    rw [hh]
    simp [F, LongTails.Setups.FiniteSumSmoothAndConvex.objective, div_eq_mul_inv, mul_comm]
  refine ⟨{s with index := p.n - 1, bestValue := F p.x0, values := 0}, ?_, rfl, rfl, rfl⟩
  rw [← hn, Function.iterate_succ_apply', local_value_prefix p f g s (Or.inl hp) hi hv _ (by omega)]
  simp only [v, Nat.mod_eq_of_lt (show p.n - 1 < p.n by omega)] at hs
  simp [localStep, localQuery, localUpdate, hp, hn, F, hs]

lemma local_iterate_absorbing (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (s : LocalState p) (h : s.phase = 4) (k : ℕ) :
    (localStep p f g)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, localStep_absorbing p f g s h]

lemma local_output_eq (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (ξ : LocalSeeds p) (K : ℕ)
    (hK : p.n + trialCount p * (2 * p.n * epochCount p + p.n) ≤ K) :
    ((localStep p f g)^[K] (localInitial p ξ)).best = amplifiedOutput p f g ξ := by
  by_cases h : p.Δ ≤ p.ε
  · rw [local_iterate_absorbing p f g _ (by simp [localInitial, h])]
    simp [localInitial, amplifiedOutput, h]
  · let s : LocalState p := localInitial p ξ
    obtain ⟨t, ht, htrials, hbest, hvalue⟩ := local_initial_queries p f g s
      (by simp [s, localInitial, h]) (by rfl) (by rfl)
    have hb : t.best = p.x0 := hbest
    have hh := local_trials_queries p f g (trialCount p) t ξ htrials (by rw [hb]; exact hvalue)
    dsimp only at hh
    let C := p.n + trialCount p * (2 * p.n * epochCount p + p.n)
    have hfull : (localStep p f g)^[C] s =
        (localStep p f g)^[trialCount p * (2 * p.n * epochCount p + p.n)] (beginTrial p t) := by
      dsimp [C]
      rw [Nat.add_comm, Function.iterate_add_apply, ht]
    have hphase : ((localStep p f g)^[C] s).phase = 4 := by rw [hfull]; exact hh.1
    have hpad : (localStep p f g)^[K] s = (localStep p f g)^[C] s := by
      rw [show K = (K - C) + C by dsimp [C]; omega, Function.iterate_add_apply]
      exact local_iterate_absorbing p f g _ hphase _
    change ((localStep p f g)^[K] s).best = _
    rw [hpad, hfull, hh.2, hb]
    simp [amplifiedOutput, h]


lemma execute_localAcceleration (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (O : Oracle (spec.Query p) (spec.Reply p))
    (hO : ∀ history i x seed, O.answer history (0, (i, x)) seed = (f i x, g i x))
    (ξ : LocalSeeds p) (ω : (k : ℕ) → O.Seed k) (K : ℕ)
    (hK : p.n + trialCount p * (2 * p.n * epochCount p + p.n) ≤ K) :
    execute O (localAcceleration p) (fun _ => K) ξ ω = amplifiedOutput p f g ξ := by
  exact (execute_eq_of_answer_eq O (fun q => (f q.1 q.2, g q.1 q.2))
    (fun history q seed => hO history q.1 q.2 seed) (localAcceleration p) K ξ ω).trans
      ((execute_iterate (fun q : Fin p.n × p.E => (f q.1 q.2, g q.1 q.2))
        (localAcceleration p) K ξ).trans (local_output_eq p f g ξ K hK))


end OracleTemplate.GeneralizedFiniteSum
