import LongTails.Algorithms.RadiusCompositeAccelerated
import LongTails.Proofs.Execution
import LongTails.Proofs.CompositeAdaptiveSearch

namespace OracleTemplate.CompositeAdaptive

attribute [local instance] Classical.propDecidable

open LongTails.Setups.RadiusCompositeGeneralizedSmooth
open LongTails.Algorithms.RadiusCompositeAccelerated

def answerOf (p : Public) (I : Instance p) : Query p → p.E
  | .gradient x => I.grad x
  | .prox a z v => I.prox a z v

noncomputable def transition (p : Public) (I : Instance p) (s : State p.E) : State p.E :=
  update p s (answerOf p I (query p s))

lemma trial_pair (p : Public) (I : Instance p) (s : Iterate p.E) (search : Search p.E) :
    (transition p I)^[2] (.gradient s search) =
      finishTrial p s search (I.grad (mix s.weight search.weight s.point s.momentum))
        (I.prox search.weight s.momentum
          (I.grad (mix s.weight search.weight s.point s.momentum))) := rfl

lemma initialization_pair (p : Public) (I : Instance p) :
    (transition p I)^[2] .initial =
      let A := initialWeight p (I.grad p.x0)
      let u := I.prox (initialStep p (I.grad p.x0)) p.x0 (I.grad p.x0)
      if targetWeight p ≤ A then .finished u else beginSearch ⟨A, u, u⟩ (A / 16) := rfl

lemma finished_iterate (p : Public) (I : Instance p) (x : p.E) (n : ℕ) :
    (transition p I)^[n] (.finished x) = .finished x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma execute_canonical (p : Public) (I : Instance p) (O : Oracle (Query p) p.E)
    (hO : ∀ history query seed, O.answer history (0, query) seed = answerOf p I query)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => K) seed ξ =
      output p ((transition p I)^[K] .initial) := by
  rw [execute_eq_of_answer_eq O (answerOf p I) hO, execute_iterate]
  rfl

noncomputable def evaluatedTrial (p : Public) (I : Instance p) (s : Iterate p.E) (a : ℝ) :
    Trial p.E :=
  ⟨a, I.grad (mix s.weight a s.point s.momentum),
    I.prox a s.momentum (I.grad (mix s.weight a s.point s.momentum))⟩

lemma refine_pair (p : Public) (I : Instance p) (s : Iterate p.E) (lo : Trial p.E)
    (hi : ℝ) (n : ℕ) :
    (transition p I)^[2] (refine p s lo hi n) =
      let t := evaluatedTrial p I s ((lo.weight + hi) / 2)
      let nextLo := if accepts p s t then t else lo
      let nextHi := if accepts p s t then hi else t.weight
      if n ≤ 1 then commit p s nextLo else refine p s nextLo nextHi (n - 1) := by
  classical
  rfl

lemma refinement_cached_bracket (p : Public) (I : Instance p) (s : Iterate p.E)
    (lo : Trial p.E) (hi : ℝ) (hlo : 0 < lo.weight) (horder : lo.weight ≤ hi)
    (hcanonical : lo = evaluatedTrial p I s lo.weight) (hsafe : accepts p s lo)
    (hunsafe : ¬ accepts p s (evaluatedTrial p I s hi)) :
    let t := evaluatedTrial p I s ((lo.weight + hi) / 2)
    let nextLo := if accepts p s t then t else lo
    let nextHi := if accepts p s t then hi else t.weight
    nextLo = evaluatedTrial p I s nextLo.weight ∧ accepts p s nextLo ∧
      ¬ accepts p s (evaluatedTrial p I s nextHi) ∧ 0 < nextLo.weight ∧
      lo.weight ≤ nextLo.weight ∧ nextLo.weight ≤ nextHi ∧ nextHi ≤ hi ∧
      nextHi - nextLo.weight = (hi - lo.weight) / 2 := by
  classical
  dsimp only
  by_cases ht : accepts p s (evaluatedTrial p I s ((lo.weight + hi) / 2))
  · simp only [ht, ↓reduceIte]
    exact ⟨rfl, trivial, hunsafe, by dsimp [evaluatedTrial]; linarith,
      by dsimp [evaluatedTrial]; linarith, by dsimp [evaluatedTrial]; linarith,
      le_rfl, by dsimp [evaluatedTrial]; ring⟩
  · simp only [ht, ↓reduceIte]
    exact ⟨hcanonical, hsafe, ht, hlo, le_rfl,
      by dsimp [evaluatedTrial]; linarith, by dsimp [evaluatedTrial]; linarith,
      by dsimp [evaluatedTrial]; ring⟩

lemma refinement_run (p : Public) (I : Instance p) (s : Iterate p.E)
    (lo : Trial p.E) (hi : ℝ) (n : ℕ) (hn : 0 < n)
    (hlo : 0 < lo.weight) (horder : lo.weight ≤ hi)
    (hcanonical : lo = evaluatedTrial p I s lo.weight) (hsafe : accepts p s lo)
    (hunsafe : ¬ accepts p s (evaluatedTrial p I s hi)) :
    ∃ nextLo : Trial p.E, ∃ nextHi : ℝ,
      (transition p I)^[2 * n] (refine p s lo hi n) = commit p s nextLo ∧
      nextLo = evaluatedTrial p I s nextLo.weight ∧ accepts p s nextLo ∧
      ¬ accepts p s (evaluatedTrial p I s nextHi) ∧ 0 < nextLo.weight ∧
      lo.weight ≤ nextLo.weight ∧ nextLo.weight ≤ nextHi ∧ nextHi ≤ hi ∧
      nextHi - nextLo.weight = (hi - lo.weight) / (2 : ℝ) ^ n := by
  induction n generalizing lo hi with
  | zero => omega
  | succ n ih =>
      let t := evaluatedTrial p I s ((lo.weight + hi) / 2)
      let lo1 := if accepts p s t then t else lo
      let hi1 := if accepts p s t then hi else t.weight
      have hb := refinement_cached_bracket p I s lo hi hlo horder hcanonical hsafe hunsafe
      change lo1 = evaluatedTrial p I s lo1.weight ∧ accepts p s lo1 ∧
        ¬ accepts p s (evaluatedTrial p I s hi1) ∧ 0 < lo1.weight ∧
        lo.weight ≤ lo1.weight ∧ lo1.weight ≤ hi1 ∧ hi1 ≤ hi ∧
        hi1 - lo1.weight = (hi - lo.weight) / 2 at hb
      obtain ⟨hc1, hs1, hu1, hp1, hl1, ho1, hh1, hw1⟩ := hb
      have hstep := refine_pair p I s lo hi (n + 1)
      change (transition p I)^[2] (refine p s lo hi (n + 1)) =
        if n + 1 ≤ 1 then commit p s lo1 else refine p s lo1 hi1 ((n + 1) - 1) at hstep
      by_cases hn0 : n = 0
      · subst n
        refine ⟨lo1, hi1, ?_, hc1, hs1, hu1, hp1, hl1, ho1, hh1, ?_⟩
        · simpa only [Nat.zero_add, Nat.reduceLeDiff, ↓reduceIte, Nat.mul_one] using hstep
        · simpa only [Nat.zero_add, pow_one] using hw1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        obtain ⟨lo2, hi2, hrun2, hc2, hs2, hu2, hp2, hl2, ho2, hh2, hw2⟩ :=
          ih lo1 hi1 hnpos hp1 ho1 hc1 hs1 hu1
        refine ⟨lo2, hi2, ?_, hc2, hs2, hu2, hp2, hl1.trans hl2, ho2, hh2.trans hh1, ?_⟩
        · rw [show 2 * (n + 1) = 2 * n + 2 by omega, Function.iterate_add_apply, hstep]
          simp only [show ¬ n + 1 ≤ 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
          exact hrun2
        · rw [hw2, hw1, pow_succ]
          ring

lemma refinement_run_precision (p : Public) (I : Instance p) (s : Iterate p.E)
    (lo : Trial p.E) (hi : ℝ) (n : ℕ) (hn : 0 < n) {X : ℝ} (hX : 0 < X)
    (hprecision : X ≤ (2 : ℝ) ^ n) (hlo : 0 < lo.weight)
    (horder : lo.weight ≤ hi) (hdouble : hi ≤ 2 * lo.weight)
    (hcanonical : lo = evaluatedTrial p I s lo.weight) (hsafe : accepts p s lo)
    (hunsafe : ¬ accepts p s (evaluatedTrial p I s hi)) :
    ∃ nextLo : Trial p.E, ∃ nextHi : ℝ,
      (transition p I)^[2 * n] (refine p s lo hi n) = commit p s nextLo ∧
      nextLo = evaluatedTrial p I s nextLo.weight ∧ accepts p s nextLo ∧
      ¬ accepts p s (evaluatedTrial p I s nextHi) ∧ 0 < nextLo.weight ∧
      lo.weight ≤ nextLo.weight ∧ nextLo.weight ≤ nextHi ∧ nextHi ≤ hi ∧
      nextHi ≤ (1 + 1 / X) * nextLo.weight := by
  obtain ⟨lo2, hi2, hrun, hc, hs, hu, hp, hl, ho, hh, hw⟩ :=
    refinement_run p I s lo hi n hn hlo horder hcanonical hsafe hunsafe
  refine ⟨lo2, hi2, hrun, hc, hs, hu, hp, hl, ho, hh, ?_⟩
  have hnum : hi - lo.weight ≤ lo2.weight := by linarith
  have hfirst := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ (2 : ℝ) ^ n)
  have hsecond := div_le_div_of_nonneg_left hp.le hX hprecision
  have hb : hi2 - lo2.weight ≤ lo2.weight / X := by rw [hw]; exact hfirst.trans hsecond
  have he : (1 + 1 / X) * lo2.weight = lo2.weight + lo2.weight / X := by ring
  rw [he]
  linarith

def ResolvedTrial (p : Public) (I : Instance p) (s : Iterate p.E) (t : Trial p.E) : Prop :=
  t = evaluatedTrial p I s t.weight ∧ accepts p s t ∧ 0 < t.weight ∧ t.weight ≤ s.weight ∧
    (t.weight = s.weight ∨ ∃ hi : ℝ, t.weight ≤ hi ∧ hi ≤ s.weight ∧
      ¬ accepts p s (evaluatedTrial p I s hi) ∧
      hi ≤ (1 + 1 / (1000 * (1 + 4 * p.L1 * p.R))) * t.weight)

lemma refinement_resolves (p : Public) (I : Instance p) (s : Iterate p.E)
    (lo : Trial p.E) (hi : ℝ) (hscale : 0 < 1000 * (1 + 4 * p.L1 * p.R))
    (hlo : 0 < lo.weight) (horder : lo.weight ≤ hi) (hdouble : hi ≤ 2 * lo.weight)
    (hcap : hi ≤ s.weight) (hcanonical : lo = evaluatedTrial p I s lo.weight)
    (hsafe : accepts p s lo) (hunsafe : ¬ accepts p s (evaluatedTrial p I s hi)) :
    ∃ t : Trial p.E,
      (transition p I)^[2 * refinementSteps p] (refine p s lo hi (refinementSteps p)) =
        commit p s t ∧ ResolvedTrial p I s t ∧ lo.weight ≤ t.weight := by
  have hm : 0 < refinementSteps p := by unfold refinementSteps; omega
  have hprec : 1000 * (1 + 4 * p.L1 * p.R) ≤ (2 : ℝ) ^ refinementSteps p :=
    refinement_count_precision hscale
  obtain ⟨t, upper, hrun, hc, hs, hu, hp, hl, ho, hh, hratio⟩ :=
    refinement_run_precision p I s lo hi (refinementSteps p) hm hscale hprec hlo horder
      hdouble hcanonical hsafe hunsafe
  exact ⟨t, hrun, ⟨hc, hs, hp, ho.trans (hh.trans hcap),
    Or.inr ⟨upper, ho, hh.trans hcap, hu, hratio⟩⟩, hl⟩

lemma grow_pair_safe (p : Public) (I : Instance p) (s : Iterate p.E) (a : ℝ)
    (lo : Option (Trial p.E)) (hsafe : accepts p s (evaluatedTrial p I s a))
    (hcap : a < s.weight) :
    (transition p I)^[2] (.gradient s ⟨a, lo, 0, .growing⟩) =
      .gradient s ⟨min (2 * a) s.weight, some (evaluatedTrial p I s a), 0, .growing⟩ := by
  rw [trial_pair]
  change (if accepts p s (evaluatedTrial p I s a) then
    if s.weight ≤ a then commit p s (evaluatedTrial p I s a) else _ else _) = _
  rw [ite_eq_left hsafe, ite_eq_right (not_le.mpr hcap)]
  rfl

lemma grow_pair_cap (p : Public) (I : Instance p) (s : Iterate p.E)
    (lo : Option (Trial p.E)) (hsafe : accepts p s (evaluatedTrial p I s s.weight)) :
    (transition p I)^[2] (.gradient s ⟨s.weight, lo, 0, .growing⟩) =
      commit p s (evaluatedTrial p I s s.weight) := by
  rw [trial_pair]
  change (if accepts p s (evaluatedTrial p I s s.weight) then
    if s.weight ≤ s.weight then commit p s (evaluatedTrial p I s s.weight) else _ else _) = _
  rw [ite_eq_left hsafe, ite_eq_left le_rfl]

lemma grow_pair_unsafe (p : Public) (I : Instance p) (s : Iterate p.E) (a : ℝ)
    (lo : Trial p.E) (hunsafe : ¬ accepts p s (evaluatedTrial p I s a)) :
    (transition p I)^[2] (.gradient s ⟨a, some lo, 0, .growing⟩) =
      refine p s lo a (refinementSteps p) := by
  rw [trial_pair]
  change (if accepts p s (evaluatedTrial p I s a) then _ else _) = _
  rw [ite_eq_right hunsafe]

lemma unsafe_after_safe_resolves (p : Public) (I : Instance p) (s : Iterate p.E)
    (a : ℝ) (lo : Option (Trial p.E)) (hscale : 0 < 1000 * (1 + 4 * p.L1 * p.R))
    (ha : 0 < a) (haA : a < s.weight) (hsafe : accepts p s (evaluatedTrial p I s a))
    (hunsafe : ¬ accepts p s (evaluatedTrial p I s (min (2 * a) s.weight))) :
    ∃ t : Trial p.E,
      (transition p I)^[2 * (2 + refinementSteps p)] (.gradient s ⟨a, lo, 0, .growing⟩) =
        commit p s t ∧ ResolvedTrial p I s t ∧ a ≤ t.weight := by
  have horder : a ≤ min (2 * a) s.weight := le_min (by linarith) haA.le
  obtain ⟨t, hrun, hresolved, hlower⟩ := refinement_resolves p I s
    (evaluatedTrial p I s a) (min (2 * a) s.weight) hscale ha horder
    (min_le_left _ _) (min_le_right _ _) rfl hsafe hunsafe
  refine ⟨t, ?_, hresolved, hlower⟩
  rw [show 2 * (2 + refinementSteps p) = (2 * refinementSteps p + 2) + 2 by omega,
    Function.iterate_add_apply, grow_pair_safe p I s a lo hsafe haA,
    Function.iterate_add_apply, grow_pair_unsafe p I s _ _ hunsafe]
  exact hrun

lemma growing_run (p : Public) (I : Instance p) (s : Iterate p.E)
    (a : ℝ) (lo : Option (Trial p.E)) (n : ℕ)
    (hscale : 0 < 1000 * (1 + 4 * p.L1 * p.R)) (ha : 0 < a) (haA : a ≤ s.weight)
    (hsafe : accepts p s (evaluatedTrial p I s a)) (hbound : s.weight ≤ (2 : ℝ) ^ n * a) :
    ∃ t : Trial p.E, ∃ j k : ℕ,
      (transition p I)^[2 * k] (.gradient s ⟨a, lo, 0, .growing⟩) = commit p s t ∧
      ResolvedTrial p I s t ∧ (2 : ℝ) ^ j * a ≤ t.weight ∧
      k ≤ j + 2 + refinementSteps p ∧ 0 < k := by
  have hcapcase : ∀ a lo, 0 < a → a = s.weight →
      accepts p s (evaluatedTrial p I s a) →
      ∃ t : Trial p.E, ∃ j k : ℕ,
        (transition p I)^[2 * k] (.gradient s ⟨a, lo, 0, .growing⟩) = commit p s t ∧
        ResolvedTrial p I s t ∧ (2 : ℝ) ^ j * a ≤ t.weight ∧
        k ≤ j + 2 + refinementSteps p ∧ 0 < k := by
    intro a lo ha he hs
    refine ⟨evaluatedTrial p I s a, 0, 1, ?_, ⟨rfl, hs, ha, he.le, Or.inl he⟩,
      by simp [evaluatedTrial], by omega, by omega⟩
    simpa only [Nat.mul_one, he] using grow_pair_cap p I s lo (by simpa only [he] using hs)
  induction n generalizing a lo with
  | zero =>
      have he : a = s.weight := haA.antisymm (by simpa only [pow_zero, one_mul] using hbound)
      exact hcapcase a lo ha he hsafe
  | succ n ih =>
      by_cases he : a = s.weight
      · exact hcapcase a lo ha he hsafe
      have hlt : a < s.weight := lt_of_le_of_ne haA he
      let b := min (2 * a) s.weight
      have hab : a ≤ b := le_min (by linarith) haA
      have hb0 : 0 < b := ha.trans_le hab
      have hbA : b ≤ s.weight := min_le_right _ _
      by_cases hbSafe : accepts p s (evaluatedTrial p I s b)
      · by_cases hbcap : b = s.weight
        · refine ⟨evaluatedTrial p I s b, 0, 2, ?_,
            ⟨rfl, hbSafe, hb0, hbA, Or.inl hbcap⟩, ?_, by omega, by omega⟩
          · rw [show 2 * 2 = 2 + 2 by omega, Function.iterate_add_apply,
              grow_pair_safe p I s a lo hsafe hlt]
            change (transition p I)^[2] (.gradient s ⟨b, some (evaluatedTrial p I s a), 0, .growing⟩) = _
            rw [hbcap]
            exact grow_pair_cap p I s _ (by simpa only [hbcap] using hbSafe)
          · simpa only [pow_zero, one_mul, evaluatedTrial] using hab
        · have hbdouble : b = 2 * a := by
            exact min_eq_left (by
              by_contra h
              have : b = s.weight := min_eq_right (le_of_not_ge h)
              exact hbcap this)
          have hnext : s.weight ≤ (2 : ℝ) ^ n * b := by
            rw [hbdouble]
            have heq : (2 : ℝ) ^ (n + 1) * a = (2 : ℝ) ^ n * (2 * a) := by rw [pow_succ]; ring
            rwa [heq] at hbound
          obtain ⟨t, j, k, hrun, hres, hcredit, hcost, hk⟩ :=
            ih b (some (evaluatedTrial p I s a)) hb0 hbA hbSafe hnext
          refine ⟨t, j + 1, k + 1, ?_, hres, ?_, by omega, by omega⟩
          · rw [show 2 * (k + 1) = 2 * k + 2 by omega, Function.iterate_add_apply,
              grow_pair_safe p I s a lo hsafe hlt]
            exact hrun
          · have heq : (2 : ℝ) ^ (j + 1) * a = (2 : ℝ) ^ j * b := by rw [hbdouble, pow_succ]; ring
            rwa [heq]
      · obtain ⟨t, hrun, hres, hcredit⟩ :=
          unsafe_after_safe_resolves p I s a lo hscale ha hlt hsafe hbSafe
        exact ⟨t, 0, 2 + refinementSteps p, hrun, hres,
          by simpa only [pow_zero, one_mul] using hcredit, by omega, by omega⟩

lemma growing_completes (p : Public) (I : Instance p) (s : Iterate p.E)
    (a : ℝ) (lo : Option (Trial p.E)) (hscale : 0 < 1000 * (1 + 4 * p.L1 * p.R))
    (ha : 0 < a) (haA : a ≤ s.weight) (hsafe : accepts p s (evaluatedTrial p I s a)) :
    ∃ t : Trial p.E, ∃ k : ℕ,
      (transition p I)^[2 * k] (.gradient s ⟨a, lo, 0, .growing⟩) = commit p s t ∧
      ResolvedTrial p I s t ∧ a ≤ t.weight ∧ 0 < k ∧
      (k : ℝ) ≤ Real.log (t.weight / a) / Real.log 2 + 2 + refinementSteps p := by
  have hA : 0 < s.weight := ha.trans_le haA
  let n := 1 + ⌈Real.log (s.weight / a) / Real.log 2⌉₊
  have hbound : s.weight ≤ (2 : ℝ) ^ n * a :=
    (div_le_iff₀ ha).mp (refinement_count_precision (div_pos hA ha))
  obtain ⟨t, j, k, hrun, hres, hcredit, hcost, hk⟩ :=
    growing_run p I s a lo n hscale ha haA hsafe hbound
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hat : a ≤ t.weight := by nlinarith
  have hratio : (2 : ℝ) ^ j ≤ t.weight / a := (le_div_iff₀ ha).mpr hcredit
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ j) hratio
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj : (j : ℝ) ≤ Real.log (t.weight / a) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  have hcost' : (k : ℝ) ≤ (j : ℝ) + 2 + refinementSteps p := by exact_mod_cast hcost
  exact ⟨t, k, hrun, hres, hat, hk, by linarith⟩

end OracleTemplate.CompositeAdaptive
