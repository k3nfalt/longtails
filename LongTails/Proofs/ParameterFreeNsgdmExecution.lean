import LongTails.Algorithms.ParameterFreeNsgdm
import LongTails.Proofs.ParameterFreeNsgdmRun
import LongTails.Proofs.ParameterFreeNsgdmSelection
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace LongTails.Proofs.ParameterFreeNsgdmExecution

open OracleTemplate
open OracleTemplate.StochasticGradient (advance execute_advance)
open LongTails.Setups.ParameterFreeHeavyTailedSmooth
open LongTails.Algorithms.ParameterFreeNsgdm
open ParameterFreeNsgdmRun ParameterFreeNsgdmSelection

variable {d : Public} {Ω : Type}

noncomputable def machine (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (i : ℕ) (s : State d) : State d :=
  update d s (g (query s) (ξ i))

lemma advance_add {S : Type*} (step : ℕ → S → S) (n m call : ℕ) (s : S) :
    advance step (n + m) call s = advance step m (call + n) (advance step n call s) := by
  induction n generalizing call s with
  | zero => simp [advance]
  | succ n ih =>
    rw [Nat.succ_add, advance, ih]
    simp only [advance, Nat.add_left_comm, Nat.add_comm]

def phaseCost (k : ℕ) : ℕ := 2 * (candidates k * horizon k)

def phaseStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => phaseStart k + phaseCost k

noncomputable def runStartState (d : Public) (s : Seed) (k c : ℕ) (cands : ℕ → d.E) (acc : d.E)
    (bn : ℝ) (best out : d.E) : State d :=
  ⟨s, k, c, 0, false, d.x0, 0, cands, acc, bn, best, out⟩

noncomputable def valStartState (d : Public) (s : Seed) (k c : ℕ) (cands : ℕ → d.E)
    (bn : ℝ) (best out : d.E) : State d :=
  ⟨s, k, c, 0, true, d.x0, 0, cands, 0, bn, best, out⟩

noncomputable def runPoint (g : d.E → Ω → d.E) (s : Seed) (k c a : ℕ) (ξ : ℕ → Ω) : d.E :=
  (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) (chosen s k c)).1

lemma run_prefix (g : d.E → Ω → d.E) (s : Seed) (k c a : ℕ) (cands : ℕ → d.E) (acc : d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) (t : ℕ) (ht : t < horizon k) :
    advance (machine g ξ) t a (runStartState d s k c cands acc bn best out) =
      ⟨s, k, c, t, false, (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) t).1,
        (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) t).2.1,
        if chosen s k c < t then Function.update cands c
          (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) (chosen s k c)).1
        else cands, acc, bn, best, out⟩ := by
  induction t with
  | zero =>
      simp [advance, runStartState, run]
  | succ t ih =>
      rw [advance_add, ih (by omega)]
      simp only [advance, machine, update, query, Bool.false_eq_true, ↓reduceIte, runUpdate,
        show t + 1 < horizon k from ht]
      have hm : mix k c t (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) t).2.1
          (g (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) t).1 (ξ (a + t))) =
          (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) (t + 1)).2.1 := by
        rw [run_momentum_succ]; rfl
      have hx : move k c (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) t).1
          (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) (t + 1)).2.1 =
          (run (momentum k c) (stepSize k c) g d.x0 (fun n => ξ (a + n)) (t + 1)).1 := by
        rw [run_point_succ]; rfl
      rw [hm, hx]
      congr 1
      by_cases hc : t = chosen s k c
      · subst hc
        simp
      · by_cases hlt : chosen s k c < t
        · simp [hlt, Nat.lt_succ_of_lt hlt, hc]
        · have : ¬ chosen s k c < t + 1 := by omega
          simp [hlt, this, hc]


lemma chosen_lt (s : Seed) (k c : ℕ) : chosen s k c < horizon k := by
  unfold chosen
  split_ifs with h
  · exact (s k ⟨c, h⟩).isLt
  · unfold horizon; positivity

lemma run_complete (g : d.E → Ω → d.E) (s : Seed) (k c a : ℕ) (cands : ℕ → d.E) (acc : d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) :
    advance (machine g ξ) (horizon k) a (runStartState d s k c cands acc bn best out) =
      if c + 1 < candidates k then
        runStartState d s k (c + 1) (Function.update cands c (runPoint g s k c a ξ)) acc bn best out
      else valStartState d s k 0 (Function.update cands c (runPoint g s k c a ξ)) bn best out := by
  have hT : 0 < horizon k := by unfold horizon; positivity
  obtain ⟨T, hTk⟩ : ∃ T, horizon k = T + 1 := ⟨horizon k - 1, by omega⟩
  rw [hTk, advance_add, run_prefix g s k c a cands acc bn best out ξ T (by omega)]
  have hch := chosen_lt s k c
  rw [hTk] at hch
  simp only [advance, machine, update, Bool.false_eq_true, ↓reduceIte, runUpdate, hTk,
    lt_irrefl]
  split_ifs with h1 <;> simp_all [runStartState, valStartState, runPoint] <;> (exfalso; omega)

noncomputable def phaseCands (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) (c : ℕ) : d.E :=
  runPoint g s k c (a + c * horizon k) ξ

lemma runs_prefix (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (cands : ℕ → d.E) (acc : d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) (c : ℕ) (hc : c < candidates k) :
    advance (machine g ξ) (c * horizon k) a (runStartState d s k 0 cands acc bn best out) =
      runStartState d s k c (fun c' => if c' < c then phaseCands g s k a ξ c' else cands c')
        acc bn best out := by
  induction c with
  | zero =>
      simp [advance, runStartState]
  | succ c ih =>
      rw [show (c + 1) * horizon k = c * horizon k + horizon k by ring, advance_add,
        ih (by omega), run_complete]
      simp only [show c + 1 < candidates k from hc, ↓reduceIte]
      unfold runStartState
      congr 1
      funext c'
      by_cases h : c' = c
      · subst h; simp [phaseCands]
      · simp only [Function.update, h, ↓reduceDIte]
        by_cases hlt : c' < c
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have : ¬ c' < c + 1 := by omega
          simp [hlt, this]

lemma runs_complete (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (cands : ℕ → d.E) (acc : d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) :
    advance (machine g ξ) (candidates k * horizon k) a (runStartState d s k 0 cands acc bn best out) =
      valStartState d s k 0 (fun c' => if c' < candidates k then phaseCands g s k a ξ c' else cands c')
        bn best out := by
  have hC : 0 < candidates k := by unfold candidates momentumCount stepCount; positivity
  obtain ⟨C, hCk⟩ : ∃ C, candidates k = C + 1 := ⟨candidates k - 1, by omega⟩
  rw [hCk, show (C + 1) * horizon k = C * horizon k + horizon k by ring, advance_add,
    runs_prefix g s k a cands acc bn best out ξ C (by omega), run_complete]
  simp only [hCk, lt_irrefl, ↓reduceIte]
  unfold valStartState
  congr 1
  funext c'
  by_cases h : c' = C
  · subst h; simp [phaseCands]
  · simp only [Function.update, h, ↓reduceDIte]
    by_cases hlt : c' < C
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · have : ¬ c' < C + 1 := by omega
      simp [hlt, this]


lemma val_prefix (g : d.E → Ω → d.E) (s : Seed) (k c a : ℕ) (cands : ℕ → d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) (t : ℕ) (ht : t < horizon k) :
    advance (machine g ξ) t a (valStartState d s k c cands bn best out) =
      ⟨s, k, c, t, true, d.x0, 0, cands, ∑ i ∈ Finset.range t, g (cands c) (ξ (a + i)),
        bn, best, out⟩ := by
  induction t with
  | zero => simp [advance, valStartState]
  | succ t ih =>
      rw [advance_add, ih (by omega)]
      simp only [advance, machine, update, query, ↓reduceIte, validateUpdate,
        show t + 1 < horizon k from ht, Finset.sum_range_succ]

noncomputable def improveNorm (c : ℕ) (v bn : ℝ) : ℝ := if c = 0 ∨ v < bn then v else bn

noncomputable def improveBest (c : ℕ) (v bn : ℝ) (y best : d.E) : d.E :=
  if c = 0 ∨ v < bn then y else best

noncomputable def estimate (g : d.E → Ω → d.E) (k a : ℕ) (cands : ℕ → d.E) (ξ : ℕ → Ω)
    (c : ℕ) : ℝ :=
  ‖batchMean g (horizon k) a (cands c) ξ‖

lemma val_complete (g : d.E → Ω → d.E) (s : Seed) (k c a : ℕ) (cands : ℕ → d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) :
    advance (machine g ξ) (horizon k) a (valStartState d s k c cands bn best out) =
      let v := estimate g k a cands ξ c
      if c + 1 < candidates k then
        valStartState d s k (c + 1) cands (improveNorm c v bn) (improveBest c v bn (cands c) best) out
      else runStartState d s (k + 1) 0 cands 0 (improveNorm c v bn)
        (improveBest c v bn (cands c) best) (improveBest c v bn (cands c) best) := by
  have hT : 0 < horizon k := by unfold horizon; positivity
  obtain ⟨T, hTk⟩ : ∃ T, horizon k = T + 1 := ⟨horizon k - 1, by omega⟩
  rw [hTk, advance_add, val_prefix g s k c a cands bn best out ξ T (by omega)]
  simp only [advance, machine, update, query, ↓reduceIte, validateUpdate, hTk, lt_irrefl,
    estimate, batchMean, improveNorm, improveBest, Finset.sum_range_succ]
  split_ifs <;> simp_all [valStartState, runStartState]

noncomputable def selectNorm (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => v 0
  | c + 1 => improveNorm (c + 1) (v (c + 1)) (selectNorm v c)

noncomputable def selectBest (v : ℕ → ℝ) (y : ℕ → d.E) : ℕ → d.E
  | 0 => y 0
  | c + 1 => improveBest (c + 1) (v (c + 1)) (selectNorm v c) (y (c + 1)) (selectBest v y c)

lemma select_spec (v : ℕ → ℝ) (y : ℕ → d.E) (c : ℕ) :
    ∃ c₀ ≤ c, selectBest v y c = y c₀ ∧ selectNorm v c = v c₀ ∧ ∀ c' ≤ c, v c₀ ≤ v c' := by
  induction c with
  | zero => exact ⟨0, le_rfl, rfl, rfl, fun c' hc' => by simp_all⟩
  | succ c ih =>
      obtain ⟨c₀, hc₀, hb, hn, hmin⟩ := ih
      simp only [selectBest, selectNorm, improveBest, improveNorm, Nat.succ_ne_zero, false_or, hn]
      by_cases h : v (c + 1) < v c₀
      · refine ⟨c + 1, le_rfl, by simp [h], by simp [h], fun c' hc' => ?_⟩
        rcases Nat.lt_or_ge c' (c + 1) with hlt | hge
        · exact h.le.trans (hmin c' (by omega))
        · have : c' = c + 1 := by omega
          simp [this]
      · refine ⟨c₀, by omega, by simp [h, hb], by simp [h], fun c' hc' => ?_⟩
        rcases Nat.lt_or_ge c' (c + 1) with hlt | hge
        · exact hmin c' (by omega)
        · have : c' = c + 1 := by omega
          simp [this]; linarith

lemma vals_prefix (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (cands : ℕ → d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) (c : ℕ) (hc : c < candidates k) :
    advance (machine g ξ) (c * horizon k) a (valStartState d s k 0 cands bn best out) =
      valStartState d s k c cands
        (if c = 0 then bn else selectNorm (fun c' => estimate g k (a + c' * horizon k) cands ξ c') (c - 1))
        (if c = 0 then best else selectBest (fun c' => estimate g k (a + c' * horizon k) cands ξ c') cands (c - 1))
        out := by
  induction c with
  | zero => simp [advance, valStartState]
  | succ c ih =>
      rw [show (c + 1) * horizon k = c * horizon k + horizon k by ring, advance_add,
        ih (by omega), val_complete]
      simp only [show c + 1 < candidates k from hc, ↓reduceIte, Nat.succ_ne_zero,
        Nat.add_sub_cancel]
      cases c with
      | zero => simp [selectNorm, selectBest, valStartState, improveNorm, improveBest]
      | succ c =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, selectNorm, selectBest]

noncomputable def phaseSelection (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) : ℕ → d.E :=
  fun c' => if c' < candidates k then phaseCands g s k a ξ c' else d.x0

noncomputable def phaseEstimates (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) (c : ℕ) : ℝ :=
  estimate g k (a + candidates k * horizon k + c * horizon k) (phaseSelection g s k a ξ) ξ c

noncomputable def phaseOutput (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) : d.E :=
  selectBest (phaseEstimates g s k a ξ) (phaseSelection g s k a ξ) (candidates k - 1)

noncomputable def phaseNorm (g : d.E → Ω → d.E) (s : Seed) (k a : ℕ) (ξ : ℕ → Ω) : ℝ :=
  selectNorm (phaseEstimates g s k a ξ) (candidates k - 1)


lemma selectNorm_congr {v w : ℕ → ℝ} (c : ℕ) (h : ∀ c' ≤ c, v c' = w c') :
    selectNorm v c = selectNorm w c := by
  induction c with
  | zero => simp [selectNorm, h 0 le_rfl]
  | succ c ih =>
      simp only [selectNorm]
      rw [ih (fun c' hc' => h c' (by omega)), h (c + 1) le_rfl]

lemma selectBest_congr {v w : ℕ → ℝ} {y z : ℕ → d.E} (c : ℕ) (hv : ∀ c' ≤ c, v c' = w c')
    (hy : ∀ c' ≤ c, y c' = z c') : selectBest v y c = selectBest w z c := by
  induction c with
  | zero => simp [selectBest, hy 0 le_rfl]
  | succ c ih =>
      simp only [selectBest]
      rw [ih (fun c' hc' => hv c' (by omega)) (fun c' hc' => hy c' (by omega)),
        hv (c + 1) le_rfl, hy (c + 1) le_rfl,
        selectNorm_congr c (fun c' hc' => hv c' (by omega))]

lemma estimate_congr (g : d.E → Ω → d.E) (k a : ℕ) {cands cands' : ℕ → d.E} (ξ : ℕ → Ω) (c : ℕ)
    (h : cands c = cands' c) : estimate g k a cands ξ c = estimate g k a cands' ξ c := by
  simp [estimate, h]

lemma candidates_pos (k : ℕ) : 0 < candidates k := by
  unfold candidates momentumCount stepCount; positivity

lemma phase_complete (g : d.E → Ω → d.E) (s : Seed) (k : ℕ) (cands : ℕ → d.E) (acc : d.E)
    (bn : ℝ) (best out : d.E) (ξ : ℕ → Ω) :
    advance (machine g ξ) (phaseCost k) (phaseStart k) (runStartState d s k 0 cands acc bn best out) =
      runStartState d s (k + 1) 0
        (fun c' => if c' < candidates k then phaseCands g s k (phaseStart k) ξ c' else cands c') 0
        (phaseNorm g s k (phaseStart k) ξ) (phaseOutput g s k (phaseStart k) ξ)
        (phaseOutput g s k (phaseStart k) ξ) := by
  have hC := candidates_pos k
  obtain ⟨C, hCk⟩ : ∃ C, candidates k = C + 1 := ⟨candidates k - 1, by omega⟩
  unfold phaseCost
  rw [two_mul, advance_add, runs_complete]
  set cands' : ℕ → d.E := fun c' => if c' < candidates k then phaseCands g s k (phaseStart k) ξ c' else cands c'
    with hcands'
  rw [show candidates k * horizon k = C * horizon k + horizon k by rw [hCk]; ring, advance_add,
    vals_prefix g s k _ cands' bn best out ξ C (by omega), val_complete]
  simp only [hCk, lt_irrefl, ↓reduceIte]
  have hsel : ∀ c' ≤ C,
      estimate g k (phaseStart k + (C * horizon k + horizon k) + c' * horizon k) cands' ξ c' =
        phaseEstimates g s k (phaseStart k) ξ c' := by
    intro c' hc'
    unfold phaseEstimates
    rw [show candidates k * horizon k = C * horizon k + horizon k by rw [hCk]; ring]
    apply estimate_congr
    simp [hcands', phaseSelection, show c' < candidates k by omega]
  have hy : ∀ c' ≤ C, cands' c' = phaseSelection g s k (phaseStart k) ξ c' := by
    intro c' hc'
    simp [hcands', phaseSelection, show c' < candidates k by omega]
  unfold phaseNorm phaseOutput
  cases C with
  | zero =>
      simp only [↓reduceIte, improveNorm, improveBest, true_or]
      rw [hsel 0 le_rfl, hy 0 le_rfl, hCk, Nat.add_sub_cancel]
      simp only [selectNorm, selectBest]
  | succ C =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [selectNorm_congr C (fun c' hc' => hsel c' (by omega)),
        selectBest_congr C (fun c' hc' => hsel c' (by omega)) (fun c' hc' => hy c' (by omega)),
        hsel (C + 1) le_rfl, hy (C + 1) le_rfl, hCk, Nat.add_sub_cancel]
      simp only [selectNorm, selectBest]

noncomputable def outBefore (g : d.E → Ω → d.E) (s : Seed) (ξ : ℕ → Ω) : ℕ → d.E
  | 0 => d.x0
  | k + 1 => phaseOutput g s k (phaseStart k) ξ

lemma advance_phases (g : d.E → Ω → d.E) (s : Seed) (ξ : ℕ → Ω) (K : ℕ) :
    ∃ (cands : ℕ → d.E) (bn : ℝ),
      advance (machine g ξ) (phaseStart K) 0 (initial d s) =
        runStartState d s K 0 cands 0 bn (outBefore g s ξ K) (outBefore g s ξ K) := by
  induction K with
  | zero => exact ⟨fun _ => d.x0, 0, rfl⟩
  | succ K ih =>
      obtain ⟨cands, bn, h⟩ := ih
      refine ⟨fun c' => if c' < candidates K then phaseCands g s K (phaseStart K) ξ c' else cands c',
        phaseNorm g s K (phaseStart K) ξ, ?_⟩
      rw [phaseStart, advance_add, h, zero_add, phase_complete]
      rfl

def remaining (k : ℕ) (s : State d) : ℕ :=
  (if s.validating then 0 else candidates k * horizon k) +
    (candidates k - s.cand - 1) * horizon k + (horizon k - s.step)

lemma out_stable (g : d.E → Ω → d.E) (ξ : ℕ → Ω) (k : ℕ) (m : ℕ) :
    ∀ (s : State d) (a : ℕ), s.phase = k → s.cand < candidates k → s.step < horizon k →
      m < remaining k s → (advance (machine g ξ) m a s).out = s.out := by
  induction m with
  | zero => intro s a _ _ _ _; rfl
  | succ m ih =>
      intro s a hk hc hs hm
      rw [advance]
      have hT : 0 < horizon k := by unfold horizon; positivity
      obtain ⟨sd, ph, c, t, val, x, mo, cands, acc, bn, best, out⟩ := s
      simp only at hk hc hs
      subst hk
      simp only [remaining] at hm
      cases val with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hm
          simp only [machine, update, query, Bool.false_eq_true, ↓reduceIte, runUpdate]
          by_cases h1 : t + 1 < horizon ph
          · simp only [h1, ↓reduceIte]
            exact ih _ (a + 1) rfl hc h1 (by simp only [remaining, Bool.false_eq_true, ↓reduceIte]; omega)
          · simp only [h1, ↓reduceIte]
            by_cases h2 : c + 1 < candidates ph
            · simp only [h2, ↓reduceIte]
              refine ih _ (a + 1) rfl h2 hT ?_
              simp only [remaining, Bool.false_eq_true, ↓reduceIte]
              have : candidates ph - c - 1 = (candidates ph - (c + 1) - 1) + 1 := by omega
              rw [this, Nat.add_mul, one_mul] at hm
              omega
            · simp only [h2, ↓reduceIte]
              refine ih _ (a + 1) rfl (candidates_pos ph) hT ?_
              simp only [remaining, ↓reduceIte]
              have : candidates ph - c - 1 = 0 := by omega
              rw [this, zero_mul, add_zero] at hm
              have : candidates ph - 0 - 1 = candidates ph - 1 := by omega
              rw [this]
              have hC := candidates_pos ph
              have : (candidates ph - 1) * horizon ph + horizon ph = candidates ph * horizon ph := by
                rw [← Nat.succ_pred_eq_of_pos hC]; simp [Nat.succ_mul]
              omega
      | true =>
          simp only [↓reduceIte, zero_add] at hm
          simp only [machine, update, query, ↓reduceIte, validateUpdate]
          by_cases h1 : t + 1 < horizon ph
          · simp only [h1, ↓reduceIte]
            exact ih _ (a + 1) rfl hc h1 (by simp only [remaining, ↓reduceIte]; omega)
          · simp only [h1, ↓reduceIte]
            by_cases h2 : c + 1 < candidates ph
            · simp only [h2, ↓reduceIte]
              refine ih _ (a + 1) rfl h2 hT ?_
              simp only [remaining, ↓reduceIte, zero_add]
              have : candidates ph - c - 1 = (candidates ph - (c + 1) - 1) + 1 := by omega
              rw [this, Nat.add_mul, one_mul] at hm
              omega
            · exfalso
              have : candidates ph - c - 1 = 0 := by omega
              rw [this, zero_mul, zero_add] at hm
              omega

lemma out_after (g : d.E → Ω → d.E) (s : Seed) (ξ : ℕ → Ω) (K N : ℕ)
    (hlow : phaseStart K ≤ N) (hhigh : N < phaseStart (K + 1)) :
    (advance (machine g ξ) N 0 (initial d s)).out = outBefore g s ξ K := by
  obtain ⟨cands, bn, h⟩ := advance_phases g s ξ K
  rw [show N = phaseStart K + (N - phaseStart K) by omega, advance_add, h]
  have hT : 0 < horizon K := by unfold horizon; positivity
  apply out_stable g ξ K _ _ _ rfl (candidates_pos K) hT
  simp only [phaseStart, phaseCost] at hhigh
  show N - phaseStart K < (if false = true then 0 else candidates K * horizon K) +
    (candidates K - 0 - 1) * horizon K + (horizon K - 0)
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Nat.sub_zero, Nat.sub_zero]
  have hC := candidates_pos K
  have hsub : (candidates K - 1) * horizon K + horizon K = candidates K * horizon K := by
    rw [← Nat.succ_pred_eq_of_pos hC]; simp [Nat.succ_mul]
  omega

lemma execute_eq [MeasurableSpace Ω] (g : d.E → Ω → d.E) (P : ProbabilityMeasure (ℕ → Ω))
    (s : Seed) (ξ : ℕ → Ω) (N : ℕ) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } (algorithm d)
        (fun _ => N) s ξ =
      (advance (machine g ξ) N 0 (initial d s)).out := by
  rw [execute_advance P g (algorithm d) N s ξ]
  rfl

end LongTails.Proofs.ParameterFreeNsgdmExecution
