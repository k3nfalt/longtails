import LongTails.Proofs.GapStrongGrowthStopped
import LongTails.Proofs.TerminalClippingConcentration
import LongTails.Proofs.StochasticGeneralizedConcentration

open MeasureTheory
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.TerminalClipping

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

noncomputable def stopUnless (good : S → Prop) (advance : S → Ω → S)
    (s : S) (ω : Ω) : S := by
  classical
  exact if good s then advance s ω else s

lemma stopUnless_measurable {good : S → Prop} (hg : MeasurableSet {s | good s})
    {advance : S → Ω → S} (ha : Measurable (Function.uncurry advance)) :
    Measurable (Function.uncurry (stopUnless good advance)) := by
  classical
  exact Measurable.ite (hg.preimage measurable_fst) ha measurable_fst

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma stopped_constant (good : S → Prop) (advance : S → Ω → S)
    (s : S) (hs : ¬good s) (n : ℕ) (ξ : Fin n → Ω) :
    iterateSamples (stopUnless good advance) n s ξ = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterateSamples, stopUnless, hs, ↓reduceIte]
    exact ih _

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma stopped_compare (good : S → Prop) (advance : S → Ω → S)
    (n : ℕ) (s : S) (ξ : Fin n → Ω) :
    iterateSamples advance n s ξ = iterateSamples (stopUnless good advance) n s ξ ∨
      ¬good (iterateSamples (stopUnless good advance) n s ξ) := by
  classical
  induction n generalizing s with
  | zero => exact Or.inl rfl
  | succ n ih =>
    by_cases hs : good s
    · simpa only [iterateSamples, stopUnless, hs, ↓reduceIte] using
        ih (advance s (ξ 0)) (fun i => ξ i.succ)
    · right
      rw [stopped_constant good advance s hs]
      exact hs

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma stopped_invariant (good I : S → Prop) (advance : S → Ω → S)
    (hstep : ∀ s, I s → good s → ∀ ω, I (advance s ω))
    (n : ℕ) (s : S) (hs : I s) (ξ : Fin n → Ω) :
    I (iterateSamples (stopUnless good advance) n s ξ) := by
  classical
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    by_cases hg : good s
    · simp only [iterateSamples, stopUnless, hg, ↓reduceIte]
      exact ih _ (hstep s hs hg (ξ 0)) _
    · rw [stopped_constant good advance s hg]
      exact hs

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma stopped_prefix_good (good : S → Prop) (advance : S → Ω → S)
    (n : ℕ) (s : S) (ξ : Fin n → Ω)
    (hg : good (iterateSamples (stopUnless good advance) n s ξ)) :
    ∀ k (hk : k ≤ n), good (iterateSamples (stopUnless good advance) k s
      (fun i => ξ (Fin.castLE hk i))) := by
  classical
  induction n with
  | zero =>
    intro k hk
    have he : k = 0 := by omega
    subst k
    exact hg
  | succ n ih =>
    have hfinal := hg
    rw [GapStrongGrowth.iterateSamples_succ_last] at hg
    have hp : good (iterateSamples (stopUnless good advance) n s (fun i => ξ i.castSucc)) := by
      by_contra h
      simp only [stopUnless, h, ↓reduceIte] at hg
    intro k hk
    by_cases he : k = n + 1
    · subst k
      simpa only [Fin.castLE_refl] using hfinal
    · have hk' : k ≤ n := by omega
      exact ih (fun i => ξ i.castSucc) hp k hk'

lemma stopped_exponential_integral {good : S → Prop} (hg : MeasurableSet {s | good s})
    {advance : S → Ω → S} (ha : Measurable (Function.uncurry advance))
    {V : S → ℝ} (hV : Measurable V) (P : ProbabilityMeasure Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ s, good s →
      Integrable (fun ω => Real.exp (V (advance s ω))) (P : Measure Ω) ∧
      (∫ ω, Real.exp (V (advance s ω)) ∂(P : Measure Ω)) ≤ Real.exp (V s + C))
    (n : ℕ) (s : S) :
    Integrable (fun ξ => Real.exp (V (iterateSamples (stopUnless good advance) n s ξ)))
      (Measure.pi fun _ : Fin n => (P : Measure Ω)) ∧
    (∫ ξ, Real.exp (V (iterateSamples (stopUnless good advance) n s ξ))
      ∂Measure.pi (fun _ : Fin n => (P : Measure Ω))) ≤ Real.exp (V s + n * C) := by
  classical
  have hs (s : S) :
      Integrable (fun ω => Real.exp (V (stopUnless good advance s ω))) (P : Measure Ω) ∧
      (∫ ω, Real.exp (V (stopUnless good advance s ω)) ∂(P : Measure Ω)) ≤
        Real.exp C * Real.exp (V s) + 0 := by
    by_cases hh : good s
    · simpa only [stopUnless, hh, ↓reduceIte, Real.exp_add, add_zero, mul_comm] using hstep s hh
    · simp only [stopUnless, hh, ↓reduceIte]
      refine ⟨integrable_const _, ?_⟩
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, add_zero]
      have he : 1 ≤ Real.exp C := by simpa using Real.exp_le_exp.mpr hC
      nlinarith [Real.exp_pos (V s)]
  have hh := GapStrongGrowth.iterateSamples_measurable_integral (stopUnless_measurable hg ha) P
    (fun s => Real.exp (V s)) (Real.measurable_exp.comp hV)
    (fun _ => (Real.exp_pos _).le) (Real.exp_nonneg C)
     hs n s
  refine ⟨hh.1, ?_⟩
  simpa only [zero_mul, add_zero, zero_add, ← Real.exp_nat_mul, ← Real.exp_add, add_comm] using hh.2

lemma stopped_exponential_tail {good : S → Prop} (hg : MeasurableSet {s | good s})
    {advance : S → Ω → S} (ha : Measurable (Function.uncurry advance))
    {V : S → ℝ} (hV : Measurable V) (P : ProbabilityMeasure Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ s, good s →
      Integrable (fun ω => Real.exp (V (advance s ω))) (P : Measure Ω) ∧
      (∫ ω, Real.exp (V (advance s ω)) ∂(P : Measure Ω)) ≤ Real.exp (V s + C))
    (n : ℕ) (s : S) (r : ℝ) :
    (Measure.pi fun _ : Fin n => (P : Measure Ω))
      {ξ | r < V (iterateSamples (stopUnless good advance) n s ξ)} ≤
      ENNReal.ofReal (Real.exp (V s + n * C - r)) := by
  have hh := stopped_exponential_integral hg ha hV P hC hstep n s
  simpa only [one_mul] using StochasticGeneralized.exponential_tail
    (t := 1) (r := r) (by norm_num) (by simpa only [one_mul] using hh.1) (by simpa only [one_mul] using hh.2)

def accumulatingTransition (advance : S → Ω → S) (increment : S → Ω → ℝ)
    (s : S × ℝ) (ω : Ω) : S × ℝ := (advance s.1 ω, s.2 + increment s.1 ω)

lemma accumulatingTransition_measurable {advance : S → Ω → S} {increment : S → Ω → ℝ}
    (ha : Measurable (Function.uncurry advance)) (hi : Measurable (Function.uncurry increment)) :
    Measurable (Function.uncurry (accumulatingTransition advance increment)) := by
  exact (ha.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    (measurable_fst.snd.add (hi.comp (measurable_fst.fst.prodMk measurable_snd)))

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma accumulatingTransition_first (advance : S → Ω → S) (increment : S → Ω → ℝ)
    (n : ℕ) (s : S) (a : ℝ) (ξ : Fin n → Ω) :
    (iterateSamples (accumulatingTransition advance increment) n (s, a) ξ).1 =
      iterateSamples advance n s ξ := by
  induction n generalizing s a with
  | zero => rfl
  | succ n ih => exact ih _ _ _

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma stopped_accumulatingTransition_first (good : S → Prop) (advance : S → Ω → S)
    (increment : S → Ω → ℝ) (n : ℕ) (s : S) (a : ℝ) (ξ : Fin n → Ω) :
    (iterateSamples (stopUnless (fun z : S × ℝ => good z.1)
      (accumulatingTransition advance increment)) n (s, a) ξ).1 =
      iterateSamples (stopUnless good advance) n s ξ := by
  classical
  induction n generalizing s a with
  | zero => rfl
  | succ n ih =>
    by_cases hg : good s
    · simp only [iterateSamples, stopUnless, hg, ↓reduceIte, accumulatingTransition]
      exact ih _ _ _
    · rw [stopped_constant (fun z : S × ℝ => good z.1) _ (s, a) hg,
        stopped_constant good advance s hg]

lemma accumulated_exponential_tail {good : S → Prop} (hg : MeasurableSet {s | good s})
    {advance : S → Ω → S} (ha : Measurable (Function.uncurry advance))
    {increment : S → Ω → ℝ} (hi : Measurable (Function.uncurry increment))
    (P : ProbabilityMeasure Ω)
    (hstep : ∀ s, good s →
      Integrable (fun ω => Real.exp (increment s ω)) (P : Measure Ω) ∧
      (∫ ω, Real.exp (increment s ω) ∂(P : Measure Ω)) ≤ 1)
    (n : ℕ) (s : S) (a r : ℝ) :
    (Measure.pi fun _ : Fin n => (P : Measure Ω))
      {ξ | good (iterateSamples (stopUnless good advance) n s ξ) ∧
        a + r < (iterateSamples (accumulatingTransition advance increment) n (s, a) ξ).2} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have hs (z : S × ℝ) (hz : good z.1) :
      Integrable (fun ω => Real.exp ((accumulatingTransition advance increment z ω).2)) (P : Measure Ω) ∧
      (∫ ω, Real.exp ((accumulatingTransition advance increment z ω).2) ∂(P : Measure Ω)) ≤
        Real.exp (z.2 + 0) := by
    have hh := hstep z.1 hz
    simp only [accumulatingTransition, Real.exp_add, add_zero]
    refine ⟨hh.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 (Real.exp_nonneg z.2)
  have hh := stopped_exponential_tail (hg.preimage measurable_fst)
    (accumulatingTransition_measurable ha hi) measurable_snd P (by norm_num : (0 : ℝ) ≤ 0)
    hs n (s, a) (a + r)
  have he : a + (n : ℝ) * 0 - (a + r) = -r := by ring
  rw [he] at hh
  apply (measure_mono ?_).trans hh
  intro ξ hξ
  have hfirst := stopped_accumulatingTransition_first good advance increment n s a ξ
  have hgood : good (iterateSamples (stopUnless (fun z : S × ℝ => good z.1)
      (accumulatingTransition advance increment)) n (s, a) ξ).1 := by
    rw [hfirst]
    exact hξ.1
  have heq := (stopped_compare (fun z : S × ℝ => good z.1)
    (accumulatingTransition advance increment) n (s, a) ξ).resolve_right (fun hn => hn hgood)
  change a + r < (iterateSamples (stopUnless (fun z : S × ℝ => good z.1)
    (accumulatingTransition advance increment)) n (s, a) ξ).2
  rw [← heq]
  exact hξ.2

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma iterateSamples_along (advance : S → Ω → S) (x : ℕ → S) (ξ : ℕ → Ω)
    (hx : ∀ t, x (t + 1) = advance (x t) (ξ t)) (n : ℕ) :
    iterateSamples advance n (x 0) (fun i => ξ i) = x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GapStrongGrowth.iterateSamples_succ_last]
    simpa only [Fin.val_castSucc, ih, Fin.val_last] using (hx n).symm

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma accumulated_along (advance : S → Ω → S) (increment : S → Ω → ℝ)
    (x : ℕ → S) (ξ : ℕ → Ω) (hx : ∀ t, x (t + 1) = advance (x t) (ξ t))
    (n : ℕ) (a : ℝ) :
    iterateSamples (accumulatingTransition advance increment) n (x 0, a) (fun i => ξ i) =
      (x n, a + ∑ t ∈ Finset.range n, increment (x t) (ξ t)) := by
  induction n with
  | zero => simp [iterateSamples]
  | succ n ih =>
    rw [GapStrongGrowth.iterateSamples_succ_last]
    simp only [Fin.val_castSucc, ih, Fin.val_last, accumulatingTransition, Finset.sum_range_succ, hx n]
    congr 1
    ring

end OracleTemplate.TerminalClipping
