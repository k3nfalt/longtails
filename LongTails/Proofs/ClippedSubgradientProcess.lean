import LongTails.Proofs.ClippedSubgradientStep
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.GapStrongGrowthIteration

open MeasureTheory
open scoped RealInnerProductSpace BigOperators
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

lemma even_samples_iid {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {ν : Measure Ω} {P : Measure Ξ}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ν P) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k => ξ (2 * k)) ν P where
  measurable k := h.measurable (2 * k)
  independent := h.independent.precomp (g := fun k : ℕ => 2 * k) (by
    intro a b hab
    dsimp only at hab
    omega)
  marginal k := h.marginal (2 * k)

section Accumulate

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

def accumulatingTransition (advance : S → Ω → S) (increment : S → Ω → ℝ)
    (s : S × ℝ) (ω : Ω) : S × ℝ := (advance s.1 ω, s.2 + increment s.1 ω)

lemma accumulatingTransition_measurable {advance : S → Ω → S} {increment : S → Ω → ℝ}
    (ha : Measurable (Function.uncurry advance)) (hi : Measurable (Function.uncurry increment)) :
    Measurable (Function.uncurry (accumulatingTransition advance increment)) := by
  exact (ha.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    (measurable_fst.snd.add (hi.comp (measurable_fst.fst.prodMk measurable_snd)))

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

end Accumulate

noncomputable def sampleOracle (q : Params) (g : q.E → q.Ω → q.E) (projection : q.E → q.E)
    (P : ProbabilityMeasure (ℕ → q.Ω)) : Oracle (Query q) q.E where
  Seed := fun _ => q.Ω
  law := P
  answer := fun _ (_, query) seed => match query with
    | .subgradient x => g x seed
    | .projection x => projection x

noncomputable def trajFrom {Ω : Type*} (q : Params) (g : q.E → Ω → q.E)
    (projection : q.E → q.E) (x : q.E) (ξ : ℕ → Ω) : ℕ → q.E
  | 0 => x
  | n + 1 => transition q g projection (trajFrom q g projection x ξ n) (ξ n)

lemma trajFrom_shift {Ω : Type*} (q : Params) (g : q.E → Ω → q.E) (projection : q.E → q.E)
    (x : q.E) (ξ : ℕ → Ω) (m : ℕ) :
    trajFrom q g projection (transition q g projection x (ξ 0)) (fun k => ξ (k + 1)) m =
      trajFrom q g projection x ξ (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [trajFrom, ih]

lemma trajectory_eq_trajFrom {Ω : Type*} (q : Params) (g : q.E → Ω → q.E)
    (projection : q.E → q.E) (ξ : ℕ → Ω) (n : ℕ) :
    trajectory q g projection ξ n = trajFrom q g projection q.x0 ξ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [trajectory, trajFrom, ih]

noncomputable def run {Ω : Type*} (q : Params) (g : q.E → Ω → q.E) (projection : q.E → q.E) :
    ℕ → ℕ → q.E → ℕ → q.E → (ℕ → Ω) → State q
  | 0, t, x, idx, out, _ => ⟨t, x, false, x, idx, out⟩
  | n + 1, t, x, idx, out, ξ =>
      let y := transition q g projection x (ξ 0)
      run q g projection n (t + 1) y idx (if t + 1 = idx then y else out) (fun k => ξ (k + 2))

lemma advance_run (q : Params) (g : q.E → q.Ω → q.E) (projection : q.E → q.E)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (ξ : ℕ → q.Ω) (n call t idx : ℕ) (x out : q.E) :
    StochasticGradient.advance
      (fun k state => (algorithm q).update state
        ((sampleOracle q g projection P).answer [] ((algorithm q).query state) (ξ k)))
      (2 * n) call ⟨t, x, false, x, idx, out⟩ =
      run q g projection n t x idx out (fun k => ξ (call + k)) := by
  dsimp only [algorithm, ClippedSubgradient.method, sampleOracle]
  induction n generalizing call t x out with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [StochasticGradient.advance, StochasticGradient.advance]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ih]
    simp only [run, Nat.add_zero, transition]
    congr 1
    funext k
    congr 1
    omega

lemma run_out {Ω : Type*} (q : Params) (g : q.E → Ω → q.E) (projection : q.E → q.E)
    (n : ℕ) : ∀ (t idx : ℕ) (x out : q.E) (ξ : ℕ → Ω),
    (run q g projection n t x idx out ξ).out =
      if t < idx ∧ idx ≤ t + n then trajFrom q g projection x (fun k => ξ (2 * k)) (idx - t)
      else out := by
  induction n with
  | zero =>
    intro t idx x out ξ
    simp only [run]
    have h0 : ¬ (t < idx ∧ idx ≤ t + 0) := by omega
    rw [ite_eq_right h0]
  | succ n ih =>
    intro t idx x out ξ
    simp only [run]
    rw [ih]
    have hs : ∀ m, trajFrom q g projection (transition q g projection x (ξ 0))
        (fun k => ξ (2 * k + 2)) m = trajFrom q g projection x (fun k => ξ (2 * k)) (m + 1) := by
      intro m
      have := trajFrom_shift q g projection x (fun k => ξ (2 * k)) m
      simp only [mul_zero] at this
      exact this
    by_cases h1 : t + 1 < idx ∧ idx ≤ t + 1 + n
    · rw [ite_eq_left h1]
      have h2 : t < idx ∧ idx ≤ t + (n + 1) := by omega
      rw [ite_eq_left h2]
      have e : idx - t = (idx - (t + 1)) + 1 := by omega
      rw [e]
      exact hs _
    · rw [ite_eq_right h1]
      by_cases h3 : t + 1 = idx
      · rw [ite_eq_left h3]
        have h2 : t < idx ∧ idx ≤ t + (n + 1) := by omega
        rw [ite_eq_left h2]
        have e : idx - t = 1 := by omega
        simp only [e, trajFrom, mul_zero]
      · rw [ite_eq_right h3]
        have h2 : ¬ (t < idx ∧ idx ≤ t + (n + 1)) := by omega
        rw [ite_eq_right h2]

lemma execute_algorithm (q : Params) (g : q.E → q.Ω → q.E) (projection : q.E → q.E)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (j : Fin (steps q + 1)) (ξ : ℕ → q.Ω) :
    execute (sampleOracle q g projection P) (algorithm q) (fun _ => (2 * steps q)) j ξ =
      trajectory q g projection (fun k => ξ (2 * k)) j.val := by
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun k query => (sampleOracle q g projection P).answer [] query (ξ k)) (fun _ _ => rfl)]
  have h := advance_run q g projection P ξ (steps q) 0 0 j.val q.x0 q.x0
  simp only [Nat.zero_add] at h
  have hinit : (algorithm q).initial j = ⟨0, q.x0, false, q.x0, j.val, q.x0⟩ := rfl
  rw [hinit, h]
  simp only [algorithm, ClippedSubgradient.method]
  rw [run_out, trajectory_eq_trajFrom]
  by_cases hj : 0 < j.val
  · have : 0 < j.val ∧ j.val ≤ 0 + steps q := ⟨hj, by have := j.isLt; omega⟩
    rw [ite_eq_left this]
    simp
  · have hj0 : j.val = 0 := by omega
    have : ¬ (0 < j.val ∧ j.val ≤ 0 + steps q) := by omega
    rw [ite_eq_right this, hj0]
    rfl

lemma trajectory_mem {Ω : Type*} (q : Params) (g : q.E → Ω → q.E) (projection : q.E → q.E)
    {D : Set q.E} (hx0 : q.x0 ∈ D) (hprojD : ∀ y, projection y ∈ D) (ξ : ℕ → Ω) (n : ℕ) :
    trajectory q g projection ξ n ∈ D := by
  cases n with
  | zero => exact hx0
  | succ n => exact hprojD _

lemma transition_measurable (q : Params) {g : q.E → q.Ω → q.E}
    (hg : Measurable (Function.uncurry g)) {projection : q.E → q.E}
    (hp : Measurable projection) :
    Measurable (Function.uncurry (transition q g projection)) := by
  unfold transition Function.uncurry
  exact hp.comp (measurable_fst.sub (((measurable_clip _).comp hg).const_smul _))

lemma trajectory_measurable (q : Params) {g : q.E → q.Ω → q.E}
    (hg : Measurable (Function.uncurry g)) {projection : q.E → q.E}
    (hp : Measurable projection) (n : ℕ) :
    Measurable (fun ξ : ℕ → q.Ω => trajectory q g projection ξ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (transition_measurable q hg hp).comp (ih.prodMk (measurable_pi_apply n))

lemma trajectory_eq_iterate {Ω : Type*} (q : Params) (g : q.E → Ω → q.E)
    (projection : q.E → q.E) (ξ : ℕ → Ω) (n : ℕ) :
    iterateSamples (transition q g projection) n q.x0 (fun i : Fin n => ξ i.val) =
      trajectory q g projection ξ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GapStrongGrowth.iterateSamples_succ_last]
    change transition q g projection
      (iterateSamples (transition q g projection) n q.x0 (fun i : Fin n => ξ i.val)) (ξ n) = _
    rw [ih]
    rfl

end OracleTemplate.WeaklyConvexHeavyTailed
