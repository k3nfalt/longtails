import LongTails.Template
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import LongTails.Proofs.CorruptedFirstOrderDelay
import LongTails.Proofs.CorruptedFirstOrderHiding
import LongTails.TemplateLowerBound

open MeasureTheory
open scoped BigOperators ENNReal

namespace LongTails.Proofs.CorruptedFirstOrderAveraging

open Classical

lemma some_bad_set {Ω W : Type*} [MeasurableSpace Ω] [Fintype W] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : W → Set Ω) (hc : 0 < Fintype.card W)
    (h : ∀ z, (Fintype.card W : ℝ) / 2 ≤ ∑ w, if z ∈ B w then (1 : ℝ) else 0) :
    ∃ w, (1 / 4 : ℝ≥0∞) < P (B w) := by
  by_contra! hall
  let X (w : W) : Ω → ℝ := (toMeasurable P (B w)).indicator 1
  have hX (w : W) : Integrable (X w) P :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable _ _)
  have hmean (w : W) : ∫ z, X w z ∂P ≤ 1 / 4 := by
    rw [show ∫ z, X w z ∂P = P.real (toMeasurable P (B w)) from
      integral_indicator_one (measurableSet_toMeasurable _ _)]
    rw [Measure.real, measure_toMeasurable]
    have hh := ENNReal.toReal_mono (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤) (hall w)
    norm_num at hh
    exact hh
  have hp (z : Ω) : (Fintype.card W : ℝ) / 2 ≤ ∑ w, X w z := by
    refine (h z).trans (Finset.sum_le_sum ?_)
    intro w _
    by_cases hz : z ∈ B w
    · simp [hz, X, Set.indicator_of_mem (subset_toMeasurable P (B w) hz)]
    · simp only [hz, ↓reduceIte]
      exact Set.indicator_nonneg (by simp) _
  have hm := integral_mono (integrable_const ((Fintype.card W : ℝ) / 2))
    (integrable_finsetSum Finset.univ (fun w _ => hX w)) hp
  rw [integral_const, probReal_univ, one_smul, integral_finsetSum Finset.univ (fun w _ => hX w)] at hm
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hmean w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  have hpos : 0 < (Fintype.card W : ℝ) := by exact_mod_cast hc
  linarith

end LongTails.Proofs.CorruptedFirstOrderAveraging

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal
open LongTails.Setups.CorruptedFirstOrderNonconvex
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.FiniteSumNondualLowerAveraging
open LongTails.Proofs.FiniteSumNondualLowerBound LongTails.Proofs.CorruptedFirstOrderChain
open LongTails.Proofs.CorruptedFirstOrderDelay LongTails.Proofs.CorruptedFirstOrderHiding
open LongTails.Proofs.CorruptedFirstOrderAveraging

namespace LongTails.Proofs.CorruptedFirstOrderLowerBound

open Classical

lemma adversary (p : Params) (hp : HighDimensional.spec.valid p) (A : Method p.d) (N : ℕ)
    (hN : N ≤ p.k + ⌊p.L * p.Δ / (2 ^ 25 * p.ε ^ 2)⌋₊) :
    ∃ (f : Space p.d → ℝ) (O : Oracle (Space p.d) (ℝ × Space p.d)),
      HighDimensional.spec.admissible p f O ∧
      ¬HighDimensional.spec.successful p f (fun z : A.Seed × ((j : ℕ) → O.Seed j) =>
        execute O A (fun _ => N) z.1 z.2) ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let n := N - p.k
  let m := min N p.k
  let W := CoordinateWords p.d n
  have hn : n ≤ ⌊p.L * p.Δ / (2 ^ 25 * p.ε ^ 2)⌋₊ := by dsimp [n]; omega
  have hnm : n + m = N := by dsimp [n, m]; omega
  have hd : 2 ^ 32 * (n + 1) ^ 4 ≤ p.d := by
    apply le_trans _ hp.2.2.2
    gcongr
  have hnd : n + 1 ≤ p.d := by
    have h1 : n + 1 ≤ (n + 1) ^ 4 := by
      simpa using (Nat.pow_le_pow_right (by omega : 0 < n + 1) (by decide : 1 ≤ 4))
    omega
  let S := scale p hp.1 hp.2.1
  let f (w : W) := objective S (coordinateEmbedding w) p.x0
  let B (w : W) := {z : A.Seed × (ℕ → Unit) |
    p.ε < ‖gradient (f w) (execute (oracle m (f w)) A (fun _ => N) z.1 z.2)‖}
  let Q : Measure (ℕ → Unit) := Measure.dirac (fun _ => ())
  let P : Measure (A.Seed × (ℕ → Unit)) := (A.law : Measure _).prod Q
  have hc : 0 < Fintype.card W := coordinateWords_card_pos p.d n hnd
  have hw (z : A.Seed × (ℕ → Unit)) :
      (Fintype.card W : ℝ) / 2 ≤ ∑ w, if z ∈ B w then (1 : ℝ) else 0 := by
    let st := warm A (A.initial z.1) m
    let bad (w : W) := Hit (n := n) A st S p.x0 w.val
    have hbad := few_hits A st S p.x0 hd
    change 8 * (∑ w : W, if bad w then (1 : ℝ) else 0) ≤ Fintype.card W at hbad
    have hpoint (w : W) : 1 ≤ (if bad w then (1 : ℝ) else 0) + (if z ∈ B w then (1 : ℝ) else 0) := by
      by_cases hh : bad w
      · simp [hh]; split <;> norm_num
      · have hl := miss_lower A st S p.x0 w hh
        have hratio : S.a / S.lam = 60 * p.ε := scale_ratio p hp.1 hp.2.1
        rw [hratio] at hl
        have hε := hp.2.1
        have hz : z ∈ B w := by
          change p.ε < ‖gradient (f w) (execute (oracle m (f w)) A (fun _ => N) z.1 z.2)‖
          rw [← hnm]
          erw [delayed_output m A z.1 p.x0 S (coordinateEmbedding w) z.2, objective_gradient]
          linarith
        simp [hh, hz]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpoint w)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (Measure.dirac (fun _ : ℕ => ())))
  have : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure ((A.law : Measure A.Seed).prod Q))
  obtain ⟨w, hw⟩ := some_bad_set P B hc hw
  refine ⟨f w, oracle m (f w), instance_admissible p hp m n (min_le_right _ _) hn _, ?_⟩
  intro hs
  exact (not_lt_of_ge (hs.trans p.failure.property.2)) hw

end LongTails.Proofs.CorruptedFirstOrderLowerBound
