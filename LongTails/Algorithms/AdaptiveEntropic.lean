import LongTails.Setups.AdaptiveHeavyTailSimplex
import Mathlib.Data.List.Sort

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def confidence (q : Public) : ℝ := Real.log (100 / q.δ)

noncomputable def window (q : Public) (t : ℕ) : ℕ :=
  ⌈16 * (confidence q + Real.log (t + 1))⌉₊

noncomputable def preload (q : Public) : ℕ := ⌈64 * confidence q⌉₊

noncomputable def geometry (q : Public) : ℝ := max 1 (Real.log q.d)

noncomputable def trimCount (q : Public) : ℕ :=
  max 1 ⌈64 * (geometry q + confidence q)⌉₊

noncomputable def minimumIndex {K : ℕ} (hK : 0 < K) (b : Fin K → ℝ) : Fin K :=
  (List.finRange K).foldl (fun i j => if b j < b i then j else i) ⟨0, hK⟩

noncomputable def softmax {d : ℕ} (hd : 0 < d) (v : Vector d) : simplex d := by
  have hs : 0 < ∑ i, Real.exp (v i) := by
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  refine ⟨WithLp.toLp 2 (fun i => Real.exp (v i) / ∑ j, Real.exp (v j)), ?_, ?_⟩
  · intro i
    exact div_nonneg (Real.exp_pos _).le hs.le
  · change (∑ i, Real.exp (v i) / ∑ j, Real.exp (v j)) = 1
    rw [← Finset.sum_div, div_self hs.ne']

noncomputable def uniform (q : Public) : simplex q.d := softmax (by have := q.hd; omega) 0

noncomputable def medianCenter {d : ℕ} (history : List (Vector d)) : Vector d :=
  WithLp.toLp 2 (fun i => ((history.map (fun v => v i)).mergeSort (· ≤ ·)).getD
    (history.length / 2) 0)

noncomputable def clippedReply {d : ℕ} (threshold : ℝ) (c g : Vector d) : Vector d :=
  c + if dualNorm (g - c) ≤ threshold then g - c else (threshold / dualNorm (g - c)) • (g - c)

noncomputable def mix {d : ℕ} (n : ℕ) (x y : simplex d) : simplex d := by
  let α : ℝ := 2 / (n + 2)
  have hden : (0 : ℝ) < n + 2 := by positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_one hden]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨(1 - α) • x.val + α • y.val, ?_, ?_⟩
  · intro i
    change 0 ≤ (1 - α) * x.val i + α * y.val i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hα1) (x.property.1 i))
      (mul_nonneg hα (y.property.1 i))
  · change (∑ i, ((1 - α) * x.val i + α * y.val i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      x.property.2, y.property.2]
    ring

structure State (q : Public) where
  warmup : ℕ
  completed : ℕ
  pending : Option (Vector q.d)
  history : List (Vector q.d)
  sumGradient : Vector q.d
  y : simplex q.d
  extremes : Fin (trimCount q) → ℝ
  variation : ℝ

noncomputable def quantileIndex (q : Public) (s : State q) : Fin (trimCount q) :=
  minimumIndex (by unfold trimCount; omega) s.extremes

noncomputable def empiricalQuantile (q : Public) (s : State q) : ℝ :=
  s.extremes (quantileIndex q s)

noncomputable def regularization (q : Public) (s : State q) : ℝ :=
  max (128 * q.L * window q (s.completed + 1) * trimCount q / geometry q)
    (max (128 * empiricalQuantile q s * trimCount q / geometry q)
      (128 * Real.sqrt (s.variation / geometry q)))

noncomputable def predictableProx (q : Public) (s : State q) : simplex q.d :=
  softmax (by have := q.hd; omega) (-(1 / regularization q s) • s.sumGradient)

noncomputable def driftRadius (q : Public) (s : State q) : ℝ :=
  24 * q.L * window q (s.completed + 1) / (s.completed + 1)

noncomputable def clippingThreshold (q : Public) (s : State q) : ℝ :=
  driftRadius q s + empiricalQuantile q s / (s.completed + 1)

noncomputable def initialState (q : Public) : State q where
  warmup := preload q
  completed := 0
  pending := none
  history := []
  sumGradient := 0
  y := uniform q
  extremes := fun _ => 0
  variation := 0

noncomputable def queryPoint (q : Public) (s : State q) : simplex q.d :=
  if 0 < s.warmup then uniform q else mix s.completed s.y (predictableProx q s)

noncomputable def updateState (q : Public) (s : State q) (g : Vector q.d) : State q :=
  if 0 < s.warmup then
    { s with warmup := s.warmup - 1, history := g :: s.history }
  else match s.pending with
    | none => { s with pending := some g }
    | some g₁ =>
      let t := s.completed + 1
      let c := medianCenter (s.history.take (window q t))
      let h := clippedReply (clippingThreshold q s) c g₁
      let h' := clippedReply (clippingThreshold q s) c g
      let sumGradient := s.sumGradient + (t : ℝ) • h
      let z := softmax (by have := q.hd; omega)
        (-(1 / regularization q s) • sumGradient)
      let v := (t : ℝ) * max 0 (dualNorm (g₁ - c) - driftRadius q s)
      { warmup := 0
        completed := t
        pending := none
        history := g₁ :: s.history
        sumGradient := sumGradient
        y := mix s.completed s.y z
        extremes := Function.update s.extremes (quantileIndex q s)
          (max (empiricalQuantile q s) v)
        variation := s.variation + (t : ℝ) ^ 2 * dualNorm (h - h') ^ 2 }

noncomputable def algorithm (q : Public) : Algorithm (simplex q.d) (Vector q.d)
    (simplex q.d) where
  State := State q
  initial := fun _ => initialState q
  query := fun s => (0, (queryPoint q) s)
  update := updateState q
  output := fun s => s.y

end OracleTemplate.AdaptiveHeavyTailSimplex
