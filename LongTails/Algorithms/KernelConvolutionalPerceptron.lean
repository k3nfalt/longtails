import LongTails.Setups.KernelConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.KernelConvolutionalPerceptron

open LongTails.Setups.KernelConvolutionalPerceptron

structure ScanState (k d n : ℕ) where
  point : Space k d
  cursor : Fin (n + 1)

noncomputable def stepSize (p : Params) : ℝ :=
  p.derivativeMargin / (16 * Real.sqrt (p.kernel / 2) * p.upper)

noncomputable def scanUpdate {k d n : ℕ} (η : ℝ) (state : ScanState k d n)
    (reply : Reply k d) : ScanState k d n :=
  ⟨if reply.margin ≤ 0 then state.point + η • reply.direction else state.point,
    finRotate (n + 1) state.cursor⟩

noncomputable def algorithm (p : Params) :
    Algorithm (Query p.kernel p.dimension p.samples) (Reply p.kernel p.dimension)
      (Space p.kernel p.dimension) where
  State := ScanState p.kernel p.dimension p.samples
  initial _ := ⟨identityFilter p.kernel p.dimension, 0⟩
  query state := (0, state.cursor, state.point)
  update := scanUpdate (stepSize p)
  output state := state.point

noncomputable def output (p : Params)
    (O : Oracle (Query p.kernel p.dimension p.samples) (Reply p.kernel p.dimension)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) : Space p.kernel p.dimension :=
  execute O (algorithm p) (fun _ => K) seed ξ

lemma stepSize_pos (p : Params) (hκ : 0 < p.derivativeMargin) (hk : 0 < p.kernel)
    (hR : 0 < p.upper) : 0 < stepSize p := by
  unfold stepSize
  have : 0 < Real.sqrt ((p.kernel : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma family_algorithm (p : Params) (hκ : 0 < p.derivativeMargin) (hk : 0 < p.kernel)
    (hR : 0 < p.upper) : family (algorithm p) := by
  refine ⟨ScanState.point, ScanState.cursor, stepSize p, stepSize_pos p hκ hk hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro seed; exact ⟨rfl, rfl⟩
  · intro s; rfl
  · intro s r; rfl
  · intro s r; rfl
  · intro s; rfl

end LongTails.Algorithms.KernelConvolutionalPerceptron
