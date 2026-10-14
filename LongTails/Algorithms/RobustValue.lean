import LongTails.Algorithms.Batched
import Mathlib.MeasureTheory.Constructions.Pi

namespace OracleTemplate.FiniteVariance

def median3 (a b c : ℝ) : ℝ := max (min a b) (max (min b c) (min c a))

abbrev TreeSample (Ω : Type*) : ℕ → Type _
  | 0 => Ω
  | k + 1 => Fin 3 → TreeSample Ω k

instance treeSampleMeasurable {Ω : Type*} [MeasurableSpace Ω] :
    (k : ℕ) → MeasurableSpace (TreeSample Ω k)
  | 0 => inferInstanceAs (MeasurableSpace Ω)
  | k + 1 => @MeasurableSpace.pi (Fin 3) (fun _ => TreeSample Ω k)
      (fun _ => treeSampleMeasurable k)

def treeValue {Ω : Type*} (X : Ω → ℝ) : (k : ℕ) → TreeSample Ω k → ℝ
  | 0 => X
  | k + 1 => fun ξ => median3 (treeValue X k (ξ 0))
      (treeValue X k (ξ 1)) (treeValue X k (ξ 2))

noncomputable def medianBatched {Q U : Type} (A : Algorithm Q ℝ U) : Algorithm Q ℝ U :=
  batched (by decide : 0 < 3) A (fun s _ => (A.query s).2)
    (fun _ v => median3 (v 0) (v 1) (v 2)) 0

noncomputable def robustify {Q U : Type} : ℕ → Algorithm Q ℝ U → Algorithm Q ℝ U
  | 0, A => A
  | k + 1, A => robustify k (medianBatched A)

def blockValue {Q : Type} (g : Q → ℕ → ℝ) : ℕ → Q → ℕ → ℝ
  | 0 => g
  | k + 1 => fun x j => median3 (blockValue g k x (j*3))
    (blockValue g k x (j*3+1)) (blockValue g k x (j*3+2))

noncomputable def liftState {Q U : Type} : (k : ℕ) → (A : Algorithm Q ℝ U) → A.State → (robustify k A).State
  | 0, _, s => s
  | k + 1, A, s => liftState k (medianBatched A) (0, s, fun _ => 0)

noncomputable def liftSeed {Q U : Type} : (k : ℕ) → (A : Algorithm Q ℝ U) → A.Seed → (robustify k A).Seed
  | 0, _, s => s
  | k + 1, A, s => liftSeed k (medianBatched A) s

noncomputable def averagedRobustify {Q U : Type} {n : ℕ} (hn : 0 < n)
    (k : ℕ) (A : Algorithm Q ℝ U) : Algorithm Q ℝ U :=
  batched hn (robustify k A) (fun s _ => ((robustify k A).query s).2)
    (fun _ v => (∑ i, v i) / n) 0

noncomputable def valueRequest {Q : Type} (x : Q) : Algorithm Q ℝ ℝ where
  State := ℝ
  initial _ := 0
  query _ := (0, x)
  update _ reply := reply
  output v := v

end OracleTemplate.FiniteVariance
