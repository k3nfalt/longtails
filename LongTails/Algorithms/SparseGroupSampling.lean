import LongTails.Setups.OptimumGapGroupDro
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory
open scoped BigOperators

namespace LongTails.Algorithms.SparseGroupSampling

open OracleTemplate LongTails.Setups.OptimumGapGroupDro

noncomputable def finiteMinimizer {α : Type*} [Fintype α] [Nonempty α]
    (score : α → ℝ) : α := by
  classical
  exact Finset.univ.toList.foldl (fun best i => if score i < score best then i else best)
    (Classical.arbitrary α)

noncomputable def finiteMaximizer {α : Type*} [Fintype α] [Nonempty α]
    (score : α → ℝ) : α := finiteMinimizer (fun i => -score i)

noncomputable def coordinateScale (q : Public) : ℝ := q.ε / (512 * (q.d + 1 : ℝ) ^ 2 * (1 + q.G))

noncomputable def meshCardBound (q : Public) : ℕ :=
  (2 * (Nat.ceil (q.R / coordinateScale q) + 1) + 1) ^ q.d

def IsPrimalMesh (q : Public) (H : Finset (Space q.d)) : Prop :=
  H.Nonempty ∧ H.card ≤ meshCardBound q ∧ (∀ x ∈ H, x ∈ q.domain) ∧
    ∀ x ∈ q.domain, ∃ y ∈ H, dist x y ≤ (q.d + 1 : ℝ) * coordinateScale q

noncomputable def primalMesh (q : Public) : Finset (Space q.d) := by
  classical
  exact if h : ∃ H, IsPrimalMesh q H then h.choose else {q.x0}

lemma primalMesh_nonempty (q : Public) : (primalMesh q).Nonempty := by
  classical
  unfold primalMesh
  split_ifs with h
  · exact h.choose_spec.1
  · exact Finset.singleton_nonempty _

abbrev PrimalIndex (q : Public) := ↥(primalMesh q)

noncomputable instance (q : Public) : Fintype (PrimalIndex q) := Fintype.ofFinite _

instance (q : Public) : Nonempty (PrimalIndex q) := (primalMesh_nonempty q).coe_sort

def SparseSimplex (q : Public) : Set (Fin q.K → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
    ∃ S : Finset (Fin q.K), S.card ≤ q.d + 1 ∧ ∀ i, i ∉ S → w i = 0}

noncomputable def dualMeshRadius (q : Public) : ℝ := q.ε / (512 * (q.d + 1 : ℝ) * q.K)

def IsDualMesh (q : Public) (W : Finset (Fin q.K → ℝ)) : Prop :=
  W.Nonempty ∧ (∀ w ∈ W, w ∈ SparseSimplex q) ∧
    ∀ w ∈ SparseSimplex q, ∃ v ∈ W, dist w v ≤ dualMeshRadius q

noncomputable def dualMesh (q : Public) : Finset (Fin q.K → ℝ) := by
  classical
  exact if h : ∃ W, IsDualMesh q W then h.choose else {Pi.single 0 1}

lemma dualMesh_nonempty (q : Public) : (dualMesh q).Nonempty := by
  classical
  unfold dualMesh
  split_ifs with h
  · exact h.choose_spec.1
  · exact Finset.singleton_nonempty _

abbrev DualIndex (q : Public) := ↥(dualMesh q)

noncomputable instance (q : Public) : Fintype (DualIndex q) := Fintype.ofFinite _

instance (q : Public) : Nonempty (DualIndex q) := (dualMesh_nonempty q).coe_sort

noncomputable def confidenceLog (q : Public) : ℝ :=
  Real.log (128 * q.K * (q.d + 1 : ℝ) / (q.ε * q.δ)) +
    q.d * Real.log (8 + 4096 * q.R * (q.d + 1 : ℝ) ^ 2 * (1 + q.G) / q.ε)

noncomputable def radius (q : Public) (n : ℕ) : ℝ :=
  if n = 0 then 1 else min 1 (Real.sqrt (8 * confidenceLog q / n))

abbrev State (q : Public) :=
  (Fin q.K → ℕ) × (Fin q.K → PrimalIndex q → ℝ) × Option (PrimalIndex q)

noncomputable def upper (q : Public) (s : State q) (i : Fin q.K)
    (h : PrimalIndex q) : ℝ := s.2.1 i h / s.1 i + radius q (s.1 i)

noncomputable def primalChoice (q : Public) (s : State q) : PrimalIndex q :=
  finiteMinimizer (fun h => upper q s (finiteMaximizer (fun i => upper q s i h)) h)

noncomputable def dualChoice (q : Public) (s : State q) : DualIndex q :=
  finiteMaximizer (fun w =>
    let h := finiteMinimizer (fun h => ∑ i, w.val i * upper q s i h)
    ∑ i, w.val i * upper q s i h)

noncomputable def uncertainty (q : Public) (s : State q) (i : Fin q.K) : ℝ :=
  (dualChoice q s).val i * radius q (s.1 i)

noncomputable def selectedGroup (q : Public) (s : State q) : Fin q.K :=
  finiteMaximizer (uncertainty q s)

noncomputable def certified (q : Public) (s : State q) : Prop :=
  uncertainty q s (selectedGroup q s) ≤ q.ε / (4 * (q.d + 1 : ℝ))

noncomputable def step (q : Public) (s : State q) (z : q.Z) : State q := by
  classical
  exact match s.2.2 with
    | some _ => s
    | none =>
      let i := selectedGroup q s
      let next : State q :=
        (Function.update s.1 i (s.1 i + 1),
          Function.update s.2.1 i (fun h => s.2.1 i h + q.loss h.val z), none)
      if certified q next then (next.1, next.2.1, some (primalChoice q next)) else next

noncomputable def output (q : Public) (s : State q) : Space q.d :=
  match s.2.2 with
  | some h => h.val
  | none => (primalChoice q s).val

noncomputable def algorithm (q : Public) : Algorithm (Fin q.K) q.Z (Space q.d) where
  State := State q
  initial _ := (fun _ => 0, fun _ _ => 0, none)
  query s := (0, match s.2.2 with | some _ => 0 | none => selectedGroup q s)
  update := step q
  output := output q

end LongTails.Algorithms.SparseGroupSampling
