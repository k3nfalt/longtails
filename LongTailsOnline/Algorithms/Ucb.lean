import LongTailsOnline.Setups.StochasticBandit

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Algorithms.Ucb

open LongTailsOnline.Setups.StochasticBandit

def armOfNat (k n : ℕ) : Arm k := ⟨n % (k + 1), Nat.mod_lt _ (by omega)⟩

@[simp]
lemma armOfNat_val {k : ℕ} (i : Arm k) : armOfNat k i.val = i := by
  apply Fin.ext
  simp [armOfNat, Nat.mod_eq_of_lt i.isLt]

lemma maximum_exists {k : ℕ} (v : Arm k → ℝ) :
    ∃ n, n < k + 1 ∧ ∀ i, v i ≤ v (armOfNat k n) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ v (by simp)
  exact ⟨i.val, i.isLt, by simpa using hi⟩

noncomputable def maximum {k : ℕ} (v : Arm k → ℝ) : Arm k :=
  armOfNat k (Nat.find (maximum_exists v))

lemma le_maximum {k : ℕ} (v : Arm k → ℝ) (i : Arm k) :
    v i ≤ v (maximum v) := (Nat.find_spec (maximum_exists v)).2 i

@[fun_prop]
lemma measurable_maximum (k : ℕ) : Measurable (maximum : (Arm k → ℝ) → Arm k) := by
  apply (measurable_of_countable (armOfNat k)).comp
  apply measurable_find (maximum_exists (k := k))
  intro n
  have hm (i : Arm k) : MeasurableSet {v : Arm k → ℝ | v i ≤ v (armOfNat k n)} :=
    measurableSet_le (measurable_pi_apply i) (measurable_pi_apply (armOfNat k n))
  have he : {v : Arm k → ℝ | ∀ i, v i ≤ v (armOfNat k n)} =
      ⋂ i, {v : Arm k → ℝ | v i ≤ v (armOfNat k n)} := by ext v; simp
  have hall : MeasurableSet {v : Arm k → ℝ | ∀ i, v i ≤ v (armOfNat k n)} :=
    he.symm ▸ MeasurableSet.iInter hm
  have hc : MeasurableSet {v : Arm k → ℝ | n < k + 1} := MeasurableSet.const _
  exact hc.inter hall

noncomputable def radius (t n : ℕ) : ℝ := Real.sqrt (2 * Real.log (t + 1) / n)

noncomputable def index {k : ℕ} (t : ℕ) (s : Statistics k) (i : Arm k) : ℝ :=
  s.2 i / s.1 i + radius t (s.1 i)

noncomputable def select {k : ℕ} (t : ℕ) (s : Statistics k) : Arm k :=
  if t < k + 1 then armOfNat k t else maximum (index t s)

@[fun_prop]
lemma measurable_index (k t : ℕ) : Measurable (fun s : Statistics k => index t s) := by
  unfold index radius
  fun_prop

@[fun_prop]
lemma measurable_select (k t : ℕ) : Measurable (select (k := k) t) := by
  unfold select
  split_ifs
  · exact measurable_const
  · exact (measurable_maximum k).comp (measurable_index k t)

noncomputable abbrev algorithm (k : ℕ) : OnlineTemplate.Algorithm Unit (Arm k) ℝ where
  State := Statistics k
  initial := ⟨Measure.dirac (fun _ => 0, fun _ => 0), inferInstance⟩
  choose t := Kernel.deterministic (fun s => (select t s.1, s.1)) (by fun_prop)
  update _ := Kernel.deterministic (fun s => record s.1 s.2.2.1 s.2.2.2) (by fun_prop)

end LongTailsOnline.Algorithms.Ucb
