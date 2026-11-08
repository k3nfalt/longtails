import LongTails.Proofs.BirchNonEuclideanSymbolic
import LongTails.Proofs.BirchNonEuclideanMoments

namespace LongTails.Proofs.BirchNonEuclideanCausality

open MeasureTheory
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (dualNorm)
open OracleTemplate.NormBallLMO
open LongTails.Proofs.BirchNonEuclideanExecution

def MeasurableMemory {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (m : Ξ → Memory d) : Prop :=
  (∀ j, Measurable (fun ξ => (m ξ).points j)) ∧ ∀ j, Measurable (fun ξ => (m ξ).vectors j)

lemma perform_measurable {Ξ : Type*} [MeasurableSpace Ξ] (p : Params)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (m : Ξ → Memory p.d) (hm : MeasurableMemory m) (n : ℕ) (hn : ∀ ξ, (m ξ).next = n)
    (i : Instruction) (reply : Ξ → Point p.d) (hr : Measurable reply) :
    MeasurableMemory (fun ξ => perform p lmo (m ξ) i (reply ξ)) := by
  have hstore (v : Ξ → Point p.d) (hv : Measurable v) (deps : Ξ → Finset ℕ) :
      MeasurableMemory (fun ξ => storeVector (m ξ) (v ξ) (deps ξ)) := by
    refine ⟨hm.1, fun j => ?_⟩
    by_cases hj : j = n
    · simpa [storeVector, hn, hj] using hv
    · simpa [storeVector, hn, hj] using hm.2 j
  cases i with
  | query worker point => exact hstore reply hr (fun ξ => insert (m ξ).replies ((m ξ).pointSamples point))
  | mix worker terms =>
      apply hstore
      induction terms with
      | nil => simp
      | cons t ts ih =>
          simp only [List.map_cons, List.sum_cons]
          convert ((hm.2 t.2).const_smul t.1).add ih using 1
  | difference worker x y => exact hstore _ ((hm.1 x).sub (hm.1 y)) _
  | lmo worker v => exact hstore _ (hlmo.comp (hm.2 v)) _
  | sharp worker v =>
      exact hstore _ (((continuous_dualNorm hR hR0).measurable.comp (hm.2 v)).smul
        (hlmo.comp (hm.2 v))) _
  | move worker x v η =>
      refine ⟨fun j => ?_, hm.2⟩
      by_cases hj : j = n
      · simp only [perform, hn, hj, Function.update_self]
        convert (hm.1 x).add ((hm.2 v).const_smul η) using 1
      · simpa [perform, hn, hj] using hm.1 j
  | sendPoint worker other x => exact hm
  | sendVector worker other x => exact hm

lemma interpret_measurable {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (g : Point p.d → Ω → Point p.d) (hg : Measurable (Function.uncurry g))
    (code : List Instruction) (m : (ℕ → Ω) → Memory p.d)
    (hm : MeasurableMemory m) (n r : ℕ) (hn : ∀ ξ, (m ξ).next = n)
    (hr : ∀ ξ, (m ξ).replies = r) :
    MeasurableMemory (fun ξ => interpret p lmo (fun k x => g x (ξ k)) code (m ξ)) := by
  induction code generalizing m n r with
  | nil => exact hm
  | cons i rest ih =>
      cases i with
      | query worker point =>
          have hreply : Measurable (fun ξ => g ((m ξ).points point) (ξ (m ξ).replies)) := by
            simpa only [hr, Function.comp_def, Function.uncurry_def] using
              hg.comp ((hm.1 point).prodMk (measurable_pi_apply r))
          exact ih _ (perform_measurable p lmo hlmo hR hR0 m hm n hn _ _ hreply) (n + 1) (r + 1)
            (fun ξ => by rw [perform_next, hn])
            (fun ξ => by rw [perform_replies, hr]; rfl)
      | mix worker terms | difference worker x y | lmo worker v | sharp worker v | move worker x v η | sendPoint worker other x | sendVector worker other x =>
          exact ih _ (perform_measurable p lmo hlmo hR hR0 m hm n hn _ _ measurable_const) (n + 1) r
            (fun ξ => by rw [perform_next, hn])
            (fun ξ => by rw [perform_replies, hr]; rfl)

lemma interpret_prefix_measurable {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (g : Point p.d → Ω → Point p.d) (hg : Measurable (Function.uncurry g))
    (code : List Instruction) :
    MeasurableMemory (fun ξ : ℕ → Ω => interpret p lmo (fun k x => g x (ξ k)) code (initialMemory p)) :=
  interpret_measurable p lmo hlmo hR hR0 g hg code _
    ⟨fun _ => measurable_const, fun _ => measurable_const⟩ 1 0 (fun _ => rfl) (fun _ => rfl)

lemma interpret_sample_congr {Ω : Type} (p : Params) (lmo : Point p.d → Point p.d)
    (g : Point p.d → Ω → Point p.d) (code : List Instruction) (m : Memory p.d)
    (ξ ξ' : ℕ → Ω) (h : ∀ j < m.replies + queryCount code, ξ j = ξ' j) :
    interpret p lmo (fun k x => g x (ξ k)) code m =
      interpret p lmo (fun k x => g x (ξ' k)) code m := by
  induction code generalizing m with
  | nil => rfl
  | cons i rest ih =>
      cases i with
      | query worker point =>
          simp only [interpret]
          rw [h m.replies (by simp [queryCount, Instruction.oracleCost])]
          apply ih
          intro j hj
          apply h j
          simpa [perform_replies, queryCount, Instruction.oracleCost, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using hj
      | mix worker terms | difference worker x y | lmo worker v | sharp worker v | move worker x v η | sendPoint worker other x | sendVector worker other x =>
          apply ih
          intro j hj
          apply h j
          simpa [perform_replies, queryCount, Instruction.oracleCost] using hj

lemma interpret_next (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code : List Instruction) (m : Memory p.d) :
    (interpret p lmo response code m).next = m.next + code.length := by
  induction code generalizing m with
  | nil => simp [interpret]
  | cons i rest ih =>
      cases i <;> simp only [interpret, ih, perform_next, List.length_cons] <;> omega

lemma interpret_replies (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code : List Instruction) (m : Memory p.d) :
    (interpret p lmo response code m).replies = m.replies + queryCount code := by
  induction code generalizing m with
  | nil => simp [interpret, queryCount]
  | cons i rest ih =>
      cases i <;> simp only [interpret, ih, perform_replies, queryCount, List.map_cons,
        List.sum_cons] <;> omega

lemma interpret_append (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (left right : List Instruction) (m : Memory p.d) :
    interpret p lmo response (left ++ right) m =
      interpret p lmo response right (interpret p lmo response left m) := by
  induction left generalizing m with
  | nil => rfl
  | cons i rest ih => cases i <;> simp only [List.cons_append, interpret, ih]

def queryLabels : List Instruction → ℕ → Finset ℕ
  | [], _ => ∅
  | i :: rest, n => if i.oracleCost = 1 then insert n (queryLabels rest (n + 1))
      else queryLabels rest (n + 1)

lemma symbolic_queryLabels (code : List Instruction) (s : SymbolicMemory) :
    (code.foldl symbolicPerform s).queries = s.queries ∪ queryLabels code s.next := by
  induction code generalizing s with
  | nil => simp [queryLabels]
  | cons i rest ih =>
      rw [List.foldl_cons, ih]
      cases i <;> simp [queryLabels, Instruction.oracleCost, symbolicPerform, symbolicStore,
        Finset.insert_union, Finset.union_insert]

lemma queryLabels_decompose (code : List Instruction) (n q : ℕ) (hq : q ∈ queryLabels code n) :
    ∃ (pre rest : List Instruction) (worker point : ℕ),
      code = pre ++ Instruction.query worker point :: rest ∧ q = n + pre.length := by
  induction code generalizing n with
  | nil => simp [queryLabels] at hq
  | cons i rest ih =>
      cases hcase : i with
      | query worker point =>
          simp only [hcase, queryLabels, Instruction.oracleCost, ite_true, Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact ⟨[], rest, worker, point, by simp, by simp⟩
          · obtain ⟨pre, tail, w, x, heq, hlen⟩ := ih (n + 1) hq
            refine ⟨Instruction.query worker point :: pre, tail, w, x, ?_, ?_⟩
            · simp [heq]
            · simp only [List.length_cons]
              omega
      | mix worker terms | difference worker x y | lmo worker v | sharp worker v | move worker x v η | sendPoint worker other x | sendVector worker other x =>
          simp only [hcase, queryLabels, Instruction.oracleCost, Nat.zero_ne_one, ite_false] at hq
          obtain ⟨pre, tail, w, x, heq, hlen⟩ := ih (n + 1) hq
          refine ⟨i :: pre, tail, w, x, ?_, ?_⟩
          · simp [hcase, heq]
          · simp only [List.length_cons]
            omega

lemma program_query_decompose (a : Program) (q : ℕ) (hq : q ∈ a.symbolic.queries) :
    ∃ (pre rest : List Instruction) (worker point : ℕ),
      a.instructions = pre ++ Instruction.query worker point :: rest ∧ q = pre.length + 1 := by
  have hm : q ∈ queryLabels a.instructions 1 := by
    simpa only [Program.symbolic, symbolic_queryLabels, Finset.empty_union] using hq
  obtain ⟨pre, rest, w, x, heq, hlen⟩ := queryLabels_decompose a.instructions 1 q hm
  exact ⟨pre, rest, w, x, heq, by omega⟩

lemma queryCount_append (left right : List Instruction) :
    queryCount (left ++ right) = queryCount left + queryCount right := by
  simp [queryCount]

lemma queryCount_take_le (code : List Instruction) (n : ℕ) :
    queryCount (code.take n) ≤ queryCount code := by
  have hh := queryCount_append (code.take n) (code.drop n)
  rw [List.take_append_drop] at hh
  omega

lemma queryCount_take_mono (code : List Instruction) {j k : ℕ} (hjk : j ≤ k) :
    queryCount (code.take j) ≤ queryCount (code.take k) := by
  have hh := queryCount_take_le (code.take k) j
  simpa only [List.take_take, Nat.min_eq_left hjk] using hh

lemma query_indices_strict (a : Program) (j k : ℕ) (hj : j ∈ a.symbolic.queries) (hjk : j < k) :
    queryCount (a.instructions.take (j - 1)) < queryCount (a.instructions.take (k - 1)) := by
  obtain ⟨pre, rest, worker, point, heq, hlen⟩ := program_query_decompose a j hj
  have hm := queryCount_take_mono a.instructions (show j ≤ k - 1 by omega)
  have hp : a.instructions.take (j - 1) = pre := by simp [heq, hlen]
  have hn : a.instructions.take j = pre ++ [Instruction.query worker point] := by
    rw [heq, hlen, List.take_append]
    simp
  rw [hp]
  rw [hn, queryCount_append] at hm
  simp only [queryCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Instruction.oracleCost, Nat.add_zero] at hm
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hm

end LongTails.Proofs.BirchNonEuclideanCausality
