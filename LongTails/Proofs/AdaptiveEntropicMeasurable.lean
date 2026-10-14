import LongTails.Proofs.AdaptiveListMeasurable
import LongTails.Algorithms.AdaptiveEntropic

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

set_option backward.isDefEq.respectTransparency false

lemma measurable_orderedInsert_ofFn (n : ℕ) :
    Measurable (fun w : ℝ × (Fin n → ℝ) =>
      List.orderedInsert (· ≤ ·) w.1 (List.ofFn w.2)) := by
  induction n with
  | zero =>
    simpa [Function.comp_def] using (AdaptiveList.measurable_cons (0 : ℝ)).comp
      (measurable_fst.prodMk (measurable_const : Measurable (fun _ : ℝ × (Fin 0 → ℝ) => ([] : List ℝ))))
  | succ n ih =>
    simp only [List.ofFn_succ, List.orderedInsert_cons]
    apply Measurable.ite (measurableSet_le
      (f := fun w : ℝ × (Fin (n + 1) → ℝ) => w.1)
      (g := fun w => w.2 0) measurable_fst ((measurable_pi_apply 0).comp measurable_snd))
    · simpa only [Function.comp_def, List.ofFn_succ] using
        (AdaptiveList.measurable_cons (0 : ℝ)).comp
          (measurable_fst.prodMk ((AdaptiveList.measurable_ofFn (n + 1)).comp
            (measurable_snd : Measurable (fun w : ℝ × (Fin (n + 1) → ℝ) => w.2))))
    · have ht : Measurable (fun w : ℝ × (Fin (n + 1) → ℝ) =>
          (w.1, fun i : Fin n => w.2 i.succ)) :=
        measurable_fst.prodMk (measurable_pi_iff.mpr (fun i =>
          (measurable_pi_apply i.succ).comp measurable_snd))
      have hh : Measurable (fun w : ℝ × (Fin (n + 1) → ℝ) => w.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      simpa only [Function.comp_def] using
        (AdaptiveList.measurable_cons (0 : ℝ)).comp (hh.prodMk (ih.comp ht))

lemma measurable_orderedInsert : Measurable (fun w : ℝ × List ℝ =>
    List.orderedInsert (· ≤ ·) w.1 w.2) := by
  let family : ℕ → ℝ × List ℝ → List ℝ := fun n w =>
    List.orderedInsert (· ≤ ·) w.1 (List.ofFn (fun i : Fin n => w.2[i.val]?.getD 0))
  apply ScalarNoisySearch.measurable_nat_selection _ (fun w : ℝ × List ℝ => w.2.length)
    (AdaptiveList.measurable_length.comp measurable_snd) family
  · intro n
    dsimp only [family]
    have ht : Measurable (fun w : ℝ × List ℝ =>
        (w.1, fun i : Fin n => w.2[i.val]?.getD 0)) :=
      measurable_fst.prodMk (measurable_pi_iff.mpr (fun i =>
        (AdaptiveList.measurable_getD i.val (0 : ℝ)).comp measurable_snd))
    simpa only [Function.comp_def] using (measurable_orderedInsert_ofFn n).comp ht
  · intro w
    dsimp [family]
    congr 1
    have he : (fun i : Fin w.2.length => w.2[i.val]?.getD 0) = w.2.get := by
      funext i
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    rw [he, List.ofFn_get]

lemma measurable_insertionSort : Measurable (List.insertionSort (· ≤ ·) : List ℝ → List ℝ) := by
  apply AdaptiveList.measurable_cases
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.insertionSort_cons]
    have ht : Measurable (fun x : Fin (n + 1) → ℝ => fun i : Fin n => x i.succ) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply i.succ)
    simpa only [Function.comp_def] using measurable_orderedInsert.comp
      ((measurable_pi_apply 0).prodMk (ih.comp ht))

lemma measurable_mergeSort : Measurable (fun l : List ℝ => l.mergeSort (· ≤ ·)) := by
  simpa only [List.mergeSort_eq_insertionSort] using measurable_insertionSort

lemma measurable_scalar_median : Measurable (fun l : List ℝ =>
    (l.mergeSort (· ≤ ·)).getD (l.length / 2) 0) := by
  apply ScalarNoisySearch.measurable_nat_selection _ (fun l : List ℝ => l.length / 2)
    (AdaptiveList.measurable_length.div_const 2)
    (fun n l => (l.mergeSort (· ≤ ·)).getD n 0)
  · intro n
    exact (AdaptiveList.measurable_getD n (0 : ℝ)).comp measurable_mergeSort
  · intro l
    rfl

lemma measurable_medianCenter (d : ℕ) : Measurable (medianCenter : List (Vector d) → Vector d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  have hmap := AdaptiveList.measurable_map (fun v : Vector d => v i)
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable
  simpa only [Function.comp_def, List.length_map] using measurable_scalar_median.comp hmap

end OracleTemplate.AdaptiveHeavyTailSimplex
