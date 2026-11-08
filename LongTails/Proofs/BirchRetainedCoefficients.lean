import LongTails.Proofs.BirchRetainedWork

namespace LongTails.Proofs.BirchRetainedCoefficients

open Finset
open LongTails.Proofs.BirchRetainedWork

lemma source_zero (history : ℕ → Finset ℕ) (q : ℕ) (β : ℕ → ℝ) (a : ℝ)
    (c : ℕ → ℝ) (hpast : ∀ n, history n ⊆ range n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n)
    (hrec : ∀ n, c n = (if q ∈ history n then a else 0) -
      ∑ j ∈ history n, β j * c j) :
    ∀ n, q ∉ history n → c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rw [hrec n, ite_eq_right hn]
      have hs : (∑ j ∈ history n, β j * c j) = 0 := by
        apply sum_eq_zero
        intro j hj
        rw [ih j (mem_range.mp (hpast n hj)) (fun hq => hn (hclosed n j hj hq))]
        ring
      simp [hs]

lemma source_nonnegative_cap (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (q : ℕ) (a : ℝ) (β scale c : ℕ → ℝ)
    (ha : 0 ≤ a) (hβ : ∀ n, 0 ≤ β n) (hscale : ∀ n, 1 ≤ scale n)
    (hp : ∀ n, 0 ≤ 1 - β n * scale n)
    (hpast : ∀ n, history n ⊆ range n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n)
    (hfrontier : ∀ n, frontier n ≤ n)
    (hprefix : ∀ n, range (frontier n) ⊆ history n)
    (hgate : ∀ n, 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hrec : ∀ n, c n = (if q ∈ history n then a else 0) -
      ∑ j ∈ history n, β j * c j) :
    ∀ n, 0 ≤ c n ∧ c n ≤ a := by
  classical
  have hz := source_zero history q β a c hpast hclosed hrec
  have hr : ∀ n, c n = if q ∈ history n then
      a - ∑ j ∈ history n, β j * c j else 0 := by
    intro n
    by_cases hq : q ∈ history n
    · simpa [hq] using hrec n
    · simpa [hq] using hz n hq
  have hb := depletion_bounds history frontier (q ∈ history ·) a β scale c
    ha hβ hscale hp hpast hfrontier hprefix hgate hr
  exact fun n => ⟨(hb n).2.1, (hb n).2.2.1⟩

lemma sum_source_births (s : Finset ℕ) (N : ℕ) (β : ℕ → ℝ) (hs : s ⊆ range N) :
    (∑ q ∈ range N, if q ∈ s then β q else 0) = ∑ q ∈ s, β q := by
  have he : (∑ q ∈ s, if q ∈ s then β q else 0) =
      ∑ q ∈ range N, if q ∈ s then β q else 0 := by
    apply sum_subset hs
    intro q _ hq
    simp [hq]
  rw [← he]
  exact sum_congr rfl (fun q hq => ite_eq_left hq)

lemma coefficient_mass (history : ℕ → Finset ℕ) (β initial : ℕ → ℝ)
    (source : ℕ → ℕ → ℝ) (hpast : ∀ n, history n ⊆ range n)
    (hi : ∀ n, initial n = 1 - ∑ j ∈ history n, β j * initial j)
    (hs : ∀ n q, source n q = (if q ∈ history n then β q else 0) -
      ∑ j ∈ history n, β j * source j q) :
    ∀ n N, n ≤ N → initial n + ∑ q ∈ range N, source n q = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro N hn
      have hsub : history n ⊆ range N := (hpast n).trans (range_mono hn)
      have hsource : (∑ q ∈ range N, source n q) =
          (∑ j ∈ history n, β j) -
            ∑ j ∈ history n, β j * ∑ q ∈ range N, source j q := by
        simp_rw [hs n]
        rw [sum_sub_distrib, sum_source_births (history n) N β hsub, sum_comm]
        simp_rw [mul_sum]
      have hmass : (∑ j ∈ history n, β j * (initial j + ∑ q ∈ range N, source j q)) =
          ∑ j ∈ history n, β j := by
        apply sum_congr rfl
        intro j hj
        rw [ih j (mem_range.mp (hpast n hj)) N (by
          have := mem_range.mp (hsub hj)
          omega), mul_one]
      simp_rw [mul_add, sum_add_distrib] at hmass
      rw [hi n, hsource]
      linarith

lemma sum_births_interchange (s : Finset ℕ) (cutoff : ℕ) (β : ℕ → ℝ) :
    (∑ q ∈ range cutoff, if q ∈ s then β q else 0) =
      ∑ j ∈ s, if j < cutoff then β j else 0 := by
  calc
    _ = ∑ q ∈ range cutoff, ∑ j ∈ s, if j = q then β j else 0 := by simp
    _ = ∑ j ∈ s, ∑ q ∈ range cutoff, if j = q then β j else 0 := sum_comm
    _ = _ := by simp

lemma old_source_recurrence (history : ℕ → Finset ℕ) (β initial : ℕ → ℝ)
    (source : ℕ → ℕ → ℝ) (cutoff : ℕ)
    (hi : ∀ n, initial n = 1 - ∑ j ∈ history n, β j * initial j)
    (hs : ∀ n q, source n q = (if q ∈ history n then β q else 0) -
      ∑ j ∈ history n, β j * source j q) (n : ℕ) :
    initial n + ∑ q ∈ range cutoff, source n q =
      1 + (∑ j ∈ history n, if j < cutoff then β j else 0) -
        ∑ j ∈ history n, β j * (initial j + ∑ q ∈ range cutoff, source j q) := by
  rw [hi n]
  simp_rw [hs n]
  rw [sum_sub_distrib, sum_comm, sum_births_interchange]
  simp_rw [mul_add, mul_sum, sum_add_distrib]
  ring

lemma masked_old_recurrence (history : ℕ → Finset ℕ) (β c : ℕ → ℝ)
    (cutoff : ℕ) (hbefore : ∀ n, n < cutoff → c n = 1)
    (hrec : ∀ n, c n = 1 + (∑ j ∈ history n, if j < cutoff then β j else 0) -
      ∑ j ∈ history n, β j * c j) :
    ∀ n, (if cutoff ≤ n then c n else 0) = if cutoff ≤ n then
      1 - ∑ j ∈ history n, β j * (if cutoff ≤ j then c j else 0) else 0 := by
  intro n
  by_cases hn : cutoff ≤ n
  · simp only [hn, ite_true]
    have he (j : ℕ) : (if j < cutoff then β j else 0) - β j * c j =
        -β j * (if cutoff ≤ j then c j else 0) := by
      by_cases hj : j < cutoff
      · simp [hj, hbefore j hj, show ¬cutoff ≤ j by omega]
      · simp [hj, show cutoff ≤ j by omega]
    rw [hrec n, add_sub_assoc, ← sum_sub_distrib]
    simp_rw [he, neg_mul, sum_neg_distrib]
    ring
  · simp [hn]

lemma old_source_tail (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (β scale initial : ℕ → ℝ) (source : ℕ → ℕ → ℝ)
    (hβ : ∀ n, 0 ≤ β n) (hscale : ∀ n, 1 ≤ scale n)
    (hp : ∀ n, 0 ≤ 1 - β n * scale n)
    (hpast : ∀ n, history n ⊆ range n)
    (hfrontier : ∀ n, frontier n ≤ n)
    (hprefix : ∀ n, range (frontier n) ⊆ history n)
    (hgate : ∀ n, 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hi : ∀ n, initial n = 1 - ∑ j ∈ history n, β j * initial j)
    (hs : ∀ n q, source n q = (if q ∈ history n then β q else 0) -
      ∑ j ∈ history n, β j * source j q) (cutoff n : ℕ) (hn : cutoff ≤ n) :
    initial n + ∑ q ∈ range cutoff, source n q ≤ scale n * survival β cutoff n := by
  let c := fun j => initial j + ∑ q ∈ range cutoff, source j q
  have hm := coefficient_mass history β initial source hpast hi hs
  have hr := masked_old_recurrence history β c cutoff
    (fun j hj => hm j cutoff hj.le)
    (old_source_recurrence history β initial source cutoff hi hs)
  have ht := masked_tail history frontier 1 β scale
    (fun j => if cutoff ≤ j then c j else 0) cutoff (by norm_num)
    hβ hscale hp hpast hfrontier hprefix hgate hr n hn
  have he := survival_range β cutoff (n - cutoff)
  rw [Nat.add_sub_of_le hn] at he
  simpa [hn, c, he] using ht

lemma initial_vanishes_after_reset (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (β scale initial : ℕ → ℝ)
    (hβ : ∀ n, 0 ≤ β n) (hscale : ∀ n, 1 ≤ scale n)
    (hp : ∀ n, 0 ≤ 1 - β n * scale n)
    (hpast : ∀ n, history n ⊆ range n)
    (hfrontier : ∀ n, frontier n ≤ n)
    (hprefix : ∀ n, range (frontier n) ⊆ history n)
    (hgate : ∀ n, 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hi : ∀ n, initial n = 1 - ∑ j ∈ history n, β j * initial j)
    (hreset : β 0 = 1) :
    (∀ n, 0 < n → initial n = 0) ∧ (∀ n, (1 - β n) * initial n = 0) := by
  have hb := depletion_bounds history frontier (fun _ => True) 1 β scale initial
    (by norm_num) hβ hscale hp hpast hfrontier hprefix hgate (by simpa using hi)
  have hempty : history 0 = ∅ := subset_empty.mp (by simpa using hpast 0)
  have hzero : initial 0 = 1 := by simpa [hempty] using hi 0
  have hu : residual 1 β initial 1 = 0 := by
    rw [show 1 = 0 + 1 from rfl, residual_succ, residual_zero, hreset, hzero]
    ring
  have hanti := residual_antitone 1 β initial hβ (fun n => (hb n).2.1)
  have hz (n : ℕ) (hn : 0 < n) : initial n = 0 := by
    have hres : residual 1 β initial n = 0 :=
      le_antisymm (by simpa [hu] using hanti (show 1 ≤ n by omega)) (hb n).1
    apply le_antisymm _ (hb n).2.1
    simpa [hres] using (hb n).2.2.2.1
  refine ⟨hz, fun n => ?_⟩
  cases n with
  | zero => simp [hreset]
  | succ n => rw [hz (n + 1) (by omega), mul_zero]

def estimatorInitial (β initial : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - β n) * initial n

def estimatorSource (β : ℕ → ℝ) (source : ℕ → ℕ → ℝ) (n q : ℕ) : ℝ :=
  (1 - β n) * source n q + if q = n then β n else 0

lemma estimator_mass (β initial : ℕ → ℝ) (source : ℕ → ℕ → ℝ)
    (n N : ℕ) (hn : n < N) (hm : initial n + ∑ q ∈ range N, source n q = 1) :
    estimatorInitial β initial n + ∑ q ∈ range N, estimatorSource β source n q = 1 := by
  simp only [estimatorInitial, estimatorSource, sum_add_distrib, ← mul_sum]
  simp only [sum_ite_eq', mem_range, hn, ite_true]
  rw [← add_assoc, ← mul_add, hm]
  ring

lemma estimator_source_cap (β : ℕ → ℝ) (source : ℕ → ℕ → ℝ)
    (hβ : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n ≤ 1) (n q : ℕ)
    (hnonneg : 0 ≤ source n q) (hcap : source n q ≤ β q) (hself : source n n = 0) :
    0 ≤ estimatorSource β source n q ∧ estimatorSource β source n q ≤ β q := by
  dsimp [estimatorSource]
  by_cases hq : q = n
  · subst q
    simp [hself, hβ n]
  · simp only [hq, ite_false, add_zero]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr (hβ1 n)) hnonneg
    · nlinarith [mul_nonneg (hβ n) hnonneg]

lemma estimator_old_tail (β scale initial : ℕ → ℝ) (source : ℕ → ℕ → ℝ)
    (n cutoff : ℕ) (hn : cutoff ≤ n) (hβ1 : β n ≤ 1)
    (htail : initial n + ∑ q ∈ range cutoff, source n q ≤ scale n * survival β cutoff n) :
    estimatorInitial β initial n + ∑ q ∈ range cutoff, estimatorSource β source n q ≤
      scale n * survival β cutoff (n + 1) := by
  have he : estimatorInitial β initial n +
      ∑ q ∈ range cutoff, estimatorSource β source n q =
      (1 - β n) * (initial n + ∑ q ∈ range cutoff, source n q) := by
    simp [estimatorInitial, estimatorSource, sum_add_distrib, ← mul_sum,
      show ¬n < cutoff by omega, mul_add]
  rw [he, survival_succ_right β cutoff n hn]
  have hm := mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr hβ1)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hm

lemma block_square_mass {ι : Type*} (s : Finset ι) (mass size : ι → ℝ) (B : ℝ)
    (hsize : ∀ q ∈ s, 0 < size q)
    (hm : ∀ q ∈ s, 0 ≤ mass q) (hcap : ∀ q ∈ s, mass q ≤ size q / B)
    (hmass : ∑ q ∈ s, mass q = 1) :
    (∑ q ∈ s, mass q ^ 2 / size q) ≤ 1 / B := by
  calc
    _ ≤ ∑ q ∈ s, mass q / B := by
      apply sum_le_sum
      intro q hq
      apply (div_le_iff₀ (hsize q hq)).2
      have hc := mul_le_mul_of_nonneg_left (hcap q hq) (hm q hq)
      calc
        mass q ^ 2 = mass q * mass q := by ring
        _ ≤ mass q * (size q / B) := hc
        _ = mass q / B * size q := by ring
    _ = (∑ q ∈ s, mass q) / B := (sum_div _ _ _).symm
    _ = 1 / B := by rw [hmass]

noncomputable def initialCoefficient (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (β : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ j : history n, β j.val * initialCoefficient history hpast β j.val
termination_by n
decreasing_by exact mem_range.mp (hpast n j.property)

noncomputable def sourceCoefficient (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (β : ℕ → ℝ) (q n : ℕ) : ℝ :=
  (if q ∈ history n then β q else 0) -
    ∑ j : history n, β j.val * sourceCoefficient history hpast β q j.val
termination_by n
decreasing_by exact mem_range.mp (hpast n j.property)

lemma initialCoefficient_rec (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (β : ℕ → ℝ) (n : ℕ) :
    initialCoefficient history hpast β n =
      1 - ∑ j ∈ history n, β j * initialCoefficient history hpast β j := by
  rw [initialCoefficient]
  congr 1
  exact sum_coe_sort (s := history n)
    (f := fun j => β j * initialCoefficient history hpast β j)

lemma sourceCoefficient_rec (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (β : ℕ → ℝ) (q n : ℕ) :
    sourceCoefficient history hpast β q n =
      (if q ∈ history n then β q else 0) -
        ∑ j ∈ history n, β j * sourceCoefficient history hpast β q j := by
  rw [sourceCoefficient]
  congr 1
  exact sum_coe_sort (s := history n)
    (f := fun j => β j * sourceCoefficient history hpast β q j)

noncomputable def sourceWeight (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (β : ℕ → ℝ) (n q : ℕ) : ℝ :=
  estimatorSource β (fun j q => sourceCoefficient history hpast β q j) n q

lemma weight_bounds (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (β scale : ℕ → ℝ) (hpast : ∀ n, history n ⊆ range n)
    (hβ : ∀ n, 0 ≤ β n) (hscale : ∀ n, 1 ≤ scale n)
    (hp : ∀ n, 0 ≤ 1 - β n * scale n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n)
    (hfrontier : ∀ n, frontier n ≤ n)
    (hprefix : ∀ n, range (frontier n) ⊆ history n)
    (hgate : ∀ n, 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hreset : β 0 = 1) :
    (∀ n q, 0 ≤ sourceWeight history hpast β n q ∧ sourceWeight history hpast β n q ≤ β q) ∧
    (∀ n N, n < N → ∑ q ∈ range N, sourceWeight history hpast β n q = 1) ∧
    (∀ n cutoff, cutoff ≤ n → (∑ q ∈ range cutoff, sourceWeight history hpast β n q) ≤
      scale n * survival β cutoff (n + 1)) := by
  let initial := initialCoefficient history hpast β
  let source := fun n q => sourceCoefficient history hpast β q n
  have hi : ∀ n, initial n = 1 - ∑ j ∈ history n, β j * initial j :=
    initialCoefficient_rec history hpast β
  have hs : ∀ n q, source n q = (if q ∈ history n then β q else 0) -
      ∑ j ∈ history n, β j * source j q :=
    fun n q => sourceCoefficient_rec history hpast β q n
  have hβ1 : ∀ j, β j ≤ 1 := by
    intro j
    nlinarith [hp j, mul_le_mul_of_nonneg_left (hscale j) (hβ j)]
  have hz := (initial_vanishes_after_reset history frontier β scale initial
    hβ hscale hp hpast hfrontier hprefix hgate hi hreset).2
  have hsb (n q : ℕ) := source_nonnegative_cap history frontier q (β q) β scale
    (fun j => source j q) (hβ q) hβ hscale hp hpast hclosed hfrontier hprefix hgate
      (fun j => hs j q) n
  have hmass := coefficient_mass history β initial source hpast hi hs
  refine ⟨?_, ?_, ?_⟩
  · intro n q
    have hself : source n n = 0 :=
      source_zero history n β (β n) (fun j => source j n) hpast hclosed (fun j => hs j n) n
        (fun hn => (Nat.lt_irrefl _) (mem_range.mp (hpast n hn)))
    exact estimator_source_cap β source hβ hβ1 n q (hsb n q).1 (hsb n q).2 hself
  · intro n N hn
    have hm := estimator_mass β initial source n N hn (hmass n N hn.le)
    simpa only [sourceWeight, source, estimatorInitial, hz n, zero_add] using hm
  · intro n cutoff hn
    have ht := old_source_tail history frontier β scale initial source
      hβ hscale hp hpast hfrontier hprefix hgate hi hs cutoff n hn
    have he := estimator_old_tail β scale initial source n cutoff hn (hβ1 n) ht
    simpa only [sourceWeight, source, estimatorInitial, hz n, zero_add] using he

end LongTails.Proofs.BirchRetainedCoefficients
