import LongTailsOnline.Proofs.TaskAllocationOracle

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma fold_min_bounds {k : ℕ} (w : List (Worker k)) (C : Counts k) {B : ℕ}
    (hB : 0 < B) (hC : ∀ i ∈ w, 0 < C i) :
    0 < w.foldl (fun c i => min c (C i)) B ∧
      w.foldl (fun c i => min c (C i)) B ≤ B ∧
      ∀ i ∈ w, w.foldl (fun c j => min c (C j)) B ≤ C i := by
  induction w generalizing B with
  | nil => simp [hB]
  | cons i w ih =>
    have hi := hC i (by simp)
    have hr := ih (lt_min hB hi) (fun j hj => hC j (by simp [hj]))
    simp only [List.foldl_cons]
    refine ⟨hr.1, hr.2.1.trans (min_le_left _ _), ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr.2.1.trans (min_le_right _ _)
    · exact hr.2.2 j hj

lemma indicator_sum_bound {k : ℕ} (w : List (Worker k)) (d : ℕ) :
    (∑ i : Worker k, if i ∈ w then d else 0) ≤ w.length * d := by
  have heq : Finset.univ.filter (fun i : Worker k => i ∈ w) = w.toFinset := by
    ext i
    simp
  calc
    _ = w.toFinset.card * d := by rw [← Finset.sum_filter, heq]; simp
    _ ≤ _ := Nat.mul_le_mul_right _ (List.toFinset_card_le w)

lemma bucket_row_feasible {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) (h : ℕ) {e : Counts k}
    (he : e ∈ bucketSchedule B q C h) :
    (∀ i, e i ≤ C i) ∧ ∑ i, e i ≤ B := by
  let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let m := w.length
  let base := 2 ^ h
  let cmin := w.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / m))))
  let chunk := max 1 (B / d)
  have hwC : ∀ i ∈ w, 0 < C i := by
    intro i hi
    have hiq : 0 < q i ∧ Nat.log2 (q i) = h := by
      simpa only [w, List.mem_filter, decide_eq_true_eq,
        List.mem_finRange, true_and] using hi
    exact hC i hiq.1
  have hc := fold_min_bounds w C hB hwC
  have hdpos : 0 < d := by dsimp only [d]; omega
  have hdle : d ≤ cmin := by
    have hbase : 0 < base := by dsimp only [base]; positivity
    have hmin : 1 ≤ min cmin (min (2 * base) (max 1 (B / m))) := by
      exact le_min hc.1 (le_min (by omega) (le_max_left _ _))
    dsimp only [d]
    rw [max_eq_right hmin]
    exact min_le_left _ _
  have hdB : d ≤ B := hdle.trans hc.2.1
  have hchunk : chunk = B / d := max_eq_right ((Nat.le_div_iff_mul_le hdpos).mpr
    (by simpa using hdB))
  change e ∈ (if m = 0 then [] else
    (List.range ((2 * base + d - 1) / d)).flatMap (fun cycle =>
      (List.range ((m + chunk - 1) / chunk)).map (fun j =>
        fun i => if i ∈ (w.drop (j * chunk)).take chunk then
          min d (2 * base - cycle * d) else 0))) at he
  split_ifs at he with hm
  · simp at he
  · obtain ⟨cycle, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    let v := (w.drop (j * chunk)).take chunk
    have hv (i : Worker k) (hi : i ∈ v) : i ∈ w :=
      List.mem_of_mem_drop (List.mem_of_mem_take hi)
    refine ⟨?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · exact (min_le_left _ _).trans (hdle.trans (hc.2.2 i (hv i hi)))
      · exact Nat.zero_le _
    · calc
        _ ≤ ∑ i : Worker k, if i ∈ v then d else 0 := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs <;> omega
        _ ≤ v.length * d := indicator_sum_bound v d
        _ ≤ chunk * d := Nat.mul_le_mul_right d (List.length_take_le _ _)
        _ ≤ B := by rw [hchunk]; exact Nat.div_mul_le_self B d

lemma schedule_row_feasible {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) {e : Counts k}
    (he : e ∈ schedule B q C) : (∀ i, e i ≤ C i) ∧ ∑ i, e i ≤ B := by
  obtain ⟨h, _, he⟩ := List.mem_flatMap.mp he
  exact bucket_row_feasible hB q C hC h he

lemma fill_spec {k B : ℕ} {b : Allocation k B} {C e : Counts k}
    (hb : ∀ i, (b.val i).val ≤ C i) (he : ∀ i, e i ≤ C i)
    (heB : ∑ i, e i ≤ B) :
    ∀ i, e i ≤ ((fill b C e).val i).val ∧
      ((fill b C e).val i).val ≤ C i ∧
      ((fill b C e).val i).val - e i ≤ (b.val i).val := by
  obtain ⟨r, hr, hC, hsum⟩ := residual_allocation_exists hb he heB
  have hcount (i : Worker k) : e i + r i < B + 1 := by
    have hi : e i + r i ≤ ∑ j, (e j + r j) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (e j + r j)) (Finset.mem_univ i)
    omega
  have hex : ∃ a : Allocation k B, ∀ i, e i ≤ (a.val i).val ∧
      (a.val i).val ≤ C i ∧ (a.val i).val - e i ≤ (b.val i).val := by
    refine ⟨⟨fun i => ⟨e i + r i, hcount i⟩, hsum⟩, ?_⟩
    intro i
    exact ⟨Nat.le_add_right _ _, hC i, by simpa using hr i⟩
  unfold fill
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

lemma fill_loss_le {k B : ℕ} {b : Allocation k B} {C e : Counts k}
    {u : Worker k → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hb : ∀ i, (b.val i).val ≤ C i) (he : ∀ i, e i ≤ C i)
    (heB : ∑ i, e i ≤ B) :
    loss u (fill b C e) ≤ loss u b +
      Finset.univ.sup' Finset.univ_nonempty (fun i => (e i : ℝ) * u i) := by
  apply (loss_le_iff _ _ _).mpr
  intro i
  have hfill := fill_spec hb he heB i
  have hcount : ((fill b C e).val i).val ≤ e i + (b.val i).val := by omega
  have hcount' : (((fill b C e).val i).val : ℝ) ≤ e i + (b.val i).val := by
    exact_mod_cast hcount
  calc
    _ ≤ ((e i : ℝ) + (b.val i).val) * u i :=
      mul_le_mul_of_nonneg_right hcount' (hu i)
    _ = ((b.val i).val : ℝ) * u i + (e i : ℝ) * u i := by ring
    _ ≤ _ := add_le_add (component_le_loss u b i)
      (Finset.le_sup' (fun i => (e i : ℝ) * u i) (Finset.mem_univ i))

lemma ceil_div_cover (m : ℕ) {d : ℕ} (hd : 0 < d) :
    m ≤ (m + d - 1) / d * d := by
  have hm := Nat.mod_lt (m + d - 1) hd
  have heq := Nat.div_add_mod (m + d - 1) d
  have hcomm : d * ((m + d - 1) / d) = (m + d - 1) / d * d := Nat.mul_comm _ _
  omega

lemma mem_chunk_iff {k : ℕ} (w : List (Worker k)) (hw : w.Nodup)
    {i : Worker k} (hi : i ∈ w) (j c : ℕ) :
    i ∈ (w.drop (j * c)).take c ↔ j * c ≤ w.idxOf i ∧ w.idxOf i < (j + 1) * c := by
  have hidx := List.idxOf_lt_length_iff.mpr hi
  constructor
  · intro hmem
    obtain ⟨r, hr, heq⟩ := List.mem_iff_getElem.mp hmem
    have hr' : r < c ∧ r < w.length - j * c := by
      simpa only [List.length_take, List.length_drop, lt_min_iff] using hr
    have hlen : j * c + r < w.length := by omega
    have heq' : w[j * c + r] = w[w.idxOf i] := by
      rw [List.getElem_idxOf hidx]
      simpa only [List.getElem_take, List.getElem_drop] using heq
    have hind := hw.getElem_inj_iff.mp heq'
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    rw [Nat.add_mul, Nat.one_mul] at hhi
    have hr : w.idxOf i - j * c < ((w.drop (j * c)).take c).length := by
      simp only [List.length_take, List.length_drop, lt_min_iff]
      constructor <;> omega
    apply List.mem_iff_getElem.mpr
    refine ⟨w.idxOf i - j * c, hr, ?_⟩
    simp only [List.getElem_take, List.getElem_drop]
    have heq : j * c + (w.idxOf i - j * c) = w.idxOf i := by omega
    simp only [heq, List.getElem_idxOf hidx]

lemma chunk_sum {k : ℕ} (w : List (Worker k)) (hw : w.Nodup)
    {c : ℕ} (hc : 0 < c) (i : Worker k) (v : ℕ) :
    (∑ j ∈ Finset.range ((w.length + c - 1) / c),
      if i ∈ (w.drop (j * c)).take c then v else 0) = if i ∈ w then v else 0 := by
  by_cases hi : i ∈ w
  · rw [ite_eq_left hi]
    have hidx := List.idxOf_lt_length_iff.mpr hi
    have hj : w.idxOf i / c < (w.length + c - 1) / c := by
      apply (Nat.div_lt_iff_lt_mul hc).mpr
      exact hidx.trans_le (ceil_div_cover w.length hc)
    have hm (j : ℕ) : i ∈ (w.drop (j * c)).take c ↔ w.idxOf i / c = j := by
      rw [mem_chunk_iff w hw hi]
      constructor
      · rintro ⟨hlo, hhi⟩
        have hl := (Nat.le_div_iff_mul_le hc).mpr hlo
        have hh := (Nat.div_lt_iff_lt_mul hc).mpr hhi
        omega
      · intro heq
        rw [← heq]
        exact ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul hc).mp (by omega)⟩
    rw [Finset.sum_eq_single (w.idxOf i / c)]
    · rw [ite_eq_left ((hm _).mpr rfl)]
    · intro j _ hj
      rw [ite_eq_right (by simpa only [hm] using Ne.symm hj)]
    · intro hj'
      exact (hj' (Finset.mem_range.mpr hj)).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (fun h => hi (List.mem_of_mem_drop (List.mem_of_mem_take h)))]

lemma capped_cycles_sum (M : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ r ∈ Finset.range ((M + d - 1) / d), min d (M - r * d)) = M := by
  have hsum (n : ℕ) : (∑ r ∈ Finset.range n, min d (M - r * d)) = M - (M - n * d) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Nat.succ_mul]
      omega
  rw [hsum, Nat.sub_eq_zero_of_le (ceil_div_cover M hd), Nat.sub_zero]

lemma list_range_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  rw [← List.sum_toFinset f List.nodup_range]
  have heq : (List.range n).toFinset = Finset.range n := by
    ext j
    simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
  rw [heq]

lemma list_flatMap_sum {α M : Type*} [AddMonoid M] (w : List α) (f : α → List M) :
    (w.flatMap f).sum = (w.map (fun i => (f i).sum)).sum := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons,
      List.sum_cons, ih]

lemma bucket_total {k B : ℕ} (q C : Counts k) (h : ℕ) (i : Worker k) :
    ((bucketSchedule B q C h).map (fun e => e i)).sum =
      if 0 < q i ∧ Nat.log2 (q i) = h then 2 * 2 ^ h else 0 := by
  let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let m := w.length
  let base := 2 ^ h
  let cmin := w.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / m))))
  let chunk := max 1 (B / d)
  have hw : w.Nodup := (List.nodup_finRange _).filter _
  have hm (i : Worker k) : i ∈ w ↔ 0 < q i ∧ Nat.log2 (q i) = h := by simp [w]
  have hd : 0 < d := by dsimp only [d]; omega
  have hchunk : 0 < chunk := by dsimp only [chunk]; omega
  change ((if m = 0 then [] else
    (List.range ((2 * base + d - 1) / d)).flatMap (fun cycle =>
      (List.range ((m + chunk - 1) / chunk)).map (fun j =>
        fun i => if i ∈ (w.drop (j * chunk)).take chunk then
          min d (2 * base - cycle * d) else 0))).map (fun e => e i)).sum = _
  by_cases hm0 : m = 0
  · have hnot : i ∉ w := by
      intro hi
      have : 0 < w.length := List.length_pos_of_mem hi
      omega
    rw [ite_eq_left hm0]
    have hnot' : ¬(0 < q i ∧ Nat.log2 (q i) = h) := fun hi => hnot ((hm i).mpr hi)
    simp only [List.map_nil, List.sum_nil, ite_eq_right hnot']
  · rw [ite_eq_right hm0]
    calc
      _ = ∑ cycle ∈ Finset.range ((2 * base + d - 1) / d),
          ∑ j ∈ Finset.range ((m + chunk - 1) / chunk),
            if i ∈ (w.drop (j * chunk)).take chunk then
              min d (2 * base - cycle * d) else 0 := by
        simp only [List.map_flatMap, list_flatMap_sum, List.map_map, Function.comp_def,
          list_range_sum]
      _ = ∑ cycle ∈ Finset.range ((2 * base + d - 1) / d),
          if i ∈ w then min d (2 * base - cycle * d) else 0 := by
        apply Finset.sum_congr rfl
        intro cycle _
        exact chunk_sum w hw hchunk i _
      _ = if i ∈ w then 2 * base else 0 := by
        by_cases hi : i ∈ w
        · simp only [ite_eq_left hi]
          exact capped_cycles_sum _ hd
        · simp only [ite_eq_right hi, Finset.sum_const_zero]
      _ = _ := by simp only [hm i]; rfl

lemma schedule_total {k B : ℕ} (q C : Counts k) (i : Worker k) :
    ((schedule B q C).map (fun e => e i)).sum =
      if q i = 0 then 0 else 2 * 2 ^ Nat.log2 (q i) := by
  unfold schedule
  simp only [List.map_flatMap, list_flatMap_sum, bucket_total, list_range_sum]
  by_cases hi : q i = 0
  · simp [hi]
  · rw [ite_eq_right hi]
    have hi0 : 0 < q i := Nat.pos_of_ne_zero hi
    have hlog : Nat.log2 (q i) < 1 + Finset.univ.sup (fun i => Nat.log2 (q i)) := by
      have := Finset.le_sup (f := fun i => Nat.log2 (q i)) (Finset.mem_univ i)
      omega
    rw [Finset.sum_eq_single (Nat.log2 (q i))]
    · simp [hi0]
    · intro j _ hj
      simp only [hi0, true_and, ite_eq_right (Ne.symm hj)]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hlog)).elim

lemma schedule_quota_bounds {k B : ℕ} (q C : Counts k) (i : Worker k) :
    q i ≤ ((schedule B q C).map (fun e => e i)).sum ∧
      ((schedule B q C).map (fun e => e i)).sum ≤ 2 * q i := by
  rw [schedule_total]
  split_ifs with hi
  · simp [hi]
  · have hlow := Nat.log2_self_le hi
    have hhigh := Nat.lt_log2_self (n := q i)
    rw [pow_succ] at hhigh
    constructor <;> omega

lemma ceil_div_upper (M d : ℕ) : (M + d - 1) / d * d ≤ M + d :=
  (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)

lemma ceil_div_eq_one {m c : ℕ} (hm : 0 < m) (hmc : m ≤ c) :
    (m + c - 1) / c = 1 := by
  have hc : 0 < c := hm.trans_le hmc
  have hl : 1 ≤ (m + c - 1) / c :=
    (Nat.le_div_iff_mul_le hc).mpr (by omega)
  have hu : (m + c - 1) / c < 2 :=
    (Nat.div_lt_iff_lt_mul hc).mpr (by omega)
  omega

lemma grid_work_bound {B M m cmin : ℕ} (hB : 0 < B) (hM : 0 < M)
    (hm : 0 < m) (hc : 0 < cmin) (hcB : cmin ≤ B) :
    let d := max 1 (min cmin (min M (max 1 (B / m))))
    let chunk := max 1 (B / d)
    let rounds := (M + d - 1) / d * ((m + chunk - 1) / chunk)
    rounds * d * B ≤ 2 * M * (B + m) := by
  dsimp only
  let d := max 1 (min cmin (min M (max 1 (B / m))))
  let chunk := max 1 (B / d)
  change ((M + d - 1) / d * ((m + chunk - 1) / chunk)) * d * B ≤ _
  have hdpos : 0 < d := by dsimp only [d]; omega
  have hd : d = min cmin (min M (max 1 (B / m))) := by
    apply max_eq_right
    exact le_min hc (le_min hM (le_max_left _ _))
  have hdB : d ≤ B := by rw [hd]; exact (min_le_left _ _).trans hcB
  have hdM : d ≤ M := by rw [hd]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hchunk : chunk = B / d :=
    max_eq_right ((Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdB))
  by_cases hmB : m ≤ B
  · have hdiv : 1 ≤ B / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hmB)
    have hdm : d ≤ B / m := by
      rw [hd, max_eq_right hdiv]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hmc : m ≤ chunk := by
      rw [hchunk]
      apply (Nat.le_div_iff_mul_le hdpos).mpr
      have hh := (Nat.le_div_iff_mul_le hm).mp hdm
      nlinarith
    rw [ceil_div_eq_one hm hmc, Nat.mul_one]
    have hu := ceil_div_upper M d
    have hround : (M + d - 1) / d * d ≤ 2 * M := by omega
    exact (Nat.mul_le_mul_right B hround).trans (by nlinarith)
  · have hlt : B < m := lt_of_not_ge hmB
    have hd1 : d = 1 := by
      dsimp only [d]
      rw [Nat.div_eq_of_lt hlt]
      simp
    have hchunkB : chunk = B := by rw [hchunk, hd1, Nat.div_one]
    rw [hd1, hchunkB]
    simp only [Nat.add_sub_cancel, Nat.div_one, Nat.mul_one]
    have hu := ceil_div_upper m B
    nlinarith

lemma bucket_length {k B : ℕ} (q C : Counts k) (h : ℕ) :
    let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
    let base := 2 ^ h
    let cmin := w.foldl (fun c i => min c (C i)) B
    let d := max 1 (min cmin (min (2 * base) (max 1 (B / w.length))))
    let chunk := max 1 (B / d)
    (bucketSchedule B q C h).length =
      if w.length = 0 then 0 else
        ((2 * base + d - 1) / d) * ((w.length + chunk - 1) / chunk) := by
  unfold bucketSchedule
  dsimp only
  split_ifs <;> simp [List.length_flatMap, List.length_map, List.length_range,
    List.map_const', List.sum_replicate]

lemma grid_round_bound {B M m cmin : ℕ} (hB : 0 < B) (hM : 0 < M)
    (hm : 0 < m) (hc : 0 < cmin) (hcB : cmin ≤ B) {A : ℝ} (hA : 0 ≤ A)
    (hMA : (M : ℝ) ≤ 2 * A * cmin) :
    let d := max 1 (min cmin (min M (max 1 (B / m))))
    let chunk := max 1 (B / d)
    let rounds := (M + d - 1) / d * ((m + chunk - 1) / chunk)
    (rounds : ℝ) ≤ 2 * A + 2 + 2 * M * m / B := by
  dsimp only
  let d := max 1 (min cmin (min M (max 1 (B / m))))
  let chunk := max 1 (B / d)
  change (((M + d - 1) / d * ((m + chunk - 1) / chunk) : ℕ) : ℝ) ≤ _
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hdpos : 0 < d := by dsimp only [d]; omega
  have hd : d = min cmin (min M (max 1 (B / m))) := by
    apply max_eq_right
    exact le_min hc (le_min hM (le_max_left _ _))
  have hdB : d ≤ B := by rw [hd]; exact (min_le_left _ _).trans hcB
  have hchunk : chunk = B / d :=
    max_eq_right ((Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hdB))
  by_cases hmB : m ≤ B
  · have hdiv : 1 ≤ B / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hmB)
    have hd' : d = min cmin (min M (B / m)) := by rw [hd, max_eq_right hdiv]
    have hdm : d ≤ B / m := by
      rw [hd']
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hdb : d * m ≤ B := (Nat.le_div_iff_mul_le hm).mp hdm
    have hmc : m ≤ chunk := by
      rw [hchunk]
      exact (Nat.le_div_iff_mul_le hdpos).mpr (by nlinarith)
    rw [ceil_div_eq_one hm hmc, Nat.mul_one]
    by_cases hcd : cmin ≤ min M (B / m)
    · have hdC : d = cmin := by rw [hd', min_eq_left hcd]
      rw [hdC]
      have hu : (((M + cmin - 1) / cmin : ℕ) : ℝ) * cmin ≤ (M : ℝ) + cmin := by
        exact_mod_cast ceil_div_upper M cmin
      have hr : (((M + cmin - 1) / cmin : ℕ) : ℝ) ≤ 2 * A + 1 := by
        apply le_of_mul_le_mul_right (a0 := (by exact_mod_cast hc : (0 : ℝ) < cmin))
        nlinarith
      have hp : 0 ≤ 2 * (M : ℝ) * m / B := by positivity
      linarith
    · have hdrest : d = min M (B / m) := by rw [hd', min_eq_right (le_of_not_ge hcd)]
      by_cases hMd : M ≤ B / m
      · have hdM : d = M := by rw [hdrest, min_eq_left hMd]
        rw [hdM]
        have heq : (M + M - 1) / M = 1 := ceil_div_eq_one hM le_rfl
        rw [heq, Nat.cast_one]
        have hp : 0 ≤ 2 * (M : ℝ) * m / B := by positivity
        linarith
      · have hdf : d = B / m := by rw [hdrest, min_eq_right (le_of_not_ge hMd)]
        have hBd : B ≤ 2 * d * m := by
          have hh : B < (B / m + 1) * m :=
            (Nat.div_lt_iff_lt_mul hm).mp (by omega)
          rw [← hdf] at hh
          nlinarith
        have hu := ceil_div_upper M d
        have hroundB : (M + d - 1) / d * B ≤ 2 * M * m + 2 * B := by
          have hh := Nat.mul_le_mul_left ((M + d - 1) / d) hBd
          have hh' := Nat.mul_le_mul_right (2 * m) hu
          nlinarith
        have hrB : (((M + d - 1) / d : ℕ) : ℝ) * B ≤
            2 * (M : ℝ) * m + 2 * B := by exact_mod_cast hroundB
        have hr : (((M + d - 1) / d : ℕ) : ℝ) ≤ 2 + 2 * M * m / B := by
          apply le_of_mul_le_mul_right (a0 := hBr)
          calc
            _ ≤ 2 * (M : ℝ) * m + 2 * B := hrB
            _ = (2 + 2 * (M : ℝ) * m / B) * B := by field_simp; ring
        linarith
  · have hlt : B < m := lt_of_not_ge hmB
    have hd1 : d = 1 := by
      dsimp only [d]
      rw [Nat.div_eq_of_lt hlt]
      simp
    have hchunkB : chunk = B := by rw [hchunk, hd1, Nat.div_one]
    rw [hd1, hchunkB]
    simp only [Nat.add_sub_cancel, Nat.div_one]
    have hu := ceil_div_upper m B
    have hroundB : M * ((m + B - 1) / B) * B ≤ 2 * M * m := by nlinarith
    have hrB : ((M * ((m + B - 1) / B) : ℕ) : ℝ) * B ≤ 2 * (M : ℝ) * m := by
      exact_mod_cast hroundB
    have hr : ((M * ((m + B - 1) / B) : ℕ) : ℝ) ≤ 2 * M * m / B :=
      (le_div_iff₀ hBr).mpr hrB
    linarith

lemma fold_min_product_lower {k : ℕ} (w : List (Worker k)) (C : Counts k)
    {r A : ℝ} {B : ℕ} (hB : r ≤ A * B) (hC : ∀ i ∈ w, r ≤ A * C i) :
    r ≤ A * w.foldl (fun c i => min c (C i)) B := by
  induction w generalizing B with
  | nil => exact hB
  | cons i w ih =>
    simp only [List.foldl_cons]
    apply ih _ (fun j hj => hC j (by simp [hj]))
    by_cases hi : B ≤ C i
    · simpa only [min_eq_left hi] using hB
    · simpa only [min_eq_right (le_of_not_ge hi)] using hC i (by simp)

lemma list_worker_sum_le {k : ℕ} (w : List (Worker k)) (hw : w.Nodup) (q : Counts k) :
    (w.map q).sum ≤ ∑ i, q i := by
  rw [← List.sum_toFinset q hw]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma bucket_round_bound {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) (hCB : ∀ i, C i ≤ B) {A : ℝ} (hA : 0 ≤ A)
    (hqA : ∀ i, (q i : ℝ) ≤ A * C i) (h : ℕ) :
    ((bucketSchedule B q C h).length : ℝ) ≤
      4 * (∑ i, (q i : ℝ)) / B + 2 * A + 2 := by
  let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let m := w.length
  let base := 2 ^ h
  let cmin := w.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / m))))
  let chunk := max 1 (B / d)
  have hw : w.Nodup := (List.nodup_finRange _).filter _
  have hmem (i : Worker k) (hi : i ∈ w) : 0 < q i ∧ Nat.log2 (q i) = h := by
    simpa only [w, List.mem_filter, decide_eq_true_eq, List.mem_finRange, true_and] using hi
  have hbase (i : Worker k) (hi : i ∈ w) : base ≤ q i := by
    have hlog := (hmem i hi).2
    have hpow := Nat.log2_self_le (Nat.ne_of_gt (hmem i hi).1)
    simpa only [hlog] using hpow
  have hlen := bucket_length (B := B) q C h
  change (bucketSchedule B q C h).length =
    if m = 0 then 0 else ((2 * base + d - 1) / d) * ((m + chunk - 1) / chunk) at hlen
  rw [hlen]
  by_cases hm0 : m = 0
  · rw [ite_eq_left hm0, Nat.cast_zero]
    positivity
  · rw [ite_eq_right hm0]
    have hm : 0 < m := Nat.pos_of_ne_zero hm0
    have hc := fold_min_bounds w C hB (fun i hi => hC i (hmem i hi).1)
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil w (List.length_pos_iff.mp hm)
    have hbaseB : (base : ℝ) ≤ A * B := by
      calc
        _ ≤ (q i : ℝ) := by exact_mod_cast hbase i hi
        _ ≤ A * C i := hqA i
        _ ≤ A * B := mul_le_mul_of_nonneg_left (by exact_mod_cast hCB i) hA
    have hbaseC : (base : ℝ) ≤ A * cmin := by
      apply fold_min_product_lower w C hbaseB
      intro j hj
      exact (show (base : ℝ) ≤ q j by exact_mod_cast hbase j hj).trans (hqA j)
    have hround := grid_round_bound hB (by dsimp only [base]; positivity) hm hc.1 hc.2.1
      hA (by push_cast; nlinarith : ((2 * base : ℕ) : ℝ) ≤ 2 * A * cmin)
    have hsum : ((w.map (fun _ => base)).sum : ℕ) ≤ ∑ i, q i :=
      (List.sum_le_sum (fun i hi => hbase i hi)).trans (list_worker_sum_le w hw q)
    have hsumNat : base * m ≤ ∑ i, q i := by
      change base * w.length ≤ ∑ i, q i
      simpa only [List.map_const', List.sum_replicate, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
        using hsum
    have hsum' : (base : ℝ) * m ≤ ∑ i, (q i : ℝ) := by exact_mod_cast hsumNat
    have hpart : 2 * (2 * (base : ℝ)) * m / B ≤ 4 * (∑ i, (q i : ℝ)) / B := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      nlinarith
    have hround' : (((2 * base + d - 1) / d * ((m + chunk - 1) / chunk) : ℕ) : ℝ) ≤
        2 * A + 2 + 2 * (2 * (base : ℝ)) * m / B := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hround
    linarith

lemma schedule_round_bound {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) (hCB : ∀ i, C i ≤ B) {A : ℝ} (hA : 0 ≤ A)
    (hqA : ∀ i, (q i : ℝ) ≤ A * C i) :
    ((schedule B q C).length : ℝ) ≤
      (1 + Finset.univ.sup (fun i => Nat.log2 (q i)) : ℕ) *
        (4 * (∑ i, (q i : ℝ)) / B + 2 * A + 2) := by
  unfold schedule
  rw [List.length_flatMap, Nat.cast_list_sum, List.map_map]
  have hh := List.sum_le_length_nsmul
    ((List.range (1 + Finset.univ.sup (fun i => Nat.log2 (q i)))).map
      (fun h => ((bucketSchedule B q C h).length : ℝ)))
    (4 * (∑ i, (q i : ℝ)) / B + 2 * A + 2) (by
      intro x hx
      obtain ⟨h, _, rfl⟩ := List.mem_map.mp hx
      exact bucket_round_bound hB q C hC hCB hA hqA h)
  simpa only [List.length_map, List.length_range, nsmul_eq_mul, Function.comp_def] using hh

lemma bucket_work_bound {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) (h : ℕ) :
    let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
    let base := 2 ^ h
    let cmin := w.foldl (fun c i => min c (C i)) B
    let d := max 1 (min cmin (min (2 * base) (max 1 (B / w.length))))
    (bucketSchedule B q C h).length * d * B ≤ 4 * base * (B + (k + 1)) := by
  dsimp only
  let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let base := 2 ^ h
  let cmin := w.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / w.length))))
  let chunk := max 1 (B / d)
  change (bucketSchedule B q C h).length * d * B ≤ _
  have hc := fold_min_bounds w C hB (by
    intro i hi
    apply hC i
    have hi' : 0 < q i ∧ Nat.log2 (q i) = h := by simpa only [w, List.mem_filter,
      decide_eq_true_eq, List.mem_finRange, true_and] using hi
    exact hi'.1)
  have hlen := bucket_length (B := B) q C h
  change (bucketSchedule B q C h).length =
    if w.length = 0 then 0 else
      ((2 * base + d - 1) / d) * ((w.length + chunk - 1) / chunk) at hlen
  rw [hlen]
  by_cases hw0 : w.length = 0
  · simp only [ite_eq_left hw0, Nat.zero_mul]
    exact Nat.zero_le _
  · rw [ite_eq_right hw0]
    have hh := grid_work_bound (B := B) (M := 2 * base) (m := w.length) (cmin := cmin)
      hB (by positivity)
      (Nat.pos_of_ne_zero hw0) hc.1 hc.2.1
    have hwlen : w.length ≤ k + 1 := by
      exact (List.length_filter_le _ _).trans_eq List.length_finRange
    exact hh.trans (by
      change 2 * (2 * base) * (B + w.length) ≤ 4 * base * (B + (k + 1))
      nlinarith)

noncomputable def explorationLoad {k : ℕ} (u : Worker k → ℝ) (e : Counts k) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (e i : ℝ) * u i)

lemma bucket_row_load {k B : ℕ} (q C : Counts k) (h : ℕ) {u : Worker k → ℝ}
    (hu : ∀ i, 0 ≤ u i) {Q : ℝ} (hQ : 0 ≤ Q) (hqQ : ∀ i, (q i : ℝ) * u i ≤ Q)
    {e : Counts k} (he : e ∈ bucketSchedule B q C h) :
    let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
    let base := 2 ^ h
    let cmin := w.foldl (fun c i => min c (C i)) B
    let d := max 1 (min cmin (min (2 * base) (max 1 (B / w.length))))
    explorationLoad u e ≤ d * Q / base := by
  dsimp only
  let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let base := 2 ^ h
  let cmin := w.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / w.length))))
  let chunk := max 1 (B / d)
  change explorationLoad u e ≤ d * Q / base
  have hbase : (0 : ℝ) < base := by dsimp only [base]; positivity
  change e ∈ (if w.length = 0 then [] else
    (List.range ((2 * base + d - 1) / d)).flatMap (fun cycle =>
      (List.range ((w.length + chunk - 1) / chunk)).map (fun j =>
        fun i => if i ∈ (w.drop (j * chunk)).take chunk then
          min d (2 * base - cycle * d) else 0))) at he
  split_ifs at he
  · simp at he
  · obtain ⟨cycle, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    apply Finset.sup'_le
    intro i _
    dsimp only
    split_ifs with hi
    · have hiw : i ∈ w := List.mem_of_mem_drop (List.mem_of_mem_take hi)
      have hiq : 0 < q i ∧ Nat.log2 (q i) = h := by
        simpa only [w, List.mem_filter, decide_eq_true_eq, List.mem_finRange, true_and] using hiw
      have hpow : (base : ℝ) ≤ q i := by
        exact_mod_cast (hiq.2 ▸ Nat.log2_self_le (Nat.ne_of_gt hiq.1))
      have hui : u i ≤ Q / base := by
        apply (le_div_iff₀ hbase).mpr
        nlinarith [mul_le_mul_of_nonneg_right hpow (hu i), hqQ i]
      have hcount : ((min d (2 * base - cycle * d) : ℕ) : ℝ) ≤ d := by
        exact_mod_cast min_le_left d (2 * base - cycle * d)
      calc
        _ ≤ (d : ℝ) * u i := mul_le_mul_of_nonneg_right hcount (hu i)
        _ ≤ (d : ℝ) * (Q / base) := mul_le_mul_of_nonneg_left hui (Nat.cast_nonneg _)
        _ = _ := by ring
    · simp only [Nat.cast_zero, zero_mul]
      positivity

lemma bucket_exploration_bound {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) (h : ℕ) {u : Worker k → ℝ}
    (hu : ∀ i, 0 ≤ u i) {Q : ℝ} (hQ : 0 ≤ Q) (hqQ : ∀ i, (q i : ℝ) * u i ≤ Q) :
    ((bucketSchedule B q C h).map (explorationLoad u)).sum ≤
      4 * Q * (1 + (k + 1 : ℝ) / B) := by
  let w := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let base := 2 ^ h
  let cmin := w.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / w.length))))
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hbase : (0 : ℝ) < base := by dsimp only [base]; positivity
  have hwork : ((bucketSchedule B q C h).length : ℝ) * d * B ≤
      4 * (base : ℝ) * (B + (k + 1 : ℝ)) := by
    exact_mod_cast bucket_work_bound hB q C hC h
  have hrow : ∀ e ∈ bucketSchedule B q C h, explorationLoad u e ≤ d * Q / base :=
    fun e he => bucket_row_load q C h hu hQ hqQ he
  calc
    _ ≤ ((bucketSchedule B q C h).length : ℝ) * ((d : ℝ) * Q / base) := by
      simpa only [List.length_map, nsmul_eq_mul] using
        List.sum_le_length_nsmul ((bucketSchedule B q C h).map (explorationLoad u))
          ((d : ℝ) * Q / base) (fun x hx => by
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
            exact hrow e he)
    _ = (((bucketSchedule B q C h).length : ℝ) * d * B) * (Q / (B * base)) := by
      field_simp
    _ ≤ (4 * (base : ℝ) * (B + (k + 1 : ℝ))) * (Q / (B * base)) :=
      mul_le_mul_of_nonneg_right hwork (by positivity)
    _ = _ := by field_simp

lemma schedule_exploration_bound {k B : ℕ} (hB : 0 < B) (q C : Counts k)
    (hC : ∀ i, 0 < q i → 0 < C i) {u : Worker k → ℝ}
    (hu : ∀ i, 0 ≤ u i) {Q : ℝ} (hQ : 0 ≤ Q) (hqQ : ∀ i, (q i : ℝ) * u i ≤ Q) :
    ((schedule B q C).map (explorationLoad u)).sum ≤
      (1 + Finset.univ.sup (fun i => Nat.log2 (q i)) : ℕ) *
        (4 * Q * (1 + (k + 1 : ℝ) / B)) := by
  unfold schedule
  rw [List.map_flatMap, list_flatMap_sum]
  have hh := List.sum_le_length_nsmul
    ((List.range (1 + Finset.univ.sup (fun i => Nat.log2 (q i)))).map
      (fun h => ((bucketSchedule B q C h).map (explorationLoad u)).sum))
    (4 * Q * (1 + (k + 1 : ℝ) / B)) (by
      intro x hx
      obtain ⟨h, _, rfl⟩ := List.mem_map.mp hx
      exact bucket_exploration_bound hB q C hC h hu hQ hqQ)
  simpa only [List.length_map, List.length_range, nsmul_eq_mul] using hh

end LongTailsOnline.Proofs.TaskAllocation
