import LongTails.Proofs.BirchCollectionRetainedQuotaHistory
import LongTails.Proofs.BirchCollectionPolicies
import LongTails.Proofs.BirchCollectionBlocks

namespace LongTails.Proofs.BirchCollectionRetainedQuotaStructure

open Finset
open LongTails.Setups.BirchCollections hiding Ordering
open LongTails.Setups.BirchCollections (Ordering)
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionRetainedQuota
open LongTails.Algorithms.BirchCollectionRetune (trace retune)
open LongTails.Proofs.BirchCollectionRetainedQuotaHistory
open LongTails.Proofs.BirchCollectionRetune
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionBlocks (interval_exists)
open LongTails.Proofs.BirchCollectionPolicies (variable_phase_gate)

lemma phase_eq {m B K k n : ℕ} {schedule : ℕ → Phase m} (hc : Complete schedule B K)
    (hk : k < K) (hn : n ∈ Ico (cut schedule k) (cut schedule (k + 1))) :
    phaseAt schedule K n = k := by
  have hex : ∃ j, j < K ∧ cut schedule j ≤ n ∧ n < cut schedule (j + 1) :=
    ⟨k, hk, (mem_Ico.mp hn).1, (mem_Ico.mp hn).2⟩
  rw [phaseAt, dite_eq_left hex]
  obtain ⟨hj, hlow, hhigh⟩ := Nat.find_spec hex
  have ⟨hlo, hhi⟩ := mem_Ico.mp hn
  apply le_antisymm
  · by_contra! h
    have hm := cut_le hc (show k + 1 ≤ Nat.find hex by omega) (by omega)
    omega
  · by_contra! h
    have hm := cut_le hc (show Nat.find hex + 1 ≤ k by omega) (by omega)
    omega

lemma label {m : ℕ} (schedule : ℕ → Phase m) (K n : ℕ) (hn : n < cut schedule K) :
    (ordering schedule K).label n = n := by
  simp [ordering, LongTails.Setups.BirchCollections.Ordering.label, hn]

lemma history_eq {m B K : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (n : ℕ) (hn : n < cut schedule K) :
    (ordering schedule K).history (trace gain s.trace) n = (s.trace.directions n).history := by
  obtain ⟨k, hk, hl, hu⟩ := interval_exists (cut schedule) rfl K n hn
  have hp := (hs.direction k hk n (mem_Ico.mpr ⟨hl, hu⟩)).2.1
  ext j
  rw [ordering_history_mem _ _ _ _ (by simpa [ordering] using hn), label schedule K n hn]
  constructor
  · rintro ⟨hj, ha⟩
    have hj' : j < cut schedule K := by simpa [ordering] using hj
    rwa [label schedule K j hj'] at ha
  · intro hj
    have hj' := (mem_range.mp (hp hj)).trans hn
    refine ⟨by simpa [ordering] using hj', ?_⟩
    rw [label schedule K j hj']
    exact hj

lemma ordering_valid {m B K : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hK : 0 < K) :
    (ordering schedule K).Valid (trace gain s.trace) K := by
  have hcut : 1 ≤ cut schedule K := cut_le hc (show 1 ≤ K by omega) le_rfl
  refine ⟨by simpa [ordering] using (show 0 < cut schedule K by omega), List.nodup_range, hs.markers, rfl,
    by simp [ordering], fun _ hk => cut_lt hc hk, ?_, ?_, ?_⟩
  · intro n hn
    have hn' : n < cut schedule K := by simpa [ordering] using hn
    simpa only [label schedule K n hn', trace, hs.count] using hn'
  · intro k hk
    change (s.trace.states (s.trace.markers[k]?.getD 0)).history = (range (cut schedule k)).image _
    rw [hs.mark k hk, image_congr (g := id) (fun n hn =>
      label schedule K n ((mem_range.mp hn).trans_le (cut_le hc hk le_rfl))), image_id]
  · intro n
    by_cases hn : n < cut schedule K
    · obtain ⟨k, hk, hl, hu⟩ := interval_exists (cut schedule) rfl K n hn
      rw [history_eq hs n hn]
      exact (hs.direction k hk n (mem_Ico.mpr ⟨hl, hu⟩)).2.1
    · simp [LongTails.Setups.BirchCollections.Ordering.history, ordering, hn]

lemma gain_one : gain 1 = (1, 1) := by norm_num [gain]

lemma gain_valid (w : ℝ) (hw : 0 ≤ w) (hw' : w ≤ 1) :
    0 ≤ (gain w).2 ∧ (gain w).2 ≤ (gain w).1 ∧ (gain w).1 ≤ 1 := by
  unfold gain
  split
  · norm_num
  · exact ⟨hw, le_rfl, hw'⟩

lemma mapped_legal {m B K : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) : ValidFrom (m + 1) {} (s.events.map (retune gain)) := by
  have h := retune_legal gain (m + 1) {} s.events gain_valid hs.legal
  rwa [trace_initial _ gain_one] at h

lemma mapped_run {m B K : ℕ} {s : Round m} {schedule : ℕ → Phase m} (hs : History s schedule B K) :
    run (s.events.map (retune gain)) = trace gain s.trace := by
  rw [retune_run gain _ gain_one, hs.represented]

lemma block_profile {m B K k n : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K)
    (hk : k < K) (hn : n ∈ Ico (cut schedule k) (cut schedule (k + 1))) :
    let o := ordering schedule K
    let t := trace gain s.trace
    (o.refresh t n, o.movement t n) = gain (movement schedule B k) ∧ (o.raw t n).card = batch schedule B k := by
  have hn' := (mem_Ico.mp hn).2.trans_le (cut_le hc (show k + 1 ≤ K by omega) le_rfl)
  obtain ⟨_, _, hm, hb⟩ := hs.direction k hk n hn
  have hraw := rawLedger_run _ _ (mapped_legal hs)
  have hdone := completedLedger_run _ _ (mapped_legal hs)
  rw [mapped_run hs] at hraw hdone
  have hn'' : n < (trace gain s.trace).nextDirection := by
    change n < s.trace.nextDirection
    rwa [hs.count]
  have hnodup := (completed_raw _ hraw hdone n hn'').1
  constructor
  · have hlabel := label schedule K n hn'
    have hlen : n < (ordering schedule K).labels.length := by simpa [ordering] using hn'
    simp only [LongTails.Setups.BirchCollections.Ordering.refresh,
      LongTails.Setups.BirchCollections.Ordering.movement, hlen, ite_true, hlabel]
    change ((gain (s.trace.directions n).movement).1, (gain (s.trace.directions n).movement).2) = _
    rw [hm]
  · rw [LongTails.Setups.BirchCollections.Ordering.raw, label schedule K n hn',
      List.toFinset_card_of_nodup hnodup]
    exact hb

lemma reset_profile {m B K : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hK : 0 < K) :
    let o := ordering schedule K
    let t := trace gain s.trace
    o.refresh t 0 = 1 ∧ o.movement t 0 = 1 / 8 ∧ (o.raw t 0).card = B := by
  obtain ⟨hg, hb⟩ := block_profile hs hc hK (show 0 ∈ Ico (cut schedule 0) (cut schedule 1) by simp [cut])
  have h : gain (movement schedule B 0) = (1, 1 / 8) := by norm_num [gain, movement]
  rw [h] at hg
  exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg, by simpa [batch] using hb⟩

lemma leaf_profile {m B K k n : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B)
    (hk0 : 0 < k) (hk : k < K) (hn : n ∈ Ico (cut schedule k) (cut schedule (k + 1))) :
    let o := ordering schedule K
    let t := trace gain s.trace
    o.refresh t n = leafGain B (schedule k).batch ∧ o.movement t n = leafGain B (schedule k).batch ∧
      (o.raw t n).card = (schedule k).batch := by
  obtain ⟨hg, hb⟩ := block_profile hs hc hk hn
  have hg0 := (leaf_bounds hB (hc k hk0 hk)).2
  have hne : leafGain B (schedule k).batch ≠ 1 / 2 := by linarith
  rw [movement, ite_eq_right hk0.ne', gain, ite_eq_right hne] at hg
  exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg, by simpa [batch, hk0.ne'] using hb⟩

lemma block_sums {m B K k : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B) (hk : k < K) :
    let o := ordering schedule K
    let t := trace gain s.trace
    let work := volume schedule B k
    (∑ n ∈ Ico (cut schedule k) (cut schedule (k + 1)), o.movement t n) = (work : ℝ) / (8 * B) ∧
      (∑ n ∈ Ico (cut schedule k) (cut schedule (k + 1)), (o.raw t n).card) = work := by
  dsimp only [volume]
  by_cases h : k = 0
  · subst k
    have hset : Ico (cut schedule 0) (cut schedule (0 + 1)) = {0} := by simp [cut]
    obtain ⟨_, hw, hr⟩ := reset_profile hs hc hk
    simp only [hset, sum_singleton, ite_true, hw, hr]
    constructor
    · have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      field_simp
    · trivial
  · have hp := Nat.pos_of_ne_zero h
    have hcard : (Ico (cut schedule k) (cut schedule (k + 1))).card = (schedule k).arrivals.length := by
      rw [cut]
      simp [h]
    rw [ite_eq_right h]
    constructor
    · rw [sum_congr rfl (fun n hn => (leaf_profile hs hc hB hp hk hn).2.1), sum_const, hcard]
      simp only [nsmul_eq_mul, Phase.work, Nat.cast_mul, leafGain]
      ring
    · rw [sum_congr rfl (fun n hn => (leaf_profile hs hc hB hp hk hn).2.2), sum_const, hcard]
      change (schedule k).arrivals.length * (schedule k).batch = (schedule k).work
      exact Nat.mul_comm _ _


lemma phase_sum_bounds {m B K k : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B) (hk : k < K) :
    let o := ordering schedule K
    let t := trace gain s.trace
    let mass := ∑ n ∈ Ico (cut schedule k) (cut schedule (k + 1)), o.movement t n
    1 / 16 ≤ mass ∧ mass ≤ 1 / 8 := by
  have hbR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  dsimp only
  rw [(block_sums hs hc hB hk).1, volume]
  by_cases h : k = 0
  · rw [ite_eq_left h]
    constructor
    · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).2
      linarith
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B)).2
      linarith
  · rw [ite_eq_right h]
    have hp := hc k (Nat.pos_of_ne_zero h) hk
    have hl : (B : ℝ) ≤ 2 * (schedule k).work := by exact_mod_cast hp.2.2.1
    have hu : ((schedule k).work : ℝ) ≤ B := by exact_mod_cast hp.2.2.2
    constructor
    · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).2
      linarith
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B)).2
      linarith

lemma frontier_in {m B K n : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hn : n < cut schedule K) :
    let o := ordering schedule K
    let t := trace gain s.trace
    o.frontier n ≤ n ∧ range (o.frontier n) ⊆ o.history t n := by
  obtain ⟨k, hk, hlo, hhi⟩ := interval_exists (cut schedule) rfl K n hn
  have he := phase_eq hc hk (mem_Ico.mpr ⟨hlo, hhi⟩)
  change cut schedule (phaseAt schedule K n) ≤ n ∧ range (cut schedule (phaseAt schedule K n)) ⊆ _
  rw [he, history_eq hs n hn]
  exact ⟨hlo, (hs.direction k hk n (mem_Ico.mpr ⟨hlo, hhi⟩)).1⟩

lemma window {m B K n : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B)
    (hn : n < cut schedule K) :
    let o := ordering schedule K
    let t := trace gain s.trace
    (∑ j ∈ Ico (o.frontier n) n, o.movement t j) ≤ 1 / 4 := by
  obtain ⟨k, hk, hlo, hhi⟩ := interval_exists (cut schedule) rfl K n hn
  have he := phase_eq hc hk (mem_Ico.mpr ⟨hlo, hhi⟩)
  change (∑ j ∈ Ico (cut schedule (phaseAt schedule K n)) n, _) ≤ _
  rw [he]
  have hsub : Ico (cut schedule k) n ⊆ Ico (cut schedule k) (cut schedule (k + 1)) := by
    intro j hj
    exact mem_Ico.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.trans hhi⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub ?_).trans
    ((phase_sum_bounds hs hc hB hk).2.trans (by norm_num))
  intro j hj _
  by_cases h : k = 0
  · have hj0 : j = 0 := by simpa [h, cut] using hj
    subst j
    have hK : 0 < K := by omega
    rw [(reset_profile hs hc hK).2.1]
    norm_num
  · rw [(leaf_profile hs hc hB (Nat.pos_of_ne_zero h) hk hj).2.1]
    exact (leaf_bounds hB (hc k (Nat.pos_of_ne_zero h) hk)).1

lemma renewal_step {m B K j : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B) (hK : 0 < K)
    (hj : j < cut schedule K) :
    let o := ordering schedule K
    let t := trace gain s.trace
    let z := o.renewalFrontier 0 j
    1 ≤ o.scale 0 j ∧ o.scale 0 j ≤ 2 ∧ 0 ≤ 1 - o.refresh t j * o.scale 0 j ∧
      z ≤ j ∧ (∀ i, i < z → i ∈ o.history t j) ∧
      1 ≤ o.scale 0 j * ∏ i ∈ range (j - z), (1 - o.refresh t (z + i) * o.scale 0 (z + i)) := by
  let o := ordering schedule K
  let t := trace gain s.trace
  let z := cut schedule (phaseAt schedule K j)
  change 1 ≤ o.scale 0 j ∧ o.scale 0 j ≤ 2 ∧ 0 ≤ 1 - o.refresh t j * o.scale 0 j ∧
    z ≤ j ∧ (∀ i, i < z → i ∈ o.history t j) ∧
    1 ≤ o.scale 0 j * ∏ i ∈ range (j - z), (1 - o.refresh t (z + i) * o.scale 0 (z + i))
  obtain ⟨k, hk, hlo, hhi⟩ := interval_exists (cut schedule) rfl K j hj
  have hmem := mem_Ico.mpr ⟨hlo, hhi⟩
  have hz : z = cut schedule k := congrArg (cut schedule) (phase_eq hc hk hmem)
  rw [hz]
  have hhist := (frontier_in hs hc hj).2
  change range z ⊆ o.history t j at hhist
  rw [hz] at hhist
  refine ⟨?_, ?_, ?_, hlo, fun i hi => hhist (mem_range.mpr hi), ?_⟩
  · simp [o, ordering]
    split <;> norm_num
  · simp [o, ordering]
    split <;> norm_num
  · by_cases h : k = 0
    · subst k
      have h0 : j = 0 := by simpa [cut] using hmem
      subst j
      have hr := (reset_profile hs hc hK).1
      change o.refresh t 0 = 1 at hr
      change 0 ≤ 1 - o.refresh t 0 * 1
      rw [hr]
      norm_num
    · have hk0 := Nat.pos_of_ne_zero h
      have hj0 : j ≠ 0 := by
        have hlow : 1 ≤ cut schedule k := cut_le hc hk0 hk.le
        omega
      have hscale : o.scale 0 j = 2 := by simp [o, ordering, hj0]
      rw [hscale, (leaf_profile hs hc hB hk0 hk hmem).1]
      linarith [(leaf_bounds hB (hc k hk0 hk)).2]
  · by_cases h : k = 0
    · subst k
      have h0 : j = 0 := by simpa [cut] using hmem
      subst j
      change 1 ≤ (1 : ℝ) * ∏ i ∈ range 0, _
      simp
    · have hk0 := Nat.pos_of_ne_zero h
      have hlow : 1 ≤ cut schedule k := cut_le hc hk0 hk.le
      have hj0 : j ≠ 0 := by omega
      have hscale : o.scale 0 j = 2 := by simp [o, ordering, hj0]
      have hp := hc k hk0 hk
      have hcount : j - cut schedule k ≤ (schedule k).arrivals.length := by
        rw [cut, ite_eq_right h] at hhi
        omega
      have hsum : (∑ _i ∈ range (j - cut schedule k), (schedule k).batch) ≤ 2 * B := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        have he := Nat.mul_le_mul_right (schedule k).batch hcount
        rw [Nat.mul_comm (schedule k).arrivals.length] at he
        exact he.trans (hp.2.2.2.trans (by omega))
      have hb : (schedule k).batch ≤ B := by
        exact (by simpa [Phase.work] using Nat.mul_le_mul_left (schedule k).batch hp.2.1 :
          (schedule k).batch ≤ (schedule k).work).trans hp.2.2.2
      have hgate := variable_phase_gate (range (j - cut schedule k)) (fun _ => (schedule k).batch)
        B hB (fun _ _ => hb) hsum
      rw [hscale]
      refine hgate.trans_eq ?_
      congr 1
      apply prod_congr rfl
      intro i hi
      have hil := mem_range.mp hi
      have he : cut schedule k + i ∈ Ico (cut schedule k) (cut schedule (k + 1)) :=
        mem_Ico.mpr ⟨by omega, by omega⟩
      have hs' : o.scale 0 (cut schedule k + i) = 2 := by
        have hne : cut schedule k + i ≠ 0 := by omega
        change (if cut schedule k + i = 0 then (1 : ℝ) else 2) = 2
        rw [ite_eq_right hne]
      rw [hs', (leaf_profile hs hc hB hk0 hk he).1]
      unfold leafGain
      ring

lemma structural {m B K D : ℕ} {s : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (hc : Complete schedule B K) (hB : 0 < B) (hK : 0 < K)
    (hcost : s.trace.nextRaw - ((range (ordering schedule K).labels.length).biUnion
      ((ordering schedule K).raw (trace gain s.trace))).card ≤ D) :
    Structural (trace gain s.trace) (ordering schedule K) (controls D) K B := by
  let o := ordering schedule K
  let t := trace gain s.trace
  have hl (n : ℕ) (hn : n < o.labels.length) : n < cut schedule K := by simpa [o, ordering] using hn
  refine ⟨ordering_valid hs hc hK, by norm_num [Controls.Valid, controls], (reset_profile hs hc hK).1,
    fun n hn => ⟨(frontier_in hs hc (hl n hn)).1, (frontier_in hs hc (hl n hn)).2,
      window hs hc hB (hl n hn)⟩, ?_, ?_, ?_, ?_, hcost, ?_⟩
  · intro k hk
    exact (phase_sum_bounds hs hc hB hk).1
  · intro k hk
    exact (phase_sum_bounds hs hc hB hk).2
  · intro n hn
    obtain ⟨k, hk, hlo, hhi⟩ := interval_exists (cut schedule) rfl K n (hl n hn)
    by_cases h : k = 0
    · subst k
      have hn0 : n = 0 := by simpa [cut] using mem_Ico.mpr ⟨hlo, hhi⟩
      subst n
      rw [(reset_profile hs hc hK).1, (reset_profile hs hc hK).2.2, one_mul]
    · obtain ⟨hr, _, hraw⟩ := leaf_profile hs hc hB (Nat.pos_of_ne_zero h) hk (mem_Ico.mpr ⟨hlo, hhi⟩)
      rw [hr, hraw]
      have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      have he : leafGain B (schedule k).batch * B = ((schedule k).batch : ℝ) / 8 := by
        unfold leafGain
        field_simp
      rw [he]
      have hbn : (0 : ℝ) ≤ (schedule k).batch := by positivity
      linarith
  · intro n hn
    right
    obtain ⟨k, hk, hlo, hhi⟩ := interval_exists (cut schedule) rfl K n (hl n hn)
    by_cases h : k = 0
    · subst k
      have hn0 : n = 0 := by simpa [cut] using mem_Ico.mpr ⟨hlo, hhi⟩
      subst n
      rw [(reset_profile hs hc hK).2.1, (reset_profile hs hc hK).2.2]
      change (B : ℝ) ≤ B * 8 * (1 / 8)
      linarith
    · obtain ⟨_, hw, hraw⟩ := leaf_profile hs hc hB (Nat.pos_of_ne_zero h) hk (mem_Ico.mpr ⟨hlo, hhi⟩)
      rw [hw, hraw]
      change ((schedule k).batch : ℝ) ≤ B * 8 * (((schedule k).batch : ℝ) / (8 * B))
      have hbR : (0 : ℝ) < 8 * B := by positivity
      have he : B * 8 * (((schedule k).batch : ℝ) / (8 * B)) = (schedule k).batch := by
        field_simp
      rw [he]
  · intro n hn
    have ha : (ordering schedule K).anchor n = 0 := rfl
    simp only [ha, Nat.zero_add, Nat.sub_zero]
    have hzero : o.history t 0 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => by simpa using (ordering_valid hs hc hK).2.2.2.2.2.2.2.2 0 hi)
    refine ⟨Nat.zero_le _, (reset_profile hs hc hK).1, fun _ => by simpa using hzero, ?_, ?_⟩
    · intro j hj hjn
      have hj' : j < cut schedule K := hjn.trans_lt (hl n hn)
      obtain ⟨k, hk, hlo, hhi⟩ := interval_exists (cut schedule) rfl K j hj'
      have hmem := mem_Ico.mpr ⟨hlo, hhi⟩
      have hk0 : 0 < k := by
        by_contra! h
        have he : k = 0 := by omega
        subst k
        have hj0 : j = 0 := by simpa [cut] using hmem
        omega
      have hf : o.frontier j = cut schedule k := congrArg (cut schedule) (phase_eq hc hk hmem)
      have hlow : 1 ≤ o.frontier j := by rw [hf]; exact cut_le hc hk0 hk.le
      exact (range_mono hlow).trans (frontier_in hs hc hj').2
    · intro j hj
      have hj' : j < cut schedule K := hj.trans_lt (hl n hn)
      exact renewal_step hs hc hB hK hj'

end LongTails.Proofs.BirchCollectionRetainedQuotaStructure
