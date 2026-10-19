import LongTails.Algorithms.MultiscaleRepresentatives
import Mathlib.Data.List.Infix

namespace OracleTemplate.MixedNoise

lemma anchorIndex_zero (cfg : Config) (seed : RepresentativeSeed cfg) (t : ℕ) :
    anchorIndex cfg seed t 0 = t := by simp [anchorIndex]

lemma anchorIndex_le (cfg : Config) (seed : RepresentativeSeed cfg) {t l : ℕ}
    (hl : l ≤ cfg.m) (ht : t ≤ cfg.T) : anchorIndex cfg seed t l ≤ t := by
  by_cases hl0 : l = 0
  · subst l; simp [anchorIndex]
  have hp : 0 < 4 ^ l := by positivity
  have hb : t / 4 ^ l * 4 ^ l ≤ t := Nat.div_mul_le_self t (4 ^ l)
  unfold anchorIndex
  simp only [hl0, ↓reduceIte]
  by_cases hz : t / 4 ^ l * 4 ^ l = 0
  · simp only [hz, ↓reduceIte]; omega
  · have ht' : t / 4 ^ l * 4 ^ l ≤ cfg.T := hb.trans ht
    simp only [hz, hl, ht', ↓reduceIte, ↓reduceDIte]
    have hi := (seed.representatives (⟨l, by omega⟩,
      ⟨t / 4 ^ l * 4 ^ l, by omega⟩)).isLt
    simp only [Fin.val_mk] at hi
    have hd0 : t / 4 ^ l ≠ 0 := by
      intro he
      apply hz
      rw [he, Nat.zero_mul]
    have hdiv : 1 ≤ t / 4 ^ l := Nat.pos_of_ne_zero hd0
    have hbase : 4 ^ l ≤ t / 4 ^ l * 4 ^ l := by
      simpa using Nat.mul_le_mul_right (4 ^ l) hdiv
    omega

lemma anchorIndex_window (cfg : Config) (seed : RepresentativeSeed cfg) {t l : ℕ}
    (hl : l ≤ cfg.m) (ht : t ≤ cfg.T) : t ≤ anchorIndex cfg seed t l + 2 * 4 ^ l := by
  by_cases hl0 : l = 0
  · subst l; simp [anchorIndex]
  have hp : 0 < 4 ^ l := by positivity
  have hb : t / 4 ^ l * 4 ^ l ≤ t := Nat.div_mul_le_self t (4 ^ l)
  have hmod := Nat.mod_lt t hp
  have hdecomp := Nat.mod_add_div t (4 ^ l)
  have ht' : t / 4 ^ l * 4 ^ l ≤ cfg.T := hb.trans ht
  unfold anchorIndex
  simp only [hl0, ↓reduceIte]
  by_cases hz : t / 4 ^ l * 4 ^ l = 0
  · simp only [hz, ↓reduceIte]
    nlinarith [Nat.mul_comm (4 ^ l) (t / 4 ^ l)]
  · simp only [hz, hl, ht', ↓reduceIte, ↓reduceDIte]
    have hd0 : t / 4 ^ l ≠ 0 := by
      intro he
      apply hz
      rw [he, Nat.zero_mul]
    have hdiv : 1 ≤ t / 4 ^ l := Nat.pos_of_ne_zero hd0
    have hbase : 4 ^ l ≤ t / 4 ^ l * 4 ^ l := by
      simpa using Nat.mul_le_mul_right (4 ^ l) hdiv
    have hsub := Nat.sub_add_cancel hbase
    nlinarith [Nat.mul_comm (4 ^ l) (t / 4 ^ l)]

lemma edge_anchor_window (cfg : Config) (seed : RepresentativeSeed cfg) {t l : ℕ}
    (hl : l < cfg.m) (ht : t ≤ cfg.T) :
    let s := t / 4 ^ l * 4 ^ l
    let a := anchorIndex cfg seed s l
    let b := anchorIndex cfg seed s (l + 1)
    max a b ≤ t ∧ t ≤ min a b + 9 * 4 ^ l := by
  dsimp only
  let s := t / 4 ^ l * 4 ^ l
  have hst : s ≤ t := Nat.div_mul_le_self t (4 ^ l)
  have hsT : s ≤ cfg.T := hst.trans ht
  have ha := anchorIndex_le cfg seed (by omega : l ≤ cfg.m) hsT
  have hb := anchorIndex_le cfg seed (by omega : l + 1 ≤ cfg.m) hsT
  have hwa := anchorIndex_window cfg seed (by omega : l ≤ cfg.m) hsT
  have hwb := anchorIndex_window cfg seed (by omega : l + 1 ≤ cfg.m) hsT
  rw [pow_succ] at hwb
  have htbound : t ≤ s + 4 ^ l := by
    have hh := Nat.lt_mul_div_succ t (by positivity : 0 < 4 ^ l)
    dsimp [s]
    nlinarith
  constructor
  · change max (anchorIndex cfg seed s l) (anchorIndex cfg seed s (l + 1)) ≤ t
    omega
  · change t ≤ min (anchorIndex cfg seed s l) (anchorIndex cfg seed s (l + 1)) + 9 * 4 ^ l
    omega

lemma task_size_pos (cfg : Config) {task : BatchTask} (ht : task ∈ cfg.tasks) : 0 < task.size := by
  obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp ht
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  rw [← he]
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

lemma task_size_eq (cfg : Config) {task : BatchTask} (ht : task ∈ cfg.tasks) :
    task.size = max 1 (cfg.batch task.t task.level) := by
  obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp ht
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  rw [← he]

lemma task_time_lt (cfg : Config) {task : BatchTask} (ht : task ∈ cfg.tasks) : task.t < cfg.T := by
  obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp ht
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  rw [← he]
  exact List.mem_range.mp ht

lemma anchorIndex_dep (cfg : Config) (seed seed' : RepresentativeSeed cfg) {t cutoff : ℕ}
    (ht : t < cutoff)
    (hrep : ∀ i : Fin (cfg.m + 1) × Fin (cfg.T + 1), i.2.val < cutoff →
      seed.representatives i = seed'.representatives i) (l : ℕ) :
    anchorIndex cfg seed t l = anchorIndex cfg seed' t l := by
  by_cases hl0 : l = 0
  · simp [anchorIndex, hl0]
  by_cases hz : t / 4 ^ l * 4 ^ l = 0
  · simp [anchorIndex, hl0, hz]
  by_cases hl : l ≤ cfg.m
  · by_cases hb : t / 4 ^ l * 4 ^ l ≤ cfg.T
    · simp only [anchorIndex, hl0, hz, hl, hb, ↓reduceIte, ↓reduceDIte]
      have hh := hrep (⟨l, by omega⟩, ⟨t / 4 ^ l * 4 ^ l, by omega⟩)
        ((Nat.div_mul_le_self t (4 ^ l)).trans_lt ht)
      rw [hh]
    · simp [anchorIndex, hl0, hz, hl, hb]
  · simp [anchorIndex, hl0, hz, hl]

lemma prefixTasks_prefix (cfg : Config) {t : ℕ} (ht : t ≤ cfg.T) :
    cfg.prefixTasks t <+: cfg.tasks := by
  have h : List.range t <+: List.range cfg.T := by
    refine ⟨(List.range (cfg.T - t)).map (t + ·), ?_⟩
    rw [← List.range_add, Nat.add_sub_of_le ht]
  exact h.flatMap cfg.iterationTasks

lemma prefixTask_time_lt (cfg : Config) {t : ℕ} {task : BatchTask}
    (ht : task ∈ cfg.prefixTasks t) : task.t < t := by
  obtain ⟨k, hk, hm⟩ := List.mem_flatMap.mp ht
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  rw [← he]
  exact List.mem_range.mp hk

lemma tasks_before_time (cfg : Config) {t k : ℕ} (ht : t ≤ cfg.T)
    (hk : k < cfg.eventOffset t) : (cfg.tasks[k]!).t < t := by
  have hp := prefixTasks_prefix cfg ht
  have hlen : k < cfg.tasks.length := hk.trans_le hp.length_le
  rw [getElem!_pos cfg.tasks k hlen, ← hp.getElem hk]
  exact prefixTask_time_lt cfg (List.getElem_mem hk)

lemma prefixTasks_succ (cfg : Config) (t : ℕ) :
    cfg.prefixTasks (t + 1) = cfg.prefixTasks t ++ cfg.iterationTasks t := by
  simp [Config.prefixTasks, List.range_succ, List.flatMap_append]

lemma eventOffset_succ (cfg : Config) (t : ℕ) :
    cfg.eventOffset (t + 1) = cfg.eventOffset t + (cfg.levels t).length := by
  simp [Config.eventOffset, prefixTasks_succ, Config.iterationTasks]

lemma tasks_split (cfg : Config) {t : ℕ} (ht : t ≤ cfg.T) :
    cfg.tasks = cfg.prefixTasks t ++
      (List.range (cfg.T - t)).flatMap (fun k => cfg.iterationTasks (t + k)) := by
  change (List.range cfg.T).flatMap cfg.iterationTasks = _
  conv_lhs => rw [← Nat.add_sub_of_le ht, List.range_add]
  simp only [List.flatMap_append, List.flatMap_map, Config.prefixTasks]

lemma tasks_after_time (cfg : Config) {t k : ℕ} (ht : t ≤ cfg.T)
    (hk : cfg.eventOffset t ≤ k) (hj : k < cfg.tasks.length) :
    t ≤ (cfg.tasks[k]!).t := by
  have hs := tasks_split cfg ht
  rw [hs] at hj ⊢
  rw [getElem!_pos _ k hj, List.getElem_append_right hk]
  have hm := List.getElem_mem (l := (List.range (cfg.T - t)).flatMap
    (fun k => cfg.iterationTasks (t + k)))
    (show k - (cfg.prefixTasks t).length <
      ((List.range (cfg.T - t)).flatMap (fun k => cfg.iterationTasks (t + k))).length by
      rw [List.length_append] at hj
      change (cfg.prefixTasks t).length ≤ k at hk
      omega)
  obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨a, ha, he⟩ := List.mem_mapIdx.mp hm
  rw [← he]
  exact Nat.le_add_right _ _

lemma levels_nonempty (cfg : Config) (t : ℕ) : cfg.levels t ≠ [] := by
  by_cases ht : t = 0
  · simp [Config.levels, ht]
  · have h0 : 0 ∈ cfg.levels t := by simp [Config.levels, ht, Nat.mod_one]
    intro he
    simp [he] at h0

lemma levels_length_pos (cfg : Config) (t : ℕ) : 0 < (cfg.levels t).length :=
  List.length_pos_iff.mpr (levels_nonempty cfg t)

lemma iterationTask_at (cfg : Config) (t i : ℕ) (hi : i < (cfg.levels t).length) :
    (cfg.iterationTasks t)[i]'(by simpa [Config.iterationTasks] using hi) =
      { t := t, level := (cfg.levels t)[i], size := max 1 (cfg.batch t ((cfg.levels t)[i])),
        finish := i + 1 = (cfg.levels t).length } := by
  simp [Config.iterationTasks]

lemma tasks_iteration_at (cfg : Config) {t i : ℕ} (ht : t < cfg.T)
    (hi : i < (cfg.levels t).length) :
    cfg.tasks[cfg.eventOffset t + i]! =
      (cfg.iterationTasks t)[i]'(by simpa [Config.iterationTasks] using hi) := by
  have hp := prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)
  have hib : cfg.eventOffset t + i < (cfg.prefixTasks (t + 1)).length := by
    rw [prefixTasks_succ, List.length_append]
    simp only [Config.iterationTasks, List.length_mapIdx]
    change (cfg.prefixTasks t).length + i < (cfg.prefixTasks t).length + (cfg.levels t).length
    omega
  rw [getElem!_pos cfg.tasks _ (hib.trans_le hp.length_le), ← hp.getElem hib]
  simp only [prefixTasks_succ, Config.eventOffset, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

lemma levels_mem (cfg : Config) {t l : ℕ} (ht : t ≠ 0) :
    l ∈ cfg.levels t ↔ l ≤ cfg.m ∧ t % 4 ^ l = 0 := by
  simp [Config.levels, ht]

lemma levels_nodup (cfg : Config) (t : ℕ) : (cfg.levels t).Nodup := by
  by_cases ht : t = 0
  · simp [Config.levels, ht]
  · simp only [Config.levels, ht, ↓reduceIte]
    exact List.nodup_range.filter _

lemma task_level_mem (cfg : Config) {task : BatchTask} (ht : task ∈ cfg.tasks) :
    task.level ∈ cfg.levels task.t := by
  obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp ht
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  rw [← he]
  exact List.getElem_mem hi

lemma event_at_level (cfg : Config) {t l : ℕ} (ht : t < cfg.T)
    (hl : l ∈ cfg.levels t) :
    ∃ j, cfg.eventOffset t ≤ j ∧ j < cfg.eventOffset (t + 1) ∧
      j < cfg.tasks.length ∧ (cfg.tasks[j]!).t = t ∧ (cfg.tasks[j]!).level = l := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hl
  refine ⟨cfg.eventOffset t + i, by omega, ?_, ?_, ?_, ?_⟩
  · rw [eventOffset_succ]
    omega
  · have h := (prefixTasks_prefix cfg (show t + 1 ≤ cfg.T by omega)).length_le
    change cfg.eventOffset (t + 1) ≤ cfg.tasks.length at h
    rw [eventOffset_succ] at h
    omega
  · rw [tasks_iteration_at cfg ht hi, iterationTask_at cfg t i hi]
  · rw [tasks_iteration_at cfg ht hi, iterationTask_at cfg t i hi]
    exact he

lemma anchorIndex_succ_eq (cfg : Config) (seed : RepresentativeSeed cfg) {t l : ℕ}
    (hmod : (t + 1) % 4 ^ l ≠ 0) :
    anchorIndex cfg seed (t + 1) l = anchorIndex cfg seed t l := by
  have hl : l ≠ 0 := by
    intro he
    simp only [he, pow_zero, Nat.mod_one] at hmod
    exact hmod rfl
  simp only [anchorIndex, hl, ↓reduceIte, Nat.succ_div_of_mod_ne_zero hmod]
  split_ifs <;> try rfl
  congr 3
  apply Prod.ext
  · rfl
  · apply Fin.ext
    exact congrArg (fun k => k * 4 ^ l) (Nat.succ_div_of_mod_ne_zero hmod)

lemma anchorIndex_held (cfg : Config) (seed : RepresentativeSeed cfg) {s t l : ℕ}
    (hst : s ≤ t) (hmod : ∀ u, s < u → u ≤ t → u % 4 ^ l ≠ 0) :
    anchorIndex cfg seed t l = anchorIndex cfg seed s l := by
  induction t with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    rfl
  | succ t ih =>
    by_cases he : s = t + 1
    · rw [he]
    rw [anchorIndex_succ_eq cfg seed (hmod (t + 1) (by omega) le_rfl)]
    exact ih (by omega) (fun u hsu hut => hmod u hsu (by omega))

lemma anchorIndex_at_zero (cfg : Config) (seed : RepresentativeSeed cfg) (l : ℕ) :
    anchorIndex cfg seed 0 l = 0 := by
  by_cases hl : l = 0 <;> simp [anchorIndex, hl]

lemma anchorIndex_initial (cfg : Config) (seed : RepresentativeSeed cfg) {t l : ℕ}
    (ht : t < 4 ^ l) : anchorIndex cfg seed t l = 0 := by
  by_cases hl : l = 0
  · subst l
    have ht0 : t = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using ht
    rw [ht0, anchorIndex_at_zero]
  · simp only [anchorIndex, hl, ↓reduceIte, Nat.div_eq_of_lt ht, Nat.zero_mul]

lemma parent_not_refresh {t l : ℕ} (hmod : t % 4 ^ l ≠ 0) : t % 4 ^ (l + 1) ≠ 0 := by
  intro he
  apply hmod
  apply Nat.mod_eq_zero_of_dvd
  exact (pow_dvd_pow 4 (by omega : l ≤ l + 1)).trans (Nat.dvd_of_mod_eq_zero he)

end OracleTemplate.MixedNoise
