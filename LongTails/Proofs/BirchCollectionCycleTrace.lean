import LongTails.Algorithms.BirchCollectionCycle
import LongTails.Proofs.BirchCollectionPoolCertificate
import LongTails.Proofs.BirchCollectionCycleTimer

namespace LongTails.Proofs.BirchCollectionCycleTrace

open Finset
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Algorithms.BirchCollectionCycle (upper window)
open LongTails.Proofs.BirchCollectionPoolTrace
open LongTails.Proofs.BirchCollectionPoolPublish
open LongTails.Proofs.BirchCollectionPoolCounts
open LongTails.Proofs.BirchCollectionCycleTimer

structure Bounds {m : ℕ} (s : Pool m) (size tick : ℕ) : Prop where
  cuts : s.cuts.length = tick + 1
  frontiers : ∀ w, (s.worker w).frontier ≤ s.accepted.length
  count : ∀ w, privateCount s w ≤ sinceLimit (cycleGroups m size) (w.val / size) tick
  age : ∀ w, age s w ≤ upper m size * sinceLimit (cycleGroups m size) (w.val / size) tick

lemma compute_one {m : ℕ} (B : ℕ) (move : ℝ) (s : Pool m) (w : Fin m) :
    let t := complete B (issue B move s w) w
    t.accepted = s.accepted ∧ t.cuts = s.cuts ∧
      (∀ v, privateCount t v = privateCount s v + if v = w then 1 else 0) ∧
      (∀ v, (t.worker v).frontier = (s.worker v).frontier) := by
  let t := complete B (issue B move s w) w
  refine ⟨by simp [complete, issue, Pool.put, Pool.append],
    by simp [complete, issue, Pool.put, Pool.append], ?_, ?_⟩
  · intro v
    change privateCount t v = _
    by_cases h : v = w
    · subst v
      simp [t, complete, issue, Pool.put, Pool.append, privateCount]
    · simp [t, complete, issue, Pool.put, Pool.append, privateCount, h]
  · intro v
    change (t.worker v).frontier = _
    by_cases h : v = w
    · subst v
      simp [t, complete, issue, Pool.put, Pool.append]
    · simp [t, complete, issue, Pool.put, Pool.append, h]

lemma compute_fold {m B lo hi W : ℕ} {move : ℝ} (s : Pool m) (ws : List (Fin m))
    (hs : Data s B lo hi W move) (hB : 0 < B) (hm : 0 ≤ move) (hm' : move ≤ 1)
    (hn : ws.Nodup) :
    let t := ws.foldl (fun t w => complete B (issue B move t w) w) s
    Data t B lo hi W move ∧ t.accepted = s.accepted ∧ t.cuts = s.cuts ∧
      (∀ v, privateCount t v = privateCount s v + if v ∈ ws then 1 else 0) ∧
      (∀ v, (t.worker v).frontier = (s.worker v).frontier) := by
  induction ws generalizing s with
  | nil => exact ⟨hs, rfl, rfl, by simp, fun _ => rfl⟩
  | cons w ws ih =>
    have hi' := data_issue s w hs hB hm hm'
    have hr : ((issue B move s w).worker w).pending.isSome := by simp [issue, Pool.put, Pool.append]
    have ht := data_complete (issue B move s w) w hi' hr
    obtain ⟨hd, ha, hc, hcount, hf⟩ := ih _ ht (List.nodup_cons.mp hn).2
    obtain ⟨ha', hc', hcount', hf'⟩ := compute_one B move s w
    refine ⟨hd, ha.trans ha', hc.trans hc', ?_, fun v => (hf v).trans (hf' v)⟩
    intro v
    change privateCount (ws.foldl (fun t w => complete B (issue B move t w) w)
      (complete B (issue B move s w) w)) v = _
    rw [hcount v, hcount' v]
    by_cases hv : v = w
    · subst v
      simp [(List.nodup_cons.mp hn).1]
    · simp [hv]

lemma publish_cut {m B : ℕ} (s : Pool m) (ws : List (Fin m))
    (hp : 0 < (selectedLabels s ws).length) :
    (publish B s ws).cuts = s.cuts ++ [s.accepted.length + (selectedLabels s ws).length] := by
  have hfalse : ¬(selectedLabels s ws).isEmpty := by
    cases hs : selectedLabels s ws with
    | nil => simp [hs] at hp
    | cons d ds => simp
  have hreset (t : Pool m) (ls : List (Fin m)) (root : Worker) :
      (ls.foldl (fun t w => t.put w root) t).cuts = t.cuts := by
    induction ls generalizing t with
    | nil => rfl
    | cons w ws ih => exact ih (t.put w root)
  unfold publish
  rw [hreset]
  simp only [publishState, ite_eq_right hfalse]

lemma cycle_step {m size B tick : ℕ} {move : ℝ} (s : Pool m)
    (hs : Data s B 1 (upper m size) (window m size) move) (hb : Bounds s size tick)
    (hm : 0 < m) (hsize : 0 < size) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    let out := cycleStep size B move s tick
    Data out B 1 (upper m size) (window m size) move ∧ Bounds out size (tick + 1) := by
  let t := cycleCompute B move s
  let T := cycleGroups m size
  let ws := cycleGroup m size tick
  let c := (selectedLabels t ws).length
  let out := publish B t ws
  have hT : 0 < T := by unfold T; rw [group_count m size hm]; exact Nat.zero_lt_succ _
  obtain ⟨hd, ha, hcut, hct, hf⟩ := compute_fold s (List.finRange m) hs hB hm0 hm1 (List.nodup_finRange m)
  change Data t B 1 (upper m size) (window m size) move at hd
  have hcount (v : Fin m) : privateCount t v = privateCount s v + 1 := by simpa [t, cycleCompute] using hct v
  have hage (v : Fin m) : age t v = age s v := by
    unfold age
    change t.accepted = s.accepted at ha
    rw [ha, show (t.worker v).frontier = _ from hf v]
  have hn : ws.Nodup := (List.nodup_finRange m).filter _
  have hsum : c = ∑ w ∈ ws.toFinset, privateCount t w := selected_count t ws hn
  have hpos : 0 < c := by
    obtain ⟨w, hw⟩ := cycle_group_nonempty m size tick hm hsize
    have hw' : w ∈ ws.toFinset := List.mem_toFinset.mpr hw
    have h := single_le_sum (f := privateCount t) (fun v _ => Nat.zero_le _) hw'
    rw [← hsum, hcount w] at h
    omega
  have hupper : c ≤ upper m size := by
    rw [hsum]
    calc
      _ ≤ ∑ _ ∈ ws.toFinset, T := sum_le_sum fun w _ => by
        rw [hcount]
        have h := hb.count w
        unfold sinceLimit at h
        omega
      _ = ws.toFinset.card * T := by simp
      _ ≤ upper m size := by
        have hc : ws.toFinset.card ≤ m := by simpa using card_le_univ ws.toFinset
        exact Nat.mul_le_mul_right T hc
  have hwindow : ∀ w ∈ ws, age t w + c - 1 ≤ window m size := by
    intro w _
    rw [hage]
    have h := hb.age w
    have hlimit : sinceLimit T (w.val / size) tick ≤ T - 1 := Nat.sub_le _ _
    have h₁ := h.trans (Nat.mul_le_mul_left (upper m size) hlimit)
    have h₂ : upper m size * (T - 1) + upper m size = upper m size * T := by
      calc
        _ = upper m size * (T - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = _ := by rw [Nat.sub_add_cancel hT]
    unfold window
    change _ ≤ upper m size * T - 1
    omega
  have hdata := data_publish t ws hd hn (fun h => h) hupper hwindow
  obtain ⟨hacc, hprivate, hfront⟩ := publish_profile B t ws
  change Data out B 1 (upper m size) (window m size) move ∧ Bounds out size (tick + 1)
  refine ⟨hdata, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [show out.cuts = _ from publish_cut t ws hpos]
    simp only [List.length_append, List.length_singleton, show t.cuts = _ from hcut, hb.cuts]
  · intro w
    rw [hfront w]
    by_cases h : w ∈ ws
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, show (t.worker w).frontier = _ from hf w, hacc, show t.accepted = _ from ha]
      exact (hb.frontiers w).trans (Nat.le_add_right _ _)
  · intro w
    rw [hprivate w]
    by_cases h : w ∈ ws
    · rw [ite_eq_left h]
      exact Nat.zero_le _
    · have hne : w.val / size ≠ tick % T := fun he => h ((cycle_group_mem w).2 he)
      rw [ite_eq_right h, hcount, since_other hT (group_lt hm w) hne]
      exact Nat.add_le_add_right (hb.count w) _
  · intro w
    change out.accepted.length - (out.worker w).frontier ≤ _
    rw [hfront w]
    by_cases h : w ∈ ws
    · rw [ite_eq_left h, Nat.sub_self]
      exact Nat.zero_le _
    · have hne : w.val / size ≠ tick % T := fun he => h ((cycle_group_mem w).2 he)
      rw [ite_eq_right h, show (t.worker w).frontier = _ from hf w, hacc,
        show t.accepted = _ from ha, since_other hT (group_lt hm w) hne, Nat.mul_add, Nat.mul_one]
      have hw := hb.frontiers w
      have hbound := hb.age w
      unfold age at hbound
      change s.accepted.length + c - (s.worker w).frontier ≤
        upper m size * sinceLimit (cycleGroups m size) (w.val / size) tick + upper m size
      omega

lemma cycle_data (m size B K : ℕ) (move : ℝ)
    (hm : 0 < m) (hsize : 0 < size) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    Data (cycle m size B K move) B 1 (upper m size) (window m size) move ∧
      Bounds (cycle m size B K move) size K := by
  induction K with
  | zero =>
    exact ⟨initial_data m B 1 (upper m size) (window m size) move, ⟨rfl,
      fun _ => le_rfl, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩⟩
  | succ K ih =>
    have he : cycle m size B (K + 1) move = cycleStep size B move (cycle m size B K move) K := by
      unfold cycle
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [he]
    exact cycle_step _ ih.1 ih.2 hm hsize hB hm0 hm1

end LongTails.Proofs.BirchCollectionCycleTrace
