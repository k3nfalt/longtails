import LongTails.Proofs.BirchCollectionPoolCounts

namespace LongTails.Proofs.BirchCollectionMetaBounds

open Finset
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Proofs.BirchCollectionPoolCounts

structure Bounds {m : ℕ} (s : Pool m) (Q : ℕ) : Prop where
  frontiers : ∀ w, (s.worker w).frontier ≤ s.accepted.length
  quota : maxAge s + remaining s ≤ Q

lemma max_bound {m : ℕ} (s : Pool m) (Q : ℕ) (hr : remaining s ≤ Q)
    (hw : ∀ w, age s w + remaining s ≤ Q) : maxAge s + remaining s ≤ Q := by
  have hs : maxAge s ≤ Q - remaining s := by
    unfold maxAge
    apply Finset.sup_le_iff.mpr
    intro w _
    have h := hw w
    omega
  omega

lemma issue_profile {m : ℕ} (B : ℕ) (move : ℝ) (s : Pool m) (w : Fin m) :
    (issue B move s w).accepted = s.accepted ∧
      ∀ v, privateCount (issue B move s w) v = privateCount s v ∧
        ((issue B move s w).worker v).frontier = (s.worker v).frontier := by
  refine ⟨rfl, ?_⟩
  intro v
  by_cases h : v = w
  · subst v
    simp [issue, privateCount, Pool.put, Pool.append]
  · simp [issue, privateCount, Pool.put, Pool.append, Function.update_of_ne h]

lemma complete_profile {m : ℕ} (B : ℕ) (s : Pool m) (w : Fin m)
    (hw : (s.worker w).pending.isSome) :
    (complete B s w).accepted = s.accepted ∧
      remaining (complete B s w) = remaining s + 1 ∧
      ∀ v, ((complete B s w).worker v).frontier = (s.worker v).frontier := by
  cases h : (s.worker w).pending with
  | none => simp [h] at hw
  | some t =>
    let out := complete B s w
    have ha : out.accepted = s.accepted := by simp [out, complete, h, Pool.put, Pool.append]
    have hworker (v : Fin m) : out.worker v =
        Function.update s.worker w
          {s.worker w with
            head := s.trace.nextState
            privateLabels := (s.worker w).privateLabels ++ [s.trace.nextDirection]
            pending := none} v := by
      simp [out, complete, h, Pool.put, Pool.append]
    have hc (v : Fin m) : privateCount out v = privateCount s v + if v = w then 1 else 0 := by
      unfold privateCount
      rw [hworker]
      by_cases hv : v = w
      · subst v
        simp
      · simp [hv]
    change out.accepted = s.accepted ∧ remaining out = remaining s + 1 ∧ _
    refine ⟨ha, ?_, ?_⟩
    · unfold remaining
      change (∑ v : Fin m, privateCount out v) = (∑ v : Fin m, privateCount s v) + 1
      simp only [hc, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    · intro v
      change (out.worker v).frontier = _
      rw [hworker]
      by_cases hv : v = w
      · subst v
        simp
      · simp [Function.update_of_ne hv]

lemma stable_bounds {m Q : ℕ} {s t : Pool m} (hs : Bounds s Q)
    (ha : t.accepted = s.accepted)
    (hp : ∀ w, privateCount t w = privateCount s w ∧ (t.worker w).frontier = (s.worker w).frontier) :
    Bounds t Q := by
  have hr : remaining t = remaining s := by
    unfold remaining
    exact sum_congr rfl fun w _ => (hp w).1
  have hage : age t = age s := by
    funext w
    simp [age, ha, (hp w).2]
  refine ⟨fun w => by rw [ha, (hp w).2]; exact hs.frontiers w, ?_⟩
  unfold maxAge
  rw [hage, hr]
  exact hs.quota

lemma publish_bounds {m Q : ℕ} (B : ℕ) (s : Pool m) (ws : List (Fin m))
    (hs : Bounds s Q) (hn : ws.Nodup) : Bounds (publish B s ws) Q := by
  let t := publish B s ws
  let c := (selectedLabels s ws).length
  obtain ⟨ha, _, hf⟩ := publish_profile B s ws
  change t.accepted.length = s.accepted.length + c at ha
  have hfront (w : Fin m) :
      (t.worker w).frontier = if w ∈ ws then t.accepted.length else (s.worker w).frontier := hf w
  have hsum : remaining t + c = remaining s := remaining_publish B s ws hn
  have hcap := hs.quota
  refine ⟨?_, max_bound t Q (by omega) ?_⟩
  · intro w
    rw [hfront]
    split
    · exact le_rfl
    · rw [ha]
      exact (hs.frontiers w).trans (Nat.le_add_right _ _)
  · intro w
    unfold age
    rw [hfront]
    by_cases hw : w ∈ ws
    · rw [ite_eq_left hw, Nat.sub_self, zero_add]
      omega
    · rw [ite_eq_right hw, ha]
      have hbase := hs.frontiers w
      have hage : age s w ≤ maxAge s := le_sup (f := age s) (mem_univ w)
      unfold age at hage
      omega

lemma meta_step {m Q B : ℕ} (move : ℝ) (s : Pool m) (e : MetaEvent m)
    (hs : Bounds s Q) (he : MetaEnabled Q s e) : Bounds (metaAdvance Q B move s e) Q := by
  cases e with
  | query w =>
    obtain ⟨ha, hp⟩ := issue_profile B move s w
    exact stable_bounds hs ha hp
  | reply w =>
    by_cases h : maxAge s + remaining s < Q
    · let t := complete B s w
      obtain ⟨ha, hr, hf⟩ := complete_profile B s w he
      have hage : age t = age s := by
        funext u
        change t.accepted.length - (t.worker u).frontier = s.accepted.length - (s.worker u).frontier
        change t.accepted = s.accepted at ha
        rw [ha, show (t.worker u).frontier = (s.worker u).frontier from hf u]
      have hb : Bounds t Q := by
        refine ⟨fun v => ?_, ?_⟩
        · rw [ha, show (t.worker v).frontier = (s.worker v).frontier from hf v]
          exact hs.frontiers v
        · unfold maxAge
          rw [hage, show remaining t = _ from hr]
          unfold maxAge at h
          omega
      simpa only [metaAdvance, ite_eq_left h] using hb
    · have ht : Bounds (discard B s w) Q :=
        stable_bounds hs (close_profile B s w w).1 (fun v => (close_profile B s w v).2)
      simpa only [metaAdvance, ite_eq_right h] using ht
  | sync ws => exact publish_bounds B s ws hs he.1

lemma meta_bounds {m Q B : ℕ} (move : ℝ) (events : List (MetaEvent m))
    (he : MetaLegal Q B move {} events) : Bounds (metaRun Q B move events) Q := by
  have aux (s : Pool m) (events : List (MetaEvent m)) (hs : Bounds s Q)
      (he : MetaLegal Q B move s events) :
      Bounds (events.foldl (metaAdvance Q B move) s) Q := by
    induction events generalizing s with
    | nil => exact hs
    | cons e es ih => exact ih _ (meta_step move s e hs he.1) he.2
  apply aux {} events _ he
  exact ⟨fun _ => le_rfl, by simp [maxAge, age, remaining]⟩

end LongTails.Proofs.BirchCollectionMetaBounds
