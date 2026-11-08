import LongTails.Proofs.BirchCollectionLocalAsyncTrace
import LongTails.Proofs.BirchCollectionLocal

namespace LongTails.Proofs.BirchCollectionLocalAsync

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round localOrdering)
open LongTails.Algorithms.BirchCollectionLocalAsync
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionLocalTrace (round_initial)
open LongTails.Proofs.BirchCollectionLocalPublish (round_info)
open LongTails.Proofs.BirchCollectionLocalRounds
open LongTails.Proofs.BirchCollectionLocalAsyncTrace
open LongTails.Algorithms.BirchCollectionLocal (tuned)
open LongTails.Proofs.BirchCollectionLocal (history_structural)
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma async_frame_step {m B : ℕ} (group : Fin m → Fin m) (move : ℝ) (s : Round m)
    (e : OriginalEvent m) :
    let t := advance group B move s e
    Extends s.trace t.trace ∧ t.trace.markers = s.trace.markers := by
  cases e with
  | query w =>
    change Extends s.trace ((capture group B move s w).foldl step s.trace) ∧
      ((capture group B move s w).foldl step s.trace).markers = _
    refine ⟨extends_fold _ _, ?_⟩
    rw [fold_marks]
    simp [marks, capture]
  | reply w =>
    cases h : s.pending w with
    | none => simp [advance, h, extends_refl]
    | some t =>
      simp only [advance, h]
      change Extends s.trace ((complete group B s w t).foldl step s.trace) ∧
        ((complete group B s w t).foldl step s.trace).markers = _
      refine ⟨extends_fold _ _, ?_⟩
      rw [fold_marks]
      simp [marks, complete, LongTails.Algorithms.BirchCollectionLocal.localComplete, List.filterMap_map]

lemma async_frame {m B : ℕ} (group : Fin m → Fin m) (move : ℝ) (s : Round m)
    (es : List (OriginalEvent m)) :
    let t := es.foldl (advance group B move) s
    Extends s.trace t.trace ∧ t.trace.markers = s.trace.markers := by
  induction es generalizing s with
  | nil => exact ⟨extends_refl _, rfl⟩
  | cons e es ih =>
    obtain ⟨he, hm⟩ := async_frame_step (B := B) group move s e
    obtain ⟨he', hm'⟩ := ih (advance group B move s e)
    exact ⟨he.trans he', hm'.trans hm⟩

lemma async_round {m K Q B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m)
    (es : List (OriginalEvent m)) (hs : History s K Q B move) (hQ : 0 < Q) (hB : 0 < B)
    (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom group Q B move (Round.initial m s.trace s.events) es)
    (hc : (es.foldl (advance group B move) (Round.initial m s.trace s.events)).completed = Q) :
    History (runRound group B move (Round.initial m s.trace s.events) es) (K + 1) Q B move := by
  let root := Round.initial m s.trace s.events
  let privateRound := es.foldl (advance group B move) root
  have hi : Data group root (K * Q) B move := by
    have hh := hs.last.2
    rw [← hs.directions] at hh
    have h := round_initial m B move s.trace s.events hs.represented hs.legal hs.retired hs.last.1 hh
    exact initial_data group s.trace s.events (round_info (hs.directions ▸ h))
  have hp : Data group privateRound (K * Q) B move := data_fold group root es hi hB hm0 hm1 he
  obtain ⟨hx, hmarks⟩ := async_frame (B := B) group move root es
  exact history_publish s privateRound hs hQ hp.info hc hx hmarks

lemma async_fold {m K Q B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m)
    (es : List (List (OriginalEvent m))) (hs : History s K Q B move)
    (hQ : 0 < Q) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : CompleteRounds group Q B move s es) :
    History (es.foldl (fun t xs => runRound group B move (Round.initial m t.trace t.events) xs) s)
      (K + es.length) Q B move := by
  induction es generalizing s K with
  | nil => exact hs
  | cons e es ih =>
    obtain ⟨hle, hc, hrest⟩ := he
    have hout := async_round group s e hs hQ hB hm0 hm1 hle hc
    have h := ih _ hout hrest
    simpa only [List.foldl_cons, List.length_cons, Nat.add_right_comm K 1 es.length, Nat.add_assoc] using h

lemma async_history {m Q B : ℕ} {move : ℝ} (group : Fin m → Fin m)
    (es : List (List (OriginalEvent m))) (hQ : 0 < Q) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : CompleteRounds group Q B move (Round.initial m {} []) es) :
    History (runRounds group B move es) es.length Q B move := by
  simpa only [runRounds, zero_add] using
    async_fold group (Round.initial m {} []) es (initial_history m Q B move) hQ hB hm0 hm1 he

lemma local_async_valid (p : Params) (m Q : ℕ) (group : Fin m → Fin m)
    (rounds : List (List (OriginalEvent m)))
    (hQ : 0 < Q) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m Q group rounds) : spec.valid (localAsync p m Q group rounds) := by
  let q := tuned p m Q
  let K := horizon q
  let B := batchSize q
  let move : ℝ := 1 / divisor Q (Q - 1)
  let s := runRounds group B move rounds
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor Q (Q - 1) := by
    exact_mod_cast (show 1 ≤ divisor Q (Q - 1) by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor Q (Q - 1) := by linarith
  have hs : History s K Q B move := by
    have h := async_history group rounds hQ hB (show 0 ≤ move by positivity) ((div_le_one hc').2 hc) he.2
    rwa [he.1] at h
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal, history_structural hs hK hQ⟩

lemma local_async_budget (p : Params) (m Q : ℕ) (group : Fin m → Fin m)
    (rounds : List (List (OriginalEvent m))) (hQ : 0 < Q) :
    let q := localAsync p m Q group rounds
    budget q 0 = q.controls.waste + batchSize q * (horizon q * Q) := by
  let q := localAsync p m Q group rounds
  exact scaled_budget q Q Q (Q - 1) q.controls.waste hQ rfl

lemma local_async_success (p : Params) (m Q : ℕ) (group : Fin m → Fin m)
    (rounds : List (List (OriginalEvent m))) (hp : spec.valid (localAsync p m Q group rounds))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (localAsync p m Q group rounds) I O) :
    let q := localAsync p m Q group rounds
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (localAsync p m Q group rounds) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionLocalAsync
