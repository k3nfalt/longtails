import LongTails.Algorithms.BirchCollectionMeta
import LongTails.Proofs.BirchCollectionPoolCertificate
import LongTails.Proofs.BirchCollectionMetaBounds
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionMeta

open LongTails.Algorithms.BirchCollectionMeta

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections (Params spec horizon batchSize)
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionPoolTrace
open LongTails.Proofs.BirchCollectionPoolPublish
open LongTails.Proofs.BirchCollectionPoolCertificate
open LongTails.Proofs.BirchCollectionPoolCounts (accepted_count_window)
open LongTails.Proofs.BirchCollectionMetaBounds
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma meta_data_step {m Q B : ℕ} (move : ℝ) (s : Pool m) (e : MetaEvent m)
    (hs : Data s B 1 Q (Q - 1) move) (hb : Bounds s Q) (he : MetaEnabled Q s e)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    Data (metaAdvance Q B move s e) B 1 Q (Q - 1) move := by
  cases e with
  | query w => exact data_issue s w hs hB hm0 hm1
  | reply w =>
    by_cases h : maxAge s + remaining s < Q
    · simpa only [metaAdvance, ite_eq_left h] using data_complete s w hs he
    · simpa only [metaAdvance, ite_eq_right h] using data_discard s w hs
  | sync ws =>
    obtain ⟨hupper, hdelay⟩ := accepted_count_window s ws Q he.1 hb.quota
    exact data_publish s ws hs he.1 (fun h => h) hupper
      (fun w hw => Nat.sub_le_sub_right (hdelay w hw) 1)

lemma meta_data {m Q B : ℕ} (move : ℝ) (events : List (MetaEvent m))
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : MetaLegal Q B move {} events) : Data (metaRun Q B move events) B 1 Q (Q - 1) move := by
  have aux (s : Pool m) (es : List (MetaEvent m)) (hs : Data s B 1 Q (Q - 1) move)
      (hb : Bounds s Q) (he : MetaLegal Q B move s es) :
      Data (es.foldl (metaAdvance Q B move) s) B 1 Q (Q - 1) move := by
    induction es generalizing s with
    | nil => exact hs
    | cons e es ih =>
      exact ih _ (meta_data_step move s e hs hb he.1 hB hm0 hm1)
        (meta_step move s e hb he.1) he.2
  exact aux {} events (initial_data m B 1 Q (Q - 1) move) ⟨fun _ => le_rfl, by
    simp [maxAge, age, remaining]⟩ he

lemma meta_valid (p : Params) (m Q : ℕ) (events : List (MetaEvent m))
    (hQ : 0 < Q) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m Q events) : spec.valid (metaLocal p m Q events) := by
  let q := tuned p m Q
  let B := batchSize q
  let K := horizon q
  let move : ℝ := 1 / divisor Q (Q - 1)
  let s := metaRun Q B move events
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor Q (Q - 1) := by
    exact_mod_cast (show 1 ≤ divisor Q (Q - 1) by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor Q (Q - 1) := by linarith
  have hs : Data s B 1 Q (Q - 1) move :=
    meta_data move events hB (by positivity) ((div_le_one hc').2 hc) he.1
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal,
    pool_certificate s hs hK Nat.one_pos hQ he.2⟩

lemma meta_budget (p : Params) (m Q : ℕ) (events : List (MetaEvent m)) (hQ : 0 < Q) :
    let q := metaLocal p m Q events
    budget q 0 = q.controls.waste + batchSize q * (horizon q * Q) := by
  let q := metaLocal p m Q events
  exact scaled_budget q 1 Q (Q - 1) q.controls.waste hQ rfl

lemma meta_success (p : Params) (m Q : ℕ) (events : List (MetaEvent m))
    (hp : spec.valid (metaLocal p m Q events))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (metaLocal p m Q events) I O) :
    let q := metaLocal p m Q events
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (metaLocal p m Q events) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionMeta
