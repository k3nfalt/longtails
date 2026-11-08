import LongTails.Proofs.BirchCollectionNestedRounds
import LongTails.Proofs.BirchCollectionLocal

namespace LongTails.Proofs.BirchCollectionNested

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Algorithms.BirchCollectionLocal (localOrdering)
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionNestedRounds
open LongTails.Proofs.BirchCollectionLocalRounds (History)
open LongTails.Algorithms.BirchCollectionLocal (tuned)
open LongTails.Proofs.BirchCollectionLocal (history_structural)
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma nested_valid (p : Params) (m Q : ℕ) (layout : Layout m) (arrivals : List (List (Fin m)))
    (hQ : 0 < Q) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (hK : arrivals.length = horizon (tuned p m Q)) (ha : ∀ order ∈ arrivals, order.length = Q) :
    spec.valid (nestedLocalAsync p m Q layout arrivals) := by
  let q := tuned p m Q
  let K := horizon q
  let B := batchSize q
  let move : ℝ := 1 / divisor Q (Q - 1)
  let s := runRounds layout Q B move arrivals
  have hK' : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor Q (Q - 1) := by
    exact_mod_cast (show 1 ≤ divisor Q (Q - 1) by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor Q (Q - 1) := by linarith
  have hs : History s K Q B move := by
    have h := nested_history layout arrivals hQ hB (show 0 ≤ move by positivity) ((div_le_one hc').2 hc) ha
    rwa [hK] at h
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal,
    history_structural hs hK' hQ⟩

lemma nested_budget (p : Params) (m Q : ℕ) (layout : Layout m)
    (arrivals : List (List (Fin m))) (hQ : 0 < Q) :
    let q := nestedLocalAsync p m Q layout arrivals
    budget q 0 = q.controls.waste + batchSize q * (horizon q * Q) := by
  let q := nestedLocalAsync p m Q layout arrivals
  exact scaled_budget q Q Q (Q - 1) q.controls.waste hQ rfl

lemma nested_success (p : Params) (m Q : ℕ) (layout : Layout m) (arrivals : List (List (Fin m)))
    (hp : spec.valid (nestedLocalAsync p m Q layout arrivals))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (nestedLocalAsync p m Q layout arrivals) I O) :
    let q := nestedLocalAsync p m Q layout arrivals
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (nestedLocalAsync p m Q layout arrivals) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionNested
