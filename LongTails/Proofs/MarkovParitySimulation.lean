import LongTails.Proofs.MarkovParityProgress
import LongTails.Proofs.AbcHardExecution

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovParitySimulation

open MarkovParityProgress AbcChain AbcHardFunction AbcHardGeometry AbcHardOracle
open AbcHardSimulation AbcHardExecution

variable {d n : ℕ} {St : Type*}

def draw (m : ℕ) (z : Color) : ℝ := if accepts m z then 0 else 2

noncomputable def response (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 x : Space d) (z : Color) : Space d :=
  reply S (fun _ => q) π x0 x (draw (stage (sel π (toUnit S x0 x))) z)

noncomputable def prefixResponse (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (r : ℕ) (x0 x : Space d) (z : Color) : Space d :=
  simReply S (fun _ => q) π r x0 x (draw (stageUpTo r (sel π (toUnit S x0 x))) z)

lemma prefixResponse_congr (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d)
    (r : ℕ) (x0 x : Space d) (z : Color)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) :
    prefixResponse S q π r x0 x z = prefixResponse S q ρ r x0 x z := by
  have hs := stageUpTo_congr r (sel π (toUnit S x0 x)) (sel ρ (toUnit S x0 x))
    (fun i hi => by rw [sel_apply, sel_apply, h i hi])
  unfold prefixResponse
  rw [hs, simReply_prefix S _ π ρ r x0 x _ h]

lemma response_eq_prefix (S : Scale) (q : ℝ) (hq : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) (z : ℕ → Color) (t : ℕ)
    (hhit : ‖toUnit S x0 x‖ ≤ 2 * radius n →
      ∀ i : Fin (n + 1), progress z t ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4) :
    response S q π x0 x (z t) = prefixResponse S q π (progress z (t + 1)) x0 x (z t) := by
  unfold response prefixResponse
  by_cases hw : 2 * radius n ≤ ‖toUnit S x0 x‖
  · rw [reply_outside S _ π x0 x _ hw, simReply_outside S _ π _ x0 x _ hw]
  · push Not at hw
    let w := toUnit S x0 x
    have hsm := hhit hw.le
    have hmono : progress z t ≤ progress z (t + 1) := progress_mono z (Nat.le_succ t)
    have hst := stageUpTo_eq (progress z (t + 1)) (sel π w) (fun i hi => hsm i (by omega))
    have hs : stage (sel π w) ≤ progress z t := by
      rw [← stageUpTo_eq _ _ hsm]
      exact stageUpTo_le _ _
    change reply S _ π x0 x (draw (stage (sel π w)) _) =
      simReply S _ π _ x0 x (draw (stageUpTo _ (sel π w)) _)
    rw [hst]
    unfold reply simReply
    change knownPart S π _ x0 x + _ = knownPart S π (stageUpTo _ (sel π w)) x0 x + _
    rw [hst]
    congr 1
    by_cases hlt : stage (sel π w) < progress z (t + 1)
    · rw [ite_eq_left hlt, visibleGrad_eq π _ w (fun i hi => small_of_stage _ i hi)]
      rfl
    · rw [ite_eq_right hlt]
      have heq : stage (sel π w) = progress z t := by omega
      have hm : accepts (progress z t) (z t) = false := by
        cases hm : accepts (progress z t) (z t) with
        | false => rfl
        | true =>
          have hstep : progress z (t + 1) = progress z t + 1 := by simp [progress, hm]
          omega
      simp [draw, heq, hm, coin, show ¬ (2 : ℝ) ≤ q by linarith]

noncomputable def runPrefix (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (z : ℕ → Color) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := runPrefix S q π x0 query update initial z t
    update s (prefixResponse S q π (progress z (t + 1)) x0 (query s) (z t))

lemma runPrefix_congr (S : Scale) (q : ℝ) (π ρ : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (z : ℕ → Color) (t : ℕ)
    (h : ∀ i : Fin (n + 1), i.val < progress z t → π i = ρ i) :
    runPrefix S q π x0 query update initial z t = runPrefix S q ρ x0 query update initial z t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm : progress z t ≤ progress z (t + 1) := progress_mono z (Nat.le_succ t)
    simp only [runPrefix, ih (fun i hi => h i (by omega)), prefixResponse_congr S q π ρ _ x0 _ _ h]

noncomputable def runActual (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (z : ℕ → Color) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := runActual S q π x0 query update initial z t
    update s (response S q π x0 (query s) (z t))

lemma run_eq (S : Scale) (q : ℝ) (hq : q ≤ 1) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d)
    (query : St → Space d) (update : St → Space d → St) (initial : St) (z : ℕ → Color) (N : ℕ)
    (hhit : ∀ t < N, let x := query (runPrefix S q π x0 query update initial z t)
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), progress z t ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4) :
    runActual S q π x0 query update initial z N = runPrefix S q π x0 query update initial z N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [runActual, runPrefix, ih (fun t ht => hhit t (by omega)),
      response_eq_prefix S q hq π x0 _ z N (hhit N (by omega))]

end LongTails.Proofs.MarkovParitySimulation
