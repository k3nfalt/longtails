import LongTails.Algorithms.BirchWindow
import LongTails.Proofs.BirchNonEuclideanCausality

namespace LongTails.Proofs.BirchWindow

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point)
open LongTails.Algorithms.BirchWindow
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Proofs.BirchNonEuclideanExecution
open LongTails.Proofs.BirchNonEuclideanCausality (interpret_append queryCount_append)

lemma warm_calls (n : ℕ) : queryCount (warm n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [warm, queryCount_append, ih]; rfl

lemma code_calls (B K : ℕ) (η : ℝ) : queryCount (code B η K) = B - 1 + K := by
  induction K with
  | zero => simpa only [Nat.add_zero, code] using warm_calls (B - 1)
  | succ k ih => rw [code, queryCount_append, ih]; rfl

lemma program_calls (B K : ℕ) (hB : 0 < B) (η : ℝ) :
    (program B K η).oracleCalls = calls B K := by
  change queryCount (code B η K) = calls B K
  rw [code_calls]
  unfold calls
  omega

structure WindowReplay (p : Params) (B : ℕ) (η : ℝ) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (s : Memory p.d) (k : ℕ) : Prop where
  next : s.next = B - 1 + 4 * k + 1
  count : s.replies = calls B k
  points : ∀ i ≤ k, s.points (pointReg B i) = iterate p B η lmo response i
  raw : ∀ j < calls B k, s.vectors (replyReg B j) =
    response j (iterate p B η lmo response (source B j))

lemma warm_replay (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (n : ℕ) :
    let s := interpret p lmo response (warm n) (initialMemory p)
    s.next = n + 1 ∧ s.replies = n ∧ s.points 0 = p.x0 ∧
      ∀ j < n, s.vectors (j + 1) = response j p.x0 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
  | succ n ih =>
    rw [warm, interpret_append]
    let s := interpret p lmo response (warm n) (initialMemory p)
    obtain ⟨hn, hc, hp, hr⟩ : s.next = n + 1 ∧ s.replies = n ∧ s.points 0 = p.x0 ∧
      ∀ j < n, s.vectors (j + 1) = response j p.x0 := ih
    change (perform p lmo s (.query 0 0) (response s.replies (s.points 0))).next = n + 1 + 1 ∧
      (perform p lmo s (.query 0 0) (response s.replies (s.points 0))).replies = n + 1 ∧
      s.points 0 = p.x0 ∧
      ∀ j < n + 1, Function.update s.vectors s.next (response s.replies (s.points 0)) (j + 1) =
        response j p.x0
    refine ⟨by change s.next + 1 = _; rw [hn], by change s.replies + 1 = _; rw [hc], hp, ?_⟩
    intro j hj
    rw [hn, hc, hp]
    rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hj | rfl
    · rw [Function.update_of_ne (by omega), hr _ hj]
    · rw [Function.update_self]

lemma window_replay (p : Params) (B : ℕ) (hB : 0 < B) (η : ℝ)
    (lmo : Point p.d → Point p.d) (response : ℕ → Point p.d → Point p.d) (k : ℕ) :
    WindowReplay p B η lmo response
      (interpret p lmo response (code B η k) (initialMemory p)) k := by
  induction k with
  | zero =>
    rw [code]
    obtain ⟨hn, hc, hp, hr⟩ := warm_replay p lmo response (B - 1)
    refine ⟨by simpa only [Nat.mul_zero, Nat.add_zero] using hn,
      by simpa only [calls, Nat.add_zero] using hc, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      simpa only [pointReg, ite_eq_left, iterate] using hp
    · intro j hj
      have hj' : j < B - 1 := by simpa only [calls, Nat.add_zero] using hj
      rw [replyReg, ite_eq_left hj', show source B j = 0 by unfold source; omega, iterate]
      exact hr j hj'
  | succ k ih =>
    rw [code, interpret_append]
    let s := interpret p lmo response (code B η k) (initialMemory p)
    let n := B - 1 + 4 * k
    let r := calls B k
    let X := iterate p B η lmo response
    let terms := (List.range B).map (fun i => (1 / (B : ℝ), replyReg B (k + i)))
    let s₁ := perform p lmo s (.query 0 (pointReg B k)) (response s.replies (s.points (pointReg B k)))
    let s₂ := perform p lmo s₁ (.mix 0 terms) 0
    let s₃ := perform p lmo s₂ (.sharp 0 (n + 2)) 0
    let s₄ := perform p lmo s₃ (.move 0 (pointReg B k) (n + 3) η) 0
    change WindowReplay p B η lmo response s₄ (k + 1)
    have hnext : s.next = n + 1 := ih.next
    have hn₁ : s₁.next = n + 2 := by change s.next + 1 = _; omega
    have hn₂ : s₂.next = n + 3 := by change s₁.next + 1 = _; omega
    have hn₃ : s₃.next = n + 4 := by change s₂.next + 1 = _; omega
    have hr : source B r = k := by unfold source r calls; omega
    have hrreg : replyReg B r = n + 1 := by
      unfold replyReg r n calls
      split <;> omega
    have hpt : s.points (pointReg B k) = X k := ih.points k le_rfl
    have hvec₁ : s₁.vectors = Function.update s.vectors (n + 1) (response r (X k)) := by
      change Function.update s.vectors s.next (response s.replies (s.points (pointReg B k))) = _
      rw [hnext, ih.count, hpt]
    have hold (j : ℕ) (hj : j < r) : replyReg B j < n + 1 := by
      unfold replyReg n r calls at *
      split <;> omega
    have hraw (j : ℕ) (hj : j ≤ r) : s₁.vectors (replyReg B j) = response j (X (source B j)) := by
      rcases hj.lt_or_eq with hj | rfl
      · rw [hvec₁, Function.update_of_ne (ne_of_lt (hold j hj)), ih.raw j hj]
      · rw [hvec₁, hrreg, Function.update_self, hr]
    let avg := (1 / (B : ℝ)) • ∑ i : Fin B, response (k + i) (X (source B (k + i)))
    have havg : (terms.map (fun t => t.1 • s₁.vectors t.2)).sum = avg := by
      simp only [terms, avg, List.map_map, Function.comp_def]
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, smul_sum,
        Fin.sum_univ_eq_sum_range (fun i => (1 / (B : ℝ)) • response (k + i) (X (source B (k + i))))]
      exact sum_congr rfl (fun i hi => by rw [hraw _ (by
        have := mem_range.mp hi
        unfold r calls
        omega)])
    have hvec₂ : s₂.vectors = Function.update s₁.vectors (n + 2) avg := by
      change Function.update s₁.vectors s₁.next ((terms.map (fun t => t.1 • s₁.vectors t.2)).sum) = _
      rw [hn₁, havg]
    have hvec₃ : s₃.vectors = Function.update s₂.vectors (n + 3) (dualNorm p.N avg • lmo avg) := by
      change Function.update s₂.vectors s₂.next
        (dualNorm p.N (s₂.vectors (n + 2)) • lmo (s₂.vectors (n + 2))) = _
      rw [hn₂, hvec₂, Function.update_self]
    have hpoint : s₄.points = Function.update s.points (pointReg B (k + 1)) (X (k + 1)) := by
      change Function.update s.points s₃.next
        (s.points (pointReg B k) + η • s₃.vectors (n + 3)) = _
      rw [hn₃, hpt, hvec₃, Function.update_self]
      have he : n + 4 = pointReg B (k + 1) := by unfold pointReg n; split <;> omega
      rw [he]
      congr 1
      change X k + η • (dualNorm p.N avg • lmo avg) = iterate p B η lmo response (k + 1)
      rw [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change s₃.next + 1 = _
      rw [hn₃]
      unfold n
      omega
    · change s.replies + 1 = _
      rw [ih.count]
      unfold calls
      omega
    · intro j hj
      rcases hj.lt_or_eq with hj | rfl
      · have hne : pointReg B j ≠ pointReg B (k + 1) := by
          unfold pointReg
          split <;> split <;> omega
        rw [hpoint, Function.update_of_ne hne, ih.points _ (by omega)]
      · rw [hpoint, Function.update_self]
    · intro j hj
      have hj' : j ≤ r := by unfold r calls at *; omega
      have hlt : replyReg B j < n + 2 := by
        rcases hj'.lt_or_eq with hj' | rfl
        · exact (hold j hj').trans (by omega)
        · rw [hrreg]; omega
      change s₃.vectors (replyReg B j) = _
      rw [hvec₃, Function.update_of_ne (by omega), hvec₂,
        Function.update_of_ne (ne_of_lt hlt), hraw j hj']

lemma execute_window {Ω : Type} [MeasurableSpace Ω] (p : Params) (B K : ℕ) (hB : 0 < B)
    (hK : 0 < K) (η : ℝ) (lmo : Point p.d → Point p.d)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (i : Fin ((program B K η).outputCount + 1)) (ξ : ℕ → Ω) :
    execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p (program B K η) lmo)
      (fun _ => calls B K) i ξ = iterate p B η lmo (fun j x => g x (ξ j)) i.val := by
  rw [← program_calls B K hB η]
  apply (execute_interpret p (program B K η) lmo P g ξ i).trans
  exact (window_replay p B hB η lmo (fun j x => g x (ξ j)) K).points i.val
    (by have := i.isLt; change i.val < K - 1 + 1 at this; omega)

end LongTails.Proofs.BirchWindow
