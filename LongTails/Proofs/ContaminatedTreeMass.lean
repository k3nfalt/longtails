import LongTails.Proofs.ContaminatedTreeTracking
import LongTails.Proofs.ContaminatedTreeProbability

namespace LongTails.Proofs.ContaminatedTreeMass

open LongTails.Algorithms.LeonCalendar
open LongTails.Algorithms.LeonTuning (height iterations)
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open ContaminatedTreeTracking ContaminatedTreeProbability
open scoped Classical

def scan (v : ℕ → ℕ → ℝ) : List ℕ → ℕ → ℝ
  | [], _ => 0
  | l :: ls, t => v l t + scan v ls (t+1)

lemma scan_append (v : ℕ → ℕ → ℝ) (a b : List ℕ) (t : ℕ) :
    scan v (a++b) t = scan v a t + scan v b (t+a.length) := by
  induction a generalizing t with
  | nil => simp [scan]
  | cons l a ih => simp [scan,ih,add_left_comm,add_comm]

lemma total_scan (v : ℕ → ℕ → ℝ) (j t : ℕ) : total v j t = scan v (levels j) t := by
  induction j generalizing t with
  | zero => simp [scan,total,levels]
  | succ j ih =>
    simp only [total,levels,scan,scan_append,List.length_append,Fin.sum_univ_four,ih,child]
    norm_num
    ring_nf

lemma scan_range (v : ℕ → ℕ → ℝ) (ls : List ℕ) (t : ℕ) :
    scan v ls t = ∑ i ∈ Finset.range ls.length, v (ls[i]?.getD 0) (t+i) := by
  induction ls generalizing t with
  | nil => simp [scan]
  | cons l ls ih =>
    simp only [scan,List.length_cons,Finset.sum_range_succ', List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.add_zero, ih]
    rw [add_comm (v l t)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1; omega

lemma total_range (v : ℕ → ℕ → ℝ) (j : ℕ) :
    total v j 0 = ∑ i ∈ Finset.range (levels j).length, v ((levels j)[i]?.getD 0) i := by
  simp only [total_scan,scan_range,Nat.zero_add]

lemma damage_lt (p : Params) {Ω : Type*} (b : ℕ → Set Ω) (ω : Ω)
    (h : mass (fun i => weight p ((levels (height (network p)))[i]?.getD 0)) b
      (levels (height (network p))).length ω < 1) :
    damage (fun i => decide (ω ∈ b i)) (height (network p)) 0 < (iterations (network p):ℝ) := by
  let H := height (network p)
  let K := (iterations (network p):ℝ)
  let l (i : ℕ) := (levels H)[i]?.getD 0
  let a (i : ℕ) := if ω ∈ b i then weight p (l i) else 0
  have hK : 0 < K := by dsimp [K,iterations]; positivity
  have hsum : ∑ i ∈ Finset.range (levels H).length, a i < 1 := h
  have hn (i : ℕ) : 0 ≤ a i := by dsimp [a]; split <;> first | exact weight_nonneg _ _ | rfl
  have he (i : ℕ) (hi : i ∈ Finset.range (levels H).length) :
      (if decide (ω ∈ b i) = true then (4:ℝ)^(2*l i) else 0) = a i * K := by
    by_cases hb : ω ∈ b i
    · have hw := (Finset.single_le_sum (fun j _ => hn j) hi).trans_lt hsum
      simp only [a,hb,ite_true,weight] at hw
      have hr : (16:ℝ)^(l i) / K < 1 := (min_lt_iff.mp hw).resolve_left (lt_irrefl _)
      simp only [a,hb,decide_true,ite_true,weight,pow_mul]
      norm_num
      change (16:ℝ)^l i = min 1 ((16:ℝ)^l i / K) * K
      rw [min_eq_right hr.le,div_mul_cancel₀ _ hK.ne']
    · simp [hb,a]
  unfold damage
  rw [total_range]
  change (∑ i ∈ Finset.range (levels H).length, _) < K
  rw [Finset.sum_congr rfl he, ← Finset.sum_mul]
  simpa only [one_mul] using mul_lt_mul_of_pos_right hsum hK

end LongTails.Proofs.ContaminatedTreeMass
