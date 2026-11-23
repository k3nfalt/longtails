import LongTails.Proofs.ContaminatedParallelTiming
import LongTails.Proofs.ContaminatedTrainingProbability

namespace LongTails.Proofs.ContaminatedParallelBudget

open DistributedTemplate
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (resolution height iterations blockSize)
open LongTails.Algorithms.LeonCalendar (levels)
open ContaminatedParallelSchedule ContaminatedValidationCalendar ContaminatedParallelTiming ContaminatedCalendarBudget

lemma calendar_size (p : Params) (z : Seed p) :
    (((operations p z).map (fun o => 1+o.level)).sum) ≤ 6*iterations (network p) := by
  let H := height (network p)
  let K := iterations (network p)
  let xs := candidateIndices p z
  let vs := validationOps H none xs
  have h (ls : List Operation) : (ls.map (fun o => 1+o.level)).sum = ls.length+(ls.map Operation.level).sum := by
    induction ls with
    | nil => simp
    | cons o ls ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega
  have hv : (vs.map Operation.level).sum ≤ H+K := validate_width H xs (indices_sorted p z)
  have hc : vs.length ≤ K := (validate_length H none xs).le.trans ((indices_length p z).trans (min_le_left _ _))
  have hH : H ≤ K := by
    have hh : ∀ n : ℕ, n+1 ≤ 4^n := by
      intro n; induction n with
      | zero => decide
      | succ n ih => rw [pow_succ]; omega
    exact (Nat.le_succ _).trans (hh H)
  have ht := levels_linear H
  change _ ≤ 2*K at ht
  unfold operations
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,Operation.level]
  change _ + (vs.map (fun o => 1+o.level)).sum ≤ 6*K
  rw [h]
  change ((levels H).map (fun l => 1+l)).sum + (vs.length+(vs.map Operation.level).sum) ≤ 6*K
  omega

lemma calendar_precision (p : Params) (z : Seed p) :
    (((operations p z).map (Operation.precision p)).sum:ℝ) ≤
      34*((iterations (network p):ℝ)+confidence p*min (iterations (network p):ℝ) (confidence p)) := by
  let K := (iterations (network p):ℝ)
  let q := (confidence p:ℝ)
  let xs := candidateIndices p z
  have hc : (xs.length:ℝ) ≤ min K q := by dsimp only [K,q,xs]; exact_mod_cast indices_length p z
  have ht := levels_precision p
  unfold operations
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,Operation.precision,
    validate_precision,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_list_sum]
  change _ + (xs.length:ℝ) * (2*q) ≤ 34*(K+q*min K q)
  change _ ≤ 32*(K+q*min K q) at ht
  nlinarith only [ht,mul_le_mul_of_nonneg_left hc (show 0 ≤ q by positivity),show 0 ≤ K by positivity]

lemma sum_cost (p : Params) (hh : ∀ i, 0 < p.h i) (ls : List Operation) :
    (ls.map (cost p)).sum ≤ 2^26 * ((ls.map (Operation.precision p)).sum:ℕ) * computeUnit p +
      16 * ((ls.map (fun o => 1+o.level)).sum:ℕ) * baseTime p := by
  induction ls with
  | nil => simp
  | cons o ls ih =>
    have h := cost_bound p hh o (ContaminatedTrainingProbability.precision_pos p o)
    apply (add_le_add h ih).trans_eq
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    ring

lemma sufficient (p : Params) (hh : ∀ i, 0 < p.h i) (z : Seed p) :
    let K := 1+⌈2^19*p.L*p.Δ/p.ε^2⌉₊
    let q := 4+⌈Real.log (1/p.failure)⌉₊
    ((operations p z).map (cost p)).sum ≤
      2^34*((K+q*min K q:ℕ):Time)*(Finset.univ.sup p.h+
        (2^18*(∑ i, (p.h i:ℝ)*p.σ i^2)/((p.n:ℝ)^2*p.ε^2)).toNNReal) +
      512*(K:Time)*(((1+Nat.log2 p.n:ℕ):Time)*Finset.univ.sup p.h + p.l +
        p.b*(64+((p.d+p.n-1)/p.n)*(8+Nat.log2 ((p.n:ℕ)*(p.d+1))):ℕ)) := by
  dsimp only
  let K := 1+⌈2^19*p.L*p.Δ/p.ε^2⌉₊
  let q := confidence p
  let I := iterations (network p)
  have he : 2*p.L*p.Δ / resolution (network p)^2 = 2^19*p.L*p.Δ/p.ε^2 := by
    unfold resolution
    change 2*p.L*p.Δ / (p.ε/512)^2 = _
    rw [div_pow,div_div_eq_mul_div]; ring
  have hI : I ≤ 4*K := by
    have h := LeonBatchTuning.iterations_upper (network p)
    change I ≤ 4*(1+⌈2*p.L*p.Δ/resolution (network p)^2⌉₊) at h
    simpa only [he] using h
  have hmin : min I q ≤ 4*min K q := by
    rcases le_total K q with h|h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans hI
    · rw [min_eq_right h]; exact (min_le_right _ _).trans (by omega)
  have hprec : ((operations p z).map (Operation.precision p)).sum ≤ 34*(I+q*min I q) := by
    dsimp only [I,q]; exact_mod_cast calendar_precision p z
  have hp : 2^26*((operations p z).map (Operation.precision p)).sum ≤ 2^34*(K+q*min K q) := by
    have hx := Nat.mul_le_mul_left q hmin
    nlinarith only [hprec,hI,hx,Nat.zero_le K,Nat.zero_le (q*min K q)]
  have hw := calendar_size p z
  change _ ≤ 6*I at hw
  have hs : 16*((operations p z).map (fun o => 1+o.level)).sum ≤ 512*K := by omega
  have hu : variance p = 2^18*(∑ i, (p.h i:ℝ)*p.σ i^2)/((p.n:ℝ)^2*p.ε^2) := by
    unfold variance resolution
    change _ / ((p.n:ℝ)^2*(p.ε/512)^2) = _
    rw [div_pow,← mul_div_assoc,div_div_eq_mul_div]; ring
  apply (sum_cost p hh _).trans
  change _ ≤ 2^34*((K+q*min K q:ℕ):Time)*_ + 512*(K:Time)*baseTime p
  rw [← hu]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ zero_le
    exact_mod_cast hp
  · apply mul_le_mul_of_nonneg_right _ zero_le
    exact_mod_cast hs

end LongTails.Proofs.ContaminatedParallelBudget
