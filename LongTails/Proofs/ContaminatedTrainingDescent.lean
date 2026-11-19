import LongTails.Proofs.ContaminatedTrainingGeometry
import LongTails.Proofs.LeonAccuracy

namespace LongTails.Proofs.ContaminatedTrainingDescent

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (resolution radius height spacing iterations)
open LongTails.Algorithms
open ContaminatedParallelHistory ContaminatedParallelTrajectory ContaminatedParallelFailures
open ContaminatedTreeTracking ContaminatedTrainingGeometry LeonBlocks LeonBlockCover
open scoped Classical
variable {p : Params}

lemma bounded_decode (D : Data p) (s : Samples p) (t : ℕ) (y : Point p) :
    err D s t ≤ ‖(model D s t).training.anchors (level p t+1)-y‖ +
      radius (network p) (level p t) + ‖y-D.G (x D s t)‖ := by
  apply LeonAggregate.shifted_error
  exact mul_nonneg (by positivity) (LeonBatchTuning.resolution_pos _ D.valid.2.2.2.1).le

lemma tracking (D : Data p) (s : Samples p) (j t : ℕ) (ha : Aligned (level p) t (levels j)) :
    Tracked (resolution (network p)) (err D s) (failed D s) j t := by
  have hs := (LeonBatchTuning.resolution_pos (network p) D.valid.2.2.2.1).le
  induction j generalizing t with
  | zero => exact .leaf t
  | succ j ih =>
    have hc (i : Fin 4) : Aligned (level p) (child j t i) (levels j) := (child_alignment ha i.isLt).2
    have hl (i : Fin 4) := LeonTreeError.aligned_head (hc i)
    have hg (i : Fin 4) := child_geometry D s t j i ha
    refine .fork j t ?_ ?_ (fun i => ih _ (hc i))
    · intro i
      have hb := bounded_decode D s (child j t i) (D.G (x D s t))
      rw [hl i,(hg i).1, norm_sub_rev (D.G (x D s t))] at hb
      change _ ≤ err D s t + 8*4^j*resolution (network p) + _ at hb
      linarith only [hb,(hg i).2]
    · intro i hp hb
      apply decode_accurate D (trainOp p) s _ (of_decide_eq_false hb)
      change ‖(model D s (child j t i)).training.anchors (level p (child j t i)+1) -
        D.G (x D s (child j t i))‖ + _ ≤ radius (network p) (level p (child j t i))
      rw [hl i,(hg i).1]
      have hd := norm_sub_le_norm_sub_add_norm_sub (v D s t) (D.G (x D s t)) (D.G (x D s (child j t i)))
      rw [norm_sub_rev (D.G (x D s t))] at hd
      change _ ≤ err D s t + _ at hd
      unfold LeonTuning.radius
      linarith only [hp,hd,(hg i).2, mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := j)) hs, hs]

lemma total_error (D : Data p) (s : Samples p)
    (hm : ContaminatedTreeProbability.mass (fun t => ContaminatedTreeProbability.weight p (level p t))
      (bad D (trainOp p)) (levels (height (network p))).length s < 1) :
    leafMass (err D s) (height (network p)) 0 ≤ 17*(iterations (network p):ℝ)*resolution (network p) := by
  let H := height (network p)
  let K := (4:ℝ)^H
  let a := resolution (network p)
  have ha : 0 ≤ a := (LeonBatchTuning.resolution_pos _ D.valid.2.2.2.1).le
  have hK : 1 ≤ K := one_le_pow₀ (by norm_num)
  have hKa := mul_le_mul_of_nonneg_right hK ha
  have hal : Aligned (level p) 0 (levels H) := by intro k; simp [level,H]
  have hl := LeonTreeError.aligned_head hal
  have hmove := bounded_decode D s 0 (0 : Point p)
  rw [hl] at hmove
  change err D s 0 ≤ ‖(0:Point p)-0‖ + 8*K*a + ‖0-D.G p.x0‖ at hmove
  simp only [sub_self,norm_zero,zero_add,zero_sub,norm_neg] at hmove
  have hstart : ‖D.G p.x0‖ ≤ K*a := D.start_bound
  have hg (hb : failed D s 0 = false) : err D s 0 ≤ 2*a := by
    apply decode_accurate D (trainOp p) s 0 (of_decide_eq_false hb)
    change ‖(0:Point p)-D.G p.x0‖ + 2*a ≤ radius (network p) (level p 0)
    rw [hl,zero_sub,norm_neg]
    change _ ≤ 8*K*a
    linarith only [hstart,hKa,ha]
  have hh := leaf_error_sum ha (tracking D s H 0 hal)
    (by linarith only [hmove,hstart,hKa,ha] : err D s 0 ≤ 2*a+11*K*a) hg
  have hd := ContaminatedTreeMass.damage_lt p (bad D (trainOp p)) s hm
  have he : (iterations (network p):ℝ) = K := by simp [K,H,iterations]
  change damage (failed D s) H 0 < _ at hd
  rw [he] at hd ⊢
  change leafMass (err D s) H 0 ≤ K*(2*a)+15*a*damage (failed D s) H 0 at hh
  linarith only [hh,mul_le_mul_of_nonneg_left hd.le ha]

noncomputable abbrev hist (D : Data p) (s : Samples p) (t : ℕ) := (model D s t).training.history

lemma history_count (D : Data p) (s : Samples p) (t : ℕ)
    (ht : t ≤ (levels (height (network p))).length) :
    (hist D s t).length = ((levels (height (network p))).take t).count 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < (levels (height (network p))).length := by omega
    unfold hist
    rw [step,List.take_succ_eq_append_getElem hlt,List.count_append]
    by_cases hz : level p t = 0
    · have h := hz
      simp only [level,List.getElem?_eq_getElem hlt,Option.getD_some] at h
      simp [LeonTrajectory.applyEstimate,hz,h,(show (model D s t).training.history.length = _ from ih hlt.le)]
    · have h := hz
      simp only [level,List.getElem?_eq_getElem hlt,Option.getD_some] at h
      simp [LeonTrajectory.applyEstimate,hz,h,(show (model D s t).training.history.length = _ from ih hlt.le)]

lemma descent (D : Data p) (s : Samples p) (t : ℕ) :
    let a := resolution (network p) / p.L
    a * ((hist D s t).map (fun z => ‖D.G z.1‖)).sum ≤
      objective p D.f p.x0 - objective p D.f (x D s t) +
      2*a* (∑ i ∈ Finset.range t, if level p i = 0 then err D s i else 0) +
      (hist D s t).length*(p.L/2*a^2) := by
  let a := resolution (network p)/p.L
  have ha : 0 ≤ a := div_nonneg (LeonBatchTuning.resolution_pos _ D.valid.2.2.2.1).le D.valid.2.1.le
  induction t with
  | zero => simp [hist,x,model,state,initialModel,LeonTrajectory.initial]
  | succ t ih =>
    dsimp only at ih ⊢
    rw [Finset.sum_range_succ]
    by_cases hz : level p t = 0
    · have hx : x D s (t+1) = x D s t - (a / ‖v D s t‖) • v D s t := by
        unfold x; rw [step]; simp [LeonTrajectory.applyEstimate,hz,a]
      have hh : hist D s (t+1) = (x D s t,‖v D s t‖) :: hist D s t := by
        unfold hist; rw [step]; simp [LeonTrajectory.applyEstimate,hz]
      have hd := ParameterFreeNsgdmRun.descent_step D.gradient D.smooth D.valid.2.1.le a ha
        (x D s t) (v D s t)
      rw [← hx] at hd
      change _ ≤ _ - a*‖D.G (x D s t)‖ + 2*a*err D s t + _ at hd
      simp only [hh,hx,hz,↓reduceIte,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [← hx]
      dsimp only [a] at hd
      linarith only [ih,hd]
    · have hx : x D s (t+1) = x D s t := by unfold x; rw [step]; simp [LeonTrajectory.applyEstimate,hz]
      have hh : hist D s (t+1) = hist D s t := by unfold hist; rw [step]; simp [LeonTrajectory.applyEstimate,hz]
      simpa only [hh,hx,hz, ↓reduceIte,add_zero] using ih

end LongTails.Proofs.ContaminatedTrainingDescent
