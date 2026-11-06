import LongTails.Algorithms.SpikedSoftCutMethod
import LongTails.Proofs.SpikedSoftCutBisection

namespace LongTails.Proofs.SpikedSoftCutOuterInvariant

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutBisection

lemma nextState_radius (q : Params) (c : Config) (k : ℕ) (s : OuterState q) (r : ℕ → Space q) :
    radius q (nextState q c k s r) = 5*radius q s/8 := rfl

lemma nextState_invariant (q : Params) (c : Config) (k : ℕ) (s : OuterState q)
    (r : ℕ → Space q) (f : Space q → ℝ) (fstar z slope : ℝ)
    (hε : 0 < q.ε) (hr : 0 < radius q s)
    (hsaved : frozen q s = true → f (saved q s)-fstar ≤ q.ε)
    (hlocation : frozen q s = false → |z-center q s| ≤ radius q s)
    (hgap : 0 ≤ f (primalOutput q c s r)-fstar)
    (hcertificate : f (primalOutput q c s r)-fstar+slope*(z-center q s) ≤ q.ε/16)
    (hnoise : |scalarEstimate q c k r-slope| ≤ q.ε/(8*radius q s)) :
    (frozen q (nextState q c k s r) = true → f (saved q (nextState q c k s r))-fstar ≤ q.ε) ∧
    (frozen q (nextState q c k s r) = false → |z-center q (nextState q c k s r)| ≤ radius q (nextState q c k s r)) := by
  by_cases hf : frozen q s = true
  · constructor
    · intro _
      simpa only [nextState, saved, hf, Bool.true_eq, ite_true] using hsaved hf
    · intro h
      change (frozen q s || decide (|scalarEstimate q c k r| ≤ q.ε/(2*radius q s))) = false at h
      simp [hf] at h
  · have hf' : frozen q s = false := Bool.eq_false_iff.mpr hf
    have hl := hlocation hf'
    by_cases hsmall : |scalarEstimate q c k r| ≤ q.ε/(2*radius q s)
    · have hh := small_estimate_gap (f (primalOutput q c s r)-fstar) slope
        (scalarEstimate q c k r) (center q s) z q.ε (radius q s) hr hε.le hcertificate hl hnoise hsmall
      constructor
      · intro _
        simp only [nextState, saved, hf', Bool.false_eq_true, ite_false]
        linarith
      · intro h
        change (frozen q s || decide (|scalarEstimate q c k r| ≤ q.ε/(2*radius q s))) = false at h
        simp [hsmall] at h
    · constructor
      · intro h
        change (frozen q s || decide (|scalarEstimate q c k r| ≤ q.ε/(2*radius q s))) = true at h
        simp [hf', hsmall] at h
      · intro _
        rw [nextState_radius]
        change |z-(if 0 ≤ scalarEstimate q c k r then center q s-3*radius q s/8 else center q s+3*radius q s/8)| ≤ _
        by_cases he : 0 ≤ scalarEstimate q c k r
        · rw [ite_eq_left he]
          have hlarge : q.ε/(2*radius q s) < scalarEstimate q c k r := by
            simpa only [abs_of_nonneg he] using lt_of_not_ge hsmall
          exact left_shift_contains _ _ _ hr.le hl (positive_estimate_location _ _ _ _ _ _ _ hr hε hgap hcertificate hnoise hlarge)
        · rw [ite_eq_right he]
          have hlarge : scalarEstimate q c k r < -(q.ε/(2*radius q s)) := by
            have hh := lt_of_not_ge hsmall
            rw [abs_of_neg (lt_of_not_ge he)] at hh
            linarith
          exact right_shift_contains _ _ _ hr.le hl (negative_estimate_location _ _ _ _ _ _ _ hr hε hgap hcertificate hnoise hlarge)

lemma last_saved_gap (q : Params) (c : Config) (k : ℕ) (s : OuterState q)
    (r : ℕ → Space q) (f : Space q → ℝ) (fstar z slope δ : ℝ)
    (hf : frozen q s = false) (hG : 0 ≤ q.G)
    (hcertificate : f (primalOutput q c s r)-fstar+slope*(z-center q s) ≤ δ)
    (hlocation : |z-center q s| ≤ radius q s) (hslope : |slope| ≤ q.G) :
    f (saved q (nextState q c k s r))-fstar ≤ δ+q.G*radius q s := by
  have hh := final_midpoint_gap _ _ _ _ _ _ _ hG hcertificate hlocation hslope
  simpa only [nextState, saved, hf, Bool.false_eq_true, ite_false] using hh

end LongTails.Proofs.SpikedSoftCutOuterInvariant
