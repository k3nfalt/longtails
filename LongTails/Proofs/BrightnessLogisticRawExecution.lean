import LongTails.Proofs.BrightnessLogisticRawDynamics
import LongTails.Proofs.Execution

open OracleTemplate
open LongTails.Setups.BrightnessLogisticRaw
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BrightnessLogisticRawExecution

open BrightnessLogisticRawDynamics

lemma execute_fails (p : Params) (hp : Valid p)
    (A : Algorithm (ℝ × Features p.d) ((ℝ × Features p.d) × Bool) (ℝ × Features p.d))
    (hA : family p.input A) (K : ℕ)
    (hK : K*p.H^2 ≤ p.R^2*(p.m*p.δ/8))
    (hslow : K*(p.threshold*Real.log p.R)*p.H^2 ≤ p.R^2*p.debt) (seed : A.Seed) :
    ¬ fits p.rows (execute { answer := fun _ q _ => answer p.rows q.2 } A (fun _ => K) seed) := by
  classical
  obtain ⟨η,point,hη,hinit,hquery,hupdate,hout⟩ := hA
  have hM := (scale_prices p hp (le_refl (p.threshold*Real.log p.R))).1
  have hf (j : ℕ) (hj : j ≤ K) : ¬ fits p.rows (iterate p η j) := by
    have hh : (j : ℝ) ≤ K := Nat.cast_le.mpr hj
    apply all_steps_fail p hp hη
    · exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans hK
    · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hM.le) (sq_nonneg _)).trans hslow
  let step := fun s => A.update s (answer p.rows (A.query s).2)
  have he : ∀ j ≤ K, point (step^[j] (A.initial seed)) = iterate p η j := by
    intro j
    induction j with
    | zero => intro; exact hinit seed
    | succ j ih =>
      intro hj
      have ht := Nat.le_of_succ_le hj
      rw [Function.iterate_succ_apply']
      let s := step^[j] (A.initial seed)
      have hh : point s = iterate p η j := ih ht
      change point (A.update s (answer p.rows (A.query s).2)) = _
      rw [hupdate,hquery]
      change (if (answer p.rows (point s)).2 then point s else
        point s + η • (answer p.rows (point s)).1) = _
      rw [hh]
      change (if decide (fits p.rows (iterate p η j)) then _ else _) = _
      rw [decide_eq_false (hf j ht)]
      exact (next p η j).symm
  rw [execute_iterate,hout,he K le_rfl]
  exact hf K le_rfl

lemma budget_limits (p : Params) (hp : Valid p) (K : ℕ)
    (h : K ≤ ⌊p.R^2*p.m*p.δ/(8*p.H^2) *
      min 1 (p.debt/(2*(1+|p.t| * p.D+p.H*‖p.w‖)*Real.log p.R))⌋₊) :
    K*p.H^2 ≤ p.R^2*(p.m*p.δ/8) ∧
      K*(p.threshold*Real.log p.R)*p.H^2 ≤ p.R^2*p.debt := by
  let B := 1+|p.t| * p.D+p.H*‖p.w‖
  let V := p.R^2*p.m*p.δ/(8*p.H^2)
  have hD := (abs_nonneg _).trans (hp.maxDC 0)
  have hH := hp.detailPos
  have hm := hp.minPos
  have hδ := hp.gapPos
  have hs := hp.debtPos
  have hl : 0 < Real.log p.R := lt_of_lt_of_le zero_lt_one hp.scale
  have hB : 0 < B := by dsimp [B]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hden : 0 < 2*B*Real.log p.R := by positivity
  have hcap : 0 ≤ V*min 1 (p.debt/(2*B*Real.log p.R)) := by positivity
  have hk : (K : ℝ) ≤ V*min 1 (p.debt/(2*B*Real.log p.R)) :=
    (Nat.cast_le.mpr h).trans (Nat.floor_le hcap)
  have hfirst := hk.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hV)
  have hnext := hk.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hV)
  constructor
  · simp only [mul_one] at hfirst
    have ht := (le_div_iff₀ (show 0 < 8*p.H^2 by positivity)).mp hfirst
    nlinarith only [ht]
  · have hh := mul_le_mul_of_nonneg_right hnext
      (show 0 ≤ p.threshold*Real.log p.R*p.H^2 from
        mul_nonneg (scale_prices p hp (le_refl _)).1.le (sq_nonneg _))
    rw [mul_assoc (K : ℝ) _ _]
    apply hh.trans
    dsimp only [V,B,Params.threshold]
    apply le_of_eq
    field_simp [hH.ne',hm.ne',hδ.ne',hl.ne',show 1+|p.t| * p.D+p.H*‖p.w‖ ≠ 0 from hB.ne']
    ring

end LongTails.Proofs.BrightnessLogisticRawExecution
