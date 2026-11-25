import LongTails.Proofs.StochasticEllSmoothRun
import LongTails.Proofs.HighProbabilityExecution
import LongTails.Proofs.IIDBlocks

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticEllSmoothUpper

open OracleTemplate QueryPlan
open LongTails.Setups.StochasticEllSmoothNonconvex LongTails.Algorithms.StochasticEllSmoothMedoid
open LongTails.Proofs.HighProbabilityAdapted LongTails.Proofs.HighProbabilityExecution
open LongTails.Proofs.StochasticEllSmoothRun LongTails.Proofs.StochasticEllSmoothStep
open LongTails.Algorithms.HighProbabilityStationarity (stepRepeat samplePlan)

section Eval

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def est (K n : ℕ) (g : E → Ω → E) (x : E) (z : Fin ((2 * K + 2) * n) → Ω) : E :=
  estimate K n (fun i => g x (z i))

lemma method_eval (ℓ : ℝ → ℝ) (ε : ℝ) (K n T : ℕ) (x0 : E) (g : E → Ω → E) (ξ : ℕ → Ω) :
    sampledEval g ξ (method ℓ ε K n T x0) 0 =
      finish x0 (traj (roundMap ℓ ε (est K n g)) (x0, false) (blocks ((2 * K + 2) * n) ξ) T) := by
  unfold method
  rw [sampledEval_map, sampledEval_stepRepeat]
  congr 1
  set body := fun s : E × Bool => (samplePlan s.1 ((2 * K + 2) * n)).map
    (fun w => roundStep ℓ ε s (estimate K n w))
  have hbody (s : E × Bool) (call : ℕ) : sampledEval g ξ (body s) call =
      roundStep ℓ ε s (estimate K n (fun i => g s.1 (ξ (call + i.val)))) := by
    simp only [body, sampledEval_map, sampledEval_samplePlan]
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [stepIter_succ, hbody, ih]
    have hidx : ∀ i : Fin ((2 * K + 2) * n),
        0 + (2 * K + 2) * n * T + i.val = T * ((2 * K + 2) * n) + i.val := by
      intro i; ring
    simp only [traj, roundMap, est, blocks, hidx]

end Eval

section Params

variable (q : Params)

lemma logb_ge (hv : spec.valid q) : 1 ≤ Real.logb 2 (2 + horizon q) := by
  have hT : 0 ≤ horizon q := by
    unfold horizon
    have := hv.2.2.1.2.2 q.ε hv.2.2.2.2.2.2.2
    have := hv.2.2.2.2.2.2.1
    positivity
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  linarith

lemma horizon_nonneg (hv : spec.valid q) : 0 ≤ horizon q := by
  unfold horizon
  have := hv.2.2.1.2.2 q.ε hv.2.2.2.2.2.2.2
  have := hv.2.2.2.2.2.2.1
  positivity

lemma two_pow_halfBlocks (hv : spec.valid q) :
    (2 + horizon q) ^ (64 / (2 - q.ρ)) ≤ (2 : ℝ) ^ halfBlocks q := by
  have hρ2 : 0 < 2 - q.ρ := by linarith [hv.2.1]
  have hT := horizon_nonneg q hv
  have hK : 64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ) ≤ (halfBlocks q : ℝ) := Nat.le_ceil _
  have h1 : (2 + horizon q) ^ (64 / (2 - q.ρ)) =
      (2 : ℝ) ^ (64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ)) := by
    rw [show 64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ) =
      Real.logb 2 (2 + horizon q) * (64 / (2 - q.ρ)) by ring, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
  rw [h1, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hK

lemma halfBlocks_ge (hv : spec.valid q) : 3 ≤ halfBlocks q := by
  have hρ0 := hv.1
  have hρ2 : 0 < 2 - q.ρ := by linarith [hv.2.1]
  have hL := logb_ge q hv
  have h : (3 : ℝ) ≤ 64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ) := by
    rw [le_div_iff₀ hρ2]; nlinarith
  have := h.trans (Nat.le_ceil (64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ)))
  exact_mod_cast this

lemma steps_le (hv : spec.valid q) : (steps q : ℝ) ≤ 72 * horizon q + 1 := by
  have hT := horizon_nonneg q hv
  unfold steps
  push_cast
  linarith [Nat.floor_le (show 0 ≤ 72 * horizon q by positivity)]

lemma steps_gt (hv : spec.valid q) : q.Δ < steps q * (q.ε ^ 2 / (72 * q.ℓ q.ε)) := by
  have hε := hv.2.2.2.2.2.2.2
  have hl := hv.2.2.1.2.2 q.ε hε
  have h1 : 72 * horizon q < (steps q : ℝ) := by
    unfold steps; push_cast; exact Nat.lt_floor_add_one _
  have he : horizon q * (q.ε ^ 2 / q.ℓ q.ε) = q.Δ := by unfold horizon; field_simp
  have h2 : 72 * horizon q * (q.ε ^ 2 / (72 * q.ℓ q.ε)) = q.Δ := by
    rw [← he]; field_simp
  have hpos : 0 < q.ε ^ 2 / (72 * q.ℓ q.ε) := by positivity
  nlinarith [mul_lt_mul_of_pos_right h1 hpos]

lemma steps_small (hv : spec.valid q) : 72 * (steps q : ℝ) ≤ (2 + horizon q) ^ (32 : ℝ) := by
  have hT := horizon_nonneg q hv
  have hs := steps_le q hv
  have h1 : (2 + horizon q) ^ (32 : ℝ) = (2 + horizon q) ^ (32 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [h1]
  have h2 : (2 + horizon q) * 2 ^ 31 ≤ (2 + horizon q) ^ 32 := by
    have h3 : (2 : ℝ) ^ 31 ≤ (2 + horizon q) ^ 31 := pow_le_pow_left₀ (by norm_num) (by linarith) 31
    calc (2 + horizon q) * 2 ^ 31 ≤ (2 + horizon q) * (2 + horizon q) ^ 31 :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = (2 + horizon q) ^ 32 := by ring
  nlinarith

lemma tail_term (hv : spec.valid q) :
    (steps q : ℝ) * (q.ε / 8 / 22 * (1 / 2) ^ (halfBlocks q + 1)) ≤ q.ε / 8 := by
  have hε := hv.2.2.2.2.2.2.2
  have hρ2 : 0 < 2 - q.ρ := by linarith [hv.2.1]
  have hT := horizon_nonneg q hv
  have hK := two_pow_halfBlocks q hv
  have h32 : (2 + horizon q) ^ (32 : ℝ) ≤ (2 + horizon q) ^ (64 / (2 - q.ρ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    rw [le_div_iff₀ hρ2]; linarith [hv.1]
  have hs := steps_small q hv
  have hK' : (steps q : ℝ) ≤ 22 * 2 ^ (halfBlocks q + 1) := by
    rw [pow_succ]; nlinarith
  have hp : (0 : ℝ) < (1 / 2) ^ (halfBlocks q + 1) := by positivity
  have hq : (2 : ℝ) ^ (halfBlocks q + 1) * (1 / 2) ^ (halfBlocks q + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have : (steps q : ℝ) * (1 / 2) ^ (halfBlocks q + 1) ≤ 22 := by
    nlinarith [mul_le_mul_of_nonneg_right hK' hp.le]
  have he : (steps q : ℝ) * (q.ε / 8 / 22 * (1 / 2) ^ (halfBlocks q + 1)) =
      q.ε / 8 / 22 * ((steps q : ℝ) * (1 / 2) ^ (halfBlocks q + 1)) := by ring
  rw [he]
  have hc : 0 ≤ q.ε / 8 / 22 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hc]

noncomputable def fallbackBound : ℝ := q.ε * (1 + (16 * horizon q) ^ (1 / (2 - q.ρ)))

lemma fail_term (hv : spec.valid q) :
    fallbackBound q * ((steps q : ℝ) * (1 / 2) ^ (2 * halfBlocks q + 2)) ≤ q.ε / 4 := by
  have hε := hv.2.2.2.2.2.2.2
  have hρ2 : 0 < 2 - q.ρ := by linarith [hv.2.1]
  have hT := horizon_nonneg q hv
  have hK := two_pow_halfBlocks q hv
  set a := 1 / (2 - q.ρ) with ha
  have ha0 : 0 < a := by positivity
  have hs := steps_small q hv
  have h32 : (2 + horizon q) ^ (32 : ℝ) ≤ (2 + horizon q) ^ (64 / (2 - q.ρ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    rw [le_div_iff₀ hρ2]; linarith [hv.1]
  have hfb : 1 + (16 * horizon q) ^ a ≤ 2 * (2 + horizon q) ^ (64 / (2 - q.ρ)) := by
    have h1 : (16 * horizon q) ^ a ≤ ((2 + horizon q) ^ (64 : ℕ)) ^ a := by
      apply Real.rpow_le_rpow (by positivity) _ ha0.le
      have : 16 * horizon q ≤ 2 + horizon q + 15 * horizon q := by linarith
      have h2 : (2 + horizon q) * 1 ≤ (2 + horizon q) ^ 64 := by
        have := one_le_pow₀ (n := 63) (show (1 : ℝ) ≤ 2 + horizon q by linarith)
        calc (2 + horizon q) * 1 ≤ (2 + horizon q) * (2 + horizon q) ^ 63 :=
              mul_le_mul_of_nonneg_left this (by linarith)
          _ = (2 + horizon q) ^ 64 := by ring
      have h3 : 16 * horizon q ≤ (2 + horizon q) ^ 16 := by
        have : (16 : ℝ) * horizon q ≤ 16 * (2 + horizon q) := by linarith
        have h4 : (16 : ℝ) ≤ (2 + horizon q) ^ 4 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ 2 + horizon q by
            linarith) 4
          norm_num at this ⊢; linarith
        have h5 : (2 + horizon q) ^ 4 * (2 + horizon q) ≤ (2 + horizon q) ^ 16 := by
          rw [← pow_succ]
          exact pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith
      have h6 : (2 + horizon q) ^ 16 ≤ (2 + horizon q) ^ 64 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h7 : ((2 + horizon q) ^ (64 : ℕ)) ^ a = (2 + horizon q) ^ (64 / (2 - q.ρ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ha]
      congr 1; push_cast; ring
    have h8 : (1 : ℝ) ≤ (2 + horizon q) ^ (64 / (2 - q.ρ)) :=
      Real.one_le_rpow (by linarith) (by positivity)
    linarith
  have hprod : 4 * (steps q : ℝ) * (1 + (16 * horizon q) ^ a) ≤ (2 : ℝ) ^ (2 * halfBlocks q + 2) := by
    have e : (2 : ℝ) ^ (2 * halfBlocks q + 2) = 4 * (2 ^ halfBlocks q * 2 ^ halfBlocks q) := by
      rw [show 2 * halfBlocks q + 2 = halfBlocks q + halfBlocks q + 2 by ring, pow_add, pow_add]
      norm_num; ring
    rw [e]
    have hst : 2 * (steps q : ℝ) ≤ 2 ^ halfBlocks q := by
      nlinarith [h32.trans hK]
    have hS0 : (0 : ℝ) ≤ steps q := Nat.cast_nonneg _
    have hfb0 : 0 ≤ 1 + (16 * horizon q) ^ a := by positivity
    have := mul_le_mul hst (hfb.trans (by nlinarith [hK] : 2 * (2 + horizon q) ^ (64 / (2 - q.ρ)) ≤
      2 * 2 ^ halfBlocks q)) (by positivity) (by positivity)
    nlinarith
  have hq : (2 : ℝ) ^ (2 * halfBlocks q + 2) * (1 / 2) ^ (2 * halfBlocks q + 2) = 1 := by
    rw [← mul_pow]; norm_num
  have hp : (0 : ℝ) < (1 / 2) ^ (2 * halfBlocks q + 2) := by positivity
  unfold fallbackBound
  rw [← ha]
  have h1 : 4 * ((steps q : ℝ) * (1 + (16 * horizon q) ^ a) * (1 / 2) ^ (2 * halfBlocks q + 2)) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hprod hp.le]
  nlinarith

lemma block_ok (hv : spec.valid q) :
    3 * q.σ / (blockSize q : ℝ) ^ ((q.p - 1) / q.p) ≤ q.ε / 8 / 1536 := by
  have hε := hv.2.2.2.2.2.2.2
  have hp1 : 1 < q.p := hv.2.2.2.1
  have hσ : 0 ≤ q.σ := hv.2.2.2.2.2.1
  set r := q.p / (q.p - 1)
  have hr : 0 < r := div_pos (by linarith) (by linarith)
  have hn0 : (0 : ℝ) < blockSize q := by unfold blockSize; positivity
  rcases hσ.eq_or_lt with h0 | hσ0
  · rw [← h0]; simp; positivity
  have hX : (2 ^ 16 * q.σ / q.ε) ^ r ≤ (blockSize q : ℝ) := by
    unfold blockSize; push_cast
    linarith [Nat.le_ceil ((2 ^ 16 * q.σ / q.ε) ^ r)]
  have he : (q.p - 1) / q.p = 1 / r := by simp only [r]; field_simp
  have hroot : 2 ^ 16 * q.σ / q.ε ≤ (blockSize q : ℝ) ^ ((q.p - 1) / q.p) := by
    rw [he]
    have := Real.rpow_le_rpow (by positivity) hX (by positivity : (0 : ℝ) ≤ 1 / r)
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hr.ne', Real.rpow_one] at this
  have hpos : 0 < (blockSize q : ℝ) ^ ((q.p - 1) / q.p) := by positivity
  rw [div_le_iff₀ hpos]
  have : q.ε / 8 / 1536 * (2 ^ 16 * q.σ / q.ε) = 2 ^ 16 / 12288 * q.σ := by field_simp; norm_num
  nlinarith [mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ q.ε / 8 / 1536)]

lemma calls_le (hv : spec.valid q) :
    ((2 * halfBlocks q + 2) * blockSize q * steps q : ℕ) ≤
      ⌈2 ^ 15 * (1 + horizon q) * (1 + (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
        Real.logb 2 (2 + horizon q) / (2 - q.ρ)⌉₊ := by
  have hρ2 : 0 < 2 - q.ρ := by linarith [hv.2.1]
  have hρ0 := hv.1
  have hT := horizon_nonneg q hv
  have hL := logb_ge q hv
  have hX : 0 ≤ (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1)) := by
    have := hv.2.2.2.2.2.1; have := hv.2.2.2.2.2.2.2; positivity
  have hK : (halfBlocks q : ℝ) ≤ 64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ) + 1 := by
    unfold halfBlocks
    have := Nat.ceil_lt_add_one (show 0 ≤ 64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ) by positivity)
    linarith
  have hn : (blockSize q : ℝ) ≤ 2 * (1 + (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1))) := by
    unfold blockSize; push_cast
    have := Nat.ceil_lt_add_one hX
    linarith
  have hs : (steps q : ℝ) ≤ 72 * (1 + horizon q) := by have := steps_le q hv; linarith
  generalize Real.logb 2 (2 + horizon q) = L at hL hK ⊢
  generalize (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1)) = X at hX hn ⊢
  generalize horizon q = H at hT hs ⊢
  have hK2 : 2 * (halfBlocks q : ℝ) + 2 ≤ 136 * L / (2 - q.ρ) := by
    have h4 : 4 ≤ 8 * L / (2 - q.ρ) := by rw [le_div_iff₀ hρ2]; nlinarith
    have e1 : 136 * L / (2 - q.ρ) = 128 * L / (2 - q.ρ) + 8 * L / (2 - q.ρ) := by ring
    have e2 : 2 * (64 * L / (2 - q.ρ) + 1) = 128 * L / (2 - q.ρ) + 2 := by ring
    rw [e1]
    linarith
  have hc : (((2 * halfBlocks q + 2) * blockSize q * steps q : ℕ) : ℝ) ≤
      2 ^ 15 * (1 + H) * (1 + X) * L / (2 - q.ρ) := by
    push_cast
    have h1 : (2 * (halfBlocks q : ℝ) + 2) * blockSize q * steps q ≤
        (136 * L / (2 - q.ρ)) * (2 * (1 + X)) * (72 * (1 + H)) := by
      apply mul_le_mul (mul_le_mul hK2 hn (by positivity) (by positivity)) hs (by positivity)
        (by positivity)
    have h2 : (136 * L / (2 - q.ρ)) * (2 * (1 + X)) * (72 * (1 + H)) =
        19584 * (1 + H) * (1 + X) * L / (2 - q.ρ) := by ring
    have h3 : 19584 * (1 + H) * (1 + X) * L / (2 - q.ρ) ≤
        2 ^ 15 * (1 + H) * (1 + X) * L / (2 - q.ρ) := by
      apply div_le_div_of_nonneg_right _ hρ2.le
      have : 0 ≤ (1 + H) * (1 + X) * L := by positivity
      nlinarith
    linarith
  exact_mod_cast hc.trans (Nat.le_ceil _)

end Params

section Main

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma est_measurable (K n : ℕ) {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (est K n g)) := by
  unfold est estimate blockMeans
  refine OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
    (Measurable.of_eval fun i => ?_)
  refine (Finset.measurable_sum _ fun l _ => ?_).const_smul _
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma ell_norm_measurable {ℓ : ℝ → ℝ} (hmono : ∀ u v, 0 ≤ u → u ≤ v → ℓ u ≤ ℓ v) :
    Measurable (fun v : E => ℓ (3 * ‖v‖)) := by
  have hm : Monotone (fun t : ℝ => ℓ (max t 0)) := fun a b hab =>
    hmono _ _ (le_max_right _ _) (max_le_max hab le_rfl)
  have he : (fun v : E => ℓ (3 * ‖v‖)) = fun v => (fun t : ℝ => ℓ (max t 0)) (3 * ‖v‖) := by
    funext v
    show ℓ (3 * ‖v‖) = ℓ (max (3 * ‖v‖) 0)
    rw [max_eq_left (by positivity)]
  rw [he]
  exact hm.measurable.comp (measurable_const.mul measurable_norm)

omit [CompleteSpace E] in
lemma roundMap_measurable {Z : Type} [MeasurableSpace Z] (ℓ : ℝ → ℝ) (ε : ℝ)
    (hℓ : Measurable (fun v : E => ℓ (3 * ‖v‖))) {e : E → Z → E}
    (he : Measurable (Function.uncurry e)) :
    Measurable (Function.uncurry (roundMap ℓ ε e)) := by
  let V : (E × Bool) × Z → E := fun w => e w.1.1 w.2
  have hV : Measurable V := he.comp (measurable_fst.fst.prodMk measurable_snd)
  have hset1 : MeasurableSet {w : (E × Bool) × Z | w.1.2 = true} :=
    measurable_fst.snd (measurableSet_singleton true)
  have hset2 : MeasurableSet {w : (E × Bool) × Z | ‖V w‖ ≤ ε / 2} :=
    measurableSet_le hV.norm measurable_const
  have hstep : Measurable (fun w : (E × Bool) × Z =>
      ((w.1.1 - (1 / (2 * ℓ (3 * ‖V w‖))) • V w, false) : E × Bool)) := by
    refine Measurable.prodMk ?_ measurable_const
    exact measurable_fst.fst.sub (((measurable_const.mul (hℓ.comp hV)).const_div 1).smul hV)
  have h2 : Measurable (fun w : (E × Bool) × Z =>
      if ‖V w‖ ≤ ε / 2 then ((w.1.1, true) : E × Bool)
      else (w.1.1 - (1 / (2 * ℓ (3 * ‖V w‖))) • V w, false)) :=
    Measurable.ite hset2 (measurable_fst.fst.prodMk measurable_const) hstep
  have h3 : Measurable (fun w : (E × Bool) × Z => if w.1.2 = true then w.1
      else if ‖V w‖ ≤ ε / 2 then ((w.1.1, true) : E × Bool)
      else (w.1.1 - (1 / (2 * ℓ (3 * ‖V w‖))) • V w, false)) :=
    Measurable.ite hset1 measurable_fst h2
  exact h3

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma finish_measurable (x0 : E) : Measurable (finish (E := E) x0) := by
  unfold finish
  exact Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_fst
    measurable_const

lemma blocks_measurable' (N : ℕ) : Measurable (blocks (Ω := Ω) N) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_pi_apply _

end Main

noncomputable def output (q : Params) (g : q.E → q.Ω → q.E)
    (b : ℕ → Fin ((2 * halfBlocks q + 2) * blockSize q) → q.Ω) : q.E :=
  finish q.x0 (traj (roundMap q.ℓ q.ε (est (halfBlocks q) (blockSize q) g)) (q.x0, false) b
    (steps q))

lemma output_measurable (q : Params) (hv : spec.valid q) {g : q.E → q.Ω → q.E}
    (hgm : Measurable (Function.uncurry g)) : Measurable (output q g) :=
  (finish_measurable q.x0).comp (traj_measurable' (roundMap_measurable q.ℓ q.ε
    (ell_norm_measurable hv.2.2.1.1) (est_measurable _ _ hgm)) _ _)

lemma round_bounds' (q : Params) (hv : spec.valid q) (ν : Measure q.Ω) [IsProbabilityMeasure ν]
    {f : q.E → ℝ} {g : q.E → q.Ω → q.E} (hgm : Measurable (Function.uncurry g)) (x : q.E)
    (hgi : Integrable (g x) ν) (hmean : (∫ ω, g x ω ∂ν) = gradient f x)
    (hpi : Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) ν)
    (hpm : (∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂ν) ≤ q.σ ^ q.p) :
    (Measure.pi fun _ : Fin ((2 * halfBlocks q + 2) * blockSize q) => ν).real
        {z | q.ε / 8 < err f (est (halfBlocks q) (blockSize q) g) x z} ≤
        (1 / 2) ^ (2 * halfBlocks q + 2) ∧
      Integrable (excess f (est (halfBlocks q) (blockSize q) g) (q.ε / 8) x)
        (Measure.pi fun _ : Fin ((2 * halfBlocks q + 2) * blockSize q) => ν) ∧
      (∫ z, excess f (est (halfBlocks q) (blockSize q) g) (q.ε / 8) x z
          ∂(Measure.pi fun _ : Fin ((2 * halfBlocks q + 2) * blockSize q) => ν)) ≤
        q.ε / 8 / 22 * (1 / 2) ^ (halfBlocks q + 1) := by
  have hn0 : 0 < blockSize q := by unfold blockSize; omega
  have hε := hv.2.2.2.2.2.2.2
  exact round_bounds ν g hgm x (gradient f x) hgi hmean hv.2.2.2.1 hv.2.2.2.2.1
    hv.2.2.2.2.2.1 hpi hpm (halfBlocks q) (blockSize q) (halfBlocks_ge q hv) hn0
    (by positivity) (block_ok q hv)

set_option maxHeartbeats 400000 in
lemma expected_bound (q : Params) (hv : spec.valid q) (ν : Measure q.Ω) [IsProbabilityMeasure ν]
    {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ q.ℓ ‖gradient f x‖) (hΔ : ∀ x, f q.x0 - f x ≤ q.Δ)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) ν)
    (hmean : ∀ x, (∫ ω, g x ω ∂ν) = gradient f x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) ν)
    (hpm : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂ν) ≤ q.σ ^ q.p) :
    Integrable (fun b => ‖gradient f (output q g b)‖)
        (Measure.infinitePi fun _ : ℕ =>
          Measure.pi fun _ : Fin ((2 * halfBlocks q + 2) * blockSize q) => ν) ∧
      (∫ b, ‖gradient f (output q g b)‖ ∂(Measure.infinitePi fun _ : ℕ =>
          Measure.pi fun _ : Fin ((2 * halfBlocks q + 2) * blockSize q) => ν)) ≤ q.ε := by
  have hε : 0 < q.ε := hv.2.2.2.2.2.2.2
  have hreg := hv.2.2.1
  have hρ2 : q.ρ < 2 := hv.2.1
  set K := halfBlocks q
  set N := (2 * K + 2) * blockSize q
  set T := steps q
  set e := est K (blockSize q) g
  set F := roundMap q.ℓ q.ε e
  set μ := Measure.pi fun _ : Fin N => ν
  set μb := Measure.infinitePi fun _ : ℕ => μ
  set α := q.ε / 8
  set H := α / 22 * (1 / 2) ^ (K + 1)
  set θ : ℝ := (1 / 2) ^ (2 * K + 2)
  have hgcont : Continuous (gradient f) := hdiff.continuous
  have hFm : Measurable (Function.uncurry F) :=
    roundMap_measurable q.ℓ q.ε (ell_norm_measurable hreg.1) (est_measurable K _ hgm)
  have hround (x : q.E) := round_bounds' q hv ν hgm x (hgi x) (hmean x) (hpi x) (hpm x)
  have herr : Measurable (fun w : (q.E × Bool) × (Fin N → q.Ω) => err f e w.1.1 w.2) :=
    (((est_measurable K _ hgm).comp (measurable_fst.fst.prodMk measurable_snd)).sub
      (hgcont.measurable.comp measurable_fst.fst)).norm
  let h : q.E × Bool → (Fin N → q.Ω) → ℝ := fun s z => excess f e α s.1 z
  have hhm : Measurable (Function.uncurry h) :=
    Measurable.ite (measurableSet_lt measurable_const herr) herr measurable_const
  have hsum := adapted_sum μ hFm (q.x0, false) (h := h) hhm (fun s z => excess_nonneg f e α s.1 z)
    (fun s => (hround s.1).2.1) (H := H) (fun s => (hround s.1).2.2) T
  have hAm : MeasurableSet {w : (q.E × Bool) × (Fin N → q.Ω) | α < err f e w.1.1 w.2} :=
    measurableSet_lt measurable_const herr
  have hunion := adapted_union μ hFm (q.x0, false) (A := fun s z => α < err f e s.1 z) hAm
    (θ := θ) (fun s => (hround s.1).1) T
  have hG0 := initial_gradient_bound f q.ℓ q.ρ q.x0 q.Δ q.ε hρ2 hreg hε hgrad hdiff hH hΔ
  set Bad := {b' : ℕ → Fin N → q.Ω | ∃ j < T, α < err f e (traj F (q.x0, false) b' j).1 (b' j)}
  have hBadm : MeasurableSet Bad := by
    have : Bad = ⋃ j ∈ Finset.range T, (fun b : ℕ → Fin N → q.Ω => (traj F (q.x0, false) b j, b j)) ⁻¹'
        {w : (q.E × Bool) × (Fin N → q.Ω) | α < err f e w.1.1 w.2} := by
      ext b; simp [Bad]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun j _ =>
      ((traj_measurable' hFm _ j).prodMk (measurable_pi_apply j)) hAm
  have hpt (b : ℕ → Fin N → q.Ω) : ‖gradient f (output q g b)‖ ≤ q.ε / 2 + q.ε / 8 +
      ∑ j ∈ Finset.range T, h (traj F (q.x0, false) b j) (b j) +
      fallbackBound q * Bad.indicator (fun _ => (1 : ℝ)) b :=
    output_bound q.ℓ q.ε e q.x0 b hreg hρ2.le hε hgrad hdiff hH hΔ T (steps_gt q hv)
      (G0 := fallbackBound q) (by unfold fallbackBound horizon; exact hG0)
  have hRi : Integrable (fun b => q.ε / 2 + q.ε / 8 +
      ∑ j ∈ Finset.range T, h (traj F (q.x0, false) b j) (b j) +
      fallbackBound q * Bad.indicator (fun _ => (1 : ℝ)) b) μb :=
    ((integrable_const _).add hsum.1).add (((integrable_const _).indicator hBadm).const_mul _)
  have hΨm : Measurable (fun b => ‖gradient f (output q g b)‖) :=
    hgcont.measurable.norm.comp (output_measurable q hv hgm)
  have hΨi : Integrable (fun b => ‖gradient f (output q g b)‖) μb :=
    hRi.mono' hΨm.aestronglyMeasurable (Filter.Eventually.of_forall fun b => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt b)
  refine ⟨hΨi, ?_⟩
  have hA1 : Integrable (fun b => q.ε / 2 + q.ε / 8 +
      ∑ j ∈ Finset.range T, h (traj F (q.x0, false) b j) (b j)) μb :=
    (integrable_const _).add hsum.1
  have hA2 : Integrable (fun b => fallbackBound q * Bad.indicator (fun _ => (1 : ℝ)) b) μb :=
    ((integrable_const _).indicator hBadm).const_mul _
  have hfb : 0 ≤ fallbackBound q := by
    unfold fallbackBound
    have := horizon_nonneg q hv
    positivity
  calc (∫ b, ‖gradient f (output q g b)‖ ∂μb)
      ≤ ∫ b, (q.ε / 2 + q.ε / 8 + ∑ j ∈ Finset.range T, h (traj F (q.x0, false) b j) (b j) +
          fallbackBound q * Bad.indicator (fun _ => (1 : ℝ)) b) ∂μb := integral_mono hΨi hRi hpt
    _ = q.ε / 2 + q.ε / 8 + (∫ b, ∑ j ∈ Finset.range T, h (traj F (q.x0, false) b j) (b j) ∂μb) +
          fallbackBound q * μb.real Bad := by
        rw [integral_add hA1 hA2, integral_add (integrable_const _) hsum.1, integral_const,
          probReal_univ, one_smul, integral_const_mul, integral_indicator_const _ hBadm,
          smul_eq_mul, mul_one]
    _ ≤ q.ε / 2 + q.ε / 8 + T * H + fallbackBound q * (T * θ) := by
        gcongr
        exact hsum.2
    _ ≤ q.ε := by
        have h1 := tail_term q hv
        have h2 := fail_term q hv
        simp only [H, α, θ, T, K] at *
        linarith

lemma execute_eq (q : Params) (hv : spec.valid q) {g : q.E → q.Ω → q.E}
    (P : ProbabilityMeasure (ℕ → q.Ω)) (w : Unit × (ℕ → q.Ω)) :
    execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (LongTails.Algorithms.StochasticEllSmoothMedoid.algorithm q)
      (fun _ => ⌈2 ^ 15 * (1 + q.Δ * q.ℓ q.ε / q.ε ^ 2) *
        (1 + (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
        Real.logb 2 (2 + q.Δ * q.ℓ q.ε / q.ε ^ 2) / (2 - q.ρ)⌉₊) w.1 w.2 =
      output q g (blocks ((2 * halfBlocks q + 2) * blockSize q) w.2) := by
  have hb : (2 * halfBlocks q + 2) * blockSize q * steps q ≤
      ⌈2 ^ 15 * (1 + q.Δ * q.ℓ q.ε / q.ε ^ 2) * (1 + (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
        Real.logb 2 (2 + q.Δ * q.ℓ q.ε / q.ε ^ 2) / (2 - q.ρ)⌉₊ := calls_le q hv
  unfold LongTails.Algorithms.StochasticEllSmoothMedoid.algorithm
  rw [execute_sampledPlan_of_le _ _ _ _ _ _ _ g w.1 w.2 hb]
  exact method_eval q.ℓ q.ε (halfBlocks q) (blockSize q) (steps q) q.x0 g w.2

lemma block_law_measure {Ω' : Type} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (P : Measure (ℕ → Ω')) [IsProbabilityMeasure P]
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω') => ξ k) ν P) (n : ℕ) :
    P.map (blocks n) = Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => ν := by
  have h := (OracleTemplate.FiniteVariance.infinite_block_law ν P hiid.independent
    hiid.marginal n).map_eq
  have hfun : blocks (Ω := Ω') n =
      fun ξ : ℕ → Ω' => fun k : ℕ => fun i : Fin n => ξ (k * n + i.val) := rfl
  rw [hfun]
  exact h

lemma block_law {Ω' : Type} [MeasurableSpace Ω'] (ν : ProbabilityMeasure Ω')
    (P : ProbabilityMeasure (ℕ → Ω'))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω') => ξ k) (ν : Measure Ω') (P : Measure (ℕ → Ω'))) (n : ℕ) :
    (P : Measure (ℕ → Ω')).map (blocks n) =
      Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => (ν : Measure Ω') :=
  block_law_measure (ν : Measure Ω') (P : Measure (ℕ → Ω')) hiid n

set_option maxHeartbeats 1000000 in
lemma successful_output (q : Params) (hv : spec.valid q) {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _))
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ q.ℓ ‖gradient f x‖) (hΔ : ∀ x, f q.x0 - f x ≤ q.Δ)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) (ν : Measure q.Ω))
    (hmean : ∀ x, (∫ ω, g x ω ∂(ν : Measure q.Ω)) = gradient f x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ q.p) (ν : Measure q.Ω))
    (hpm : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ q.p ∂(ν : Measure q.Ω)) ≤ q.σ ^ q.p) :
    spec.successful q f
      (fun w : Unit × (ℕ → q.Ω) =>
        output q g (blocks ((2 * halfBlocks q + 2) * blockSize q) w.2))
      ⟨(unitLaw : Measure Unit).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩ := by
  have hbound := expected_bound q hv (ν : Measure q.Ω) hgrad hdiff hH hΔ hgm hgi hmean hpi hpm
  have hmapP := block_law ν P hiid ((2 * halfBlocks q + 2) * blockSize q)
  have hU : (unitLaw : Measure Unit) = Measure.dirac () := rfl
  have hsnd : ((unitLaw : Measure Unit).prod (P : Measure (ℕ → q.Ω))).map Prod.snd =
      (P : Measure _) := by
    rw [Measure.map_snd_prod, hU]; simp
  have hΨm : Measurable (fun b => ‖gradient f (output q g b)‖) :=
    hdiff.continuous.measurable.norm.comp (output_measurable q hv hgm)
  have hbm := blocks_measurable' (Ω := q.Ω) ((2 * halfBlocks q + 2) * blockSize q)
  refine ⟨(output_measurable q hv hgm).comp (hbm.comp measurable_snd), ?_, ?_⟩
  · have h1 := hbound.1
    rw [← hmapP, ← hsnd, Measure.map_map hbm measurable_snd] at h1
    exact h1.comp_measurable (hbm.comp measurable_snd)
  · have hm1 : AEStronglyMeasurable (fun b => ‖gradient f (output q g b)‖)
        (((unitLaw : Measure Unit).prod (P : Measure (ℕ → q.Ω))).map
          (blocks ((2 * halfBlocks q + 2) * blockSize q) ∘ Prod.snd)) :=
      hΨm.aestronglyMeasurable
    have h2 := integral_map (f := fun b => ‖gradient f (output q g b)‖)
      (hbm.comp measurable_snd).aemeasurable hm1
    rw [← Measure.map_map hbm measurable_snd, hsnd, hmapP] at h2
    change (∫ w, ‖gradient f (output q g (blocks ((2 * halfBlocks q + 2) * blockSize q) w.2))‖
      ∂((unitLaw : Measure Unit).prod (P : Measure (ℕ → q.Ω)))) ≤ q.ε
    rw [show (fun w : Unit × (ℕ → q.Ω) =>
        ‖gradient f (output q g (blocks ((2 * halfBlocks q + 2) * blockSize q) w.2))‖) =
        fun w => (fun b => ‖gradient f (output q g b)‖)
          ((blocks ((2 * halfBlocks q + 2) * blockSize q) ∘ Prod.snd) w) from rfl, ← h2]
    exact hbound.2

theorem convergence : Convergence spec (fun q _ =>
    ⌈2 ^ 15 * (1 + q.Δ * q.ℓ q.ε / q.ε ^ 2) * (1 + (2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1))) *
      Real.logb 2 (2 + q.Δ * q.ℓ q.ε / q.ε ^ 2) / (2 - q.ρ)⌉₊) := by
  refine ⟨fun q => LongTails.Algorithms.StochasticEllSmoothMedoid.algorithm q,
    fun q hv f O hadm => ?_, fun _ _ => trivial⟩
  obtain ⟨g, ν, P, hiid, hO, hgrad, hdiff, hH, hΔ, hgm, hgi, hmean, hpi, hpm⟩ := hadm
  subst hO
  have hsucc := successful_output q hv ν P hiid hgrad hdiff hH hΔ hgm hgi hmean hpi hpm
  intro A result
  have hres : result = fun w => output q g (blocks ((2 * halfBlocks q + 2) * blockSize q) w.2) :=
    funext fun w => execute_eq q hv P w
  rw [hres]
  exact hsucc

end LongTails.Proofs.StochasticEllSmoothUpper
