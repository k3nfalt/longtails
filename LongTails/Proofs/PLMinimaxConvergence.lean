import LongTails.Proofs.PLMinimaxPhases
import LongTails.Proofs.PLMinimaxCubicDescent

open LongTails.Setups.NonconvexPLSecondOrder
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

lemma finite_potential_execution {A S : Type*} (step : S → S) (launch : A → S)
    (V : A → ℝ) (success : S → Prop) {δ c C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hV : ∀ a, 0 ≤ V a)
    (transition : ∀ a, ∃ (m : ℕ) (s : S), step^[m] (launch a) = s ∧
      ((success s ∧ (m : ℝ) ≤ c) ∨
        ∃ b, s = launch b ∧ V b ≤ V a - δ ∧ (m : ℝ) ≤ C * (V a - V b)))
    (a : A) : ∃ (t : ℕ) (s : S), step^[t] (launch a) = s ∧ success s ∧ (t : ℝ) ≤ c + C * V a := by
  have aux : ∀ (n : ℕ) (a : A), V a < (n : ℝ) * δ →
      ∃ (t : ℕ) (s : S), step^[t] (launch a) = s ∧ success s ∧ (t : ℝ) ≤ c + C * V a := by
    intro n
    induction n with
    | zero =>
      intro a ha
      simp only [Nat.cast_zero, zero_mul] at ha
      exact (not_lt_of_ge (hV a) ha).elim
    | succ n ih =>
      intro a ha
      obtain ⟨m, s, hm, hcase⟩ := transition a
      rcases hcase with ⟨hs, hc⟩ | ⟨b, hs, hdec, hcost⟩
      · refine ⟨m, s, hm, hs, ?_⟩
        exact hc.trans (le_add_of_nonneg_right (mul_nonneg hC (hV a)))
      · have hb : V b < (n : ℝ) * δ := by
          push_cast at ha
          linarith only [ha, hdec]
        obtain ⟨t, q, ht, hq, hbound⟩ := ih b hb
        refine ⟨t + m, q, ?_, hq, ?_⟩
        · rw [Function.iterate_add_apply, hm, hs, ht]
        · push_cast
          nlinarith only [hcost, hbound]
  obtain ⟨n, hn⟩ := exists_nat_gt (V a / δ)
  exact aux n a ((div_lt_iff₀ hδ).mp hn)

lemma outer_execution {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (s : State p)
    (hr : ‖regularizedGradient (gradient f) p.L s.center s.point‖ ≤ (tuning p).residualTolerance) :
    ∃ (t : ℕ) (r : State p),
      (exactStep p f)^[t] (cubicAdvance p s (f s.point, gradient f s.point, fderiv ℝ (gradient f) s.point)) = r ∧
      r.phase = .finished ∧ ‖gradient (value f) r.point.fst‖ ≤ p.ε ∧
      (∀ v, -(tuning p).curvature * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient (value f)) r.point.fst v⟫) ∧
      (t : ℝ) ≤ ((tuning p).refinementSteps + 1 : ℕ) *
        (1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
          4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) *
          (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L s.center -
            envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 + p.Δ)) := by
  classical
  let A := { s : State p // ‖regularizedGradient (gradient f) p.L s.center s.point‖ ≤ (tuning p).residualTolerance }
  let launch := fun a : A => cubicAdvance p a.val
    (f a.val.point, gradient f a.val.point, fderiv ℝ (gradient f) a.val.point)
  let E := envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L
  let V := fun a : A => E a.val.center - E p.x0 + p.Δ
  let success := fun r : State p => r.phase = .finished ∧ ‖gradient (value f) r.point.fst‖ ≤ p.ε ∧
    ∀ v, -(tuning p).curvature * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient (value f)) r.point.fst v⟫
  let c : ℝ := ((tuning p).refinementSteps + 1 : ℕ)
  let B := 8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
    4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)
  let δ := (tuning p).smoothness / 4 * (tuning p).threshold ^ 3
  have hp := tuning_positive hv
  have hM := hp.1
  have hs := hp.2.2.2.2.1
  have hmesh := hp.2.2.1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hV : ∀ a : A, 0 ≤ V a := by
    intro a
    have hh := setup_envelope_gap hv hf a.val.center
    change 0 ≤ E a.val.center - E p.x0 + p.Δ
    change E p.x0 - E a.val.center ≤ p.Δ at hh
    linarith only [hh]
  have transition : ∀ a : A, ∃ (m : ℕ) (r : State p), (exactStep p f)^[m] (launch a) = r ∧
      ((success r ∧ (m : ℝ) ≤ c) ∨
        ∃ b : A, r = launch b ∧ V b ≤ V a - δ ∧ (m : ℝ) ≤ (c * B) * (V a - V b)) := by
    intro a
    let g := (2 * p.L) • (a.val.center - a.val.point.fst)
    let H := envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) a.val.point) p.L)
      (tuning p).regularization
    let d := envelopeCubicStep g H (tuning p).smoothness
    let m := max 1 ⌈‖d‖ / (tuning p).mesh⌉₊
    have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    obtain ⟨w, hw, hrun⟩ := tracking_all_complete hv hf a.val.center d a.val.point m hm
      (decide (‖d‖ ≤ (tuning p).threshold)) a.property (tracking_mesh_bound hv d)
    change (exactStep p f)^[m * ((tuning p).refinementSteps + 1)] (launch a) = _ at hrun
    by_cases ht : ‖d‖ ≤ (tuning p).threshold
    · simp only [ht, decide_true, ↓reduceIte] at hrun
      refine ⟨m * ((tuning p).refinementSteps + 1), _, hrun, Or.inl ⟨?_, ?_⟩⟩
      · have hcert := setup_cubic_terminal hv hf a.val.center a.val.point a.property ht
        have hout := setup_output_certificate hv hf (a.val.center + d) w hw hcert.1 hcert.2
        exact ⟨rfl, hout⟩
      · have hm₁ : m = 1 := terminal_segment_count hv d ht
        simp only [hm₁, one_mul]
        exact le_rfl
    · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte] at hrun
      let b : A := ⟨{ center := a.val.center + d, point := w, phase := .track a.val.center d m m (tuning p).refinementSteps false }, hw⟩
      have hd := setup_cubic_descent hv hf a.val.center a.val.point a.property (lt_of_not_ge ht).le
      change E (a.val.center + d) - E a.val.center ≤ -(tuning p).smoothness / 4 * ‖d‖ ^ 3 at hd
      have hdecrease : (tuning p).smoothness / 4 * ‖d‖ ^ 3 ≤ E a.val.center - E (a.val.center + d) := by
        linarith only [hd]
      have hp₃ := pow_le_pow_left₀ hs.le (lt_of_not_ge ht).le 3
      have hscaled := mul_le_mul_of_nonneg_left hp₃ (show 0 ≤ (tuning p).smoothness / 4 by positivity)
      have hcharge := cubic_segment_charge hM hs hmesh (lt_of_not_ge ht).le hdecrease
      refine ⟨m * ((tuning p).refinementSteps + 1), launch b, hrun, Or.inr ⟨b, rfl, ?_, ?_⟩⟩
      · change E (a.val.center + d) - E p.x0 + p.Δ ≤
          E a.val.center - E p.x0 + p.Δ - δ
        change δ ≤ (tuning p).smoothness / 4 * ‖d‖ ^ 3 at hscaled
        linarith only [hscaled, hdecrease]
      · have hh := mul_le_mul_of_nonneg_left hcharge hc
        change c * (m : ℝ) ≤ c * (B * (E a.val.center - E (a.val.center + d))) at hh
        rw [Nat.cast_mul]
        change (m : ℝ) * c ≤ (c * B) *
          ((E a.val.center - E p.x0 + p.Δ) - (E (a.val.center + d) - E p.x0 + p.Δ))
        nlinarith only [hh]
  obtain ⟨t, r, ht, hsuccess, hcost⟩ := finite_potential_execution (exactStep p f) launch V success
    hδ (mul_nonneg hc hB) hV transition ⟨s, hr⟩
  refine ⟨t, r, ht, hsuccess.1, hsuccess.2.1, hsuccess.2.2, ?_⟩
  change (t : ℝ) ≤ c * (1 + B * V ⟨s, hr⟩)
  convert hcost using 1
  ring

lemma initialized_execution {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) :
    ∃ (t : ℕ) (r : State p),
      (exactStep p f)^[t] { center := p.x0, point := WithLp.toLp 2 (p.x0, p.y0), phase := .initialize 0 0 } = r ∧
      r.phase = .finished ∧ ‖gradient (value f) r.point.fst‖ ≤ p.ε ∧
      (∀ v, -(tuning p).curvature * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient (value f)) r.point.fst v⟫) ∧
      (t : ℝ) ≤ (((tuning p).primalSteps + 1) * ((tuning p).dualSteps + 1) : ℕ) +
        ((tuning p).refinementSteps + 1 : ℕ) *
        (1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
          4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) * p.Δ) := by
  obtain ⟨y, u, hy0, hu0, hu, hy, hstart⟩ := initialization_sequences p f
  let w := WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps, y (tuning p).dualSteps)
  let s : State p := { center := p.x0, point := w, phase := .initialize (tuning p).dualSteps (tuning p).primalSteps }
  have hr := initialization_residual_certificate hv hf y u hy0 hu0 hu hy hstart
  obtain ⟨t, r, ht, hphase, hgrad, hcurv, hcost⟩ := outer_execution hv hf s hr
  let I := ((tuning p).primalSteps + 1) * ((tuning p).dualSteps + 1)
  have hinit := initialization_last_query p f p.x0 y u hu hy hstart
  rw [hu0, hy0] at hinit
  have hcount : I = ((tuning p).dualSteps * ((tuning p).primalSteps + 1) + (tuning p).primalSteps) + 1 := by
    dsimp [I]
    ring
  have hlaunch : (exactStep p f)^[I]
      { center := p.x0, point := WithLp.toLp 2 (p.x0, p.y0), phase := .initialize 0 0 } =
      cubicAdvance p s (f s.point, gradient f s.point, fderiv ℝ (gradient f) s.point) := by
    rw [hcount, Function.iterate_succ_apply', hinit]
    exact initialize_final_end p f p.x0 _ _
  refine ⟨t + I, r, ?_, hphase, hgrad, hcurv, ?_⟩
  · rw [Function.iterate_add_apply, hlaunch, ht]
  · change (t : ℝ) ≤ ((tuning p).refinementSteps + 1 : ℕ) *
      (1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
        4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) *
        (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 -
          envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 + p.Δ)) at hcost
    simp only [sub_self, zero_add] at hcost
    push_cast
    dsimp [I]
    push_cast
    push_cast at hcost
    linarith only [hcost]

lemma output_accuracy_of_budget {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (K : ℕ)
    (hK : (((tuning p).primalSteps + 1) * ((tuning p).dualSteps + 1) : ℕ) +
        ((tuning p).refinementSteps + 1 : ℕ) *
        (1 + (8 / ((tuning p).smoothness * (tuning p).threshold ^ 3) +
          4 / ((tuning p).smoothness * (tuning p).mesh ^ 3)) * p.Δ) ≤ (K : ℝ))
    (seed : (k : ℕ) → oracle.Seed k) :
    ‖gradient (value f) (output p oracle K seed)‖ ≤ p.ε ∧
      ∀ v, -(tuning p).curvature * ‖v‖ ^ 2 ≤
        ⟪v, fderiv ℝ (gradient (value f)) (output p oracle K seed) v⟫ := by
  obtain ⟨t, r, ht, hphase, hgrad, hcurv, hcost⟩ := initialized_execution hv hf
  have hle : t ≤ K := by exact_mod_cast hcost.trans hK
  have he : output p oracle K seed = r.point.fst := by
    rw [output_eq_iterate hf K seed, ← Nat.sub_add_cancel hle, Function.iterate_add_apply, ht,
      iterate_finished p f r hphase]
  rw [he]
  exact ⟨hgrad, hcurv⟩

end OracleTemplate.PLMinimax
