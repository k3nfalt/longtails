import LongTails.Algorithms.PLMinimaxMethod
import LongTails.Proofs.Execution

open LongTails.Setups.NonconvexPLSecondOrder

namespace OracleTemplate.PLMinimax

noncomputable def exactStep (p : Params) (f : Space p → ℝ) (s : State p) : State p :=
  methodUpdate p s (f s.point, gradient f s.point, fderiv ℝ (gradient f) s.point)

lemma output_eq_iterate {p : Params} {f : Space p → ℝ} {oracle}
    (hf : spec.admissible p f oracle) (K : ℕ) (seed : (k : ℕ) → oracle.Seed k) :
    output p oracle K seed =
      ((exactStep p f)^[K] { center := p.x0, point := WithLp.toLp 2 (p.x0, p.y0), phase := .initialize 0 0 }).point.fst := by
  have he := execute_eq_of_answer_eq oracle
    (fun w => (f w, gradient f w, fderiv ℝ (gradient f) w))
    (fun k w seed => hf.2.2.2.2.2.2.2.2 k seed w) (method p) K () seed
  have hi := execute_iterate (fun w : Space p => (f w, gradient f w, fderiv ℝ (gradient f) w))
    (method p) K ()
  exact he.trans hi

lemma exactStep_finished (p : Params) (f : Space p → ℝ) (s : State p)
    (hs : s.phase = .finished) : exactStep p f s = s := by
  simp [exactStep, methodUpdate, hs]

lemma iterate_finished (p : Params) (f : Space p → ℝ) (s : State p)
    (hs : s.phase = .finished) (n : ℕ) : (exactStep p f)^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, exactStep_finished p f s hs]

lemma initialize_prefix (p : Params) (f : Space p → ℝ) (z : p.E) (y : p.F)
    (u : ℕ → p.E) (j : ℕ)
    (hu : ∀ n, u (n + 1) = u n - (1 / (9 * p.L)) •
      ((gradient f (WithLp.toLp 2 (u n, y))).fst + (2 * p.L) • (u n - z)))
    (n : ℕ) (hn : n ≤ (tuning p).primalSteps) :
    (exactStep p f)^[n] { center := z, point := WithLp.toLp 2 (u 0, y), phase := .initialize j 0 } =
      { center := z, point := WithLp.toLp 2 (u n, y), phase := .initialize j n } := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hi : n < (tuning p).primalSteps := by omega
    simp [exactStep, methodUpdate, hi, hu n]

lemma initialize_stage_end (p : Params) (f : Space p → ℝ) (z x : p.E) (y : p.F)
    (j : ℕ) (hj : j < (tuning p).dualSteps) :
    exactStep p f { center := z, point := WithLp.toLp 2 (x, y), phase := .initialize j (tuning p).primalSteps } =
      { center := z, point := WithLp.toLp 2 (x, y + (1 / (2 * p.L)) •
        (gradient f (WithLp.toLp 2 (x, y))).snd), phase := .initialize (j + 1) 0 } := by
  classical
  simp [exactStep, methodUpdate, hj]

lemma initialize_final_end (p : Params) (f : Space p → ℝ) (z x : p.E) (y : p.F) :
    exactStep p f { center := z, point := WithLp.toLp 2 (x, y), phase := .initialize (tuning p).dualSteps (tuning p).primalSteps } =
      cubicAdvance p { center := z, point := WithLp.toLp 2 (x, y), phase := .initialize (tuning p).dualSteps (tuning p).primalSteps }
        (f (WithLp.toLp 2 (x, y)), gradient f (WithLp.toLp 2 (x, y)),
          fderiv ℝ (gradient f) (WithLp.toLp 2 (x, y))) := by
  classical
  simp [exactStep, methodUpdate]

lemma tracking_prefix (p : Params) (f : Space p → ℝ) (z origin d : p.E)
    (u : ℕ → Space p) (m j : ℕ) (terminal : Bool)
    (hu : ∀ n, u (n + 1) = u n + residualNewtonStep
      (regularizedGradient (gradient f) p.L z (u n))
      (regularizedHessian (fderiv ℝ (gradient f) (u n)) p.L) p.ρ)
    (n : ℕ) (hn : n ≤ (tuning p).refinementSteps) :
    (exactStep p f)^[n] { center := z, point := u 0, phase := .track origin d m j 0 terminal } =
      { center := z, point := u n, phase := .track origin d m j n terminal } := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hi : n < (tuning p).refinementSteps := by omega
    simp [exactStep, methodUpdate, hi, hu n, regularizedGradient]

lemma tracking_segment_end (p : Params) (f : Space p → ℝ) (z origin d : p.E)
    (w : Space p) (m j : ℕ) (terminal : Bool) (hj : j < m) :
    exactStep p f { center := z, point := w, phase := .track origin d m j (tuning p).refinementSteps terminal } =
      { center := origin + ((j + 1 : ℕ) / (m : ℝ)) • d, point := w, phase := .track origin d m (j + 1) 0 terminal } := by
  classical
  simp [exactStep, methodUpdate, hj]

lemma tracking_terminal_end (p : Params) (f : Space p → ℝ) (z origin d : p.E)
    (w : Space p) (m : ℕ) :
    exactStep p f { center := z, point := w, phase := .track origin d m m (tuning p).refinementSteps true } =
      { center := z, point := w, phase := .finished } := by
  classical
  simp [exactStep, methodUpdate]

lemma tracking_nonterminal_end (p : Params) (f : Space p → ℝ) (z origin d : p.E)
    (w : Space p) (m : ℕ) :
    exactStep p f { center := z, point := w, phase := .track origin d m m (tuning p).refinementSteps false } =
      cubicAdvance p { center := z, point := w, phase := .track origin d m m (tuning p).refinementSteps false }
        (f w, gradient f w, fderiv ℝ (gradient f) w) := by
  classical
  simp [exactStep, methodUpdate]

end OracleTemplate.PLMinimax
