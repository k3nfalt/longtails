import LongTails.Proofs.PLMinimaxExecution
import LongTails.Proofs.PLMinimaxTracking
import LongTails.Proofs.PLMinimaxInitialization

open LongTails.Setups.NonconvexPLSecondOrder

namespace OracleTemplate.PLMinimax

lemma tracking_refinement_complete {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z origin d : p.E)
    (w : Space p) (m j : ℕ) (terminal : Bool)
    (hstart : ∃ q, regularizedGradient (gradient f) p.L z q = 0 ∧
      ‖q - w‖ ≤ p.μ / (64 * p.ρ)) :
    ∃ w', (exactStep p f)^[(tuning p).refinementSteps]
      { center := z, point := w, phase := .track origin d m j 0 terminal } =
        { center := z, point := w', phase := .track origin d m j (tuning p).refinementSteps terminal } ∧
      ‖regularizedGradient (gradient f) p.L z w'‖ ≤ (tuning p).residualTolerance := by
  let step := fun w : Space p => w + residualNewtonStep
    (regularizedGradient (gradient f) p.L z w)
    (regularizedHessian (fderiv ℝ (gradient f) w) p.L) p.ρ
  let u := fun n : ℕ => step^[n] w
  have hu : ∀ n, u (n + 1) = u n + residualNewtonStep
      (regularizedGradient (gradient f) p.L z (u n))
      (regularizedHessian (fderiv ℝ (gradient f) (u n)) p.L) p.ρ := by
    intro n
    exact Function.iterate_succ_apply' step n w
  refine ⟨u (tuning p).refinementSteps, ?_, ?_⟩
  · exact tracking_prefix p f z origin d u m j terminal hu _ le_rfl
  · exact setup_fixed_refinement hv hf z u hu hstart

lemma tracking_block_complete {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (origin d : p.E)
    (m : ℕ) (hm : 0 < m) (terminal : Bool)
    (hmesh : ‖(1 / (m : ℝ)) • d‖ ≤ (tuning p).mesh)
    (n j : ℕ) (hjm : j + n = m) (w : Space p)
    (hstart : ∃ q, regularizedGradient (gradient f) p.L
      (origin + ((j : ℝ) / m) • d) q = 0 ∧ ‖q - w‖ ≤ p.μ / (64 * p.ρ)) :
    ∃ w', (exactStep p f)^[n * ((tuning p).refinementSteps + 1) + (tuning p).refinementSteps]
      { center := origin + ((j : ℝ) / m) • d, point := w, phase := .track origin d m j 0 terminal } =
        { center := origin + d, point := w', phase := .track origin d m m (tuning p).refinementSteps terminal } ∧
      ‖regularizedGradient (gradient f) p.L (origin + d) w'‖ ≤ (tuning p).residualTolerance := by
  induction n generalizing j w with
  | zero =>
    have hj : j = m := by omega
    subst j
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    simp only [div_self hm', one_smul] at hstart
    simpa [hm'] using tracking_refinement_complete hv hf (origin + d) origin d w m m terminal hstart
  | succ n ih =>
    obtain ⟨w₁, hw₁, hr₁⟩ := tracking_refinement_complete hv hf
      (origin + ((j : ℝ) / m) • d) origin d w m j terminal hstart
    have hj : j < m := by omega
    have hc : origin + ((j : ℝ) / m) • d + (1 / (m : ℝ)) • d =
        origin + (((j + 1 : ℕ) : ℝ) / m) • d := by
      rw [add_assoc, ← add_smul]
      congr 2
      push_cast
      ring
    have hs := setup_tracking_start hv hf (origin + ((j : ℝ) / m) • d)
      ((1 / (m : ℝ)) • d) w₁ hr₁ hmesh
    rw [hc] at hs
    obtain ⟨w₂, hw₂, hr₂⟩ := ih (j + 1) (by omega) w₁ hs
    refine ⟨w₂, ?_, hr₂⟩
    have hcount : (n + 1) * ((tuning p).refinementSteps + 1) + (tuning p).refinementSteps =
        (n * ((tuning p).refinementSteps + 1) + (tuning p).refinementSteps) +
          (1 + (tuning p).refinementSteps) := by ring
    rw [hcount, Function.iterate_add_apply,
      Function.iterate_add_apply (exactStep p f) 1 (tuning p).refinementSteps, hw₁]
    simp only [Function.iterate_one]
    rw [tracking_segment_end p f _ origin d w₁ m j terminal hj]
    exact hw₂

lemma tracking_mesh_bound {p : Params} (hv : spec.valid p) (d : p.E) :
    ‖(1 / ((max 1 ⌈‖d‖ / (tuning p).mesh⌉₊ : ℕ) : ℝ)) • d‖ ≤ (tuning p).mesh := by
  let m := max 1 ⌈‖d‖ / (tuning p).mesh⌉₊
  have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m from lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have ht := (tuning_positive hv).2.2.1
  have hn : ‖d‖ / (tuning p).mesh ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈‖d‖ / (tuning p).mesh⌉₊)
  have hd := (div_le_iff₀ ht).mp hn
  change ‖(1 / (m : ℝ)) • d‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
  apply (mul_le_mul_iff_right₀ hm).mp
  have he : (m : ℝ) * (1 / (m : ℝ) * ‖d‖) = ‖d‖ := by field_simp
  rw [he]
  exact hd

lemma tracking_all_complete {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (origin d : p.E)
    (w : Space p) (m : ℕ) (hm : 0 < m) (terminal : Bool)
    (hr : ‖regularizedGradient (gradient f) p.L origin w‖ ≤ (tuning p).residualTolerance)
    (hmesh : ‖(1 / (m : ℝ)) • d‖ ≤ (tuning p).mesh) :
    ∃ w', ‖regularizedGradient (gradient f) p.L (origin + d) w'‖ ≤ (tuning p).residualTolerance ∧
      (exactStep p f)^[m * ((tuning p).refinementSteps + 1)]
        { center := origin + (1 / (m : ℝ)) • d, point := w, phase := .track origin d m 1 0 terminal } =
      if terminal then { center := origin + d, point := w', phase := .finished }
      else cubicAdvance p
        { center := origin + d, point := w', phase := .track origin d m m (tuning p).refinementSteps false }
        (f w', gradient f w', fderiv ℝ (gradient f) w') := by
  have hs := setup_tracking_start hv hf origin ((1 / (m : ℝ)) • d) w hr hmesh
  obtain ⟨w', hw', hr'⟩ := tracking_block_complete hv hf origin d m hm terminal hmesh
    (m - 1) 1 (by omega) w (by simpa using hs)
  refine ⟨w', hr', ?_⟩
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have he := congrArg (fun k => k * ((tuning p).refinementSteps + 1)) hm'
  simp only [Nat.add_mul, Nat.one_mul] at he
  have hcount : m * ((tuning p).refinementSteps + 1) =
      ((m - 1) * ((tuning p).refinementSteps + 1) + (tuning p).refinementSteps) + 1 := by omega
  rw [hcount, Function.iterate_succ_apply']
  simp only [Nat.cast_one] at hw'
  rw [hw']
  cases terminal
  · exact tracking_nonterminal_end p f _ origin d w' m
  · exact tracking_terminal_end p f _ origin d w' m

lemma initialization_stage_start (p : Params) (f : Space p → ℝ) (z : p.E)
    (y : ℕ → p.F) (u : ℕ → ℕ → p.E)
    (hu : ∀ j n, u j (n + 1) = u j n - (1 / (9 * p.L)) •
      ((gradient f (WithLp.toLp 2 (u j n, y j))).fst + (2 * p.L) • (u j n - z)))
    (hy : ∀ j, y (j + 1) = y j + (1 / (2 * p.L)) •
      (gradient f (WithLp.toLp 2 (u j (tuning p).primalSteps, y j))).snd)
    (hstart : ∀ j, u (j + 1) 0 = u j (tuning p).primalSteps)
    (j : ℕ) (hj : j ≤ (tuning p).dualSteps) :
    (exactStep p f)^[j * ((tuning p).primalSteps + 1)]
      { center := z, point := WithLp.toLp 2 (u 0 0, y 0), phase := .initialize 0 0 } =
      { center := z, point := WithLp.toLp 2 (u j 0, y j), phase := .initialize j 0 } := by
  induction j with
  | zero => simp only [Nat.zero_mul, Function.iterate_zero, id_eq]
  | succ j ih =>
    have hc : (j + 1) * ((tuning p).primalSteps + 1) =
        (1 + (tuning p).primalSteps) + j * ((tuning p).primalSteps + 1) := by ring
    rw [hc, Function.iterate_add_apply, ih (by omega), Function.iterate_add_apply]
    rw [initialize_prefix p f z (y j) (u j) j (hu j) _ le_rfl]
    simp only [Function.iterate_one]
    rw [initialize_stage_end p f z _ _ j (by omega), hy j, hstart j]

lemma initialization_last_query (p : Params) (f : Space p → ℝ) (z : p.E)
    (y : ℕ → p.F) (u : ℕ → ℕ → p.E)
    (hu : ∀ j n, u j (n + 1) = u j n - (1 / (9 * p.L)) •
      ((gradient f (WithLp.toLp 2 (u j n, y j))).fst + (2 * p.L) • (u j n - z)))
    (hy : ∀ j, y (j + 1) = y j + (1 / (2 * p.L)) •
      (gradient f (WithLp.toLp 2 (u j (tuning p).primalSteps, y j))).snd)
    (hstart : ∀ j, u (j + 1) 0 = u j (tuning p).primalSteps) :
    (exactStep p f)^[(tuning p).dualSteps * ((tuning p).primalSteps + 1) + (tuning p).primalSteps]
      { center := z, point := WithLp.toLp 2 (u 0 0, y 0), phase := .initialize 0 0 } =
      { center := z, point := WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps,
          y (tuning p).dualSteps), phase := .initialize (tuning p).dualSteps (tuning p).primalSteps } := by
  rw [Nat.add_comm, Function.iterate_add_apply,
    initialization_stage_start p f z y u hu hy hstart _ le_rfl]
  exact initialize_prefix p f z _ _ _ (hu _) _ le_rfl

lemma initialization_sequences (p : Params) (f : Space p → ℝ) :
    ∃ (y : ℕ → p.F) (u : ℕ → ℕ → p.E), y 0 = p.y0 ∧ u 0 0 = p.x0 ∧
      (∀ j n, u j (n + 1) = u j n - (1 / (9 * p.L)) •
        ((gradient f (WithLp.toLp 2 (u j n, y j))).fst + (2 * p.L) • (u j n - p.x0))) ∧
      (∀ j, y (j + 1) = y j + (1 / (2 * p.L)) •
        (gradient f (WithLp.toLp 2 (u j (tuning p).primalSteps, y j))).snd) ∧
      ∀ j, u (j + 1) 0 = u j (tuning p).primalSteps := by
  let step := fun (y : p.F) (x : p.E) => x - (1 / (9 * p.L)) •
    ((gradient f (WithLp.toLp 2 (x, y))).fst + (2 * p.L) • (x - p.x0))
  let stage := fun w : p.E × p.F =>
    let x := (step w.2)^[(tuning p).primalSteps] w.1
    (x, w.2 + (1 / (2 * p.L)) • (gradient f (WithLp.toLp 2 (x, w.2))).snd)
  let rounds := fun j : ℕ => stage^[j] (p.x0, p.y0)
  let y := fun j => (rounds j).2
  let u := fun j n => (step (y j))^[n] (rounds j).1
  refine ⟨y, u, rfl, rfl, ?_, ?_, ?_⟩
  · intro j n
    exact Function.iterate_succ_apply' (step (y j)) n (rounds j).1
  · intro j
    exact congrArg Prod.snd (Function.iterate_succ_apply' stage j (p.x0, p.y0))
  · intro j
    exact congrArg Prod.fst (Function.iterate_succ_apply' stage j (p.x0, p.y0))

lemma initialization_residual_certificate {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle)
    (y : ℕ → p.F) (u : ℕ → ℕ → p.E) (hy0 : y 0 = p.y0) (hu0 : u 0 0 = p.x0)
    (hu : ∀ j n, u j (n + 1) = u j n - (1 / (9 * p.L)) •
      ((gradient f (WithLp.toLp 2 (u j n, y j))).fst + (2 * p.L) • (u j n - p.x0)))
    (hy : ∀ j, y (j + 1) = y j + (1 / (2 * p.L)) •
      (gradient f (WithLp.toLp 2 (u j (tuning p).primalSteps, y j))).snd)
    (hstart : ∀ j, u (j + 1) 0 = u j (tuning p).primalSteps) :
    ‖regularizedGradient (gradient f) p.L p.x0
      (WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps, y (tuning p).dualSteps))‖ ≤
        (tuning p).residualTolerance := by
  have H := setup_hyp hv hf
  have hμ := hv.1
  have hL := H.hL
  have hΔ := hv.2.2.2.1
  have hD := hv.2.2.2.2.1
  have hτ := (tuning_positive hv).2.2.2.2.2.2.2.2.2
  let S₀ := 32 * (p.L / p.μ) * (p.Δ + p.D)
  let S := fun j : ℕ => (1 - p.μ / (4 * p.L)) ^ j *
    (S₀ + (tuning p).residualTolerance ^ 2 / (64 * p.L))
  have hS₀ : 0 ≤ S₀ := by dsimp [S₀]; positivity
  have hq : 0 ≤ 1 - p.μ / (4 * p.L) := by
    have hh : p.μ / (4 * p.L) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [H.hμL, hL])
    linarith only [hh]
  have hS : ∀ j, 0 ≤ S j := by intro j; dsimp [S]; positivity
  have hSn : ∀ j, S (j + 1) = (1 - p.μ / (4 * p.L)) * S j := by
    intro j
    dsimp [S]
    rw [pow_succ]
    ring
  have hbase : S₀ ≤ S 0 := by
    dsimp [S]
    simp only [pow_zero, one_mul]
    exact le_add_of_nonneg_right (by positivity)
  have hgap := H.initial_dual_gap p.x0 p.y0 hΔ hD hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1
  have hgap' : envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 -
      dual (fun x y => f (WithLp.toLp 2 (x, y))) p.L p.x0 (y 0) ≤ S 0 := by
    rw [hy0]
    apply hgap.trans
    convert hbase using 1
    dsimp [S₀]
    ring
  have hres := H.initial_primal_gradient p.x0 p.y0 hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1
  have hresbase : (16 * p.L ^ 2 / p.μ) * p.Δ + (32 * p.L ^ 2 / p.μ) * p.D ≤ p.L * S₀ := by
    dsimp [S₀]
    apply (mul_le_mul_iff_right₀ hμ).mp
    field_simp
    linarith only [hΔ]
  have hres' : ‖(gradient f (WithLp.toLp 2 (u 0 0, y 0))).fst +
      (2 * p.L) • (u 0 0 - p.x0)‖ ^ 2 ≤ 16 * p.L * S 0 := by
    rw [hu0, hy0, sub_self, smul_zero, add_zero]
    apply hres.trans (hresbase.trans ?_)
    have hs := mul_le_mul_of_nonneg_left hbase hL.le
    have hn := mul_nonneg hL.le (hS 0)
    nlinarith only [hs, hn]
  have hround := H.initialization_rounds p.x0 (tuning p).primalSteps S y u hS hSn
    (tuning_primal_iterations hv) hu hy hstart hgap' hres' (tuning p).dualSteps
  have hdual := H.approximate_dual_gradient_gap p.x0
    (u (tuning p).dualSteps (tuning p).primalSteps) (y (tuning p).dualSteps)
    (hS _) hround.1 hround.2.2
  have hlast : S (tuning p).dualSteps ≤ (tuning p).residualTolerance ^ 2 / (64 * p.L) :=
    tuning_dual_iterations hv
  have hnorm := WithLp.prod_norm_sq_eq_of_L2
    (regularizedGradient (gradient f) p.L p.x0
      (WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps, y (tuning p).dualSteps)))
  change ‖regularizedGradient (gradient f) p.L p.x0
      (WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps, y (tuning p).dualSteps))‖ ^ 2 =
    ‖(gradient f (WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps, y (tuning p).dualSteps))).fst +
      (2 * p.L) • (u (tuning p).dualSteps (tuning p).primalSteps - p.x0)‖ ^ 2 +
    ‖(gradient f (WithLp.toLp 2 (u (tuning p).dualSteps (tuning p).primalSteps, y (tuning p).dualSteps))).snd + 0‖ ^ 2 at hnorm
  simp only [add_zero] at hnorm
  have hsum := add_le_add hround.2.2 hdual
  have hμL := mul_le_mul_of_nonneg_right H.hμL (hS (tuning p).dualSteps)
  have hlast' := mul_le_mul_of_nonneg_left hlast (show 0 ≤ 11 * p.L by positivity)
  have he : (11 * p.L) * ((tuning p).residualTolerance ^ 2 / (64 * p.L)) =
      11 / 64 * (tuning p).residualTolerance ^ 2 := by field_simp
  rw [he] at hlast'
  apply (sq_le_sq₀ (norm_nonneg _) hτ.le).mp
  nlinarith only [hnorm, hsum, hμL, hlast', sq_nonneg (tuning p).residualTolerance]

end OracleTemplate.PLMinimax
