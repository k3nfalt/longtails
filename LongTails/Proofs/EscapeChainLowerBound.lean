import LongTails.Proofs.EscapeChainParameters

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainLowerBound

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open scoped RealInnerProductSpace BigOperators ENNReal
open LongTails.Setups.HighDimensionalVarianceOnlySecondOrder
open EscapeChainFunction EscapeChainOracle EscapeChainSimulator EscapeChainFamily EscapeChainCalculus
open EscapeChainCounting EscapeChainRun EscapeChainCertificate EscapeChainRegularity EscapeChainMeasurable
open EscapeChainProbability EscapeChainParameters EscapeChainCoordinates
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcLowerMeasure

variable {d : ℕ}

noncomputable def ctx (q : Params) (hv : spec.valid q) (N : ℕ) (hN : N ≤ budgetFormula q) : Ctx q.d where
  n := nq q N
  b := bq q N
  K := Kq q
  N := N
  m := mq q N
  hnb := Nat.div_mul_le_self _ _
  hb := by unfold bq; omega
  hK := by have := n_large hv hN; omega
  A := Aq q
  r0 := r0 q
  δ0 := δ0 q
  hA := A_large hv
  hr0 := r0_pos hv
  hδ0 := δ0_pos hv

noncomputable def hardF (c : Ctx d) (θ : Hid c.n c.b) (x : Sp d) : ℝ :=
  c.δ0 * objective c.K (radius c.K) (U c θ) (V c θ) (c.r0⁻¹ • x)

noncomputable def hardO (c : Ctx d) (θ : Hid c.n c.b) : Oracle (Sp d) (Sp d) :=
  { Seed := fun _ => ℝ, law := ⟨stream, inferInstance⟩, answer := fun _ (_, x) w => ans c θ c.K x w }

lemma hardF_smooth (c : Ctx d) (θ : Hid c.n c.b) : ContDiff ℝ 3 (hardF c θ) := by
  unfold hardF
  exact contDiff_const.mul ((objective_smooth _ _ _ _).comp (contDiff_const_smul _))

lemma hardF_gradient (c : Ctx d) (θ : Hid c.n c.b) (x : Sp d) :
    gradient (hardF c θ) x = (c.δ0 * c.r0⁻¹) •
      gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x) :=
  ThirdOrderAffineCalculus.scale_gradient (objective_smooth _ _ _ _) c.δ0 c.r0⁻¹ x

lemma hardF_hessian (c : Ctx d) (θ : Hid c.n c.b) (x : Sp d) :
    fderiv ℝ (gradient (hardF c θ)) x = (c.δ0 * c.r0⁻¹ ^ 2) •
      fderiv ℝ (gradient (objective c.K (radius c.K) (U c θ) (V c θ))) (c.r0⁻¹ • x) :=
  ThirdOrderAffineCalculus.scale_hessian (objective_smooth _ _ _ _) c.δ0 c.r0⁻¹ x

lemma ans_K (c : Ctx d) (θ : Hid c.n c.b) (x : Sp d) (w : ℝ) :
    ans c θ c.K x w = (c.δ0 / c.r0) • answerN c.K c.A (U c θ) (V c θ) (c.r0⁻¹ • x) w := rfl


lemma ctx_d (q : Params) : (Sp q.d) = EuclideanSpace ℝ (Fin q.d) := rfl

section admissible

variable (q : Params) (c : Ctx q.d) (θ : Hid c.n c.b)

lemma hard_grad_lip (hv : spec.valid q) (hr : c.r0 = r0 q) (hd : c.δ0 = δ0 q) (x y : Sp q.d) :
    ‖gradient (hardF c θ) x - gradient (hardF c θ) y‖ ≤ q.L * ‖x - y‖ := by
  have fr := frameθ c θ
  have hr0 : 0 < c.r0 := c.hr0
  have hδ0 : 0 < c.δ0 := c.hδ0
  rw [hardF_gradient, hardF_gradient, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h := objective_gradient_lipschitz fr (c.r0⁻¹ • x) (c.r0⁻¹ • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  have hg : c.δ0 * 2 ^ 126 / c.r0 ^ 2 ≤ q.L := by rw [hr, hd]; exact grad_const hv
  calc c.δ0 * c.r0⁻¹ * ‖gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x) -
        gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • y)‖
      ≤ c.δ0 * c.r0⁻¹ * (2 ^ 126 * (c.r0⁻¹ * ‖x - y‖)) := by gcongr
    _ = c.δ0 * 2 ^ 126 / c.r0 ^ 2 * ‖x - y‖ := by ring
    _ ≤ q.L * ‖x - y‖ := by gcongr

lemma hard_hess_lip (hv : spec.valid q) (hr : c.r0 = r0 q) (hd : c.δ0 = δ0 q) (x y : Sp q.d) :
    ‖fderiv ℝ (gradient (hardF c θ)) x - fderiv ℝ (gradient (hardF c θ)) y‖ ≤ q.ρ * ‖x - y‖ := by
  have fr := frameθ c θ
  have hr0 : 0 < c.r0 := c.hr0
  have hδ0 : 0 < c.δ0 := c.hδ0
  have e : fderiv ℝ (gradient (hardF c θ)) x - fderiv ℝ (gradient (hardF c θ)) y =
      (c.δ0 * c.r0⁻¹ ^ 2) • (fderiv ℝ (gradient (objective c.K (radius c.K) (U c θ) (V c θ)))
        (c.r0⁻¹ • x) - fderiv ℝ (gradient (objective c.K (radius c.K) (U c θ) (V c θ))) (c.r0⁻¹ • y)) := by
    rw [hardF_hessian, hardF_hessian, smul_sub]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h := objective_hessian_lipschitz fr (c.r0⁻¹ • x) (c.r0⁻¹ • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  have hg : c.δ0 * 2 ^ 126 / c.r0 ^ 3 ≤ q.ρ := by rw [hr, hd]; exact hess_const hv
  calc c.δ0 * c.r0⁻¹ ^ 2 * ‖fderiv ℝ (gradient (objective c.K (radius c.K) (U c θ) (V c θ)))
        (c.r0⁻¹ • x) - fderiv ℝ (gradient (objective c.K (radius c.K) (U c θ) (V c θ)))
        (c.r0⁻¹ • y)‖
      ≤ c.δ0 * c.r0⁻¹ ^ 2 * (2 ^ 126 * (c.r0⁻¹ * ‖x - y‖)) := by gcongr
    _ = c.δ0 * 2 ^ 126 / c.r0 ^ 3 * ‖x - y‖ := by ring
    _ ≤ q.ρ * ‖x - y‖ := by gcongr

lemma hard_gap (hv : spec.valid q) (hd : c.δ0 = δ0 q) (hK : c.K = Kq q) (x : Sp q.d) : hardF c θ 0 - hardF c θ x ≤ q.Δ := by
  have fr := frameθ c θ
  have hδ0 : 0 < c.δ0 := c.hδ0
  show c.δ0 * objective c.K (radius c.K) (U c θ) (V c θ) (c.r0⁻¹ • (0 : Sp q.d)) -
    c.δ0 * objective c.K (radius c.K) (U c θ) (V c θ) (c.r0⁻¹ • x) ≤ q.Δ
  rw [smul_zero, objective_zero]
  have hl := objective_lower fr (c.r0⁻¹ • x)
  have hdep := depth hv
  have h1 : c.δ0 * (-(2 ^ 121 * ((c.K : ℝ) + 1))) ≤
      c.δ0 * objective c.K (radius c.K) (U c θ) (V c θ) (c.r0⁻¹ • x) :=
    mul_le_mul_of_nonneg_left hl hδ0.le
  have hK' : (c.K : ℝ) = Kq q := by rw [hK]
  rw [hK', hd] at h1
  rw [hd]
  linarith

lemma hard_int (x : Sp q.d) : Integrable (fun w => ans c θ c.K x w) unif := by
  simp only [ans_K]
  exact (answer_integrable c.K c.A (U c θ) (V c θ) (c.r0⁻¹ • x)).smul (c.δ0 / c.r0)

lemma hard_mean (x : Sp q.d) : ∫ w, ans c θ c.K x w ∂unif = gradient (hardF c θ) x := by
  simp only [ans_K]
  rw [integral_smul, answer_mean (frameθ c θ) c.hA, hardF_gradient, div_eq_mul_inv]

lemma hard_dev_eq (x : Sp q.d) :
    (fun w => ‖ans c θ c.K x w - gradient (hardF c θ) x‖ ^ 2) = fun w =>
      (c.δ0 / c.r0) ^ 2 * ‖answerN c.K c.A (U c θ) (V c θ) (c.r0⁻¹ • x) w -
        gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x)‖ ^ 2 := by
  funext w
  rw [ans_K, hardF_gradient, ← div_eq_mul_inv, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]

lemma hard_dev_int (x : Sp q.d) :
    Integrable (fun w => ‖ans c θ c.K x w - gradient (hardF c θ) x‖ ^ 2) unif := by
  rw [hard_dev_eq]
  exact (dev_integrable c.K c.A (U c θ) (V c θ) (c.r0⁻¹ • x)).const_mul _

lemma hard_var (hv : spec.valid q) (hr : c.r0 = r0 q) (hd : c.δ0 = δ0 q) (hA : c.A = Aq q)
    (x : Sp q.d) :
    ∫ w, ‖ans c θ c.K x w - gradient (hardF c θ) x‖ ^ 2 ∂unif ≤ q.σ ^ 2 := by
  obtain ⟨-, -, hε, -⟩ := pos_facts hv
  rw [hard_dev_eq, integral_const_mul]
  have hvar := answer_variance (frameθ c θ) c.hA (c.r0⁻¹ • x)
  have hq1 : c.δ0 / c.r0 = 2 ^ 133 * q.ε := by
    rw [hd, hr]; unfold δ0; exact mul_div_cancel_right₀ _ (r0_pos hv).ne'
  have hq2 : 45 ^ 2 * c.A = (q.σ / (2 ^ 133 * q.ε)) ^ 2 := by
    rw [hA]; unfold Aq σh; ring
  have hne : (2 : ℝ) ^ 133 * q.ε ≠ 0 := by positivity
  calc (c.δ0 / c.r0) ^ 2 * ∫ w, ‖answerN c.K c.A (U c θ) (V c θ) (c.r0⁻¹ • x) w -
        gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x)‖ ^ 2 ∂unif
      ≤ (c.δ0 / c.r0) ^ 2 * (45 ^ 2 * c.A) := by gcongr
    _ = (2 ^ 133 * q.ε * (q.σ / (2 ^ 133 * q.ε))) ^ 2 := by rw [hq1, hq2, ← mul_pow]
    _ = q.σ ^ 2 := by rw [mul_div_cancel₀ q.σ hne]

end admissible

theorem hard_admissible (q : Params) (hv : spec.valid q) (c : Ctx q.d) (hK : c.K = Kq q)
    (hr : c.r0 = r0 q) (hd : c.δ0 = δ0 q) (hA : c.A = Aq q) (θ : Hid c.n c.b) :
    spec.admissible q (hardF c θ) (hardO c θ) :=
  ⟨ans c θ c.K, (⟨unif, inferInstance⟩ : ProbabilityMeasure ℝ),
    (⟨stream, inferInstance⟩ : ProbabilityMeasure (ℕ → ℝ)), stream_iid, rfl,
    (hardF_smooth c θ).of_le (by norm_num), hard_grad_lip q c θ hv hr hd,
    hard_hess_lip q c θ hv hr hd, hard_gap q c θ hv hd hK, ans_measurable c θ c.K, hard_int q c θ,
    hard_mean q c θ, hard_dev_int q c θ, hard_var q c θ hv hr hd hA⟩

lemma calm_of_success (q : Params) (hv : spec.valid q) (c : Ctx q.d) (hr : c.r0 = r0 q)
    (hd : c.δ0 = δ0 q) (θ : Hid c.n c.b) (x : Sp q.d)
    (hg : ‖gradient (hardF c θ) x‖ ≤ q.ε)
    (hH : ∀ v, -Real.sqrt (q.ρ * q.ε) * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient (hardF c θ)) x v⟫) :
    Calm' c θ (c.r0⁻¹ • x) (1 / 2 ^ 133) := by
  have hr0 : 0 < c.r0 := c.hr0
  have hδ0 : 0 < c.δ0 := c.hδ0
  have hrat : q.ε * c.r0 / c.δ0 = 1 / 2 ^ 133 := by rw [hr, hd]; exact ratio_one hv
  have hcurv : Real.sqrt (q.ρ * q.ε) * c.r0 ^ 2 / c.δ0 = 1 / 10 := by rw [hr, hd]; exact ratio_curv hv
  rintro (⟨e, he, hlt⟩ | ⟨e, he, hlt⟩)
  · rw [hardF_gradient, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hg
    have h1 : |D (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x) e| ≤
        ‖gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x)‖ := by
      unfold EscapeChainCalculus.D
      exact (abs_real_inner_le_norm _ _).trans (by rw [he, mul_one])
    have h2 : ‖gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x)‖ ≤
        q.ε * c.r0 / c.δ0 := by
      rw [le_div_iff₀ hδ0]
      have e1 : c.δ0 * c.r0⁻¹ * ‖gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x)‖ *
          c.r0 = c.δ0 * ‖gradient (objective c.K (radius c.K) (U c θ) (V c θ)) (c.r0⁻¹ • x)‖ := by
        field_simp
      have h2' := mul_le_mul_of_nonneg_right hg hr0.le
      rw [e1] at h2'
      linarith
    rw [hrat] at h2
    linarith
  · have h := hH e
    rw [hardF_hessian, smul_apply, inner_smul_right, he] at h
    unfold Q at hlt
    rw [real_inner_comm] at hlt
    have hpos : 0 < c.δ0 * c.r0⁻¹ ^ 2 := by positivity
    have h3 : -(1 / 10) * (c.δ0 * c.r0⁻¹ ^ 2) = -Real.sqrt (q.ρ * q.ε) := by
      rw [← hcurv]
      field_simp
    have key := mul_lt_mul_of_pos_left hlt hpos
    rw [one_pow, mul_one] at h
    linarith

theorem exists_failure (q : Params) (hv : spec.valid q)
    (alg : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (halg : spec.allowedAlgorithm q alg) (N : ℕ)
    (hN : N ≤ budgetFormula q) :
    ∃ θ : Hid (ctx q hv N hN).n (ctx q hv N hN).b,
      ¬ spec.successful q (hardF (ctx q hv N hN) θ)
        (fun w : alg.Seed × ((k : ℕ) → (hardO (ctx q hv N hN) θ).Seed k) =>
          execute (hardO (ctx q hv N hN) θ) alg (fun _ => N) w.1 w.2)
        ⟨(alg.law : Measure _).prod ((hardO (ctx q hv N hN) θ).law : Measure _), inferInstance⟩ := by
  classical
  set c := ctx q hv N hN with hc
  obtain ⟨inst, hinit, hq, hu, hout⟩ := halg
  by_contra hall
  push Not at hall
  obtain ⟨-, hρ, hε, hδ, hδ2, -⟩ := pos_facts hv
  have hK40 : 40 ≤ Kq q := (K_bounds hv).2.2
  have hKpos : 0 < Kq q := by omega
  have hK : 0 < c.K := hKpos
  have hm : 2 * c.N ≤ (c.m + 1) * c.K := by
    show 2 * N ≤ (mq q N + 1) * Kq q
    unfold mq
    rw [add_mul, one_mul]
    exact (Nat.lt_div_mul_add (a := 2 * N) hKpos).le
  let S : Hid c.n c.b → Set (alg.Seed × (ℕ → ℝ)) := fun θ =>
    {z | ‖gradient (hardF c θ) (execute (hardO c θ) alg (fun _ => N) z.1 z.2)‖ ≤ q.ε ∧
      ∀ v, -Real.sqrt (q.ρ * q.ε) * ‖v‖ ^ 2 ≤
        ⟪v, fderiv ℝ (gradient (hardF c θ)) (execute (hardO c θ) alg (fun _ => N) z.1 z.2) v⟫}
  have hexec : ∀ θ z, execute (hardO c θ) alg (fun _ => N) z.1 z.2 =
      alg.output (runJ c alg θ c.K z c.N) := by
    intro θ z
    exact execute_run alg (ans c θ c.K) ⟨stream, inferInstance⟩ N z.1 z.2
  have hS : ∀ θ z, z ∈ S θ → Calm' c θ (yo c alg θ c.K z) (1 / 2 ^ 133) := by
    intro θ z hz
    obtain ⟨h1, h2⟩ := hz
    rw [hexec] at h1 h2
    exact calm_of_success q hv c rfl rfl θ _ h1 h2
  have htot := total c alg hinit hq hu hout S (by positivity) (by norm_num) hS hK hm
  have hlow : ∀ θ, ENNReal.ofReal (1 - q.δ) ≤ μ alg (S θ) := fun θ => (hall θ).2
  have hcard : (1 : ℝ) ≤ Fintype.card (Hid c.n c.b) := by
    have : 0 < Fintype.card (Hid c.n c.b) := Fintype.card_pos
    exact_mod_cast this
  have hsum_low : ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 2)) ≤
      ∑ θ : Hid c.n c.b, μ alg (S θ) := by
    calc ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 2))
        ≤ ∑ _θ : Hid c.n c.b, ENNReal.ofReal (1 - q.δ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith)
      _ ≤ _ := Finset.sum_le_sum fun θ _ => hlow θ
  have hbad : ((c.K : ℝ) + 1) * (c.N + 1) * c.K * 2 *
      (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2)))) ≤ 1 / 8 := bad_small hv N
  have hrev : 2 * (2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) * (c.m + 1)) ≤ 1 / 8 :=
    reveal_small hv hN
  have hup : ∑ θ : Hid c.n c.b, μ alg (S θ) ≤ ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 4)) := by
    refine htot.trans ?_
    have e1 : ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (((c.K : ℝ) + 1) * (c.N + 1) * c.K * 2 *
        (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2)))))) ≤
        ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 8)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbad (by positivity))
    have e2 : 2 * ENNReal.ofReal (2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) * ((c.m + 1) *
        Fintype.card (Hid c.n c.b))) ≤ ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 8)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hrev (show (0 : ℝ) ≤ Fintype.card (Hid c.n c.b) by positivity)
      linarith
    calc _ ≤ ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 8)) +
          ENNReal.ofReal (Fintype.card (Hid c.n c.b) * (1 / 8)) := add_le_add e1 e2
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  have := hsum_low.trans hup
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  nlinarith

end LongTails.Proofs.EscapeChainLowerBound
