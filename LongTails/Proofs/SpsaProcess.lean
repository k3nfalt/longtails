import LongTails.Proofs.SpsaStep
import LongTails.Proofs.HessianNcscProcess

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace LongTails.Proofs.SpsaProcess

open OracleTemplate.ClippedSpsa LongTails.Proofs.SpsaStep LongTails.Proofs.SpsaMoments
  LongTails.Proofs.ClippedScalarDescent

section Fresh

variable {A B St : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace St]

lemma fresh_pair (pa : Measure A) [IsProbabilityMeasure pa] (pb : Measure B)
    [IsProbabilityMeasure pb] (k : ℕ) (S : (ℕ → A) → (ℕ → B) → St)
    (hS : Measurable (Function.uncurry S))
    (hdepA : ∀ U U' Ξ, (∀ i, i < k → U i = U' i) → S U Ξ = S U' Ξ)
    (hdepB : ∀ U Ξ Ξ', (∀ i, i < k → Ξ i = Ξ' i) → S U Ξ = S U Ξ')
    (h : St × (A × B) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ w, h (S w.1 w.2, (w.1 k, w.2 k))
        ∂((Measure.infinitePi fun _ : ℕ => pa).prod (Measure.infinitePi fun _ : ℕ => pb)) =
      ∫⁻ w, (∫⁻ z, h (S w.1 w.2, z) ∂(pa.prod pb))
        ∂((Measure.infinitePi fun _ : ℕ => pa).prod (Measure.infinitePi fun _ : ℕ => pb)) := by
  set PA := Measure.infinitePi fun _ : ℕ => pa
  set PB := Measure.infinitePi fun _ : ℕ => pb
  have hSU : ∀ U, Measurable (S U) := fun U => hS.comp (measurable_const.prodMk measurable_id)
  have hSΞ : ∀ Ξ, Measurable (fun U => S U Ξ) :=
    fun Ξ => hS.comp (measurable_id.prodMk measurable_const)
  have hm1 : Measurable (fun w : (ℕ → A) × (ℕ → B) => h (S w.1 w.2, (w.1 k, w.2 k))) :=
    hh.comp (hS.prodMk ((measurable_pi_apply k).comp measurable_fst |>.prodMk
      ((measurable_pi_apply k).comp measurable_snd)))
  have hin : Measurable (fun q : St × A => ∫⁻ ω, h (q.1, (q.2, ω)) ∂pb) :=
    (hh.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  have hm2 : Measurable (fun w : (ℕ → A) × (ℕ → B) => ∫⁻ z, h (S w.1 w.2, z) ∂(pa.prod pb)) :=
    (hh.comp ((hS.comp measurable_fst).prodMk measurable_snd)).lintegral_prod_right'
  rw [lintegral_prod _ hm1.aemeasurable, lintegral_prod _ hm2.aemeasurable]
  dsimp only
  have step1 : ∀ U : ℕ → A, ∫⁻ Ξ, h (S U Ξ, (U k, Ξ k)) ∂PB =
      ∫⁻ Ξ, ∫⁻ ω, h (S U Ξ, (U k, ω)) ∂pb ∂PB := by
    intro U
    exact OracleTemplate.HessianNcsc.fresh_lintegral pb k (S U) (hSU U)
      (fun Ξ Ξ' hΞ => hdepB U Ξ Ξ' hΞ) (fun q => h (q.1, (U k, q.2)))
      (hh.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  simp_rw [step1]
  have hjoint : Measurable (Function.uncurry (fun (U : ℕ → A) (Ξ : ℕ → B) =>
      ∫⁻ ω, h (S U Ξ, (U k, ω)) ∂pb)) :=
    hin.comp (hS.prodMk ((measurable_pi_apply k).comp measurable_fst))
  rw [lintegral_lintegral_swap (f := fun (U : ℕ → A) (Ξ : ℕ → B) => ∫⁻ ω, h (S U Ξ, (U k, ω)) ∂pb)
    hjoint.aemeasurable]
  have step2 : ∀ Ξ : ℕ → B, ∫⁻ U, ∫⁻ ω, h (S U Ξ, (U k, ω)) ∂pb ∂PA =
      ∫⁻ U, ∫⁻ s, ∫⁻ ω, h (S U Ξ, (s, ω)) ∂pb ∂pa ∂PA := by
    intro Ξ
    exact OracleTemplate.HessianNcsc.fresh_lintegral pa k (fun U => S U Ξ) (hSΞ Ξ)
      (fun U U' hU => hdepA U U' Ξ hU) (fun q => ∫⁻ ω, h (q.1, (q.2, ω)) ∂pb) hin
  simp_rw [step2]
  have hzm : ∀ y : St, Measurable (fun z : A × B => h (y, z)) :=
    fun y => hh.comp (measurable_const.prodMk measurable_id)
  have step3 : ∀ y : St, ∫⁻ s, ∫⁻ ω, h (y, (s, ω)) ∂pb ∂pa = ∫⁻ z, h (y, z) ∂(pa.prod pb) :=
    fun y => (lintegral_prod _ (hzm y).aemeasurable).symm
  simp_rw [step3]
  have hjoint2 : Measurable (Function.uncurry (fun (Ξ : ℕ → B) (U : ℕ → A) =>
      ∫⁻ z, h (S U Ξ, z) ∂(pa.prod pb))) :=
    hm2.comp measurable_swap
  exact lintegral_lintegral_swap (f := fun (Ξ : ℕ → B) (U : ℕ → A) => ∫⁻ z, h (S U Ξ, z) ∂(pa.prod pb))
    hjoint2.aemeasurable

end Fresh

section Trajectory

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

noncomputable def traj (F : Point d → Ω → ℝ) (μ0 η c : ℝ) (x0 : Point d) (U : ℕ → Sign d)
    (Ξ : ℕ → Ω) : ℕ → Point d
  | 0 => x0
  | n + 1 => stepPoint F μ0 η c (traj F μ0 η c x0 U Ξ n) (U n, Ξ n)

variable {F : Point d → Ω → ℝ} {μ0 η c : ℝ} {x0 : Point d}

omit [MeasurableSpace Ω] in
lemma traj_congr (U U' : ℕ → Sign d) (Ξ Ξ' : ℕ → Ω) :
    ∀ n, (∀ i, i < n → U i = U' i) → (∀ i, i < n → Ξ i = Ξ' i) →
      traj F μ0 η c x0 U Ξ n = traj F μ0 η c x0 U' Ξ' n
  | 0, _, _ => rfl
  | n + 1, hU, hΞ => by
      simp only [traj]
      rw [traj_congr U U' Ξ Ξ' n (fun i hi => hU i (by omega)) (fun i hi => hΞ i (by omega)),
        hU n (by omega), hΞ n (by omega)]

lemma measurable_stepPoint (hF : Measurable (Function.uncurry F)) :
    Measurable (fun q : Point d × (Sign d × Ω) => stepPoint F μ0 η c q.1 q.2) := by
  have hu : Measurable (fun q : Point d × (Sign d × Ω) => signVec q.2.1) :=
    (measurable_on_signs (fun s : Sign d => signVec s)).comp measurable_snd.fst
  have h1 : Measurable (fun q : Point d × (Sign d × Ω) => F (q.1 + μ0 • signVec q.2.1) q.2.2) :=
    hF.comp ((measurable_fst.add (hu.const_smul μ0)).prodMk measurable_snd.snd)
  have h2 : Measurable (fun q : Point d × (Sign d × Ω) => F (q.1 - μ0 • signVec q.2.1) q.2.2) :=
    hF.comp ((measurable_fst.sub (hu.const_smul μ0)).prodMk measurable_snd.snd)
  have hq : Measurable (fun q : Point d × (Sign d × Ω) => diffQuot F μ0 q.1 q.2) :=
    (h1.sub h2).div_const _
  have hcl : Measurable (fun q : Point d × (Sign d × Ω) => clipScalar c (diffQuot F μ0 q.1 q.2)) := by
    simp only [clipScalar]; exact measurable_const.max (measurable_const.min hq)
  exact measurable_fst.sub ((hcl.smul hu).const_smul η)

lemma measurable_traj (hF : Measurable (Function.uncurry F)) :
    ∀ n, Measurable (fun w : (ℕ → Sign d) × (ℕ → Ω) => traj F μ0 η c x0 w.1 w.2 n)
  | 0 => measurable_const
  | n + 1 => by
      simp only [traj]
      exact (measurable_stepPoint hF).comp ((measurable_traj hF n).prodMk
        (((measurable_pi_apply n).comp measurable_fst).prodMk
          ((measurable_pi_apply n).comp measurable_snd)))

omit [MeasurableSpace Ω] in
lemma norm_stepPoint_sub (hc : 0 ≤ c) (x : Point d) (z : Sign d × Ω) :
    ‖stepPoint F μ0 η c x z - x‖ ≤ |η| * c * Real.sqrt d := by
  simp only [stepPoint, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, norm_signVec]
  have := clip_abs_le hc (diffQuot F μ0 x z)
  have hd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hd) (abs_nonneg η)
  linarith [show |η| * (c * Real.sqrt d) = |η| * c * Real.sqrt d by ring]

omit [MeasurableSpace Ω] in
lemma traj_dist (hc : 0 ≤ c) (U : ℕ → Sign d) (Ξ : ℕ → Ω) :
    ∀ n, ‖traj F μ0 η c x0 U Ξ n - x0‖ ≤ n * (|η| * c * Real.sqrt d)
  | 0 => by simp [traj]
  | n + 1 => by
      have ih := traj_dist hc U Ξ n
      have hs := norm_stepPoint_sub (F := F) (μ0 := μ0) (η := η) hc (traj F μ0 η c x0 U Ξ n) (U n, Ξ n)
      simp only [traj]
      calc ‖stepPoint F μ0 η c (traj F μ0 η c x0 U Ξ n) (U n, Ξ n) - x0‖
          ≤ ‖stepPoint F μ0 η c (traj F μ0 η c x0 U Ξ n) (U n, Ξ n) - traj F μ0 η c x0 U Ξ n‖ +
              ‖traj F μ0 η c x0 U Ξ n - x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ |η| * c * Real.sqrt d + n * (|η| * c * Real.sqrt d) := add_le_add hs ih
        _ = ((n + 1 : ℕ) : ℝ) * (|η| * c * Real.sqrt d) := by push_cast; ring

end Trajectory

section Execution

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma run_active (F : Point d → Ω → ℝ) (μ0 η c : ℝ) (T : ℕ) (x0 : Point d) (U : ℕ → Sign d)
    (Ξ : ℕ → Ω) (τ : ℕ) :
    ∀ j, j ≤ τ →
      (fun sc : ((ℕ → Sign d) × ℕ × ℕ × Point d) × ℕ =>
          ((method μ0 η c T x0).update sc.1
            (F ((method μ0 η c T x0).query sc.1).2.1 (Ξ sc.2),
              F ((method μ0 η c T x0).query sc.1).2.2 (Ξ sc.2)), sc.2 + 1))^[j]
          ((U, τ, 0, x0), 0) = ((U, τ, j, traj F μ0 η c x0 U Ξ j), j)
  | 0, _ => rfl
  | j + 1, h => by
      rw [Function.iterate_succ_apply', run_active F μ0 η c T x0 U Ξ τ j (by omega)]
      have hj : j < τ := by omega
      simp only [method, hj, ite_true, traj, stepPoint, increment, diffQuot]

omit [MeasurableSpace Ω] in
lemma run_frozen (F : Point d → Ω → ℝ) (μ0 η c : ℝ) (T : ℕ) (x0 : Point d) (U : ℕ → Sign d)
    (Ξ : ℕ → Ω) (τ : ℕ) :
    ∀ m, ((fun sc : ((ℕ → Sign d) × ℕ × ℕ × Point d) × ℕ =>
          ((method μ0 η c T x0).update sc.1
            (F ((method μ0 η c T x0).query sc.1).2.1 (Ξ sc.2),
              F ((method μ0 η c T x0).query sc.1).2.2 (Ξ sc.2)), sc.2 + 1))^[τ + m]
          ((U, τ, 0, x0), 0)).1 = (U, τ, τ, traj F μ0 η c x0 U Ξ τ)
  | 0 => by rw [Nat.add_zero, run_active F μ0 η c T x0 U Ξ τ τ le_rfl]
  | m + 1 => by
      rw [show τ + (m + 1) = (τ + m) + 1 by omega, Function.iterate_succ_apply']
      have ih := run_frozen F μ0 η c T x0 U Ξ τ m
      set sc := (fun sc : ((ℕ → Sign d) × ℕ × ℕ × Point d) × ℕ =>
          ((method μ0 η c T x0).update sc.1
            (F ((method μ0 η c T x0).query sc.1).2.1 (Ξ sc.2),
              F ((method μ0 η c T x0).query sc.1).2.2 (Ξ sc.2)), sc.2 + 1))^[τ + m]
          ((U, τ, 0, x0), 0)
      obtain ⟨st, k⟩ := sc
      simp only at ih
      subst ih
      simp [method]

noncomputable def spsaOracle (F : Point d → Ω → ℝ) (P : ProbabilityMeasure (ℕ → Ω)) :
    OracleTemplate.Oracle (Point d × Point d) (ℝ × ℝ) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, y) ω => (F y.1 ω, F y.2 ω)

lemma execute_spsa (F : Point d → Ω → ℝ) (P : ProbabilityMeasure (ℕ → Ω)) (μ0 η c : ℝ) (T : ℕ)
    (x0 : Point d) (K : ℕ) (hK : T ≤ K) (seed : (ℕ → Sign d) × Fin (T + 1)) (Ξ : ℕ → Ω) :
    OracleTemplate.execute (spsaOracle F P) (method μ0 η c T x0) (fun _ => K) seed Ξ =
      traj F μ0 η c x0 seed.1 Ξ seed.2.val := by
  refine (OracleTemplate.execute_indexed_of_answer (spsaOracle F P) (method μ0 η c T x0) K seed Ξ
    (fun k q => (F q.2.1 (Ξ k), F q.2.2 (Ξ k))) (fun _ _ => rfl)).trans ?_
  obtain ⟨U, τ⟩ := seed
  obtain ⟨m, hm⟩ : ∃ m, K = τ.val + m := ⟨K - τ.val, by have := τ.isLt; omega⟩
  subst hm
  have h := run_frozen F μ0 η c T x0 U Ξ τ.val m
  change (((fun sc : ((ℕ → Sign d) × ℕ × ℕ × Point d) × ℕ =>
          ((method μ0 η c T x0).update sc.1
            (F ((method μ0 η c T x0).query sc.1).2.1 (Ξ sc.2),
              F ((method μ0 η c T x0).query sc.1).2.2 (Ξ sc.2)), sc.2 + 1))^[τ.val + m]
          ((U, τ.val, 0, x0), 0)).1).2.2.2 = _
  rw [h]

end Execution

noncomputable abbrev pathLaw (d : ℕ) {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) :
    Measure ((ℕ → Sign d) × (ℕ → Ω)) :=
  (Measure.infinitePi fun _ : ℕ => signLaw d).prod (Measure.infinitePi fun _ : ℕ => ν)

section Window

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
  {F : Point d → Ω → ℝ} {G : Point d → Ω → Point d} {L σ p μ0 c η lower : ℝ} {f : Point d → ℝ}
  {x0 : Point d}

structure RunHyp (ν : Measure Ω) (F : Point d → Ω → ℝ) (G : Point d → Ω → Point d)
    (f : Point d → ℝ) (L σ p μ0 c η lower : ℝ) : Prop where
  sample : SampleHyp ν F G L σ p
  grad : ∀ x, HasGradientAt f (gradient f x) x
  mean : ∀ x, ∫ ω, G x ω ∂ν = gradient f x
  lower_le : ∀ x, lower ≤ f x
  hd : 0 < d
  hp1 : 1 < p
  hp2 : p ≤ 2
  hσ : 0 ≤ σ
  hL : 0 < L
  hμ0 : 0 < μ0
  hS : 256 * (2 * (σ + L * μ0 * d / 2)) ≤ c
  hB : 512 * biasLevel L σ p μ0 c d ≤ c
  hη0 : 0 ≤ η
  hη : η * (8192 * L * d) ≤ 1

noncomputable def driftConst (L σ p μ0 c η : ℝ) (d : ℕ) : ℝ :=
  2 * η * biasLevel L σ p μ0 c d ^ 2 + L * η ^ 2 * d * (c ^ (2 - p) * (2 * (σ + L * μ0 * d / 2)) ^ p)


omit [IsProbabilityMeasure ν] in
lemma RunHyp.continuous (H : RunHyp ν F G f L σ p μ0 c η lower) : Continuous f :=
  continuous_iff_continuousAt.mpr fun y => (H.grad y).hasFDerivAt.continuousAt

omit [IsProbabilityMeasure ν] in
lemma RunHyp.c_nonneg (H : RunHyp ν F G f L σ p μ0 c η lower) : 0 ≤ c := by
  have := H.hS
  have hσ := H.hσ
  have : 0 ≤ 2 * (σ + L * μ0 * d / 2) := by
    have := H.hL; have := H.hμ0; positivity
  linarith

lemma RunHyp.measurable_gradient (H : RunHyp ν F G f L σ p μ0 c η lower) :
    Measurable (gradient f) := by
  have hc : Continuous (gradient f) := by
    refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ H.hL.le]
    exact H.sample.gradient_lipschitz H.mean x y
  exact hc.measurable

lemma RunHyp.f_bound (H : RunHyp ν F G f L σ p μ0 c η lower) {y : Point d} {R : ℝ}
    (hy : ‖y - x0‖ ≤ R) :
    f y - lower ≤ (f x0 - lower) + ‖gradient f x0‖ * R + L / 2 * R ^ 2 := by
  have hlip := H.sample.gradient_lipschitz H.mean
  have h := OracleTemplate.Gradient.smooth_upper_bound H.grad hlip x0 y
  have h1 : ⟪gradient f x0, y - x0⟫ ≤ ‖gradient f x0‖ * R :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  have hR : 0 ≤ R := (norm_nonneg _).trans hy
  have h2 : ‖y - x0‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  nlinarith [H.hL]

lemma RunHyp.grad_bound (H : RunHyp ν F G f L σ p μ0 c η lower) {y : Point d} {R : ℝ}
    (hy : ‖y - x0‖ ≤ R) : ‖gradient f y‖ ≤ ‖gradient f x0‖ + L * R := by
  have hlip := H.sample.gradient_lipschitz H.mean y x0
  have := norm_le_insert' (gradient f y) (gradient f x0)
  calc ‖gradient f y‖ ≤ ‖gradient f x0‖ + ‖gradient f y - gradient f x0‖ := by
        have := norm_sub_norm_le (gradient f y) (gradient f x0); linarith
    _ ≤ ‖gradient f x0‖ + L * R := by
        have := mul_le_mul_of_nonneg_left hy H.hL.le; linarith

lemma phiFun_nonneg (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ phiFun c t := by
  unfold phiFun; exact le_min (by positivity) (by positivity)

lemma phiFun_le_sq {t : ℝ} : phiFun c t ≤ t ^ 2 / 2 := min_le_left _ _

lemma RunHyp.run_step (H : RunHyp ν F G f L σ p μ0 c η lower) (n : ℕ) :
    Integrable (fun w : (ℕ → Sign d) × (ℕ → Ω) => f (traj F μ0 η c x0 w.1 w.2 (n + 1)) - lower) (pathLaw d ν) ∧
    Integrable (fun w : (ℕ → Sign d) × (ℕ → Ω) =>
      phiFun c ‖gradient f (traj F μ0 η c x0 w.1 w.2 n)‖) (pathLaw d ν) ∧
    ∫ w, (f (traj F μ0 η c x0 w.1 w.2 (n + 1)) - lower) ∂(pathLaw d ν) ≤
      ∫ w, (f (traj F μ0 η c x0 w.1 w.2 n) - lower) ∂(pathLaw d ν) -
        η / 4 * ∫ w, phiFun c ‖gradient f (traj F μ0 η c x0 w.1 w.2 n)‖ ∂(pathLaw d ν) +
          driftConst L σ p μ0 c η d := by
  have hc := H.c_nonneg
  have hfc := H.continuous
  have hgr : Measurable (gradient f) := H.measurable_gradient
  set X : ℕ → (ℕ → Sign d) × (ℕ → Ω) → Point d := fun m w => traj F μ0 η c x0 w.1 w.2 m
  have hXm : ∀ m, Measurable (X m) := fun m => measurable_traj H.sample.measF m
  have hR : ∀ m w, ‖X m w - x0‖ ≤ m * (|η| * c * Real.sqrt d) :=
    fun m w => traj_dist hc w.1 w.2 m
  have hfX : ∀ m, Integrable (fun w => f (X m w) - lower) (pathLaw d ν) := by
    intro m
    refine Integrable.of_bound ((hfc.measurable.comp (hXm m)).sub_const _).aestronglyMeasurable
      ((f x0 - lower) + ‖gradient f x0‖ * (m * (|η| * c * Real.sqrt d)) +
        L / 2 * (m * (|η| * c * Real.sqrt d)) ^ 2) (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (H.lower_le _))]
    exact H.f_bound (hR m w)
  have hφX : Integrable (fun w => phiFun c ‖gradient f (X n w)‖) (pathLaw d ν) := by
    refine Integrable.of_bound ?_ ((‖gradient f x0‖ + L * (n * (|η| * c * Real.sqrt d))) ^ 2 / 2)
      (Filter.Eventually.of_forall fun w => ?_)
    · unfold phiFun
      exact (((hgr.comp (hXm n)).norm.pow_const 2).div_const _ |>.min
        (((hgr.comp (hXm n)).norm.const_mul c).div_const _)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (phiFun_nonneg hc (norm_nonneg _))]
      refine phiFun_le_sq.trans ?_
      have hg := H.grad_bound (hR n w)
      have : ‖gradient f (X n w)‖ ^ 2 ≤ (‖gradient f x0‖ + L * (n * (|η| * c * Real.sqrt d))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hg 2
      linarith
  refine ⟨hfX (n + 1), hφX, ?_⟩
  set K := driftConst L σ p μ0 c η d
  set g : Point d → ℝ := fun y => f y - lower - η / 4 * phiFun c ‖gradient f y‖ + K with hg
  have hdesc := fun y => H.sample.expected_descent H.grad H.mean H.hd H.hp1 H.hp2 H.hσ H.hL H.hμ0
    H.hS H.hB H.hη0 H.hη y
  have hΦ : ∀ y, ∫⁻ z, ENNReal.ofReal (f (stepPoint F μ0 η c y z) - lower) ∂((signLaw d).prod ν) ≤
      ENNReal.ofReal (g y) := by
    intro y
    obtain ⟨hi, hb⟩ := hdesc y
    rw [← ofReal_integral_eq_lintegral_ofReal (isub hi (integrable_const lower))
      (Filter.Eventually.of_forall fun z => sub_nonneg.mpr (H.lower_le _))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub hi (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul, g, K, driftConst]
    linarith
  have hhm : Measurable (fun q : Point d × (Sign d × Ω) =>
      ENNReal.ofReal (f (stepPoint F μ0 η c q.1 q.2) - lower)) :=
    ENNReal.measurable_ofReal.comp ((hfc.measurable.comp (measurable_stepPoint H.sample.measF)).sub_const _)
  have hfresh := fresh_pair (signLaw d) ν n (fun U Ξ => traj F μ0 η c x0 U Ξ n)
    ((measurable_traj H.sample.measF n).comp (measurable_id))
    (fun U U' Ξ hU => traj_congr U U' Ξ Ξ n hU (fun _ _ => rfl))
    (fun U Ξ Ξ' hΞ => traj_congr U U Ξ Ξ' n (fun _ _ => rfl) hΞ)
    (fun q => ENNReal.ofReal (f (stepPoint F μ0 η c q.1 q.2) - lower)) hhm
  have hgnn : ∀ y, 0 ≤ g y := by
    intro y
    have h1 := hΦ y
    by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_of_nonpos hneg.le, nonpos_iff_eq_zero] at h1
    have hpos : (0 : ℝ) ≤ ∫ z, (f (stepPoint F μ0 η c y z) - lower) ∂((signLaw d).prod ν) :=
      integral_nonneg fun z => sub_nonneg.mpr (H.lower_le _)
    obtain ⟨hi, hb⟩ := hdesc y
    have hle : ∫ z, (f (stepPoint F μ0 η c y z) - lower) ∂((signLaw d).prod ν) ≤ g y := by
      rw [integral_sub hi (integrable_const _), integral_const]
      simp only [probReal_univ, one_smul, g, K, driftConst]; linarith
    linarith
  have hgX : Integrable (fun w => g (X n w)) (pathLaw d ν) :=
    ((hfX n).sub (hφX.const_mul _)).add (integrable_const K)
  have hlint : ∫⁻ w, ENNReal.ofReal (f (X (n + 1) w) - lower) ∂(pathLaw d ν) ≤
      ∫⁻ w, ENNReal.ofReal (g (X n w)) ∂(pathLaw d ν) := by
    have hfresh' : ∫⁻ w, ENNReal.ofReal (f (X (n + 1) w) - lower) ∂(pathLaw d ν) =
        ∫⁻ w, (∫⁻ z, ENNReal.ofReal (f (stepPoint F μ0 η c (X n w) z) - lower)
          ∂((signLaw d).prod ν)) ∂(pathLaw d ν) := hfresh
    rw [hfresh']
    exact lintegral_mono fun w => hΦ (X n w)
  have hreal : ∫ w, (f (X (n + 1) w) - lower) ∂(pathLaw d ν) ≤ ∫ w, g (X n w) ∂(pathLaw d ν) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfX (n + 1))
        (Filter.Eventually.of_forall fun w => sub_nonneg.mpr (H.lower_le _)),
      ← ofReal_integral_eq_lintegral_ofReal hgX (Filter.Eventually.of_forall fun w => hgnn _)]
      at hlint
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun w => hgnn _)).mp hlint
  have hsplit : ∫ w, g (X n w) ∂(pathLaw d ν) = ∫ w, (f (X n w) - lower) ∂(pathLaw d ν) -
      η / 4 * ∫ w, phiFun c ‖gradient f (X n w)‖ ∂(pathLaw d ν) + K := by
    simp only [g]
    rw [integral_add (isub (hfX n) (hφX.const_mul _)) (integrable_const K),
      integral_sub (hfX n) (hφX.const_mul _), integral_const_mul, integral_const]
    simp
  linarith

lemma RunHyp.window_sum (H : RunHyp ν F G f L σ p μ0 c η lower) :
    ∀ N, (∑ i ∈ Finset.range N, η / 4 *
        ∫ w, phiFun c ‖gradient f (traj F μ0 η c x0 w.1 w.2 i)‖ ∂(pathLaw d ν)) +
      ∫ w, (f (traj F μ0 η c x0 w.1 w.2 N) - lower) ∂(pathLaw d ν) ≤
        (f x0 - lower) + N * driftConst L σ p μ0 c η d
  | 0 => by simp [traj]
  | N + 1 => by
      have ih := H.window_sum N
      obtain ⟨-, -, hs⟩ := H.run_step (x0 := x0) N
      rw [Finset.sum_range_succ]
      push_cast
      linarith

end Window

end LongTails.Proofs.SpsaProcess
