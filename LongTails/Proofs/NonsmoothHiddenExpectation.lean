import LongTails.Proofs.NonsmoothHiddenLocal
import LongTails.Proofs.HiddenConvexExpectation
import LongTails.Proofs.GeneralNormClipping

open Set Metric InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NonsmoothHidden

open LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def localEnergy (F : E → ℝ) (c : E → E) (J : E → E →L[ℝ] E)
    (b : E) (r D : ℝ) (u : E) (k : ℕ) (s : E × E) : ℝ :=
  (k : ℝ) * (F s.1 - F u) + D / 2 * ‖s.2 - u‖ ^ 2 -
    D * ⟪s.2 - u, qField c J b r u s.1⟫

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma mean_norm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {oracle : Ω → E} {g : E} {G : ℝ}
    (hG : 0 ≤ G) (hi : Integrable oracle P)
    (hi2 : Integrable (fun ω => ‖oracle ω‖ ^ 2) P)
    (hm : ∫ ω, oracle ω ∂P = g) (hb : ∫ ω, ‖oracle ω‖ ^ 2 ∂P ≤ G ^ 2) :
    ‖g‖ ≤ G := by
  have h := GeneralNormClipping.norm_integral_sq_le hi hi2
  rw [hm] at h
  nlinarith [norm_nonneg g]

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma local_correction_measurable {c : E → E} {J : E → E →L[ℝ] E}
    {μ LJ r : ℝ} (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hr : 0 ≤ r)
    (hreg : 64 * LJ * r ≤ μ) (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (hlip : ∀ x y, ‖J x - J y‖ ≤ LJ * ‖x - y‖)
    {b u : E} (hu : u ∈ closedBall b r) : Measurable (qField c J b r u) := by
  classical
  let C : NNReal := ⟨8 * (LJ / μ) * r, by positivity⟩
  have hC : LipschitzOnWith C (fun x => corr c J x u) (closedBall b (2 * r)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    change ‖corr c J x u - corr c J y u‖ ≤ (8 * (LJ / μ) * r) * ‖x - y‖
    exact correction_lipschitz_local hμ hLJ hr hreg hJ hTaylor hlip hx hy hu
  unfold qField
  exact hC.continuousOn.measurable_piecewise continuousOn_const measurableSet_closedBall

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma localEnergy_measurable {F : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {b u : E} {r D : ℝ} (hF : Measurable F) (hq : Measurable (qField c J b r u))
    (k : ℕ) : Measurable (localEnergy F c J b r D u k) := by
  unfold localEnergy
  exact (((hF.comp measurable_fst).sub_const _).const_mul _).add
    (((measurable_snd.sub_const u).norm.pow_const 2).const_mul (D / 2)) |>.sub
      (((measurable_snd.sub_const u).inner (hq.comp measurable_fst)).const_mul D)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma ballProj_joint_measurable (r : ℝ) :
    Measurable (fun w : E × E => ballProj w.1 r w.2) := by
  classical
  unfold ballProj
  refine Measurable.ite ?_ measurable_snd ?_
  · exact measurableSet_le ((measurable_snd.sub measurable_fst).norm) measurable_const
  · exact measurable_fst.add
      ((measurable_const.div ((measurable_snd.sub measurable_fst).norm)).smul
        (measurable_snd.sub measurable_fst))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] in
lemma restartOutside_measurable (R : ℝ) : Measurable (restartOutside (E := E) R) := by
  classical
  unfold restartOutside
  exact Measurable.ite (measurableSet_le measurable_const measurable_id.norm)
    measurable_const measurable_id

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma localRun_measurable {Ω : Type*} [MeasurableSpace Ω] {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (r D : ℝ) (N k : ℕ) :
    Measurable (fun w : (E × E × E) × (Fin N → Ω) =>
      localRun oracle r D w.1.1 N k w.1.2.1 w.1.2.2 w.2) := by
  induction N generalizing k with
  | zero => exact measurable_fst.snd
  | succ N ih =>
    let y := fun w : (E × E × E) × (Fin (N + 1) → Ω) =>
      averageQuery k w.1.2.1 w.1.2.2
    have hy : Measurable y := by dsimp [y, averageQuery]; fun_prop
    have hg := ho.comp (hy.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have hz : Measurable (fun w : (E × E × E) × (Fin (N + 1) → Ω) =>
        ballProj w.1.1 (2 * r) (w.1.2.2 - D⁻¹ • oracle (y w) (w.2 0))) :=
      (ballProj_joint_measurable (2 * r)).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.snd.sub (hg.const_smul _)))
    exact (ih (k + 1)).comp
      ((measurable_fst.fst.prodMk (hy.prodMk hz)).prodMk (by fun_prop))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma localRun_mem {Ω : Type*} (oracle : E → Ω → E) {r D : ℝ} {b : E}
    (hr : 0 ≤ r) (N k : ℕ) {x z : E}
    (hx : x ∈ closedBall b (2 * r)) (hz : z ∈ closedBall b (2 * r))
    (ξ : Fin N → Ω) :
    (localRun oracle r D b N k x z ξ).1 ∈ closedBall b (2 * r) ∧
      (localRun oracle r D b N k x z ξ).2 ∈ closedBall b (2 * r) := by
  induction N generalizing k x z with
  | zero => exact ⟨hx, hz⟩
  | succ N ih =>
    exact ih (k + 1) (averageQuery_mem k hx hz)
      (ballProj_mem b _ (by positivity)) (fun i => ξ i.succ)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma local_energy_pathwise {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {p : E → E} {μ LJ r D G : ℝ} (hμ : 0 < μ) (hLJ : 0 ≤ LJ)
    (hr : 0 ≤ r) (hD : 0 < D) (hG : 0 ≤ G) (hreg : 64 * LJ * r ≤ μ)
    (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (hlip : ∀ x y, ‖J x - J y‖ ≤ LJ * ‖x - y‖)
    (heq : ∀ x, F x = H (c x))
    (hp : ∀ x, LongTails.Setups.NonsmoothHiddenConvex.IsPulledSubgradient H c J p x)
    (hpG : ∀ x, ‖p x‖ ≤ G) (k : ℕ) {b u x z g : E}
    (hu : u ∈ closedBall b r) (hx : x ∈ closedBall b (2 * r))
    (hz : z ∈ closedBall b (2 * r)) :
    let y := averageQuery k x z
    let z' := ballProj b (2 * r) (z - D⁻¹ • g)
    localEnergy F c J b r D u (k + 1) (y, z') ≤
      localEnergy F c J b r D u k (x, z) + ‖g‖ ^ 2 / (2 * D) -
        ⟪g - p y, z - u - corr c J y u⟫ +
        (96 * D * (LJ / μ) * r ^ 3 + 16 * G * (LJ / μ) * r ^ 2) / ((k : ℝ) + 1) := by
  dsimp only
  let y := averageQuery k x z
  have hy : y ∈ closedBall b (2 * r) := averageQuery_mem k hx hz
  have hM : 0 ≤ LJ / μ := div_nonneg hLJ hμ.le
  have ht : 0 < (k : ℝ) + 1 := by positivity
  have hd : ‖x - y‖ ≤ 4 * r / ((k : ℝ) + 1) := by
    rw [norm_sub_rev]
    exact local_average_displacement k hx hz
  have hqq : ‖corr c J x u - corr c J y u‖ ≤
      8 * (LJ / μ) * r * (4 * r / ((k : ℝ) + 1)) :=
    (correction_lipschitz_local hμ hLJ hr hreg hJ hTaylor hlip hx hy hu).trans
      (mul_le_mul_of_nonneg_left hd (by positivity))
  have hzu : ‖z - u‖ ≤ 3 * r := by linarith [norm_sub_ball hz hu]
  have hDrift := correction_drift_bound hD.le hr hzu hqq
  have hCross : ‖corr c J y x‖ ≤ (LJ / μ) * (4 * r / ((k : ℝ) + 1)) ^ 2 :=
    (correction_bound hμ hJ hTaylor y x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) hM)
  have hPrevious := previous_support_bound k hG hM (hpG y) hCross
  have hIdentity : ((k : ℝ) + 1) • y = ((k : ℝ) + 1 - 1) • x + z := by
    simpa only [add_sub_cancel_right] using averageQuery_identity k x z
  have hInner : ‖u - b‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hu
  have hStep := averaged_energy_step (g := g) (by have := Nat.cast_nonneg (α := ℝ) k; linarith : 1 ≤ (k : ℝ) + 1)
    hr hD hIdentity hInner (correction_small hμ hLJ hr hreg hJ hTaylor hy hu).2
    heq (hp y) (exists_preimage hμ (hJ y) (c u - c y))
    (exists_preimage hμ (hJ y) (c x - c y))
  dsimp only at hStep
  simp only [add_sub_cancel_right] at hStep
  change localEnergy F c J b r D u (k + 1)
      (y, ballProj b (2 * r) (z - D⁻¹ • g)) ≤ _
  simp only [localEnergy, qField_eq hx, qField_eq hy, Nat.cast_add, Nat.cast_one]
  rw [add_div]
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma localEnergy_abs_le {F : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {b u x z : E} {r D G : ℝ} (hr : 0 ≤ r) (hD : 0 ≤ D) (k : ℕ)
    (hu : u ∈ closedBall b r) (hz : z ∈ closedBall b (2 * r))
    (hgap : |F x - F u| ≤ 4 * G * r) (hq : ‖qField c J b r u x‖ ≤ r) :
    |localEnergy F c J b r D u k (x, z)| ≤
      4 * (k : ℝ) * G * r + 15 / 2 * D * r ^ 2 := by
  have hn : ‖z - u‖ ≤ 3 * r := by linarith [norm_sub_ball hz hu]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hi := (abs_real_inner_le_norm (z - u) (qField c J b r u x)).trans
    (mul_le_mul hn hq (norm_nonneg _) (by positivity))
  have h1 : |(k : ℝ) * (F x - F u)| ≤ 4 * (k : ℝ) * G * r := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    nlinarith [mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg k)]
  have h2 : |D / 2 * ‖z - u‖ ^ 2| ≤ 9 / 2 * D * r ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs hD]
  have h3 : |D * ⟪z - u, qField c J b r u x⟫| ≤ 3 * D * r ^ 2 := by
    rw [abs_mul, abs_of_nonneg hD]
    nlinarith [mul_le_mul_of_nonneg_left hi hD]
  have h4 := abs_sub ((k : ℝ) * (F x - F u) + D / 2 * ‖z - u‖ ^ 2)
    (D * ⟪z - u, qField c J b r u x⟫)
  have h5 := abs_add_le ((k : ℝ) * (F x - F u)) (D / 2 * ‖z - u‖ ^ 2)
  unfold localEnergy
  dsimp only
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma localEnergy_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {b u : E} {r D G : ℝ} (hr : 0 ≤ r) (hD : 0 ≤ D) (k : ℕ)
    (hu : u ∈ closedBall b r) (hF : Measurable F)
    (hqm : Measurable (qField c J b r u))
    (hgap : ∀ x ∈ closedBall b (2 * r), |F x - F u| ≤ 4 * G * r)
    (hq : ∀ x ∈ closedBall b (2 * r), ‖qField c J b r u x‖ ≤ r)
    {state : Ω → E × E} (hm : Measurable state)
    (hstate : ∀ ω, (state ω).1 ∈ closedBall b (2 * r) ∧
      (state ω).2 ∈ closedBall b (2 * r)) :
    Integrable (fun ω => localEnergy F c J b r D u k (state ω)) P := by
  apply Integrable.of_bound ((localEnergy_measurable hF hqm k).comp hm).aestronglyMeasurable
    (4 * (k : ℝ) * G * r + 15 / 2 * D * r ^ 2)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  exact localEnergy_abs_le hr hD k hu (hstate ω).2
    (hgap _ (hstate ω).1) (hq _ (hstate ω).1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma integrate_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {oracle : Ω → E} {p V : E}
    {a C D G : ℝ} (hD : 0 < D) (hf : Integrable f P) (ho : Integrable oracle P)
    (ho2 : Integrable (fun ω => ‖oracle ω‖ ^ 2) P)
    (hm : ∫ ω, oracle ω ∂P = p) (hG : ∫ ω, ‖oracle ω‖ ^ 2 ∂P ≤ G ^ 2)
    (hb : ∀ ω, f ω ≤ a + ‖oracle ω‖ ^ 2 / (2 * D) - ⟪oracle ω - p, V⟫ + C) :
    (∫ ω, f ω ∂P) ≤ a + G ^ 2 / (2 * D) + C := by
  have hn : Integrable (fun ω => oracle ω - p) P := ho.sub (integrable_const _)
  have hni : Integrable (fun ω => ⟪oracle ω - p, V⟫) P := hn.inner_const V
  have hz : (∫ ω, ⟪oracle ω - p, V⟫ ∂P) = 0 := by
    calc (∫ ω, ⟪oracle ω - p, V⟫ ∂P) = ∫ ω, ⟪V, oracle ω - p⟫ ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
      _ = 0 := by
        rw [integral_inner (𝕜 := ℝ) hn V, integral_sub ho (integrable_const _), hm]
        simp
  have hi : Integrable (fun ω => a + ‖oracle ω‖ ^ 2 / (2 * D)) P :=
    (integrable_const a).add (ho2.div_const (2 * D))
  have hsub : Integrable (fun ω => a + ‖oracle ω‖ ^ 2 / (2 * D) - ⟪oracle ω - p, V⟫) P :=
    hi.sub hni
  have hB : Integrable (fun ω => a + ‖oracle ω‖ ^ 2 / (2 * D) - ⟪oracle ω - p, V⟫ + C) P :=
    hsub.add (integrable_const C)
  have h := integral_mono hf hB hb
  rw [integral_add hsub (integrable_const C), integral_sub hi hni,
    integral_add (integrable_const a) (ho2.div_const (2 * D)), integral_div, hz] at h
  simp only [integral_const, probReal_univ, one_smul, sub_zero] at h
  exact h.trans (by
    have hv := div_le_div_of_nonneg_right hG (by positivity : 0 ≤ 2 * D)
    linarith)

lemma local_energy_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {g : E → E} {oracle : E → Ω → E} {μ LJ r D G : ℝ}
    (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hr : 0 ≤ r) (hD : 0 < D) (hG : 0 ≤ G)
    (hreg : 64 * LJ * r ≤ μ) (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    (hlip : ∀ x y, ‖J x - J y‖ ≤ LJ * ‖x - y‖)
    (heq : ∀ x, F x = H (c x)) (hF : Measurable F)
    (hg : ∀ x, LongTails.Setups.NonsmoothHiddenConvex.IsPulledSubgradient H c J g x)
    (hom : Measurable (Function.uncurry oracle)) (hoi : ∀ x, Integrable (oracle x) P)
    (hoi2 : ∀ x, Integrable (fun ω => ‖oracle x ω‖ ^ 2) P)
    (homean : ∀ x, ∫ ω, oracle x ω ∂P = g x)
    (hoG : ∀ x, ∫ ω, ‖oracle x ω‖ ^ 2 ∂P ≤ G ^ 2)
    (k : ℕ) {b u x z : E} (hu : u ∈ closedBall b r)
    (hx : x ∈ closedBall b (2 * r)) (hz : z ∈ closedBall b (2 * r)) :
    let y := averageQuery k x z
    let state := fun ω => (y, ballProj b (2 * r) (z - D⁻¹ • oracle y ω))
    Integrable (fun ω => localEnergy F c J b r D u (k + 1) (state ω)) P ∧
      (∫ ω, localEnergy F c J b r D u (k + 1) (state ω) ∂P) ≤
        localEnergy F c J b r D u k (x, z) + G ^ 2 / (2 * D) +
          (96 * D * (LJ / μ) * r ^ 3 + 16 * G * (LJ / μ) * r ^ 2) / ((k : ℝ) + 1) := by
  dsimp only
  let y := averageQuery k x z
  have hy : y ∈ closedBall b (2 * r) := averageQuery_mem k hx hz
  have hpG : ∀ v, ‖g v‖ ≤ G := fun v =>
    mean_norm_le hG (hoi v) (hoi2 v) (homean v) (hoG v)
  have hqm := local_correction_measurable hμ hLJ hr hreg hJ hTaylor hlip hu
  have hgap : ∀ v ∈ closedBall b (2 * r), |F v - F u| ≤ 4 * G * r :=
    fun v hv => local_gap_abs_le hμ hLJ hG hr hreg hJ hTaylor heq hg hpG hv hu
  have hq : ∀ v ∈ closedBall b (2 * r), ‖qField c J b r u v‖ ≤ r := by
    intro v hv
    rw [qField_eq hv]
    exact (correction_small hμ hLJ hr hreg hJ hTaylor hv hu).2
  have hmOracle : Measurable (oracle y) := hom.comp (measurable_const.prodMk measurable_id)
  have hmState : Measurable (fun ω => (y, ballProj b (2 * r) (z - D⁻¹ • oracle y ω))) :=
    measurable_const.prodMk ((ballProj_measurable b (2 * r)).comp
      (measurable_const.sub (hmOracle.const_smul _)))
  have hstate : ∀ ω, y ∈ closedBall b (2 * r) ∧
      ballProj b (2 * r) (z - D⁻¹ • oracle y ω) ∈ closedBall b (2 * r) :=
    fun ω => ⟨hy, ballProj_mem b _ (by positivity)⟩
  have hfi := localEnergy_integrable (P := P) hr hD.le (k + 1) hu hF hqm hgap hq hmState hstate
  refine ⟨hfi, integrate_step (V := z - u - corr c J y u)
    hD hfi (hoi y) (hoi2 y) (homean y) (hoG y) ?_⟩
  intro ω
  exact local_energy_pathwise hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hg hpG k hu hx hz

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma localEnergy_endpoint {F : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {μ LJ r D : ℝ} (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hreg : 64 * LJ * r ≤ μ) (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    {b u x z : E} (hu : u ∈ closedBall b r) (hx : x ∈ closedBall b (2 * r))
    (hz : z ∈ closedBall b (2 * r)) (k : ℕ) :
    (k : ℝ) * (F x - F u) ≤ localEnergy F c J b r D u k (x, z) +
      27 * D * (LJ / μ) * r ^ 3 := by
  have hn : ‖z - u‖ ≤ 3 * r := by linarith [norm_sub_ball hz hu]
  have hq := (correction_small hμ hLJ hr hreg hJ hTaylor hx hu).1
  have hi := (real_inner_le_norm (z - u) (corr c J x u)).trans
    (mul_le_mul hn hq (norm_nonneg _) (by positivity))
  simp only [localEnergy, qField_eq hx]
  nlinarith [mul_le_mul_of_nonneg_left hi hD, mul_nonneg hD (sq_nonneg ‖z - u‖)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma localEnergy_initial {F : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
    {μ LJ r D : ℝ} (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
    (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
    {b u : E} (hu : u ∈ closedBall b r) :
    localEnergy F c J b r D u 0 (b, b) ≤ D * r ^ 2 / 2 + D * (LJ / μ) * r ^ 3 := by
  have hb : b ∈ closedBall b (2 * r) := mem_closedBall_self (by positivity)
  have hn : ‖b - u‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hu
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hq : ‖corr c J b u‖ ≤ (LJ / μ) * r ^ 2 :=
    (correction_bound hμ hJ hTaylor b u).trans
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hs) (by positivity))
  have hi := (abs_real_inner_le_norm (b - u) (corr c J b u)).trans
    (mul_le_mul hn hq (norm_nonneg _) hr)
  have hlo := (neg_le_abs ⟪b - u, corr c J b u⟫).trans hi
  simp only [localEnergy, Nat.cast_zero, zero_mul, zero_add, qField_eq hb]
  nlinarith [mul_le_mul_of_nonneg_left hs hD, mul_le_mul_of_nonneg_left hlo hD]

end OracleTemplate.NonsmoothHidden
