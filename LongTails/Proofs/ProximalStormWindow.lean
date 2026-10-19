import LongTails.Proofs.ProximalStormRun

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.f_continuous (H : Hyp p f g Lbar Γ xstar) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (H.grad x).differentiableAt.continuousAt

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.phiGrad_continuous (H : Hyp p f g Lbar Γ xstar) (lam : ℝ) :
    Continuous fun z : E × E => phiGrad f lam z.1 z.2 := by
  unfold phiGrad
  exact (H.grad_continuous.comp continuous_snd).add
    ((continuous_snd.sub continuous_fst).const_smul _)

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.phi_continuous (H : Hyp p f g Lbar Γ xstar) (lam : ℝ) :
    Continuous fun z : E × E => phi f lam z.1 z.2 := by
  unfold phi
  exact (H.f_continuous.comp continuous_snd).add
    (((continuous_snd.sub continuous_fst).norm.pow 2).div_const _)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.innerPot_continuous (H : Hyp p f g Lbar Γ xstar) {lam : ℝ} (hlam : 0 < lam)
    (eta a Γh : ℝ) : Continuous fun z : E × (E × E) => innerPot f lam eta a Γh z.1 z.2 := by
  have hpr := H.continuous_prox hlam
  have hφ := H.phi_continuous lam
  have hG := H.phiGrad_continuous lam
  unfold innerPot innerGap innerErr
  have h1 : Continuous fun z : E × (E × E) => phi f lam z.1 z.2.1 :=
    hφ.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun z : E × (E × E) => phi f lam z.1 (prox f lam z.1) :=
    hφ.comp (continuous_fst.prodMk (hpr.comp continuous_fst))
  have h3 : Continuous fun z : E × (E × E) => phiGrad f lam z.1 z.2.1 :=
    hG.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  exact ((h1.sub h2).add (((continuous_snd.comp continuous_snd).sub h3).norm.pow 2
    |>.const_mul _)).sub ((h3.norm.pow 2).const_mul _)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.dist2_continuous (H : Hyp p f g Lbar Γ xstar) {lam : ℝ} (hlam : 0 < lam) :
    Continuous fun x : E => ‖x - prox f lam x‖ ^ 2 :=
  ((continuous_id.sub (H.continuous_prox hlam)).norm.pow 2)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.pot_contract (H : Hyp p f g Lbar Γ xstar) {lam eta a Γh c : ℝ}
    (T : InnerTune Lbar lam eta a Γh) (hc0 : 0 ≤ c) (hc1 : c * lam ≤ eta / 2) (hc2 : c ≤ a / 2)
    (xt : E) (s : E × E) :
    ∫ ω, innerPot f lam eta a Γh xt (innerStep g lam eta a xt s ω) ∂p ≤
      (1 - c) * innerPot f lam eta a Γh xt s +
        4 * eta * a * Γ ^ 2 * ‖xt - prox f lam xt‖ ^ 2 / lam ^ 2 := by
  obtain ⟨-, hb⟩ := H.pot_step T xt s
  have hub := (H.pot_bounds T xt s).2
  have hpl := H.phi_pl T.lam_pos xt s.1
  have hgap : innerGap f lam xt s.1 ≤ lam / 2 * ‖phiGrad f lam xt s.1‖ ^ 2 := hpl
  have hea : c * (eta / a) ≤ eta / 2 := by
    have : c * (eta / a) = (c / a) * eta := by field_simp
    rw [this]
    have : c / a ≤ 1 / 2 := by rw [div_le_iff₀ T.a_pos]; linarith
    nlinarith [T.eta_nn]
  have h1 : c * innerGap f lam xt s.1 ≤ eta / 4 * ‖phiGrad f lam xt s.1‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hgap hc0
    nlinarith [sq_nonneg ‖phiGrad f lam xt s.1‖]
  have h2 : c * (eta / a * ‖innerErr f lam xt s‖ ^ 2) ≤ eta / 2 * ‖innerErr f lam xt s‖ ^ 2 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hea (sq_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left hub hc0
  nlinarith

variable (lam eta a Γh : ℝ)

noncomputable def runPot (X : (ℕ → Ω) → E) (n0 t : ℕ) (ξ : ℕ → Ω) : ℝ :=
  innerPot f lam eta a Γh (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t)

variable {lam eta a Γh}

lemma Hyp.run_step (H : Hyp p f g Lbar Γ xstar) (T : InnerTune Lbar lam eta a Γh)
    {X : (ℕ → Ω) → E} (hX : Measurable X) {n0 : ℕ}
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 → ξ i = ξ' i) → X ξ = X ξ')
    (w : E → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c * lam ≤ eta / 2) (hc2 : c ≤ a / 2) (hc : c ≤ 1) (t : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 (t + 1) ξ) ∂P +
        ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (eta / 4 *
          ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t).1‖ ^ 2)) ∂P ≤
      ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 t ξ) ∂P +
        ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (4 * eta * a * Γ ^ 2 *
          ‖X ξ - prox f lam (X ξ)‖ ^ 2 / lam ^ 2)) ∂P ∧
    ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 (t + 1) ξ) ∂P ≤
      ENNReal.ofReal (1 - c) *
          ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 t ξ) ∂P +
        ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (4 * eta * a * Γ ^ 2 *
          ‖X ξ - prox f lam (X ξ)‖ ^ 2 / lam ^ 2)) ∂P := by
  have hlam := T.lam_pos
  set S : (ℕ → Ω) → E × (E × E) := fun ξ => (X ξ, innerRun g lam eta a (X ξ) ξ n0 t)
  have hS : Measurable S := hX.prodMk (measurable_innerRun H.meas lam eta a hX n0 t)
  have hSdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 + t + 1 → ξ i = ξ' i) → S ξ = S ξ' := by
    intro ξ ξ' h
    simp only [S, Prod.mk.injEq]
    exact ⟨hdep ξ ξ' fun i hi => h i (by omega), innerRun_congr g lam eta a hdep t ξ ξ' h⟩
  set h : E × (E × E) → Ω → ℝ := fun z ω =>
    w z.1 * innerPot f lam eta a Γh z.1 (innerStep g lam eta a z.1 z.2 ω)
  have hpc := H.innerPot_continuous hlam eta a Γh
  have hh : Measurable (Function.uncurry h) := by
    have h1 : Measurable fun z : (E × (E × E)) × Ω => w z.1.1 := hw.comp (by fun_prop)
    have h2 : Measurable fun z : (E × (E × E)) × Ω =>
        innerPot f lam eta a Γh z.1.1 (innerStep g lam eta a z.1.1 z.1.2 z.2) :=
      hpc.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_innerStep H.meas lam eta a))
    exact h1.mul h2
  have hpot0 : ∀ xt s, 0 ≤ innerPot f lam eta a Γh xt s := by
    intro xt s
    have hb := (H.pot_bounds T xt s).1
    have hg0 : 0 ≤ innerGap f lam xt s.1 := by
      simp only [innerGap]; linarith [H.phi_prox_le hlam xt s.1]
    have : 0 ≤ eta / a * ‖innerErr f lam xt s‖ ^ 2 :=
      mul_nonneg (div_nonneg T.eta_nn T.a_pos.le) (sq_nonneg _)
    linarith
  have hh0 : ∀ z ω, 0 ≤ h z ω := fun z ω => mul_nonneg (hw0 _) (hpot0 _ _)
  have hhi : ∀ z, Integrable (h z) p := fun z => ((H.pot_step T z.1 z.2).1.const_mul _)
  have hrun : ∀ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 (t + 1) ξ) =
      ENNReal.ofReal (h (S ξ) (ξ (n0 + t + 1))) := fun ξ => rfl
  set K : E → ℝ := fun x => 4 * eta * a * Γ ^ 2 * ‖x - prox f lam x‖ ^ 2 / lam ^ 2
  have hK0 : ∀ x, 0 ≤ K x := fun x => by
    have := T.eta_nn; have := T.a_pos
    show 0 ≤ 4 * eta * a * Γ ^ 2 * ‖x - prox f lam x‖ ^ 2 / lam ^ 2
    positivity
  have hKm : Measurable fun x => w x * K x :=
    hw.mul (((H.dist2_continuous hlam).measurable.const_mul _).div_const _)
  have hKX : Measurable fun ξ => ENNReal.ofReal (w (X ξ) * K (X ξ)) :=
    ENNReal.measurable_ofReal.comp (hKm.comp hX)
  constructor
  · set r : E × (E × E) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (w z.1 * innerPot f lam eta a Γh z.1 z.2) + ENNReal.ofReal (w z.1 * K z.1) -
        ENNReal.ofReal (w z.1 * (eta / 4 * ‖phiGrad f lam z.1 z.2.1‖ ^ 2))
    have hpt : ∀ z, ENNReal.ofReal (∫ ω, h z ω ∂p) +
        ENNReal.ofReal (w z.1 * (eta / 4 * ‖phiGrad f lam z.1 z.2.1‖ ^ 2)) ≤
        ENNReal.ofReal (w z.1 * innerPot f lam eta a Γh z.1 z.2) + ENNReal.ofReal (w z.1 * K z.1) := by
      intro z
      have hb := (H.pot_step T z.1 z.2).2
      have hint : ∫ ω, h z ω ∂p = w z.1 *
          ∫ ω, innerPot f lam eta a Γh z.1 (innerStep g lam eta a z.1 z.2 ω) ∂p :=
        integral_const_mul _ _
      rw [hint, ← ENNReal.ofReal_add (mul_nonneg (hw0 _) (integral_nonneg fun _ => hpot0 _ _))
        (mul_nonneg (hw0 _) (by have := T.eta_nn; positivity)),
        ← ENNReal.ofReal_add (mul_nonneg (hw0 _) (hpot0 _ _)) (mul_nonneg (hw0 _) (hK0 _))]
      apply ENNReal.ofReal_le_ofReal
      have hE : 0 ≤ eta / 2 * ‖innerErr f lam z.1 z.2‖ ^ 2 := by have := T.eta_nn; positivity
      have := mul_le_mul_of_nonneg_left hb (hw0 z.1)
      simp only [K]
      nlinarith [hw0 z.1, mul_nonneg (hw0 z.1) hE]
    have hm1 : Measurable fun ξ => ENNReal.ofReal (w (X ξ) * (eta / 4 *
        ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t).1‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((hw.comp hX).mul
        ((((H.phiGrad_continuous lam).measurable.comp
          (hX.prodMk (measurable_innerRun H.meas lam eta a hX n0 t).fst)).norm.pow_const 2).const_mul _))
    calc ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 (t + 1) ξ) ∂P +
          ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (eta / 4 *
            ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t).1‖ ^ 2)) ∂P
        ≤ ∫⁻ ξ, ENNReal.ofReal (∫ ω, h (S ξ) ω ∂p) ∂P +
          ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (eta / 4 *
            ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t).1‖ ^ 2)) ∂P := by
          exact add_le_add
            (tower_le p (n0 + t + 1) S hS hSdep h hh hh0 hhi _ fun z => le_rfl) le_rfl
      _ = ∫⁻ ξ, (ENNReal.ofReal (∫ ω, h (S ξ) ω ∂p) + ENNReal.ofReal (w (X ξ) * (eta / 4 *
            ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t).1‖ ^ 2))) ∂P :=
          (lintegral_add_right _ hm1).symm
      _ ≤ ∫⁻ ξ, (ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 t ξ) +
            ENNReal.ofReal (w (X ξ) * K (X ξ))) ∂P := lintegral_mono fun ξ => hpt (S ξ)
      _ = _ := by
          exact lintegral_add_right _ hKX
  · have hpt : ∀ z, ENNReal.ofReal (∫ ω, h z ω ∂p) ≤
        ENNReal.ofReal (1 - c) * ENNReal.ofReal (w z.1 * innerPot f lam eta a Γh z.1 z.2) +
          ENNReal.ofReal (w z.1 * K z.1) := by
      intro z
      have hb := H.pot_contract T hc0 hc1 hc2 z.1 z.2 (g := g)
      have hint : ∫ ω, h z ω ∂p = w z.1 *
          ∫ ω, innerPot f lam eta a Γh z.1 (innerStep g lam eta a z.1 z.2 ω) ∂p :=
        integral_const_mul _ _
      rw [hint, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add (mul_nonneg (by linarith) (mul_nonneg (hw0 _) (hpot0 _ _)))
          (mul_nonneg (hw0 _) (hK0 _))]
      apply ENNReal.ofReal_le_ofReal
      have := mul_le_mul_of_nonneg_left hb (hw0 z.1)
      simp only [K]
      nlinarith [hw0 z.1]
    calc ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 (t + 1) ξ) ∂P
        ≤ ∫⁻ ξ, ENNReal.ofReal (∫ ω, h (S ξ) ω ∂p) ∂P := by
          exact tower_le p (n0 + t + 1) S hS hSdep h hh hh0 hhi _ fun z => le_rfl
      _ ≤ ∫⁻ ξ, (ENNReal.ofReal (1 - c) *
            ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 t ξ) +
            ENNReal.ofReal (w (X ξ) * K (X ξ))) ∂P := lintegral_mono fun ξ => hpt (S ξ)
      _ = _ := by
          rw [lintegral_add_right _ hKX, lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp ((hw.comp hX).mul
            (hpc.measurable.comp hS))

end OracleTemplate.ProximalStorm

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E} {lam eta a Γh : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma Hyp.run_init (H : Hyp p f g Lbar Γ xstar) (T : InnerTune Lbar lam eta a Γh)
    {X : (ℕ → Ω) → E} (hX : Measurable X) {n0 : ℕ}
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 → ξ i = ξ' i) → X ξ = X ξ')
    (w : E → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) :
    ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 0 ξ) ∂P ≤
      ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (((Lbar + 1 / lam) + eta / a * (Γ ^ 2 *
        (Lbar + 1 / lam) ^ 2)) * ‖X ξ - prox f lam (X ξ)‖ ^ 2)) ∂P := by
  have hlam := T.lam_pos
  set h : E → Ω → ℝ := fun x ω => w x * innerPot f lam eta a Γh x (x, g x ω)
  have hpc := H.innerPot_continuous hlam eta a Γh
  have hh : Measurable (Function.uncurry h) := by
    have h1 : Measurable fun z : E × Ω => w z.1 := hw.comp measurable_fst
    have h2 : Measurable fun z : E × Ω => innerPot f lam eta a Γh z.1 (z.1, g z.1 z.2) :=
      hpc.measurable.comp (measurable_fst.prodMk (measurable_fst.prodMk H.meas))
    exact h1.mul h2
  have hpot0 : ∀ xt s, 0 ≤ innerPot f lam eta a Γh xt s := by
    intro xt s
    have hb := (H.pot_bounds T xt s).1
    have hg0 : 0 ≤ innerGap f lam xt s.1 := by
      simp only [innerGap]; linarith [H.phi_prox_le hlam xt s.1]
    have : 0 ≤ eta / a * ‖innerErr f lam xt s‖ ^ 2 :=
      mul_nonneg (div_nonneg T.eta_nn T.a_pos.le) (sq_nonneg _)
    linarith
  have herr : ∀ x ω, innerErr f lam x (x, g x ω) = g x ω - gradient f x := by
    intro x ω; simp [innerErr, phiGrad]
  have hup : ∀ x ω, innerPot f lam eta a Γh x (x, g x ω) ≤
      innerGap f lam x x + eta / a * ‖g x ω - gradient f x‖ ^ 2 := by
    intro x ω
    have := (H.pot_bounds T x (x, g x ω)).2
    rwa [herr] at this
  have hint : ∀ x, Integrable (fun ω => innerPot f lam eta a Γh x (x, g x ω)) p := by
    intro x
    refine (((integrable_const (innerGap f lam x x)).add
      ((H.var_int x).const_mul (eta / a)))).mono'
      (hpc.measurable.comp (measurable_const.prodMk
        (measurable_const.prodMk (H.meas.comp (measurable_const.prodMk measurable_id))))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hpot0 _ _)]
    exact hup x ω
  have hhi : ∀ x, Integrable (h x) p := fun x => (hint x).const_mul _
  have hh0 : ∀ x ω, 0 ≤ h x ω := fun x ω => mul_nonneg (hw0 _) (hpot0 _ _)
  have hb : ∀ x, ENNReal.ofReal (∫ ω, h x ω ∂p) ≤ ENNReal.ofReal (w x * (((Lbar + 1 / lam) +
      eta / a * (Γ ^ 2 * (Lbar + 1 / lam) ^ 2)) * ‖x - prox f lam x‖ ^ 2)) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    have hi1 : ∫ ω, innerPot f lam eta a Γh x (x, g x ω) ∂p ≤
        innerGap f lam x x + eta / a * ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p := by
      have hI : Integrable (fun ω => innerGap f lam x x +
          eta / a * ‖g x ω - gradient f x‖ ^ 2) p :=
        (integrable_const _).add ((H.var_int x).const_mul _)
      have := integral_mono (hint x) hI (hup x)
      rwa [integral_add (integrable_const _) ((H.var_int x).const_mul _), integral_const,
        integral_const_mul, probReal_univ, one_smul] at this
    have hgap := H.phi_start_le hlam x
    have hn := H.start_noise hlam x
    have hea : 0 ≤ eta / a := div_nonneg T.eta_nn T.a_pos.le
    have : ∫ ω, h x ω ∂p = w x * ∫ ω, innerPot f lam eta a Γh x (x, g x ω) ∂p :=
      integral_const_mul _ _
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (hw0 x)
    have h2 := mul_le_mul_of_nonneg_left hn hea
    simp only [innerGap] at hi1
    nlinarith
  exact tower_le p n0 X hX hdep h hh hh0 hhi _ hb

lemma Hyp.inner_window (H : Hyp p f g Lbar Γ xstar) (T : InnerTune Lbar lam eta a Γh)
    {X : (ℕ → Ω) → E} (hX : Measurable X) {n0 : ℕ}
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 → ξ i = ξ' i) → X ξ = X ξ')
    (w : E → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c * lam ≤ eta / 2) (hc2 : c ≤ a / 2) (hc : c ≤ 1) (T0 W : ℕ) :
    ∑ j ∈ Finset.range W, ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (eta / 4 *
        ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 (T0 + j)).1‖ ^ 2)) ∂P ≤
      (1 - ENNReal.ofReal c) ^ T0 *
          ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (((Lbar + 1 / lam) + eta / a * (Γ ^ 2 *
            (Lbar + 1 / lam) ^ 2)) * ‖X ξ - prox f lam (X ξ)‖ ^ 2)) ∂P +
        (ENNReal.ofReal c)⁻¹ * ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (4 * eta * a * Γ ^ 2 *
          ‖X ξ - prox f lam (X ξ)‖ ^ 2 / lam ^ 2)) ∂P +
        W * ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (4 * eta * a * Γ ^ 2 *
          ‖X ξ - prox f lam (X ξ)‖ ^ 2 / lam ^ 2)) ∂P := by
  set u : ℕ → ℝ≥0∞ := fun t =>
    ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * runPot (f := f) (g := g) lam eta a Γh X n0 t ξ) ∂P
  set v : ℕ → ℝ≥0∞ := fun t => ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (eta / 4 *
    ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 t).1‖ ^ 2)) ∂P
  set K := ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (4 * eta * a * Γ ^ 2 *
    ‖X ξ - prox f lam (X ξ)‖ ^ 2 / lam ^ 2)) ∂P
  have hstep := fun t => H.run_step T hX hdep w hw hw0 hc0.le hc1 hc2 hc t
  have h1 : ∀ t, u (t + 1) + v t ≤ u t + K := fun t => (hstep t).1
  have hsub : ENNReal.ofReal (1 - c) = 1 - ENNReal.ofReal c := by
    rw [ENNReal.ofReal_sub _ hc0.le, ENNReal.ofReal_one]
  have h2 : ∀ t, u (t + 1) ≤ (1 - ENNReal.ofReal c) * u t + K := by
    intro t; rw [← hsub]; exact (hstep t).2
  have hc1' : ENNReal.ofReal c ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc
  have hc0' : ENNReal.ofReal c ≠ 0 := by simpa using hc0
  have hw' := window_bound u v K (ENNReal.ofReal c) hc1' hc0' h1 h2 T0 W
  refine hw'.trans ?_
  have hu0 := H.run_init T hX hdep w hw hw0 (n0 := n0)
  rw [ENNReal.div_eq_inv_mul]
  gcongr

end OracleTemplate.ProximalStorm
