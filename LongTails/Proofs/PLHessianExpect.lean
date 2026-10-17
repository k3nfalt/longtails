import LongTails.Proofs.PLHessianStep

open Set Metric MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.PLHessian

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type} [MeasurableSpace Ω]

structure Hyp (p : Measure Ω) (f : E → ℝ) (g : E → Ω → E) (u : E) (L μ ρ σ K : ℝ) : Prop where
  grad : ∀ x, HasGradientAt f (gradient f x) x
  lip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  diff : Differentiable ℝ (gradient f)
  hess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖
  min : IsMinOn f univ u
  pl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  var_int : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  kurt_int : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 4) p
  var : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2
  kurt : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 4 ∂p ≤ K * σ ^ 4
  L_pos : 0 < L
  μ_pos : 0 < μ
  μ_le : μ ≤ L
  ρ_nn : 0 ≤ ρ
  σ_nn : 0 ≤ σ
  K_ge : 1 ≤ K

noncomputable def pot (f : E → ℝ) (u : E) (lam Φ0 : ℝ) (x : E) : ℝ :=
  distSq f u x + lam * hub (Φ0 / 4) (Φ0 / 4) (f x - f u)

variable {p : Measure Ω} {f : E → ℝ} {g : E → Ω → E} {u : E} {L μ ρ σ K : ℝ}

omit [BorelSpace E] in
lemma Hyp.continuous (H : Hyp p f g u L μ ρ σ K) : Continuous f :=
  continuous_iff_continuousAt.mpr fun z => (H.grad z).continuousAt

omit [BorelSpace E] in
lemma Hyp.pot_continuous (H : Hyp p f g u L μ ρ σ K) {lam Φ0 : ℝ} (hΦ0 : 0 < Φ0) :
    Continuous (pot f u lam Φ0) := by
  unfold pot
  exact distSq_continuous.add (continuous_const.mul
    ((hub_continuous (by positivity)).comp (H.continuous.sub continuous_const)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pot_nonneg {lam Φ0 : ℝ} (hlam : 0 ≤ lam) (hΦ0 : 0 < Φ0) (x : E) : 0 ≤ pot f u lam Φ0 x := by
  unfold pot distSq
  have := hub_nonneg (a := Φ0 / 4) (by positivity : (0:ℝ) < Φ0 / 4) (f x - f u)
  positivity



omit [BorelSpace E] in
lemma Hyp.aim_region (H : Hyp p f g u L μ ρ σ K) {Φ0 : ℝ} (hΦ0ρ : 36864 * ρ ^ 2 * Φ0 ≤ μ ^ 3)
    {x p0 : E} (hp0f : f p0 = f u) (hgp0 : gradient f p0 = 0)
    (hD : μ * ‖x - p0‖ ^ 2 ≤ 16 * (f x - f u)) (hA : f x - f u ≤ Φ0) :
    f x - f u ≤ ⟪gradient f x, x - p0⟫ := by
  have ha := aiming H.ρ_nn H.grad H.diff H.hess hgp0 x
  rw [hp0f] at ha
  have hρ := H.ρ_nn
  have hμ := H.μ_pos
  set d := x - p0
  have hn := norm_nonneg d
  have hsq : (ρ * ‖d‖) ^ 2 ≤ (μ / 48) ^ 2 := by
    have h4 : μ * ‖d‖ ^ 2 ≤ 16 * Φ0 := by linarith
    have h5 : ρ ^ 2 * (μ * ‖d‖ ^ 2) ≤ ρ ^ 2 * (16 * Φ0) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : μ * (ρ * ‖d‖) ^ 2 ≤ μ * (μ / 48) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left h6 hμ
  have hρd : ρ * ‖d‖ ≤ μ / 48 := by
    have h7 : 0 ≤ ρ * ‖d‖ := by positivity
    nlinarith [sq_nonneg (ρ * ‖d‖ - μ / 48), sq_nonneg (ρ * ‖d‖ + μ / 48)]
  have h8 : 3 * ρ * ‖d‖ ^ 3 ≤ f x - f u := by
    have e : 3 * ρ * ‖d‖ ^ 3 = 3 * (ρ * ‖d‖) * ‖d‖ ^ 2 := by ring
    rw [e]
    have : 3 * (ρ * ‖d‖) * ‖d‖ ^ 2 ≤ 3 * (μ / 48) * ‖d‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma far_inner {G d : E} {Φ : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hΦ : 0 ≤ Φ)
    (hG2 : ‖G‖ ^ 2 ≤ 2 * L * Φ) (hD : μ * ‖d‖ ^ 2 ≤ 16 * Φ) :
    -(6 * Real.sqrt (L / μ) * Φ) ≤ ⟪G, d⟫ := by
  set sk := Real.sqrt (L / μ)
  have hsk2 : sk ^ 2 = L / μ := Real.sq_sqrt (by positivity)
  have hcs : ⟪G, d⟫ ^ 2 ≤ ‖G‖ ^ 2 * ‖d‖ ^ 2 := by
    have := abs_real_inner_le_norm G d
    rw [← mul_pow]
    exact sq_le_sq' (by linarith [neg_abs_le ⟪G, d⟫]) (le_trans (le_abs_self _) this)
  have hd2 : ‖d‖ ^ 2 ≤ 16 * Φ / μ := by rw [le_div_iff₀ hμ]; linarith
  have h1 : ‖G‖ ^ 2 * ‖d‖ ^ 2 ≤ (2 * L * Φ) * (16 * Φ / μ) :=
    mul_le_mul hG2 hd2 (by positivity) (by positivity)
  have e : (2 * L * Φ) * (16 * Φ / μ) = 32 * sk ^ 2 * Φ ^ 2 := by
    rw [hsk2]; field_simp; ring
  have hip2 : ⟪G, d⟫ ^ 2 ≤ (6 * sk * Φ) ^ 2 := by nlinarith [sq_nonneg (sk * Φ)]
  have h0 : 0 ≤ 6 * sk * Φ := by positivity
  nlinarith [sq_nonneg (⟪G, d⟫ + 6 * sk * Φ)]

lemma sq_div_le {η Φ Φ0 δ : ℝ} (hΦ : 0 ≤ Φ) (hΦ0 : 0 < Φ0)
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ L * η * Φ) (hA : Φ ≤ Φ0) :
    δ ^ 2 / (Φ0 / 4) ≤ 4 * η ^ 2 * L ^ 2 * Φ := by
  have hδ2 : δ ^ 2 ≤ (L * η * Φ) ^ 2 := by gcongr
  rw [div_le_iff₀ (by positivity)]
  have : 0 ≤ η ^ 2 * L ^ 2 * Φ := by positivity
  nlinarith

lemma far_gap {η Φ Φ0 δ : ℝ} (hΦ : 0 ≤ Φ) (hΦ0 : 0 < Φ0)
    (h1 : 16 * L * η ≤ 1) (hδle : δ ≤ L * η * Φ) (hA : Φ0 < Φ) :
    Φ0 / 4 + Φ0 / 4 ≤ Φ - δ := by
  have : L * η * Φ ≤ Φ / 16 := by
    have := mul_le_mul_of_nonneg_right h1 hΦ
    nlinarith
  linarith

set_option maxHeartbeats 800000 in
lemma Hyp.step [IsProbabilityMeasure p] (H : Hyp p f g u L μ ρ σ K) {η Φ0 : ℝ} (hη : 0 < η)
    (hΦ0 : 0 < Φ0) (hΦ0ρ : 36864 * ρ ^ 2 * Φ0 ≤ μ ^ 3) (h1 : 16 * L * η ≤ 1)
    (h2 : 768 * Real.sqrt (L / μ) * K * L * σ ^ 2 * η ≤ μ * Φ0)
    (h3 : 196 * Real.sqrt (L / μ) * L ^ 2 * η ^ 2 ≤ 1) (x : E) :
    Integrable (fun ω => pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (x - η • g x ω)) p ∧
      ∫ ω, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (x - η • g x ω) ∂p ≤
        (1 - μ * η / 32) * pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x - η / 2 * (f x - f u) +
          2 * η ^ 2 * σ ^ 2 := by
  set sk := Real.sqrt (L / μ) with hskdef
  set lam := 32 * sk / μ with hlamdef
  have hL := H.L_pos
  have hμ := H.μ_pos
  have hsk : 1 ≤ sk := by
    rw [hskdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hμ]; linarith [H.μ_le])
  have hlam0 : 0 ≤ lam := by positivity
  have hc := H.continuous
  set G := gradient f x
  set Φ := f x - f u
  have hΦ : 0 ≤ Φ := sub_nonneg.mpr (H.min (mem_univ x))
  obtain ⟨p0, hp0f, hpd⟩ := nearest (u := u) hc x
  set d := x - p0
  have hmin0 : IsMinOn f univ p0 := fun z _ => by
    show f p0 ≤ f z; rw [hp0f]; exact H.min (mem_univ z)
  have hgp0 : gradient f p0 = 0 := grad_zero_of_min hL H.grad H.lip hmin0
  have hDd : distSq f u x = ‖d‖ ^ 2 := by unfold distSq; rw [hpd]
  have hD : μ * ‖d‖ ^ 2 ≤ 16 * Φ := by
    obtain ⟨p', hp', hq⟩ := quad_growth hL hμ H.μ_le H.grad H.lip H.min H.pl x
    have hle : ‖d‖ ≤ ‖x - p'‖ := by
      rw [← hpd]
      have := infDist_le_dist_of_mem (x := x) (show p' ∈ minSet f u from
        le_antisymm (hp' (mem_univ u)) (H.min (mem_univ p')))
      rwa [dist_eq_norm] at this
    have : ‖d‖ ^ 2 ≤ ‖x - p'‖ ^ 2 := by gcongr
    nlinarith
  have hG2 : ‖G‖ ^ 2 ≤ 2 * L * Φ := grad_sq_le hL H.grad H.lip H.min x
  have hG2' : 2 * μ * Φ ≤ ‖G‖ ^ 2 := H.pl x
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set ζ : Ω → E := fun ω => g x ω - G with hζdef
  have iζ : Integrable ζ p := (H.int x).sub (integrable_const _)
  have hζ0 : ∫ ω, ζ ω ∂p = 0 := by
    simp only [ζ]; rw [integral_sub (H.int x) (integrable_const _), H.mean]; simp [G]
  have iζ2 : Integrable (fun ω => ‖ζ ω‖ ^ 2) p := H.var_int x
  have iζ4 : Integrable (fun ω => ‖ζ ω‖ ^ 4) p := H.kurt_int x
  have hζ2 : ∫ ω, ‖ζ ω‖ ^ 2 ∂p ≤ σ ^ 2 := H.var x
  have hζ4 : ∫ ω, ‖ζ ω‖ ^ 4 ∂p ≤ K * σ ^ 4 := H.kurt x
  have iin : ∀ v : E, Integrable (fun ω => ⟪v, ζ ω⟫) p := fun v => iζ.const_inner v
  have hin0 : ∀ v : E, ∫ ω, ⟪v, ζ ω⟫ ∂p = 0 := by
    intro v; rw [integral_inner iζ v, hζ0, inner_zero_right]
  have hgζ : ∀ ω, g x ω = G + ζ ω := fun ω => by simp [ζ]
  set δ := η / 2 * ‖G‖ ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  set N : Ω → ℝ := fun ω => -(η * ⟪G, ζ ω⟫) + L * η ^ 2 * ‖ζ ω‖ ^ 2 with hNdef
  have hNe : N = fun ω => L * η ^ 2 * ‖ζ ω‖ ^ 2 - η * ⟪G, ζ ω⟫ := by
    funext ω; simp only [N]; ring
  have iN : Integrable N p := by
    rw [hNe]; exact (iζ2.const_mul _).sub ((iin G).const_mul η)
  have hNint : ∫ ω, N ω ∂p = L * η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p := by
    rw [hNe, integral_sub (iζ2.const_mul _) ((iin G).const_mul η), integral_const_mul,
      integral_const_mul, hin0]
    ring
  have hN2 : ∀ ω, N ω ^ 2 ≤ 2 * η ^ 2 * ‖G‖ ^ 2 * ‖ζ ω‖ ^ 2 + 2 * L ^ 2 * η ^ 4 * ‖ζ ω‖ ^ 4 := by
    intro ω
    have hcs : ⟪G, ζ ω⟫ ^ 2 ≤ ‖G‖ ^ 2 * ‖ζ ω‖ ^ 2 := by
      have := abs_real_inner_le_norm G (ζ ω)
      have h0 : 0 ≤ ‖G‖ * ‖ζ ω‖ := by positivity
      rw [← mul_pow]
      exact sq_le_sq' (by linarith [neg_abs_le ⟪G, ζ ω⟫]) (le_trans (le_abs_self _) this)
    simp only [N]
    nlinarith [sq_nonneg (η * ⟪G, ζ ω⟫ + L * η ^ 2 * ‖ζ ω‖ ^ 2)]
  have iNb : Integrable
      (fun ω => 2 * η ^ 2 * ‖G‖ ^ 2 * ‖ζ ω‖ ^ 2 + 2 * L ^ 2 * η ^ 4 * ‖ζ ω‖ ^ 4) p :=
    (iζ2.const_mul _).add (iζ4.const_mul _)
  have iN2 : Integrable (fun ω => N ω ^ 2) p := by
    refine Integrable.mono' iNb (iN.aestronglyMeasurable.pow 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hN2 ω
  have hN2int : ∫ ω, N ω ^ 2 ∂p ≤
      2 * η ^ 2 * ‖G‖ ^ 2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4) := by
    calc ∫ ω, N ω ^ 2 ∂p
        ≤ ∫ ω, (2 * η ^ 2 * ‖G‖ ^ 2 * ‖ζ ω‖ ^ 2 + 2 * L ^ 2 * η ^ 4 * ‖ζ ω‖ ^ 4) ∂p :=
          integral_mono iN2 iNb hN2
      _ = 2 * η ^ 2 * ‖G‖ ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p + 2 * L ^ 2 * η ^ 4 * ∫ ω, ‖ζ ω‖ ^ 4 ∂p := by
          rw [integral_add (iζ2.const_mul _) (iζ4.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * η ^ 2 * ‖G‖ ^ 2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4) := by
          gcongr
  set b := Φ0 / 4 with hbdef
  have hb : 0 < b := by positivity
  set c' := dhub b b (Φ - δ) with hc'def
  have hc'0 : 0 ≤ c' := dhub_nonneg hb _
  have hLη : L * η ≤ 1 / 2 := by linarith
  have hfstep : ∀ ω, f (x - η • g x ω) - f u ≤ Φ - δ + N ω := by
    intro ω
    have h := HeavyTailedPL.noisy_step H.grad H.lip hL.le hη.le hLη x (g x ω)
    have e : g x ω - gradient f x = ζ ω := rfl
    rw [e] at h
    simp only [N, Φ, δ, G]
    linarith
  have hhub : ∀ ω, hub b b (f (x - η • g x ω) - f u) ≤
      hub b b (Φ - δ) + c' * N ω + N ω ^ 2 / (2 * b) := by
    intro ω
    have h1' := hub_mono (a := b) hb (hfstep ω)
    have h2' := hub_taylor (a := b) hb (Φ - δ) (Φ - δ + N ω)
    have e : Φ - δ + N ω - (Φ - δ) = N ω := by ring
    rw [e] at h2'
    linarith
  have hdist : ∀ ω, distSq f u (x - η • g x ω) ≤
      ‖d - η • G‖ ^ 2 - 2 * η * ⟪d - η • G, ζ ω⟫ + η ^ 2 * ‖ζ ω‖ ^ 2 := by
    intro ω
    have h := distSq_le (u := u) (x - η • g x ω) p0 hp0f
    have e : x - η • g x ω - p0 = (d - η • G) - η • ζ ω := by
      rw [hgζ ω, smul_add]; simp only [d]; abel
    rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    linarith
  set B : Ω → ℝ := fun ω => (‖d - η • G‖ ^ 2 - 2 * η * ⟪d - η • G, ζ ω⟫ + η ^ 2 * ‖ζ ω‖ ^ 2) +
    lam * (hub b b (Φ - δ) + c' * N ω + N ω ^ 2 / (2 * b)) with hBdef
  have iB1 : Integrable
      (fun ω => ‖d - η • G‖ ^ 2 - 2 * η * ⟪d - η • G, ζ ω⟫ + η ^ 2 * ‖ζ ω‖ ^ 2) p :=
    ((integrable_const _).sub ((iin _).const_mul _)).add (iζ2.const_mul _)
  have iB2 : Integrable (fun ω => hub b b (Φ - δ) + c' * N ω + N ω ^ 2 / (2 * b)) p :=
    ((integrable_const _).add (iN.const_mul _)).add (iN2.div_const _)
  have iB : Integrable B p := iB1.add (iB2.const_mul lam)
  have hpotB : ∀ ω, pot f u lam Φ0 (x - η • g x ω) ≤ B ω := by
    intro ω
    unfold pot
    have := mul_le_mul_of_nonneg_left (hhub ω) hlam0
    simp only [B, hbdef]
    linarith [hdist ω]
  have hmeas : Measurable fun ω => x - η • g x ω :=
    measurable_const.sub ((H.meas.comp (measurable_const.prodMk measurable_id)).const_smul η)
  have hpm : AEStronglyMeasurable (fun ω => pot f u lam Φ0 (x - η • g x ω)) p :=
    ((H.pot_continuous hΦ0).measurable.comp hmeas).aestronglyMeasurable
  have ipot : Integrable (fun ω => pot f u lam Φ0 (x - η • g x ω)) p := by
    refine Integrable.mono' iB hpm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pot_nonneg hlam0 hΦ0 _)]
    exact hpotB ω
  refine ⟨ipot, ?_⟩
  have hBint : ∫ ω, B ω ∂p ≤ (‖d‖ ^ 2 - 2 * η * ⟪G, d⟫ + η ^ 2 * ‖G‖ ^ 2 + η ^ 2 * σ ^ 2) +
      lam * (hub b b (Φ - δ) + c' * (L * η ^ 2 * σ ^ 2) +
        (2 * η ^ 2 * ‖G‖ ^ 2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4))) := by
    have I1 : ∫ ω, (‖d - η • G‖ ^ 2 - 2 * η * ⟪d - η • G, ζ ω⟫ + η ^ 2 * ‖ζ ω‖ ^ 2) ∂p =
        ‖d - η • G‖ ^ 2 + η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p := by
      have ha : Integrable (fun ω => ‖d - η • G‖ ^ 2 - 2 * η * ⟪d - η • G, ζ ω⟫) p :=
        (integrable_const _).sub ((iin _).const_mul _)
      rw [integral_add ha (iζ2.const_mul _),
        integral_sub (integrable_const _) ((iin _).const_mul _),
        integral_const_mul, integral_const_mul, hin0, integral_const]
      simp
    have I2 : ∫ ω, (hub b b (Φ - δ) + c' * N ω + N ω ^ 2 / (2 * b)) ∂p =
        hub b b (Φ - δ) + c' * (L * η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p) + (∫ ω, N ω ^ 2 ∂p) / (2 * b) := by
      have ha : Integrable (fun ω => hub b b (Φ - δ) + c' * N ω) p :=
        (integrable_const _).add (iN.const_mul _)
      rw [integral_add ha (iN2.div_const _), integral_add (integrable_const _) (iN.const_mul _),
        integral_const_mul, integral_div, hNint, integral_const]
      simp
    have IB : ∫ ω, B ω ∂p = (‖d - η • G‖ ^ 2 + η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p) +
        lam * (hub b b (Φ - δ) + c' * (L * η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p) +
          (∫ ω, N ω ^ 2 ∂p) / (2 * b)) := by
      rw [← I1, ← I2, ← integral_const_mul, ← integral_add iB1 (iB2.const_mul lam)]
    rw [IB]
    have hdG : ‖d - η • G‖ ^ 2 = ‖d‖ ^ 2 - 2 * η * ⟪G, d⟫ + η ^ 2 * ‖G‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_comm]; ring
    rw [hdG]
    have e1 : c' * (L * η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p) ≤ c' * (L * η ^ 2 * σ ^ 2) := by
      gcongr
    have e2 : (∫ ω, N ω ^ 2 ∂p) / (2 * b) ≤
        (2 * η ^ 2 * ‖G‖ ^ 2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4)) := by
      rw [hbdef]; gcongr
    have e3 : η ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p ≤ η ^ 2 * σ ^ 2 := by gcongr
    have := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl (hub b b (Φ - δ))) e1) e2) hlam0
    linarith
  have hpot_le := integral_mono ipot iB hpotB
  have hb0nn := hub_nonneg (a := b) hb Φ
  have hconv : hub b b (Φ - δ) + c' * (η / 2 * ‖G‖ ^ 2) ≤ hub b b Φ := by
    have h := hub_tangent (a := b) hb (Φ - δ) Φ
    have e : Φ - (Φ - δ) = η / 2 * ‖G‖ ^ 2 := by simp only [δ]; ring
    rw [e] at h; exact h
  have hcle : c' ≤ Φ / (Φ0 / 4) :=
    (dhub_mono hb (by linarith : Φ - δ ≤ Φ)).trans (dhub_le_div hb hb hΦ)
  have hδle : δ ≤ L * η * Φ := by
    have : η / 2 * ‖G‖ ^ 2 ≤ η / 2 * (2 * L * Φ) := mul_le_mul_of_nonneg_left hG2 (by positivity)
    simp only [δ]; linarith
  have key : ∃ r, hub b b Φ ≤ c' * Φ + r ∧ ((Φ ≤ ⟪G, d⟫ ∧ r ≤ 4 * η ^ 2 * L ^ 2 * Φ) ∨
      (-(6 * sk * Φ) ≤ ⟪G, d⟫ ∧ c' = 1 ∧ r = 0)) := by
    by_cases hA : Φ ≤ Φ0
    · refine ⟨δ ^ 2 / b, hub_decrease hb.le hb hδ0, Or.inl ⟨?_, ?_⟩⟩
      · exact H.aim_region hΦ0ρ hp0f hgp0 hD hA
      · exact sq_div_le hΦ hΦ0 hδ0 hδle hA
    · have hfar : b + b ≤ Φ - δ := far_gap hΦ hΦ0 h1 hδle (not_le.mp hA)
      obtain ⟨hc1, hF⟩ := hub_decrease_far hb.le hb hδ0 hfar
      exact ⟨0, hF, Or.inr ⟨far_inner hμ hL hΦ hG2 hD, hc1, rfl⟩⟩
  obtain ⟨r, hF2, hcase⟩ := key
  have hD' : μ * ‖d‖ ^ 2 ≤ 16 * Φ := hD
  have hfin := step_alg hη hμ hL H.K_ge hΦ hΦ0 hsk hlamdef hD' h1 h2 h3 hG2 hG2' hc'0 hcle
    hb0nn hconv hF2 hcase
  have hpotx : pot f u lam Φ0 x = ‖d‖ ^ 2 + lam * hub b b Φ := by
    unfold pot; rw [hDd]
  rw [hpotx]
  linarith

end OracleTemplate.PLHessian
