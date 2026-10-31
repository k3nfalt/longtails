import LongTails.Proofs.SpsaProcess
import LongTails.Proofs.SpsaTuning
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.HeavyTailedTwoPointZerothOrder

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace LongTails.Proofs.SpsaConvergence

open OracleTemplate OracleTemplate.ClippedSpsa LongTails.Proofs.SpsaStep LongTails.Proofs.SpsaProcess
  LongTails.Proofs.SpsaTuning LongTails.Proofs.SpsaMoments

section Average

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
  {F : Point d → Ω → ℝ} {G : Point d → Ω → Point d} {L σ p μ0 c η lower : ℝ} {f : Point d → ℝ}
  {x0 : Point d}

lemma measurable_out (hF : Measurable (Function.uncurry F)) (T : ℕ) :
    Measurable (fun ω : ((ℕ → Sign d) × Fin (T + 1)) × (ℕ → Ω) =>
      traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val) := by
  have h2 : Measurable (fun r : Fin (T + 1) × ((ℕ → Sign d) × (ℕ → Ω)) =>
      traj F μ0 η c x0 r.2.1 r.2.2 r.1.val) :=
    measurable_from_prod_countable_right fun τ => (measurable_traj hF τ.val)
  exact h2.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))

lemma lintegral_out {T : ℕ} (g : Point d → ℝ≥0∞) (hg : Measurable g)
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ ω, g (traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val)
        ∂(((Measure.infinitePi fun _ : ℕ => signLaw d).prod
          (PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod
          (Measure.infinitePi fun _ : ℕ => ν)) =
      ∑ τ : Fin (T + 1), (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ *
        ∫⁻ w, g (traj F μ0 η c x0 w.1 w.2 τ.val)
          ∂((Measure.infinitePi fun _ : ℕ => signLaw d).prod (Measure.infinitePi fun _ : ℕ => ν)) := by
  set PA := Measure.infinitePi fun _ : ℕ => signLaw d
  set PB := Measure.infinitePi fun _ : ℕ => ν
  set Uτ := (PMF.uniformOfFintype (Fin (T + 1))).toMeasure
  have hm : Measurable (fun ω : ((ℕ → Sign d) × Fin (T + 1)) × (ℕ → Ω) =>
      g (traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val)) := hg.comp (measurable_out hF T)
  have hτ : ∀ τ : Fin (T + 1), Measurable (fun w : (ℕ → Sign d) × (ℕ → Ω) =>
      g (traj F μ0 η c x0 w.1 w.2 τ.val)) := fun τ => hg.comp (measurable_traj hF τ.val)
  rw [lintegral_prod _ hm.aemeasurable]
  dsimp only
  have hin : Measurable (fun x : (ℕ → Sign d) × Fin (T + 1) =>
      ∫⁻ Ξ, g (traj F μ0 η c x0 x.1 Ξ x.2.val) ∂PB) := hm.lintegral_prod_right'
  rw [lintegral_prod _ hin.aemeasurable]
  dsimp only
  have hU : ∀ τ : Fin (T + 1), Uτ {τ} = (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    intro τ
    simp only [Uτ]
    rw [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
    simp
  simp_rw [lintegral_fintype, hU]
  rw [lintegral_finsetSum _ (fun τ _ => ((hτ τ).lintegral_prod_right').mul_const _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [lintegral_mul_const _ ((hτ τ).lintegral_prod_right'), lintegral_prod _ (hτ τ).aemeasurable,
    mul_comm]

end Average


lemma norm_le_phi {ε c t : ℝ} (hε : 0 < ε) (hc0 : 0 < c) (ht0 : 0 ≤ t) :
    t ≤ (2 / ε + 128 / c) * phiFun c t + ε / 4 := by
  unfold phiFun
  rcases min_choice (t ^ 2 / 2) (c * t / 128) with h | h <;> rw [h]
  · have h1 : t ≤ t ^ 2 / ε + ε / 4 := by
      rw [div_add_div _ _ hε.ne' (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (t - ε / 2)]
    have h2 : 0 ≤ 128 / c * (t ^ 2 / 2) := by positivity
    have e : 2 / ε * (t ^ 2 / 2) = t ^ 2 / ε := by field_simp
    have e2 : (2 / ε + 128 / c) * (t ^ 2 / 2) = 2 / ε * (t ^ 2 / 2) + 128 / c * (t ^ 2 / 2) := by
      ring
    linarith
  · have e : 128 / c * (c * t / 128) = t := by field_simp
    have h2 : 0 ≤ 2 / ε * (c * t / 128) := by positivity
    have e2 : (2 / ε + 128 / c) * (c * t / 128) = 2 / ε * (c * t / 128) + 128 / c * (c * t / 128) := by
      ring
    linarith

lemma final_bound {ε c Iφ Ig : ℝ} (hε : 0 < ε) (hcε : 64 * ε ≤ c) (hφ : Iφ ≤ ε ^ 2 / 8)
    (hIg : Ig ≤ (2 / ε + 128 / c) * Iφ + ε / 4) : Ig ≤ ε := by
  have hc0 : 0 < c := by linarith
  have hcoef : 0 ≤ 2 / ε + 128 / c := by positivity
  have h1 := mul_le_mul_of_nonneg_left hφ hcoef
  have e : (2 / ε + 128 / c) * (ε ^ 2 / 8) = ε / 4 + 16 * ε ^ 2 / c := by field_simp; ring
  have h3 : 16 * ε ^ 2 / c ≤ ε / 4 := by
    rw [div_le_iff₀ hc0]; nlinarith
  linarith

lemma avg_bound {η ε B W L Δ D K : ℝ} {d T : ℕ} {I : ℕ → ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hBle : B ≤ ε / 14) (hV : 4 * L * η * d * W ≤ ε ^ 2 / 24)
    (hhor : 96 * Δ / (η * ε ^ 2) ≤ (T : ℝ) + 1) (hD : D ≤ Δ)
    (hK : K = 2 * η * B ^ 2 + L * η ^ 2 * d * W)
    (hwin : η / 4 * ∑ i ∈ Finset.range (T + 1), I i ≤ D + ((T : ℝ) + 1) * K) :
    (∑ i ∈ Finset.range (T + 1), I i) / ((T : ℝ) + 1) ≤ ε ^ 2 / 8 := by
  have hN : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hε2 : 0 < ε ^ 2 := by positivity
  have h1 : 96 * Δ ≤ ((T : ℝ) + 1) * (η * ε ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at hhor; linarith
  set Ssum := ∑ i ∈ Finset.range (T + 1), I i
  have hsum : Ssum ≤ 4 / η * (D + ((T : ℝ) + 1) * K) := by
    have h4 : 0 ≤ 4 / η := by positivity
    calc Ssum = 4 / η * (η / 4 * Ssum) := by field_simp
      _ ≤ 4 / η * (D + ((T : ℝ) + 1) * K) := mul_le_mul_of_nonneg_left hwin h4
  rw [div_le_iff₀ hN]
  have e : 4 / η * (D + ((T : ℝ) + 1) * K) =
      4 * D / η + ((T : ℝ) + 1) * (8 * B ^ 2 + 4 * L * η * d * W) := by
    rw [hK]; field_simp; ring
  have hb2 : 8 * B ^ 2 ≤ ε ^ 2 / 24 := by
    have := mul_le_mul hBle hBle hB0 (by positivity)
    nlinarith
  have hdiv : 4 * D / η ≤ ε ^ 2 / 24 * ((T : ℝ) + 1) := by
    rw [div_le_iff₀ hη]; nlinarith
  have hNnn : (0 : ℝ) ≤ (T : ℝ) + 1 := hN.le
  have h5 := mul_le_mul_of_nonneg_left hb2 hNnn
  have h6 := mul_le_mul_of_nonneg_left hV hNnn
  nlinarith

section Core

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
  {F : Point d → Ω → ℝ} {G : Point d → Ω → Point d} {L σ p μ0 c η lower Δ ε : ℝ}
  {f : Point d → ℝ} {x0 : Point d}

theorem RunHyp.core (H : RunHyp ν F G f L σ p μ0 c η lower) {T : ℕ} (hη : 0 < η) (hε : 0 < ε)
    (hcε : 64 * ε ≤ c) (hBle : biasLevel L σ p μ0 c d ≤ ε / 14)
    (hV : 4 * L * η * d * (c ^ (2 - p) * (2 * (σ + L * μ0 * d / 2)) ^ p) ≤ ε ^ 2 / 24)
    (hhor : 96 * Δ / (η * ε ^ 2) ≤ (T : ℝ) + 1) (hgap : f x0 - lower ≤ Δ) :
    Measurable (fun ω : ((ℕ → Sign d) × Fin (T + 1)) × (ℕ → Ω) =>
        traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val) ∧
      Integrable (fun ω : ((ℕ → Sign d) × Fin (T + 1)) × (ℕ → Ω) =>
        ‖gradient f (traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val)‖)
        (((Measure.infinitePi fun _ : ℕ => signLaw d).prod
          (PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod (Measure.infinitePi fun _ : ℕ => ν)) ∧
      ∫ ω, ‖gradient f (traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val)‖
        ∂(((Measure.infinitePi fun _ : ℕ => signLaw d).prod
          (PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod (Measure.infinitePi fun _ : ℕ => ν)) ≤ ε := by
  set μT := ((Measure.infinitePi fun _ : ℕ => signLaw d).prod
    (PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod (Measure.infinitePi fun _ : ℕ => ν)
    with hμTdef
  have : IsProbabilityMeasure μT := by rw [hμTdef]; infer_instance
  set out : ((ℕ → Sign d) × Fin (T + 1)) × (ℕ → Ω) → Point d :=
    fun ω => traj F μ0 η c x0 ω.1.1 ω.2 ω.1.2.val with houtdef
  have hmo : Measurable out := measurable_out H.sample.measF T
  refine ⟨hmo, ?_⟩
  have hc := H.c_nonneg
  have hc0 : 0 < c := by linarith
  have hgr : Measurable (gradient f) := H.measurable_gradient
  have hnm : Measurable (fun ω => ‖gradient f (out ω)‖) := (hgr.comp hmo).norm
  set R := (T : ℝ) * (|η| * c * Real.sqrt d)
  have hR : ∀ ω, ‖out ω - x0‖ ≤ R := by
    intro ω
    refine (traj_dist hc ω.1.1 ω.2 ω.1.2.val).trans ?_
    have : (ω.1.2.val : ℝ) ≤ T := by exact_mod_cast Nat.lt_succ_iff.mp ω.1.2.isLt
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hbd : ∀ ω, ‖gradient f (out ω)‖ ≤ ‖gradient f x0‖ + L * R :=
    fun ω => H.grad_bound (hR ω)
  have hint : Integrable (fun ω => ‖gradient f (out ω)‖) μT :=
    Integrable.of_bound hnm.aestronglyMeasurable (‖gradient f x0‖ + L * R)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_norm]; exact hbd ω)
  refine ⟨hint, ?_⟩
  have hNpos : (0 : ℝ) < (T + 1) := by positivity
  have hφm : Measurable (fun y : Point d => phiFun c ‖gradient f y‖) := by
    unfold phiFun
    exact ((hgr.norm.pow_const 2).div_const _).min ((hgr.norm.const_mul c).div_const _)
  have hφi : ∀ τ : ℕ, Integrable (fun w : (ℕ → Sign d) × (ℕ → Ω) =>
      phiFun c ‖gradient f (traj F μ0 η c x0 w.1 w.2 τ)‖) (pathLaw d ν) :=
    fun τ => (H.run_step (x0 := x0) τ).2.1
  have hwin := H.window_sum (x0 := x0) (T + 1)
  push_cast at hwin
  have hlast : 0 ≤ ∫ w, (f (traj F μ0 η c x0 w.1 w.2 (T + 1)) - lower) ∂(pathLaw d ν) :=
    integral_nonneg fun w => sub_nonneg.mpr (H.lower_le _)
  set I : ℕ → ℝ := fun i =>
    ∫ w, phiFun c ‖gradient f (traj F μ0 η c x0 w.1 w.2 i)‖ ∂(pathLaw d ν) with hIdef
  have hI0 : ∀ i, 0 ≤ I i := fun i => integral_nonneg fun w => phiFun_nonneg hc (norm_nonneg _)
  have hwin' : η / 4 * ∑ i ∈ Finset.range (T + 1), I i ≤
      (f x0 - lower) + (T + 1) * driftConst L σ p μ0 c η d := by
    rw [Finset.mul_sum]; linarith
  set B := biasLevel L σ p μ0 c d
  set W := c ^ (2 - p) * (2 * (σ + L * μ0 * d / 2)) ^ p
  have hB0 : 0 ≤ B := by
    have := H.hσ; have := H.hL; have := H.hμ0
    simp only [B, biasLevel]; positivity
  have hK : driftConst L σ p μ0 c η d = 2 * η * B ^ 2 + L * η ^ 2 * d * W := rfl
  have havg : (∑ i ∈ Finset.range (T + 1), I i) / (T + 1) ≤ ε ^ 2 / 8 :=
    avg_bound hη hε hB0 hBle hV hhor hgap hK hwin'
  have hpt : ∀ y : Point d, ‖gradient f y‖ ≤
      (2 / ε + 128 / c) * phiFun c ‖gradient f y‖ + ε / 4 :=
    fun y => norm_le_phi hε hc0 (norm_nonneg _)
  have hφout : Measurable (fun ω => phiFun c ‖gradient f (out ω)‖) := hφm.comp hmo
  have hφint : Integrable (fun ω => phiFun c ‖gradient f (out ω)‖) μT := by
    refine Integrable.of_bound hφout.aestronglyMeasurable ((‖gradient f x0‖ + L * R) ^ 2 / 2)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (phiFun_nonneg hc (norm_nonneg _))]
    refine phiFun_le_sq.trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) (hbd ω) 2
    linarith
  have hlin := lintegral_out (ν := ν) (F := F) (μ0 := μ0) (η := η) (c := c) (x0 := x0) (T := T)
    (fun y => ENNReal.ofReal (phiFun c ‖gradient f y‖)) (ENNReal.measurable_ofReal.comp hφm)
    H.sample.measF
  have hφle : ∫ ω, phiFun c ‖gradient f (out ω)‖ ∂μT ≤ ε ^ 2 / 8 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      phiFun_nonneg hc (norm_nonneg _)) hφout.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hl : ∫⁻ ω, ENNReal.ofReal (phiFun c ‖gradient f (out ω)‖) ∂μT =
        ∑ τ : Fin (T + 1), (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ * ENNReal.ofReal (I τ.val) := by
      rw [hlin]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hφi τ.val)
        (Filter.Eventually.of_forall fun w => phiFun_nonneg hc (norm_nonneg _))]
    rw [hl, ← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun τ _ => hI0 _),
      Fin.sum_univ_eq_sum_range (fun i => I i)]
    have hinv : (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((T + 1) : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hNpos, ENNReal.ofReal_one, one_div]
      congr 1
      rw [show ((T : ℝ) + 1) = ((T + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    rw [hinv, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [one_div_mul_eq_div]
    exact havg
  have hrhs : Integrable (fun ω => (2 / ε + 128 / c) * phiFun c ‖gradient f (out ω)‖ + ε / 4) μT :=
    (hφint.const_mul _).add (integrable_const _)
  have hmono := integral_mono hint hrhs (fun ω => hpt (out ω))
  rw [integral_add (hφint.const_mul _) (integrable_const _), integral_const_mul,
    integral_const] at hmono
  simp only [probReal_univ, one_smul] at hmono
  exact final_bound hε hcε hφle hmono

end Core

open LongTails.Setups.HeavyTailedTwoPointZerothOrder in
theorem convergence : Convergence LongTails.Setups.HeavyTailedTwoPointZerothOrder.spec
    (fun q _ => ⌈2 ^ 20 * 132 ^ (q.p / (q.p - 1)) * q.L * q.d * q.Δ / q.ε ^ 2 *
      (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1)))⌉₊ + 1) := by
  refine ⟨fun q => method (smoothing q.L q.ε q.d) (stepSize q.L q.σ q.p q.ε q.d)
    (clipLevel q.σ q.p q.ε) (horizon q.L q.Δ q.σ q.p q.ε q.d) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hd, hL, hΔ, hσ, hp1, hp2, hε⟩ := hq
  obtain ⟨F, G, ν, P, hIID, rfl, hgrad, ⟨lower, hlow, hgap⟩, hFm, hGm, hFG, hlip, hGi, hmean,
    hmi, hm⟩ := hadm
  have HS : SampleHyp (ν : Measure q.Ω) F G q.L q.σ q.p :=
    ⟨hFm, hGm, hFG, hlip, hGi, fun x => by rw [hmean x]; exact hmi x,
      fun x => by rw [hmean x]; exact hm x⟩
  have H : RunHyp (ν : Measure q.Ω) F G f q.L q.σ q.p (smoothing q.L q.ε q.d)
      (clipLevel q.σ q.p q.ε) (stepSize q.L q.σ q.p q.ε q.d) lower :=
    ⟨HS, hgrad, hmean, hlow, hd, hp1, hp2, hσ, hL, smoothing_pos hd hL hε,
      by rw [S_eq hd hL hε]; exact clip_ge_S hε hσ, bias_mul_le hd hL hε hσ hp1,
      (step_pos hd hL hε hσ).le, step_le hd hL⟩
  have hcore := LongTails.Proofs.SpsaConvergence.RunHyp.core H (x0 := q.x0) (T := horizon q.L q.Δ q.σ q.p q.ε q.d) (Δ := q.Δ)
    (step_pos hd hL hε hσ) hε (clip_ge_eps hε hσ) (bias_le hd hL hε hσ hp1)
    (by rw [S_eq hd hL hε]; exact step_var hd hL hε hσ)
    (horizon_suffices hd hL hσ hp1 hp2 hε hΔ) hgap
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (ν : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  change Measurable (fun seed : ((ℕ → Sign q.d) × Fin (horizon q.L q.Δ q.σ q.p q.ε q.d + 1)) ×
      (ℕ → q.Ω) => execute (spsaOracle F P)
        (method (smoothing q.L q.ε q.d) (stepSize q.L q.σ q.p q.ε q.d) (clipLevel q.σ q.p q.ε)
          (horizon q.L q.Δ q.σ q.p q.ε q.d) q.x0)
        (fun _ => horizon q.L q.Δ q.σ q.p q.ε q.d + 1) seed.1 seed.2) ∧
    Integrable (fun seed : ((ℕ → Sign q.d) × Fin (horizon q.L q.Δ q.σ q.p q.ε q.d + 1)) ×
      (ℕ → q.Ω) => ‖gradient f (execute (spsaOracle F P)
        (method (smoothing q.L q.ε q.d) (stepSize q.L q.σ q.p q.ε q.d) (clipLevel q.σ q.p q.ε)
          (horizon q.L q.Δ q.σ q.p q.ε q.d) q.x0)
        (fun _ => horizon q.L q.Δ q.σ q.p q.ε q.d + 1) seed.1 seed.2)‖)
      (((Measure.infinitePi fun _ : ℕ => signLaw q.d).prod
        (PMF.uniformOfFintype (Fin (horizon q.L q.Δ q.σ q.p q.ε q.d + 1))).toMeasure).prod
        (P : Measure (ℕ → q.Ω))) ∧
    ∫ seed, ‖gradient f (execute (spsaOracle F P)
        (method (smoothing q.L q.ε q.d) (stepSize q.L q.σ q.p q.ε q.d) (clipLevel q.σ q.p q.ε)
          (horizon q.L q.Δ q.σ q.p q.ε q.d) q.x0)
        (fun _ => horizon q.L q.Δ q.σ q.p q.ε q.d + 1) seed.1 seed.2)‖
      ∂(((Measure.infinitePi fun _ : ℕ => signLaw q.d).prod
        (PMF.uniformOfFintype (Fin (horizon q.L q.Δ q.σ q.p q.ε q.d + 1))).toMeasure).prod
        (P : Measure (ℕ → q.Ω))) ≤ q.ε
  simp_rw [execute_spsa F P _ _ _ _ q.x0 _ (Nat.le_add_right _ 1)]
  rw [hP]
  exact hcore

end LongTails.Proofs.SpsaConvergence
