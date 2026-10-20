import LongTails.Proofs.RiverValleyProcess

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

structure Orc (K : Submodule ℝ E) [K.HasOrthogonalProjection] (p : Measure Ω) (g : E → Ω → E)
    (F : E → E) (σu σv : ℝ) : Prop where
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = F x
  intQ : ∀ x, Integrable (fun ω => ‖Kᗮ.starProjection (g x ω - F x)‖ ^ 2) p
  intP : ∀ x, Integrable (fun ω => ‖K.starProjection (g x ω - F x)‖ ^ 2) p
  varQ : ∀ x, ∫ ω, ‖Kᗮ.starProjection (g x ω - F x)‖ ^ 2 ∂p ≤ σu ^ 2
  varP : ∀ x, ∫ ω, ‖K.starProjection (g x ω - F x)‖ ^ 2 ∂p ≤ σv ^ 2

lemma Orc.noise {g : E → Ω → E} {F : E → E} {σu σv : ℝ} (O : Orc K p g F σu σv) (x : E) :
    NoiseAt K p (fun ω => g x ω - F x) σu σv where
  meas := (O.meas.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  int := (O.int x).sub (integrable_const _)
  mean := by
    rw [integral_sub (O.int x) (integrable_const _), O.mean x, integral_const]
    simp
  intQ := O.intQ x
  intP := O.intP x
  varQ := O.varQ x
  varP := O.varP x

structure Regime (Lh ρh G Luv μ Lv LJ ρJ σu σv : ℝ) : Prop where
  hΓ : 16 * Luv ≤ μ
  hLh : 16 * Lh ≤ μ
  hLm : 64 * (Luv / μ * Lh + 2 * LJ * G) ≤ μ
  hc : 64 * (2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2) * σu ≤ μ * Lv
  hσu : 0 ≤ σu
  hσv : 0 ≤ σv

noncomputable def lamOf (Lh ρh G Luv μ Lv LJ ρJ σu : ℝ) : ℝ :=
  (256 * (Luv / μ * Lh + 2 * LJ * G) ^ 2 + 32 * (Luv / μ * Lh + 2 * LJ * G) * Luv) / μ +
    2 * (2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2) * σu / Lv

noncomputable def NOf (Lh ρh G Luv μ Lv LJ ρJ σu σv : ℝ) : ℝ :=
  2 * (Lh / 2 + 2 * (Luv / μ) * (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) +
      8 * lamOf Lh ρh G Luv μ Lv LJ ρJ σu * (Luv / μ) ^ 2) * σu ^ 2 +
    4 * lamOf Lh ρh G Luv μ Lv LJ ρJ σu * (σv ^ 2 + (Luv / μ) ^ 2 * σu ^ 2) +
    (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) * (σu * σv + Luv / μ * σu ^ 2) +
    Luv / μ * G * LJ * σu ^ 2 +
    (2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2) * σu ^ 3 / μ +
    (2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2) * (Luv / μ) * G * σu ^ 2 / (8 * Lv) +
    8 * lamOf Lh ρh G Luv μ Lv LJ ρJ σu * LJ ^ 2 * σu ^ 4 / (μ * Lv) +
    lamOf Lh ρh G Luv μ Lv LJ ρJ σu * LJ * (Luv / μ) * G * σu ^ 2 / (4 * Lv)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma step_eq (g : E → Ω → E) (F : E → E) (x : E) (η : ℝ) (ω : Ω) :
    x - η • (F x + (g x ω - F x)) = x - η • g x ω := by
  congr 2; abel

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

lemma pt_V {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {hstar : ℝ}
    {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (y : E) :
    Integrable (fun ω => Vfun K h gh φ Jφ (lamOf Lh ρh G Luv μ Lv LJ ρJ σu) (y - η • g y ω) -
        hstar) p ∧
      ∫ ω, (Vfun K h gh φ Jφ (lamOf Lh ρh G Luv μ Lv LJ ρJ σu) (y - η • g y ω) - hstar) ∂p ≤
        Vfun K h gh φ Jφ (lamOf Lh ρh G Luv μ Lv LJ ρJ σu) y - hstar -
          (η / 2) * ‖ar K gh (Kᗮ.starProjection y)‖ ^ 2 -
          η * lamOf Lh ρh G Luv μ Lv LJ ρJ σu * μ / 2 * ‖wv K φ y‖ ^ 2 +
          η ^ 2 * NOf Lh ρh G Luv μ Lv LJ ρJ σu σv := by
  obtain ⟨hi, hE⟩ := H.descent (O.noise y) R.hσu R.hσv y hη0 hη R.hΓ R.hLh R.hLm R.hc
  simp only [step_eq] at hi hE
  simp only [NOf, lamOf]
  refine ⟨hi.sub (integrable_const _), ?_⟩
  rw [integral_sub hi (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  linarith

lemma pt_w {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (y : E) :
    Integrable (fun ω => ‖wv K φ (y - η • g y ω)‖ ^ 2) p ∧
    ∫ ω, ‖wv K φ (y - η • g y ω)‖ ^ 2 ∂p ≤
      (1 - η * μ / 2) * ‖wv K φ y‖ ^ 2 +
        η * (8 * (Luv / μ) ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Luv / μ * (LJ * G) / μ) *
          ‖ar K gh (Kᗮ.starProjection y)‖ ^ 2 / μ +
        η ^ 2 * (4 * (σv ^ 2 + (Luv / μ) ^ 2 * σu ^ 2) + 16 * (Luv / μ) ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Luv / μ * G * LJ * σu ^ 2 / (4 * Lv)) := by
  have := H.w_step (O.noise y) y hη0 hη R.hΓ
  simpa only [step_eq] using this

lemma pt_Aw {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (y : E) :
    Integrable (fun ω => ‖A (wv K φ (y - η • g y ω))‖ ^ 2) p ∧
    ∫ ω, ‖A (wv K φ (y - η • g y ω))‖ ^ 2 ∂p ≤
      (1 - η * μ / 2) * ‖A (wv K φ y)‖ ^ 2 +
        η * (8 * (Luv / μ) ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Luv / μ * (LJ * G)) *
          ‖ar K gh (Kᗮ.starProjection y)‖ ^ 2 +
        η ^ 2 * (4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Luv / μ * μ * G * LJ * σu ^ 2 / 4) := by
  have := H.Aw_step (O.noise y) y hη0 hη R.hΓ
  simpa only [step_eq] using this

lemma pt_a {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * Lh * η ≤ 1) (y : E) :
    Integrable (fun ω => ‖ar K gh (Kᗮ.starProjection (y - η • g y ω))‖ ^ 2) p ∧
    ∫ ω, ‖ar K gh (Kᗮ.starProjection (y - η • g y ω))‖ ^ 2 ∂p ≤
      (1 + 4 * Lh * η) * ‖ar K gh (Kᗮ.starProjection y)‖ ^ 2 +
        2 * Lh * η * Luv ^ 2 * ‖wv K φ y‖ ^ 2 + η ^ 2 * ((2 * G * ρh + Lh ^ 2) * σu ^ 2) := by
  have := H.a_step (O.noise y) y hη0 hη
  simpa only [step_eq] using this

end Model


lemma int_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {F f1 f2 f3 : α → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (c1 c2 c3 d : ℝ) (hF : ∀ a, F a = c1 * f1 a + c2 * f2 a + c3 * f3 a + d) :
    ∫ a, F a ∂μ = c1 * ∫ a, f1 a ∂μ + c2 * ∫ a, f2 a ∂μ + c3 * ∫ a, f3 a ∂μ + d := by
  simp_rw [hF]
  have g1 : Integrable (fun a => c1 * f1 a) μ := h1.const_mul c1
  have g2 : Integrable (fun a => c2 * f2 a) μ := h2.const_mul c2
  have g3 : Integrable (fun a => c3 * f3 a) μ := h3.const_mul c3
  have g12 : Integrable (fun a => c1 * f1 a + c2 * f2 a) μ := g1.add g2
  have g123 : Integrable (fun a => c1 * f1 a + c2 * f2 a + c3 * f3 a) μ := g12.add g3
  rw [integral_add g123 (integrable_const d), integral_add g12 g3, integral_add g1 g2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp

local notation "Pω" p => Measure.infinitePi fun _ : ℕ => p

lemma run_step {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (ηf : ℕ → ℝ) (x0 : E)
    (n : ℕ) (F : E → ℝ) (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y) (b : E → ℝ)
    (hb : ∀ y, Integrable (fun ω => F (y - ηf n • g y ω)) p ∧
      ∫ ω, F (y - ηf n • g y ω) ∂p ≤ b y)
    (hbS : Integrable (fun ξ => b (schedSeq g ηf x0 ξ n)) (Pω p)) :
    Integrable (fun ξ => F (schedSeq g ηf x0 ξ (n + 1))) (Pω p) ∧
      ∫ ξ, F (schedSeq g ηf x0 ξ (n + 1)) ∂(Pω p) ≤ ∫ ξ, b (schedSeq g ηf x0 ξ n) ∂(Pω p) := by
  have hΦ : Measurable (Function.uncurry fun (y : E) (ω : Ω) => F (y - ηf n • g y ω)) :=
    hF.measurable.comp (measurable_fst.sub (hg.const_smul _))
  exact fresh_expect p n (fun ξ => schedSeq g ηf x0 ξ n) (measurable_schedSeq hg ηf x0 n)
    (fun ξ ξ' h => schedSeq_congr g ηf x0 n h) (fun y ω => F (y - ηf n • g y ω)) hΦ
    (fun y ω => hF0 _) b hb hbS

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma lam_ge {σu : ℝ} (hσu : 0 ≤ σu) :
    Lh * (Luv / μ) ^ 2 / 2 ≤ lamOf Lh ρh G Luv μ Lv LJ ρJ σu := by
  have hμ := H.μpos
  have hLv : 0 < Lv := lt_of_lt_of_le hμ H.μ_le
  have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; have := H.ρJ_nn; have := H.ρh_nn
  have := H.Luv_nn
  have hΓ0 : 0 ≤ Luv / μ := by positivity
  have e : 32 * (Luv / μ * Lh + 2 * LJ * G) * Luv / μ = 32 * (Luv / μ) * (Luv / μ * Lh + 2 * LJ * G) := by
    field_simp
  have h1 : 0 ≤ 256 * (Luv / μ * Lh + 2 * LJ * G) ^ 2 / μ := by positivity
  have h2 : 0 ≤ 2 * (2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2) * σu / Lv := by positivity
  have h3 : Lh * (Luv / μ) ^ 2 / 2 ≤ 32 * (Luv / μ) * (Luv / μ * Lh + 2 * LJ * G) := by
    have : 0 ≤ (Luv / μ) * (2 * LJ * G) := by positivity
    nlinarith [mul_nonneg hΓ0 (mul_nonneg hΓ0 H.Lh_nn)]
  simp only [lamOf]
  rw [add_div, e]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma ar_cont : Continuous (ar K gh) :=
  Kᗮ.starProjection.continuous.comp
    (continuous_iff_continuousAt.mpr fun z => (H.hHh z).continuousAt)

lemma run_int {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {hstar : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y)
    (ηf : ℕ → ℝ) (hηf : ∀ n, 0 ≤ ηf n ∧ 8 * ηf n * Lv ≤ 1) (x0 : E) :
    ∀ n, Integrable (fun ξ => Vfun K h gh φ Jφ (lamOf Lh ρh G Luv μ Lv LJ ρJ σu)
        (schedSeq g ηf x0 ξ n) - hstar) (Pω p) ∧
      Integrable (fun ξ => ‖wv K φ (schedSeq g ηf x0 ξ n)‖ ^ 2) (Pω p) ∧
      Integrable (fun ξ => ‖A (wv K φ (schedSeq g ηf x0 ξ n))‖ ^ 2) (Pω p) ∧
      Integrable (fun ξ => ‖ar K gh (Kᗮ.starProjection (schedSeq g ηf x0 ξ n))‖ ^ 2) (Pω p) := by
  intro n
  induction n with
  | zero =>
      simp only [schedSeq]
      exact ⟨integrable_const _, integrable_const _, integrable_const _, integrable_const _⟩
  | succ n ih =>
      obtain ⟨iV, iw, iA, ia⟩ := ih
      obtain ⟨hη0, hη⟩ := hηf n
      set lam := lamOf Lh ρh G Luv μ Lv LJ ρJ σu
      have hlam := H.lam_ge (ρh := ρh) (ρJ := ρJ) R.hσu
      have hVc : Continuous (fun y => Vfun K h gh φ Jφ lam y - hstar) :=
        (H.Vfun_cont lam).sub continuous_const
      have hV0 : ∀ y, 0 ≤ Vfun K h gh φ Jφ lam y - hstar :=
        fun y => sub_nonneg.mpr (H.V_lower hlow hlam y)
      have hSm := measurable_schedSeq O.meas ηf x0 (n + 1)
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine (run_step O.meas ηf x0 n _ hVc hV0 _ (fun y => H.pt_V O R hη0 hη y) ?_).1
        exact (((iV.sub ((ia.const_mul _))).sub (iw.const_mul _)).add (integrable_const _))
      · refine (run_step O.meas ηf x0 n (fun y => ‖wv K φ y‖ ^ 2) (H.wv_cont.norm.pow 2)
          (fun y => sq_nonneg _) _ (fun y => H.pt_w O R hη0 hη y) ?_).1
        exact ((iw.const_mul _).add ((ia.const_mul _).div_const _)).add (integrable_const _)
      · refine (run_step O.meas ηf x0 n (fun y => ‖A (wv K φ y)‖ ^ 2)
          ((A.continuous.comp H.wv_cont).norm.pow 2) (fun y => sq_nonneg _) _
          (fun y => H.pt_Aw O R hη0 hη y) ?_).1
        exact ((iA.const_mul _).add (ia.const_mul _)).add (integrable_const _)
      · have hm : Measurable (fun ξ => ‖ar K gh (Kᗮ.starProjection
            (schedSeq g ηf x0 ξ (n + 1)))‖ ^ 2) :=
          (((H.ar_cont.comp Kᗮ.starProjection.continuous).measurable.comp hSm).norm).pow_const 2
        refine Integrable.mono' (integrable_const (G ^ 2)) hm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (H.ar_norm _) 2

lemma run_rec {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {hstar : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y)
    (ηf : ℕ → ℝ) (hηf : ∀ n, 0 ≤ ηf n ∧ 8 * ηf n * Lv ≤ 1) (x0 : E) (n : ℕ) :
    let S := fun m ξ => schedSeq g ηf x0 ξ m
    let lam := lamOf Lh ρh G Luv μ Lv LJ ρJ σu
    let η := ηf n
    let Γ := Luv / μ
    (∫ ξ, (Vfun K h gh φ Jφ lam (S (n + 1) ξ) - hstar) ∂(Pω p) ≤
      ∫ ξ, (Vfun K h gh φ Jφ lam (S n ξ) - hstar) ∂(Pω p) -
        (η / 2) * ∫ ξ, ‖ar K gh (Kᗮ.starProjection (S n ξ))‖ ^ 2 ∂(Pω p) -
        η * lam * μ / 2 * ∫ ξ, ‖wv K φ (S n ξ)‖ ^ 2 ∂(Pω p) +
        η ^ 2 * NOf Lh ρh G Luv μ Lv LJ ρJ σu σv) ∧
    (∫ ξ, ‖wv K φ (S (n + 1) ξ)‖ ^ 2 ∂(Pω p) ≤
      (1 - η * μ / 2) * ∫ ξ, ‖wv K φ (S n ξ)‖ ^ 2 ∂(Pω p) +
        η * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) / μ *
          ∫ ξ, ‖ar K gh (Kᗮ.starProjection (S n ξ))‖ ^ 2 ∂(Pω p) +
        η ^ 2 * (4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv))) ∧
    (∫ ξ, ‖A (wv K φ (S (n + 1) ξ))‖ ^ 2 ∂(Pω p) ≤
      (1 - η * μ / 2) * ∫ ξ, ‖A (wv K φ (S n ξ))‖ ^ 2 ∂(Pω p) +
        η * (8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)) *
          ∫ ξ, ‖ar K gh (Kᗮ.starProjection (S n ξ))‖ ^ 2 ∂(Pω p) +
        η ^ 2 * (4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4)) ∧
    (∫ ξ, ‖ar K gh (Kᗮ.starProjection (S (n + 1) ξ))‖ ^ 2 ∂(Pω p) ≤
      (1 + 4 * Lh * η) * ∫ ξ, ‖ar K gh (Kᗮ.starProjection (S n ξ))‖ ^ 2 ∂(Pω p) +
        2 * Lh * η * Luv ^ 2 * ∫ ξ, ‖wv K φ (S n ξ)‖ ^ 2 ∂(Pω p) +
        η ^ 2 * ((2 * G * ρh + Lh ^ 2) * σu ^ 2)) := by
  intro S lam η Γ
  obtain ⟨iV, iw, iA, ia⟩ := H.run_int O R hlow ηf hηf x0 n
  obtain ⟨hη0, hη⟩ := hηf n
  have hlam := H.lam_ge (ρh := ρh) (ρJ := ρJ) R.hσu
  have hLv : 0 < Lv := lt_of_lt_of_le H.μpos H.μ_le
  have hηLh : 8 * Lh * η ≤ 1 := by
    have : Lh ≤ Lv := by have := R.hLh; have := H.μ_le; have := H.Lh_nn; linarith
    have := mul_le_mul_of_nonneg_left this hη0
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hVc : Continuous (fun y => Vfun K h gh φ Jφ lam y - hstar) :=
      (H.Vfun_cont lam).sub continuous_const
    have hV0 : ∀ y, 0 ≤ Vfun K h gh φ Jφ lam y - hstar :=
      fun y => sub_nonneg.mpr (H.V_lower hlow hlam y)
    have i1 := ((iV.sub (ia.const_mul (η / 2))).sub (iw.const_mul (η * lam * μ / 2))).add
      (integrable_const (η ^ 2 * NOf Lh ρh G Luv μ Lv LJ ρJ σu σv))
    have := (run_step O.meas ηf x0 n _ hVc hV0 _ (fun y => H.pt_V O R hη0 hη y) i1).2
    refine this.trans (le_of_eq ?_)
    rw [int_comb iV ia iw 1 (-(η / 2)) (-(η * lam * μ / 2))
      (η ^ 2 * NOf Lh ρh G Luv μ Lv LJ ρJ σu σv) (fun ξ => by ring)]
    ring
  · have i1 := ((iw.const_mul (1 - η * μ / 2)).add
      ((ia.const_mul (η * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ))).div_const μ)).add
      (integrable_const (η ^ 2 * (4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv))))
    have := (run_step O.meas ηf x0 n (fun y => ‖wv K φ y‖ ^ 2) (H.wv_cont.norm.pow 2)
      (fun y => sq_nonneg _) _ (fun y => H.pt_w O R hη0 hη y) i1).2
    refine this.trans (le_of_eq ?_)
    rw [int_comb iw ia ia (1 - η * μ / 2)
      (η * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) / μ) 0
      (η ^ 2 * (4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv))) (fun ξ => by ring)]
    ring
  · have i1 := ((iA.const_mul (1 - η * μ / 2)).add
      (ia.const_mul (η * (8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G))))).add
      (integrable_const (η ^ 2 * (4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4)))
    have := (run_step O.meas ηf x0 n (fun y => ‖A (wv K φ y)‖ ^ 2)
      ((A.continuous.comp H.wv_cont).norm.pow 2) (fun y => sq_nonneg _) _
      (fun y => H.pt_Aw O R hη0 hη y) i1).2
    refine this.trans (le_of_eq ?_)
    rw [int_comb iA ia ia (1 - η * μ / 2) (η * (8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)))
      0 (η ^ 2 * (4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4)) (fun ξ => by ring)]
    ring
  · have i1 := ((ia.const_mul (1 + 4 * Lh * η)).add (iw.const_mul (2 * Lh * η * Luv ^ 2))).add
      (integrable_const (η ^ 2 * ((2 * G * ρh + Lh ^ 2) * σu ^ 2)))
    have hac : Continuous (fun y => ‖ar K gh (Kᗮ.starProjection y)‖ ^ 2) :=
      ((H.ar_cont.comp Kᗮ.starProjection.continuous).norm).pow 2
    have := (run_step O.meas ηf x0 n (fun y => ‖ar K gh (Kᗮ.starProjection y)‖ ^ 2) hac
      (fun y => sq_nonneg _) _ (fun y => H.pt_a O hη0 hηLh y) i1).2
    refine this.trans (le_of_eq ?_)
    rw [int_comb ia iw iw (1 + 4 * Lh * η) (2 * Lh * η * Luv ^ 2) 0
      (η ^ 2 * ((2 * G * ρh + Lh ^ 2) * σu ^ 2)) (fun ξ => by ring)]
    ring

end Model

end OracleTemplate.RiverValley
