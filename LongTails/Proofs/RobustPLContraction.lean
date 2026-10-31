import LongTails.Proofs.RobustPLExpect

open Set Metric MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RobustPLPotential

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma geometry_hyp {f : E → ℝ} {u : E} {L μ ρ : ℝ}
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hdiff : Differentiable ℝ (gradient f))
    (hhess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hmin : IsMinOn f univ u) (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hρ : 0 ≤ ρ) :
    PLHessian.Hyp P f (fun x (_ : Ω) => gradient f x) u L μ ρ 0 1 where
  grad := hgrad
  lip := hlip
  diff := hdiff
  hess := hhess
  min := hmin
  pl := hpl
  meas := hdiff.continuous.measurable.comp measurable_fst
  int _ := integrable_const _
  mean _ := by simp
  var_int _ := by simp
  kurt_int _ := by simp
  var _ := by simp
  kurt _ := by simp
  L_pos := hμ.trans_le hμL
  μ_pos := hμ
  μ_le := hμL
  ρ_nn := hρ
  σ_nn := le_rfl
  K_ge := le_rfl

open PLHessian

set_option maxHeartbeats 1000000 in
lemma contraction {f : E → ℝ} {u : E} {L μ ρ η lam t B V Q : ℝ}
    (H : PLHessian.Hyp P f (fun x (_ : Ω) => gradient f x) u L μ ρ 0 1)
    {ζ : Ω → E} (hm : Measurable ζ) (hi : Integrable ζ P)
    (hi2 : Integrable (fun ω => ‖ζ ω‖ ^ 2) P) (hi4 : Integrable (fun ω => ‖ζ ω‖ ^ 4) P)
    (hbias : ‖∫ ω, ζ ω ∂P‖ ≤ B) (hvar : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ V)
    (hfourth : (∫ ω, ‖ζ ω‖ ^ 4 ∂P) ≤ Q)
    (hη : 0 < η) (ht : 0 < t) (hlam : lam * μ = 32 * Real.sqrt (L / μ))
    (hlocal : 36864 * ρ ^ 2 * t ≤ μ ^ 3)
    (hstep : 8 * L * η ≤ 1) (hsmall : 32 * Real.sqrt (L / μ) * η ^ 2 * L ^ 2 ≤ 1)
    (hVsmall : 96 * lam * L * η * V ≤ t)
    (hQsmall : 4 * lam * L ^ 2 * η ^ 2 * Q ≤ t * V)
    (hBsmall : B ^ 2 ≤ μ * η * V) (x : E) :
    Integrable (fun ω => pot f u lam t (x - η • (gradient f x + ζ ω))) P ∧
    (∫ ω, pot f u lam t (x - η • (gradient f x + ζ ω)) ∂P) ≤
      (1 - μ * η / 64) * pot f u lam t x - η * (f x - f u) / 2 + 290 * η ^ 2 * V := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let s := Real.sqrt (L / μ)
  have hL := H.L_pos
  have hμ := H.μ_pos
  have hs : 1 ≤ s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ((le_div_iff₀ hμ).mpr (by linarith [H.μ_le]))
  have hlam0 : 0 ≤ lam := by
    have h : 0 ≤ lam * μ := by rw [hlam]; positivity
    exact nonneg_of_mul_nonneg_left h hμ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hbias
  have hV0 : 0 ≤ V := (integral_nonneg fun ω => sq_nonneg ‖ζ ω‖).trans hvar
  let G := gradient f x
  let Φ := f x - f u
  let b := t / 4
  let δ := η / 2 * ‖G‖ ^ 2
  let c := dhub b b (Φ - δ)
  have hΦ : 0 ≤ Φ := sub_nonneg.mpr (H.min (mem_univ x))
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 ≤ c := dhub_nonneg hb _
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  obtain ⟨p0, hp0, hnear⟩ := nearest (u := u) H.continuous x
  let d := x - p0
  have hmin0 : IsMinOn f univ p0 := fun z _ => by rw [hp0]; exact H.min (mem_univ z)
  have hgp0 := grad_zero_of_min hL H.grad H.lip hmin0
  have hdist : distSq f u x = ‖d‖ ^ 2 := by unfold distSq; rw [hnear]
  have hD : μ * ‖d‖ ^ 2 ≤ 16 * Φ := by
    obtain ⟨p', hp', hq⟩ := quad_growth hL hμ H.μ_le H.grad H.lip H.min H.pl x
    have hd : ‖d‖ ≤ ‖x - p'‖ := by
      rw [← hnear]
      have hh := infDist_le_dist_of_mem (x := x) (show p' ∈ minSet f u from
        le_antisymm (hp' (mem_univ u)) (H.min (mem_univ p')))
      rwa [dist_eq_norm] at hh
    have hh := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith
  have hG2 : ‖G‖ ^ 2 ≤ 2 * L * Φ := grad_sq_le hL H.grad H.lip H.min x
  have hG2' : 2 * μ * Φ ≤ ‖G‖ ^ 2 := H.pl x
  have hδle : δ ≤ L * η * Φ := by
    have hh := mul_le_mul_of_nonneg_left hG2 (show 0 ≤ η / 2 by positivity)
    dsimp [δ]
    nlinarith
  have hconv : hub b b (Φ - δ) + c * δ ≤ hub b b Φ := by
    have hh := hub_tangent (a := b) hb (Φ - δ) Φ
    rwa [show Φ - (Φ - δ) = δ by ring] at hh
  have hct : c * t ≤ 4 * Φ := by
    have hh := (dhub_mono hb (by linarith : Φ - δ ≤ Φ)).trans (dhub_le_div hb hb hΦ)
    change c ≤ Φ / b at hh
    rw [le_div_iff₀ hb] at hh
    dsimp [b] at hh
    linarith
  have hcase : ∃ r, hub b b Φ ≤ c * Φ + r ∧
      ((Φ ≤ ⟪G, d⟫ ∧ r ≤ 4 * η ^ 2 * L ^ 2 * Φ) ∨
      (-6 * s * Φ ≤ ⟪G, d⟫ ∧ c = 1 ∧ hub b b Φ ≤ Φ)) := by
    by_cases ha : Φ ≤ t
    · refine ⟨δ ^ 2 / b, hub_decrease hb.le hb hδ, Or.inl ⟨?_, ?_⟩⟩
      · exact H.aim_region hlocal hp0 hgp0 hD ha
      · exact sq_div_le hΦ ht hδ hδle ha
    · have hfar : b + b ≤ Φ - δ := by
        have hh := mul_le_mul_of_nonneg_right hstep hΦ
        dsimp [b]
        linarith
      obtain ⟨hc1, hH⟩ := hub_decrease_far hb.le hb hδ hfar
      refine ⟨0, hH, Or.inr ⟨by simpa only [neg_mul, s] using far_inner hμ hL hΦ hG2 hD, hc1, ?_⟩⟩
      exact hub_le_self hb.le hb hΦ
  have hLη : L * η ≤ 1 / 2 := by linarith
  have hraw := raw_potential_step H.grad H.lip hL.le hη.le hLη hlam0 hb hm hi hi2 hi4
    hbias hvar hfourth x u p0 hp0
  refine ⟨hraw.1, ?_⟩
  obtain ⟨r, hH, hcases⟩ := hcase
  have hdg : μ * (‖d‖ + η * ‖G‖) ^ 2 ≤ 36 * Φ := by
    have hμL := H.μ_le
    have hmul : μ * η ^ 2 * L ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_right hμL (show 0 ≤ η ^ 2 * L by positivity)
      have h2 : (L * η) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (L * η)]
      nlinarith
    have h1 := mul_le_mul_of_nonneg_left hG2 (show 0 ≤ 2 * μ * η ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmul hΦ
    have h3 := mul_nonneg hμ.le (sq_nonneg (‖d‖ - η * ‖G‖))
    nlinarith
  have hdb := distance_bias (B := B) hη.le hμ hdg
  have hgbsmall : 64 * lam * B ^ 2 ≤ t := by
    have h1 := mul_le_mul_of_nonneg_left hBsmall (show 0 ≤ 64 * lam by positivity)
    have h2 := mul_le_mul_of_nonneg_right H.μ_le (show 0 ≤ 64 * lam * η * V by positivity)
    have h3 : 0 ≤ lam * L * η * V := by positivity
    nlinarith
  have hgb := gradient_bias hη.le hlam0 hc ht hΦ hct hgbsmall (g := ‖G‖)
  have hnorm : ‖d - η • G‖ ≤ ‖d‖ + η * ‖G‖ := by
    have hh := norm_sub_le d (η • G)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hη] using hh
  have hdb' : 2 * η * ‖d - η • G‖ * B ≤ η * Φ / 8 + 288 * η * B ^ 2 / μ := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (by positivity)) hB0).trans hdb
  have hdexp : ‖d - η • G‖ ^ 2 = ‖d‖ ^ 2 - 2 * η * ⟪G, d⟫ + η ^ 2 * ‖G‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  have hpot : pot f u lam t x = ‖d‖ ^ 2 + lam * hub b b Φ := by
    unfold pot
    rw [hdist]
  have hbound : (∫ ω, pot f u lam t (x - η • (gradient f x + ζ ω)) ∂P) ≤
      ‖d‖ ^ 2 + lam * hub b b Φ - 2 * η * ⟪G, d⟫ + η ^ 2 * ‖G‖ ^ 2 -
      3 / 8 * lam * c * η * ‖G‖ ^ 2 + η * Φ / 4 + 288 * η * B ^ 2 / μ +
      η ^ 2 * V + lam * c * L * η ^ 2 * V + 4 * lam * η ^ 2 * ‖G‖ ^ 2 * V / t +
      4 * lam * L ^ 2 * η ^ 4 * Q / t := by
    have hh := hraw.2
    change (∫ ω, pot f u lam t (x - η • (gradient f x + ζ ω)) ∂P) ≤
      ‖d - η • G‖ ^ 2 + 2 * η * ‖d - η • G‖ * B + η ^ 2 * V +
      lam * (hub b b (Φ - δ) + c * (L * η ^ 2 * V + η * ‖G‖ * B) +
        (η ^ 2 * ‖G‖ ^ 2 * V + L ^ 2 * η ^ 4 * Q) / b) at hh
    rw [hdexp] at hh
    have hcv := mul_le_mul_of_nonneg_left hconv hlam0
    dsimp [δ] at hcv
    have he : lam * ((η ^ 2 * ‖G‖ ^ 2 * V + L ^ 2 * η ^ 4 * Q) / b) =
        4 * lam * η ^ 2 * ‖G‖ ^ 2 * V / t + 4 * lam * L ^ 2 * η ^ 4 * Q / t := by
      dsimp [b]
      ring
    rw [mul_add] at hh
    rw [he] at hh
    nlinarith only [hh, hcv, hdb', hgb]
  have hfin := assembled_step hη hμ hL.le hΦ hs hlam hlam0 hD hc hG2' hG2 hstep hsmall
    hH hcases ht hV0 hct hVsmall hQsmall hBsmall hbound
  rwa [hpot]

end OracleTemplate.RobustPLPotential
