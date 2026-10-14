import LongTails.Proofs.AcceleratedMarkovEnergy

open MeasureTheory ProbabilityTheory Set Preorder

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω]

lemma integral_clippedRunError_succ (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ δ : ℝ} (hL : 0 < L) (hD : 0 < D) (hR : 0 ≤ R)
    (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (m : ℕ) (hd : Integrable (mixingDistance κ π m) (π : Measure Ω))
    (hmix : (∫ y, mixingDistance κ π m y ∂(π : Measure Ω)) ≤ δ)
    (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (k : ℕ) :
    (∫ ξ, clippedRunError f g D R C p m x0 u (k + 1) ξ ∂(pathLaw κ π : Measure (ℕ → Ω))) ≤
      2 * R * (((k + 1 : ℕ) : ℝ) + 1) / 2 * (σ ^ p / (C / 2) ^ (p - 1)) +
      (((((k + 1 : ℕ) : ℝ) + 1) / 2) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * σ ^ p +
      12 * R * ((((k + 1 : ℕ) : ℝ) + 1) / 2) * C * δ := by
  let a := ((((k + 1 : ℕ) : ℝ) + 1) / 2)
  let ρ := (pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe (k * m))
  let S := fun h : Finset.Iic (k * m) → Ω => clippedRun g D R C m x0 (extendHistory (k * m) h) (k + 1)
  let Y := fun h => Gradient.acceleratedQuery (S h)
  let W := fun h y => heavyError a D R p ((S h).2.2 - u) (gradient f (Y h) - clip C (g (Y h) y))
  have : IsProbabilityMeasure ρ := inferInstance
  have hS : Measurable (fun h => (S h).2) :=
    (measurable_clippedRun hG D R C m x0 (k + 1)).comp (measurable_extendHistory (k * m))
  have hY : Measurable Y :=
    (measurable_clippedRun_query hG D R C m x0 (k + 1)).comp (measurable_extendHistory (k * m))
  have hgrad : Measurable (fun h => gradient f (Y h)) := (measurable_gradient_of_lipschitz hL.le hlip).comp hY
  have hGY : Measurable (fun z : (Finset.Iic (k * m) → Ω) × Ω => g (Y z.1) z.2) :=
    hG.comp ((hY.comp measurable_fst).prodMk measurable_snd)
  have hW : Measurable (Function.uncurry W) :=
    (measurable_heavyError a D R p).comp (((hS.snd.sub_const u).comp measurable_fst).prodMk
      ((hgrad.comp measurable_fst).sub ((measurable_clip C).comp hGY)))
  have hgn : ∀ h, ‖gradient f (Y h)‖ ≤ C / 2 := by
    intro h
    have hh := gradient_ball hL hg hlip hm hu
      (clippedRun_query_ball g D C hR m x0 (extendHistory (k * m) h) (k + 1))
    change ‖gradient f (Y h)‖ ≤ C / 2
    change ‖gradient f (Y h)‖ ≤ 2 * L * R at hh
    linarith
  have hvn : ∀ h, ‖(S h).2.2 - u‖ ≤ 2 * R := by
    intro h
    have hh := (clippedRun_ball g D C hR m x0 (extendHistory (k * m) h) (k + 1)).2
    calc
      _ ≤ ‖(S h).2.2 - x0‖ + ‖x0 - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * R := by rw [norm_sub_rev x0 u]; linarith
  have hbound : ∀ h y, |W h y| ≤ 6 * R * a * C := by
    intro h y
    have he : ‖gradient f (Y h) - clip C (g (Y h) y)‖ ≤ 3 * C / 2 :=
      (norm_sub_le _ _).trans (by have hh := norm_clip_le hC.le (g (Y h) y); have hh' := hgn h; linarith)
    exact (heavyError_bound (by dsimp [a]; positivity) hD hR (hvn h) he).trans (by ring_nf; rfl)
  have hmap : ρ.map (fun h => h ⟨k * m, Finset.mem_Iic.mpr le_rfl⟩) = (π : Measure Ω) := by
    rw [show ρ = (pathLaw κ π : Measure (ℕ → Ω)).map (frestrictLe (k * m)) from rfl,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact pathLaw_stationary_marginal κ π hπ (k * m)
  have hh := averaged_heavyError_bound κ π (G := fun h y => g (Y h) y)
    (u := fun h => gradient f (Y h)) (v := fun h => (S h).2.2 - u)
    (by fun_prop) hmap m hd hGY hgrad (hS.snd.sub_const u)
    (fun h => hGi (Y h)) (fun h => hmean (Y h))
    (show 0 ≤ a by dsimp [a]; positivity) hD hR hC hp hgn hvn
    (fun h => hmi (Y h)) (fun h => hmoment (Y h)) hmix
  have heq : (fun ξ => W (frestrictLe (k * m) ξ) (ξ (k * m + m))) =
      clippedRunError f g D R C p m x0 u (k + 1) := by
    funext ξ
    simp only [W, Y, S, clippedRun_prefix, clippedRunError, Nat.succ_mul, a]
  have hlaw := pathLaw_integral_future κ π (k * m) m hW hbound
  rw [heq] at hlaw
  rw [hlaw]
  convert hh using 1; dsimp [a]; ring

lemma integral_clippedRunError_zero (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) {f : E → ℝ} {g : E → Ω → E}
    (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ : ℝ} (hL : 0 < L) (hD : 0 < D) (hR : 0 ≤ R)
    (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (m : ℕ) (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) :
    (∫ ξ, clippedRunError f g D R C p m x0 u 0 ξ ∂(pathLaw κ π : Measure (ℕ → Ω))) ≤
      2 * R * (1 / 2) * (σ ^ p / (C / 2) ^ (p - 1)) +
      ((1 / 2 : ℝ) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) * σ ^ p := by
  let W : Ω → ℝ := fun y => heavyError (1 / 2) D R p (x0 - u) (gradient f x0 - clip C (g x0 y))
  have hW : Measurable W :=
    (measurable_heavyError (1 / 2) D R p).comp (measurable_const.prodMk
      (measurable_const.sub ((measurable_clip C).comp (hG.comp (measurable_const.prodMk measurable_id)))))
  have hmap := pathLaw_map_zero κ π
  have hW' : AEStronglyMeasurable W ((pathLaw κ π : Measure (ℕ → Ω)).map (fun ξ => ξ 0)) :=
    hW.aestronglyMeasurable
  have he := integral_map (μ := (pathLaw κ π : Measure (ℕ → Ω)))
    (measurable_pi_apply 0).aemeasurable hW'
  rw [hmap] at he
  have heq : clippedRunError f g D R C p m x0 u 0 = (fun ξ => W (ξ 0)) := by
    funext ξ
    simp [clippedRunError, clippedRun, Gradient.acceleratedQuery, W]
  rw [heq, ← he]
  have hgrad := gradient_ball hL hg hlip hm hu (show ‖x0 - x0‖ ≤ R by simpa using hR)
  apply integral_heavyError_bound (hG.comp (measurable_const.prodMk measurable_id)) (hGi x0)
    (hmean x0) (by norm_num) hD hR hC hp (by linarith) _ (hmi x0) (hmoment x0)
  rw [norm_sub_rev]
  linarith

lemma integral_clippedRunError (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ δ : ℝ} (hL : 0 < L) (hD : 0 < D) (hR : 0 ≤ R)
    (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (m : ℕ) (hd : Integrable (mixingDistance κ π m) (π : Measure Ω))
    (hmix : (∫ y, mixingDistance κ π m y ∂(π : Measure Ω)) ≤ δ)
    (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (k : ℕ) :
    (∫ ξ, clippedRunError f g D R C p m x0 u k ξ ∂(pathLaw κ π : Measure (ℕ → Ω))) ≤
      (((k : ℝ) + 1) / 2) * (2 * R * (σ ^ p / (C / 2) ^ (p - 1)) + 12 * R * C * δ) +
      ((((k : ℝ) + 1) / 2) ^ p) * ((2 * R) ^ (2 - p) / (D / 4) ^ (p - 1) * σ ^ p) := by
  cases k with
  | zero =>
    have hh := integral_clippedRunError_zero κ π hG hGi hmean hL hD hR hC hLC hp hg hlip hmi hmoment m x0 u hm hu
    have hδ : 0 ≤ δ := (integral_nonneg (mixingDistance_nonneg κ π m)).trans hmix
    have hn : 0 ≤ 12 * R * C * δ := by positivity
    simp only [Nat.cast_zero, zero_add] at ⊢
    calc
      _ ≤ _ := hh
      _ ≤ _ := by
        ring_nf at *
        nlinarith only [hn]
  | succ k =>
    have hh := integral_clippedRunError_succ κ π hπ hG hGi hmean hL hD hR hC hLC hp hg hlip hmi hmoment
      m hd hmix x0 u hm hu k
    convert hh using 1; ring

end OracleTemplate.HeavyTailedMarkovGradient
