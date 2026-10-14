import LongTails.Proofs.AcceleratedMarkovRun
import LongTails.Proofs.HeavyTailedMarkovError

open MeasureTheory ProbabilityTheory Set Preorder
open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def clippedRunError [CompleteSpace E] (f : E → ℝ) (g : E → Ω → E) (D R C p : ℝ)
    (m : ℕ) (x0 u : E) (k : ℕ) (ξ : ℕ → Ω) : ℝ :=
  let s := clippedRun g D R C m x0 ξ k
  let y := Gradient.acceleratedQuery s
  heavyError (((k : ℝ) + 1) / 2) D R p (s.2.2 - u) (gradient f y - clip C (g y (ξ (k * m))))

lemma clippedRun_energy_step [CompleteSpace E] {f : E → ℝ} (g : E → Ω → E)
    {L D R C p : ℝ} (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (m : ℕ) (x0 u : E) (hu : ‖u - x0‖ ≤ R) (k : ℕ) (ξ : ℕ → Ω) :
    StochasticGradient.acceleratedEnergy f D u (k + 1) (clippedRun g D R C m x0 ξ (k + 1)).2 ≤
      StochasticGradient.acceleratedEnergy f D u k (clippedRun g D R C m x0 ξ k).2 +
        clippedRunError f g D R C p m x0 u k ξ := by
  let s := clippedRun g D R C m x0 ξ k
  have hi : s.1 = k := clippedRun_index g D R C m x0 ξ k
  have hs := accelerated_projected_step hL.le hD hLD hR hp hp2 hc hg hlip
    x0 s.2.1 s.2.2 u (clip C (g (Gradient.acceleratedQuery s) (ξ (k * m))))
    (clippedRun_ball g D C hR m x0 ξ k).2 hu
    (A := (k : ℝ) * ((k : ℝ) + 1) / 4) (a := ((k : ℝ) + 1) / 2)
    (by positivity) (by positivity) (by positivity)
    (by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
  have hw : ((k : ℝ) + 1) * ((k : ℝ) + (1 + 1)) / 4 =
      (k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2 := by ring
  simpa only [StochasticGradient.acceleratedEnergy, StochasticGradient.acceleratedWeight,
    clippedRun, projectedClippedUpdate, clippedRun_index, Gradient.acceleratedQuery,
    Nat.cast_add, Nat.cast_one, hw, clippedRunError, heavyError, add_assoc, s, hi] using hs

def extendHistory (k : ℕ) (h : Finset.Iic k → Ω) (n : ℕ) : Ω :=
  h ⟨min n k, Finset.mem_Iic.mpr (Nat.min_le_right _ _)⟩

lemma measurable_extendHistory [MeasurableSpace Ω] (k : ℕ) : Measurable (extendHistory (Ω := Ω) k) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma clippedRun_prefix (g : E → Ω → E) (D R C : ℝ) (m : ℕ) (x0 : E)
    (k : ℕ) (ξ : ℕ → Ω) :
    clippedRun g D R C m x0 (extendHistory (k * m) (frestrictLe (k * m) ξ)) (k + 1) =
      clippedRun g D R C m x0 ξ (k + 1) := by
  apply clippedRun_congr
  intro j hj
  have hj' : j * m ≤ k * m := Nat.mul_le_mul_right m (by omega)
  simp only [extendHistory, frestrictLe, Nat.min_eq_left hj']
  rfl

lemma measurable_clippedRun_query [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (D R C : ℝ) (m : ℕ) (x0 : E) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => Gradient.acceleratedQuery (clippedRun g D R C m x0 ξ k)) := by
  have hs := measurable_clippedRun hg D R C m x0 k
  simp only [Gradient.acceleratedQuery, clippedRun_index]
  exact (hs.fst.const_smul _).add (hs.snd.const_smul _)

lemma measurable_gradient_of_lipschitz [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Measurable (gradient f) := by
  have hh : LipschitzWith ⟨L, hL⟩ (gradient f) := lipschitzWith_iff_norm_sub_le.mpr hlip
  exact hh.continuous.measurable

lemma clippedRunError_bound [CompleteSpace E] {f : E → ℝ} (g : E → Ω → E)
    {L D R C p : ℝ} (hL : 0 < L) (hD : 0 < D) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hLC : 4 * L * R ≤ C) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (m : ℕ) (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R)
    (k : ℕ) (ξ : ℕ → Ω) :
    |clippedRunError f g D R C p m x0 u k ξ| ≤ 6 * R * (((k : ℝ) + 1) / 2) * C := by
  let s := clippedRun g D R C m x0 ξ k
  let y := Gradient.acceleratedQuery s
  have hv : ‖s.2.2 - u‖ ≤ 2 * R := by
    have hz := (clippedRun_ball g D C hR m x0 ξ k).2
    calc
      _ ≤ ‖s.2.2 - x0‖ + ‖x0 - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * R := by rw [norm_sub_rev x0 u]; linarith
  have hgrad := gradient_ball hL hg hlip hm hu (clippedRun_query_ball g D C hR m x0 ξ k)
  have he : ‖gradient f y - clip C (g y (ξ (k * m)))‖ ≤ 3 * C / 2 :=
    (norm_sub_le _ _).trans (by have hh := norm_clip_le hC (g y (ξ (k * m))); dsimp [y, s] at *; linarith)
  exact (heavyError_bound (by positivity) hD hR hv he).trans (by ring_nf; rfl)

lemma integrable_clippedRunError [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {f : E → ℝ} {g : E → Ω → E}
    {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P]
    (hG : Measurable (Function.uncurry g)) {L D R C p : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hR : 0 ≤ R) (hC : 0 ≤ C) (hLC : 4 * L * R ≤ C)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (m : ℕ) (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (k : ℕ) :
    Integrable (clippedRunError f g D R C p m x0 u k) P := by
  have hs := measurable_clippedRun hG D R C m x0 k
  have hy := measurable_clippedRun_query hG D R C m x0 k
  have he : Measurable (clippedRunError f g D R C p m x0 u k) :=
    (measurable_heavyError _ D R p).comp ((hs.snd.sub_const u).prodMk
      (((measurable_gradient_of_lipschitz hL.le hlip).comp hy).sub
        ((measurable_clip C).comp (hG.comp (hy.prodMk (measurable_pi_apply _))))))
  exact Integrable.of_bound he.aestronglyMeasurable (6 * R * (((k : ℝ) + 1) / 2) * C)
    (Filter.Eventually.of_forall (clippedRunError_bound g hL hD hR hC hLC hg hlip m x0 u hm hu k))

lemma integrable_energy_ball {H : Type*} [MeasurableSpace H]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure H} [IsProbabilityMeasure P] {s : H → E × E} (hs : Measurable s)
    {f : E → ℝ} {L D R : ℝ} (hL : 0 < L) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x0 u : E} (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R)
    (hb : ∀ h, ‖(s h).1 - x0‖ ≤ R ∧ ‖(s h).2 - x0‖ ≤ R) (k : ℕ) :
    Integrable (fun h => StochasticGradient.acceleratedEnergy f D u k (s h)) P := by
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hg x).differentiableAt.continuousAt)).measurable
  apply Integrable.of_bound ((StochasticGradient.measurable_acceleratedEnergy hf D u k).comp hs).aestronglyMeasurable
    (StochasticGradient.acceleratedWeight k * (2 * L * R ^ 2) + 2 * D * R ^ 2)
  apply Filter.Eventually.of_forall
  intro h
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (StochasticGradient.acceleratedEnergy_nonneg hD hm k (s h))]
  have hg' := (smooth_gap_ball hL hR hg hlip hm hu (hb h).1).2
  have hz : ‖(s h).2 - u‖ ≤ 2 * R := by
    calc
      _ ≤ ‖(s h).2 - x0‖ + ‖x0 - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * R := by rw [norm_sub_rev x0 u]; have hh := (hb h).2; linarith
  have hz' : ‖(s h).2 - u‖ ^ 2 ≤ (2 * R) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz
  have h₁ := mul_le_mul_of_nonneg_left hg' (StochasticGradient.acceleratedWeight_nonneg k)
  have h₂ := mul_le_mul_of_nonneg_left hz' hD
  unfold StochasticGradient.acceleratedEnergy
  nlinarith only [h₁, h₂]

end OracleTemplate.HeavyTailedMarkovGradient
