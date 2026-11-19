import LongTails.Proofs.MarkovClippedExecution
import LongTails.Proofs.MarkovClippedTuning
import LongTails.Proofs.HeavyTailedMarkovLaw

open MeasureTheory ProbabilityTheory OracleTemplate Function Preorder

namespace LongTails.Proofs.MarkovClippedExpectation

open LongTails.Setups.MarkovSmoothNonconvex LongTails.Algorithms.MarkovClippedSgd
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex (mixingDistance pathLaw)
open MarkovClippedTuning MarkovClippedExecution HeavyTailedMarkovGradient

variable (p : Params) (hv : spec.valid p) {Z : Type} [MeasurableSpace Z]
    {f : Space p → ℝ} {g : Space p → Z → Space p}

noncomputable abbrev iterate (g : Space p → Z → Space p) (z : ℕ → Z) (k : ℕ) : Space p :=
  point g (stepSize p) (threshold p) (period p) p.x0 z k

noncomputable def gradBound (f : Space p → ℝ) (k : ℕ) : ℝ :=
  ‖gradient f p.x0‖ + p.L * (k * stepSize p * threshold p)

omit [MeasurableSpace Z] in
include hv in
lemma grad_bound (hl : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (g : Space p → Z → Space p) (z : ℕ → Z) (k : ℕ) :
    ‖gradient f (iterate p g z k)‖ ≤ gradBound p f k := by
  obtain ⟨_, hC, hη, _⟩ := constants p hv
  have hr := point_radius g hη.le hC.le (period p) p.x0 z k
  have hh := (hl (iterate p g z k) p.x0).trans (mul_le_mul_of_nonneg_left hr hv.1.le)
  exact (norm_le_norm_sub_add _ _).trans (by unfold gradBound; linarith)

private def extend {Z : Type} (k : ℕ) (h : Finset.Iic k → Z) (i : ℕ) : Z :=
  h ⟨min i k, Finset.mem_Iic.mpr (min_le_right _ _)⟩

private lemma measurable_extend (k : ℕ) : Measurable (extend (Z := Z) k) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

include hv in
lemma expected_score (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hmix : ∀ t z, mixingDistance κ π t z ≤ 2 * Real.exp (-(t : ℝ) / p.τ))
    (hl : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) (π : Measure Z))
    (hmean : ∀ x, ∫ z, g x z ∂(π : Measure Z) = gradient f x)
    (hmi : ∀ x, Integrable (fun z => ‖g x z - gradient f x‖ ^ 2) (π : Measure Z))
    (hm : ∀ x, (∫ z, ‖g x z - gradient f x‖ ^ 2 ∂(π : Measure Z)) ≤ p.σ ^ 2) (k : ℕ) :
    (∫ z, score p (gradient f (iterate p g z k)) (g (iterate p g z k) (z (k * period p)))
      ∂(pathLaw κ π : Measure (ℕ → Z))) ≤ 0 := by
  let m := period p
  have hc := (AbcSgdRate.gradient_continuous hl).measurable
  have hsection (x : Space p) : Measurable (g x) := hg.of_uncurry_left
  have hscore (x : Space p) : Measurable (fun y => score p (gradient f x) (g x y)) := by
    have hpair : Measurable (fun y => (gradient f x, g x y)) := measurable_const.prodMk (hsection x)
    have hs := (score_measurable p).comp hpair
    exact hs
  cases k with
  | zero =>
    let W := fun y => score p (gradient f p.x0) (g p.x0 y)
    simp only [Nat.zero_mul]
    change (∫ z, W (z 0) ∂(pathLaw κ π : Measure (ℕ → Z))) ≤ 0
    rw [← integral_map (measurable_pi_apply 0).aemeasurable (hscore p.x0).aestronglyMeasurable,
      pathLaw_map_zero]
    apply score_mean p hv π (π : Measure Z) (hsection _)
      (hi _) (hmean _) (hmi _) (hm _)
    intro V _ B hB _
    obtain ⟨_, hC, _⟩ := constants p hv
    have hε := hv.2.1
    simp only [sub_self, abs_zero]
    positivity
  | succ k =>
    let t := k * m
    let X := fun h : Finset.Iic t → Z => iterate p g (extend t h) (k + 1)
    have hx : Measurable X := (point_measurable hg _ _ m p.x0 (k+1)).comp (measurable_extend t)
    have he (z : ℕ → Z) : X (frestrictLe t z) = iterate p g z (k+1) := by
      apply point_congr
      intro j hj
      have hle : j * m ≤ t := Nat.mul_le_mul_right m (by omega)
      simp [extend, m, t, frestrictLe, min_eq_left hle]
    let W := fun h y => score p (gradient f (X h)) (g (X h) y)
    have hxp : Measurable (fun z : (Finset.Iic t → Z) × Z => X z.1) := hx.comp measurable_fst
    have hgpair := hg.comp (hxp.prodMk (measurable_snd (α := Finset.Iic t → Z) (β := Z)))
    have hW := (score_measurable p).comp ((hc.comp hxp).prodMk hgpair)
    change Measurable (Function.uncurry W) at hW
    let U := gradBound p f (k+1)
    let B := p.L * stepSize p / 2 * threshold p ^ 2 + (threshold p + p.ε / 4) * U + p.ε ^ 2 / 8
    obtain ⟨_, hC, _, _⟩ := constants p hv
    have hε := hv.2.1
    have hbd (h : Finset.Iic t → Z) (y : Z) : |W h y| ≤ B := by
      have h1 := score_bound p hv (gradient f (X h)) (g (X h) y)
      have h2 := grad_bound p hv hl g (extend t h) (k+1)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ threshold p + p.ε / 4)
      exact h1.trans (by dsimp only [B, U]; linarith only [h3])
    have hj := pathLaw_integral_future κ π t m hW hbd
    have hfun (z : ℕ → Z) : W (frestrictLe t z) (z (t+m)) =
        score p (gradient f (iterate p g z (k+1))) (g (iterate p g z (k+1)) (z ((k+1)*period p))) := by
      simp only [W, he, Nat.succ_mul, t, m]
    simp_rw [hfun] at hj
    rw [hj]
    apply integral_nonpos
    intro h
    let a := h ⟨t, Finset.mem_Iic.mpr le_rfl⟩
    apply score_mean p hv π ((κ ^ m) a) (hsection _)
      (hi (X h)) (hmean _) (hmi _) (hm _)
    intro V hV D hD hVb
    exact (integral_sub_le_mixingDistance κ π m a hD hV hVb).trans
      (mul_le_mul_of_nonneg_left ((hmix m a).trans (period_pos_and_mix p hv).2) (by positivity))

end LongTails.Proofs.MarkovClippedExpectation
