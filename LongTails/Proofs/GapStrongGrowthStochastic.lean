import LongTails.Proofs.GapStrongGrowthStopped
import LongTails.Proofs.GapStrongGrowthExecution

open MeasureTheory Set
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

lemma measurable_queryPoint (p : Params) (n : ℕ) : Measurable (queryPoint p n) := by
  unfold queryPoint
  fun_prop

lemma measurable_batch (p : Params) {g : p.E → p.Ω → p.E}
    (hg : Measurable (fun z : p.E × p.Ω => g z.1 z.2)) :
    Measurable (fun z : p.E × (Fin (batchSize p) → p.Ω) =>
      StochasticGeneralized.batchReply g z.1 z.2) := by
  unfold StochasticGeneralized.batchReply
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i _
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_step (p : Params) (n : ℕ) :
    Measurable (fun z : (p.E × p.E) × p.E => step p n z.1 z.2) := by
  have hh := (measurable_clip (p.R / (confidence p * increment p (weight p n)))).comp
    (measurable_snd : Measurable (fun z : (p.E × p.E) × p.E => z.2))
  unfold step
  exact (((measurable_queryPoint p n).comp measurable_fst).sub
    (hh.const_smul _)).prodMk (measurable_fst.snd.sub (hh.const_smul _))

noncomputable def blockAdvance (p : Params) (g : p.E → p.Ω → p.E)
    (s : ℕ × (p.E × p.E)) (ξ : Fin (batchSize p) → p.Ω) : ℕ × (p.E × p.E) :=
  (s.1 + 1, step p s.1 s.2 (StochasticGeneralized.batchReply g (queryPoint p s.1 s.2) ξ))

lemma measurable_blockAdvance (p : Params) {g : p.E → p.Ω → p.E}
    (hg : Measurable (fun z : p.E × p.Ω => g z.1 z.2)) :
    Measurable (fun z : (ℕ × (p.E × p.E)) × (Fin (batchSize p) → p.Ω) =>
      blockAdvance p g z.1 z.2) := by
  have hh : Measurable (fun z : ℕ × ((p.E × p.E) × (Fin (batchSize p) → p.Ω)) =>
      blockAdvance p g (z.1, z.2.1) z.2.2) := by
    apply measurable_from_prod_countable_right
    intro n
    dsimp [blockAdvance]
    exact measurable_const.prodMk ((measurable_step p n).comp (measurable_fst.prodMk
      ((measurable_batch p hg).comp (((measurable_queryPoint p n).comp measurable_fst).prodMk measurable_snd))))
  exact hh.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

lemma measurable_energy (p : Params) {f : p.E → ℝ} (hf : Measurable f) (u : p.E) :
    Measurable (fun s : ℕ × (p.E × p.E) => energy p f u s.1 s.2) := by
  have hw : Measurable (fun s : ℕ × (p.E × p.E) => weight p s.1) :=
    (measurable_of_countable (weight p)).comp measurable_fst
  unfold energy
  fun_prop

lemma batch_step_exponential (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hρ : 1 ≤ p.ρ)
    {f : p.E → ℝ} {u : p.E} (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hmin : IsMinOn f univ u) (hmodel : GapUpperModel f u p.H0 p.H1)
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] {g : p.E → p.Ω → p.E}
    (hg : IsStrongGrowthOracle μ f g p.ρ) (n : ℕ) (s : p.E × p.E)
    (hV : energy p f u n s ≤ 8 * p.R ^ 2) :
    Integrable (fun ξ => Real.exp (confidence p / (64 * p.R ^ 2) *
      energy p f u (n + 1) (step p n s (StochasticGeneralized.batchReply g (queryPoint p n s) ξ))))
      (Measure.pi fun _ : Fin (batchSize p) => μ) ∧
    (∫ ξ, Real.exp (confidence p / (64 * p.R ^ 2) *
      energy p f u (n + 1) (step p n s (StochasticGeneralized.batchReply g (queryPoint p n s) ξ)))
      ∂Measure.pi (fun _ : Fin (batchSize p) => μ)) ≤
      Real.exp (confidence p / (64 * p.R ^ 2) * energy p f u n s) := by
  let a := increment p (weight p n)
  let q := confidence p
  let y := queryPoint p n s
  let M := p.R / (q * a)
  let v := fun ξ : Fin (batchSize p) → p.Ω => StochasticGeneralized.batchReply g y ξ
  let h := fun ξ => clip M (v ξ)
  let t := q / (64 * p.R ^ 2)
  have hq : 0 < q := confidence_pos p
  have ha : 0 < a := increment_pos p hR.le (weight_pos p hR hΔ n)
  have hM : 0 < M := by dsimp [M]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 < batchSize p := by
    have hc : p.ρ ≤ (batchSize p : ℝ) := Nat.le_ceil _
    have : 0 < (batchSize p : ℝ) := by linarith
    exact_mod_cast this
  have hvm : Measurable v := (measurable_batch p hg.measurable).comp
    (measurable_const.prodMk measurable_id)
  have hvi := LightTail.finite_mean_integral (hg.integrable y) (batchSize p) hb
  have hvc := batch_centered_moment p hρ μ hg y
  have hvr := raw_moment_of_centered hvm (gradient f y) hvc.1 hvc.2
  have hvmean : (∫ ξ, v ξ ∂Measure.pi (fun _ : Fin (batchSize p) => μ)) = gradient f y :=
    hvi.2.trans (hg.unbiased y)
  have hhm := (measurable_clip M).comp hvm
  have hhc := clipped_raw_moments hvm hvi.1 hvr.1 hvmean hM hvr.2
  have hhb : ‖(∫ ξ, h ξ ∂Measure.pi (fun _ : Fin (batchSize p) => μ)) - gradient f y‖ ≤
      4 * q * a * ‖gradient f y‖ ^ 2 / p.R := by
    have hh := hhc.2.2.1
    change _ ≤ (4 * ‖gradient f y‖ ^ 2) / (p.R / (q * a)) at hh
    convert hh using 1; field_simp
  have hvb := energy_small_bounds p hR hΔ hmin n s hV
  have hl := query_local_bounds p hR hΔ h0 h1 hconv hmin hmodel n s.1 s.2 hvb.2 hvb.1
  have hclip (ξ) : q * a * ‖h ξ‖ ≤ p.R := by
    have hh := norm_clip_le hM.le (v ξ)
    change ‖h ξ‖ ≤ p.R / (q * a) at hh
    have := (le_div_iff₀ (mul_pos hq ha)).mp hh
    nlinarith only [this]
  have hexp := clipped_exponential_step hhm hhc.1 hhc.2.1 ha.le hR (confidence_ge_one p)
    hvb.2 hhb hhc.2.2.2 hl.2.2 hclip
  let U := fun ξ => energyIncrement q a (gradient f y) (s.2 - u) (h ξ)
  let W := fun ξ => Real.exp (t * energy p f u (n + 1) (step p n s (v ξ)))
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hgrad x).differentiableAt.continuousAt)).measurable
  have hW : Measurable W := by
    have hs : Measurable (fun ξ => step p n s (v ξ)) :=
      (measurable_step p n).comp (measurable_const.prodMk hvm)
    exact Real.measurable_exp.comp (((measurable_energy p hf u).comp
      (measurable_const.prodMk hs)).const_mul t)
  have hupper (ξ) : W ξ ≤ Real.exp (t * energy p f u n s) * Real.exp (t * U ξ) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left
      (step_energy_le p hR hΔ h0 h1 hconv hgrad hmin hmodel n s (v ξ) hV) ht
    change t * energy p f u (n + 1) (step p n s (v ξ)) ≤ _
    change t * energy p f u (n + 1) (step p n s (v ξ)) ≤ t * (energy p f u n s + U ξ) at hh
    linarith
  have hWi : Integrable W (Measure.pi fun _ : Fin (batchSize p) => μ) :=
    (hexp.1.const_mul (Real.exp (t * energy p f u n s))).mono' hW.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hupper ξ)
  refine ⟨hWi, ?_⟩
  have hh := integral_mono hWi (hexp.1.const_mul (Real.exp (t * energy p f u n s))) hupper
  rw [integral_const_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left hexp.2 (Real.exp_pos (t * energy p f u n s)).le
  simp only [mul_one] at hh'
  exact hh.trans hh'

end OracleTemplate.GapStrongGrowth
