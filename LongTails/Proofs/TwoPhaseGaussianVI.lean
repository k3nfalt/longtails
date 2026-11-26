import LongTails.Proofs.TwoPhaseGaussianVIStep
import LongTails.Proofs.TwoPhaseGaussianVITrace

open MeasureTheory
namespace OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
open LongTails.Setups.GaussianVariationalInference
variable {d : ℕ} {L μ : ℝ} {V : Point d → ℝ}

private lemma integrate_cons {n : ℕ} {f : (Fin (n+1) → Fin d → ℝ) → ℝ}
    (hf : Measurable f) (hn : ∀ ξ, 0 ≤ f ξ) {B : (Fin d → ℝ) → ℝ}
    (hB : Integrable B (noiseLaw d))
    (hs : ∀ v, Integrable (fun ξ => f (Fin.cons v ξ)) (Measure.pi fun _ => noiseLaw d))
    (hb : ∀ v, ∫ ξ, f (Fin.cons v ξ) ∂Measure.pi (fun _ => noiseLaw d) ≤ B v) :
    Integrable f (Measure.pi fun _ => noiseLaw d) ∧
      ∫ ξ, f ξ ∂Measure.pi (fun _ => noiseLaw d) ≤ ∫ v, B v ∂noiseLaw d := by
  let q := Measure.pi (fun _ : Fin n => noiseLaw d)
  have mp := StochasticGradient.cons_measurePreserving (noiseLaw d) n
  let F := fun w : (Fin d → ℝ) × (Fin n → Fin d → ℝ) => f (Fin.cons w.1 w.2)
  have fm : Measurable F := hf.comp mp.measurable
  have fi : Integrable F ((noiseLaw d).prod q) := by
    apply (integrable_prod_iff fm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hs, hB.mono' fm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (ae_of_all _ fun v => ?_)⟩
    simp only [F, Real.norm_eq_abs, abs_of_nonneg (hn _)]
    rw [abs_of_nonneg (integral_nonneg (μ := q) (f := fun ξ => f (Fin.cons v ξ)) fun ξ => hn _)]
    exact hb v
  refine ⟨(mp.integrable_comp hf.aestronglyMeasurable).mp fi, ?_⟩
  calc _ = ∫ w, F w ∂(noiseLaw d).prod q := by
          rw [← mp.map_eq, integral_map mp.measurable.aemeasurable hf.aestronglyMeasurable]
       _ = _ := integral_prod F fi
       _ ≤ _ := integral_mono fi.integral_prod_left hB hb

lemma averaged_bound (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (ho : IsOptimal V ms Cs) {K : ℕ} (hK : 0 < K) (t : ℕ) (z : Location d × Scale d)
    (hz : IsCholesky z.2) :
    let a := offset L μ d
    let η := stepSize μ a 0
    let ρ := 1 - η*μ
    let floor := d / (2*μ)
    let W := wmass a 0 K
    let c := 2/W * (μ/4*a^2)
    let b := 2/W * (4*K*noiseConst L μ d/μ)
    let f := fun ξ => gap V ms Cs (averaged V μ a K t z ξ)
    Integrable f (Measure.pi fun _ => noiseLaw d) ∧
      ∫ ξ, f ξ ∂Measure.pi (fun _ => noiseLaw d) ≤
        c * (ρ^t * (energy V ms Cs η z - floor) + floor) + b := by
  intro a η ρ floor W c b f
  have hc := constants h
  have hm := h.pos
  have ha : 2 ≤ a := hc.offset_ge
  have he : 0 < η := hc.step_pos
  have hid : η * (μ*a) = 2 := hc.identity
  have hW : 0 < W := wmass_pos ha 0 hK
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    nlinarith [mul_nonneg (mul_nonneg he.le hm.le) (show 0 ≤ a-2 by linarith)]
  have hcoef : 0 ≤ c := by dsimp [c]; positivity
  have hf : Measurable f := (measurable_gap h ms Cs).comp
    ((measurable_averaged h a K t).of_uncurry_left)
  have hn ξ : 0 ≤ f ξ := sub_nonneg.mpr (ho.2 _ _ (averaged_cholesky h ha hK t z hz ξ))
  induction t generalizing z with
  | zero =>
    let P := pot V ms Cs μ a 0 K z
    have hp := pot_bound h ho K 0 z hz
    have hi : Integrable P (Measure.pi fun _ => noiseLaw d) := hp.1
    have hd ξ : f ξ ≤ (2/W)*P ξ := (avg_bound h ms Cs ha K hK 0 z ξ hz).2.trans_eq (by ring)
    have hfi := (hi.const_mul (2/W)).mono' hf.aestronglyMeasurable (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn ξ)]; exact hd ξ)
    refine ⟨hfi, ?_⟩
    have hi' := integral_mono hfi (hi.const_mul (2/W)) hd
    rw [integral_const_mul] at hi'
    have hr := sqd_nonneg z (ms,Cs)
    have hD := (mul_nonneg (half_pos hm).le (sqDist_nonneg z.1 ms z.2 Cs)).trans
      (bregmanMean_lower h z.1 (isLower_sub hz.1 ho.1.1))
    have h1 : μ/4*((a-1)*(a-2)) ≤ μ/4*a^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have h2 : 8*smoothConst L μ d/μ ≤ a := by
      change 8*smoothConst L μ d/μ ≤ 16*smoothConst L μ d/μ+2
      nlinarith [div_nonneg hc.nonneg hm.le, show 8*smoothConst L μ d/μ =
        8*(smoothConst L μ d/μ) by ring, show 16*smoothConst L μ d/μ =
        16*(smoothConst L μ d/μ) by ring]
    have h3 : μ/4*a^2*(2*η) = a := by linear_combination a/2 * hid
    have hp' := hp.2
    change (∫ ξ, P ξ ∂Measure.pi (fun _ => noiseLaw d)) ≤
      μ/4*((((0:ℕ):ℝ)+a-1)*(((0:ℕ):ℝ)+a-2))*sqd z (ms,Cs) +
      8*smoothConst L μ d/μ*bregmanMean V ms Cs z.1 z.2+4*K*noiseConst L μ d/μ at hp'
    simp only [Nat.cast_zero, zero_add] at hp'
    have hraw : (∫ ξ, P ξ ∂Measure.pi (fun _ => noiseLaw d)) ≤
        μ/4*a^2*energy V ms Cs η z+4*K*noiseConst L μ d/μ := by
      unfold energy
      nlinarith [mul_le_mul_of_nonneg_right h1 hr, mul_le_mul_of_nonneg_right h2 hD,
        congrArg (· * bregmanMean V ms Cs z.1 z.2) h3]
    apply le_trans hi'
    refine (mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 2/W)).trans_eq ?_
    dsimp only [b,c]; ring
  | succ t ih =>
    let p := stepAt V μ a 0 z
    let Q := fun v => energy V ms Cs η (p v)
    have hw := warm_step h ho z hz
    have hi : Integrable Q (noiseLaw d) := hw.1
    let B := fun v => (c*ρ^t)*Q v + (c*(floor-ρ^t*floor)+b)
    have hB : Integrable B (noiseLaw d) := (hi.const_mul _).addL (integrable_const _)
    have sec v := ih (p v) (stepAt_cholesky h.pos ha 0 hz v)
      ((measurable_gap h ms Cs).comp (measurable_averaged h a K t).of_uncurry_left)
      (fun ξ => sub_nonneg.mpr (ho.2 _ _ (averaged_cholesky h ha hK t _
        (stepAt_cholesky h.pos ha 0 hz v) ξ)))
    have eqf v : (fun ξ => f (Fin.cons v ξ)) =
        fun ξ => gap V ms Cs (averaged V μ a K t (p v) ξ) := by
      funext ξ
      simp [f, averaged, p]
    have result := integrate_cons hf hn hB (fun v => by rw [eqf]; exact (sec v).1) (fun v => by
      rw [eqf]; exact (sec v).2.trans_eq (by dsimp [B,Q]; ring))
    refine ⟨result.1, result.2.trans ?_⟩
    change (∫ v, (c*ρ^t)*Q v + _ ∂noiseLaw d) ≤ _
    rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    have hh : (∫ v, Q v ∂noiseLaw d) ≤ ρ*energy V ms Cs η z + (1-ρ)*floor := by
      simpa only [ρ, sub_sub_cancel] using hw.2
    have := mul_le_mul_of_nonneg_left hh (show 0 ≤ c*ρ^t by positivity)
    rw [pow_succ]
    linarith only [this]

end OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
