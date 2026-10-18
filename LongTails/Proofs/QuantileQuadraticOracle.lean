import LongTails.Proofs.QuantileShellOracle
import LongTails.Proofs.AdaptiveIID

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.QuantileQuadraticOracle

open LongTails.Setups.QuantileSymmetricRemainderConvex
open QuantileOracleLowerBound QuantileShellOracle

noncomputable def ones (d : ℕ) : Space d := WithLp.toLp 2 (fun _ => 1)

lemma ones_apply (d : ℕ) (i : Fin d) : ones d i = 1 := rfl

lemma ones_norm (d : ℕ) : ‖ones d‖ = Real.sqrt d := by
  have hs : ‖ones d‖ ^ 2 = (d : ℝ) := by
    simp [PiLp.norm_sq_eq_of_L2, ones_apply]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

noncomputable def center (d : ℕ) (R : ℝ) : Space d := (R / Real.sqrt d) • ones d

lemma center_norm {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) : ‖center d R‖ = R := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  rw [center, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR hs.le), ones_norm]
  exact div_mul_cancel₀ _ hs.ne'

lemma scaled_center {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) (h : ℝ) :
    (h * Real.sqrt d / R) • center d R = h • ones d := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [center, smul_smul]
  congr 1
  field_simp

noncomputable def answer (d : ℕ) (lam : ℝ) (x : Space d) (ω : ℝ) : Space d :=
  lam • x - ω • ones d

lemma measurable_answer (d : ℕ) (lam : ℝ) : Measurable (Function.uncurry (answer d lam)) := by
  unfold answer Function.uncurry
  fun_prop

lemma positive_error {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) (h : ℝ)
    (x : Space d) (ω : ℝ) (i : Fin d) :
    (answer d (h * Real.sqrt d / R) x ω -
      gradient (centeredQuadratic (h * Real.sqrt d / R) (center d R)) x) i = h - ω := by
  rw [(centeredQuadratic_gradient _ _ _).gradient, answer, smul_sub, scaled_center hd hR h]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, ones_apply, mul_one]
  ring

lemma negative_error {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) (h : ℝ)
    (x : Space d) (ω : ℝ) (i : Fin d) :
    (answer d (h * Real.sqrt d / R) x ω -
      gradient (centeredQuadratic (h * Real.sqrt d / R) (-center d R)) x) i = -h - ω := by
  rw [(centeredQuadratic_gradient _ _ _).gradient, answer, smul_sub, smul_neg, scaled_center hd hR h]
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, ones_apply, mul_one]
  ring

lemma minimizer_value {d : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (c u : Space d)
    (hu : IsMinOn (centeredQuadratic lam c) Set.univ u) : centeredQuadratic lam c u = 0 := by
  have hupper : centeredQuadratic lam c u ≤ 0 := by
    have hb := hu (show c ∈ Set.univ from Set.mem_univ _)
    change centeredQuadratic lam c u ≤ centeredQuadratic lam c c at hb
    simpa only [centeredQuadratic, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero] using hb
  have hlower : 0 ≤ centeredQuadratic lam c u := by unfold centeredQuadratic; positivity
  exact le_antisymm hupper hlower

noncomputable def params (d : ℕ) (L R r M ε : ℝ) : Params where
  d := d
  Ω := ℝ
  x0 := 0
  L := L
  R := R
  r := r
  M := M
  ε := ε

noncomputable def oracle (d : ℕ) (lam : ℝ) (p : ProbabilityMeasure ℝ) :
    OracleTemplate.Oracle (Space d) (Space d) where
  Seed := fun _ => ℝ
  law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure ℝ)), inferInstance⟩
  answer := fun _ (_, x) ω => answer d lam x ω

lemma quadratic_admissible (d : ℕ) (L R r M ε lam : ℝ) (c : Space d)
    (p : ProbabilityMeasure ℝ) (hlam : 0 ≤ lam) (hL : lam ≤ L) (hc : ‖c‖ ≤ R)
    (hnoise : ∀ x i, NoiseCondition
      ((p : Measure ℝ).map (fun ω => (answer d lam x ω - lam • (x - c)) i)) r M) :
    spec.admissible (params d L R r M ε) (centeredQuadratic lam c) (oracle d lam p) := by
  let P : ProbabilityMeasure (ℕ → ℝ) :=
    ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure ℝ)), inferInstance⟩
  refine ⟨answer d lam, p, P,
    OracleTemplate.StochasticGeneralized.infinitePi_iid (p : Measure ℝ), rfl,
    centeredQuadratic_convex hlam c, ?_, ?_, ?_, measurable_answer d lam, ?_⟩
  · intro x
    change HasGradientAt (centeredQuadratic lam c) (gradient (centeredQuadratic lam c) x) x
    rw [(centeredQuadratic_gradient lam c x).gradient]
    exact centeredQuadratic_gradient lam c x
  · exact centeredQuadratic_lipschitz hlam hL c
  · refine ⟨c, centeredQuadratic_min hlam c, ?_⟩
    change ‖(0 : Space d) - c‖ ≤ R
    simpa only [zero_sub, norm_neg] using hc
  · intro x i
    change NoiseCondition ((p : Measure ℝ).map (fun ω => (answer d lam x ω - gradient (centeredQuadratic lam c) x) i)) r M
    rw [(centeredQuadratic_gradient lam c x).gradient]
    exact hnoise x i

lemma positive_admissible {d : ℕ} (hd : 0 < d) {L R r M ε h : ℝ}
    (hR : 0 < R) (hh : 0 ≤ h) (hL : h * Real.sqrt d / R ≤ L)
    (p : ProbabilityMeasure ℝ)
    (hnoise : NoiseCondition ((p : Measure ℝ).map (fun ω => h - ω)) r M) :
    spec.admissible (params d L R r M ε)
      (centeredQuadratic (h * Real.sqrt d / R) (center d R))
      (oracle d (h * Real.sqrt d / R) p) := by
  apply quadratic_admissible _ _ _ _ _ _ _ _ p (by positivity) hL (le_of_eq (center_norm hd hR.le))
  intro x i
  have he (ω : ℝ) : (answer d (h * Real.sqrt d / R) x ω -
      (h * Real.sqrt d / R) • (x - center d R)) i = h - ω := by
    rw [← (centeredQuadratic_gradient _ _ _).gradient]
    exact positive_error hd hR h x ω i
  simpa only [he] using hnoise

lemma negative_admissible {d : ℕ} (hd : 0 < d) {L R r M ε h : ℝ}
    (hR : 0 < R) (hh : 0 ≤ h) (hL : h * Real.sqrt d / R ≤ L)
    (p : ProbabilityMeasure ℝ)
    (hnoise : NoiseCondition ((p : Measure ℝ).map (fun ω => -h - ω)) r M) :
    spec.admissible (params d L R r M ε)
      (centeredQuadratic (h * Real.sqrt d / R) (-center d R))
      (oracle d (h * Real.sqrt d / R) p) := by
  apply quadratic_admissible _ _ _ _ _ _ _ _ p (by positivity) hL
    (by rw [norm_neg, center_norm hd hR.le])
  intro x i
  have he (ω : ℝ) : (answer d (h * Real.sqrt d / R) x ω -
      (h * Real.sqrt d / R) • (x - -center d R)) i = -h - ω := by
    rw [← (centeredQuadratic_gradient _ _ _).gradient]
    exact negative_error hd hR h x ω i
  simpa only [he] using hnoise

end LongTails.Proofs.QuantileQuadraticOracle
