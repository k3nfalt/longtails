import LongTails.Proofs.GatedEscapePancake
import LongTails.Proofs.GatedEscapeGaussian
import Mathlib.MeasureTheory.Integral.Pi

namespace LongTails.Proofs.GatedEscapeSlice

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Proofs.ComparisonTrustTaylor LongTails.Proofs.GatedEscapePancake

section majority

variable {Y : Type*} [MeasurableSpace Y]

theorem majority_bound (μ : Measure Y) [IsProbabilityMeasure μ] (bad : Y → Prop) [DecidablePred bad]
    (hbad : MeasurableSet {y | bad y})
    (hμ : (∫ y, (if bad y then (1 : ℝ) else 0) ∂μ) ≤ 1 / 16) (M : ℕ) :
    ∫ ω, (if M ≤ 2 * (Finset.univ.filter (fun c : Fin M => bad (ω c))).card then (1 : ℝ) else 0)
      ∂(Measure.pi fun _ : Fin M => μ) ≤ (19 / 32) ^ M := by
  set F : Y → ℝ := fun y => if bad y then 4 else 1 with hF
  have hFm : Measurable F := Measurable.ite hbad measurable_const measurable_const
  have hprod : ∀ ω : Fin M → Y, ∏ c, F (ω c) =
      (4 : ℝ) ^ (Finset.univ.filter (fun c : Fin M => bad (ω c))).card := by
    intro ω
    simp only [hF]
    rw [Finset.prod_ite]
    simp
  have hpt : ∀ ω : Fin M → Y,
      (if M ≤ 2 * (Finset.univ.filter (fun c : Fin M => bad (ω c))).card then (1 : ℝ) else 0) ≤
        (∏ c, F (ω c)) / 2 ^ M := by
    intro ω
    rw [hprod]
    split_ifs with h
    · rw [le_div_iff₀ (by positivity), one_mul]
      calc (2 : ℝ) ^ M ≤ 2 ^ (2 * (Finset.univ.filter (fun c : Fin M => bad (ω c))).card) :=
            pow_le_pow_right₀ (by norm_num) h
        _ = 4 ^ (Finset.univ.filter (fun c : Fin M => bad (ω c))).card := by
            rw [pow_mul]; norm_num
    · positivity
  have hIntF : Integrable (fun ω : Fin M → Y => (∏ c, F (ω c)) / 2 ^ M) (Measure.pi fun _ : Fin M => μ) := by
    refine (Integrable.of_bound (C := 4 ^ M / 2 ^ M) ?_ ?_)
    · exact (Finset.measurable_prod _ (fun c _ => hFm.comp (measurable_pi_apply c))).div_const _
        |>.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [hprod, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      · norm_num
      · exact (Finset.card_filter_le _ _).trans (by simp)
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num)
    hIntF (Filter.Eventually.of_forall hpt)
  refine hle.trans ?_
  rw [integral_div, integral_fintype_prod_eq_pow F]
  have hEF : ∫ y, F y ∂μ ≤ 19 / 16 := by
    have hrw : F = fun y => 1 + 3 * (if bad y then (1 : ℝ) else 0) := by
      funext y; simp only [hF]; split_ifs <;> norm_num
    have hi : Integrable (fun y => (if bad y then (1 : ℝ) else 0)) μ := by
      refine Integrable.of_bound (C := 1) (Measurable.ite hbad measurable_const measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      split_ifs <;> norm_num
    rw [hrw, integral_add (integrable_const _) (hi.const_mul 3), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    linarith
  have hEF0 : 0 ≤ ∫ y, F y ∂μ := integral_nonneg fun y => by simp only [hF]; split_ifs <;> norm_num
  calc (∫ y, F y ∂μ) ^ Fintype.card (Fin M) / 2 ^ M ≤ (19 / 16) ^ M / 2 ^ M := by
        rw [Fintype.card_fin]; gcongr
    _ = (19 / 32) ^ M := by rw [← div_pow]; norm_num

end majority

section orbitdef

variable {E : Type*}

def orbit (Φ : E → E) : ℕ → E → E
  | 0, v => v
  | t + 1, v => Φ (orbit Φ t v)

lemma orbit_succ (Φ : E → E) (t : ℕ) (v : E) : orbit Φ (t + 1) v = Φ (orbit Φ t v) := rfl

lemma orbit_continuous [TopologicalSpace E] {Φ : E → E} (hΦ : Continuous Φ) :
    ∀ t, Continuous (orbit Φ t) := by
  intro t
  induction t with
  | zero => exact continuous_id
  | succ t ih => exact hΦ.comp ih

end orbitdef

section slice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem slice_bound {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) (hρ : 0 ≤ ρ) (x g0 : E)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, fderiv ℝ (gradient f) x v⟫ = eig i * ⟪b i, v⟫)
    (j0 : ι) {η R ζ γ' c : ℝ} {Tn : ℕ} (hj0 : eig j0 = -γ')
    (ha : ∀ i, |1 - η * eig i| ≤ 1 + η * γ') (hη : 0 < η) (hRζ : ρ * R ≤ ζ) (hζ : 0 ≤ ζ)
    (hgap : 2 * (η * ζ) ≤ η * γ') (hsmall : 8 * (η * ζ) * Tn ≤ 1) (hc0 : 0 < c)
    (u : E) (a a' : ℝ)
    (h1 : ∀ t ≤ Tn, ‖orbit (fun w => w - η • (gradient f (x + w) - g0)) t (c • (u + a • b j0))‖ ≤ R)
    (h2 : ∀ t ≤ Tn, ‖orbit (fun w => w - η • (gradient f (x + w) - g0)) t (c • (u + a' • b j0))‖ ≤ R) :
    |a - a'| * (c * (1 + η * γ' - 2 * (η * ζ)) ^ Tn) ≤ 2 * R := by
  set Φ := fun w => w - η • (gradient f (x + w) - g0) with hΦ
  have key : ∀ a a' : ℝ, a ≤ a' →
      (∀ t ≤ Tn, ‖orbit Φ t (c • (u + a • b j0))‖ ≤ R) →
      (∀ t ≤ Tn, ‖orbit Φ t (c • (u + a' • b j0))‖ ≤ R) →
      (a' - a) * (c * (1 + η * γ' - 2 * (η * ζ)) ^ Tn) ≤ 2 * R := by
    intro a a' hle k1 k2
    have hp := pancake h hρ x g0 b eig hc j0 hj0 ha hη hRζ hζ hgap hsmall
      (fun t => orbit Φ t (c • (u + a • b j0))) (fun t => orbit Φ t (c • (u + a' • b j0)))
      (fun t => orbit_succ Φ t _) (fun t => orbit_succ Φ t _)
      (θ := c * (a' - a)) (by simp only [orbit]; module)
      (mul_nonneg hc0.le (by linarith)) (fun t ht => ⟨k1 t ht, k2 t ht⟩)
    linarith [hp]
  rcases le_total a a' with hle | hle
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact key a a' hle h1 h2
  · rw [abs_of_nonneg (by linarith)]; exact key a' a hle h2 h1

theorem bad_measure {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) (hρ : 0 ≤ ρ) (x g0 : E) {n : ℕ}
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) (eig : Fin (n + 1) → ℝ)
    (hc : ∀ i v, ⟪b i, fderiv ℝ (gradient f) x v⟫ = eig i * ⟪b i, v⟫)
    (j0 : Fin (n + 1)) {η R ζ γ' c : ℝ} {Tn : ℕ} (hj0 : eig j0 = -γ')
    (ha : ∀ i, |1 - η * eig i| ≤ 1 + η * γ') (hη : 0 < η) (hRζ : ρ * R ≤ ζ) (hζ : 0 ≤ ζ)
    (hgap : 2 * (η * ζ) ≤ η * γ') (hsmall : 8 * (η * ζ) * Tn ≤ 1) (hc0 : 0 < c) :
    stdGaussian E {z | ∀ t ≤ Tn, ‖orbit (fun w => w - η • (gradient f (x + w) - g0)) t (c • z)‖ ≤ R}
      ≤ ENNReal.ofReal (R / (c * (1 + η * γ' - 2 * (η * ζ)) ^ Tn)) := by
  have hq : 1 ≤ 1 + η * γ' - 2 * (η * ζ) := by linarith
  have hqpos : 0 < c * (1 + η * γ' - 2 * (η * ζ)) ^ Tn := mul_pos hc0 (pow_pos (by linarith) _)
  have hΦc : Continuous (fun w : E => w - η • (gradient f (x + w) - g0)) := by
    have hgc : Continuous (gradient f) :=
      LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
        rw [dist_eq_norm, dist_eq_norm]
        exact (h.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
    exact continuous_id.sub ((hgc.comp (continuous_const.add continuous_id)).sub continuous_const |>.const_smul η)
  have hmeas : MeasurableSet
      {z : E | ∀ t ≤ Tn, ‖orbit (fun w => w - η • (gradient f (x + w) - g0)) t (c • z)‖ ≤ R} := by
    have : {z : E | ∀ t ≤ Tn, ‖orbit (fun w => w - η • (gradient f (x + w) - g0)) t (c • z)‖ ≤ R} =
        ⋂ t ∈ Finset.range (Tn + 1),
          {z : E | ‖orbit (fun w => w - η • (gradient f (x + w) - g0)) t (c • z)‖ ≤ R} := by
      ext z; simp
    rw [this]
    refine Finset.measurableSet_biInter _ (fun t _ => ?_)
    exact measurableSet_le (((orbit_continuous hΦc t).comp (continuous_const_smul c)).norm.measurable)
      measurable_const
  have hsl := LongTails.Proofs.GatedEscapeGaussian.gauss_slice b j0 _ hmeas
    (D := 2 * R / (c * (1 + η * γ' - 2 * (η * ζ)) ^ Tn)) (fun u a a' k1 k2 => by
    have hsb := slice_bound h hρ x g0 b eig hc j0 hj0 ha hη hRζ hζ hgap hsmall hc0 u a a' k1 k2
    rw [le_div_iff₀ hqpos]; exact hsb)
  refine hsl.trans (le_of_eq ?_)
  congr 1; ring

end slice

end LongTails.Proofs.GatedEscapeSlice
