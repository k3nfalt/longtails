import LongTails.Proofs.GatedEscapeGaussian
import LongTails.Proofs.CovarianceAcceleratedGaussian
import LongTails.Setups.SphericalRandomUtility

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace LongTails.Proofs.SphericalPreferenceGaussian

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.GatedEscapeGaussian

noncomputable def tail (t : ℝ) : ℝ := (gaussianReal 0 1).real (Ici t)

lemma tail_mem (t : ℝ) : tail t ∈ Icc 0 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

lemma tail_difference {a b : ℝ} (hab : a ≤ b) :
    0 ≤ tail a-tail b ∧ tail a-tail b ≤ (b-a)/2 := by
  have hsub : Ici b ⊆ Ici a := Ici_subset_Ici.mpr hab
  have hsplit := measureReal_sdiff (μ := gaussianReal 0 1) hsub measurableSet_Ici (measure_ne_top _ _)
  have hdiam : ∀ x ∈ Ici a \ Ici b, ∀ y ∈ Ici a \ Ici b, |x-y| ≤ b-a := by
    rintro x ⟨hx,hxb⟩ y ⟨hy,hyb⟩
    change a ≤ x at hx
    change ¬ b ≤ x at hxb
    change a ≤ y at hy
    change ¬ b ≤ y at hyb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr
    (gaussianReal_le_of_diam _ hdiam)
  rw [ENNReal.toReal_ofReal (by linarith)] at h
  exact ⟨sub_nonneg.mpr (measureReal_mono hsub), hsplit ▸ h⟩

lemma tail_lipschitz (a b : ℝ) : |tail a - tail b| ≤ |a-b|/2 := by
  rcases le_total a b with hab | hba
  · obtain ⟨h1,h2⟩ := tail_difference hab
    rwa [abs_of_nonneg h1, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
  · rw [abs_sub_comm, abs_sub_comm a b]
    obtain ⟨h1,h2⟩ := tail_difference hba
    rwa [abs_of_nonneg h1, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]

lemma tail_zero : tail 0 = 1/2 := by
  let μ := gaussianReal 0 1
  have he : μ (Iic 0) = μ (Ici 0) := by
    have hmap : μ.map Neg.neg = μ := by simpa [μ] using gaussianReal_map_neg (μ := 0) (v := 1)
    have h := Measure.map_apply (μ := μ) measurable_neg (s := Ici (0:ℝ)) measurableSet_Ici
    simpa [hmap] using h.symm
  have : NullSingletonClass μ := nullSingletonClass_gaussianReal one_ne_zero
  have hi : μ (Iio 0) = μ (Iic 0) := measure_congr (Iio_ae_eq_Iic (μ := μ))
  have hr : μ.real (Iio 0) = μ.real (Ici 0) := congrArg ENNReal.toReal (hi.trans he)
  have hrc := measureReal_compl (μ := μ) (s := Ici (0:ℝ)) measurableSet_Ici
  rw [compl_Ici, probReal_univ] at hrc
  change μ.real (Ici 0) = _
  linarith

variable {d : ℕ}
local notation "H" => Point d

noncomputable def scaled (d : ℕ) (σ : ℝ) : Measure (Point d) :=
  (stdGaussian (Point d)).map (fun z => σ • z)

instance (d : ℕ) (σ : ℝ) : IsProbabilityMeasure (scaled d σ) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

lemma scaled_spherical (σ : ℝ) : Spherical (scaled d σ) := by
  intro U
  unfold scaled
  rw [Measure.map_map U.continuous.measurable (by fun_prop)]
  have he : (U ∘ (fun z => σ • z)) = (fun z => σ • z) ∘ U := by ext z; simp
  rw [he, ← Measure.map_map (by fun_prop) U.continuous.measurable, stdGaussian_map]

lemma projected_tail (σ : ℝ) (hσ : 0 < σ) (u : H) (hu : ‖u‖ = 1) (a : ℝ) :
    (scaled d σ).real {z | a ≤ ⟪u,z⟫} = tail (a/σ) := by
  let L := InnerProductSpace.toDual ℝ H u
  have hL : HasLaw L (gaussianReal 0 1) (stdGaussian H) := by
    simpa [L, hu] using LongTails.Proofs.CovarianceAcceleratedGaussian.gaussian_dual_law L
  simp only [tail, measureReal_def, scaled]
  rw [Measure.map_apply (by fun_prop) (measurableSet_le measurable_const (by fun_prop))]
  rw [← hL.map_eq, Measure.map_apply L.continuous.measurable measurableSet_Ici]
  congr 2
  ext z
  change a ≤ ⟪u,σ • z⟫ ↔ a/σ ≤ ⟪u,z⟫
  rw [real_inner_smul_right, div_le_iff₀ hσ, mul_comm]

noncomputable def mixture (d : ℕ) (B : ℝ) : Measure (Point d) :=
  (3/4 : ℝ≥0) • scaled d (B/(8*Real.sqrt d)) + (1/4 : ℝ≥0) • scaled d (2*B)

instance (d : ℕ) (B : ℝ) : IsProbabilityMeasure (mixture d B) where
  measure_univ := by
    simp only [mixture,Measure.add_apply,Measure.smul_apply,measure_univ,ENNReal.smul_def,
      smul_eq_mul,mul_one]
    norm_cast
    norm_num

lemma mixture_real (B : ℝ) (s : Set H) :
    (mixture d B).real s = (3/4)*(scaled d (B/(8*Real.sqrt d))).real s +
      (1/4)*(scaled d (2*B)).real s := by
  rw [mixture, measureReal_add_apply]
  simp [measureReal_def,Measure.smul_apply,ENNReal.smul_def]

lemma mixture_spherical (B : ℝ) : Spherical (mixture d B) := by
  intro U
  rw [mixture,Measure.map_add _ _ U.continuous.measurable,Measure.map_smul,Measure.map_smul,
    scaled_spherical _ U,scaled_spherical _ U] <;> exact U.continuous.measurable.aemeasurable

noncomputable def link (d : ℕ) (B a : ℝ) : ℝ :=
  3/4*tail (a/(B/(8*Real.sqrt d))) + 1/4*tail (a/(2*B))

lemma link_eq [NeZero d] {B : ℝ} (hB : 0 < B) (u : H) (hu : ‖u‖ = 1) (a : ℝ) :
    (mixture d B).real {z | a ≤ ⟪u,z⟫} = link d B a := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  rw [mixture_real,projected_tail _ (by positivity) _ hu,projected_tail _ (by positivity) _ hu]
  rfl

lemma link_interior (d : ℕ) {B a : ℝ} (hB : 0 < B) (ha : |a| ≤ B/2) :
    link d B a ∈ Icc (1/16) (1-1/16) := by
  have hab := tail_lipschitz (a/(2*B)) 0
  rw [tail_zero,sub_zero,abs_div,abs_of_pos (show 0 < 2*B by positivity)] at hab
  have hratio : |a|/(2*B) ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨hl,hu⟩ := abs_le.mp hab
  have hx := tail_mem (a/(B/(8*Real.sqrt d)))
  unfold link
  constructor <;> linarith only [hl,hu,hratio,hx.1,hx.2]

lemma link_modulus {d : ℕ} [NeZero d] {B : ℝ} (hB : 0 < B) (a b : ℝ) :
    |link d B a-link d B b| ≤ 4*Real.sqrt d/B*|a-b| := by
  have hd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast NeZero.pos d)
  have hs : 0 < B/(8*Real.sqrt d) := by positivity
  have hw : 0 < 2*B := by positivity
  have hf (c : ℝ) (hc : 0 < c) : |tail (a/c)-tail (b/c)| ≤ |a-b|/c/2 := by
    simpa only [← sub_div,abs_div,abs_of_pos hc] using tail_lipschitz (a/c) (b/c)
  unfold link
  rw [show ∀ x y z w : ℝ, 3/4*x+1/4*y-(3/4*z+1/4*w) = 3/4*(x-z)+1/4*(y-w) by intros; ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/4), abs_of_pos (by norm_num : (0:ℝ)<1/4)]
  apply (add_le_add (mul_le_mul_of_nonneg_left (hf _ hs) (by norm_num))
    (mul_le_mul_of_nonneg_left (hf _ hw) (by norm_num))).trans
  have hs' : Real.sqrt d ≠ 0 := by linarith
  field_simp [hB.ne',hs']
  nlinarith only [mul_le_mul_of_nonneg_right hd (abs_nonneg (a-b)), abs_nonneg (a-b)]

end LongTails.Proofs.SphericalPreferenceGaussian
