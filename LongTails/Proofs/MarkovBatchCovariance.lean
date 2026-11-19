import LongTails.Proofs.HeavyTailedMarkovLaw
import LongTails.Proofs.AcceleratedMarkovRun
import LongTails.Proofs.AcceleratedMarkovEnergy

open MeasureTheory ProbabilityTheory Function Preorder

namespace LongTails.Proofs.MarkovWeightedComparison

open Setups.HeavyTailedMarkovSmoothAndConvex
open OracleTemplate.HeavyTailedMarkovGradient

variable {Ω : Type} [MeasurableSpace Ω]

lemma mixing_representative (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (t : ℕ) (hd : Integrable (mixingDistance κ π t) (π : Measure Ω)) :
    ∃ u : Ω → ℝ, Measurable u ∧ (∀ z, 0 ≤ u z ∧ u z ≤ 1) ∧
      u =ᵐ[(π : Measure Ω)] mixingDistance κ π t := by
  let m := hd.aestronglyMeasurable
  refine ⟨fun z => max 0 (min 1 (m.mk _ z)), measurable_const.max
    (measurable_const.min m.stronglyMeasurable_mk.measurable), fun z =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, ?_⟩
  filter_upwards [m.ae_eq_mk] with z hz
  rw [← hz, min_eq_right (mixingDistance_le_one κ π t z),
    max_eq_right (mixingDistance_nonneg κ π t z)]

lemma weighted_comparison (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω)) (s h : ℕ)
    (u : Ω → ℝ) (hu : Measurable u) (hub : ∀ z, 0 ≤ u z ∧ u z ≤ 1)
    (hue : u =ᵐ[(π : Measure Ω)] mixingDistance κ π h)
    (G : (Finset.Iic s → Ω) → ℝ) (W : (Finset.Iic s → Ω) → Ω → ℝ)
    (hG : Measurable G) (hW : Measurable (Function.uncurry W)) {M : ℝ}
    (hM : ∀ a, G a ≤ M) (hb : ∀ a z, |W a z| ≤ G a) :
    let P : Measure (ℕ → Ω) := pathLaw κ π
    |(∫ ξ, W (frestrictLe s ξ) (ξ (s + h)) ∂P) -
      ∫ ξ, ∫ z, W (frestrictLe s ξ) z ∂(π : Measure Ω) ∂P| ≤
      2 * ∫ ξ, G (frestrictLe s ξ) * u (ξ s) ∂P := by
  intro P
  let last : (Finset.Iic s → Ω) → Ω := fun a => a ⟨s, Finset.mem_Iic.mpr le_rfl⟩
  let ρ := P.map (frestrictLe s)
  have hf : Measurable (frestrictLe s : (ℕ → Ω) → _) := by fun_prop
  have hl : Measurable last := measurable_pi_apply _
  have hmarg : ρ.map last = (π : Measure Ω) := by
    rw [show ρ = P.map (frestrictLe s) by rfl, Measure.map_map hl hf]
    exact pathLaw_stationary_marginal κ π hπ s
  have hmp : MeasurePreserving last ρ (π : Measure Ω) := ⟨hl, hmarg⟩
  have hae := hmp.quasiMeasurePreserving.ae_eq_comp hue
  let K := (κ ^ h).comap last hl
  let a := fun x => ∫ y, W x y ∂K x
  let b := fun x => ∫ y, W x y ∂(π : Measure Ω)
  have ha : StronglyMeasurable a := hW.stronglyMeasurable.integral_kernel_prod_right (κ := K)
  have hb' : StronglyMeasurable b := hW.stronglyMeasurable.integral_kernel_prod_right
    (κ := Kernel.const _ (π : Measure Ω))
  have hn (x) : 0 ≤ G x := by
    have : Nonempty Ω := nonempty_of_isProbabilityMeasure (π : Measure Ω)
    exact (abs_nonneg _).trans (hb x (Classical.choice ‹Nonempty Ω›))
  have hI : IsProbabilityMeasure ρ := by dsimp [ρ, P]; infer_instance
  have haI : Integrable a ρ := Integrable.of_bound ha.aestronglyMeasurable M
    (.of_forall fun x => by simpa [a] using norm_integral_le_of_norm_le_const (μ := K x) (f := W x) (.of_forall fun y => (hb x y).trans (hM x)))
  have hbI : Integrable b ρ := Integrable.of_bound hb'.aestronglyMeasurable M
    (.of_forall fun x => by simpa [b] using norm_integral_le_of_norm_le_const (μ := (π : Measure Ω)) (f := W x) (.of_forall fun y => (hb x y).trans (hM x)))
  let w := fun x => G x * u (last x)
  have hw : Measurable w := hG.mul (hu.comp hl)
  have hwi : Integrable w ρ := Integrable.of_bound hw.aestronglyMeasurable M (.of_forall fun x => by
    rw [Real.norm_of_nonneg (mul_nonneg (hn x) (hub _).1)]
    exact (mul_le_of_le_one_right (hn x) (hub _).2).trans (hM x))
  have he : ∀ᵐ x ∂ρ, ‖a x - b x‖ ≤ 2 * w x := by
    filter_upwards [hae] with x hx
    dsimp only [Function.comp_apply] at hx
    dsimp only [a, b, w, K]
    rw [Kernel.comap_apply, hx, ← mul_assoc]
    exact integral_sub_le_mixingDistance κ π h (last x) (hn x)
      (hW.comp (measurable_const.prodMk measurable_id)) (hb x)
  have hh := norm_integral_le_of_norm_le (hwi.const_mul 2) he
  rw [integral_sub haI hbI, integral_const_mul] at hh
  have hreal := pathLaw_integral_future κ π s h hW (fun x y => (hb x y).trans (hM x))
  have hbmap := integral_map hf.aemeasurable (μ := P) hb'.aestronglyMeasurable
  have hwmap := integral_map hf.aemeasurable (μ := P) hw.aestronglyMeasurable
  change |(∫ ξ, W (frestrictLe s ξ) (ξ (s + h)) ∂P) - ∫ ξ, b (frestrictLe s ξ) ∂P| ≤
    2 * ∫ ξ, w (frestrictLe s ξ) ∂P
  rw [← hbmap, ← hwmap, hreal]
  exact hh

end LongTails.Proofs.MarkovWeightedComparison

open MeasureTheory ProbabilityTheory Function Preorder

namespace LongTails.Proofs.MarkovBatchCovariance

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient

variable {Ω : Type} [MeasurableSpace Ω]

def AdaptedAt {E : Type*} (s : ℕ) (A : (ℕ → Ω) → E) : Prop :=
  ∀ ξ ζ, (∀ i ≤ s, ξ i = ζ i) → A ξ = A ζ

omit [MeasurableSpace Ω] in
lemma AdaptedAt.prefix {E : Type*} {s : ℕ} {A : (ℕ → Ω) → E} (ha : AdaptedAt s A)
    (ξ : ℕ → Ω) : A (extendHistory s (frestrictLe s ξ)) = A ξ := by
  apply ha
  intro i hi
  simp [extendHistory, frestrictLe, Nat.min_eq_left hi]

lemma prefix_covariance (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω)) (s t : ℕ)
    (hd : Integrable (mixingDistance κ π t) (π : Measure Ω)) {δ : ℝ}
    (hm : (∫ y, mixingDistance κ π t y ∂(π : Measure Ω)) ≤ δ)
    {A : (ℕ → Ω) → ℝ} (ha : Measurable A) (hp : AdaptedAt s A) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ ξ, |A ξ| ≤ c) {u : Ω → ℝ} (hu : Measurable u) (hub : ∀ z, |u z| ≤ 1) :
    let P : Measure (ℕ → Ω) := pathLaw κ π
    |(∫ ξ, A ξ * u (ξ (s+t)) ∂P) - (∫ ξ, A ξ ∂P) * ∫ z, u z ∂(π : Measure Ω)| ≤
      2 * c * δ := by
  intro P
  let F := fun a => A (extendHistory s a)
  have hF : Measurable F := ha.comp (measurable_extendHistory s)
  let W := fun a z => F a * u z
  have hW : Measurable (Function.uncurry W) := (hF.comp measurable_fst).mul (hu.comp measurable_snd)
  have hw a z : |W a z| ≤ c := by
    rw [show W a z = F a * u z by rfl, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hub z)).trans (hb _)
  have h := pathLaw_averaged_mixing_bound κ π hπ s t hd hW hc hw hm
  have he a : (∫ y, W a y ∂(π : Measure Ω)) = F a * ∫ y, u y ∂(π : Measure Ω) :=
    integral_const_mul _ _
  simp_rw [he] at h
  rw [integral_mul_const, integral_map (by fun_prop) hF.aestronglyMeasurable] at h
  simpa only [W, F, hp.prefix] using h

end LongTails.Proofs.MarkovBatchCovariance

open MeasureTheory ProbabilityTheory
namespace LongTails.Proofs.MarkovBatchMoments

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient
open MarkovBatchCovariance

variable {Ω : Type} [MeasurableSpace Ω]

lemma weighted_moment (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω)) (B h : ℕ) (hB : 0 < B)
    (hd : ∀ t, Integrable (mixingDistance κ π t) (π : Measure Ω))
    (hm : ∀ i : ℕ, (∫ z, mixingDistance κ π (i*h) z ∂(π : Measure Ω)) ≤ (1/2 : ℝ)^i)
    {G : ℕ → (ℕ → Ω) → ℝ} (hg : ∀ j, Measurable (G j))
    (hgb : ∀ j, ∃ M : ℝ, ∀ ξ, |G j ξ| ≤ M) {g0 : ℝ} (h0 : ∀ ξ, G 0 ξ = g0)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ j ξ, |G (j+1) ξ - G j ξ| ≤ c)
    (hp : ∀ j, AdaptedAt (((j+1)*B-1)*h) (fun ξ => G (j+1) ξ - G j ξ))
    {u : Ω → ℝ} (hu : Measurable u) (hub : ∀ z, |u z| ≤ 1) (j i : ℕ) :
    let P : Measure (ℕ → Ω) := pathLaw κ π
    (∫ ξ, G j ξ * u (ξ ((j*B+i-1)*h)) ∂P) ≤
      (∫ ξ, G j ξ ∂P) * (∫ z, u z ∂(π : Measure Ω)) + 4*c*(1/2 : ℝ)^i := by
  intro P
  have hgI k : Integrable (G k) P := by
    obtain ⟨M,hM⟩ := hgb k
    exact Integrable.of_bound (hg k).aestronglyMeasurable M (.of_forall hM)
  have hwI k t : Integrable (fun ξ => G k ξ * u (ξ t)) P := by
    obtain ⟨M,hM⟩ := hgb k
    refine Integrable.of_bound ((hg k).mul (hu.comp (measurable_pi_apply t))).aestronglyMeasurable M
      (.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hub _)).trans (hM _)
  induction j generalizing i with
  | zero =>
    simp_rw [h0, integral_const_mul, integral_const, probReal_univ, one_smul]
    have he (t : ℕ) : (∫ ξ, u (ξ t) ∂P) = ∫ z, u z ∂(π : Measure Ω) := by
      rw [← integral_map (measurable_pi_apply t).aemeasurable hu.aestronglyMeasurable,
        pathLaw_stationary_marginal κ π hπ]
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  | succ j ih =>
    let s := ((j+1)*B-1)*h
    let t := ((j+1)*B+i-1)*h
    have hpos : 0 < (j+1)*B := Nat.mul_pos (by omega) hB
    have he : s + i*h = t := by
      dsimp [s,t]
      rw [← Nat.add_mul]
      congr 1
      omega
    have he' : (j*B+(B+i)-1)*h = t := by simp [t, Nat.add_mul, Nat.add_assoc]
    have prev := ih (B+i)
    rw [he'] at prev
    have cov := prefix_covariance κ π hπ s (i*h) (hd _) (hm i)
      ((hg (j+1)).sub (hg j)) (hp j) hc (hb j) hu hub
    dsimp only at cov
    rw [he] at cov
    have hh := (le_abs_self _).trans cov
    change (∫ ξ, (G (j+1) ξ - G j ξ) * u (ξ t) ∂P) -
      (∫ ξ, G (j+1) ξ - G j ξ ∂P) * _ ≤ _ at hh
    simp_rw [sub_mul] at hh
    rw [integral_sub (hwI _ _) (hwI _ _), integral_sub (hgI _) (hgI _)] at hh
    have hpow : (1/2 : ℝ)^B ≤ 1/2 := by
      simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
        (show 1 ≤ B by omega)
    have scale := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ 4*c*(1/2 : ℝ)^i)
    rw [pow_add] at prev
    change (∫ ξ, G (j+1) ξ * u (ξ t) ∂P) ≤ _
    nlinarith

end LongTails.Proofs.MarkovBatchMoments
