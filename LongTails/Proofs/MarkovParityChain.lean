import LongTails.Proofs.MarkovParityProgress
import LongTails.Proofs.FiniteMarkovLaw
import LongTails.Proofs.PolynomialMixingLowerBound

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.MarkovParityChain

open MarkovParityProgress PolynomialMixingLowerBound OracleTemplate.MarkovProduct
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

instance colorMeasurable : MeasurableSpace Color := ⊤
instance colorDiscrete : DiscreteMeasurableSpace Color := ⟨fun _ => trivial⟩

def weight (q : ℝ) : Color → ℝ
  | none => 1 - 2 * q
  | some _ => q

lemma weight_nonneg {q : ℝ} (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) (z : Color) : 0 ≤ weight q z := by
  cases z <;> simp [weight, hq, hq']

lemma weight_total (q : ℝ) : ∑ z : Color, weight q z = 1 := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  simp [weight]
  ring

noncomputable def colorLaw (q : ℝ) (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) : ProbabilityMeasure Color :=
  let K := finiteWeightKernel (fun (_ : Color) z => weight q z)
  letI : IsMarkovKernel K := finiteWeightKernel_markov _ (fun _ => weight_nonneg hq hq')
    (fun _ => weight_total q)
  ⟨K none, inferInstance⟩

lemma colorLaw_real (q : ℝ) (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) (z : Color) :
    (colorLaw q hq hq' : Measure Color).real {z} = weight q z :=
  finiteWeightKernel_real (fun (_ : Color) y => weight q y) (fun _ => weight_nonneg hq hq') _ z

lemma refresh_mixing {Z : Type} [MeasurableSpace Z] (π : ProbabilityMeasure Z) (r : unitInterval)
    (t : ℕ) (z : Z) :
    mixingDistance (refreshKernel π r) π t z ≤ Real.exp (-(r : ℝ) * t) := by
  apply ciSup_le
  intro s
  change |((refreshKernel π r ^ t) z).real s.val - (π : Measure Z).real s.val| ≤ _
  rw [refreshKernel_pow_deviation]
  have hle (μ : ProbabilityMeasure Z) : (μ : Measure Z).real s.val ≤ 1 :=
    (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq probReal_univ
  have h1 := hle ⟨Measure.dirac z, inferInstance⟩
  have h2 := hle π
  change (Measure.dirac z).real s.val ≤ 1 at h1
  have hab : |(Measure.dirac z).real s.val - (π : Measure Z).real s.val| ≤ 1 :=
    abs_le.mpr ⟨by linarith [measureReal_nonneg (μ := Measure.dirac z) (s := s.val)],
      by linarith [measureReal_nonneg (μ := (π : Measure Z)) (s := s.val)]⟩
  exact (mul_le_of_le_one_right (pow_nonneg (sub_nonneg.mpr r.2.2) _) hab).trans
    (refresh_decay_le_exponential r t)

def entryCost (a b : Color) : ℝ := if b.isSome && a != b then 1 else 0

lemma entryCost_bound (a b : Color) : |entryCost a b| ≤ 1 := by
  unfold entryCost
  split <;> norm_num

lemma next_entry_bound (q : ℝ) (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) (r : unitInterval)
    (a : Color) :
    ∫ b, entryCost a b ∂refreshKernel (colorLaw q hq hq') r a ≤ 2 * r * q := by
  rw [finite_integral, Fintype.sum_option, Fintype.sum_bool]
  have hweight (b : Color) :
      (refreshKernel (colorLaw q hq hq') r a).real {b} =
        (1 - (r : ℝ)) * (if a = b then 1 else 0) + r * weight q b := by
    change (_ + _ : Measure Color).real _ = _
    rw [measureReal_add_apply, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply,
      colorLaw_real]
    by_cases he : a = b <;> simp [he, measureReal_def, Measure.dirac_apply', unitInterval.coe_symm_eq]
  simp only [hweight, smul_eq_mul]
  cases a with
  | none => simp [entryCost, weight]; ring_nf; try rfl
  | some b => cases b <;> simp [entryCost, weight] <;> nlinarith [mul_nonneg r.2.1 hq]

lemma path_entry_bound (q : ℝ) (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) (r : unitInterval)
    (t : ℕ) :
    ∫ z, entryCost (z t) (z (t + 1))
      ∂(pathLaw (refreshKernel (colorLaw q hq hq') r) (colorLaw q hq hq') : Measure (ℕ → Color))
      ≤ 2 * r * q := by
  let π := colorLaw q hq hq'
  let κ := refreshKernel π r
  let W := fun (h : Finset.Iic t → Color) (y : Color) => entryCost (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) y
  have he := finite_pathLaw_integral_future κ π t 1 W
  change (∫ z, entryCost (z t) (z (t + 1)) ∂(pathLaw κ π : Measure (ℕ → Color))) ≤ _
  rw [show (∫ z, entryCost (z t) (z (t + 1)) ∂(pathLaw κ π : Measure (ℕ → Color))) = _ from he]
  refine (integral_mono (finite_integrable _ _) (integrable_const (2 * (r : ℝ) * q))
    (fun h => ?_)).trans_eq (by simp)
  simpa only [pow_one, W, κ, π] using next_entry_bound q hq hq' r (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩)

lemma entries_measurable (t : ℕ) : Measurable (fun z : ℕ → Color => entries z t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let h : Color × Color → ℕ := fun p =>
      if p.1.isSome && (t == 0 || p.1 != p.2) then 1 else 0
    change Measurable (fun z : ℕ → Color => entries z t + (h ∘ (fun z : ℕ → Color => (z t, z (t - 1)))) z)
    exact ih.add ((measurable_of_countable h).comp
      ((measurable_pi_apply t).prodMk (measurable_pi_apply (t - 1))))

lemma entries_le (z : ℕ → Color) (t : ℕ) : entries z t ≤ t := by
  induction t with
  | zero => rfl
  | succ t ih => unfold entries; split <;> omega

lemma entries_mean (q : ℝ) (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) (r : unitInterval)
    (t : ℕ) :
    ∫ z, (entries z t : ℝ)
      ∂(pathLaw (refreshKernel (colorLaw q hq hq') r) (colorLaw q hq hq') : Measure (ℕ → Color))
      ≤ 1 + t * (2 * r * q) := by
  let P : Measure (ℕ → Color) := pathLaw (refreshKernel (colorLaw q hq hq') r) (colorLaw q hq hq')
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hi (k : ℕ) : Integrable (fun z : ℕ → Color => (entries z k : ℝ)) P :=
    Integrable.of_bound ((measurable_of_countable (fun t : ℕ => (t : ℝ))).comp (entries_measurable k)).aestronglyMeasurable k
      (.of_forall fun z => by simpa using (show ((entries z k : ℕ) : ℝ) ≤ k by exact_mod_cast entries_le z k))
  induction t with
  | zero => simp [entries]
  | succ t ih =>
    cases t with
    | zero =>
      apply (integral_mono (hi 1) (integrable_const (1 : ℝ)) (fun z => show (entries z 1 : ℝ) ≤ 1 by
        exact_mod_cast entries_le z 1)).trans
      simp only [integral_const, probReal_univ, one_smul]
      push_cast
      nlinarith [mul_nonneg r.2.1 hq]
    | succ k =>
      have he (z : ℕ → Color) : (entries z (k + 1 + 1) : ℝ) =
          entries z (k + 1) + entryCost (z k) (z (k + 1)) := by
        simp [entries, entryCost, ne_comm]
      have hm : Measurable ((fun p : Color × Color => entryCost p.1 p.2) ∘
          (fun z : ℕ → Color => (z k, z (k + 1)))) :=
        (measurable_of_countable (fun p : Color × Color => entryCost p.1 p.2)).comp
          ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
      have hb := path_entry_bound q hq hq' r k
      simp_rw [he]
      erw [integral_add (hi (k + 1)) (Integrable.of_bound hm.aestronglyMeasurable 1
        (.of_forall fun z => entryCost_bound _ _))]
      push_cast at ih ⊢
      exact (add_le_add ih hb).trans_eq (by ring)

end LongTails.Proofs.MarkovParityChain
