import LongTails.Proofs.MomentumSeparationInstance
import LongTails.Proofs.AdamSeparationModel
import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.MomentumSpectralSmooth

namespace LongTails.Proofs.MomentumSeparationModel

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.MomentumSeparationInstance LongTails.Proofs.AdamSeparationModel

variable {m n : ℕ}

abbrev Col (m n : ℕ) := Fin (n - min m n + 1)

def row0 (hr : 0 < min m n) : Fin m := ⟨0, lt_of_lt_of_le hr (min_le_left _ _)⟩

def colOf (hr : 0 < min m n) (i : Col m n) : Fin n :=
  if h : i.val = 0 then ⟨0, lt_of_lt_of_le hr (min_le_right _ _)⟩
  else ⟨min m n + i.val - 1, by have := i.isLt; have := min_le_right m n; omega⟩

lemma colOf_injective (hr : 0 < min m n) : Function.Injective (colOf hr) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  unfold colOf at hv
  split_ifs at hv with hi hj hj <;> simp at hv <;> omega

lemma stiffEntry_colOf (hr : 0 < min m n) (i : Col m n) :
    stiffEntry ((row0 hr, colOf hr i) : Fin m × Fin n) := by
  refine ⟨rfl, ?_⟩
  unfold colOf
  split_ifs with h
  · left; rfl
  · right; simp; omega

lemma stiffEntry_iff (hr : 0 < min m n) (p : Fin m × Fin n) :
    stiffEntry p ↔ ∃ i, p = (row0 hr, colOf hr i) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases h2 with h2 | h2
    · refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact h1
      · simp [colOf, h2]
    · refine ⟨⟨p.2.val - min m n + 1, by have := p.2.isLt; omega⟩, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact h1
      · simp only [colOf]
        rw [dite_eq_right (by omega)]
        simp; omega
  · rintro ⟨i, rfl⟩
    exact stiffEntry_colOf hr i

noncomputable def noise (hr : 0 < min m n) (s : ℝ) (ω : Col m n × Bool) : Space m n :=
  (s * sign ω.2) • EuclideanSpace.single ((row0 hr, colOf hr ω.1) : Fin m × Fin n) (1 : ℝ)

lemma noise_apply (hr : 0 < min m n) (s : ℝ) (ω : Col m n × Bool) (p : Fin m × Fin n) :
    noise hr s ω p = if p = (row0 hr, colOf hr ω.1) then s * sign ω.2 else 0 := by
  simp only [noise, PiLp.smul_apply, smul_eq_mul]
  rw [show (EuclideanSpace.single ((row0 hr, colOf hr ω.1) : Fin m × Fin n) (1 : ℝ)) p =
    if p = (row0 hr, colOf hr ω.1) then 1 else 0 from PiLp.single_apply _ _ _ _ _]
  split_ifs <;> simp

noncomputable def colLaw (m n : ℕ) : ProbabilityMeasure (Col m n × Bool) :=
  ⟨(PMF.uniformOfFintype (Col m n × Bool)).toMeasure, inferInstance⟩

lemma finite_integrable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : Col m n × Bool → E) : Integrable f (colLaw m n : Measure _) := by
  apply Integrable.of_bound (measurable_of_finite f).aestronglyMeasurable
    (∑ ω, ‖f ω‖)
  exact Filter.Eventually.of_forall fun ω =>
    Finset.single_le_sum (f := fun ω => ‖f ω‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ ω)

lemma integral_noise (hr : 0 < min m n) (s : ℝ) :
    (∫ ω, noise hr s ω ∂(colLaw m n : Measure _)) = 0 := by
  rw [colLaw, ProbabilityMeasure.coe_mk, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fintype.sum_bool]
  simp only [noise, sign, ite_true, mul_one, Bool.false_eq_true, ite_false, mul_neg, neg_smul,
    smul_neg]
  exact add_neg_cancel _

noncomputable def sample (hr : 0 < min m n) (f : Space m n → ℝ) (s : ℝ) (X : Space m n)
    (ω : Col m n × Bool) : Space m n :=
  gradient f X + noise hr s ω

lemma sample_measurable (hr : 0 < min m n) (f : Space m n → ℝ) (s : ℝ) :
    Measurable (Function.uncurry (sample hr f s)) :=
  ((LongTails.Proofs.MuonProcess.measurable_gradient f).comp measurable_fst).add
    ((measurable_of_finite (noise hr s)).comp measurable_snd)

lemma sample_unbiased (hr : 0 < min m n) (f : Space m n → ℝ) (s : ℝ) (X : Space m n) :
    (∫ ω, sample hr f s X ω ∂(colLaw m n : Measure _)) = gradient f X := by
  unfold sample
  rw [integral_add (integrable_const _) (finite_integrable _), integral_const, integral_noise]
  simp

lemma noise_row_norm (hr : 0 < min m n) {s : ℝ} (hs : 0 ≤ s) (ω : Col m n × Bool) (i : Fin m) :
    ‖(operatorEquiv m n (noise hr s ω)).adjoint (EuclideanSpace.basisFun (Fin m) ℝ i)‖ =
      if i.val = 0 then s else 0 := by
  rw [row_norm_eq]
  have hv : (s * sign ω.2) ^ 2 = s ^ 2 := by
    rw [mul_pow]
    cases ω.2 <;> simp [sign]
  have hsum : ∑ j, noise hr s ω (i, j) ^ 2 = if i.val = 0 then s ^ 2 else 0 := by
    simp_rw [noise_apply]
    by_cases hi : i.val = 0
    · have hi' : i = row0 hr := Fin.ext hi
      rw [Finset.sum_eq_single (colOf hr ω.1), ite_eq_left hi]
      · rw [ite_eq_left (by rw [hi'])]
        exact hv
      · intro j _ hj
        have : ((i, j) : Fin m × Fin n) ≠ (row0 hr, colOf hr ω.1) := by
          intro h; exact hj (congrArg Prod.snd h)
        rw [ite_eq_right this]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j _
      have : ((i, j) : Fin m × Fin n) ≠ (row0 hr, colOf hr ω.1) := by
        intro h
        have h1 : i = row0 hr := congrArg Prod.fst h
        exact hi (by rw [h1]; rfl)
      rw [ite_eq_right this]; ring
  rw [hsum]
  split_ifs
  · exact Real.sqrt_sq hs
  · exact Real.sqrt_zero

noncomputable def gradientModel (hr : 0 < min m n) (f : Space m n → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s where
  Ω := Col m n × Bool
  law := colLaw m n
  sample := sample hr f s
  jointly_measurable := sample_measurable hr f s
  integrable X := finite_integrable _
  unbiased := sample_unbiased hr f s
  row_profile := by
    refine ⟨EuclideanSpace.basisFun (Fin m) ℝ, fun i => if i.val = 0 then s else 0,
      fun i => by dsimp only; split_ifs <;> linarith, ?_, ?_⟩
    · rw [Finset.sum_eq_single (row0 hr)]
      · simp [row0]
      · intro i _ hi
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro X i
      have heq (ω : Col m n × Bool) :
          ‖(operatorEquiv m n (sample hr f s X ω - gradient f X)).adjoint
            (EuclideanSpace.basisFun (Fin m) ℝ i)‖ = if i.val = 0 then s else 0 := by
        simp only [sample, add_sub_cancel_left]
        exact noise_row_norm hr hs ω i
      constructor
      · apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable s
        exact Filter.Eventually.of_forall fun ω => by
          rw [heq]; split_ifs <;> simp [hs]
      · simp_rw [heq]
        rw [integral_const, probReal_univ, one_smul]

noncomputable def colStream (m n : ℕ) : ProbabilityMeasure (ℕ → Col m n × Bool) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (colLaw m n : Measure (Col m n × Bool))), inferInstance⟩

lemma colStream_iid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
    (fun k (ξ : ℕ → Col m n × Bool) => ξ k) (colLaw m n : Measure _) (colStream m n : Measure _) :=
  OracleTemplate.StochasticGeneralized.infinitePi_iid _

noncomputable def hardOracle (hr : 0 < min m n) (f : Space m n → ℝ) (s : ℝ) :
    Oracle (Space m n) (Space m n) where
  Seed := fun _ => Col m n × Bool
  law := colStream m n
  answer := fun _ (_, X) ω => sample hr f s X ω

end LongTails.Proofs.MomentumSeparationModel
