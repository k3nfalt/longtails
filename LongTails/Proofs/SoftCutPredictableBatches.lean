import LongTails.Proofs.CovarianceSoftCutProcess
import LongTails.Proofs.PredictableSubGaussian

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.SoftCutPredictableBatches

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Proofs.CovarianceSoftCutProcess

def prefixStream {Z : Type*} (z : Z) (n : ℕ) (h : Fin n → Z) : ℕ → Z :=
  fun i => if hi : i < n then h ⟨i, hi⟩ else z

lemma measurable_prefixStream {Z : Type*} [MeasurableSpace Z] (z : Z) (n : ℕ) :
    Measurable (prefixStream z n) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i < n
  · simpa [prefixStream, hi] using (measurable_pi_apply (⟨i, hi⟩ : Fin n))
  · simp only [prefixStream, hi, dite_false]
    exact measurable_const

lemma samplePoint_prefix (q : Params) (α η : ℝ) (b n : ℕ)
    (g : Space q → q.Ω → Space q) (z : q.Ω) (ξ : ℕ → q.Ω) :
    samplePoint q α η b g (n / b) (prefixStream z n (fun i => ξ i)) =
      samplePoint q α η b g (n / b) ξ := by
  unfold samplePoint
  congr 2
  apply sampleCuts_eq_of_prefix
  intro i hi
  have hin : i < n := lt_of_lt_of_le hi (Nat.div_mul_le_self n b)
  simp [prefixStream, hin]

lemma sum_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (T b : ℕ) :
    ∑ i ∈ Finset.range (T*b), f i =
      ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range b, f (t*b+j) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma repeated_coeff_square (a : ℕ → ℝ) (T b : ℕ) (hb : 0 < b) :
    ∑ i ∈ Finset.range (T*b), (a (i/b) / b) ^ 2 =
      (∑ t ∈ Finset.range T, a t ^ 2) / b := by
  rw [sum_blocks, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t ht
  have he : ∀ j ∈ Finset.range b, (t*b+j)/b = t := by
    intro j hj
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt (Finset.mem_range.mp hj)]
    simp
  simp_rw [Finset.sum_congr rfl (fun j hj => congrArg (fun k => (a k / (b : ℝ)) ^ 2) (he j hj))]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hb' : (b : ℝ) ≠ 0 := by positivity
  field_simp

def batchError (q : Params) (α η : ℝ) (b : ℕ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (t : ℕ) (ξ : ℕ → q.Ω) : Space q :=
  (b : ℝ)⁻¹ • ∑ j ∈ Finset.range b,
    (g (samplePoint q α η b g t ξ) (ξ (t*b+j)) - v (samplePoint q α η b g t ξ))

lemma micro_sum_eq_batches (q : Params) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (D : Space q → Space q) (a : ℕ → ℝ) (T : ℕ) (ξ : ℕ → q.Ω) :
    (∑ i ∈ Finset.range (T*b), a (i/b) / b *
      ⟪g (samplePoint q α η b g (i/b) ξ) (ξ i) - v (samplePoint q α η b g (i/b) ξ),
        D (samplePoint q α η b g (i/b) ξ)⟫) =
      ∑ t ∈ Finset.range T, a t * ⟪batchError q α η b g v t ξ,
        D (samplePoint q α η b g t ξ)⟫ := by
  rw [sum_blocks]
  apply Finset.sum_congr rfl
  intro t ht
  unfold batchError
  rw [real_inner_smul_left, sum_inner, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : (t*b+j)/b = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt (Finset.mem_range.mp hj)]
    simp
  rw [he]
  ring

lemma sample_direction_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (hR : 0 < q.R) (α η : ℝ) (b : ℕ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → q.Ω) (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (z : q.Ω) (D : ℕ → Space q → Space q) (hD : ∀ n, Measurable (D n))
    (a : ℕ → ℝ) (variance R A : ℝ)
    (hvariance : 0 ≤ variance) (hbound : 0 ≤ R) (hA : 0 ≤ A)
    (hDn : ∀ n x, ‖x‖ ≤ 2*q.R → ‖D n x‖ ≤ R)
    (hmgf : ∀ x u t, Integrable (fun w => Real.exp (t * ⟪g x w - v x, u⟫)) p ∧
      (∫ w, Real.exp (t * ⟪g x w - v x, u⟫) ∂p) ≤
        Real.exp (variance * ‖u‖ ^ 2 * t ^ 2 / 2))
    (N : ℕ) (hcoeff : ∑ i ∈ Finset.range N, a i ^ 2 ≤ A) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.range N,
      a i * ⟪g (samplePoint q α η b g (i/b) (fun j => ξ j ω)) (ξ i ω) -
        v (samplePoint q α η b g (i/b) (fun j => ξ j ω)),
        D i (samplePoint q α η b g (i/b) (fun j => ξ j ω))⟫)
      ⟨variance * R ^ 2 * A, by positivity⟩ P := by
  let point := fun n (h : Fin n → q.Ω) =>
    samplePoint q α η b g (n/b) (prefixStream z n h)
  have hp (n : ℕ) : Measurable (point n) :=
    (measurable_samplePoint q hR α η b g hg (n/b)).comp (measurable_prefixStream z n)
  let X := fun n (hz : (Fin n → q.Ω) × q.Ω) =>
    g (point n hz.1) hz.2 - v (point n hz.1)
  have hX (n : ℕ) : Measurable (X n) :=
    (hg.comp (((hp n).comp measurable_fst).prodMk measurable_snd)).sub
      (hv.comp ((hp n).comp measurable_fst))
  have hd (n : ℕ) : Measurable (fun h => D n (point n h)) := (hD n).comp (hp n)
  have hdn (n : ℕ) (h : Fin n → q.Ω) : ‖D n (point n h)‖ ≤ R := by
    apply hDn
    exact CovarianceSoftCutDensity.norm_centroid_le q hR α η _
  have hh := PredictableSubGaussian.predictable_direction_mgf hξ hind hlaw X hX
    (fun n h => D n (point n h)) hd a variance R A hvariance hbound hA hdn
    (fun n h u t => hmgf (point n h) u t) N hcoeff
  have he (n : ℕ) (ω : Ξ) : point n (fun j => ξ j ω) =
      samplePoint q α η b g (n/b) (fun j => ξ j ω) :=
    samplePoint_prefix q α η b n g z (fun j => ξ j ω)
  simp only [X] at hh
  simp_rw [he] at hh
  exact hh

lemma batch_direction_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (hR : 0 < q.R) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → q.Ω) (hξ : ∀ i, Measurable (ξ i))
    (hind : ProbabilityTheory.iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (z : q.Ω) (D : Space q → Space q) (hD : Measurable D)
    (a : ℕ → ℝ) (variance R A : ℝ)
    (hvariance : 0 ≤ variance) (hbound : 0 ≤ R) (hA : 0 ≤ A)
    (hDn : ∀ x, ‖x‖ ≤ 2*q.R → ‖D x‖ ≤ R)
    (hmgf : ∀ x u t, Integrable (fun w => Real.exp (t * ⟪g x w - v x, u⟫)) p ∧
      (∫ w, Real.exp (t * ⟪g x w - v x, u⟫) ∂p) ≤
        Real.exp (variance * ‖u‖ ^ 2 * t ^ 2 / 2))
    (T : ℕ) (hcoeff : ∑ i ∈ Finset.range T, a i ^ 2 ≤ A) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => ∑ t ∈ Finset.range T,
      a t * ⟪batchError q α η b g v t (fun j => ξ j ω),
        D (samplePoint q α η b g t (fun j => ξ j ω))⟫)
      ⟨variance * R ^ 2 * (A / b), by positivity⟩ P := by
  have hc : ∑ i ∈ Finset.range (T*b), (a (i/b) / b) ^ 2 ≤ A / b := by
    rw [repeated_coeff_square a T b hb]
    exact div_le_div_of_nonneg_right hcoeff (by positivity)
  have hh := sample_direction_mgf q hR α η b g v hg hv p P ξ hξ hind hlaw z
    (fun _ => D) (fun _ => hD) (fun i => a (i/b) / b) variance R (A/b)
    hvariance hbound (by positivity) (fun _ => hDn) hmgf (T*b) hc
  have he := fun ω : Ξ => micro_sum_eq_batches q α η b hb g v D a T (fun j => ξ j ω)
  simp_rw [he] at hh
  exact hh

end LongTails.Proofs.SoftCutPredictableBatches
