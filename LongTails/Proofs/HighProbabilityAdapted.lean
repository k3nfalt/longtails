import LongTails.Proofs.AdaptiveOracleConcentration
import LongTails.Proofs.StoppedVectorConcentration
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityAdapted

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

def histPoint (F : X → Z → X) (x0 : X) : (n : ℕ) → (Fin n → Z) → X
  | 0, _ => x0
  | n + 1, a => F (histPoint F x0 n (Fin.init a)) (a (Fin.last n))

def traj (F : X → Z → X) (x0 : X) (b : ℕ → Z) : ℕ → X
  | 0 => x0
  | t + 1 => F (traj F x0 b t) (b t)

omit [MeasurableSpace X] [MeasurableSpace Z] in
lemma histPoint_eq (F : X → Z → X) (x0 : X) (b : ℕ → Z) (n : ℕ) :
    histPoint F x0 n (fun i => b i) = traj F x0 b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [histPoint, traj]
    have h : (Fin.init (fun i : Fin (n + 1) => b i)) = fun i : Fin n => b i := by
      funext i; simp [Fin.init]
    rw [h, ih]
    simp [Fin.last]

lemma measurable_histPoint {F : X → Z → X} (hF : Measurable (Function.uncurry F)) (x0 : X) :
    ∀ n, Measurable (histPoint F x0 n)
  | 0 => measurable_const
  | n + 1 => by
    have hinit : Measurable (Fin.init : (Fin (n + 1) → Z) → Fin n → Z) := by
      apply Measurable.of_eval
      intro i
      exact measurable_pi_apply i.castSucc
    exact hF.comp (((measurable_histPoint hF x0 n).comp hinit).prodMk
      (measurable_pi_apply (Fin.last n)))

variable {pb : Measure Z} [IsProbabilityMeasure pb]

lemma adapted_mgf {F : X → Z → X} (hF : Measurable (Function.uncurry F)) (x0 : X)
    {h : X → Z → ℝ} (hh : Measurable (Function.uncurry h)) {θ c : ℝ}
    (hint : ∀ x, Integrable (fun z => Real.exp (θ * h x z)) pb)
    (hbound : ∀ x, (∫ z, Real.exp (θ * h x z) ∂pb) ≤ Real.exp c) (T : ℕ) :
    Integrable (fun b : ℕ → Z => Real.exp (θ * ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t)))
        (Measure.infinitePi fun _ : ℕ => pb) ∧
      (∫ b, Real.exp (θ * ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t))
        ∂(Measure.infinitePi fun _ : ℕ => pb)) ≤ Real.exp (T * c) := by
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid pb
  let increment : (n : ℕ) → (Fin n → Z) × Z → ℝ := fun n az => h (histPoint F x0 n az.1) az.2
  have hinc : ∀ n, Measurable (increment n) := fun n =>
    hh.comp (((measurable_histPoint hF x0 n).comp measurable_fst).prodMk measurable_snd)
  have hres := LongTails.Proofs.AdaptiveOracleConcentration.iid_predictable_sum_exponential_bound
    hiid.measurable hiid.independent hiid.marginal (increment := increment) (fun _ => c) θ hinc
    (fun n a => hint (histPoint F x0 n a)) (fun n a => hbound (histPoint F x0 n a)) T
  have heq : (fun b : ℕ → Z => Real.exp (θ * ∑ i ∈ Finset.range T,
      increment i ((fun j => b j), b i))) =
      fun b => Real.exp (θ * ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t)) := by
    funext b
    congr 2
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [increment, histPoint_eq]
  rw [heq] at hres
  refine ⟨hres.1, hres.2.trans_eq ?_⟩
  simp

lemma adapted_tail {F : X → Z → X} (hF : Measurable (Function.uncurry F)) (x0 : X)
    {h : X → Z → ℝ} (hh : Measurable (Function.uncurry h)) {θ c : ℝ} (hθ : 0 ≤ θ)
    (hint : ∀ x, Integrable (fun z => Real.exp (θ * h x z)) pb)
    (hbound : ∀ x, (∫ z, Real.exp (θ * h x z) ∂pb) ≤ Real.exp c) (T : ℕ) (r : ℝ) :
    (Measure.infinitePi fun _ : ℕ => pb).real
      {b | r ≤ ∑ t ∈ Finset.range T, h (traj F x0 b t) (b t)} ≤ Real.exp (T * c - θ * r) := by
  have hm := adapted_mgf hF x0 hh hint hbound T
  exact LongTails.Proofs.StoppedVectorConcentration.exponential_tail_of_bound hθ hm.1 hm.2 r

lemma indicator_mgf {A : Set Z} (hA : MeasurableSet A) {ρ θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : pb.real A ≤ ρ) :
    Integrable (fun z => Real.exp (θ * A.indicator (fun _ => (1 : ℝ)) z)) pb ∧
      (∫ z, Real.exp (θ * A.indicator (fun _ => (1 : ℝ)) z) ∂pb) ≤
        Real.exp ((Real.exp θ - 1) * ρ) := by
  have he : (fun z => Real.exp (θ * A.indicator (fun _ => (1 : ℝ)) z)) =
      fun z => 1 + (Real.exp θ - 1) * A.indicator (fun _ => (1 : ℝ)) z := by
    funext z
    by_cases hz : z ∈ A
    · simp [hz]
    · simp [hz]
  have hi : Integrable (fun z => A.indicator (fun _ => (1 : ℝ)) z) pb :=
    (integrable_const (1 : ℝ)).indicator hA
  rw [he]
  refine ⟨(integrable_const 1).add (hi.const_mul _), ?_⟩
  rw [integral_add (integrable_const 1) (hi.const_mul _), integral_const_mul,
    integral_indicator_const (1 : ℝ) hA, integral_const, probReal_univ, one_smul, smul_eq_mul,
    mul_one]
  have hθ1 : 0 ≤ Real.exp θ - 1 := by linarith [Real.one_le_exp hθ]
  calc 1 + (Real.exp θ - 1) * pb.real A ≤ 1 + (Real.exp θ - 1) * ρ := by
        nlinarith [mul_le_mul_of_nonneg_left hρ hθ1]
    _ ≤ Real.exp ((Real.exp θ - 1) * ρ) := by
        linarith [Real.add_one_le_exp ((Real.exp θ - 1) * ρ)]

end LongTails.Proofs.HighProbabilityAdapted
