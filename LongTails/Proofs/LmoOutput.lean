import LongTails.Proofs.LmoTrajectory
import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

lemma uniform_integral {T : ℕ} {μ : Measure (ℕ → Ω)} [IsProbabilityMeasure μ]
    (Z : Fin (T + 1) → (ℕ → Ω) → ℝ) (hZ : ∀ j, Measurable (Z j)) {B : ℝ}
    (hB : ∀ j ξ, |Z j ξ| ≤ B) :
    Integrable (fun ω : Fin (T + 1) × (ℕ → Ω) => Z ω.1 ω.2)
        (((PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod μ) ∧
      ∫ ω : Fin (T + 1) × (ℕ → Ω), Z ω.1 ω.2
          ∂(((PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod μ) =
        1 / ((T : ℝ) + 1) * ∑ j : Fin (T + 1), ∫ ξ, Z j ξ ∂μ := by
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) => Z ω.1 ω.2) :=
    measurable_from_prod_countable_right fun j => hZ j
  have hint : Integrable (fun ω : Fin (T + 1) × (ℕ → Ω) => Z ω.1 ω.2)
      (((PMF.uniformOfFintype (Fin (T + 1))).toMeasure).prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB ω.1 ω.2)
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  have hin : Integrable (fun j : Fin (T + 1) => ∫ ξ, Z j ξ ∂μ)
      ((PMF.uniformOfFintype (Fin (T + 1))).toMeasure) := Integrable.of_finite
  rw [integral_fintype hin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
  simp only [Fintype.card_unique, Nat.cast_one, Fintype.card_fin]
  rw [ENNReal.toReal_div, ENNReal.toReal_one]
  congr 1
  rw [show (((T + 1 : ℕ) : ENNReal)) = ((T + 1 : ℕ) : ENNReal) from rfl, ENNReal.toReal_natCast]
  push_cast; ring

lemma output_integral (step : Space d → Space d → Space d)
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2)) (α : ℕ → ℝ) (T : ℕ)
    (x₁ : Space d) {g : Space d → Ω → Space d} (hg : Measurable (Function.uncurry g))
    (P₀ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (P₀ : Measure Ω) (P : Measure (ℕ → Ω)))
    (K : ℕ) (hK : T ≤ K) (F : Space d → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : ∀ j, j ≤ T → ∀ ξ, |F (path step α x₁ g ξ j).1| ≤ B) :
    Measurable (fun seed : (lmoMethod step α T x₁).Seed × ((k : ℕ) → Ω) =>
        execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
          Oracle (Space d) (Space d)) (lmoMethod step α T x₁) (fun _ => K) seed.1 seed.2) ∧
      Integrable (fun seed : (lmoMethod step α T x₁).Seed × ((k : ℕ) → Ω) =>
        F (execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
          Oracle (Space d) (Space d)) (lmoMethod step α T x₁) (fun _ => K) seed.1 seed.2))
        (((lmoMethod step α T x₁).law : Measure _).prod (P : Measure (ℕ → Ω))) ∧
      ∫ seed : (lmoMethod step α T x₁).Seed × ((k : ℕ) → Ω),
          F (execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
            Oracle (Space d) (Space d)) (lmoMethod step α T x₁) (fun _ => K) seed.1 seed.2)
          ∂(((lmoMethod step α T x₁).law : Measure _).prod (P : Measure (ℕ → Ω))) =
        1 / ((T : ℝ) + 1) * ∑ j ∈ Finset.range (T + 1),
          ∫ ξ, F (path step α x₁ g ξ j).1 ∂(Measure.infinitePi fun _ : ℕ => (P₀ : Measure Ω)) := by
  have hP : (P : Measure (ℕ → Ω)) = Measure.infinitePi fun _ : ℕ => (P₀ : Measure Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → Ω)))).symm.trans this
  have hexec : ∀ seed : (lmoMethod step α T x₁).Seed × ((k : ℕ) → Ω),
      execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
        Oracle (Space d) (Space d)) (lmoMethod step α T x₁) (fun _ => K) seed.1 seed.2 =
      (path step α x₁ g seed.2 (seed.1 : Fin (T + 1)).val).1 :=
    fun seed => execute_lmoMethod step α T x₁ g P K hK seed.1 seed.2
  have hpath := measurable_path hstep α x₁ hg
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) => (path step α x₁ g ω.2 ω.1.val).1) :=
    measurable_from_prod_countable_right fun j => (hpath j.val).fst
  have hu := uniform_integral (μ := (P : Measure (ℕ → Ω)))
    (fun (j : Fin (T + 1)) ξ => F (path step α x₁ g ξ j.val).1)
    (fun j => hF.comp (hpath j.val).fst) (fun j ξ => hB j.val (Nat.lt_succ_iff.mp j.isLt) ξ)
  simp only [hexec]
  refine ⟨hm, hu.1, ?_⟩
  have h2 := hu.2
  rw [Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, F (path step α x₁ g ξ j).1 ∂(P : Measure _))] at h2
  rw [← hP]
  exact h2

end OracleTemplate.NormBallLMO
