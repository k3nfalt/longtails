import LongTails.Proofs.LinearDecaySgdExpectation
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TwoSidedPL

variable {Ω : Type*} [MeasurableSpace Ω] {Y : Type*} [MeasurableSpace Y]

noncomputable def extendPrefix (ω0 : Ω) (k : ℕ) (u : Fin k → Ω) : ℕ → Ω :=
  fun i => if h : i < k then u ⟨i, h⟩ else ω0

lemma measurable_extendPrefix (ω0 : Ω) (k : ℕ) : Measurable (extendPrefix ω0 k) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i < k
  · simp only [extendPrefix, h, dite_true]; exact measurable_pi_apply _
  · simp only [extendPrefix, h, dite_false]; exact measurable_const

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
lemma factor_prefix (ω0 : Ω) (k : ℕ) (X : (ℕ → Ω) → Y)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ') (ξ : ℕ → Ω) :
    X ξ = (X ∘ extendPrefix ω0 k) (fun i : Fin k => ξ i) := by
  apply hdep
  intro i hi
  simp [extendPrefix, hi]

lemma integral_prefix_dep (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (X : (ℕ → Ω) → Y) (hX : Measurable X)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (Φ : Y → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hi : Integrable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) (Measure.infinitePi fun _ : ℕ => p)) :
    ∫ ξ, Φ (X ξ) (ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫ ξ, (∫ ω, Φ (X ξ) ω ∂p) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hf := factor_prefix ω0 k X hdep
  have hX' : Measurable (X ∘ extendPrefix ω0 k) := hX.comp (measurable_extendPrefix ω0 k)
  simp_rw [hf] at hi ⊢
  exact (SampledConvex.integral_prefix p k (X ∘ extendPrefix ω0 k) hX' Φ hΦ hi).2

lemma integrable_prefix_dep (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (X : (ℕ → Ω) → Y) (hX : Measurable X)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (Φ : Y → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ)) (hnn : ∀ y ω, 0 ≤ Φ y ω)
    (hsec : ∀ y, Integrable (Φ y) p) {B : ℝ} (hB : ∀ y, ∫ ω, Φ y ω ∂p ≤ B) :
    Integrable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, Φ (X ξ) (ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) ≤ B := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  set P := Measure.infinitePi fun _ : ℕ => p
  set X' := X ∘ extendPrefix ω0 k
  have hX' : Measurable X' := hX.comp (measurable_extendPrefix ω0 k)
  have hf := factor_prefix ω0 k X hdep
  set π : (ℕ → Ω) → (Fin k → Ω) := fun ξ i => ξ i
  have hπ : Measurable π := by fun_prop
  have hpair : Measurable (fun ξ : ℕ → Ω => (π ξ, ξ k)) := by fun_prop
  let H : (Fin k → Ω) × Ω → ℝ := fun w => Φ (X' w.1) w.2
  have hH : Measurable H := hΦ.comp ((hX'.comp measurable_fst).prodMk measurable_snd)
  have hmap := SampledConvex.map_prefix_pair p k
  have hHi : Integrable H ((P.map π).prod p) := by
    rw [integrable_prod_iff hH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun u => hsec (X' u), ?_⟩
    have hm : Measurable fun u => ∫ ω, ‖H (u, ω)‖ ∂p :=
      (hH.norm.stronglyMeasurable.integral_prod_right' :
        StronglyMeasurable fun u => ∫ ω, ‖H (u, ω)‖ ∂p).measurable
    refine Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall fun u => ?_)
    have e : ∫ ω, ‖H (u, ω)‖ ∂p = ∫ ω, Φ (X' u) ω ∂p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by simp [H, Real.norm_eq_abs, abs_of_nonneg (hnn _ _)]
    rw [e, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => hnn _ _)]
    exact hB _
  have hint : Integrable (fun ξ : ℕ → Ω => Φ (X ξ) (ξ k)) P := by
    have h1 : Integrable (H ∘ fun ξ : ℕ → Ω => (π ξ, ξ k)) P := by
      rw [← hmap] at hHi
      exact (integrable_map_measure hH.aestronglyMeasurable hpair.aemeasurable).mp hHi
    refine h1.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Function.comp, H, X', π]
    congr 1
    exact (hf ξ).symm
  refine ⟨hint, ?_⟩
  rw [integral_prefix_dep p k X hX hdep Φ hΦ hint]
  calc ∫ ξ, (∫ ω, Φ (X ξ) ω ∂p) ∂P ≤ ∫ _ξ, B ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => integral_nonneg fun ω => hnn _ _)
          (integrable_const B) (Filter.Eventually.of_forall fun ξ => hB _)
    _ = B := by simp

lemma integral_inner_prefix {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (X : (ℕ → Ω) → Y) (hX : Measurable X)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (U : Y → V) (hU : Measurable U) (G : Y → Ω → V) (hG : Measurable (Function.uncurry G))
    (m : Y → V) (hm : Measurable m) (hGi : ∀ y, Integrable (G y) p)
    (hmean : ∀ y, ∫ ω, G y ω ∂p = m y)
    (hi : Integrable (fun ξ : ℕ → Ω => ⟪U (X ξ), G (X ξ) (ξ k) - m (X ξ)⟫)
      (Measure.infinitePi fun _ : ℕ => p)) :
    ∫ ξ, ⟪U (X ξ), G (X ξ) (ξ k) - m (X ξ)⟫ ∂(Measure.infinitePi fun _ : ℕ => p) = 0 := by
  have hΦ : Measurable (Function.uncurry fun (y : Y) (ω : Ω) => ⟪U y, G y ω - m y⟫) := by
    have h1 : Measurable fun w : Y × Ω => U w.1 := hU.comp measurable_fst
    have h2 : Measurable fun w : Y × Ω => G w.1 w.2 - m w.1 := hG.sub (hm.comp measurable_fst)
    exact h1.inner h2
  rw [integral_prefix_dep p k X hX hdep (fun y ω => ⟪U y, G y ω - m y⟫) hΦ hi]
  have hz : ∀ y, ∫ ω, ⟪U y, G y ω - m y⟫ ∂p = 0 := by
    intro y
    have h1 := integral_inner (𝕜 := ℝ) (f := fun ω => G y ω - m y) ((hGi y).sub (integrable_const _)) (U y)
    have h2 : ∫ ω, (G y ω - m y) ∂p = 0 := by
      rw [integral_sub (hGi y) (integrable_const _), hmean, integral_const]
      simp
    rw [h1, h2, inner_zero_right]
  simp [hz]

section MemLp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_two_of_norm_le {G : Type*} [NormedAddCommGroup G] {f : α → G} {g : α → ℝ}
    (hg : MemLp g 2 μ) (hf : AEStronglyMeasurable f μ) (h : ∀ a, ‖f a‖ ≤ g a) : MemLp f 2 μ :=
  hg.of_le hf (Filter.Eventually.of_forall fun a => (h a).trans (Real.le_norm_self _))

lemma memLp_two_iff_sq {G : Type*} [NormedAddCommGroup G] {f : α → G}
    (hf : AEStronglyMeasurable f μ) : MemLp f 2 μ ↔ Integrable (fun a => ‖f a‖ ^ 2) μ :=
  memLp_two_iff_integrable_sq_norm hf

lemma integrable_norm_mul_norm {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {f : α → G} {g : α → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun a => ‖f a‖ * ‖g a‖) μ :=
  hf.norm.integrable_mul hg.norm

lemma integrable_inner_of_memLp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f g : α → V} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun a => ⟪f a, g a⟫) μ := by
  refine (integrable_norm_mul_norm hf hg).mono' ?_ (Filter.Eventually.of_forall fun a => ?_)
  · exact hf.aestronglyMeasurable.inner hg.aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _

end MemLp

end OracleTemplate.TwoSidedPL
