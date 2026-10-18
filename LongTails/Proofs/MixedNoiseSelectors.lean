import LongTails.Algorithms.MultiscaleRepresentatives
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Logic.Equiv.Prod

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.MixedNoise

lemma integral_uniform_finite {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ i, f i ∂(PMF.uniformOfFintype α).toMeasure) =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, f i := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [Finset.mul_sum]

lemma integrable_uniform_integral {α β : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (P : Measure β) (f : α → β → ℝ) (hi : ∀ a, Integrable (f a) P) :
    Integrable (fun b => ∫ a, f a b ∂(PMF.uniformOfFintype α).toMeasure) P := by
  simp only [integral_uniform_finite]
  exact (integrable_finsetSum _ (fun a _ => hi a)).const_mul _

lemma integral_uniform_measure_comm {α β : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (P : Measure β) (f : α → β → ℝ) (hi : ∀ a, Integrable (f a) P) :
    (∫ b, (∫ a, f a b ∂(PMF.uniformOfFintype α).toMeasure) ∂P) =
      ∫ a, (∫ b, f a b ∂P) ∂(PMF.uniformOfFintype α).toMeasure := by
  simp only [integral_uniform_finite]
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => hi a)]

lemma integral_uniform_weighted_sum {α β ι : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (P : Measure β) (s : Finset ι) (w : ι → ℝ) (f : α → β → ι → ℝ)
    (hi : ∀ a i, i ∈ s → Integrable (fun b => f a b i) P) :
    (∑ i ∈ s, w i * (∫ a, (∫ b, f a b i ∂P) ∂(PMF.uniformOfFintype α).toMeasure)) =
      ∫ a, (∫ b, ∑ i ∈ s, w i * f a b i ∂P) ∂(PMF.uniformOfFintype α).toMeasure := by
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  funext a
  exact (integral_finsetSum _ (fun i hi' => (hi a i hi').const_mul (w i))).symm

lemma integral_uniform_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : α ≃ β) (f : β → ℝ) :
    (∫ i, f (e i) ∂(PMF.uniformOfFintype α).toMeasure) =
      ∫ j, f j ∂(PMF.uniformOfFintype β).toMeasure := by
  rw [integral_uniform_finite, integral_uniform_finite, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

lemma integral_uniform_prod {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β → ℝ) :
    (∫ z, f z.1 z.2 ∂(PMF.uniformOfFintype (α × β)).toMeasure) =
      ∫ a, (∫ b, f a b ∂(PMF.uniformOfFintype β).toMeasure)
        ∂(PMF.uniformOfFintype α).toMeasure := by
  simp only [integral_uniform_finite, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum]
  ring

lemma integral_uniform_comm {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β → ℝ) :
    (∫ a, (∫ b, f a b ∂(PMF.uniformOfFintype β).toMeasure)
        ∂(PMF.uniformOfFintype α).toMeasure) =
      ∫ b, (∫ a, f a b ∂(PMF.uniformOfFintype α).toMeasure)
        ∂(PMF.uniformOfFintype β).toMeasure := by
  simp only [integral_uniform_finite, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

lemma uniform_selected_component {S α β : Type*}
    [Fintype S] [Fintype α] [Fintype β] [Nonempty S] [Nonempty α] [Nonempty β]
    [MeasurableSpace S] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass S] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : S ≃ α × β) (f : β → α → ℝ) :
    (∫ s, f (e s).2 (e s).1 ∂(PMF.uniformOfFintype S).toMeasure) =
      ∫ s, (∫ a, f (e s).2 a ∂(PMF.uniformOfFintype α).toMeasure)
        ∂(PMF.uniformOfFintype S).toMeasure := by
  rw [integral_uniform_equiv e (fun z => f z.2 z.1),
    integral_uniform_equiv e (fun z => ∫ a, f z.2 a ∂(PMF.uniformOfFintype α).toMeasure)]
  rw [integral_uniform_prod (fun a b => f b a),
    integral_uniform_prod (fun (_ : α) b => ∫ a, f b a ∂(PMF.uniformOfFintype α).toMeasure),
    integral_uniform_comm]
  simp

lemma uniform_choice_energy {S α β : Type*}
    [Fintype S] [Fintype α] [Fintype β] [Nonempty S] [Nonempty α] [Nonempty β]
    [MeasurableSpace S] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass S] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : S ≃ α × β) (F : S → α → ℝ)
    (hdep : ∀ s s', (e s).2 = (e s').2 → F s = F s') :
    (∫ s, F s (e s).1 ∂(PMF.uniformOfFintype S).toMeasure) =
      ∫ s, (∫ a, F s a ∂(PMF.uniformOfFintype α).toMeasure)
        ∂(PMF.uniformOfFintype S).toMeasure := by
  obtain ⟨a0⟩ := ‹Nonempty α›
  let G : β → α → ℝ := fun b => F (e.symm (a0, b))
  have hf : ∀ s, F s = G (e s).2 := by
    intro s
    apply hdep
    simp
  simp_rw [hf]
  exact uniform_selected_component e G

def representativeSeedEquiv (cfg : Config) :
    RepresentativeSeed cfg ≃ Fin (max 1 cfg.T) ×
      ((i : Fin (cfg.m + 1) × Fin (cfg.T + 1)) → Fin (4 ^ i.1.val)) where
  toFun s := (s.outputIndex, s.representatives)
  invFun z := ⟨z.1, z.2⟩
  left_inv s := by cases s; rfl
  right_inv z := by cases z; rfl

def representativeSplit (cfg : Config) (i : Fin (cfg.m + 1) × Fin (cfg.T + 1)) :
    RepresentativeSeed cfg ≃ Fin (4 ^ i.1.val) ×
      (Fin (max 1 cfg.T) × ((j : {j : Fin (cfg.m + 1) × Fin (cfg.T + 1) // j ≠ i}) →
        Fin (4 ^ j.val.1.val))) :=
  (representativeSeedEquiv cfg).trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.piSplitAt i (fun j => Fin (4 ^ j.1.val)))).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))))

lemma representativeSplit_fst (cfg : Config) (i : Fin (cfg.m + 1) × Fin (cfg.T + 1))
    (seed : RepresentativeSeed cfg) :
    (representativeSplit cfg i seed).1 = seed.representatives i := by rfl

lemma representativeSplit_snd (cfg : Config) (i : Fin (cfg.m + 1) × Fin (cfg.T + 1))
    (seed : RepresentativeSeed cfg) :
    (representativeSplit cfg i seed).2 = (seed.outputIndex,
      fun j : {j : Fin (cfg.m + 1) × Fin (cfg.T + 1) // j ≠ i} =>
        seed.representatives j.val) := by rfl

end OracleTemplate.MixedNoise
