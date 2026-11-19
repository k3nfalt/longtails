import LongTails.Setups.PolynomialMixingSubgradient
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

namespace LongTails.Proofs.PolynomialMixingBlocks

open LongTails.Setups.PolynomialMixingSubgradient

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def SetError (μ ν : Measure X) (a : ℝ) : Prop :=
  ∀ B : Set X, MeasurableSet B → |μ.real B - ν.real B| ≤ a

lemma setError_trans {μ ν ρ : Measure X} {a b : ℝ}
    (h : SetError μ ν a) (k : SetError ν ρ b) : SetError μ ρ (a + b) := by
  intro B hB
  exact (abs_sub_le _ _ _).trans (add_le_add (h B hB) (k B hB))

lemma setError_map {μ ν : Measure X} {f : X → Y} {a : ℝ} (hf : Measurable f)
    (h : SetError μ ν a) : SetError (μ.map f) (ν.map f) a := by
  intro B hB
  simpa only [measureReal_def, Measure.map_apply hf hB] using h _ (hf hB)

lemma prod_section_real (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure ν] {B : Set (X × Y)} (hB : MeasurableSet B) :
    (μ.prod ν).real B = ∫ x, ν.real (Prod.mk x ⁻¹' B) ∂μ := by
  rw [measureReal_def, Measure.prod_apply hB]
  exact (integral_toReal (measurable_measure_prodMk_left hB).aemeasurable
    (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)).symm

lemma setError_prod_left (μ : Measure X) {ν ρ : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] {a : ℝ}
    (h : SetError ν ρ a) : SetError (μ.prod ν) (μ.prod ρ) a := by
  intro B hB
  rw [prod_section_real μ ν hB, prod_section_real μ ρ hB]
  have hi (η : Measure Y) [IsProbabilityMeasure η] :
      Integrable (fun x : X => η.real (Prod.mk x ⁻¹' B)) μ := by
    apply Integrable.of_bound (measurable_measure_prodMk_left hB).ennreal_toReal.aestronglyMeasurable 1
    filter_upwards with x
    change ‖η.real (Prod.mk x ⁻¹' B)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  rw [← integral_sub (hi ν) (hi ρ)]
  have ht := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x : X => ν.real (Prod.mk x ⁻¹' B) - ρ.real (Prod.mk x ⁻¹' B))
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using h _ (measurable_prodMk_left hB))
  simpa [Real.norm_eq_abs] using ht

lemma setError_symm {μ ν : Measure X} {a : ℝ} (h : SetError μ ν a) : SetError ν μ a := by
  intro B hB
  rw [abs_sub_comm]
  exact h B hB

lemma setError_prod_right (μ : Measure X) {ν ρ : Measure Y} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] {a : ℝ}
    (h : SetError ν ρ a) : SetError (ν.prod μ) (ρ.prod μ) a := by
  have hh := setError_map (f := Prod.swap) measurable_swap (setError_prod_left μ h)
  simpa only [Measure.prod_swap] using hh

lemma setError_coupling {W : Type*} [MeasurableSpace W] (P : Measure W) [IsProbabilityMeasure P]
    {F H : W → X} (hF : Measurable F) (hH : Measurable H) (bad : Set W)
    (he : ∀ w ∉ bad, F w = H w) : SetError (P.map F) (P.map H) (P.real bad) := by
  intro B hB
  rw [map_measureReal_apply hF hB, map_measureReal_apply hH hB]
  have hle {U V : W → X} (hh : ∀ w ∉ bad, U w = V w) :
      P.real (U ⁻¹' B) ≤ P.real (V ⁻¹' B) + P.real bad := by
    apply (measureReal_mono (show U ⁻¹' B ⊆ (V ⁻¹' B) ∪ bad from ?_)).trans
      (measureReal_union_le _ _)
    intro w hw
    by_cases hb : w ∈ bad
    · exact Or.inr hb
    · exact Or.inl (by simpa only [Set.mem_preimage, ← hh w hb] using hw)
  have h₁ := hle he
  have h₂ := hle (fun w hw => (he w hw).symm)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma two_block_error (P : ProbabilityMeasure Path) {τ β : ℝ}
    (h : AbsolutelyRegular P τ β) (n t : ℕ) :
    SetError ((P : Measure Path).map (fun z => (past (n + 1) z, future (n + t) z)))
      (((P : Measure Path).map (past (n + 1))).prod (P : Measure Path))
      ((1 + (t : ℝ) / τ) ^ (-β)) := by
  have hm : Measurable (fun z => (past (n + 1) z, future (n + t) z)) := by
    unfold past future
    fun_prop
  intro B hB
  rw [measureReal_def, Measure.map_apply hm hB]
  exact h.2 n t B hB


def blocks {h : ℕ} (read : (Fin (h + 1) → ℝ) → X) (stride k : ℕ) (z : Path) : Fin k → X :=
  fun i => read (fun j => z (i.val * stride + j.val))

lemma measurable_blocks {h : ℕ} {read : (Fin (h + 1) → ℝ) → X} (hr : Measurable read)
    (stride k : ℕ) : Measurable (blocks read stride k) := by
  unfold blocks
  fun_prop

lemma block_error (P : ProbabilityMeasure Path) {τ β : ℝ} (hmix : AbsolutelyRegular P τ β)
    {h : ℕ} {read : (Fin (h + 1) → ℝ) → X} (hr : Measurable read)
    (t k : ℕ) :
    SetError ((P : Measure Path).map (blocks read (h + t) k))
      (Measure.pi fun _ : Fin k => (P : Measure Path).map (read ∘ past (h + 1)))
      (k * (1 + (t : ℝ) / τ) ^ (-β)) := by
  let stride := h + t
  let M := (P : Measure Path).map (read ∘ past (h + 1))
  have hm : Measurable (read ∘ past (h + 1)) := by unfold past; fun_prop
  let : IsProbabilityMeasure M := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  induction k with
  | zero =>
    let : IsProbabilityMeasure ((P : Measure Path).map (blocks read stride 0)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_blocks hr stride 0).aemeasurable).mpr inferInstance
    change SetError ((P : Measure Path).map (blocks read stride 0)) (Measure.pi (fun _ : Fin 0 => M)) _
    intro B _
    rcases B.eq_empty_or_nonempty with he | he
    · simp [he]
    · simp [Subsingleton.eq_univ_of_nonempty he]
  | succ k ih =>
    let rest := blocks read stride k
    have hrest : Measurable rest := measurable_blocks hr stride k
    let split := fun z : Path => (past (h + 1) z, future stride z)
    have hs : Measurable split := by unfold split past future; fun_prop
    let pack := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => X) 0).symm
    let F := Prod.map read rest
    have hF : Measurable F := hr.prodMap hrest
    have h₁ := setError_map hF (two_block_error P hmix h t)
    change SetError (((P : Measure Path).map split).map F)
      ((((P : Measure Path).map (past (h + 1))).prod (P : Measure Path)).map F) _ at h₁
    have hp : Measurable (past (h + 1)) := by unfold past; fun_prop
    rw [Measure.map_map hF hs, ← Measure.map_prod_map _ _ hr hrest,
      Measure.map_map hr hp] at h₁
    have ht := setError_trans h₁ (setError_prod_left M ih)
    have hpck := setError_map pack.measurable ht
    rw [Measure.map_map pack.measurable (hF.comp hs)] at hpck
    have hprod := ((measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => M) 0).symm).map_eq
    change ((M.prod (Measure.pi fun _ : Fin k => M)).map pack) = _ at hprod
    rw [hprod] at hpck
    have he : pack ∘ F ∘ split = blocks read stride (k + 1) := by
      funext z i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [pack, F, split, blocks, Function.comp_def,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        rfl
      · simp [pack, F, split, rest, blocks, future, Function.comp_def,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Nat.succ_mul, Nat.add_left_comm, Nat.add_comm]
    rw [he] at hpck
    simpa only [Nat.cast_succ, add_mul, one_mul, add_comm] using hpck

end LongTails.Proofs.PolynomialMixingBlocks
