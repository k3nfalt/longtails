import LongTails.Proofs.StrongGrowthAgdBridge
import Mathlib.Probability.ProductMeasure

namespace LongTails.Proofs.GatedEscapeStream

open MeasureTheory ProbabilityTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def zip (q : (ℕ → A) × (ℕ → B)) : ℕ → A × B := fun n => (q.1 n, q.2 n)

lemma zip_measurable : Measurable (zip (A := A) (B := B)) :=
  measurable_pi_iff.mpr fun n =>
    ((measurable_pi_apply n).comp measurable_fst).prodMk ((measurable_pi_apply n).comp measurable_snd)

theorem zip_preserving (π : Measure A) (γ : Measure B) [IsProbabilityMeasure π]
    [IsProbabilityMeasure γ] :
    MeasurePreserving zip ((Measure.infinitePi fun _ : ℕ => π).prod (Measure.infinitePi fun _ : ℕ => γ))
      (Measure.infinitePi fun _ : ℕ => π.prod γ) := by
  refine ⟨zip_measurable, ?_⟩
  refine Measure.eq_infinitePi _ (fun s t ht => ?_)
  rw [Measure.map_apply zip_measurable (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  set e := MeasurableEquiv.arrowProdEquivProdArrow A B s
  set R : (ℕ → A) × (ℕ → B) → (s → A) × (s → B) := fun q => (fun i => q.1 i, fun i => q.2 i) with hR
  have hRm : Measurable R := by rw [hR]; fun_prop
  have hpre : zip ⁻¹' ((s : Set ℕ).pi t) = R ⁻¹' (e.symm ⁻¹' (Set.univ.pi fun i : s => t i)) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_univ, true_implies, zip, hR]
    constructor
    · intro h i
      exact h i i.2
    · intro h i hi
      exact h ⟨i, hi⟩
  have hU : MeasurableSet (e.symm ⁻¹' (Set.univ.pi fun i : s => t i)) :=
    e.symm.measurable (MeasurableSet.univ_pi fun i => ht i)
  have hmap : ((Measure.infinitePi fun _ : ℕ => π).prod (Measure.infinitePi fun _ : ℕ => γ)).map R =
      (Measure.pi fun _ : s => π).prod (Measure.pi fun _ : s => γ) := by
    have h1 : (Measure.infinitePi fun _ : ℕ => π).map (fun x (i : s) => x i) = Measure.pi fun _ : s => π :=
      Measure.infinitePi_map_restrict (fun _ : ℕ => π) (I := s)
    have h2 : (Measure.infinitePi fun _ : ℕ => γ).map (fun x (i : s) => x i) = Measure.pi fun _ : s => γ :=
      Measure.infinitePi_map_restrict (fun _ : ℕ => γ) (I := s)
    rw [← h1, ← h2, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    rfl
  rw [hpre, ← Measure.map_apply hRm hU, hmap]
  have hmp := measurePreserving_arrowProdEquivProdArrow A B s (fun _ => π) (fun _ => γ)
  rw [← hmp.map_eq, Measure.map_apply e.measurable hU]
  have : e ⁻¹' (e.symm ⁻¹' (Set.univ.pi fun i : s => t i)) = Set.univ.pi fun i : s => t i := by
    ext q; simp
  rw [this, Measure.pi_pi]
  exact Finset.prod_coe_sort s (fun i => (π.prod γ) (t i))

end LongTails.Proofs.GatedEscapeStream
