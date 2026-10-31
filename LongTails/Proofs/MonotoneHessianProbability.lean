import LongTails.Proofs.MonotoneHessianIteration
import Mathlib.MeasureTheory.Constructions.Pi

namespace LongTails.Proofs.MonotoneHessianProbability

open MeasureTheory
open scoped ENNReal

variable {Ω S : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def badRun (step : S → Ω → S) (bad : S → Ω → Prop) : (n : ℕ) → S → (Fin n → Ω) → Prop
  | 0, _, _ => False
  | n + 1, st, seeds => bad st (seeds 0) ∨ badRun step bad n (step st (seeds 0)) (fun j => seeds j.succ)

lemma adaptive_failure (Q : Measure Ω) [IsProbabilityMeasure Q]
    (step : S → Ω → S) (bad : S → Ω → Prop) (valid : S → Prop)
    (hvalid : ∀ st, valid st → ∀ z, valid (step st z)) {η : ℝ} (hη : 0 ≤ η)
    (hbad : ∀ st, valid st → Q {z | bad st z} ≤ ENNReal.ofReal η)
    (n : ℕ) (st : S) (hs : valid st) :
    (Measure.pi fun _ : Fin n => Q) {seeds | badRun step bad n st seeds} ≤ ENNReal.ofReal (n * η) := by
  classical
  induction n generalizing st with
  | zero => simp [badRun]
  | succ n ih =>
    let P := Measure.pi fun _ : Fin n => Q
    let A : Set (Ω × (Fin n → Ω)) := {z | bad st z.1}
    let B : Set (Ω × (Fin n → Ω)) := {z | badRun step bad n (step st z.1) z.2}
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) 0
    have he : {seeds : Fin (n + 1) → Ω | badRun step bad (n + 1) st seeds} = e ⁻¹' (A ∪ B) := by
      ext seeds
      simp [badRun, e, A, B, MeasurableEquiv.piFinSuccAbove]
      rfl
    have hA : (Q.prod P) A = Q {z | bad st z} := by
      have heq : A = {z | bad st z} ×ˢ Set.univ := by ext z; simp [A]
      rw [heq, Measure.prod_prod]
      simp
    have hB : (Q.prod P) B ≤ ENNReal.ofReal (n * η) := by
      rw [Measure.prod_apply (Set.toFinite B).measurableSet]
      calc
        _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (n * η) ∂Q := lintegral_mono (fun z => ih (step st z) (hvalid st hs z))
        _ = _ := by simp
    rw [he, hpres.measure_preimage (Set.toFinite (A ∪ B)).measurableSet.nullMeasurableSet]
    calc
      _ ≤ (Q.prod P) A + (Q.prod P) B := measure_union_le A B
      _ ≤ ENNReal.ofReal η + ENNReal.ofReal (n * η) := add_le_add (hA ▸ hbad st hs) hB
      _ = ENNReal.ofReal ((n + 1 : ℕ) * η) := by
        rw [← ENNReal.ofReal_add hη (by positivity)]
        congr 1
        push_cast
        ring

end LongTails.Proofs.MonotoneHessianProbability
