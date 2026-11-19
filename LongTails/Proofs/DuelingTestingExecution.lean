import LongTails.Proofs.DuelingBinaryTesting
import LongTails.Proofs.HeavyTailedTapeExecution
import Mathlib.MeasureTheory.Constructions.UnitInterval

open MeasureTheory
open scoped unitInterval
open LongTails.Proofs.HeavyTailedProductProcess

namespace LongTails.Proofs.DuelingTestingExecution

open DuelingBinaryTesting OracleTemplate

noncomputable def uniforms : ProbabilityMeasure (ℕ → I) :=
  ⟨Measure.infinitePi fun _ : ℕ => (volume : Measure I), inferInstance⟩

noncomputable def bit (u v : I) : Bool := decide (v ≤ u)

lemma integral_bit (u : I) (a b : ℝ) :
    (∫ v : I, if bit u v then a else b) = mix u a b := by
  simp only [bit, decide_eq_true_eq]
  change (∫ v : I, (Set.Iic u).piecewise (fun _ => a) (fun _ => b) v) = _
  rw [integral_piecewise measurableSet_Iic (integrableOn_const (by simp))
    (integrableOn_const (by simp)), Set.compl_Iic]
  simp [Measure.real, ENNReal.toReal_ofReal u.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr u.property.2),mix]

noncomputable def oracle {Q : Type} (prob : Q → I) : Oracle Q Bool where
  Seed := fun _ => I
  law := uniforms
  answer := fun _ q z => bit (prob q.2) z

noncomputable def readout {S : Type*} (step : S → Bool → S) (p : S → I) (test : S → Bool) :
    ℕ → S → (ℕ → I) → ℝ
  | 0, s, _ => if test s then 1 else 0
  | n+1, s, ξ => readout step p test n (step s (bit (p s) (ξ 0))) (fun k => ξ (k+1))

lemma readout_mem {S : Type*} (step : S → Bool → S) (p : S → I) (test : S → Bool)
    (n : ℕ) (s : S) (ξ : ℕ → I) : readout step p test n s ξ ∈ Set.Icc 0 1 := by
  induction n generalizing s ξ with
  | zero => cases h : test s <;> simp [readout,h]
  | succ n ih => exact ih _ _

lemma readout_measurable {S : Type*} (step : S → Bool → S) (p : S → I) (test : S → Bool)
    (n : ℕ) (s : S) : Measurable (readout step p test n s) := by
  classical
  induction n generalizing s with
  | zero => exact measurable_const
  | succ n ih =>
    let tail := fun (ξ : ℕ → I) k => ξ (k+1)
    have ht : Measurable tail := Measurable.of_eval fun k => measurable_pi_apply _
    convert ((ih (step s true)).comp ht).ite
      (measurableSet_le (measurable_pi_apply 0) (measurable_const (a := p s)))
      ((ih (step s false)).comp ht) using 1
    funext ξ
    by_cases h : ξ 0 ≤ p s <;> simp [h, readout, bit, tail]
    all_goals infer_instance

lemma readout_integral {S : Type*} (step : S → Bool → S) (p : S → I) (test : S → Bool)
    (n : ℕ) (s : S) :
    (∫ ξ, readout step p test n s ξ ∂(uniforms : Measure _)) =
      acceptance step (fun s => (p s : ℝ)) test n s := by
  classical
  induction n generalizing s with
  | zero => simp [readout, acceptance]
  | succ n ih =>
    let F := fun (z : I × (ℕ → I)) => readout step p test n (step s (bit (p s) z.1)) z.2
    have hF : Measurable F := by
      convert ((readout_measurable step p test n (step s true)).comp measurable_snd).ite
        (measurableSet_le measurable_fst (measurable_const (a := p s)))
        ((readout_measurable step p test n (step s false)).comp measurable_snd) using 1
      funext z
      by_cases h : z.1 ≤ p s <;> simp [F, bit, h]
      all_goals infer_instance
    have hi : Integrable F ((volume : Measure I).prod (uniforms : Measure _)) :=
      Integrable.of_bound hF.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun z => by
        have hz := readout_mem step p test n (step s (bit (p s) z.1)) z.2
        exact (abs_of_nonneg hz.1).le.trans hz.2)
    have hsplit : MeasurePreserving (fun ξ : ℕ → I => (ξ 0,fun k => ξ (k+1)))
        (uniforms : Measure _) ((volume : Measure I).prod (uniforms : Measure _)) :=
      head_tail_preserving (volume : Measure I)
    have he := integral_map (μ := (uniforms : Measure _)) hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at he
    change (∫ ξ : ℕ → I, F (ξ 0, fun k => ξ (k+1)) ∂(uniforms : Measure (ℕ → I))) = _
    rw [← he, integral_prod _ hi]
    simp only [F,ih,acceptance]
    convert integral_bit (p s) (acceptance step (fun t => (p t : ℝ)) test n (step s true))
      (acceptance step (fun t => (p t : ℝ)) test n (step s false)) using 1
    apply integral_congr_ae
    filter_upwards [] with v
    cases bit (p s) v <;> rfl

lemma execute_readout {Q Y : Type} (A : Algorithm Q Bool Y) (p : Q → I) (test : Y → Bool)
    (n : ℕ) (seed : A.Seed) (ξ : ℕ → I) :
    (if test (execute (oracle p) A (fun _ => n) seed ξ) then (1 : ℝ) else 0) =
    readout A.update (fun s => p (A.query s).2) (fun s => test (A.output s)) n (A.initial seed) ξ := by
  rw [execute_indexed_of_answer (oracle p) A n seed ξ
    (fun k q => bit (p q.2) (ξ k)) (by intros; rfl)]
  let advance := fun sc : A.State × ℕ => (A.update sc.1 (bit (p (A.query sc.1).2) (ξ sc.2)), sc.2+1)
  have he (N : ℕ) (s : A.State) (i : ℕ) :
      (if test (A.output ((advance^[N]) (s,i)).1) then (1:ℝ) else 0) =
      readout A.update (fun s => p (A.query s).2) (fun s => test (A.output s)) N s
        (fun k => ξ (k+i)) := by
    induction N generalizing s i with
    | zero => rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply, readout]
      simpa [advance, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (advance (s,i)).1 (i+1)
  simpa using he n (A.initial seed) 0

end LongTails.Proofs.DuelingTestingExecution
