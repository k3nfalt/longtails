import LongTails.Proofs.PolynomialMixingSelectionLaw
import LongTails.Proofs.PolynomialMixingBudget
import LongTails.Proofs.ValidatedHessianSampling

open MeasureTheory

namespace LongTails.Proofs.PolynomialMixingSampling

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingTraining LongTails.Proofs.PolynomialMixingAccuracy
open LongTails.Proofs.PolynomialMixingExecution LongTails.Proofs.PolynomialMixingSelectionLaw
open LongTails.Proofs.PolynomialMixingBlocks PolynomialMixingBudget

def extend {n : ℕ} (v : Fin n → ℝ) : Path := fun i => if h : i < n then v ⟨i,h⟩ else 0

def trim (n : ℕ) (z : Path) : Path := extend (past n z)

lemma measurable_extend (n : ℕ) : Measurable (@extend n) :=
  Measurable.of_eval fun i => by by_cases h : i < n <;> simp [extend, h, measurable_pi_apply]

lemma measurable_trim (n : ℕ) : Measurable (trim n) :=
  (measurable_extend n).comp (by unfold past; fun_prop)

lemma measurable_slice (gap call : ℕ) : Measurable (slice gap call) := by unfold slice; fun_prop

variable {q : Params} {g : Point q → ℝ → Space q}

lemma state_congr {z w : Path} (n : ℕ) (he : ∀ i < n, z i = w i) : state g n z = state g n w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [state_succ, state_succ, ih (fun i hi => he i (by omega)), he n (by omega)]

lemma average_trim (n : ℕ) (z : Path) : average g n (trim n z) = average g n z := by
  unfold PolynomialMixingTraining.average; rw [state_congr (w := z) n (fun i hi => by simp [trim, extend, past, hi])]

lemma score_trim (n : ℕ) (z : Path) (x : Point q) : score g x n (trim n z) = score g x n z := by
  unfold score; congr 1
  exact Finset.sum_congr rfl fun i hi => by simp [trim, extend, past, Finset.mem_range.mp hi]

lemma selected_trim (c : Schedule) (w : Fin c.trials → Fin (c.trials+1) → Path) :
    selected g c (fun i j => trim c.samples (w i j)) = selected g c w := by
  simp [selected, trial, average_trim, score_trim]

noncomputable def blockLaw (P : ProbabilityMeasure Path) (c : Schedule) : ProbabilityMeasure Path :=
  P.map (trim c.samples ∘ slice c.innerSkip 0)

lemma inner_transfer (P : ProbabilityMeasure Path) (c : Schedule) {τ β : ℝ}
    (hr : AbsolutelyRegular P τ β) :
    SetError (blockLaw P c : Measure Path)
      ((Measure.infinitePi (fun _ : ℕ => (P : Measure Path).map (fun z => z 0))).map (trim c.samples))
      (c.samples * (1 + ((c.innerSkip+1 : ℕ) : ℝ) / τ) ^ (-β)) := by
  let π := (P : Measure Path).map (fun z => z 0)
  let : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply 0).aemeasurable).mpr inferInstance
  have hh := block_error P hr (h := 0) (read := fun a => a 0) (measurable_pi_apply 0)
    (c.innerSkip+1) c.samples
  have hh' := setError_map (measurable_extend c.samples) hh
  rw [Measure.map_map (measurable_extend _) (measurable_blocks (measurable_pi_apply 0) _ _)] at hh'
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving π c.samples
  have he : (Measure.infinitePi (fun _ : ℕ => π)).map (trim c.samples) =
      (Measure.pi (fun _ : Fin c.samples => π)).map extend := by
    rw [← hpre.map_eq, Measure.map_map (measurable_extend _) hpre.measurable]; rfl
  change SetError _ ((Measure.infinitePi (fun _ : ℕ => π)).map _) _
  rw [he]
  convert hh' using 2
  · change (P : Measure Path).map _ = _
    congr 1; funext z; apply congrArg (@extend c.samples); funext i
    simp [past, blocks, slice, Nat.mul_comm]
  · rfl

def flatten (c : Schedule) (v : Fin (c.trials*(c.trials+1)) → Path)
    (i : Fin c.trials) (j : Fin (c.trials+1)) : Path :=
  v (finProdFinEquiv (i,j))

lemma flatten_law (Q : ProbabilityMeasure Path) (c : Schedule) :
    (Measure.pi (fun _ : Fin (c.trials*(c.trials+1)) => (Q : Measure Path))).map (flatten c) =
      Measure.pi (fun _ : Fin c.trials => Measure.pi fun _ : Fin (c.trials+1) => (Q : Measure Path)) := by
  have hp := OracleTemplate.StochasticGeneralized.prefix_preserving (Q : Measure Path) (c.trials*(c.trials+1))
  rw [← hp.map_eq, Measure.map_map (by unfold flatten; fun_prop) hp.measurable]
  convert (ValidatedHessianSampling.finite_blocks_preserving (Q : Measure Path) c.trials (c.trials+1)).map_eq using 2
  funext z i j
  simp [flatten, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

lemma outer_transfer (P : ProbabilityMeasure Path) (c : Schedule) {τ β : ℝ}
    (hr : AbsolutelyRegular P τ β) :
    SetError ((P : Measure Path).map (fun z i j => trim c.samples (observations c z i j)))
      (Measure.pi (fun _ : Fin c.trials => Measure.pi fun _ : Fin (c.trials+1) => (blockLaw P c : Measure Path)))
      ((c.trials*(c.trials+1) : ℕ) * (1 + (c.outerSkip : ℝ)/τ) ^ (-β)) := by
  let h := (c.innerSkip+1)*c.samples
  let read := fun (a : Fin (h+1) → ℝ) => extend (fun i : Fin c.samples =>
    a ⟨(c.innerSkip+1)*i.val, by dsimp [h]; have := Nat.mul_le_mul_left (c.innerSkip+1) i.isLt.le; omega⟩)
  have hm : Measurable read := (measurable_extend _).comp (Measurable.of_eval fun i => measurable_pi_apply _)
  have hh := block_error P hr hm c.outerSkip (c.trials*(c.trials+1))
  have he := setError_map (f := flatten c) (by unfold flatten; fun_prop) hh
  rw [Measure.map_map (by unfold flatten; fun_prop) (measurable_blocks hm _ _)] at he
  have hQ : (P : Measure Path).map (read ∘ past (h+1)) = (blockLaw P c : Measure Path) := by
    change _ = (P : Measure Path).map _
    congr 1; funext z; dsimp only [Function.comp_apply, read, trim]
    apply congrArg (@extend c.samples); funext i
    simp [slice, past]
  simp_rw [hQ] at he
  rw [flatten_law] at he
  convert he using 2
  funext z i j; dsimp only [trim, flatten, Function.comp_apply, blocks, read]; apply congrArg (@extend c.samples); funext a
  simp [past, observations, slice, blockCost, h, finProdFinEquiv,
    Nat.mul_comm, Nat.add_comm]

end LongTails.Proofs.PolynomialMixingSampling
