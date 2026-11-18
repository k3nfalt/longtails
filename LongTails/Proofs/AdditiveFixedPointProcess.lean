import LongTails.Proofs.AdditiveFixedPointNoise
import LongTails.Proofs.HeavyTailedProductProcess
import LongTails.Proofs.SgdExecution
import LongTails.Setups.AdditiveCubeFixedPoint

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointProcess

open HeavyTailedProductProcess AdditiveFixedPointGaussian AdditiveFixedPointNoise
open LongTails.Setups.AdditiveCubeFixedPoint OracleTemplate

noncomputable def average {S E : Type*} [MeasurableSpace E] (μ : Measure E)
    (step : S → E → S) (pay : S → ℝ≥0∞) (n : ℕ) (s : S) : ℝ≥0∞ :=
  ∫⁻ ξ, pay (trajectory step n s ξ) ∂Measure.infinitePi (fun _ : ℕ => μ)

lemma average_measurable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {step : S → E → S} {pay : S → ℝ≥0∞}
    (hs : Measurable step.uncurry) (hp : Measurable pay) (n : ℕ) :
    Measurable (average μ step pay n) :=
  Measurable.lintegral_prod_right (f := fun s ξ => pay (trajectory step n s ξ))
    (hp.comp (trajectory_measurable hs n))

lemma average_zero {S E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (step : S → E → S) (pay : S → ℝ≥0∞) (s : S) : average μ step pay 0 s = pay s := by
  simp [average, trajectory]

lemma average_succ {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {step : S → E → S} {pay : S → ℝ≥0∞} (hs : Measurable step.uncurry)
    (hp : Measurable pay) (n : ℕ) (s : S) :
    average μ step pay (n + 1) s = ∫⁻ z, average μ step pay n (step s z) ∂μ := by
  let F : E × (ℕ → E) → ℝ≥0∞ := fun z => pay (trajectory step n (step s z.1) z.2)
  have hF : Measurable F := hp.comp ((trajectory_measurable hs n).comp
    (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd))
  change (∫⁻ ξ : ℕ → E, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => μ)) = _
  rw [(head_tail_preserving μ).lintegral_comp hF, lintegral_prod _ hF.aemeasurable]
  rfl

lemma average_gaussian {S : Type*} [MeasurableSpace S] {d : ℕ} {v : NNReal} (hv : v ≠ 0)
    {mean : S → Fin d → ℝ} {update : S → (Fin d → ℝ) → S} {pay : S → ℝ≥0∞}
    (hm : Measurable mean) (hu : Measurable update.uncurry) (hp : Measurable pay)
    (n : ℕ) (s : S) :
    average (law v 0) (fun x z => update x (mean x + z)) pay n s =
      run v mean update pay n s := by
  have hs : Measurable (fun p : S × (Fin d → ℝ) => update p.1 (mean p.1 + p.2)) :=
    hu.comp (measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd))
  induction n generalizing s with
  | zero => exact average_zero _ _ _ _
  | succ n ih =>
    rw [average_succ _ hs hp]
    simp_rw [ih]
    have hf : Measurable (fun z => run v mean update pay n (update s z)) :=
      (run_measurable v hm hu hp n).comp (hu.comp measurable_prodMk_left)
    exact run_shift hv (mean s) hf

lemma average_add {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {step : S → E → S} {pay : S → ℝ≥0∞} (hs : Measurable step.uncurry)
    (hp : Measurable pay) (n m : ℕ) (s : S) :
    average μ step pay (n + m) s = average μ step (average μ step pay m) n s := by
  induction n generalizing s with
  | zero => simp [average_zero]
  | succ n ih =>
    rw [Nat.succ_add, average_succ μ hs hp, average_succ μ hs (average_measurable μ hs hp m)]
    simp_rw [ih]

lemma advance_trajectory {S E : Type*} (step : S → E → S) (n offset : ℕ) (s : S) (ξ : ℕ → E) :
    StochasticGradient.advance (fun j x => step x (ξ j)) n offset s =
      trajectory step n s (fun i => ξ (offset + i)) := by
  induction n generalizing offset s with
  | zero => rfl
  | succ n ih =>
    rw [StochasticGradient.advance, ih, trajectory]
    simp [Nat.add_left_comm, Nat.add_comm]

lemma execute_trajectory {p : Params} (P : ProbabilityMeasure (ℕ → Point p))
    (T : Cube p → Cube p) (A : Algorithm (Cube p) (Point p) (Cube p)) (n : ℕ) (s : A.Seed)
    (ξ : ℕ → Point p) :
    execute { Seed := fun _ => Point p, law := P, answer := fun _ (_, x) z => (T x).val + z } A (fun _ => n) s ξ =
    A.output (trajectory (fun x z => A.update x ((T (A.query x).2).val + z)) n (A.initial s) ξ) := by
  rw [StochasticGradient.execute_advance P (fun x z => (T x).val + z)]
  simpa using congrArg A.output (advance_trajectory
    (fun x z => A.update x ((T (A.query x).2).val + z)) n 0 (A.initial s) ξ)

noncomputable def stateLaw {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (π : ProbabilityMeasure S) (μ : Measure E) [IsProbabilityMeasure μ]
    (step : S → E → S) (n : ℕ) : ProbabilityMeasure S :=
  ProbabilityMeasure.map
    ⟨(π : Measure S).prod (Measure.infinitePi fun _ : ℕ => μ), inferInstance⟩
    (trajectory step n).uncurry

lemma stateLaw_integral {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (π : ProbabilityMeasure S) (μ : Measure E) [IsProbabilityMeasure μ]
    {step : S → E → S} {pay : S → ℝ≥0∞} (hs : Measurable step.uncurry) (hp : Measurable pay)
    (n : ℕ) : (∫⁻ s, pay s ∂(stateLaw π μ step n : Measure S)) =
      ∫⁻ s, average μ step pay n s ∂(π : Measure S) := by
  change (∫⁻ s, pay s ∂Measure.map (trajectory step n).uncurry
    ((π : Measure S).prod (Measure.infinitePi fun _ : ℕ => μ))) = _
  rw [lintegral_map hp (trajectory_measurable hs n)]
  exact lintegral_prod _ (hp.comp (trajectory_measurable hs n)).aemeasurable

lemma integrated_compare {S : Type*} [MeasurableSpace S] {d : ℕ} (π : ProbabilityMeasure S)
    {v : NNReal} (hv : v ≠ 0) {a b : S → Fin d → ℝ} (ha : Measurable a) (hb : Measurable b)
    {update : S → (Fin d → ℝ) → S} (hu : Measurable update.uncurry)
    {pay : S → ℝ≥0∞} (hp : Measurable pay) (hp2 : ∀ s, pay s ^ 2 = pay s)
    {B : ℝ} (he : ∀ s, ∑ i, (b s i - a s i) ^ 2 / v ≤ B) (n : ℕ) :
    (∫⁻ s, average (law v 0) (fun x z => update x (b x + z)) pay n s ∂(π : Measure S)) ^ 2 ≤
      ENNReal.ofReal (Real.exp B) ^ n *
        ∫⁻ s, average (law v 0) (fun x z => update x (a x + z)) pay n s ∂(π : Measure S) := by
  simp_rw [average_gaussian hv hb hu hp, average_gaussian hv ha hu hp]
  have hcs := integral_compare (μ := (π : Measure S)) (p := fun _ => 1) (q := fun _ => 1)
    (r := fun _ => 1) (C := 1) (run_measurable v hb hu hp n) measurable_const
    measurable_const (by simp) (by simp)
  simp only [one_mul] at hcs
  apply hcs.trans
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_mono
  intro s
  simpa only [hp2] using adaptive_compare hv hb hu hp he n s

end LongTails.Proofs.AdditiveFixedPointProcess
