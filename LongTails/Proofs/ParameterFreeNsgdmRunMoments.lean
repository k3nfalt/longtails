import LongTails.Proofs.ParameterFreeNsgdmRun
import Mathlib.Algebra.Order.Field.GeomSum
import LongTails.Proofs.ParameterFreeNsgdmMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ParameterFreeNsgdmRunMoments

open ParameterFreeNsgdmRun ParameterFreeNsgdmMoments

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma run_eq_trajectory (α η : ℝ) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (n : ℕ) :
    run α η g x0 ξ n =
      HeavyTailedProductProcess.trajectory (runStep α η g) n (x0, 0, 0) ξ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run, ih, HeavyTailedProductProcess.trajectory_succ_last]

omit [CompleteSpace E] in
lemma runStep_measurable {α η : ℝ} {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (runStep α η g)) := by
  unfold runStep mixStep
  apply Measurable.prodMk
  · apply Measurable.sub measurable_fst.fst
    apply Measurable.smul
    · apply Measurable.div measurable_const
      apply Measurable.norm
      apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      · exact hg.comp (measurable_fst.fst.prodMk measurable_snd)
      · exact (measurable_const.smul measurable_fst.snd.fst).add
          (measurable_const.smul (hg.comp (measurable_fst.fst.prodMk measurable_snd)))
    · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      · exact hg.comp (measurable_fst.fst.prodMk measurable_snd)
      · exact (measurable_const.smul measurable_fst.snd.fst).add
          (measurable_const.smul (hg.comp (measurable_fst.fst.prodMk measurable_snd)))
  · apply Measurable.prodMk
    · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      · exact hg.comp (measurable_fst.fst.prodMk measurable_snd)
      · exact (measurable_const.smul measurable_fst.snd.fst).add
          (measurable_const.smul (hg.comp (measurable_fst.fst.prodMk measurable_snd)))
    · exact (measurable_fst.snd.snd :
        Measurable fun x : (E × E × ℕ) × Ω => x.1.2.2).add measurable_const

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma noisePart_eq_timedSum (α η : ℝ) (g : E → Ω → E) (grad : E → E) (x0 : E) (ξ : ℕ → Ω)
    (t : ℕ) :
    noisePart α η g grad x0 ξ t =
      timedSum (runStep α η g) (fun s st ω => weight α t s • sampleNoise g grad st.1 ω) (t + 1) 0
        (x0, 0, 0) 0 ξ := by
  rw [timedSum_eq_sum, zero_add]
  unfold noisePart
  apply Finset.sum_congr rfl
  intro s _
  rw [zero_add, run_eq_trajectory]

lemma weight_nonneg {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (t s : ℕ) : 0 ≤ weight α t s := by
  have h1 : 0 ≤ 1 - α := by linarith
  unfold weight
  split_ifs <;> positivity

lemma weight_sum_rpow {α p : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hp : 1 ≤ p) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1), weight α t s ^ p ≤ (1 - α) ^ (p * t) + α ^ (p - 1) := by
  have h1 : 0 ≤ 1 - α := by linarith
  rw [Finset.sum_range_succ']
  simp only [weight, ↓reduceIte, Nat.succ_ne_zero]
  have hfirst : ((1 - α) ^ t) ^ p = (1 - α) ^ (p * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1, mul_comm]
  rw [hfirst, add_comm]
  gcongr
  have hterm : ∀ s ∈ Finset.range t, (α * (1 - α) ^ (t - (s + 1))) ^ p =
      α ^ p * ((1 - α) ^ p) ^ (t - (s + 1)) := by
    intro s _
    rw [Real.mul_rpow hα0.le (by positivity), ← Real.rpow_natCast ((1 - α) ^ p),
      ← Real.rpow_mul h1, ← Real.rpow_natCast, ← Real.rpow_mul h1,
      mul_comm (((t - (s + 1) : ℕ) : ℝ)) p]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hq0 : 0 ≤ (1 - α) ^ p := by positivity
  have hq1 : (1 - α) ^ p ≤ 1 - α := by
    calc (1 - α) ^ p ≤ (1 - α) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge' h1 (by linarith) zero_le_one hp
      _ = 1 - α := Real.rpow_one _
  have hgeom : ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ (t - (s + 1)) ≤ 1 / α := by
    have hre : ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ (t - (s + 1)) =
        ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ s := by
      calc ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ (t - (s + 1))
          = ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ (t - 1 - s) :=
            Finset.sum_congr rfl (fun s _ => by rw [Nat.sub_sub, add_comm])
        _ = ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ s :=
            Finset.sum_range_reflect (fun s => ((1 - α) ^ p) ^ s) t
    rw [hre]
    have hlt : (1 - α) ^ p < 1 := by linarith
    calc ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ s ≤ 1 / (1 - (1 - α) ^ p) := by
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := t) hq0 hlt
          simpa using this
      _ ≤ 1 / α := by
          apply one_div_le_one_div_of_le hα0
          linarith
  calc α ^ p * ∑ s ∈ Finset.range t, ((1 - α) ^ p) ^ (t - (s + 1)) ≤ α ^ p * (1 / α) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = α ^ (p - 1) := by
        rw [Real.rpow_sub hα0, Real.rpow_one]; ring

end LongTails.Proofs.ParameterFreeNsgdmRunMoments
