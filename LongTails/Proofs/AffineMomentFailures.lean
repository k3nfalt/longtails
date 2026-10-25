import LongTails.Proofs.AffineMomentProcess
import LongTails.Proofs.AffineMomentOracle
import LongTails.Proofs.RobustAdaptiveFailures

open MeasureTheory
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentProcess
open LongTails.Proofs.AffineMomentParameters

namespace LongTails.Proofs.AffineMomentFailures

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*}

noncomputable def failure (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) : ℝ := by
  classical
  exact if active t g s ∧ n = sampleSize t ∧ s.2.2.1 = false ∧
    (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8 < ‖pilotEstimate t
      (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t s.1 s.2.1) ξ) -
        g (point t s.1 s.2.1)‖ then 1 else 0

lemma failure_bounds (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) :
    0 ≤ failure t g oracle n s ξ ∧ failure t g oracle n s ξ ≤ 1 := by
  unfold failure
  split <;> norm_num

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma measurable_failure (t : Tuning) {g : E → E} (hg : Measurable g)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (failure t g oracle n)) := by
  classical
  have hpoint : Measurable (fun s : ProofState E => point t s.1 s.2.1) := by
    apply measurable_from_prod_countable_right
    intro k
    unfold point couplingPoint
    fun_prop
  have hy : Measurable (fun v : ProofState E × (Fin n → Ω) => point t v.1.1 v.1.2.1) :=
    hpoint.comp measurable_fst
  have hr := (measurable_replies ho n).comp (hy.prodMk measurable_snd)
  have hh := (measurable_pilotEstimate (E := E) t).comp hr
  unfold Function.uncurry failure
  apply Measurable.ite
  · exact ((measurable_active t hg).preimage measurable_fst).inter
      ((MeasurableSet.const (n = sampleSize t)).inter
        ((measurableSet_eq_fun (show Measurable (fun v : ProofState E × (Fin n → Ω) => v.1.2.2.1) by fun_prop)
          (measurable_const (a := false))).inter
          (measurableSet_lt (((hg.comp hy).norm.add_const (pilotRadius t)).div_const 8) (hh.sub (hg.comp hy)).norm)))
  · exact measurable_const
  · exact measurable_const

variable [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]

lemma failure_mean {t : Tuning} (ht : Valid t) {g : E → E}
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle))
    (hoi : ∀ x, Integrable (oracle x) P) (homean : ∀ x, (∫ ω, oracle x ω ∂P) = g x)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - g x‖ ^ t.p) P)
    (hom : ∀ x, (∫ ω, ‖oracle x ω - g x‖ ^ t.p ∂P) ≤ t.σ0 ^ t.p + t.σ ^ t.p * ‖g x‖ ^ t.p)
    (s : ProofState E) :
    (∫ ξ, failure t g oracle (sampleSize t) s ξ ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤
      (1 / 2 : ℝ) ^ pilotGroups t := by
  classical
  by_cases hs : active t g s ∧ s.2.2.1 = false
  · let y := point t s.1 s.2.1
    have hy : Measurable (oracle y) := ho.comp measurable_prodMk_left
    have hb := LongTails.Proofs.AffineMomentOracle.pilot_failure ht y (g y) hy (hoi y)
      (homean y) (hop y) (hom y)
    have hrep : Measurable (fun ξ : Fin (sampleSize t) → Ω =>
        OracleTemplate.RobustGeneralized.sampleReplies oracle y ξ) :=
      (measurable_replies ho (sampleSize t)).comp (measurable_const.prodMk measurable_id)
    have hh := (measurable_pilotEstimate (E := E) t).comp hrep
    have hset := measurableSet_lt (measurable_const (a := (‖g y‖ + pilotRadius t) / 8)) (hh.sub_const (g y)).norm
    have he : (fun ξ : Fin (sampleSize t) → Ω => failure t g oracle (sampleSize t) s ξ) =
        {ξ | (‖g y‖ + pilotRadius t) / 8 < ‖pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle y ξ) - g y‖}.indicator
          (fun _ => (1 : ℝ)) := by
      funext ξ
      simp only [failure, hs.1, hs.2, true_and, Set.indicator, Set.mem_ofPred_eq]
      rfl
    rw [he]
    have heint := integral_indicator_one (μ := Measure.pi fun _ : Fin (sampleSize t) => P) hset
    change (∫ ξ, {ξ | (‖g y‖ + pilotRadius t) / 8 < ‖pilotEstimate t
      (OracleTemplate.RobustGeneralized.sampleReplies oracle y ξ) - g y‖}.indicator 1 ξ
      ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤ _
    simp only [Function.comp_apply] at heint
    rw [heint]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hb |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  · have he : ∀ ξ : Fin (sampleSize t) → Ω, failure t g oracle (sampleSize t) s ξ = 0 := by
      intro ξ
      unfold failure
      split
      · rename_i h
        exact False.elim (hs ⟨h.1, h.2.2.1⟩)
      · rfl
    simp only [he, integral_zero]
    positivity

omit [CompleteSpace E] in
lemma accumulated_failure_bound (t : Tuning) {g : E → E} (hg : Measurable g)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle))
    (hbound : ∀ s : ProofState E,
      (∫ ξ, failure t g oracle (sampleSize t) s ξ ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤
        (1 / 2 : ℝ) ^ pilotGroups t) (m : ℕ) (s : ProofState E) :
    (Measure.infinitePi fun _ : ℕ => P) {ξ | 1 ≤ OracleTemplate.StochasticGeneralized.accumulated
      (fun _ => sampleSize t) (next t g oracle) (failure t g oracle) m s ξ} ≤
      ENNReal.ofReal ((m : ℝ) * (1 / 2 : ℝ) ^ pilotGroups t) := by
  exact OracleTemplate.RobustGradient.accumulated_failure_probability P measurable_const
    (measurable_next t hg ho) (measurable_failure t hg ho) (failure_bounds t g oracle) hbound m s

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma failure_zero_of_accumulated_lt (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (m : ℕ) (s : ProofState E) (ξ : ℕ → Ω)
    (h : OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
      (next t g oracle) (failure t g oracle) m s ξ < 1) (i : ℕ) (hi : i < m) :
    let v := OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t) (next t g oracle) s ξ i
    failure t g oracle (sampleSize t) v.1 (fun j => v.2 j) = 0 := by
  classical
  rw [OracleTemplate.StochasticGeneralized.accumulated_eq_sum] at h
  let v := OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t) (next t g oracle) s ξ
  have hm := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range m) => (failure_bounds t g oracle (sampleSize t)
      (v j).1 (fun k => (v j).2 k)).1) (Finset.mem_range.mpr hi)
  have hh := hm.trans_lt h
  dsimp only [v] at hh
  dsimp only
  unfold failure at hh ⊢
  split_ifs with hb
  · rw [ite_eq_left hb] at hh
    exact False.elim ((lt_irrefl (1 : ℝ)) hh)
  · rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma pilot_good_of_failure_zero (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (k : ℕ) (s : E × E) (hk : k < iterations t) (hx : ‖s.1‖ ≤ 4) (hz : ‖s.2‖ ≤ 1)
    (ξ : Fin (sampleSize t) → Ω)
    (hf : failure t g oracle (sampleSize t) (k, s, false, 0, false) ξ = 0) :
    ‖pilotEstimate t (OracleTemplate.RobustGeneralized.sampleReplies oracle (point t k s) ξ) -
      g (point t k s)‖ ≤ (‖g (point t k s)‖ + pilotRadius t) / 8 := by
  by_contra hb
  have hh := lt_of_not_ge hb
  simp [failure, active, hk, hx, hz, hh] at hf

end LongTails.Proofs.AffineMomentFailures
