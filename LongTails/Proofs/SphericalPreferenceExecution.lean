import LongTails.Proofs.SphericalPreferenceIteration
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.GatedEscapeStream
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.SphericalPreferenceExecution

open OracleTemplate LongTails.Setups.SphericalRandomUtility LongTails.Algorithms.SphericalPreferenceDescent
open LongTails.Proofs.SphericalPreferenceIteration LongTails.Proofs.SphericalPreferenceOracle
open OracleTemplate.ContinuizedSimilarQuasar

noncomputable def gathered (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (a : Fin n → Sample p) : Acc p := iterateSamples (transition p n f F o) n (start p) a

noncomputable def returned (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (a : Fin n → Sample p) : Feasible p := output p n (gathered p n f F o a).2.1

lemma advance_eq (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (seed : ℕ → Draw p.d) (ξ : ℕ → Point p.d) (k j : ℕ) (s : Acc p) :
    let a : Fin k → Sample p := fun i => (seed (j+i.val),ξ (j+i.val))
    let A := method p n
    let t := iterateSamples (transition p n f F o) k s a
    StochasticGradient.advance (fun l q => A.update q (comparePair f (A.query q).2 (ξ l)))
      k j (seed,j,s.1.val,s.2.1) = (seed,j+k,t.1.val,t.2.1) := by
  induction k generalizing s j with
  | zero => rfl
  | succ k ih =>
    dsimp only [StochasticGradient.advance, iterateSamples]
    have h := ih (j+1) (transition p n f F o s (seed j,ξ j))
    simp only [method, transition, response, next, Fin.val_zero,Nat.add_zero,Fin.val_succ, Nat.add_assoc, Nat.add_comm 1,
      Nat.add_left_comm] at h ⊢
    convert h using 3 <;> rfl

lemma execute_eq (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (P : ProbabilityMeasure (ℕ → Point p.d)) (seed : ℕ → Draw p.d) (ξ : ℕ → Point p.d) :
    execute { Seed := fun _ => Point p.d, law := P, answer := fun _ (_,q) z => comparePair f q z }
      (method p n) (fun _ => n) seed ξ = returned p n f F o (fun i => (seed i,ξ i)) := by
  apply (StochasticGradient.execute_advance P (comparePair f) (method p n) n seed ξ).trans
  have hs : (method p n).initial seed = (seed,0,(start p).1.val,(start p).2.1) := by
    simp [method,start,project,clip]
  rw [hs, advance_eq p n f F o seed ξ n 0 (start p)]
  simp [method,returned,gathered]

lemma prefix_law (p : Params) (n : ℕ) (μ : ProbabilityMeasure (Point p.d))
    (P : ProbabilityMeasure (ℕ → Point p.d))
    (hi : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (z : ℕ → Point p.d) => z k)
      (μ : Measure _) (P : Measure _)) :
    MeasurePreserving (fun q : (ℕ → Draw p.d) × (ℕ → Point p.d) => fun i : Fin n => (q.1 i,q.2 i))
      ((Measure.infinitePi fun _ : ℕ => (drawLaw p n : Measure (Draw p.d))).prod (P : Measure (ℕ → Point p.d))) (Measure.pi fun _ : Fin n => (sampleLaw p n μ : Measure _)) := by
  have he := hi.independent.map_fun_eq_infinitePi_map hi.measurable
  have hP : (P : Measure _) = Measure.infinitePi (fun _ : ℕ => (μ : Measure (Point p.d))) := by
    rw [show (fun (ω : ℕ → Point p.d) i => ω i) = id by rfl, Measure.map_id] at he
    simpa only [hi.marginal] using he
  rw [hP]
  exact (StochasticGeneralized.prefix_preserving ((drawLaw p n : Measure (Draw p.d)).prod (μ : Measure (Point p.d))) n).comp
    (LongTails.Proofs.GatedEscapeStream.zip_preserving (drawLaw p n : Measure (Draw p.d)) (μ : Measure (Point p.d)))

lemma expected_output (p : Params) [NeZero p.d] {n : ℕ} (hn : 0 < n) (hd : 2 ≤ p.d)
    (hR : 0 < p.R) (hB : 0 < p.B) (μ : ProbabilityMeasure (Point p.d))
    (hs : Spherical (μ : Measure (Point p.d))) (hq : 1/2 ≤ (μ : Measure (Point p.d)).real (closedBall 0 (2*p.B)))
    (f F : Point p.d → ℝ) (he : EqOn f F (closedBall 0 p.R)) (hL : LipschitzWith ⟨p.B,hB.le⟩ F)
    (hc : ConvexOn ℝ (closedBall 0 p.R) F) (o : Feasible p) (hmin : IsMinOn F (closedBall 0 p.R) o.val)
    (hm : Measurable (Function.uncurry (comparePair (p := p) f))) :
    let P := Measure.pi (fun _ : Fin n => (sampleLaw p n μ : Measure (Sample p)))
    let loss := fun a => F (returned p n f F o a).val - F o.val
    Measurable loss ∧ Integrable loss P ∧
      (∫ a, loss a ∂P) ≤ 672*p.B*Real.sqrt p.d*p.R/Real.sqrt n := by
  let η := stepSize p n
  let scale := 2*η/(192*p.B*Real.sqrt p.d)
  let P := Measure.pi (fun _ : Fin n => (sampleLaw p n μ : Measure (Sample p)))
  let acc := gathered p n f F o
  let loss := fun a => F (returned p n f F o a).val - F o.val
  have ht := LongTails.Proofs.SphericalPreferenceStep.tuning p hn hd hR
  have hds : 0 < Real.sqrt p.d := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos p.d)
  have hscale : 0 < scale := div_pos (mul_pos (by norm_num) ht.1) (by positivity)
  have htr := transition_measurable p n f F o hm hL.continuous.measurable
  have hacc : Measurable acc := (GapStrongGrowth.iterateSamples_measurable htr n).comp
    (measurable_const.prodMk measurable_id)
  have hp : Measurable (project p) := (measurable_clip (E := Point p.d) p.R).subtype_mk
  have hret : Measurable (returned p n f F o) := hp.comp ((measurable_snd.comp hacc).fst.const_smul (n : ℝ)⁻¹)
  have hlm : Measurable loss := (hL.continuous.measurable.comp (measurable_subtype_coe.comp hret)).sub_const _
  have hli : Integrable loss P := by
    apply Integrable.of_bound hlm.aestronglyMeasurable (p.B*(2*p.R))
    filter_upwards [] with a
    let v := returned p n f F o a
    have h := hL.dist_le_mul v.val o.val
    rw [Real.dist_eq,dist_eq_norm] at h
    apply h.trans (mul_le_mul_of_nonneg_left _ hB.le)
    exact (norm_sub_le _ _).trans (by simpa only [two_mul] using add_le_add (mem_closedBall_zero_iff.mp v.property) (mem_closedBall_zero_iff.mp o.property))
  have hpot := GapStrongGrowth.iterateSamples_measurable_integral htr (sampleLaw p n μ)
    (potential p n o) (by unfold potential; fun_prop) (fun s => by
      change 0 ≤ ‖s.1.val-o.val‖^2+scale*(s.2.2 : ℝ)
      positivity) (q := 1) (r := 6*η^2) zero_le_one (fun s => by
        simpa only [one_mul] using potential_step p hn hd hR hB μ hs hq f F he hL hc o hmin hm s) n (start p)
  have hle (a) : scale*(n : ℝ)*loss a ≤ potential p n o (acc a) := by
    obtain ⟨y, hy, hz⟩ := history p n f F o hmin n (start p) a
    change (acc a).2.1 = 0 + _ at hy
    change ((acc a).2.2 : ℝ) = 0 + _ at hz
    rw [zero_add] at hy hz
    have hJ := jensen_output p F hc o hn y
    have hout : (returned p n f F o a).val = (output p n (∑ i, (y i).val)).val := by rw [returned]; change (output p n (acc a).2.1).val = _; rw [hy]
    change _ ≤ ‖(acc a).1.val-o.val‖^2 + scale*((acc a).2.2 : ℝ)
    rw [hz, mul_assoc]
    apply (mul_le_mul_of_nonneg_left (show (n:ℝ)*loss a ≤ _ by simpa only [loss,hout] using hJ) hscale.le).trans
    linarith only [sq_nonneg ‖(acc a).1.val-o.val‖]
  have hh := integral_mono (hli.const_mul (scale*n)) hpot.1 hle
  rw [integral_const_mul] at hh
  have hstart : potential p n o (start p) ≤ (p.R : ℝ)^2 := by
    simpa [potential,start,project,clip] using pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp o.property) 2
  have hb : (∫ a, potential p n o (acc a) ∂P) ≤ p.R^2 + 6*η^2*n := by
    have hh' := hpot.2
    simp only [one_pow,one_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hh'
    exact hh'.trans (add_le_add hstart le_rfl)
  refine ⟨hlm,hli,?_⟩
  have hsN := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have he' : η^2*(n : ℝ) = (p.R : ℝ)^2 := by
    dsimp [η,stepSize]
    rw [div_pow]
    field_simp [hspos.ne']
    nlinarith only [hsN]
  have hp' := hh.trans hb
  have hnum : scale*(n : ℝ)*(672*p.B*Real.sqrt p.d*p.R/Real.sqrt n) = 7*(p.R : ℝ)^2 := by
    dsimp [scale,η,stepSize]
    field_simp [hspos.ne', hB.ne', hds.ne']
    ring_nf
    rw [hsN]
  change (∫ a, loss a ∂P) ≤ _
  apply le_of_mul_le_mul_left _ (mul_pos hscale (Nat.cast_pos.mpr hn))
  rw [hnum]
  linarith only [hp',he']

lemma enough_calls (p : Params) (hd : 2 ≤ p.d) (hB : 0 < p.B) (hR : 0 < p.R) (he : 0 < p.ε)
    {n : ℕ} (hn : (p.d : ℝ)*(672*p.B*p.R/p.ε)^2 ≤ n) :
    0 < n ∧ 672*p.B*Real.sqrt p.d*p.R/Real.sqrt n ≤ p.ε := by
  have hr : 0 < (p.R : ℝ) := hR
  have hd' : 0 < (p.d : ℝ) := by exact_mod_cast (show 0 < p.d by omega)
  have hn' : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hn
  have h := Real.sqrt_le_sqrt hn
  rw [Real.sqrt_mul hd'.le, Real.sqrt_sq (by positivity)] at h
  refine ⟨Nat.cast_pos.mp hn', (div_le_iff₀ (Real.sqrt_pos.mpr hn')).mpr ?_⟩
  have heq : 672*p.B*Real.sqrt p.d*p.R = (Real.sqrt p.d*(672*p.B*p.R/p.ε))*p.ε := by
    field_simp
  rw [heq, mul_comm p.ε]
  exact mul_le_mul_of_nonneg_right h he.le

end LongTails.Proofs.SphericalPreferenceExecution
