import LongTails.Proofs.DuelingFlatTransfer
import LongTails.Proofs.DuelingSignGeometry
import LongTails.Proofs.DuelingTestingExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped unitInterval
open LongTails.Setups.StronglyConvexDueling

namespace LongTails.Proofs.DuelingSignOracle

open DuelingSignFamily DuelingFlatTransfer DuelingTestingExecution

abbrev Params := LongTails.Setups.FlatTransferDueling.Params

def flip {d : ℕ} (i : Fin d) (θ : Fin d → Bool) := Function.update θ i (!θ i)

lemma flip_at {d : ℕ} (i : Fin d) (θ : Fin d → Bool) : flip i θ i = !θ i := by simp [flip]

lemma flip_involutive {d : ℕ} (i : Fin d) : Function.Involutive (flip i) := by
  intro θ
  ext k
  by_cases hk : k = i
  · subst k; simp [flip]
  · simp [flip, Function.update_of_ne hk]

lemma loss_flip {d : ℕ} (h : ℝ) (θ : Fin d → Bool) (i : Fin d) (x : Point d) :
    |loss h θ x - loss h (flip i θ) x| ≤ h^2 / 2 := by
  classical
  unfold loss FiniteSumNondualLowerComponents.separableEnergy
  rw [← Finset.sum_sub_distrib,Finset.sum_eq_single i]
  · dsimp only
    rw [flip_at]
    have hb (b : Bool) : |sign b * h^2/4 * Real.sin (phase h (x i) b)| ≤ h^2/4 := by
      have he : |sign b| = 1 := by cases b <;> norm_num [sign]
      rw [abs_mul,abs_div,abs_mul,he,one_mul,abs_of_nonneg (sq_nonneg _),abs_of_pos (by norm_num : (0:ℝ)<4)]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (phase h (x i) b)) (by positivity : 0 ≤ h^2/4)
    unfold profile
    rw [sub_sub_sub_cancel_left]
    exact (abs_sub _ _).trans (by linarith [hb (!θ i),hb (θ i)])
  · intro j _ hj
    simp [flip,Function.update_of_ne hj]
  · simp

noncomputable def chance (p : Params) (θ : Fin p.d → Bool) (q : Ball p.d × Ball p.d) : I :=
  let t := loss (scale p) θ q.1.val - loss (scale p) θ q.2.val
  ⟨(1+link p.j t)/2, by
    obtain ⟨ha,hb⟩ := abs_le.mp (link_bound p.j t)
    exact ⟨by linarith,by linarith⟩⟩

lemma chance_range (p : Params) (θ : Fin p.d → Bool) (q : Ball p.d × Ball p.d) :
    (chance p θ q : ℝ) ∈ Set.Icc (1/4) (3/4) := by
  have h := abs_le.mp (link_bound p.j (loss (scale p) θ q.1.val - loss (scale p) θ q.2.val))
  change (1/4:ℝ) ≤ (1+_)/2 ∧ (1+_)/2 ≤ 3/4
  constructor <;> linarith [h.1,h.2]

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma chance_measurable {p : Params} (hp : 0 < p.ε) (θ : Fin p.d → Bool) :
    Measurable (chance p θ) := by
  have hf : Continuous (loss (scale p) θ) := continuous_iff_continuousAt.mpr fun x =>
    (gradient_loss (scale_pos hp) θ x).continuousAt
  have hl : Continuous (link p.j) := continuous_iff_continuousAt.mpr fun t =>
    (derivative p.j t).continuousAt
  apply Measurable.subtype_mk
  fun_prop

lemma chance_flip (p : Params) (θ : Fin p.d → Bool) (i : Fin p.d) (q : Ball p.d × Ball p.d) :
    |(chance p θ q : ℝ) - (chance p (flip i θ) q : ℝ)| ≤
      (2*(p.j:ℝ)+1)*scale p^2 / 8 := by
  let h := scale p
  let t (b : Fin p.d → Bool) := loss h b q.1.val - loss h b q.2.val
  have hdiff : |t θ - t (flip i θ)| ≤ h^2 := by
    rw [show t θ-t (flip i θ) = (loss h θ q.1.val - loss h (flip i θ) q.1.val) -
      (loss h θ q.2.val - loss h (flip i θ) q.2.val) by unfold t; ring]
    exact (abs_sub _ _).trans (by linarith [loss_flip h θ i q.1.val, loss_flip h θ i q.2.val])
  let C : NNReal := ⟨(2*(p.j:ℝ)+1)/4,by positivity⟩
  have hL : LipschitzWith C (link p.j) := lipschitzWith_of_nnnorm_deriv_le
    (fun t => (derivative p.j t).differentiableAt) (fun t => by
      rw [(derivative p.j t).deriv]
      change |gain p.j t| ≤ _
      rw [abs_of_nonneg (gain_nonneg _ _)]
      exact gain_le _ _)
  have hl := hL.dist_le_mul (t θ) (t (flip i θ))
  change |link p.j (t θ) - link p.j (t (flip i θ))| ≤ ((2*(p.j:ℝ)+1)/4)*|t θ-t (flip i θ)| at hl
  change |(1+link p.j (t θ))/2-(1+link p.j (t (flip i θ)))/2| ≤ _
  rw [← sub_div, add_sub_add_left_eq_sub, abs_div]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 2*(p.j:ℝ)+1 by positivity)]

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace in
lemma admissible {p : Params} (hp : 0 < p.ε ∧ p.ε ≤ 1/64) (θ : Fin p.d → Bool) :
    LongTails.Setups.FlatTransferDueling.spec.admissible p (loss (scale p) θ)
      (oracle (chance p θ)) := by
  refine ⟨objective hp θ, link p.j, transfer p, I, inferInstance,
    ⟨volume,inferInstance⟩, uniforms, (fun q z => bit (chance p θ q) z),
    OracleTemplate.StochasticGeneralized.infinitePi_iid volume, ?_, ?_, rfl⟩
  · change Measurable (fun z : (Ball p.d × Ball p.d) × I => bit (chance p θ z.1) z.2)
    unfold bit
    apply measurable_to_bool
    simp only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    exact measurableSet_le measurable_snd ((chance_measurable hp.1 θ).comp measurable_fst)
  · intro q
    change (∫ z : I, if bit (chance p θ q) z then (1:ℝ) else -1) = _
    rw [integral_bit]
    unfold DuelingBinaryTesting.mix chance
    ring_nf

end LongTails.Proofs.DuelingSignOracle
