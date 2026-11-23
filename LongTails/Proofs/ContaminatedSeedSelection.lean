import LongTails.Proofs.ContaminatedValidationState

namespace LongTails.Proofs.ContaminatedSeedSelection

open MeasureTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (resolution iterations)
open ContaminatedParallelSampling ContaminatedParallelHistory ContaminatedParallelFailures ContaminatedTrainingGeometry
open ContaminatedTrainingHistory ContaminatedValidationCalendar ContaminatedTreeProbability
open scoped Classical
variable {p : Params}

noncomputable def loss (D : Data p) (s : Samples p) := mass (fun t => weight p (level p t)) (bad D (trainOp p)) (count p) s

lemma loss_measurable (D : Data p) : Measurable (loss D) :=
  mass_measurable _ _ _ (fun i _ => past_le p _ _ (bad_measurable D (trainOp p) i))

lemma point_measurable (D : Data p) (j : ℕ) : Measurable (fun s => point D s j) := by
  have h := (measurable_state p D.g (fun i => (D.clean i).measurable) (trainOp p) (count p)).history j
  exact h.mono (past_le p _) le_rfl

noncomputable def single (p : Params) : Measure (Fin (iterations (network p))) := by
  letI : NeZero (iterations (network p)) := ⟨by unfold iterations; positivity⟩
  exact (PMF.uniformOfFintype (Fin (iterations (network p)))).toMeasure

instance single_probability (p : Params) : IsProbabilityMeasure (single p) := by unfold single; infer_instance

noncomputable def seeds (p : Params) : Measure (Seed p) := Measure.pi (fun _ : Fin (confidence p) => single p)
instance seeds_probability (p : Params) : IsProbabilityMeasure (seeds p) := by unfold seeds; infer_instance

lemma fraction (D : Data p) (s : Samples p) (hl : loss D s < 1) :
    single p {j | p.ε/2 < ‖D.G (point D s j)‖} ≤ ENNReal.ofReal (1/4) := by
  classical
  let K := iterations (network p)
  let g (j : Fin K) := ‖D.G (point D s j)‖
  let U := Finset.univ.filter (fun j : Fin K => p.ε/2 < g j)
  have h := gradient_sum D s hl
  have hmark : (U.card:ℝ)*(p.ε/2) ≤ ∑ j, g j := by
    calc
      _ = ∑ _j ∈ U, p.ε/2 := by simp
      _ ≤ ∑ j ∈ U, g j := Finset.sum_le_sum (fun j hj => ((Finset.mem_filter.mp hj).2).le)
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun j => norm_nonneg _)
  change (∑ j, g j) ≤ 35*(K:ℝ)*(p.ε/512) at h
  have hcard : 4*U.card ≤ K := by
    have hε := D.valid.2.2.2.1
    apply Nat.cast_le (α := ℝ) |>.mp
    push_cast
    apply le_of_mul_le_mul_right (a := p.ε) _ hε
    nlinarith only [hmark,h,show 0 ≤ (K:ℝ)*p.ε by positivity]
  have hpos : 0 < K := by dsimp [K,iterations]; positivity
  let _ : NeZero K := ⟨hpos.ne'⟩
  have he : {j : Fin (iterations (network p)) | p.ε/2 < ‖D.G (point D s j)‖} = (↑U : Set (Fin K)) := by
    ext j
    change (p.ε/2 < g j) ↔ j ∈ Finset.univ.filter (fun j : Fin K => p.ε/2 < g j)
    simp
  rw [he]
  change (PMF.uniformOfFintype (Fin K)).toMeasure (↑U : Set (Fin K)) ≤ _
  have hsize : Fintype.card (↑(↑U : Set (Fin K))) = U.card := by
    calc
      _ = Fintype.card (↥U) := Fintype.card_congr (Equiv.refl _)
      _ = _ := Fintype.card_coe U
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.Finite.measurableSet (Set.toFinite _)),hsize,Fintype.card_fin]
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num only [ENNReal.ofReal_ofNat]
  apply (ENNReal.div_le_iff (by exact_mod_cast hpos.ne') (by simp)).mpr
  rw [one_div, ← ENNReal.div_eq_inv_mul]
  apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hcard : U.card*4 ≤ K)

lemma missed (D : Data p) (s : Samples p) (hl : loss D s < 1) :
    seeds p {z | ∀ i, p.ε/2 < ‖D.G (point D s (z i))‖} ≤ ENNReal.ofReal (Real.exp (-(confidence p:ℝ))) := by
  let B := {j : Fin (iterations (network p)) | p.ε/2 < ‖D.G (point D s j)‖}
  have he : {z : Seed p | ∀ i, p.ε/2 < ‖D.G (point D s (z i))‖} = Set.pi Set.univ (fun _ => B) := by ext z; simp [B]
  rw [he,seeds,Measure.pi_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply (pow_le_pow_left' (fraction D s hl) (confidence p)).trans
  rw [← ENNReal.ofReal_pow (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [show -(confidence p:ℝ) = (confidence p:ℝ)*(-1) by ring,Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by norm_num)
  rw [Real.exp_neg]
  apply (le_inv_comm₀ (by norm_num) (Real.exp_pos 1)).mpr
  norm_num
  linarith only [Real.exp_one_lt_d9]

lemma confidence_budget (p : Params) (hd : 0 < p.failure) :
    Real.exp (-(confidence p:ℝ)) + Real.exp (-(confidence p:ℝ)) +
      2*(confidence p:ℝ)*Real.exp (-(2*(confidence p:ℝ))) ≤ p.failure := by
  let q := (confidence p:ℝ)
  have hq : 4+Real.log (1/p.failure) ≤ q := by
    dsimp [q,confidence]; push_cast; linarith only [Nat.le_ceil (Real.log (1/p.failure))]
  rw [one_div,Real.log_inv] at hq
  have he : Real.exp (-q) ≤ p.failure*Real.exp (-4) := by
    have h := Real.exp_le_exp.mpr (by linarith only [hq] : -q ≤ Real.log p.failure + (-4))
    rw [Real.exp_add,Real.exp_log hd] at h
    exact h
  have hqexp : q*Real.exp (-q) ≤ 1 := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr (by linarith only [Real.add_one_le_exp q])
  have hterm : 2*q*Real.exp (-(2*q)) ≤ 2*Real.exp (-q) := by
    rw [show -(2*q) = -q + -q by ring,Real.exp_add]
    nlinarith only [mul_le_mul_of_nonneg_right hqexp (Real.exp_pos (-q)).le]
  have hconst : 4*Real.exp (-4) ≤ 1 := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr (by linarith only [Real.add_one_le_exp 4])
  change Real.exp (-q)+Real.exp (-q)+2*q*Real.exp (-(2*q)) ≤ p.failure
  nlinarith only [hterm,he,mul_le_mul_of_nonneg_left hconst hd.le]

end LongTails.Proofs.ContaminatedSeedSelection
