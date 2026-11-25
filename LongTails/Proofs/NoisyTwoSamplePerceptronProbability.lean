import LongTails.Proofs.NoisyTwoSamplePerceptronStopping

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LongTails.Setups.FiniteLogisticTwoTap (Weights Separates)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronGaussian
open LongTails.Proofs.NoisyTwoSamplePerceptronHorizon
open LongTails.Proofs.NoisyTwoSamplePerceptronBlocks
open LongTails.Proofs.NoisyTwoSamplePerceptronExecution
open LongTails.Proofs.NoisyTwoSamplePerceptronStopping

namespace LongTails.Proofs.NoisyTwoSamplePerceptronProbability

noncomputable def threshold (p : Params) := 4*Real.sqrt (noiseScale p/5)

lemma tail_cost (p : Params) (hp : spec.valid p) :
    2*Real.exp (-(threshold p)^2/2) ≤ p.ρ/(10*(horizon p:ℝ)) := by
  let M := noiseScale p
  let T := (horizon p:ℝ)
  have H := (horizon_bounds p hp).2.2.1
  have hM : 5 ≤ M := H
  have hr := hp.2.2.2.2.2.1
  have hT := (valid_scales p hp).2.2.2.2.2
  have hT₀ : 0 < T := by dsimp [T]; exact_mod_cast (by omega : 0 < horizon p)
  have h₁ : T/p.ρ ≤ Real.exp M := (Real.log_le_iff_le_exp (div_pos hT₀ hr)).mp (le_max_right _ _)
  have h₂ : (20:ℝ) ≤ Real.exp (3*M/5) := by
    apply le_trans _ (Real.exp_le_exp.mpr (show (3:ℝ) ≤ 3*M/5 by linarith))
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 3
    norm_num at hh
    linarith
  have hpow : 20*(T/p.ρ) ≤ Real.exp (8*M/5) := by
    rw [show 8*M/5=3*M/5+M by ring,Real.exp_add]
    exact mul_le_mul h₂ h₁ (div_pos hT₀ hr).le (Real.exp_pos _).le
  have hsq : (threshold p)^2/2 = 8*M/5 := by
    dsimp [threshold]
    rw [mul_pow,Real.sq_sqrt (by change 0 ≤ M/5; linarith)]
    ring
  rw [neg_div,hsq,Real.exp_neg]
  change 2*(Real.exp (8*M/5))⁻¹ ≤ p.ρ/(10*T)
  field_simp
  have H' := (div_le_iff₀ hr).mp (show (20*T)/p.ρ ≤ Real.exp (8*M/5) by
    convert hpow using 1
    ring)
  linarith

lemma good_sample (p : Params) (hp : spec.valid p) (i : Fin p.d) (g : Weights p.d)
    (hh : ∀ k, |component i k g| ≤ threshold p) :
    ‖sigma p • proj (coords i g)‖ ≤ noiseBound p ∧
      |sigma p*slowProjection i g| ≤ noiseBound p := by
  let M := noiseScale p
  have hM := (horizon_bounds p hp).2.2.1
  have hM₀ : 0 < M := by change 5 ≤ M at hM; linarith
  have hT := (valid_scales p hp).2.2.2.2.2
  have hs := hp.2.2.2.1
  have hT₀ : 0 < (horizon p:ℝ) := by exact_mod_cast (by omega : 0 < horizon p)
  have hσ : 0 < sigma p := by dsimp [sigma]; positivity
  have hsq := projected_bounds i g _ hh
  have he : 5*(threshold p)^2=16*M := by
    dsimp [threshold]
    rw [mul_pow,Real.sq_sqrt (by change 0 ≤ M/5; linarith)]
    ring
  rw [he] at hsq
  have hroot := Real.sq_sqrt hM₀.le
  have hR : 0 ≤ 4*Real.sqrt M := by positivity
  have h₁ : ‖proj (coords i g)‖ ≤ 4*Real.sqrt M := by
    nlinarith [sq_nonneg (slowProjection i g),norm_nonneg (proj (coords i g))]
  have h₂ : |slowProjection i g| ≤ 4*Real.sqrt M := by
    nlinarith [sq_abs (slowProjection i g),sq_nonneg ‖proj (coords i g)‖]
  have H : sigma p*(4*Real.sqrt M)=noiseBound p := by
    dsimp [sigma,noiseBound,M]
    field_simp [show Real.sqrt (noiseScale p) ≠ 0 from (Real.sqrt_pos.mpr hM₀).ne']
    ring
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hσ,← H]
  exact ⟨mul_le_mul_of_nonneg_left h₁ hσ.le,mul_le_mul_of_nonneg_left h₂ hσ.le⟩

lemma fails_rarely (p : Params) (hp : spec.valid p) (i : Fin p.d) (hi : finRotate p.d i ≠ i)
    (hs : p.signal ≤ |slowProjection i p.x₀|) :
    law p.d {g | ¬Separates p.μ i (point p.μ (gamma p.d) (sigma p) i p.x₀ g (horizon p))} ≤
      ENNReal.ofReal p.ρ := by
  classical
  let T := horizon p
  let noise := fun (j : Fin T × Fin 5) =>
    {g : ℕ → Weights p.d | threshold p < |component i j.2 (g j.1)|}
  let block := fun (s : Fin T) =>
    {g : ℕ → Weights p.d | |forced p.μ (sigma p) i p.x₀ g s (blockLength p)| ≤ terminalBound p}
  have hT := (valid_scales p hp).2.2.2.2.2
  have hT₀ : 0 < (T:ℝ) := by dsimp [T]; exact_mod_cast (by omega : 0 < horizon p)
  have hr := hp.2.2.2.2.2.1
  have hM := (horizon_bounds p hp).2.2.1
  have hs₀ := hp.2.2.2.1
  have hσ : 0 < sigma p := by dsimp [sigma]; positivity
  have hN (j : Fin T × Fin 5) : law p.d (noise j) ≤ ENNReal.ofReal (p.ρ/(10*(T:ℝ))) := by
    have HM : MeasurableSet {x | threshold p < |component i j.2 x|} :=
      measurableSet_lt measurable_const (by fun_prop)
    let f := fun (g : ℕ → Weights p.d) => g (j.1:ℕ)
    change law p.d (f ⁻¹' {x | threshold p < |component i j.2 x|}) ≤ _
    rw [← Measure.map_apply (μ := law p.d) (show Measurable f from measurable_pi_apply (j.1:ℕ)) HM,
      show (law p.d).map f = stdGaussian _ from Measure.infinitePi_map_eval (fun _ : ℕ => stdGaussian (Weights p.d)) _]
    exact (component_tail hp.1 i hi _ (by dsimp [threshold]; positivity)).trans (ENNReal.ofReal_le_ofReal (tail_cost p hp))
  have hB (s : Fin T) : law p.d (block s) ≤ ENNReal.ofReal (p.ρ/(2*(T:ℝ))) := by
    have hx := (valid_scales p hp).1
    have hC := (valid_scales p hp).2.1
    apply (forced_small p.μ (sigma p) hσ i p.x₀ s (blockLength p-1) (terminalBound p)
      (by dsimp [terminalBound]; positivity)).trans
    exact ENNReal.ofReal_le_ofReal (block_dilution p hp)
  have hsub : {g | ¬Separates p.μ i (point p.μ (gamma p.d) (sigma p) i p.x₀ g T)} ⊆
      (⋃ j, noise j) ∪ (⋃ s, block s) := by
    intro g hg
    by_cases h : ∀ j : Fin T × Fin 5, |component i j.2 (g j.1)| ≤ threshold p
    · obtain ⟨s,hst,H⟩ := path_or_block p hp i hi hs g (fun n hn =>
        good_sample p hp i _ (fun k => h (⟨n,hn⟩,k))) hg
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨s,hst⟩,H⟩)
    · push Not at h
      obtain ⟨j,hj⟩ := h
      exact Or.inl (Set.mem_iUnion.mpr ⟨j,hj⟩)
  apply (measure_mono hsub).trans ((measure_union_le ..).trans _)
  apply (add_le_add ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum (fun j _ => hN j)))
    ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum (fun s _ => hB s)))).trans
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
  norm_cast
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  field_simp
  ring_nf
  rfl

end LongTails.Proofs.NoisyTwoSamplePerceptronProbability
