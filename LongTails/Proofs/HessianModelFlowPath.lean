import LongTails.Algorithms.PointwiseHessianModelFlow
import LongTails.Proofs.RelativeHessianTuning
import LongTails.Proofs.SelfConcordantCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace LongTails.Proofs.HessianModelFlowPath

open LongTails.Algorithms.PointwiseHessianModelFlow
open LongTails.Setups.PointwiseHessianStationarity Set MeasureTheory

variable {p : Params}

lemma radius_pos (hp : broadSpec.valid p) : 0 < radius p :=
  div_pos (Real.sqrt_pos.2 hp.2.2.2.2.2)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (RelativeHessianTuning.curvature_pos hp)))

lemma cap_pos (hp : broadSpec.valid p) : 0 < energyCap p :=
  div_pos (mul_pos hp.2.2.2.2.2 (radius_pos hp)) (by norm_num)

lemma radius_scale (hp : broadSpec.valid p) :
    (p.L₀ + p.L₁ * p.ε) * radius p ^ 2 = p.ε / 16 := by
  have hA := RelativeHessianTuning.curvature_pos hp
  rw [radius, div_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hp.2.2.2.2.2.le]
  field_simp
  ring

lemma relative_radius (hp : broadSpec.valid p) : p.L₁ * radius p ^ 2 ≤ 1 / 16 := by
  have h := radius_scale hp
  have hε := hp.2.2.2.2.2
  apply le_of_mul_le_mul_right (a := p.ε) _ hε
  nlinarith [mul_nonneg hp.1 (sq_nonneg (radius p))]

variable (g : Point p) (H : Point p →L[ℝ] Point p)

lemma velocity_zero : velocity g H 0 = g := by simp [velocity]

lemma velocity_deriv (t : ℝ) :
    HasDerivAt (velocity g H) (-(H (velocity g H t))) t := by
  change HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-H)) g) (-(H (NormedSpace.exp (t • (-H)) g))) t
  simpa using
    ((hasDerivAt_exp_smul_const' (-H) t).clm_apply (hasDerivAt_const t g))

lemma velocity_continuous : Continuous (velocity g H) :=
  continuous_iff_continuousAt.mpr fun t => (velocity_deriv g H t).continuousAt

lemma primitive_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ → V} (hc : Continuous F) (t : ℝ) :
    HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, F u) (F t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma displacement_deriv (t : ℝ) :
    HasDerivAt (displacement g H) (-velocity g H t) t :=
  (primitive_deriv (velocity_continuous g H) t).neg

lemma energy_deriv (t : ℝ) : HasDerivAt (energy g H) (‖velocity g H t‖ ^ 2) t :=
  primitive_deriv ((velocity_continuous g H).norm.pow 2) t

lemma stop_spec (hp : broadSpec.valid p) (hg : p.ε < ‖g‖) :
    let τ := stopTime p g H
    0 ≤ τ ∧ (∀ t ∈ Icc 0 τ, p.ε / 2 ≤ ‖velocity g H t‖ ∧ energy g H t ≤ energyCap p) ∧
      (‖velocity g H τ‖ ≤ p.ε / 2 ∨ energy g H τ = energyCap p) := by
  let M := margin p g H
  let Z := {t : ℝ | 0 ≤ t ∧ M t = 0}
  have hε := hp.2.2.2.2.2
  have hc : Continuous M := ((velocity_continuous g H).norm.sub continuous_const).min
    (continuous_const.sub (continuous_iff_continuousAt.mpr (fun t => (energy_deriv g H t).continuousAt)))
  have h0 : 0 < M 0 := by
    simp only [M, margin, velocity_zero, energy, intervalIntegral.integral_same, sub_zero, lt_min_iff]
    exact ⟨by linarith, cap_pos hp⟩
  have cross {t : ℝ} (ht : 0 ≤ t) (hm : M t ≤ 0) : ∃ u ∈ Icc 0 t, M u = 0 :=
    intermediate_value_Icc' ht hc.continuousOn ⟨hm, h0.le⟩
  have hne : Z.Nonempty := by
    by_contra hn
    have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < M t := by
      by_contra! h
      obtain ⟨u, hu, he⟩ := cross ht h
      exact hn ⟨u, hu.1, he⟩
    let T := energyCap p / (p.ε / 2) ^ 2
    have hT : 0 ≤ T := div_nonneg (cap_pos hp).le (sq_nonneg _)
    have hle : (∫ _ in (0 : ℝ)..T, (p.ε / 2) ^ 2) ≤ energy g H T := by
      apply intervalIntegral.integral_mono_on hT intervalIntegrable_const
        (((velocity_continuous g H).norm.pow 2).intervalIntegrable _ _)
      intro t ht
      have h := (lt_min_iff.mp (hpos t ht.1)).1
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have heq : T * (p.ε / 2) ^ 2 = energyCap p := div_mul_cancel₀ _ (by positivity)
    have hh := (lt_min_iff.mp (hpos T hT)).2
    have hcT : energyCap p ≤ energy g H T := by
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, heq] using hle
    linarith only [hcT, hh]
  have hb : BddBelow Z := ⟨0, fun _ ht => ht.1⟩
  have hclosed : IsClosed Z := isClosed_Ici.inter (isClosed_eq hc continuous_const)
  have hτ : stopTime p g H ∈ Z := hclosed.csInf_mem hne hb
  have hall (t : ℝ) (ht : t ∈ Icc 0 (stopTime p g H)) : 0 ≤ M t := by
    by_contra! hn
    obtain ⟨u, hu, hz⟩ := cross ht.1 hn.le
    have hmin : stopTime p g H ≤ u := csInf_le hb (show u ∈ Z from ⟨hu.1, hz⟩)
    have he : u = t := le_antisymm hu.2 (ht.2.trans hmin)
    exact hn.ne (he ▸ hz)
  refine ⟨hτ.1, fun t ht => ?_, ?_⟩
  · obtain ⟨h₁, h₂⟩ := le_min_iff.mp (hall t ht)
    exact ⟨by linarith, by linarith⟩
  · have hz := hτ.2
    change min _ _ = (0 : ℝ) at hz
    rcases le_total (‖velocity g H (stopTime p g H)‖ - p.ε / 2)
        (energyCap p - energy g H (stopTime p g H)) with h | h
    · rw [min_eq_left h] at hz
      exact Or.inl (by linarith)
    · rw [min_eq_right h] at hz
      exact Or.inr (by linarith)

noncomputable def pathLength (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, ‖velocity g H u‖

lemma length_deriv (t : ℝ) : HasDerivAt (pathLength g H) ‖velocity g H t‖ t :=
  primitive_deriv (velocity_continuous g H).norm t

lemma length_bound (hp : broadSpec.valid p) {τ : ℝ}
    (hpath : ∀ t ∈ Icc 0 τ, p.ε / 2 ≤ ‖velocity g H t‖ ∧ energy g H t ≤ energyCap p)
    {t : ℝ} (ht : t ∈ Icc 0 τ) : pathLength g H t ≤ radius p := by
  have hh := SelfConcordantCalculus.le_of_deriv_nonpos ht.1
    (F := fun s => p.ε / 2 * pathLength g H s - energy g H s)
    (fun s _ => ((length_deriv g H s).const_mul (p.ε / 2)).sub (energy_deriv g H s))
    (fun s hs => by
      have hb := mul_le_mul_of_nonneg_right (hpath s ⟨hs.1, hs.2.trans ht.2⟩).1 (norm_nonneg (velocity g H s))
      nlinarith only [hb])
  simp only [pathLength, energy, intervalIntegral.integral_same, mul_zero, sub_zero] at hh
  change p.ε / 2 * pathLength g H t - energy g H t ≤ 0 at hh
  have hc := (hpath t ht).2
  unfold energyCap at hc
  exact le_of_mul_le_mul_left (a := p.ε) (by linarith) hp.2.2.2.2.2

end LongTails.Proofs.HessianModelFlowPath
