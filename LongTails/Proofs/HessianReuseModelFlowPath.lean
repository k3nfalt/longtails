import LongTails.Algorithms.HessianReuseModelFlow
import LongTails.Proofs.SelfConcordantCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace LongTails.Proofs.HessianReuseModelFlowPath

open LongTails.Algorithms.HessianReuseModelFlow
open LongTails.Setups.GradientDependentHessian Set MeasureTheory

variable {p : Params}

lemma curvature_pos (hp : spec.valid p) : 0 < curvature p :=
  add_pos_of_pos_of_nonneg hp.1 (mul_nonneg hp.2.1 hp.2.2.2.2.1.le)

lemma m_pos (hp : spec.valid p) : 0 < (p.m : ℝ) := by
  exact_mod_cast (show 0 < p.m from hp.2.2.2.2.2)

lemma radius_pos (hp : spec.valid p) : 0 < radius p := by
  unfold radius allowance
  have := hp.2.2.2.2.1
  have := curvature_pos hp
  have := m_pos hp
  positivity

lemma cap_pos (hp : spec.valid p) : 0 < energyCap p := by
  unfold energyCap threshold
  have := hp.2.2.2.2.1
  have := radius_pos hp
  positivity

lemma radius_scale (hp : spec.valid p) :
    p.m * curvature p * radius p ^ 2 = allowance p := by
  have hm := m_pos hp
  have hA := curvature_pos hp
  have hb : 0 < allowance p := by
    unfold allowance
    linarith [hp.2.2.2.2.1]
  rw [radius, Real.sq_sqrt (by positivity)]
  field_simp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g : E) (H : E →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
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

lemma stop_spec (hp : spec.valid p) (hg : p.ε < ‖g‖) :
    let τ := stopTime p g H
    0 ≤ τ ∧ (∀ t ∈ Icc 0 τ, threshold p ≤ ‖velocity g H t‖ ∧ energy g H t ≤ energyCap p) ∧
      (‖velocity g H τ‖ ≤ threshold p ∨ energy g H τ = energyCap p) := by
  let M := margin p g H
  let Z := {t : ℝ | 0 ≤ t ∧ M t = 0}
  have hε := hp.2.2.2.2.1
  have hq : 0 < threshold p := by unfold threshold; positivity
  have hc : Continuous M := ((velocity_continuous g H).norm.sub continuous_const).min
    (continuous_const.sub (continuous_iff_continuousAt.mpr (fun t => (energy_deriv g H t).continuousAt)))
  have h0 : 0 < M 0 := by
    simp only [M, margin, threshold, velocity_zero, energy, intervalIntegral.integral_same, sub_zero, lt_min_iff]
    exact ⟨by linarith, cap_pos hp⟩
  have cross {t : ℝ} (ht : 0 ≤ t) (hm : M t ≤ 0) : ∃ u ∈ Icc 0 t, M u = 0 :=
    intermediate_value_Icc' ht hc.continuousOn ⟨hm, h0.le⟩
  have hne : Z.Nonempty := by
    by_contra hn
    have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < M t := by
      by_contra! h
      obtain ⟨u, hu, he⟩ := cross ht h
      exact hn ⟨u, hu.1, he⟩
    let T := energyCap p / (threshold p) ^ 2
    have hT : 0 ≤ T := div_nonneg (cap_pos hp).le (sq_nonneg _)
    have hle : (∫ _ in (0 : ℝ)..T, (threshold p) ^ 2) ≤ energy g H T := by
      apply intervalIntegral.integral_mono_on hT intervalIntegrable_const
        (((velocity_continuous g H).norm.pow 2).intervalIntegrable _ _)
      intro t ht
      have h := (lt_min_iff.mp (hpos t ht.1)).1
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have heq : T * (threshold p) ^ 2 = energyCap p := div_mul_cancel₀ _ (by positivity)
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
    rcases le_total (‖velocity g H (stopTime p g H)‖ - threshold p)
        (energyCap p - energy g H (stopTime p g H)) with h | h
    · rw [min_eq_left h] at hz
      exact Or.inl (by linarith)
    · rw [min_eq_right h] at hz
      exact Or.inr (by linarith)

noncomputable def pathLength (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, ‖velocity g H u‖

lemma length_deriv (t : ℝ) : HasDerivAt (pathLength g H) ‖velocity g H t‖ t :=
  primitive_deriv (velocity_continuous g H).norm t

lemma length_bound (hp : spec.valid p) {τ : ℝ}
    (hpath : ∀ t ∈ Icc 0 τ, threshold p ≤ ‖velocity g H t‖ ∧ energy g H t ≤ energyCap p)
    {t : ℝ} (ht : t ∈ Icc 0 τ) : pathLength g H t ≤ radius p := by
  have hh := SelfConcordantCalculus.le_of_deriv_nonpos ht.1
    (F := fun s => threshold p * pathLength g H s - energy g H s)
    (fun s _ => ((length_deriv g H s).const_mul (threshold p)).sub (energy_deriv g H s))
    (fun s hs => by
      have hb := mul_le_mul_of_nonneg_right (hpath s ⟨hs.1, hs.2.trans ht.2⟩).1 (norm_nonneg (velocity g H s))
      nlinarith only [hb])
  simp only [pathLength, energy, intervalIntegral.integral_same, mul_zero, sub_zero] at hh
  change threshold p * pathLength g H t - energy g H t ≤ 0 at hh
  have hc := (hpath t ht).2
  unfold energyCap at hc
  exact le_of_mul_le_mul_left (a := threshold p) (by linarith) (by unfold threshold; linarith [hp.2.2.2.2.1])

end LongTails.Proofs.HessianReuseModelFlowPath
