import LongTails.Proofs.PointwiseHessianEpisodePartition
import LongTails.Proofs.PointwiseHessianBounds

open scoped Classical

namespace LongTails.Proofs.PointwiseHessianTrialCount

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianExecution

def RadiusInitializationInvariant {p : Public} (s : State p) : Prop :=
  (s.phase = .newtonHessian ∨ s.phase = .newtonGradient) → initialRadius p s.τ ≤ s.r

lemma startTrial_radiusInitialization {p : Public} (s : State p) (τ : ℝ) :
    RadiusInitializationInvariant (startTrial s τ (initialRadius p τ)) := by
  intro _
  exact le_rfl

lemma failedTrial_radiusInitialization {p : Public} {f : p.E → ℝ} (s : State p)
    (hp : InnerParameters f s) (hinit : initialRadius p s.τ ≤ s.r) :
    RadiusInitializationInvariant (failedTrial s) := by
  unfold failedTrial
  split_ifs
  · intro _
    change initialRadius p s.τ ≤ min (2 * s.r) (radiusCap p s.τ)
    exact le_min (by linarith [hp.r_pos]) (hinit.trans hp.r_le)
  · exact startTrial_radiusInitialization s _

lemma accept_radiusInitialization {p : Public} (s : State p) :
    RadiusInitializationInvariant (accept s) := by
  intro h
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · simp [accept, finish, ht] at h
  · simp [accept, ht] at h

lemma center_radiusInitialization {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .centerGradient) :
    RadiusInitializationInvariant (update s reply) := by
  simp only [update, hs]
  split_ifs
  · intro h
    simp [finish] at h
  · exact startTrial_radiusInitialization _ _

lemma gradient_radiusInitialization {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonGradient)
    (hi : RadiusInitializationInvariant s) : RadiusInitializationInvariant (update s reply) := by
  have hp := hi (Or.inr hs)
  simp only [update, hs]
  split_ifs
  · intro h
    simp [finish] at h
  · intro _
    exact hp
  · exact accept_radiusInitialization _
  · intro _
    exact hp

lemma hessian_radiusInitialization {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonHessian)
    (hi : PhaseInvariant f xs s) (hinit : RadiusInitializationInvariant s) :
    RadiusInitializationInvariant (update s reply) := by
  have hp := hi
  simp only [PhaseInvariant, hs] at hp
  have hh := hinit (Or.inl hs)
  simp only [update, hs]
  split_ifs
  · intro _
    exact hh
  · exact failedTrial_radiusInitialization s hp.1 hh

lemma radiusInitialization_step {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hi : PhaseInvariant f xs s)
    (hinit : RadiusInitializationInvariant s) : RadiusInitializationInvariant (update s reply) := by
  cases hs : s.phase with
  | centerGradient => exact center_radiusInitialization s reply hs
  | newtonHessian => exact hessian_radiusInitialization s reply hs hi hinit
  | newtonGradient => exact gradient_radiusInitialization s reply hs hinit
  | finished => simpa only [update, hs] using hinit

lemma radiusInitialization_path {p : Public} {f : p.E → ℝ} {xs : p.E}
    (s : ℕ → State p) (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (h0 : (s 0).phase = .centerGradient)
    (hi : ∀ k < N, PhaseInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    RadiusInitializationInvariant (s N) := by
  induction N with
  | zero =>
    intro h
    simp only [h0, reduceCtorEq, or_self] at h
  | succ N ih =>
    rw [hs N (by omega)]
    exact radiusInitialization_step (s N) (reply N) (hi N (by omega))
      (ih (fun k hk => hi k (by omega)) (fun k hk => hs k (by omega)))

lemma initialRadius_lower {p : Public} {τ Z : ℝ} (hM₀ : 0 ≤ p.M₀)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hZ : 2 ≤ Z) (hτ : 0 < τ)
    (hlo : p.ε / p.R ^ 2 ≤ τ) (hhi : τ * p.R ^ 2 / p.ε ≤ 1024 * Z)
    (hM : p.M₀ * p.R ^ 3 / p.ε ≤ Z) :
    p.R / (1048576 * Z) ≤ initialRadius p τ := by
  have hZp : 0 < Z := by linarith
  have hRZ : p.R ≤ p.R * Z := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr (show 1 ≤ Z by linarith))]
  have hlarge : p.R / (1048576 * Z) ≤ 16 * p.R := by
    apply (div_le_iff₀ (by positivity : 0 < 1048576 * Z)).mpr
    nlinarith
  have ht := (div_le_iff₀ hε).mp hhi
  unfold initialRadius
  apply le_min
  · change p.R / (1048576 * Z) ≤ (p.ε / (1000 * p.R)) / τ
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 1048576 * Z) (by positivity : 0 < 1000 * p.R * τ)).mpr
    nlinarith [mul_pos hZp hε]
  · by_cases hz : p.M₀ = 0
    · simpa only [radiusCap, hz, ite_true] using hlarge
    · have hMp : 0 < p.M₀ := lt_of_le_of_ne hM₀ (Ne.symm hz)
      simp only [radiusCap, hz, ite_false]
      refine le_min hlarge ?_
      have hR2 : 0 < p.R ^ 2 := sq_pos_of_pos hR
      have hτlow := (div_le_iff₀ hR2).mp hlo
      have hMhigh := (div_le_iff₀ hε).mp hM
      have hscaled := mul_le_mul_of_nonneg_left hτlow hZp.le
      have hMR : p.M₀ * p.R ≤ Z * τ := by
        apply (mul_le_mul_iff_right₀ hR2).mp
        nlinarith
      apply (div_le_div_iff₀ (by positivity : 0 < 1048576 * Z) (by positivity : 0 < 64 * p.M₀)).mpr
      nlinarith [mul_pos hZp hτ]


lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hh
  linarith

lemma log_ratio_nonneg {r ρ : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r) :
    0 ≤ Real.log (r / ρ) / Real.log 2 := by
  apply div_nonneg _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact Real.log_nonneg ((le_div_iff₀ hρ).mpr (by simpa using hr))

lemma log_ratio_double {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    Real.log ((2 * r) / ρ) / Real.log 2 = Real.log (r / ρ) / Real.log 2 + 1 := by
  have he : (2 * r) / ρ = 2 * (r / ρ) := by ring
  rw [he, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_pos hr hρ).ne']
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hl]
  ring

noncomputable def radiusPotential {p : Public} (ρ τ r : ℝ) : ℝ :=
  Real.log (r / ρ) / Real.log 2 + if r = radiusCap p τ then 1 else 0

lemma radiusPotential_nonneg {p : Public} {ρ τ r : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r) :
    0 ≤ radiusPotential (p := p) ρ τ r := by
  have hh := log_ratio_nonneg hρ hr
  unfold radiusPotential
  split_ifs <;> linarith

lemma log_ratio_power_bound {r ρ Z : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hZ : 1 ≤ Z)
    (n : ℕ) (hbound : r / ρ ≤ (2 : ℝ) ^ n * Z) :
    Real.log (r / ρ) / Real.log 2 ≤ n + 2 * Real.log Z := by
  have hZp : 0 < Z := by linarith
  have hl := Real.log_le_log (div_pos hr hρ) hbound
  rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) n).ne' hZp.ne', Real.log_pow] at hl
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have hnonneg := Real.log_nonneg hZ
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr half_le_log_two)]

lemma radiusPotential_upper {p : Public} {ρ τ r Z : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hZ : 2 ≤ Z) (hbound : r / ρ ≤ 16777216 * Z) :
    radiusPotential (p := p) ρ τ r ≤ 32 * (1 + Real.log Z) - 1 := by
  have hh := log_ratio_power_bound hr hρ (show 1 ≤ Z by linarith) 24
    (by norm_num; exact hbound)
  have hn := Real.log_nonneg (show 1 ≤ Z by linarith)
  norm_num at hh
  unfold radiusPotential
  split_ifs <;> linarith

lemma tau_log_upper {τ τlo Z : ℝ} (hτ : 0 < τ) (hlo : 0 < τlo)
    (hZ : 2 ≤ Z) (hbound : τ / τlo ≤ 1024 * Z) :
    Real.log (τ / τlo) / Real.log 2 ≤ 16 * (1 + Real.log Z) := by
  have hh := log_ratio_power_bound hτ hlo (show 1 ≤ Z by linarith) 10
    (by norm_num; exact hbound)
  have hn := Real.log_nonneg (show 1 ≤ Z by linarith)
  norm_num at hh
  linarith

lemma radiusPotential_growth {p : Public} {ρ τ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hcap : r < radiusCap p τ) :
    radiusPotential (p := p) ρ τ r + 1 ≤ radiusPotential (p := p) ρ τ (min (2 * r) (radiusCap p τ)) := by
  by_cases hd : 2 * r < radiusCap p τ
  · simp only [min_eq_left hd.le, radiusPotential, ite_eq_right hcap.ne, ite_eq_right hd.ne]
    rw [log_ratio_double hr hρ]
    simp only [add_zero, le_refl]
  · simp only [min_eq_right (le_of_not_gt hd), radiusPotential, ite_eq_right hcap.ne,
      ite_true, add_zero]
    have hh : Real.log (r / ρ) / Real.log 2 ≤ Real.log (radiusCap p τ / ρ) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      exact Real.log_le_log (div_pos hr hρ) (div_le_div_of_nonneg_right hcap.le hρ.le)
    linarith

lemma restart_potential_growth {p : Public} {ρ τ τlo r rnew J : ℝ}
    (hτ : 0 < τ) (hlo : 0 < τlo)
    (hold : radiusPotential (p := p) ρ τ r ≤ J - 1)
    (hnew : 0 ≤ radiusPotential (p := p) ρ (2 * τ) rnew) :
    (1 + J * (Real.log (τ / τlo) / Real.log 2) + radiusPotential (p := p) ρ τ r) + 1 ≤
      1 + J * (Real.log ((2 * τ) / τlo) / Real.log 2) + radiusPotential (p := p) ρ (2 * τ) rnew := by
  rw [log_ratio_double hτ hlo]
  nlinarith

noncomputable def trialPotential {p : Public} (τlo ρ Z : ℝ) (s : State p) : ℝ :=
  if s.phase = .newtonHessian ∨ s.phase = .newtonGradient then
    1 + (32 * (1 + Real.log Z)) * (Real.log (s.τ / τlo) / Real.log 2) +
      radiusPotential (p := p) ρ s.τ s.r
  else 0

lemma trialPotential_inner_lower {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (hτ : τlo ≤ s.τ) (hr : ρ ≤ s.r) : 1 ≤ trialPotential τlo ρ Z s := by
  have hlog := Real.log_nonneg (show 1 ≤ Z by linarith)
  have ht := log_ratio_nonneg hlo hτ
  have hrad := radiusPotential_nonneg (p := p) (τ := s.τ) hρ hr
  simp only [trialPotential, ite_eq_left hp]
  nlinarith [mul_nonneg (show 0 ≤ 32 * (1 + Real.log Z) by positivity) ht]

lemma trialPotential_inner_upper {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z) (hτ : 0 < s.τ) (hr : 0 < s.r)
    (hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (ht : s.τ / τlo ≤ 1024 * Z) (hrad : s.r / ρ ≤ 16777216 * Z) :
    trialPotential τlo ρ Z s ≤ 1024 * (1 + Real.log Z) ^ 2 := by
  have hlog := Real.log_nonneg (show 1 ≤ Z by linarith)
  have ht' := tau_log_upper hτ hlo hZ ht
  have hr' := radiusPotential_upper (p := p) (τ := s.τ) hr hρ hZ hrad
  have hm := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 32 * (1 + Real.log Z) by positivity)
  simp only [trialPotential, ite_eq_left hp]
  nlinarith [sq_nonneg (Real.log Z)]


def TrialBounds {p : Public} (τlo ρ Z : ℝ) (s : State p) : Prop :=
  (s.phase = .newtonHessian ∨ s.phase = .newtonGradient) →
    τlo ≤ s.τ ∧ ρ ≤ s.r ∧ s.τ / τlo ≤ 1024 * Z ∧ s.r / ρ ≤ 16777216 * Z

lemma trialPotential_bounds {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z) (hb : TrialBounds τlo ρ Z s) :
    0 ≤ trialPotential τlo ρ Z s ∧ trialPotential τlo ρ Z s ≤ 1024 * (1 + Real.log Z) ^ 2 := by
  by_cases hp : s.phase = .newtonHessian ∨ s.phase = .newtonGradient
  · have hh := hb hp
    exact ⟨le_trans (by norm_num) (trialPotential_inner_lower s hlo hρ hZ hp hh.1 hh.2.1),
      trialPotential_inner_upper s hlo hρ hZ (hlo.trans_le hh.1) (hρ.trans_le hh.2.1) hp hh.2.2.1 hh.2.2.2⟩
  · simp only [trialPotential, ite_eq_right hp]
    constructor
    · exact le_rfl
    · positivity

lemma trialPotential_startTrial {p : Public} (s : State p) (τlo ρ Z τ r : ℝ) :
    trialPotential τlo ρ Z (startTrial s τ r) =
      1 + (32 * (1 + Real.log Z)) * (Real.log (τ / τlo) / Real.log 2) + radiusPotential (p := p) ρ τ r := by
  simp [trialPotential, startTrial]

lemma trialPotential_transfer {p : Public} {s t : State p} (τlo ρ Z : ℝ)
    (hs : s.phase = .newtonHessian ∨ s.phase = .newtonGradient)
    (ht : t.phase = .newtonHessian ∨ t.phase = .newtonGradient)
    (hτ : t.τ = s.τ) (hr : t.r = s.r) : trialPotential τlo ρ Z t = trialPotential τlo ρ Z s := by
  simp only [trialPotential, ite_eq_left hs, ite_eq_left ht, hτ, hr]

lemma trialPotential_center {p : Public} (s : State p) (τlo ρ Z : ℝ) (hs : s.phase = .centerGradient) :
    trialPotential τlo ρ Z s = 0 := by
  simp only [trialPotential, hs, reduceCtorEq, or_self, ite_false]

lemma trialPotential_accept {p : Public} (s : State p) (τlo ρ Z : ℝ) :
    trialPotential τlo ρ Z (accept s) = 0 := by
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · simp [accept, finish, trialPotential, ht]
  · simp [accept, trialPotential, ht]

open LongTails.Proofs.PointwiseHessianEpisodes
open LongTails.Proofs.PointwiseHessianEpisodePartition

lemma trialPotential_center_growth {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (hs : s.phase = .centerGradient) (hn : (update s reply).phase ≠ .finished)
    (hb : TrialBounds τlo ρ Z (update s reply)) :
    trialPotential τlo ρ Z s + 1 ≤ trialPotential τlo ρ Z (update s reply) := by
  have hstart := center_starts_radius s reply hs hn
  have hp := hb (Or.inl hstart.2)
  have hh := trialPotential_inner_lower (update s reply) hlo hρ hZ (Or.inl hstart.2) hp.1 hp.2.1
  rw [trialPotential_center s τlo ρ Z hs]
  simpa only [zero_add] using hh

lemma trialPotential_failed_growth {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (hs : s.phase = .newtonHessian)
    (hg : ¬ ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r)
    (hb : TrialBounds τlo ρ Z s) (hbn : TrialBounds τlo ρ Z (update s reply)) :
    trialPotential τlo ρ Z s + 1 ≤ trialPotential τlo ρ Z (update s reply) := by
  have hp := hb (Or.inl hs)
  have hτ : 0 < s.τ := hlo.trans_le hp.1
  have hr : 0 < s.r := hρ.trans_le hp.2.1
  have hu : update s reply = failedTrial s := by simp only [update, hs, hg, ite_false]
  have hsource : trialPotential τlo ρ Z s =
      1 + (32 * (1 + Real.log Z)) * (Real.log (s.τ / τlo) / Real.log 2) + radiusPotential (p := p) ρ s.τ s.r := by
    simp only [trialPotential, hs, true_or, ite_true]
  by_cases hc : s.r < radiusCap p s.τ
  · have hh := radiusPotential_growth hρ hr hc
    rw [hsource, hu]
    simp only [failedTrial, ite_eq_left hc, trialPotential_startTrial]
    linarith
  · have hnext := hbn (Or.inl (failed_hessian_starts_radius s reply hs hg).2)
    have hnew : ρ ≤ initialRadius p (2 * s.τ) := by
      simpa only [hu, failedTrial, ite_eq_right hc, startTrial] using hnext.2.1
    have hrad := radiusPotential_nonneg (p := p) (τ := 2 * s.τ) hρ hnew
    have hold := radiusPotential_upper (p := p) (τ := s.τ) hr hρ hZ hp.2.2.2
    have hh := restart_potential_growth hτ hlo hold hrad
    rw [hsource, hu]
    simpa only [failedTrial, ite_eq_right hc, trialPotential_startTrial] using hh


open LongTails.Proofs.PointwiseHessianLedger

lemma trialPotential_nonaccepted_credit {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (hn : s.phase ≠ .finished) (hn' : (update s reply).phase ≠ .finished)
    (hb : TrialBounds τlo ρ Z s) (hb' : TrialBounds τlo ρ Z (update s reply))
    (ha : ¬ Accepted s reply) :
    (if RadiusStart s (update s reply) then (1 : ℝ) else 0) ≤
      trialPotential τlo ρ Z (update s reply) - trialPotential τlo ρ Z s := by
  cases hs : s.phase with
  | centerGradient =>
    have hstart := center_starts_radius s reply hs hn'
    have hh := trialPotential_center_growth s reply hlo hρ hZ hs hn' hb'
    rw [ite_eq_left hstart]
    linarith
  | newtonHessian =>
    by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r
    · simp [trialPotential, RadiusStart, update, hs, hg]
    · have hstart := failed_hessian_starts_radius s reply hs hg
      have hh := trialPotential_failed_growth s reply hlo hρ hZ hs hg hb hb'
      rw [ite_eq_left hstart]
      linarith
  | newtonGradient =>
    have hstart : ¬ RadiusStart s (update s reply) := by simp [RadiusStart, hs]
    rw [ite_eq_right hstart]
    by_cases hg : ‖readGradient reply‖ ≤ gradientThreshold p
    · exact False.elim (hn' (by simp [update, hs, hg, finish]))
    by_cases hsmall : s.b < 1 / s.τ
    · simp only [trialPotential, update, hs, hg, hsmall, ite_true, ite_false, true_or, or_true, reduceCtorEq, sub_self, le_refl]
    by_cases hm : ‖s.b • readGradient reply + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2
    · exact False.elim (ha ⟨hs, hg, hsmall, hm⟩)
    · simp only [trialPotential, update, hs, hg, hsmall, hm, ite_true, ite_false, true_or, or_true, reduceCtorEq, sub_self, le_refl]
  | finished => exact False.elim (hn hs)

lemma trialPotential_credit {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (hn : s.phase ≠ .finished) (hn' : (update s reply).phase ≠ .finished)
    (hb : TrialBounds τlo ρ Z s) (hb' : TrialBounds τlo ρ Z (update s reply)) :
    (if RadiusStart s (update s reply) then (1 : ℝ) else 0) ≤
      trialPotential τlo ρ Z (update s reply) - trialPotential τlo ρ Z s +
        (if Accepted s reply then 1024 * (1 + Real.log Z) ^ 2 else 0) := by
  by_cases ha : Accepted s reply
  · have hstart := accepted_not_radiusStart s reply ha
    have hpot : trialPotential τlo ρ Z (update s reply) = 0 := by
      rw [accepted_update s reply ha]
      exact trialPotential_accept _ τlo ρ Z
    have hh := (trialPotential_bounds s hlo hρ hZ hb).2
    simp only [ite_eq_right hstart, ite_eq_left ha, hpot]
    linarith
  · simp only [ite_eq_right ha, add_zero]
    exact trialPotential_nonaccepted_credit s reply hlo hρ hZ hn hn' hb hb' ha

lemma finite_potential_sum (q v c : ℕ → ℝ) (N : ℕ)
    (hs : ∀ k < N, q k ≤ v (k + 1) - v k + c k) :
    (∑ k ∈ Finset.range N, q k) ≤ v N - v 0 + ∑ k ∈ Finset.range N, c k := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun k hk => hs k (by omega))
    have ht := hs N (by omega)
    simp only [Finset.sum_range_succ]
    linarith

lemma path_radius_start_count {p : Public} {τlo ρ Z : ℝ} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (h0 : (s 0).phase = .centerGradient)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hn : ∀ k ≤ N, (s k).phase ≠ .finished)
    (hb : ∀ k ≤ N, TrialBounds τlo ρ Z (s k)) :
    (∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then (1 : ℝ) else 0) ≤
      1024 * (1 + Real.log Z) ^ 2 *
        ((∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then (1 : ℝ) else 0) + 1) := by
  have hstep (k : ℕ) (hk : k < N) := trialPotential_credit (s k) (reply k) hlo hρ hZ
    (hn k hk.le) (by rw [← hs k hk]; exact hn (k + 1) (by omega))
    (hb k hk.le) (by rw [← hs k hk]; exact hb (k + 1) (by omega))
  have hsum := finite_potential_sum
    (fun k => if RadiusStart (s k) (s (k + 1)) then (1 : ℝ) else 0)
    (fun k => trialPotential τlo ρ Z (s k))
    (fun k => if Accepted (s k) (reply k) then 1024 * (1 + Real.log Z) ^ 2 else 0) N
    (fun k hk => by simpa only [← hs k hk] using hstep k hk)
  have hz := trialPotential_center (s 0) τlo ρ Z h0
  have hu := (trialPotential_bounds (s N) hlo hρ hZ (hb N le_rfl)).2
  have hc : (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then 1024 * (1 + Real.log Z) ^ 2 else 0) =
      1024 * (1 + Real.log Z) ^ 2 * (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [hz, hc] at hsum
  nlinarith

lemma nonaccepted_center_displacement {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (ha : ¬ Accepted s reply) :
    ‖(update s reply).center - (update s reply).w‖ = ‖s.center - s.w‖ := by
  have he := nonaccepted_outer_fields s reply ha
  have hA := congrArg Prod.fst he
  have hη := congrArg (fun q : ℝ × ℝ × p.E × p.E => q.2.1) he
  have hw := congrArg (fun q : ℝ × ℝ × p.E × p.E => q.2.2.1) he
  have hz := congrArg (fun q : ℝ × ℝ × p.E × p.E => q.2.2.2) he
  dsimp only at hA hη hw hz
  simp only [State.center, State.a, hA, hη, hw, hz]


lemma weighted_trialPotential_credit {p : Public} {τlo ρ Z : ℝ} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (hn : s.phase ≠ .finished) (hn' : (update s reply).phase ≠ .finished)
    (hb : TrialBounds τlo ρ Z s) (hb' : TrialBounds τlo ρ Z (update s reply)) :
    (if RadiusStart s (update s reply) then ‖(update s reply).center - (update s reply).w‖ else 0) ≤
      ‖(update s reply).center - (update s reply).w‖ * trialPotential τlo ρ Z (update s reply) -
        ‖s.center - s.w‖ * trialPotential τlo ρ Z s +
        (if Accepted s reply then 1024 * (1 + Real.log Z) ^ 2 * ‖s.center - s.w‖ else 0) := by
  by_cases ha : Accepted s reply
  · have hstart := accepted_not_radiusStart s reply ha
    have hpot : trialPotential τlo ρ Z (update s reply) = 0 := by
      rw [accepted_update s reply ha]
      exact trialPotential_accept _ τlo ρ Z
    have hh := mul_le_mul_of_nonneg_left (trialPotential_bounds s hlo hρ hZ hb).2 (norm_nonneg (s.center - s.w))
    simp only [ite_eq_right hstart, ite_eq_left ha, hpot, mul_zero]
    nlinarith
  · have hd := nonaccepted_center_displacement s reply ha
    have hh := trialPotential_nonaccepted_credit s reply hlo hρ hZ hn hn' hb hb' ha
    have hm := mul_le_mul_of_nonneg_left hh (norm_nonneg (s.center - s.w))
    simp only [ite_eq_right ha, add_zero, hd]
    by_cases hstart : RadiusStart s (update s reply)
    · simp only [ite_eq_left hstart, mul_one] at hm ⊢
      nlinarith
    · simp only [ite_eq_right hstart, mul_zero] at hm ⊢
      nlinarith

lemma path_weighted_radius_start_count {p : Public} {τlo ρ Z : ℝ} (s : ℕ → State p)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hlo : 0 < τlo) (hρ : 0 < ρ) (hZ : 2 ≤ Z)
    (h0 : (s 0).phase = .centerGradient)
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hn : ∀ k ≤ N, (s k).phase ≠ .finished)
    (hb : ∀ k ≤ N, TrialBounds τlo ρ Z (s k)) :
    (∑ k ∈ Finset.range N, if RadiusStart (s k) (s (k + 1)) then ‖(s (k + 1)).center - (s (k + 1)).w‖ else 0) ≤
      1024 * (1 + Real.log Z) ^ 2 *
        ((∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then ‖(s k).center - (s k).w‖ else 0) +
          ‖(s N).center - (s N).w‖) := by
  have hstep (k : ℕ) (hk : k < N) := weighted_trialPotential_credit (s k) (reply k) hlo hρ hZ
    (hn k hk.le) (by rw [← hs k hk]; exact hn (k + 1) (by omega))
    (hb k hk.le) (by rw [← hs k hk]; exact hb (k + 1) (by omega))
  have hsum := finite_potential_sum
    (fun k => if RadiusStart (s k) (s (k + 1)) then ‖(s (k + 1)).center - (s (k + 1)).w‖ else 0)
    (fun k => ‖(s k).center - (s k).w‖ * trialPotential τlo ρ Z (s k))
    (fun k => if Accepted (s k) (reply k) then 1024 * (1 + Real.log Z) ^ 2 * ‖(s k).center - (s k).w‖ else 0) N
    (fun k hk => by simpa only [← hs k hk] using hstep k hk)
  have hz := trialPotential_center (s 0) τlo ρ Z h0
  have hu := mul_le_mul_of_nonneg_left (trialPotential_bounds (s N) hlo hρ hZ (hb N le_rfl)).2
    (norm_nonneg ((s N).center - (s N).w))
  have hc : (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then 1024 * (1 + Real.log Z) ^ 2 * ‖(s k).center - (s k).w‖ else 0) =
      1024 * (1 + Real.log Z) ^ 2 * (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then ‖(s k).center - (s k).w‖ else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [hz, mul_zero, hc] at hsum
  nlinarith


lemma scaleCeiling_bound {p : Public} {Z : ℝ} (hR : 0 < p.R) (hε : 0 < p.ε) (hZ : 2 ≤ Z)
    (hΔ : p.Δ / p.ε ≤ Z) (hM : p.M₀ * p.R ^ 3 / p.ε ≤ Z) :
    PointwiseHessianBounds.scaleCeiling p ≤ 1024 * Z * (p.ε / p.R ^ 2) := by
  have hZp : 0 < Z := by linarith
  have hΔ' := (div_le_iff₀ hε).mp hΔ
  have hM' := (div_le_iff₀ hε).mp hM
  have hR2 := sq_pos_of_pos hR
  unfold PointwiseHessianBounds.scaleCeiling
  simp only [initialWeight, one_div_div]
  rw [← mul_div_assoc]
  apply max_le
  · apply div_le_div_of_nonneg_right _ hR2.le
    nlinarith [mul_pos hZp hε]
  · apply (le_div_iff₀ hR2).mpr
    nlinarith

lemma trialBounds_of_scalars {p : Public} {f : p.E → ℝ} {xs : p.E} {Z : ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hε : 0 < p.ε) (hZ : 2 ≤ Z)
    (hΔ : p.Δ / p.ε ≤ Z) (hM : p.M₀ * p.R ^ 3 / p.ε ≤ Z)
    (hi : StateInvariant f xs s) (hA : s.A < targetWeight p)
    (hb : PointwiseHessianBounds.BoundedScales s) (hinit : RadiusInitializationInvariant s) :
    TrialBounds (p.ε / p.R ^ 2) (p.R / (1048576 * Z)) Z s := by
  intro hp
  have hpar : InnerParameters f s := by
    have hh := hi.phase
    rcases hp with h | h
    · simp only [PhaseInvariant, h] at hh
      exact hh.1
    · simp only [PhaseInvariant, h] at hh
      exact hh.1
  have hZp : 0 < Z := by linarith
  have hlo : 0 < p.ε / p.R ^ 2 := by positivity
  have hτlo : p.ε / p.R ^ 2 ≤ s.τ :=
    (PointwiseHessianBounds.active_scale_lower hR hε hi.outer hA).le.trans hpar.η_le
  have hτhi := (hb.2 hp).trans (scaleCeiling_bound hR hε hZ hΔ hM)
  have hτratio : s.τ / (p.ε / p.R ^ 2) ≤ 1024 * Z := (div_le_iff₀ hlo).mpr hτhi
  have hτscaled : s.τ * p.R ^ 2 / p.ε ≤ 1024 * Z := by
    simpa only [div_div_eq_mul_div] using hτratio
  have hrlo := (initialRadius_lower hM₀ hR hε hZ hpar.τ_pos hτlo hτscaled hM).trans (hinit hp)
  have hrhi := hpar.r_le.trans (PointwiseHessianTuning.radiusCap_le p s.τ)
  have hrratio : s.r / (p.R / (1048576 * Z)) ≤ 16777216 * Z := by
    rw [div_div_eq_mul_div]
    apply (div_le_iff₀ hR).mpr
    have hh := mul_le_mul_of_nonneg_right hrhi (show 0 ≤ 1048576 * Z by positivity)
    nlinarith
  exact ⟨hτlo, hrlo, hτratio, hrratio⟩

lemma path_trialBounds {p : Public} {f : p.E → ℝ} {xs : p.E} {Z : ℝ}
    (s : ℕ → State p) (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R) (hε : 0 < p.ε) (hZ : 2 ≤ Z)
    (hΔ : p.Δ / p.ε ≤ Z) (hM : p.M₀ * p.R ^ 3 / p.ε ≤ Z)
    (h0 : (s 0).phase = .centerGradient)
    (hi : ∀ k ≤ N, StateInvariant f xs (s k))
    (hA : ∀ k ≤ N, (s k).A < targetWeight p)
    (hb : ∀ k ≤ N, PointwiseHessianBounds.BoundedScales (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k)) :
    ∀ k ≤ N, TrialBounds (p.ε / p.R ^ 2) (p.R / (1048576 * Z)) Z (s k) := by
  intro k hk
  apply trialBounds_of_scalars (s k) hM₀ hR hε hZ hΔ hM (hi k hk) (hA k hk) (hb k hk)
  exact radiusInitialization_path s reply k h0 (fun i hi' => (hi i (by omega)).phase)
    (fun i hi' => hs i (by omega))


end LongTails.Proofs.PointwiseHessianTrialCount
