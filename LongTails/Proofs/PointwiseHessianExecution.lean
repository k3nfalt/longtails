import LongTails.Proofs.PointwiseHessianOuter
import LongTails.Proofs.PointwiseHessianTrial
import LongTails.Proofs.ExecutionHistory

namespace LongTails.Proofs.PointwiseHessianExecution

open OracleTemplate
open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianTuning
open LongTails.Proofs.PointwiseHessianTrial

structure NewtonReady {p : Public} (f : p.E → ℝ) (s : State p) : Prop where
  τ_pos : 0 < s.τ
  r_pos : 0 < s.r
  b_pos : 0 < s.b
  b_le : s.b ≤ 1 / s.τ
  gradient_eq : s.g = gradient f s.x
  radius : ‖s.x - s.center‖ ≤ 2 * s.r
  residual : ‖s.b • s.g + s.x - s.center‖ ≤ 2 * continuationRatio p s.τ s.r * s.r

lemma startTrial_ready {p : Public} {f : p.E → ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (hg : s.centerG = gradient f s.center) (hn : s.centerG ≠ 0) :
    NewtonReady f (startTrial s τ r) := by
  have ha := continuationRatio_pos p hM₀ hM₁ hτ hr.le
  have hb := initialRegularization_pos p hM₀ hM₁ hτ hr s.centerG hn
  have he := initialRegularization_residual p hM₀ hM₁ hτ hr s.centerG hn
  constructor
  · exact hτ
  · exact hr
  · exact hb
  · exact min_le_left _ _
  · exact hg
  · change ‖s.center - s.center‖ ≤ 2 * r
    simp only [sub_self, norm_zero]
    positivity
  · change ‖initialRegularization p τ r s.centerG • s.centerG + s.center - s.center‖ ≤
      2 * continuationRatio p τ r * r
    rw [add_sub_cancel_right]
    nlinarith [mul_pos ha hr]

lemma newton_query_residual {p : Public} {f : p.E → ℝ} (s : State p)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hi : NewtonReady f s) :
    let y := newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x)
    ‖s.b • gradient f y + y - s.center‖ ≤ continuationRatio p s.τ s.r * s.r / 2 := by
  have he := hi.residual
  rw [hi.gradient_eq] at he ⊢
  have hh := (newton_contract p hf hc hM₀ hM₁ hT hi.τ_pos hi.r_pos hi.b_pos hi.b_le
    s.center s.x hi.radius he).2
  dsimp only at hh ⊢
  linarith

lemma gradient_continue_ready {p : Public} {f : p.E → ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hτ : 0 < s.τ) (hr : 0 < s.r)
    (hb : 0 < s.b) (hbt : s.b ≤ 1 / s.τ) (hx : ‖s.x - s.center‖ ≤ 2 * s.r)
    (he : ‖s.b • gradient f s.x + s.x - s.center‖ ≤ continuationRatio p s.τ s.r * s.r) :
    NewtonReady f { s with
      phase := .newtonHessian
      g := gradient f s.x
      b := min (1 / s.τ) (s.b * (1 + continuationRatio p s.τ s.r / 8)) } := by
  have ha := continuationRatio_pos p hM₀ hM₁ hτ hr.le
  constructor
  · exact hτ
  · exact hr
  · change 0 < min (1 / s.τ) (s.b * (1 + continuationRatio p s.τ s.r / 8))
    positivity
  · exact min_le_left _ _
  · rfl
  · exact hx
  · exact continued_residual p hM₀ hM₁ hτ hr.le hb hbt s.center s.x (gradient f s.x) hx he

lemma gradient_refine_ready {p : Public} {f : p.E → ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hτ : 0 < s.τ) (hr : 0 < s.r)
    (hb : 0 < s.b) (hbt : s.b ≤ 1 / s.τ) (hx : ‖s.x - s.center‖ ≤ 2 * s.r)
    (he : ‖s.b • gradient f s.x + s.x - s.center‖ ≤ continuationRatio p s.τ s.r * s.r) :
    NewtonReady f { s with phase := .newtonHessian, g := gradient f s.x } := by
  have ha := continuationRatio_pos p hM₀ hM₁ hτ hr.le
  refine ⟨hτ, hr, hb, hbt, rfl, hx, ?_⟩
  change ‖s.b • gradient f s.x + s.x - s.center‖ ≤ 2 * continuationRatio p s.τ s.r * s.r
  nlinarith [mul_pos ha hr]

lemma hessian_update_guard {p : Public} (s : State p) (H : p.E →L[ℝ] p.E)
    (hs : s.phase = .newtonHessian)
    (hg : ‖newtonPoint p s.b s.center s.x s.g H - s.center‖ ≤ 2 * s.r) :
    update s (.inr H) = { s with
      phase := .newtonGradient
      x := newtonPoint p s.b s.center s.x s.g H } := by
  simp [update, hs, readHessian, hg]

lemma hessian_update_failure {p : Public} (s : State p) (H : p.E →L[ℝ] p.E)
    (hs : s.phase = .newtonHessian)
    (hg : ¬ ‖newtonPoint p s.b s.center s.x s.g H - s.center‖ ≤ 2 * s.r) :
    update s (.inr H) = failedTrial s := by
  simp [update, hs, readHessian, hg]

lemma failedTrial_ready {p : Public} {f : p.E → ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hτ : 0 < s.τ) (hr : 0 < s.r)
    (hg : s.centerG = gradient f s.center) (hn : s.centerG ≠ 0) :
    NewtonReady f (failedTrial s) := by
  unfold failedTrial
  split_ifs
  · apply startTrial_ready s hM₀ hM₁ hτ _ hg hn
    exact lt_min (by positivity) (radiusCap_pos p hM₀ hR hτ)
  · apply startTrial_ready s hM₀ hM₁ (by positivity) _ hg hn
    exact initialRadius_pos p hM₀ hR hε (by positivity)

lemma guarded_gradient_accuracy {p : Public} {f : p.E → ℝ}
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) (x c xs : p.E)
    (hR : 0 < p.R) (hε : 0 < p.ε) {r : ℝ}
    (hr : r ≤ 16 * p.R) (hx : ‖x - c‖ ≤ 2 * r) (hcenter : ‖c - xs‖ ≤ 4 * p.R)
    (hg : ‖gradient f x‖ ≤ gradientThreshold p) : f x - f xs ≤ p.ε := by
  have hd : ‖x - xs‖ ≤ 36 * p.R := by
    have hh := norm_add_le (x - c) (c - xs)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hh := LongTails.Proofs.PointwiseHessianProx.gradient_gap hf hc x xs
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg (gradient f x))
  unfold gradientThreshold at hg
  have ht := (le_div_iff₀ (show 0 < 1000 * p.R by positivity)).mp hg
  nlinarith

lemma center_gradient_accuracy {p : Public} {f : p.E → ℝ}
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) (s : State p) (xs : p.E)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hmin : ∀ x, f xs ≤ f x)
    (hi : PointwiseHessianOuter.Invariant f xs s)
    (hg : ‖gradient f s.center‖ ≤ gradientThreshold p) : f s.center - f xs ≤ p.ε := by
  have hz := PointwiseHessianOuter.energy_radius s xs hR.le hi.A_pos.le hmin hi.energy_le
  have hcenter := PointwiseHessianOuter.center_radius s xs hR.le hi.A_pos.le hi.η_pos hi.radius hz
  apply guarded_gradient_accuracy hf hc s.center s.center xs hR hε
    (r := 0) (by positivity) (by simp) hcenter hg

structure InnerParameters {p : Public} (f : p.E → ℝ) (s : State p) : Prop where
  τ_pos : 0 < s.τ
  η_le : s.η ≤ s.τ
  r_pos : 0 < s.r
  r_le : s.r ≤ radiusCap p s.τ
  b_pos : 0 < s.b
  b_le : s.b ≤ 1 / s.τ
  cached_gradient : s.centerG = gradient f s.center
  cached_nonzero : s.centerG ≠ 0
  scale_gap : s.τ = s.η ∨ 2 * s.η ≤ s.τ

def PhaseInvariant {p : Public} (f : p.E → ℝ) (xs : p.E) (s : State p) : Prop :=
  match s.phase with
  | .centerGradient => True
  | .newtonHessian => InnerParameters f s ∧ NewtonReady f s
  | .newtonGradient => InnerParameters f s ∧ ‖s.x - s.center‖ ≤ 2 * s.r ∧
      ‖s.b • gradient f s.x + s.x - s.center‖ ≤ continuationRatio p s.τ s.r * s.r / 2
  | .finished => f s.out - f xs ≤ p.ε

structure StateInvariant {p : Public} (f : p.E → ℝ) (xs : p.E) (s : State p) : Prop where
  outer : PointwiseHessianOuter.Invariant f xs s
  phase : PhaseInvariant f xs s

lemma startTrial_parameters {p : Public} {f : p.E → ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) {τ r : ℝ} (hτ : 0 < τ) (hη : s.η ≤ τ)
    (hr : 0 < r) (hrc : r ≤ radiusCap p τ)
    (hg : s.centerG = gradient f s.center) (hn : s.centerG ≠ 0)
    (hgap : τ = s.η ∨ 2 * s.η ≤ τ) :
    InnerParameters f (startTrial s τ r) := by
  refine ⟨hτ, hη, hr, hrc, ?_, min_le_left _ _, hg, hn, hgap⟩
  exact initialRegularization_pos p hM₀ hM₁ hτ hr s.centerG hn

lemma failedTrial_parameters {p : Public} {f : p.E → ℝ} (s : State p)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hi : InnerParameters f s) : InnerParameters f (failedTrial s) := by
  unfold failedTrial
  split_ifs
  · apply startTrial_parameters s hM₀ hM₁ hi.τ_pos hi.η_le _ (min_le_right _ _)
      hi.cached_gradient hi.cached_nonzero hi.scale_gap
    exact lt_min (by linarith [hi.r_pos]) (radiusCap_pos p hM₀ hR hi.τ_pos)
  · apply startTrial_parameters s hM₀ hM₁ (by linarith [hi.τ_pos])
      (by linarith [hi.η_le, hi.τ_pos]) _ (min_le_right _ _)
      hi.cached_gradient hi.cached_nonzero (Or.inr (by linarith [hi.η_le]))
    exact initialRadius_pos p hM₀ hR hε (by linarith [hi.τ_pos])

lemma initial_stateInvariant {p : Public} {f : p.E → ℝ} (xs : p.E)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (hx : ‖p.x0 - xs‖ ≤ p.R) (hg : f p.x0 - f xs ≤ p.Δ) :
    StateInvariant f xs (initial p) := by
  refine ⟨PointwiseHessianOuter.initial_invariant xs hR hΔ hx hg, ?_⟩
  unfold PhaseInvariant initial
  split_ifs with h
  · exact hg.trans h
  · trivial

lemma outer_transfer {p : Public} {f : p.E → ℝ} {xs : p.E} {s t : State p}
    (hi : PointwiseHessianOuter.Invariant f xs s)
    (hA : t.A = s.A) (hη : t.η = s.η) (hw : t.w = s.w) (hz : t.z = s.z) :
    PointwiseHessianOuter.Invariant f xs t := by
  constructor
  · simpa only [hA] using hi.A_pos
  · simpa only [hη] using hi.η_pos
  · simpa only [hη, hA] using hi.scale
  · simpa only [hA] using hi.weight_lower
  · simpa only [PointwiseHessianOuter.energy, hA, hw, hz] using hi.energy_le
  · simpa only [hw] using hi.radius

lemma center_update_invariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hmin : ∀ x, f xs ≤ f x) (hi : StateInvariant f xs s) (hs : s.phase = .centerGradient) :
    StateInvariant f xs (update s (.inl (gradient f s.center))) := by
  simp only [update, hs, readGradient]
  split_ifs with hg
  · refine ⟨outer_transfer hi.outer rfl rfl rfl rfl, ?_⟩
    exact center_gradient_accuracy hf hc s xs hR hε hmin hi.outer hg
  · have hgn : gradient f s.center ≠ 0 := by
      intro hz
      apply hg
      rw [hz, norm_zero]
      unfold gradientThreshold
      positivity
    have hr := initialRadius_pos p hM₀ hR hε hi.outer.η_pos
    refine ⟨outer_transfer hi.outer rfl rfl rfl rfl, ?_⟩
    constructor
    · exact startTrial_parameters { s with centerG := gradient f s.center } hM₀ hM₁
        hi.outer.η_pos le_rfl hr (min_le_right _ _) rfl hgn (Or.inl rfl)
    · exact startTrial_ready { s with centerG := gradient f s.center } hM₀ hM₁
        hi.outer.η_pos hr rfl hgn

lemma hessian_update_invariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hi : StateInvariant f xs s) (hs : s.phase = .newtonHessian) :
    StateInvariant f xs (update s (.inr (fderiv ℝ (gradient f) s.x))) := by
  have hp := hi.phase
  simp only [PhaseInvariant, hs] at hp
  obtain ⟨hp, hn⟩ := hp
  by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r
  · rw [hessian_update_guard s _ hs hg]
    refine ⟨outer_transfer hi.outer rfl rfl rfl rfl,
      ⟨hp.τ_pos, hp.η_le, hp.r_pos, hp.r_le, hp.b_pos, hp.b_le, hp.cached_gradient, hp.cached_nonzero, hp.scale_gap⟩, hg, ?_⟩
    exact newton_query_residual s hf hc hM₀ hM₁ hT hn
  · rw [hessian_update_failure s _ hs hg]
    have ho : PointwiseHessianOuter.Invariant f xs (failedTrial s) := by
      unfold failedTrial
      split_ifs <;> exact outer_transfer hi.outer rfl rfl rfl rfl
    refine ⟨ho, ?_⟩
    have hr := failedTrial_ready s hM₀ hM₁ hR hε hp.τ_pos hp.r_pos hp.cached_gradient hp.cached_nonzero
    have hp' := failedTrial_parameters s hM₀ hM₁ hR hε hp
    have hs' : (failedTrial s).phase = .newtonHessian := by
      unfold failedTrial
      split_ifs <;> rfl
    simpa only [PhaseInvariant, hs'] using And.intro hp' hr

lemma accept_stateInvariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hmin : ∀ x, f xs ≤ f x) (hi : PointwiseHessianOuter.Invariant f xs s)
    (hητ : s.η ≤ s.τ) (hg : s.g = gradient f s.x)
    (hres : ‖(1 / s.τ) • s.g + s.x - s.center‖ ≤ ‖s.x - s.center‖ / 2) :
    StateInvariant f xs (accept s) := by
  have ho := PointwiseHessianOuter.accept_invariant hf hc s xs hR hmin hi hητ hg hres
  refine ⟨ho, ?_⟩
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · have hp : (accept s).phase = .finished := by simp [accept, finish, ht]
    simp only [PhaseInvariant, hp]
    rw [PointwiseHessianOuter.accept_output]
    apply PointwiseHessianOuter.target_accuracy ho hε
    rwa [(PointwiseHessianOuter.accept_fields s).1]
  · have hp : (accept s).phase = .centerGradient := by simp [accept, ht]
    simp only [PhaseInvariant, hp]

lemma gradient_update_invariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hmin : ∀ x, f xs ≤ f x) (hi : StateInvariant f xs s) (hs : s.phase = .newtonGradient) :
    StateInvariant f xs (update s (.inl (gradient f s.x))) := by
  have hp := hi.phase
  simp only [PhaseInvariant, hs] at hp
  obtain ⟨hp, hx, he⟩ := hp
  have ha := continuationRatio_pos p hM₀ hM₁ hp.τ_pos hp.r_pos.le
  have he' : ‖s.b • gradient f s.x + s.x - s.center‖ ≤ continuationRatio p s.τ s.r * s.r := by
    nlinarith [mul_pos ha hp.r_pos]
  simp only [update, hs, readGradient]
  split_ifs with hg hb hms
  · refine ⟨outer_transfer hi.outer rfl rfl rfl rfl, ?_⟩
    have hz := PointwiseHessianOuter.energy_radius s xs hR.le hi.outer.A_pos.le hmin hi.outer.energy_le
    have hcenter := PointwiseHessianOuter.center_radius s xs hR.le hi.outer.A_pos.le
      hi.outer.η_pos hi.outer.radius hz
    exact guarded_gradient_accuracy hf hc s.x s.center xs hR hε
      (hp.r_le.trans (radiusCap_le p s.τ)) hx hcenter hg
  · refine ⟨outer_transfer hi.outer rfl rfl rfl rfl, ?_, ?_⟩
    · refine ⟨hp.τ_pos, hp.η_le, hp.r_pos, hp.r_le, ?_, min_le_left _ _,
        hp.cached_gradient, hp.cached_nonzero, hp.scale_gap⟩
      change 0 < min (1 / s.τ) (s.b * (1 + continuationRatio p s.τ s.r / 8))
      have hτp := hp.τ_pos
      have hbp := hp.b_pos
      positivity
    · exact gradient_continue_ready s hM₀ hM₁ hp.τ_pos hp.r_pos hp.b_pos hp.b_le hx he'
  · have hbe : s.b = 1 / s.τ := le_antisymm hp.b_le (le_of_not_gt hb)
    apply accept_stateInvariant { s with g := gradient f s.x } xs hf hc hR hε hmin
      (outer_transfer hi.outer rfl rfl rfl rfl) hp.η_le rfl
    simpa [hbe, State.center, State.a] using hms
  · refine ⟨outer_transfer hi.outer rfl rfl rfl rfl, ?_, ?_⟩
    · exact ⟨hp.τ_pos, hp.η_le, hp.r_pos, hp.r_le, hp.b_pos, hp.b_le,
        hp.cached_gradient, hp.cached_nonzero, hp.scale_gap⟩
    · exact gradient_refine_ready s hM₀ hM₁ hp.τ_pos hp.r_pos hp.b_pos hp.b_le hx he'

lemma oracle_step_invariant {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : ∀ x, f xs ≤ f x) (hi : StateInvariant f xs s)
    (O : Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (history : List ((Fin 2 × p.E) × (p.E ⊕ (p.E →L[ℝ] p.E)))) (seed : O.Seed history.length) :
    StateInvariant f xs (update s (O.answer history (query s) seed)) := by
  cases hs : s.phase with
  | centerGradient =>
    rw [show query s = (0, s.center) by simp [query, hs], hgrad]
    exact center_update_invariant s xs hf hc hM₀ hM₁ hR hε hmin hi hs
  | newtonHessian =>
    rw [show query s = (1, s.x) by simp [query, hs], hHess]
    exact hessian_update_invariant s xs hf hc hM₀ hM₁ hR hε hT hi hs
  | newtonGradient =>
    rw [show query s = (0, s.x) by simp [query, hs], hgrad]
    exact gradient_update_invariant s xs hf hc hM₀ hM₁ hR hε hmin hi hs
  | finished =>
    rw [PointwiseHessianOuter.finished_output s _ hs]
    exact hi

lemma trace_invariant {p : Public} {f : p.E → ℝ} (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : ∀ x, f xs ≤ f x) (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (O : Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    StateInvariant f xs (executeIndexedState O (algorithm p) seed ξ n).1 := by
  induction n with
  | zero => exact initial_stateInvariant xs hR hΔ hx hgap
  | succ n ih =>
    exact oracle_step_invariant _ xs hf hc hM₀ hM₁ hR hε hT hmin ih O hgrad hHess _ _

lemma trace_finished_stable {p : Public}
    (O : Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) {n : ℕ}
    (hn : (executeIndexedState O (algorithm p) seed ξ n).1.phase = .finished) (m : ℕ) :
    (executeIndexedState O (algorithm p) seed ξ (n + m)).1 =
      (executeIndexedState O (algorithm p) seed ξ n).1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by omega, executeIndexedState]
    change update (executeIndexedState O (algorithm p) seed ξ (n + m)).1 _ = _
    rw [ih]
    exact PointwiseHessianOuter.finished_output _ _ hn

lemma execute_of_finished {p : Public}
    (O : Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hn : (executeIndexedState O (algorithm p) seed ξ K).1.phase = .finished) :
    execute O (algorithm p) (fun _ => K) seed ξ =
      (executeIndexedState O (algorithm p) seed ξ K).1.out := by
  classical
  let remaining : ℕ → Fin 2 → ℕ := fun n => Nat.rec (fun _ => K)
    (fun k rem => Function.update rem
      (query (executeIndexedState O (algorithm p) seed ξ k).1).1
      (rem (query (executeIndexedState O (algorithm p) seed ξ k).1).1 - 1)) n
  have hrem (n : ℕ) (i : Fin 2) : K - n ≤ remaining n i := by
    induction n generalizing i with
    | zero => exact le_rfl
    | succ n ih =>
      change K - (n + 1) ≤ Function.update (remaining n)
        (query (executeIndexedState O (algorithm p) seed ξ n).1).1
        (remaining n (query (executeIndexedState O (algorithm p) seed ξ n).1).1 - 1) i
      by_cases he : i = (query (executeIndexedState O (algorithm p) seed ξ n).1).1
      · rw [he, Function.update_self]
        have hh := ih (query (executeIndexedState O (algorithm p) seed ξ n).1).1
        omega
      · rw [Function.update_of_ne he]
        have hh := ih i
        omega
  apply execute_eq_of_history_safe_prefix O (algorithm p) (fun _ => K) seed ξ remaining K
    (executeIndexedState O (algorithm p) seed ξ K).1.out rfl (fun _ => rfl)
  · intro k hk
    change 0 < remaining k (query (executeIndexedState O (algorithm p) seed ξ k).1).1
    have hh := hrem k (query (executeIndexedState O (algorithm p) seed ξ k).1).1
    omega
  · intro k hk
    have he := trace_finished_stable O seed ξ hn (k - K)
    rw [Nat.add_sub_of_le hk] at he
    change (executeIndexedState O (algorithm p) seed ξ k).1.out = _
    rw [he]
  · simp only [Fin.sum_univ_two]
    omega

end LongTails.Proofs.PointwiseHessianExecution
