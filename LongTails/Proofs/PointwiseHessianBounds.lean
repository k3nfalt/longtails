import LongTails.Proofs.PointwiseHessianLedger
import LongTails.Proofs.PointwiseHessianGrowth

namespace LongTails.Proofs.PointwiseHessianBounds

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianGeometry

lemma stored_gap {p : Public} {f : p.E → ℝ} {xs : p.E} {s : State p}
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hi : PointwiseHessianOuter.Invariant f xs s) :
    f s.w - f xs ≤ 2 * p.Δ := by
  have hA := PointwiseHessianTuning.initialWeight_pos p hR hΔ
  calc
    _ ≤ p.R ^ 2 / s.A := PointwiseHessianOuter.invariant_gap hi
    _ ≤ p.R ^ 2 / initialWeight p :=
      div_le_div_of_nonneg_left (sq_nonneg _) hA hi.weight_lower
    _ = 2 * p.Δ := by unfold initialWeight; field_simp

lemma sublevel_hessian_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    {xs : E} (hmin : IsMinOn f Set.univ xs) {M₀ M₁ H₀ R Δ : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ M₀ + M₁ * ‖gradient f x‖)
    (x0 w : E) (hH : ‖fderiv ℝ (gradient f) x0‖ ≤ H₀)
    (hx0 : ‖x0 - xs‖ ≤ R) (hg0 : f x0 - f xs ≤ Δ)
    (hw : ‖w - xs‖ ≤ 4 * R) (hgw : f w - f xs ≤ 2 * Δ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (gradient f) (xs + t • (w - xs))‖ ≤
      4 * H₀ + 12 * M₀ * R + 34 * M₁ ^ 2 * R ^ 2 * Δ := by
  have hg0p : 0 ≤ f x0 - f xs := sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hgwp : 0 ≤ f w - f xs := sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hstar : ‖fderiv ℝ (gradient f) xs‖ ≤ 2 * H₀ + 2 * M₀ * R + M₁ ^ 2 * R ^ 2 * Δ := by
    apply (minimizer_hessian_bound hf hc hmin hM₀ hM₁ hT x0).trans
    gcongr
  have hh := segment_hessian_bound hf hc hmin hM₀ hM₁ hT (w - xs)
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) ht
  simp only [zero_smul, add_zero, add_sub_cancel] at hh
  calc
    _ ≤ 2 * ‖fderiv ℝ (gradient f) xs‖ + 2 * M₀ * ‖w - xs‖ +
        M₁ ^ 2 * ‖w - xs‖ ^ 2 * (f w - f xs) := hh
    _ ≤ 2 * (2 * H₀ + 2 * M₀ * R + M₁ ^ 2 * R ^ 2 * Δ) +
        2 * M₀ * (4 * R) + M₁ ^ 2 * (4 * R) ^ 2 * (2 * Δ) := by gcongr
    _ = _ := by ring

lemma ray_gradient_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {xs : E} (hmin : IsMinOn f Set.univ xs) (w : E) {K : ℝ} (hK : 0 ≤ K)
    (hH : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (gradient f) (xs + t • (w - xs))‖ ≤ K) :
    ‖gradient f w‖ ≤ K * ‖w - xs‖ := by
  obtain ⟨_, hg, _⟩ := LongTails.Proofs.GradientDependentLocal.derivative_chain hf
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => gradient f (xs + u • (w - xs)))
      (fderiv ℝ (gradient f) (xs + t • (w - xs)) (w - xs)) t := by
    apply (hg _).comp_hasDerivAt
    simpa using ((hasDerivAt_id t).smul_const (w - xs)).const_add xs
  have hh := PointwiseHessianLocalization.unit_interval_transport _ _ hd
    (fun _ => K * ‖w - xs‖) continuous_const (fun _ _ => by positivity)
    (fun t ht => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hH t ht) (norm_nonneg _)))
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  simpa [minimizer_gradient hmin] using hh

lemma initial_live_weight (p : Public) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hs : (initial p).phase ≠ .finished) : (initial p).A < targetWeight p := by
  have hd : p.ε < p.Δ := by
    by_contra hn
    have hh : p.Δ ≤ p.ε := le_of_not_gt hn
    exact hs (by simp [initial, hh])
  change p.R ^ 2 / (2 * p.Δ) < p.R ^ 2 / p.ε
  exact div_lt_div_of_pos_left (sq_pos_of_pos hR) hε (by linarith)

lemma accept_live_weight {p : Public} (s : State p) (hs : (accept s).phase ≠ .finished) :
    (accept s).A < targetWeight p := by
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · exact False.elim (hs (by simp [accept, finish, ht]))
  · rw [(PointwiseHessianOuter.accept_fields s).1]
    exact lt_of_not_ge ht

lemma update_live_weight {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hi : s.phase ≠ .finished → s.A < targetWeight p)
    (hs : (update s reply).phase ≠ .finished) : (update s reply).A < targetWeight p := by
  cases hp : s.phase with
  | finished =>
    exact False.elim (hs (by simp [update, hp]))
  | centerGradient =>
    have hA := hi (by simp [hp])
    simp only [update, hp] at hs ⊢
    split_ifs at hs ⊢
    · exact False.elim (hs rfl)
    · exact hA
  | newtonHessian =>
    have hA := hi (by simp [hp])
    simp only [update, hp] at hs ⊢
    split_ifs
    · exact hA
    · unfold failedTrial
      split_ifs <;> exact hA
  | newtonGradient =>
    have hA := hi (by simp [hp])
    simp only [update, hp] at hs ⊢
    split_ifs at hs ⊢
    · exact False.elim (hs rfl)
    · exact hA
    · exact accept_live_weight _ hs
    · exact hA

lemma trace_live_weight (p : Public) (hR : 0 < p.R) (hε : 0 < p.ε)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1.phase ≠ .finished →
      (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1.A < targetWeight p := by
  induction n with
  | zero => exact initial_live_weight p hR hε
  | succ n ih => exact update_live_weight _ _ ih

lemma active_scale_lower {p : Public} {f : p.E → ℝ} {xs : p.E} {s : State p}
    (hR : 0 < p.R) (hε : 0 < p.ε) (hi : PointwiseHessianOuter.Invariant f xs s)
    (hA : s.A < targetWeight p) : p.ε / p.R ^ 2 < s.η := by
  unfold targetWeight at hA
  have hh := (lt_div_iff₀ hε).mp hA
  have hm := mul_lt_mul_of_pos_left hh hi.η_pos
  have hq := mul_le_mul_of_nonneg_right hi.scale hε.le
  apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
  nlinarith

lemma accept_eta_le {p : Public} (s : State p) (hη : 0 < s.η)
    (hgap : s.τ = s.η ∨ 2 * s.η ≤ s.τ) : (accept s).η ≤ s.τ := by
  rw [(PointwiseHessianOuter.accept_fields s).2.2.2]
  split_ifs with he
  · rw [he]
    linarith
  · exact hgap.resolve_left he

noncomputable def scaleCeiling (p : Public) : ℝ := max (1 / initialWeight p) (1024 * p.M₀ * p.R)

def BoundedScales {p : Public} (s : State p) : Prop :=
  s.η ≤ scaleCeiling p ∧
    ((s.phase = .newtonHessian ∨ s.phase = .newtonGradient) → s.τ ≤ scaleCeiling p)

lemma initial_boundedScales (p : Public) : BoundedScales (initial p) := by
  constructor
  · exact le_max_left _ _
  · intro hs
    simp only [initial] at hs
    split_ifs at hs <;> simp at hs

lemma startTrial_boundedScales {p : Public} (s : State p) {τ r : ℝ}
    (hη : s.η ≤ scaleCeiling p) (hτ : τ ≤ scaleCeiling p) :
    BoundedScales (startTrial s τ r) := ⟨hη, fun _ => hτ⟩

lemma failedTrial_boundedScales {p : Public} (s : State p)
    (hη : s.η ≤ scaleCeiling p) (hτ : s.τ ≤ scaleCeiling p)
    (hcap : radiusCap p s.τ ≤ s.r → s.τ < 512 * p.M₀ * p.R) :
    BoundedScales (failedTrial s) := by
  unfold failedTrial
  split_ifs with hr
  · exact startTrial_boundedScales s hη hτ
  · apply startTrial_boundedScales s hη
    have hh := hcap (le_of_not_gt hr)
    have hb : 1024 * p.M₀ * p.R ≤ scaleCeiling p := le_max_right _ _
    linarith

lemma accept_boundedScales {p : Public} (s : State p) (hη : 0 < s.η)
    (hgap : s.τ = s.η ∨ 2 * s.η ≤ s.τ) (hτ : s.τ ≤ scaleCeiling p) :
    BoundedScales (accept s) := by
  refine ⟨(accept_eta_le s hη hgap).trans hτ, ?_⟩
  intro hs
  by_cases ht : targetWeight p ≤ s.A + (s.η / s.τ) * s.a
  · simp [accept, finish, ht] at hs
  · simp [accept, ht] at hs

lemma center_boundedScales {p : Public} (s : State p) (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hs : s.phase = .centerGradient) (hi : BoundedScales s) : BoundedScales (update s reply) := by
  simp only [update, hs]
  split_ifs
  · exact ⟨hi.1, by intro h; simp [finish] at h⟩
  · exact startTrial_boundedScales _ hi.1 hi.1

lemma gradient_boundedScales {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hs : s.phase = .newtonGradient)
    (hi : PointwiseHessianExecution.StateInvariant f xs s) (hb : BoundedScales s) :
    BoundedScales (update s reply) := by
  have hp := hi.phase
  simp only [PointwiseHessianExecution.PhaseInvariant, hs] at hp
  have hτ := hb.2 (Or.inr hs)
  simp only [update, hs]
  split_ifs
  · exact ⟨hb.1, by intro h; simp [finish] at h⟩
  · exact ⟨hb.1, fun _ => hτ⟩
  · exact accept_boundedScales _ hi.outer.η_pos hp.1.scale_gap hτ
  · exact ⟨hb.1, fun _ => hτ⟩

lemma hessian_boundedScales {p : Public} {f : p.E → ℝ} (s : State p) (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : IsMinOn f Set.univ xs) (hi : PointwiseHessianExecution.StateInvariant f xs s)
    (hs : s.phase = .newtonHessian) (hb : BoundedScales s) :
    BoundedScales (update s (.inr (fderiv ℝ (gradient f) s.x))) := by
  have hp := hi.phase
  simp only [PointwiseHessianExecution.PhaseInvariant, hs] at hp
  obtain ⟨hp, hn⟩ := hp
  have hτ := hb.2 (Or.inl hs)
  by_cases hg : ‖newtonPoint p s.b s.center s.x s.g (fderiv ℝ (gradient f) s.x) - s.center‖ ≤ 2 * s.r
  · rw [PointwiseHessianExecution.hessian_update_guard s _ hs hg]
    exact ⟨hb.1, fun _ => hτ⟩
  · rw [PointwiseHessianExecution.hessian_update_failure s _ hs hg]
    apply failedTrial_boundedScales s hb.1 hτ
    intro hcap
    have hre : s.r = radiusCap p s.τ := le_antisymm hp.r_le hcap
    have hz := PointwiseHessianOuter.energy_radius s xs hR.le hi.outer.A_pos.le
      (fun x => hmin (Set.mem_univ x)) hi.outer.energy_le
    have hcenter := PointwiseHessianOuter.center_radius s xs hR.le hi.outer.A_pos.le
      hi.outer.η_pos hi.outer.radius hz
    apply PointwiseHessianTrial.failed_cap_bound p hf hc hM₀ hM₁ hR hT hp.τ_pos hp.b_pos hp.b_le
      s.center s.x xs hmin hcenter
    · simpa only [hre] using hn.radius
    · simpa only [hre, hn.gradient_eq] using hn.residual
    · simpa only [hre, hn.gradient_eq] using lt_of_not_ge hg

lemma trace_boundedScales (p : Public) {f : p.E → ℝ} (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : IsMinOn f Set.univ xs) (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    BoundedScales (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1 := by
  induction n with
  | zero => exact initial_boundedScales p
  | succ n ih =>
    have hi := PointwiseHessianExecution.trace_invariant xs hf hc hM₀ hM₁ hR hΔ hε hT
      (fun x => hmin (Set.mem_univ x)) hx hgap O hgrad hHess seed ξ n
    let s := (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1
    change BoundedScales (update s (O.answer _ (query s) _))
    change BoundedScales s at ih
    change PointwiseHessianExecution.StateInvariant f xs s at hi
    cases hs : s.phase with
    | centerGradient => exact center_boundedScales s _ hs ih
    | newtonHessian =>
      rw [show query s = (1, s.x) by simp [query, hs], hHess]
      exact hessian_boundedScales s xs hf hc hM₀ hM₁ hR hT hmin hi hs ih
    | newtonGradient => exact gradient_boundedScales s xs _ hs hi ih
    | finished =>
      rw [PointwiseHessianOuter.finished_output s _ hs]
      exact ih

lemma scaleCeiling_formula (p : Public) (hR : 0 < p.R) (hΔ : 0 < p.Δ) :
    scaleCeiling p = max (2 * p.Δ / p.R ^ 2) (1024 * p.M₀ * p.R) := by
  unfold scaleCeiling initialWeight
  congr 1
  field_simp

lemma update_weight_cap {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E)) (hi : PointwiseHessianExecution.StateInvariant f xs s)
    (hcap : s.A ≤ 3 * targetWeight p)
    (hlive : s.phase ≠ .finished → s.A < targetWeight p) :
    (update s reply).A ≤ 3 * targetWeight p := by
  by_cases h : PointwiseHessianLedger.Accepted s reply
  · have hp := hi.phase
    simp only [PointwiseHessianExecution.PhaseInvariant, h.1] at hp
    have ha := hlive (by simp [h.1])
    have hu := (PointwiseHessianOuter.accepted_weight_bounds s hi.outer.A_pos hi.outer.η_pos
      hp.1.η_le hi.outer.scale).2
    have he := congrArg Prod.fst (PointwiseHessianLedger.accepted_scales s reply h)
    dsimp only at he
    rw [he]
    linarith
  · have he := congrArg Prod.fst (PointwiseHessianLedger.nonaccepted_outer_fields s reply h)
    dsimp only at he
    rwa [he]

lemma trace_weight_cap (p : Public) {f : p.E → ℝ} (xs : p.E)
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε) (hΔ : p.ε < p.Δ)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hmin : IsMinOn f Set.univ xs) (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (O : OracleTemplate.Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2)
    (hgrad : ∀ history x seed, O.answer history (0, x) seed = Sum.inl (gradient f x))
    (hHess : ∀ history x seed, O.answer history (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) :
    (OracleTemplate.executeIndexedState O (algorithm p) seed ξ n).1.A ≤ 3 * targetWeight p := by
  induction n with
  | zero =>
    have hl := initial_live_weight p hR hε (by simp [initial, not_le.mpr hΔ])
    have ht : 0 < targetWeight p := by unfold targetWeight; positivity
    change (initial p).A ≤ 3 * targetWeight p
    linarith
  | succ n ih =>
    have hi := PointwiseHessianExecution.trace_invariant xs hf hc hM₀ hM₁ hR (hε.trans hΔ) hε hT
      (fun x => hmin (Set.mem_univ x)) hx hgap O hgrad hHess seed ξ n
    exact update_weight_cap _ _ hi ih (trace_live_weight p hR hε O seed ξ n)

lemma weight_log_bound (p : Public) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    {A : ℝ} (hA : 0 < A) (hcap : A ≤ 3 * targetWeight p) :
    Real.log A - Real.log (initialWeight p) ≤ Real.log (6 * p.Δ / p.ε) := by
  have hinit := PointwiseHessianTuning.initialWeight_pos p hR hΔ
  rw [← Real.log_div hA.ne' hinit.ne']
  apply Real.log_le_log (div_pos hA hinit)
  calc
    A / initialWeight p ≤ (3 * targetWeight p) / initialWeight p :=
      div_le_div_of_nonneg_right hcap hinit.le
    _ = 6 * p.Δ / p.ε := by unfold targetWeight initialWeight; field_simp; ring

lemma initial_scale_product (p : Public) (hR : 0 < p.R) (hΔ : 0 < p.Δ) :
    (2048 * p.M₀ * p.R + p.ε / p.R ^ 2) * initialWeight p =
      1024 * p.M₀ * p.R ^ 3 / p.Δ + p.ε / (2 * p.Δ) := by
  unfold initialWeight
  field_simp
  ring

end LongTails.Proofs.PointwiseHessianBounds
