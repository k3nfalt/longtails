import LongTails.Proofs.GapTransientChain
import LongTails.Proofs.GapChainLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set OracleTemplate MeasureTheory

namespace LongTails.Proofs.GapTransientLowerBound

open LongTails.Setups.GapGeneralizedSmoothConvex GapTransientParameters
open FiniteSumNondualLowerComponents

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) (hq : 1 ≤ scale p)
  (hmq : (m : ℝ) ≤ scale p)

noncomputable def source := GapTransientChain.seed p hp m hm hq hmq
noncomputable def embedded (π : Fin m ↪ Fin p.d) := GapLocalizedChain.liftSeed (source p hp m hm hq hmq) π

noncomputable def objective (π : Fin m ↪ Fin p.d) : EuclideanSpace ℝ (Fin p.d) → ℝ :=
  AdaptivePolynomialLocalization.value (embedded p hp m hm hq hmq π).f (degree p)
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)

noncomputable def field (π : Fin m ↪ Fin p.d) : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  AdaptivePolynomialLocalization.field (embedded p hp m hm hq hmq π).f (embedded p hp m hm hq hmq π).g
    (degree p) (coefficient p m) (width p) (coefficient p m * width p ^ 2)

variable (hlinear : 16384 * (m : ℝ) * logarithm p ≤ scale p)
  (hgap : 32768 * (m : ℝ) * Real.sqrt m * logarithm p ≤ scale p * gapLog p)

include hp hm hq hmq hlinear hgap

lemma radius_bound (π : Fin m ↪ Fin p.d) : (embedded p hp m hm hq hmq π).r ≤ p.R / 32 :=
  GapTransientChain.seed_radius p hp m hm hq hmq hlinear hgap

omit hlinear hgap hmq in
lemma coefficient_pos : 0 < coefficient p m := by
  have hG := peak_pos p hp hm hq
  have hB := width_pos p hp
  have h0 := hp.1
  unfold coefficient
  positivity

lemma radius_width (π : Fin m ↪ Fin p.d) : 2 * (embedded p hp m hm hq hmq π).r ≤ width p := by
  have hh := radius_bound p hp m hm hq hmq hlinear hgap π
  have hR := hp.2.2.1
  unfold width
  linarith

lemma field_curvature (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    ‖fderiv ℝ (field p hp m hm hq hmq π) x‖ ≤ p.L0 + p.L1 * ‖field p hp m hm hq hmq π x‖ := by
  let s := embedded p hp m hm hq hmq π
  have hwidth : 256 * ((degree p : ℝ) * (degree p + 1 : ℕ)) ≤ s.L₁ * width p := by
    change _ ≤ (4 * (p.L1 / 4)) * width p
    simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using width_valid p hq
  have htuning : coefficient p m * width p = s.G + s.L₀ * width p / 1000 := by
    change coefficient p m * width p = peak p m + (4 * (p.L0 / 4)) * width p / 1000
    simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using coefficient_tuning p hp m
  have hsupp : s.G * (1 / 2 : ℝ) ^ degree p * s.L₁ ≤ s.L₀ := by
    change peak p m * (1 / 2 : ℝ) ^ degree p * (4 * (p.L1 / 4)) ≤ 4 * (p.L0 / 4)
    simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using peak_suppression p hp hm hq hmq
  have hh := AdaptiveGeneralizedSmoothLocalization.gradient_curvature s (degree p) (degree_valid p hq)
    (coefficient p m) (width p) (coefficient_pos p hp m hm hq) (width_pos p hp)
    (radius_width p hp m hm hq hmq hlinear hgap π) hwidth htuning hsupp x
  change ‖fderiv ℝ (field p hp m hm hq hmq π) x‖ ≤
    (4 * (p.L0 / 4)) + (4 * (p.L1 / 4)) * ‖field p hp m hm hq hmq π x‖ at hh
  convert hh using 1; ring

lemma admissible (π : Fin m ↪ Fin p.d) : spec.admissible p
    (fun x : EuclideanSpace ℝ (Fin p.d) => objective p hp m hm hq hmq π (x - p.x0))
    (SmoothConvexFiniteLowerBound.oracle p.x0 (field p hp m hm hq hmq π)) := by
  apply GapLocalizedChain.admissible p (embedded p hp m hm hq hmq π) (degree p) (degree_valid p hq)
    (coefficient p m) (width p) (coefficient_pos p hp m hm hq) (width_pos p hp)
  · have hh := radius_width p hp m hm hq hmq hlinear hgap π
    have hr := (embedded p hp m hm hq hmq π).r_pos
    linarith
  · have hh := radius_bound p hp m hm hq hmq hlinear hgap π
    have hR := hp.2.2.1
    linarith
  · change (source p hp m hm hq hmq).f (coordinateMap π 0) ≤ p.Δ
    rw [map_zero]
    exact GapTransientChain.seed_origin_gap p hp m hm hq hmq
  · exact field_curvature p hp m hm hq hmq hlinear hgap π

omit hlinear hgap in
lemma objective_nonnegative (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ objective p hp m hm hq hmq π x :=
  ((embedded p hp m hm hq hmq π).nonnegative x).trans
    (AdaptivePolynomialLocalization.value_above _ (degree p) (degree_valid p hq) _ _ _
      (by have := coefficient_pos p hp m hm hq; have := width_pos p hp; positivity) x)

lemma objective_zero (π : Fin m ↪ Fin p.d) :
    objective p hp m hm hq hmq π (embedded p hp m hm hq hmq π).z = 0 := by
  let s := embedded p hp m hm hq hmq π
  have hr : s.r ≤ width p := by
    have hh := radius_width p hp m hm hq hmq hlinear hgap π
    have hn := s.r_pos
    change 2 * s.r ≤ width p at hh
    linarith
  exact (AdaptiveGeneralizedSmoothLocalization.value_interior s (degree p) (coefficient p m) (width p)
    (coefficient_pos p hp m hm hq) (width_pos p hp) s.z (s.radius.trans hr)).trans s.zero

omit hlinear hgap in
lemma objective_near (π : Fin m ↪ Fin p.d) (i : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π i)| ≤ threshold p m) : 3 * p.ε ≤ objective p hp m hm hq hmq π x := by
  have hh := GapTransientChain.seed_hidden_gap p hp m hm hq hmq (coordinateMap π x) i (abs_le.mp hx).1
  have ha := AdaptivePolynomialLocalization.value_above (embedded p hp m hm hq hmq π).f
    (degree p) (degree_valid p hq) (coefficient p m) (width p) (coefficient p m * width p ^ 2)
    (by have := coefficient_pos p hp m hm hq; have := width_pos p hp; positivity) x
  change (source p hp m hm hq hmq).f (coordinateMap π x) ≤ objective p hp m hm hq hmq π x at ha
  have hε := hp.2.2.2.1
  dsimp only [source] at ha
  linarith

omit hlinear hgap in
lemma objective_far (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : 4 * width p ≤ ‖x‖) : 3 * p.ε ≤ objective p hp m hm hq hmq π x := by
  have ha := coefficient_pos p hp m hm hq
  have hB := width_pos p hp
  have hnorm := pow_le_pow_left₀ (show 0 ≤ 4 * width p by positivity) hx 2
  have hw := AdaptivePolynomialLocalization.value_above_wall (embedded p hp m hm hq hmq π).f
    (degree p) (degree_valid p hq) (coefficient p m) (width p) (coefficient p m * width p ^ 2)
    (by positivity) x
  have hcoef : p.L0 / 1000 ≤ coefficient p m := by
    have hG := peak_pos p hp hm hq
    exact le_add_of_nonneg_left (div_nonneg hG.le hB.le)
  have hm' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (width p))
  have hnorm' := mul_le_mul_of_nonneg_left hnorm ha.le
  have he := hp.2.2.2.2.1
  have hε := hp.2.2.2.1
  change AdaptivePolynomialLocalization.wall (coefficient p m) (width p) x - coefficient p m * width p ^ 2 ≤
    objective p hp m hm hq hmq π x at hw
  unfold AdaptivePolynomialLocalization.wall at hw
  unfold width at hm' hnorm' hw
  nlinarith only [hm', hnorm', hw, he, hε]

lemma field_exterior (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : 4 * width p ≤ ‖x‖) : field p hp m hm hq hmq π x = coefficient p m • x := by
  apply AdaptiveGeneralizedSmoothLocalization.field_exterior (embedded p hp m hm hq hmq π)
    (degree p) (coefficient p m) (width p) (coefficient_pos p hp m hm hq) (width_pos p hp)
    (radius_width p hp m hm hq hmq hlinear hgap π) _ x hx
  change peak p m ≤ coefficient p m * width p
  rw [coefficient_tuning p hp m]
  have hh : 0 ≤ p.L0 * width p / 1000 := by have := hp.1; have := width_pos p hp; positivity
  linarith

noncomputable def partialReply (π : Fin m ↪ Fin p.d) (r : ℕ) :
    EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  GapLocalizedChain.partialField (source p hp m hm hq hmq).f (source p hp m hm hq hmq).g
    (degree p) (coefficient p m) (width p) π r

omit hlinear hgap in
lemma partial_prefix (π ρ : Fin m ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) :
    partialReply p hp m hm hq hmq π r x = partialReply p hp m hm hq hmq ρ r x :=
  GapLocalizedChain.partialField_prefix _ _ _ _ _ π ρ r x h

lemma partial_exact (π : Fin m ↪ Fin p.d) (r : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : ‖x‖ < 4 * width p → ∀ i, r ≤ i → |x (π i)| ≤ threshold p m) :
    partialReply p hp m hm hq hmq π r.val x = field p hp m hm hq hmq π x := by
  apply GapLocalizedChain.partialField_eq _ _ _ _ _ (threshold p m) π r x
    (fun y hy => (GapTransientChain.seed_truncated p hp m hm hq hmq r y hy).1)
    (fun y hy => (GapTransientChain.seed_truncated p hp m hm hq hmq r y hy).2)
  · exact field_exterior p hp m hm hq hmq hlinear hgap π x
  · exact hx

omit m hm hq hmq hlinear hgap in
lemma exists_failure (N : ℕ)
    (hmq : (N + 1 : ℕ) ≤ scale p)
    (hlinear : 16384 * (N + 1 : ℕ) * logarithm p ≤ scale p)
    (hgap : 32768 * (N + 1 : ℕ) * Real.sqrt (N + 1 : ℕ) * logarithm p ≤ scale p * gapLog p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hm : 0 < N + 1 := by omega
  have hq : 1 ≤ scale p := by
    have hh : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hm
    exact hh.trans hmq
  have hB := width_pos p hp
  apply GapChainLowerBound.exists_failure p hp.2.2.2.1 N (4 * width p) (threshold p (N + 1))
    (by positivity) (threshold_pos p hp hm hq) (hiding_dimension p hp hm hq hmq)
    (objective p hp (N + 1) hm hq hmq) (field p hp (N + 1) hm hq hmq)
    (partialReply p hp (N + 1) hm hq hmq)
    (fun π => (embedded p hp (N + 1) hm hq hmq π).z)
    (admissible p hp (N + 1) hm hq hmq hlinear hgap)
    (partial_prefix p hp (N + 1) hm hq hmq)
    (fun π r x hr hs => partial_exact p hp (N + 1) hm hq hmq hlinear hgap π ⟨r, by omega⟩ x hs)
    (objective_nonnegative p hp (N + 1) hm hq hmq)
    (objective_zero p hp (N + 1) hm hq hmq hlinear hgap)
    (fun π x hx => objective_near p hp (N + 1) hm hq hmq π (Fin.last N) x hx)
    (objective_far p hp (N + 1) hm hq hmq) A

end LongTails.Proofs.GapTransientLowerBound
