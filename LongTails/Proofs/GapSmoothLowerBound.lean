import LongTails.Proofs.GapSmoothInstance
import LongTails.Proofs.GapChainLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set OracleTemplate MeasureTheory

namespace LongTails.Proofs.GapSmoothLowerBound

open LongTails.Setups.GapGeneralizedSmoothConvex GapSmoothInstance
open FiniteSumNondualLowerComponents

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m)

noncomputable def embedded (π : Fin m ↪ Fin p.d) := GapLocalizedChain.liftSeed (seed p hp m hm) π
noncomputable def objective (π : Fin m ↪ Fin p.d) : EuclideanSpace ℝ (Fin p.d) → ℝ :=
  AdaptivePolynomialLocalization.value (embedded p hp m hm π).f 2 (coefficient p m) p.R (coefficient p m * p.R ^ 2)
noncomputable def field (π : Fin m ↪ Fin p.d) : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  AdaptivePolynomialLocalization.field (embedded p hp m hm π).f (embedded p hp m hm π).g 2
    (coefficient p m) p.R (coefficient p m * p.R ^ 2)

variable (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2)
include hp hm

lemma radius_width (π : Fin m ↪ Fin p.d) : 2 * (embedded p hp m hm π).r ≤ p.R := by
  have hh := seed_radius p hp m hm
  have hR := hp.2.2.1
  change 2 * (seed p hp m hm).r ≤ p.R
  linarith

include hbound in
lemma admissible (π : Fin m ↪ Fin p.d) : spec.admissible p
    (fun x : EuclideanSpace ℝ (Fin p.d) => objective p hp m hm π (x - p.x0))
    (SmoothConvexFiniteLowerBound.oracle p.x0 (field p hp m hm π)) := by
  apply GapLocalizedChain.admissible p (embedded p hp m hm π) 2 (by norm_num) (coefficient p m) p.R
    (coefficient_pos p hp m hm) hp.2.2.1
  · have hh := radius_width p hp m hm π
    have hr := (embedded p hp m hm π).r_pos
    linarith
  · have hh := radius_width p hp m hm π
    have hr := (embedded p hp m hm π).r_pos
    linarith
  · change (seed p hp m hm).f (coordinateMap π 0) ≤ p.Δ
    rw [map_zero]
    exact seed_origin_gap p hp m hm
  · intro x
    exact (localized_curvature p hp m hm hbound π x).trans
      (le_add_of_nonneg_right (mul_nonneg hp.2.1 (norm_nonneg _)))

lemma objective_nonnegative (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ objective p hp m hm π x :=
  ((embedded p hp m hm π).nonnegative x).trans
    (AdaptivePolynomialLocalization.value_above _ 2 (by norm_num) _ _ _
      (by have := coefficient_pos p hp m hm; have := hp.2.2.1; positivity) x)

lemma objective_zero (π : Fin m ↪ Fin p.d) : objective p hp m hm π (embedded p hp m hm π).z = 0 := by
  let s := embedded p hp m hm π
  have hr : s.r ≤ p.R := by
    have hh := radius_width p hp m hm π
    have hn := s.r_pos
    change 2 * s.r ≤ p.R at hh
    linarith
  exact (AdaptiveGeneralizedSmoothLocalization.value_interior s 2 (coefficient p m) p.R
    (coefficient_pos p hp m hm) hp.2.2.1 s.z (s.radius.trans hr)).trans s.zero

include hbound in
lemma objective_near (π : Fin m ↪ Fin p.d) (i : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π i)| ≤ threshold p m) : 3 * p.ε ≤ objective p hp m hm π x := by
  have hh := seed_hidden_gap p hp m hm hbound (coordinateMap π x) i (abs_le.mp hx).1
  exact hh.trans (AdaptivePolynomialLocalization.value_above (embedded p hp m hm π).f 2 (by norm_num)
    (coefficient p m) p.R (coefficient p m * p.R ^ 2)
    (by have := coefficient_pos p hp m hm; have := hp.2.2.1; positivity) x)

lemma objective_far (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : 4 * p.R ≤ ‖x‖) : 3 * p.ε ≤ objective p hp m hm π x := by
  have ha := coefficient_pos p hp m hm
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  have hL : 0 < curvature p := by have := hp.1; unfold curvature; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
  have ht := coefficient_tuning p hp m
  have hG : GapBoundedSmoothParameters.slope m p.R p.ε * p.R = 320 * p.ε * Real.sqrt m := by
    unfold GapBoundedSmoothParameters.slope
    field_simp
  have ht' := congrArg (fun z => z * p.R) ht
  have hsize : 320 * p.ε ≤ coefficient p m * p.R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 320 * p.ε by positivity)
    have hn : 0 ≤ curvature p * p.R ^ 2 := by positivity
    nlinarith only [ht', hG, hh, hn]
  have hnorm := pow_le_pow_left₀ (show 0 ≤ 4 * p.R by positivity) hx 2
  have hnorm' := mul_le_mul_of_nonneg_left hnorm ha.le
  have hw := AdaptivePolynomialLocalization.value_above_wall (embedded p hp m hm π).f 2 (by norm_num)
    (coefficient p m) p.R (coefficient p m * p.R ^ 2) (by positivity) x
  change AdaptivePolynomialLocalization.wall (coefficient p m) p.R x - coefficient p m * p.R ^ 2 ≤
    objective p hp m hm π x at hw
  unfold AdaptivePolynomialLocalization.wall at hw
  nlinarith only [hsize, hnorm', hw, hε]

lemma field_exterior (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : 4 * p.R ≤ ‖x‖) : field p hp m hm π x = coefficient p m • x := by
  apply AdaptiveGeneralizedSmoothLocalization.field_exterior (embedded p hp m hm π) 2
    (coefficient p m) p.R (coefficient_pos p hp m hm) hp.2.2.1 (radius_width p hp m hm π) _ x hx
  change GapBoundedSmoothParameters.slope m p.R p.ε ≤ coefficient p m * p.R
  rw [coefficient_tuning p hp m]
  have hh : 0 ≤ curvature p * p.R := by have := hp.1; have := hp.2.2.1; unfold curvature; positivity
  linarith

noncomputable def partialReply (π : Fin m ↪ Fin p.d) (r : ℕ) :
    EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  GapLocalizedChain.partialField (seed p hp m hm).f (seed p hp m hm).g 2 (coefficient p m) p.R π r

lemma partial_prefix (π ρ : Fin m ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) : partialReply p hp m hm π r x = partialReply p hp m hm ρ r x :=
  GapLocalizedChain.partialField_prefix _ _ _ _ _ π ρ r x h

include hbound in
lemma partial_exact (π : Fin m ↪ Fin p.d) (r : Fin m) (x : EuclideanSpace ℝ (Fin p.d))
    (hx : ‖x‖ < 4 * p.R → ∀ i, r ≤ i → |x (π i)| ≤ threshold p m) :
    partialReply p hp m hm π r.val x = field p hp m hm π x := by
  apply GapLocalizedChain.partialField_eq _ _ _ _ _ (threshold p m) π r x
    (fun y hy => (seed_truncated p hp m hm hbound r y hy).1)
    (fun y hy => (seed_truncated p hp m hm hbound r y hy).2)
  · exact field_exterior p hp m hm π x
  · exact hx

omit m hm in
lemma exists_failure (N : ℕ) (hN : 65536 * (N + 1 : ℕ) ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε))
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hm : 0 < N + 1 := by omega
  have hε := hp.2.2.2.1
  have h0 := hp.1
  have hR := hp.2.2.1
  have hms : (N + 1 : ℕ) ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := by
    have hh : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
    nlinarith only [hN, hh]
  have hbound : 819200000 * (N + 1 : ℕ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2 := by
    have hs := pow_le_pow_left₀ (show 0 ≤ 65536 * ((N + 1 : ℕ) : ℝ) by positivity) hN 2
    rw [Real.sq_sqrt (by positivity : 0 ≤ p.L0 * p.R ^ 2 / p.ε)] at hs
    have hh := (le_div_iff₀ hε).mp hs
    nlinarith [mul_nonneg (sq_nonneg ((N + 1 : ℕ) : ℝ)) hε.le]
  apply GapChainLowerBound.exists_failure p hε N (4 * p.R) (threshold p (N + 1))
    (by positivity) (threshold_pos p hp (N + 1) hm)
    (GapBoundedSmoothParameters.hiding_dimension p hp hm hms)
    (objective p hp (N + 1) hm) (field p hp (N + 1) hm) (partialReply p hp (N + 1) hm)
    (fun π => (embedded p hp (N + 1) hm π).z)
    (admissible p hp (N + 1) hm hbound) (partial_prefix p hp (N + 1) hm)
    (fun π r x hr hs => partial_exact p hp (N + 1) hm hbound π ⟨r, by omega⟩ x hs)
    (objective_nonnegative p hp (N + 1) hm) (objective_zero p hp (N + 1) hm)
    (fun π x hx => objective_near p hp (N + 1) hm hbound π (Fin.last N) x hx)
    (objective_far p hp (N + 1) hm) A

end LongTails.Proofs.GapSmoothLowerBound
