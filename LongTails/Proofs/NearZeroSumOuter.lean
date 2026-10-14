import LongTails.Proofs.NearZeroSumProjection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open ConstrainedMonotone (Proj Normal)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_monotone {C : Set E} {A : E → E} {m β : ℝ}
    (hmono : ∀ u ∈ C, ∀ v ∈ C, m * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (center : E) {u v : E} (hu : u ∈ C) (hv : v ∈ C) :
    (m + β) * ‖u - v‖ ^ 2 ≤
      ⟪(A u + β • (u - center)) - (A v + β • (v - center)), u - v⟫ := by
  have he : (A u + β • (u - center)) - (A v + β • (v - center)) =
      (A u - A v) + β • (u - v) := by module
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith [hmono u hu v hv]

lemma regularized_lipschitz {C : Set E} {A : E → E} {L β : ℝ} (hβ : 0 ≤ β)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ L * ‖u - v‖)
    (center : E) {u v : E} (hu : u ∈ C) (hv : v ∈ C) :
    ‖(A u + β • (u - center)) - (A v + β • (v - center))‖ ≤ (L + β) * ‖u - v‖ := by
  have he : (A u + β • (u - center)) - (A v + β • (v - center)) =
      (A u - A v) + β • (u - v) := by module
  rw [he]
  have h := norm_add_le (A u - A v) (β • (u - v))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ] at h
  nlinarith [hlip u hu v hv]

lemma regularized_vi_exists {C : Set E} {P A : E → E} {m L β : ℝ}
    (hC : IsComplete C) (hne : C.Nonempty) (hP : Proj C P)
    (hm : 0 < m) (hL : m ≤ L) (hβ : 0 ≤ β)
    (hmono : ∀ u ∈ C, ∀ v ∈ C, m * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ L * ‖u - v‖) (center : E) :
    ∃ s ∈ C, Normal C s (-(A s + β • (s - center))) :=
  strongly_monotone_vi_exists hC hne hP (by linarith : 0 < m + β)
    (by linarith : m + β ≤ L + β)
    (fun u hu v hv => regularized_monotone hmono center hu hv)
    (fun u hu v hv => regularized_lipschitz hβ hlip center hu hv)

lemma resolvent_distance {C : Set E} {A : E → E} {m β : ℝ} {u s center : E}
    (hm : 0 < m) (hβ : 0 ≤ β) (hu : u ∈ C) (hs : s ∈ C)
    (hmono : m * ‖u - s‖ ^ 2 ≤ ⟪A u - A s, u - s⟫)
    (hn : Normal C u (-(A u + β • (u - center)))) (hnstar : Normal C s (-A s)) :
    ‖u - s‖ ≤ β / (m + β) * ‖center - s‖ := by
  have hnorm := ConstrainedMonotone.normal_monotone hu hs hn hnstar
  have he : ⟪-(A u + β • (u - center)) - -A s, u - s⟫ =
      -⟪A u - A s, u - s⟫ - β * ‖u - s‖ ^ 2 + β * ⟪center - s, u - s⟫ := by
    have hd : u - center = (u - s) - (center - s) := by module
    rw [hd]
    simp only [inner_sub_left, inner_neg_left, inner_add_left,
      real_inner_smul_left]
    have hh : ⟪u, u - s⟫ - ⟪s, u - s⟫ = ‖u - s‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    nlinarith [congrArg (fun t : ℝ => β * t) hh]
  rw [he] at hnorm
  have hc := mul_le_mul_of_nonneg_left (real_inner_le_norm (center - s) (u - s)) hβ
  have h := norm_nonneg (u - s)
  have hd : 0 < m + β := by linarith
  by_cases hz : ‖u - s‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖u - s‖ := lt_of_le_of_ne h (Ne.symm hz)
    have hmul : (m + β) * ‖u - s‖ ≤ β * ‖center - s‖ := by nlinarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hd).mpr (by nlinarith)

lemma approximate_resolvent_distance {C : Set E} {A : E → E} {m β e : ℝ} {u s center out : E}
    (hm : 0 < m) (hβ : 0 ≤ β) (hu : u ∈ C) (hs : s ∈ C)
    (hmono : m * ‖u - s‖ ^ 2 ≤ ⟪A u - A s, u - s⟫)
    (hn : Normal C u (-(A u + β • (u - center)))) (hnstar : Normal C s (-A s))
    (herr : ‖out - u‖ ≤ e) :
    ‖out - s‖ ≤ β / (m + β) * ‖center - s‖ + e := by
  have h := norm_sub_le_norm_sub_add_norm_sub out u s
  have hr := resolvent_distance hm hβ hu hs hmono hn hnstar
  linarith

omit [InnerProductSpace ℝ E] in
lemma inexact_contraction_iterates {step : E → E} {C : Set E} {s u0 : E} {q e D : ℝ}
    (hq : 0 ≤ q) (hq₁ : q < 1) (he : 0 ≤ e) (hu0 : u0 ∈ C) (hinit : ‖u0 - s‖ ≤ D)
    (hstep : ∀ u ∈ C, step u ∈ C ∧ ‖step u - s‖ ≤ q * ‖u - s‖ + e) (n : ℕ) :
    step^[n] u0 ∈ C ∧ ‖step^[n] u0 - s‖ ≤ q ^ n * D + e / (1 - q) := by
  induction n with
  | zero =>
      refine ⟨hu0, ?_⟩
      simp only [Function.iterate_zero_apply, pow_zero, one_mul]
      have hh : 0 ≤ e / (1 - q) := div_nonneg he (by linarith)
      linarith
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hm, hd⟩ := hstep _ ih.1
      refine ⟨hm, ?_⟩
      have hh := mul_le_mul_of_nonneg_left ih.2 hq
      have hne : 1 - q ≠ 0 := by linarith
      have heq : q * (e / (1 - q)) + e = e / (1 - q) := by field_simp; ring
      rw [pow_succ]
      nlinarith

end OracleTemplate.NearZeroSum
