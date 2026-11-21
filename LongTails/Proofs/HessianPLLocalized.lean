import LongTails.Proofs.HessianPLChain

namespace LongTails.Proofs.HessianPLLocalized

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGeometry RelativeHessianLocalized
open HessianPLWell HessianPLChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma inside_value {m : ℕ} (v : Fin (m + 1) → E) (x : E) (hx : ‖x‖ ≤ radius m) :
    value v x = RelativeHessianGuard.value v x := by
  have hc := (RelativeHessianCutoffSpatial.inside_jets (radius_pos m) x hx).1
  unfold value perturbation RelativeHessianGuard.value
  rw [hc, one_mul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma value_bounds {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    coefficient / 2 * ‖x‖ ^ 2 - 4 * (m + 1 : ℕ) ≤ value v x ∧
      value v x ≤ coefficient / 2 * ‖x‖ ^ 2 + 4 * (m + 1 : ℕ) := by
  have hc := RelativeHessianChainBounds.value_bound v x
  have hχ := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius m) x)
  change 0 ≤ RelativeHessianCutoffSpatial.value (radius m) x ∧
    RelativeHessianCutoffSpatial.value (radius m) x ≤ 1 at hχ
  have hprod : |perturbation v x| ≤ 4 * (m + 1 : ℕ) := by
    unfold perturbation
    rw [abs_mul, abs_of_nonneg hχ.1]
    exact (mul_le_mul hχ.2 hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have h := abs_le.mp hprod
  unfold value FullGeneralizedSmoothZeroQuery.quadratic
  rw [sub_zero]
  constructor <;> linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma radius_sq_lower (m : ℕ) {x : E} (hx : radius m ≤ ‖x‖) :
    2 ^ 60 * ((m + 1 : ℕ) : ℝ) ≤ ‖x‖ ^ 2 := by
  have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  unfold radius at hx
  have h1 : (1 : ℝ) ≤ ‖x‖ := by nlinarith
  nlinarith

lemma value_lower {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    (m + 1 : ℕ) * bottom ≤ value v x := by
  have ha := coefficient_bounds
  have hb := bottom_bounds
  by_cases hx : ‖x‖ ≤ radius m
  · rw [inside_value v x hx]
    have h := value_decomposition v x
    have h1 := rest_nonneg hv x
    have h2 : 0 ≤ well ⟪v 0, x⟫ - bottom := sub_nonneg.mpr (bottom_le_well _)
    have h3 : 0 ≤ ∑ i : Fin m, (coefficient / 2 * ⟪v i.succ, x⟫ ^ 2 +
        RelativeHessianChain.link ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ - bottom) :=
      Finset.sum_nonneg (fun i _ => by
        linarith [link_bracket ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫])
    have h4 : 0 ≤ coefficient / 2 * rest v x := mul_nonneg (by linarith) h1
    linarith
  · push Not at hx
    have hl := (value_bounds v x).1
    have hr := radius_sq_lower m hx.le
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    have hNb : ((m + 1 : ℕ) : ℝ) * bottom ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hq : 1 / 2 * ‖x‖ ^ 2 ≤ coefficient / 2 * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖x‖]
    nlinarith

noncomputable def minimizer {m : ℕ} (v : Fin (m + 1) → E) : E := ∑ j, balance • v j

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma minimizer_inner {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (j : Fin (m + 1)) :
    ⟪v j, minimizer v⟫ = balance := by
  unfold minimizer
  rw [hv.inner_right_fintype]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma minimizer_norm_sq {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) :
    ‖minimizer v‖ ^ 2 = (m + 1 : ℕ) * balance ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold minimizer
  rw [hv.inner_sum]
  simp only [conj_trivial, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma balance_large : 1 / 5 ≤ balance := by
  obtain ⟨_, hb0, _, hb, _⟩ := balance_parameters
  nlinarith

lemma value_minimizer {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) :
    value v (minimizer v) = (m + 1 : ℕ) * bottom := by
  have hn := minimizer_norm_sq hv
  obtain ⟨_, hb0, hb1, hb, _⟩ := balance_parameters
  have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  have hin : ‖minimizer v‖ ≤ radius m := by
    by_contra h
    push Not at h
    have hr := radius_pos m
    have h2 := mul_lt_mul'' h h hr.le hr.le
    unfold radius at h2 hr
    nlinarith
  have hdec := value_decomposition v (minimizer v)
  have hrest : rest v (minimizer v) = 0 := by
    unfold rest
    simp only [minimizer_inner hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [hn]
    ring
  simp only [minimizer_inner hv] at hdec
  rw [hrest, link_saturated balance_large] at hdec
  have hz : coefficient / 2 * balance ^ 2 + -profile balance - bottom = 0 := by
    unfold bottom well
    ring
  have hw : well balance - bottom = 0 := by
    unfold bottom
    ring
  simp only [hz, hw, Finset.sum_const_zero, mul_zero, add_zero] at hdec
  rw [inside_value v _ hin]
  linarith

lemma minimizer_isMin {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) :
    IsMinOn (value v) Set.univ (minimizer v) := by
  intro x _
  change value v (minimizer v) ≤ value v x
  rw [value_minimizer hv]
  exact value_lower hv x

theorem value_pl {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    value v x - (m + 1 : ℕ) * bottom ≤ 2 ^ 9 * (m + 1 : ℕ) * ‖gradient (value v) x‖ ^ 2 := by
  by_cases hx : ‖x‖ ≤ radius m
  · rw [inside_value v x hx, inside_gradient v x hx]
    exact guard_pl hv x
  · push Not at hx
    have hg := outside_gradient hv x hx.le
    have hu := (value_bounds v x).2
    have hr := radius_sq_lower m hx.le
    have ha := coefficient_bounds
    have hb := bottom_bounds
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    have hq : coefficient / 2 * ‖x‖ ^ 2 ≤ 13 / 20 * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖x‖]
    have hg2 : ‖x‖ ^ 2 ≤ 4 * ‖gradient (value v) x‖ ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg (gradient (value v) x)]
    have hNb : -(((m + 1 : ℕ) : ℝ) * bottom) ≤ 4 * (m + 1 : ℕ) := by nlinarith
    have hQ : 0 ≤ ‖gradient (value v) x‖ ^ 2 := sq_nonneg _
    have hNQ : ‖gradient (value v) x‖ ^ 2 ≤
        ((m + 1 : ℕ) : ℝ) * ‖gradient (value v) x‖ ^ 2 := by nlinarith
    nlinarith

lemma value_unfinished {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) (r : ℕ)
    (hsmall : ‖x‖ ≤ radius m → ∀ j : Fin (m + 1), r ≤ j.val → |⟪v j, x⟫| ≤ 1 / 10) :
    (m : ℝ) - r ≤ value v x - (m + 1 : ℕ) * bottom := by
  by_cases hx : ‖x‖ ≤ radius m
  · rw [inside_value v x hx]
    exact guard_unfinished hv x r (hsmall hx)
  · push Not at hx
    have hl := (value_bounds v x).1
    have hr := radius_sq_lower m hx.le
    have ha := coefficient_bounds
    have hb := bottom_bounds
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    have hq : 1 / 2 * ‖x‖ ^ 2 ≤ coefficient / 2 * ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖x‖]
    have hNb : ((m + 1 : ℕ) : ℝ) ≤ -(((m + 1 : ℕ) : ℝ) * bottom) := by nlinarith
    have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hNm : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    linarith

end LongTails.Proofs.HessianPLLocalized
