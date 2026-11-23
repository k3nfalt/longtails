import LongTails.Proofs.ComponentHessianGap
import LongTails.Proofs.RelativeHessianScaling
import LongTails.Setups.ConvexFiniteSumMeanSquareHessian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.ComponentHessianInstance

open OracleTemplate LongTails.Setups.ConvexFiniteSumMeanSquareHessian
open ComponentHessianFamily ComponentHessianGap RelativeHessianOracle

variable {p : Params} {k : ℕ}

noncomputable def minimizer (π : Fin (k + 1) ↪ Fin p.d) (o : Fin (k + 1) → Fin p.n)
    (hn : 0 < p.n) := Classical.choose (mean_exists_minimum π o hn)

noncomputable def problem (π : Fin (k + 1) ↪ Fin p.d) (o : Fin (k + 1) → Fin p.n)
    (hn : 0 < p.n) (c β : ℝ) : Instance p where
  f i x := c * part π (owned o i) p.n (β • x)
  xstar := β⁻¹ • minimizer (p := p) π o hn

noncomputable def exactOracle (I : Instance p) : Oracle (Fin p.n × Point p)
    (LongTails.Setups.ConvexFiniteSumMeanSquareHessian.Reply p) where
  answer _ q _ := jet (I.f q.2.1) q.2.2

lemma objective_eq (π : Fin (k + 1) ↪ Fin p.d) (o : Fin (k + 1) → Fin p.n)
    (hn : 0 < p.n) (c β : ℝ) (x : Point p) :
    objective (problem (p := p) π o hn c β) x = c * mean π o (β • x) := by
  unfold objective problem mean
  rw [← Finset.mul_sum]
  ring

lemma problem_admissible (π : Fin (k + 1) ↪ Fin p.d) (o : Fin (k + 1) → Fin p.n)
    (hn : 0 < p.n) {c β : ℝ} (hc : 0 ≤ c) (hβ : 0 < β) (hR : ‖anchorPoint π‖ ≤ β * p.R)
    (hH : 2^56 * (c * β^3)^2 ≤ p.n * p.H^2) :
    spec.admissible p (problem (p := p) π o hn c β) (exactOracle (problem (p := p) π o hn c β)) := by
  have hm := Classical.choose_spec (mean_exists_minimum π o hn)
  change ‖minimizer (p := p) π o hn‖ ≤ _ ∧ _ at hm
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ _ _ _ => rfl⟩
  · intro i
    apply ContDiff.of_le (n := 3) _ (by norm_num)
    exact contDiff_const.mul ((part_smooth π (owned o i) p.n).comp (by fun_prop))
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [objective_eq (p := p) π o hn c β, smul_add, smul_comm β a, smul_comm β b, smul_eq_mul]
    have h (i : Fin p.n) := (part_convex π (owned o i) hn).2
      (Set.mem_univ (β • x)) (Set.mem_univ (β • y)) ha hb hab
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    simp only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have he := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (Nat.cast_nonneg p.n)) hc
    unfold mean
    convert he using 1
    ring
  · intro x y
    have hh := family_squared_bound π o hn (β • x) (β • y)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hβ.le] at hh
    let H := fun (i : Fin p.n) (z : Point p) => fderiv ℝ (gradient (part π (owned o i) p.n)) (β • z)
    have he (i : Fin p.n) : ‖fderiv ℝ (gradient ((problem (p := p) π o hn c β).f i)) x -
        fderiv ℝ (gradient ((problem (p := p) π o hn c β).f i)) y‖^2 ≤
        (c * β^2)^2 * ‖H i x - H i y‖^2 := by
      unfold problem
      rw [ThirdOrderAffineCalculus.scale_hessian (part_smooth _ _ _),
        ThirdOrderAffineCalculus.scale_hessian (part_smooth _ _ _)]
      have hs : (c * β^2) • H i x - (c * β^2) • H i y = (c * β^2) • (H i x - H i y) := by
        ext u
        simp only [sub_apply, smul_apply, smul_sub]
      change ‖(c * β^2) • H i x - (c * β^2) • H i y‖^2 ≤ _
      rw [hs]
      have h := ThirdOrderAffineCalculus.norm_smul_operator_le (c * β^2) (H i x - H i y)
      rw [abs_of_nonneg (mul_nonneg hc (sq_nonneg β))] at h
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
    refine (Finset.sum_le_sum (fun i _ => he i)).trans ?_
    rw [← Finset.mul_sum]
    calc
      _ ≤ (c*β^2)^2 * (2^56 * (β * ‖x-y‖)^2) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = (2^56 * (c*β^3)^2) * ‖x-y‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  · change ‖β⁻¹ • minimizer (p := p) π o hn‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hβ.le), inv_mul_le_iff₀ hβ]
    exact hm.1.trans hR
  · intro x
    rw [objective_eq (p := p) π o hn c β, objective_eq (p := p) π o hn c β]
    change c * mean π o (β • β⁻¹ • minimizer (p := p) π o hn) ≤ _
    rw [smul_inv_smul₀ hβ.ne']
    exact mul_le_mul_of_nonneg_left (hm.2 _) hc

end LongTails.Proofs.ComponentHessianInstance
