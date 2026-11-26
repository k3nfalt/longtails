import LongTails.Proofs.HessianReuseModelFlowPath
import LongTails.Proofs.GradientDependentLocal

namespace LongTails.Proofs.HessianReuseModelFlowDescent

open Set LongTails.Setups.GradientDependentHessian
open LongTails.Algorithms.HessianReuseModelFlow HessianReuseModelFlowPath
open scoped RealInnerProductSpace

variable {p : Params}

local instance : CompleteSpace p.E := FiniteDimensional.complete ℝ p.E

lemma stopped_estimates (hp : spec.valid p) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (x : p.E) (H : p.E →L[ℝ] p.E) (j : ℕ) (hj : j < p.m)
    (hstart : ‖fderiv ℝ (gradient f) x - H‖ ≤ j * radius p * curvature p)
    (hg : p.ε < ‖gradient f x‖) :
    let g := gradient f x
    let τ := stopTime p g H
    let y := x + displacement g H τ
    ‖gradient f y - velocity g H τ‖ ≤ allowance p ∧
      ‖fderiv ℝ (gradient f) y - H‖ ≤ (j + 1 : ℝ) * radius p * curvature p ∧
      f y + energy g H τ - allowance p * radius p / 2 ≤ f x := by
  let g := gradient f x
  let A := fderiv ℝ (gradient f)
  let T := fderiv ℝ A
  let τ := stopTime p g H
  let v := velocity g H
  let γ := fun t => x + displacement g H t
  let e := fun t => gradient f (γ t) - v t
  let D := fun t => A (γ t) - H
  obtain ⟨hτ, hpath, _⟩ := stop_spec g H hp hg
  change 0 ≤ τ at hτ
  obtain ⟨hF, hG, hA⟩ := GradientDependentLocal.derivative_chain hf
  have hγ (t : ℝ) : HasDerivAt γ (-v t) t := (displacement_deriv g H t).const_add x
  have hγ0 : γ 0 = x := by simp [γ, displacement]
  have hD (t : ℝ) : HasDerivAt D (T (γ t) (-v t)) t :=
    ((hA _).comp_hasDerivAt t (hγ t)).sub_const H
  have he (t : ℝ) : HasDerivAt e (D t (-v t)) t := by
    simpa [e, D, A, v, sub_apply, Pi.sub_def, Function.comp_def] using
      (((hG _).comp_hasDerivAt t (hγ t)).sub (velocity_deriv g H t))
  have he0 : e 0 = 0 := by simp [e, hγ0, v, velocity_zero, g]
  obtain ⟨a, ha, hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hτ)
    (f := fun t => ‖e t‖) (fun t _ => (he t).continuousAt.norm.continuousWithinAt)
  let E := ‖e a‖
  have hE : 0 ≤ E := norm_nonneg _
  have herr (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖e t‖ ≤ E := hm ht
  let J := (j : ℝ) * radius p * curvature p
  have hJ : 0 ≤ J := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (radius_pos hp).le) (curvature_pos hp).le
  let C := J + ((p.L₀ + p.L₁ * E) * radius p + p.L₁ * energyCap p)
  have hcoef : 0 ≤ p.L₀ + p.L₁ * E := add_nonneg hp.1.le (mul_nonneg hp.2.1 hE)
  have hC : 0 ≤ C := add_nonneg hJ (add_nonneg (mul_nonneg hcoef (radius_pos hp).le)
    (mul_nonneg hp.2.1 (cap_pos hp).le))
  have hDb (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖D t‖ ≤ C := by
    let B := fun s => J + ((p.L₀ + p.L₁ * E) * pathLength g H s + p.L₁ * energy g H s)
    have hB (s : ℝ) : HasDerivAt B ((p.L₀ + p.L₁ * E) * ‖v s‖ + p.L₁ * ‖v s‖ ^ 2) s :=
      (((length_deriv g H s).const_mul _).add ((energy_deriv g H s).const_mul _)).const_add J
    have hb (s : ℝ) (hs : s ∈ Ico 0 τ) :
        ‖T (γ s) (-v s)‖ ≤ (p.L₀ + p.L₁ * E) * ‖v s‖ + p.L₁ * ‖v s‖ ^ 2 := by
      have hgrad : ‖gradient f (γ s)‖ ≤ E + ‖v s‖ := by
        calc
          _ = ‖e s + v s‖ := by simp [e]
          _ ≤ ‖e s‖ + ‖v s‖ := norm_add_le _ _
          _ ≤ _ := add_le_add (herr s ⟨hs.1, hs.2.le⟩) le_rfl
      have hcurv : ‖T (γ s)‖ ≤ p.L₀ + p.L₁ * (E + ‖v s‖) :=
        (hT (γ s)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgrad hp.2.1))
      calc
        _ ≤ ‖T (γ s)‖ * ‖-v s‖ := (T (γ s)).le_opNorm _
        _ = ‖T (γ s)‖ * ‖v s‖ := by rw [norm_neg]
        _ ≤ (p.L₀ + p.L₁ * (E + ‖v s‖)) * ‖v s‖ :=
          mul_le_mul_of_nonneg_right hcurv (norm_nonneg _)
        _ = _ := by ring
    have hh := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun s _ => (hD s).continuousAt.continuousWithinAt)
      (fun s _ => (hD s).hasDerivWithinAt)
      (show ‖D 0‖ ≤ B 0 by simpa [D, hγ0, B, pathLength, energy, J, A] using hstart) hB hb ht
    exact hh.trans (add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left (length_bound g H hp hpath ht) hcoef)
      (mul_le_mul_of_nonneg_left (hpath t ht).2 hp.2.1)))
  have heB (s : ℝ) : HasDerivAt (fun t => C * pathLength g H t) (C * ‖v s‖) s :=
    (length_deriv g H s).const_mul C
  have heb (s : ℝ) (hs : s ∈ Ico 0 τ) : ‖D s (-v s)‖ ≤ C * ‖v s‖ := by
    simpa only [norm_neg] using ((D s).le_opNorm (-v s)).trans
      (mul_le_mul_of_nonneg_right (hDb s ⟨hs.1, hs.2.le⟩) (norm_nonneg _))
  have herrL (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖e t‖ ≤ C * pathLength g H t :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun s _ => (he s).continuousAt.continuousWithinAt)
      (fun s _ => (he s).hasDerivWithinAt)
      (show ‖e 0‖ ≤ C * pathLength g H 0 by simp [he0, pathLength]) heB heb ht
  have hmax := (herrL a ha).trans
    (mul_le_mul_of_nonneg_left (length_bound g H hp hpath ha) hC)
  have hr := radius_pos hp
  have hA := curvature_pos hp
  have hj' : (j : ℝ) + 1 ≤ p.m := by exact_mod_cast hj
  have hCeq : C = ((j : ℝ) + 1) * radius p * curvature p +
      p.L₁ * radius p * (E - allowance p) := by
    dsimp only [C, J, energyCap, curvature, allowance, threshold]
    ring
  have hscale := radius_scale hp
  have hbase := mul_le_mul_of_nonneg_right hj' (mul_nonneg hA.le (sq_nonneg (radius p)))
  have hε := hp.2.2.2.2.1
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast hp.2.2.2.2.2
  have hcoefLt : p.L₁ * radius p ^ 2 < 1 := by
    have ht := mul_le_mul_of_nonneg_right hm (mul_nonneg hA.le (sq_nonneg (radius p)))
    dsimp only [curvature, allowance] at hscale ht
    have hs : p.L₁ * radius p ^ 2 * p.ε < 1 * p.ε := by
      nlinarith only [hscale, ht, mul_nonneg hp.1.le (sq_nonneg (radius p)), hε]
    exact lt_of_mul_lt_mul_right hs hε.le
  have hsmall : E ≤ allowance p := by
    by_contra! h
    have hh := mul_lt_mul_of_pos_right hcoefLt (sub_pos.mpr h)
    rw [hCeq] at hmax
    change E ≤ _ at hmax
    nlinarith only [hmax, hbase, hscale, hh]
  have hCsmall : C ≤ ((j : ℝ) + 1) * radius p * curvature p := by
    rw [hCeq]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hp.2.1 hr.le) (sub_nonpos.mpr hsmall))
  have hCr : C * radius p ≤ allowance p := by
    have := mul_le_mul_of_nonneg_right hCsmall hr.le
    nlinarith only [this, hbase, hscale]
  have hdec := SelfConcordantCalculus.le_of_deriv_nonpos hτ
    (F := fun t => f (γ t) + energy g H t - (C / 2) * pathLength g H t ^ 2)
    (fun s _ => (((hF _).comp_hasDerivAt s (hγ s)).add (energy_deriv g H s)).sub
      (((length_deriv g H s).pow 2).const_mul (C / 2)))
    (fun s hs => by
      change ⟪gradient f (γ s), -v s⟫ + ‖v s‖ ^ 2 -
        C / 2 * (2 * pathLength g H s ^ 1 * ‖v s‖) ≤ 0
      have heq : gradient f (γ s) = e s + v s := (sub_add_cancel _ _).symm
      rw [heq, inner_neg_right, inner_add_left, real_inner_self_eq_norm_sq]
      have hprod := mul_le_mul_of_nonneg_right (herrL s hs) (norm_nonneg (v s))
      change ‖e s‖ * ‖v s‖ ≤ C * pathLength g H s * ‖v s‖ at hprod
      rw [pow_one]
      nlinarith only [(abs_le.mp (abs_real_inner_le_norm (e s) (v s))).1, hprod])
  have htτ : τ ∈ Icc 0 τ := ⟨hτ, le_rfl⟩
  have hlen := length_bound g H hp hpath htτ
  have hlen0 : 0 ≤ pathLength g H τ :=
    intervalIntegral.integral_nonneg hτ (fun _ _ => norm_nonneg _)
  have hcost := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlen0 hlen 2) hC
  have hh := mul_le_mul_of_nonneg_right hCr hr.le
  have hd : f (γ τ) + energy g H τ - C / 2 * pathLength g H τ ^ 2 ≤ f x := by
    simpa [hγ0, energy, pathLength] using hdec
  exact ⟨(herr τ htτ).trans hsmall, (hDb τ htτ).trans hCsmall, by
    change f (γ τ) + energy g H τ - _ ≤ f x
    nlinarith only [hd, hcost, hh]⟩

end LongTails.Proofs.HessianReuseModelFlowDescent
