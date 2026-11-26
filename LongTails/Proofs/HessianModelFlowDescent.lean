import LongTails.Proofs.HessianModelFlowPath
import LongTails.Proofs.GradientDependentLocal

namespace LongTails.Proofs.HessianModelFlowDescent

open Set LongTails.Setups.PointwiseHessianStationarity
open LongTails.Algorithms.PointwiseHessianModelFlow HessianModelFlowPath
open scoped RealInnerProductSpace

variable {p : Params}

private lemma absorb_error (hp : broadSpec.valid p) {E : ℝ} (hE : 0 ≤ E)
    (hb : E ≤ ((p.L₀ + p.L₁ * E) * radius p + p.L₁ * energyCap p) * radius p) :
    E ≤ p.ε / 15 := by
  have h₁ := mul_le_mul_of_nonneg_right (relative_radius hp) hE
  have h₂ := mul_nonneg (mul_nonneg hp.2.1 hp.2.2.2.2.2.le) (sq_nonneg (radius p))
  unfold energyCap at hb
  nlinarith only [hb, h₁, h₂, radius_scale hp]

lemma stopped_estimates (hp : broadSpec.valid p) {f : Point p → ℝ} (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (x : Point p) (hg : p.ε < ‖gradient f x‖) :
    let g := gradient f x
    let H := fderiv ℝ (gradient f) x
    let τ := stopTime p g H
    let y := x + displacement g H τ
    ‖gradient f y - velocity g H τ‖ ≤ p.ε / 15 ∧
      f y + 3 / 4 * energy g H τ ≤ f x := by
  let g := gradient f x
  let A := fderiv ℝ (gradient f)
  let T := fderiv ℝ A
  let H := A x
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
    simpa [e, D, A, H, v, sub_apply, Pi.sub_def, Function.comp_def] using
      (((hG _).comp_hasDerivAt t (hγ t)).sub (velocity_deriv g H t))
  have he0 : e 0 = 0 := by simp [e, hγ0, v, velocity_zero, g]
  obtain ⟨a, ha, hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hτ)
    (f := fun t => ‖e t‖) (fun t _ => (he t).continuousAt.norm.continuousWithinAt)
  let E := ‖e a‖
  have hE : 0 ≤ E := norm_nonneg _
  have herr (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖e t‖ ≤ E := hm ht
  let C := (p.L₀ + p.L₁ * E) * radius p + p.L₁ * energyCap p
  have hcoef : 0 ≤ p.L₀ + p.L₁ * E := add_nonneg hp.1 (mul_nonneg hp.2.1 hE)
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hcoef (radius_pos hp).le)
    (mul_nonneg hp.2.1 (cap_pos hp).le)
  have hDb (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖D t‖ ≤ C := by
    let B := fun s => (p.L₀ + p.L₁ * E) * pathLength g H s + p.L₁ * energy g H s
    have hB (s : ℝ) : HasDerivAt B ((p.L₀ + p.L₁ * E) * ‖v s‖ + p.L₁ * ‖v s‖ ^ 2) s :=
      ((length_deriv g H s).const_mul _).add ((energy_deriv g H s).const_mul _)
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
      (show ‖D 0‖ ≤ B 0 by simp [D, H, hγ0, B, pathLength, energy]) hB hb ht
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (length_bound g H hp hpath ht) hcoef)
      (mul_le_mul_of_nonneg_left (hpath t ht).2 hp.2.1))
  have heB (s : ℝ) : HasDerivAt (fun t => C * pathLength g H t) (C * ‖v s‖) s :=
    (length_deriv g H s).const_mul C
  have heb (s : ℝ) (hs : s ∈ Ico 0 τ) : ‖D s (-v s)‖ ≤ C * ‖v s‖ := by
    simpa only [norm_neg] using ((D s).le_opNorm (-v s)).trans
      (mul_le_mul_of_nonneg_right (hDb s ⟨hs.1, hs.2.le⟩) (norm_nonneg _))
  have hmax := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (he s).continuousAt.continuousWithinAt)
    (fun s _ => (he s).hasDerivWithinAt)
    (show ‖e 0‖ ≤ C * pathLength g H 0 by simp [he0, pathLength]) heB heb ha
  have hsmall := absorb_error hp hE
    (hmax.trans (mul_le_mul_of_nonneg_left (length_bound g H hp hpath ha) hC))
  have hdec := SelfConcordantCalculus.le_of_deriv_nonpos hτ
    (F := fun t => f (γ t) + 3 / 4 * energy g H t)
    (fun s _ => ((hF _).comp_hasDerivAt s (hγ s)).add ((energy_deriv g H s).const_mul (3 / 4)))
    (fun s hs => by
      change ⟪gradient f (γ s), -v s⟫ + 3 / 4 * ‖v s‖ ^ 2 ≤ 0
      have heq : gradient f (γ s) = e s + v s := (sub_add_cancel _ _).symm
      rw [heq, inner_neg_right, inner_add_left, real_inner_self_eq_norm_sq]
      have hbound : ‖e s‖ ≤ ‖v s‖ / 4 := by
        have h := (herr s hs).trans hsmall
        linarith [(hpath s hs).1, hp.2.2.2.2.2]
      have hprod := mul_le_mul_of_nonneg_right hbound (norm_nonneg (v s))
      nlinarith only [(abs_le.mp (abs_real_inner_le_norm (e s) (v s))).1, hprod])
  exact ⟨(herr τ ⟨hτ, le_rfl⟩).trans hsmall, by simpa [hγ0, energy] using hdec⟩

lemma step_spec (hp : broadSpec.valid p) {f : Point p → ℝ} (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (x : Point p) :
    match step p x (gradient f x) (fderiv ℝ (gradient f) x) with
    | .done y => ‖gradient f y‖ ≤ p.ε
    | .active y => f y + 3 / 4 * energyCap p ≤ f x := by
  by_cases hn : ‖gradient f x‖ ≤ p.ε
  · simp only [step, hn, ite_true]
  · obtain ⟨he, hd⟩ := stopped_estimates hp hf hT x (lt_of_not_ge hn)
    let g := gradient f x
    let H := fderiv ℝ (gradient f) x
    let τ := stopTime p g H
    obtain ⟨_, _, hend⟩ := stop_spec g H hp (lt_of_not_ge hn)
    by_cases h : ‖velocity g H τ‖ ≤ p.ε / 2
    · dsimp only [τ, H, g] at h
      simp only [step, hn, h, ite_true, ite_false]
      have htol : p.ε / 15 + p.ε / 2 ≤ p.ε := by linarith [hp.2.2.2.2.2]
      exact (norm_le_norm_sub_add _ _).trans ((add_le_add he h).trans htol)
    · dsimp only [τ, H, g] at h
      simp only [step, hn, h, ite_false]
      rw [← hend.resolve_left h]
      exact hd

end LongTails.Proofs.HessianModelFlowDescent
