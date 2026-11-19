import LongTails.Proofs.SmoothConvexFiniteGeometry
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import LongTails.Proofs.LocalizedMonotoneConstruction
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.SecondOrderMintyProfile

open SmoothConvexFiniteGeometry

noncomputable def step (u : ℝ) : ℝ := ramp u - ramp (u - 1)

def stepSlope (u : ℝ) : ℝ := rampSlope u - rampSlope (u - 1)

lemma step_hasDerivAt (u : ℝ) : HasDerivAt step (stepSlope u) u := by
  have h2 : HasDerivAt (fun x => ramp (x - 1)) (rampSlope (u - 1)) u := by
    exact HasDerivAt.comp_sub_const u 1 (ramp_hasDerivAt (u - 1))
  exact (ramp_hasDerivAt u).sub h2

lemma stepSlope_nonneg (u : ℝ) : 0 ≤ stepSlope u := by
  simp only [stepSlope, rampSlope_cases]
  split_ifs <;> linarith

lemma stepSlope_le_one (u : ℝ) : stepSlope u ≤ 1 := by
  simp only [stepSlope, rampSlope_cases]
  split_ifs <;> linarith

lemma stepSlope_lipschitz (u v : ℝ) : |stepSlope u - stepSlope v| ≤ 2 * |u - v| := by
  have h1 := rampSlope_lipschitz u v
  have h2 := rampSlope_lipschitz (u - 1) (v - 1)
  have he : u - 1 - (v - 1) = u - v := by ring
  rw [he] at h2
  calc
    |stepSlope u - stepSlope v| =
        |(rampSlope u - rampSlope v) - (rampSlope (u - 1) - rampSlope (v - 1))| := by
      congr 1
      simp only [stepSlope]
      ring
    _ ≤ |rampSlope u - rampSlope v| + |rampSlope (u - 1) - rampSlope (v - 1)| := abs_sub _ _
    _ ≤ 2 * |u - v| := by linarith

lemma step_flat (u : ℝ) (hu : u ≤ 0) : step u = 0 ∧ stepSlope u = 0 := by
  have hu1 : u - 1 ≤ 0 := by linarith
  simp [step, stepSlope, ramp, rampSlope_cases, hu, hu1]

lemma step_top (u : ℝ) (hu : 2 ≤ u) : step u = 1 ∧ stepSlope u = 0 := by
  simp only [step, stepSlope, ramp, rampSlope_cases]
  split_ifs <;> constructor <;> nlinarith

lemma step_bounds (u : ℝ) : 0 ≤ step u ∧ step u ≤ 1 := by
  simp only [step, ramp]
  split_ifs <;> constructor <;> nlinarith

lemma step_symm (u : ℝ) : step (2 - u) = 1 - step u := by
  simp only [step, ramp]
  split_ifs <;> first | linarith | nlinarith

lemma step_monotone : Monotone step := by
  apply monotone_of_deriv_nonneg (fun x => (step_hasDerivAt x).differentiableAt)
  intro x
  rw [(step_hasDerivAt x).deriv]
  exact stepSlope_nonneg x

lemma step_half : step (1 / 2) = 1 / 8 := by
  norm_num [step, ramp]

noncomputable def gate (t : ℝ) : ℝ := step (8 * t - 2)

noncomputable def gateSlope (t : ℝ) : ℝ := 8 * stepSlope (8 * t - 2)

lemma gate_hasDerivAt (t : ℝ) : HasDerivAt gate (gateSlope t) t := by
  have hi : HasDerivAt (fun s : ℝ => 8 * s - 2) 8 t := by
    simpa using ((hasDerivAt_id t).const_mul 8).sub_const 2
  have h := (step_hasDerivAt (8 * t - 2)).comp t hi
  have he : gateSlope t = stepSlope (8 * t - 2) * 8 := by simp only [gateSlope]; ring
  rw [he]
  exact h

lemma gate_flat (t : ℝ) (ht : t ≤ 1 / 4) : gate t = 0 ∧ gateSlope t = 0 := by
  have h := step_flat (8 * t - 2) (by linarith)
  simp [gate, gateSlope, h.1, h.2]

lemma gate_top (t : ℝ) (ht : 1 / 2 ≤ t) : gate t = 1 := by
  exact (step_top (8 * t - 2) (by linarith)).1

lemma gate_bounds (t : ℝ) : 0 ≤ gate t ∧ gate t ≤ 1 := step_bounds _

lemma gateSlope_bounds (t : ℝ) : 0 ≤ gateSlope t ∧ gateSlope t ≤ 8 := by
  constructor
  · have := stepSlope_nonneg (8 * t - 2); simp only [gateSlope]; linarith
  · have := stepSlope_le_one (8 * t - 2); simp only [gateSlope]; linarith

lemma gateSlope_lipschitz (t s : ℝ) : |gateSlope t - gateSlope s| ≤ 128 * |t - s| := by
  have h := stepSlope_lipschitz (8 * t - 2) (8 * s - 2)
  have he : 8 * t - 2 - (8 * s - 2) = 8 * (t - s) := by ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at h
  have he2 : gateSlope t - gateSlope s = 8 * (stepSlope (8 * t - 2) - stepSlope (8 * s - 2)) := by
    simp only [gateSlope]; ring
  rw [he2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith

noncomputable def sat (s : ℝ) : ℝ := 2 * step (s + 1) - 1

noncomputable def satSlope (s : ℝ) : ℝ := 2 * stepSlope (s + 1)

lemma sat_hasDerivAt (s : ℝ) : HasDerivAt sat (satSlope s) s := by
  have h1 : HasDerivAt (fun x => step (x + 1)) (stepSlope (s + 1)) s := by
    exact HasDerivAt.comp_add_const s 1 (step_hasDerivAt (s + 1))
  exact (h1.const_mul 2).sub_const 1

lemma sat_zero : sat 0 = 0 := by norm_num [sat, step, ramp]

lemma sat_neg (s : ℝ) : sat (-s) = -sat s := by
  have h := step_symm (s + 1)
  have he : 2 - (s + 1) = -s + 1 := by ring
  rw [he] at h
  simp only [sat, h]
  ring

lemma sat_bounds (s : ℝ) : |sat s| ≤ 1 := by
  have h := step_bounds (s + 1)
  rw [abs_le]
  constructor <;> simp only [sat] <;> linarith

lemma satSlope_bounds (s : ℝ) : 0 ≤ satSlope s ∧ satSlope s ≤ 2 := by
  constructor
  · have := stepSlope_nonneg (s + 1); simp only [satSlope]; linarith
  · have := stepSlope_le_one (s + 1); simp only [satSlope]; linarith

lemma satSlope_lipschitz (s t : ℝ) : |satSlope s - satSlope t| ≤ 4 * |s - t| := by
  have h := stepSlope_lipschitz (s + 1) (t + 1)
  have he : s + 1 - (t + 1) = s - t := by ring
  rw [he] at h
  have he2 : satSlope s - satSlope t = 2 * (stepSlope (s + 1) - stepSlope (t + 1)) := by
    simp only [satSlope]; ring
  rw [he2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

lemma sat_monotone : Monotone sat := by
  intro a b hab
  have := step_monotone (show a + 1 ≤ b + 1 by linarith)
  simp only [sat]
  linarith

lemma sat_mul_nonneg (s : ℝ) : 0 ≤ s * sat s := by
  rcases le_total 0 s with h | h
  · have := sat_monotone h
    rw [sat_zero] at this
    exact mul_nonneg h this
  · have := sat_monotone h
    rw [sat_zero] at this
    exact mul_nonneg_of_nonpos_of_nonpos h this

lemma sat_low (s : ℝ) (hs : s ≤ -1 / 2) : sat s ≤ -3 / 4 := by
  have h := sat_monotone hs
  have hv : sat (-1 / 2) = -3 / 4 := by
    have : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    simp only [sat, this, step_half]
    norm_num
  linarith

lemma gate_difference (t s : ℝ) : |gate t - gate s| ≤ 8 * |t - s| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (gate_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => show ‖gateSlope z‖ ≤ 8 by
      rw [Real.norm_eq_abs, abs_of_nonneg (gateSlope_bounds z).1]
      exact (gateSlope_bounds z).2) (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using h

lemma sat_difference (t s : ℝ) : |sat t - sat s| ≤ 2 * |t - s| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (sat_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => show ‖satSlope z‖ ≤ 2 by
      rw [Real.norm_eq_abs, abs_of_nonneg (satSlope_bounds z).1]
      exact (satSlope_bounds z).2) (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using h

end LongTails.Proofs.SecondOrderMintyProfile

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SecondOrderMintyChain

open SecondOrderMintyProfile LocalizedMonotoneConstruction ContinuousLinearMap

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def head (κ r t : ℝ) : ℝ := κ * r * sat (t / r - 1)

noncomputable def headSlope (κ r t : ℝ) : ℝ := κ * satSlope (t / r - 1)

noncomputable def link (κ r s t : ℝ) : ℝ := κ * r * (gate (s / r) * sat (t / r - 1))

noncomputable def linkIn (κ r s t : ℝ) : ℝ := κ * (gateSlope (s / r) * sat (t / r - 1))

noncomputable def linkOut (κ r s t : ℝ) : ℝ := κ * (gate (s / r) * satSlope (t / r - 1))

noncomputable def chain {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) : Space d :=
  head κ r (x (π 0)) • axis (π 0) +
    ∑ j : Fin n, link κ r (x (π j.castSucc)) (x (π j.succ)) • axis (π j.succ)

noncomputable def chainJacobian {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    Space d →L[ℝ] Space d :=
  headSlope κ r (x (π 0)) • InnerProductSpace.rankOne ℝ (axis (π 0)) (axis (π 0)) +
    ∑ j : Fin n, (linkIn κ r (x (π j.castSucc)) (x (π j.succ)) •
        InnerProductSpace.rankOne ℝ (axis (π j.succ)) (axis (π j.castSucc)) +
      linkOut κ r (x (π j.castSucc)) (x (π j.succ)) •
        InnerProductSpace.rankOne ℝ (axis (π j.succ)) (axis (π j.succ)))

lemma coordinate_hasFDerivAt {d : ℕ} (i : Fin d) (x : Space d) :
    HasFDerivAt (fun y : Space d => y i) (innerSL ℝ (axis i)) x := by
  have h := (innerSL ℝ (axis i)).hasFDerivAt (x := x)
  convert h using 1
  funext y
  simp [axis_inner]

lemma scaled_sat_hasDerivAt (r t : ℝ) :
    HasDerivAt (fun s : ℝ => sat (s / r - 1)) (satSlope (t / r - 1) / r) t := by
  have hi : HasDerivAt (fun s : ℝ => s / r - 1) (1 / r) t := by
    simpa using ((hasDerivAt_id t).div_const r).sub_const 1
  have h := (sat_hasDerivAt (t / r - 1)).comp t hi
  have he : satSlope (t / r - 1) / r = satSlope (t / r - 1) * (1 / r) := by ring
  rw [he]
  exact h

lemma scaled_gate_hasDerivAt (r t : ℝ) :
    HasDerivAt (fun s : ℝ => gate (s / r)) (gateSlope (t / r) / r) t := by
  have hi : HasDerivAt (fun s : ℝ => s / r) (1 / r) t := by
    simpa using (hasDerivAt_id t).div_const r
  have h := (gate_hasDerivAt (t / r)).comp t hi
  have he : gateSlope (t / r) / r = gateSlope (t / r) * (1 / r) := by ring
  rw [he]
  exact h

lemma head_term_hasFDerivAt {d : ℕ} (κ r : ℝ) (hr : 0 < r) (i : Fin d) (x : Space d) :
    HasFDerivAt (fun y : Space d => head κ r (y i) • axis i)
      (headSlope κ r (x i) • InnerProductSpace.rankOne ℝ (axis i) (axis i)) x := by
  have hs := ((scaled_sat_hasDerivAt r (x i)).comp_hasFDerivAt x
    (coordinate_hasFDerivAt i x)).const_mul (κ * r)
  have h := hs.smul_const (axis i)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [smul_apply, InnerProductSpace.rankOne_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul, smul_eq_mul]
  congr 1
  simp only [headSlope]
  field_simp

lemma link_term_hasFDerivAt {d : ℕ} (κ r : ℝ) (hr : 0 < r) (i k : Fin d) (x : Space d) :
    HasFDerivAt (fun y : Space d => link κ r (y i) (y k) • axis k)
      (linkIn κ r (x i) (x k) • InnerProductSpace.rankOne ℝ (axis k) (axis i) +
        linkOut κ r (x i) (x k) • InnerProductSpace.rankOne ℝ (axis k) (axis k)) x := by
  have hg := (scaled_gate_hasDerivAt r (x i)).comp_hasFDerivAt x (coordinate_hasFDerivAt i x)
  have hs := (scaled_sat_hasDerivAt r (x k)).comp_hasFDerivAt x (coordinate_hasFDerivAt k x)
  have hp := (hg.mul hs).const_mul (κ * r)
  have h := hp.smul_const (axis k)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [add_apply, smul_apply,
    InnerProductSpace.rankOne_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_smul, smul_eq_mul, ← add_smul, Function.comp_apply]
  congr 1
  simp only [linkIn, linkOut]
  field_simp
  ring

lemma chain_hasFDerivAt {d n : ℕ} (κ r : ℝ) (hr : 0 < r) (π : Fin (n + 1) ↪ Fin d)
    (x : Space d) : HasFDerivAt (chain κ r π) (chainJacobian κ r π x) x := by
  have h0 := head_term_hasFDerivAt κ r hr (π 0) x
  have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) (fun j _ =>
    link_term_hasFDerivAt κ r hr (π j.castSucc) (π j.succ) x)
  exact h0.add hs

lemma chain_zero {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    chain κ r π x (π 0) = head κ r (x (π 0)) := by
  classical
  simp only [chain, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp [axis, π.injective.eq_iff, Fin.succ_ne_zero]

lemma chain_succ {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) (j : Fin n) :
    chain κ r π x (π j.succ) = link κ r (x (π j.castSucc)) (x (π j.succ)) := by
  classical
  simp only [chain, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp [axis, π.injective.eq_iff]

lemma chain_outside {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x : Space d) (i : Fin d)
    (hi : ∀ j, i ≠ π j) : chain κ r π x i = 0 := by
  classical
  simp only [chain, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp [axis, hi]

lemma chainJacobian_zero {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x z : Space d) :
    chainJacobian κ r π x z (π 0) = headSlope κ r (x (π 0)) * z (π 0) := by
  classical
  simp only [chainJacobian, add_apply, smul_apply, sum_apply, InnerProductSpace.rankOne_apply,
    axis_inner]
  simp [axis, π.injective.eq_iff, Fin.succ_ne_zero]

lemma chainJacobian_succ {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x z : Space d)
    (j : Fin n) :
    chainJacobian κ r π x z (π j.succ) =
      linkIn κ r (x (π j.castSucc)) (x (π j.succ)) * z (π j.castSucc) +
        linkOut κ r (x (π j.castSucc)) (x (π j.succ)) * z (π j.succ) := by
  classical
  simp only [chainJacobian, add_apply, smul_apply, sum_apply, InnerProductSpace.rankOne_apply,
    axis_inner]
  simp [axis, Pi.single_apply, π.injective.eq_iff, Finset.sum_add_distrib]

lemma chainJacobian_outside {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) (x z : Space d)
    (i : Fin d) (hi : ∀ j, i ≠ π j) : chainJacobian κ r π x z i = 0 := by
  classical
  simp only [chainJacobian, add_apply, smul_apply, sum_apply, InnerProductSpace.rankOne_apply,
    axis_inner]
  simp [axis, hi]

end LongTails.Proofs.SecondOrderMintyChain
