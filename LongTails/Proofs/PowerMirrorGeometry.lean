import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import LongTails.Proofs.PowerMirrorEnergy

namespace LongTails.Proofs.PowerMirrorGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_direction [FiniteDimensional ℝ E] (g : E →L[ℝ] ℝ) :
    ∃ v, ‖v‖ ≤ ‖g‖ ∧ g v = ‖g‖ ^ 2 := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (show (Metric.closedBall (0 : E) 1).Nonempty from ⟨0, by simp⟩)
    g.continuous.continuousOn
  have hu' : ‖u‖ ≤ 1 := by simpa using hu
  have hnonneg : 0 ≤ g u := by simpa using hmax (by simp : (0 : E) ∈ Metric.closedBall 0 1)
  have hop : ‖g‖ ≤ g u := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hnonneg
    intro w hw
    have hpos : g w ≤ g u := hmax (by simp [hw] : w ∈ Metric.closedBall (0 : E) 1)
    have hneg : g (-w) ≤ g u := hmax (by simp [hw] : -w ∈ Metric.closedBall (0 : E) 1)
    rw [Real.norm_eq_abs, abs_le]
    simp only [map_neg] at hneg
    exact ⟨by linarith, hpos⟩
  have heq : g u = ‖g‖ := le_antisymm
    ((le_abs_self _).trans ((g.le_opNorm u).trans
      (by nlinarith [norm_nonneg g]))) hop
  refine ⟨‖g‖ • u, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg g)]
    nlinarith [norm_nonneg g]
  · simp [heq, sq]

lemma smooth_upper {f : E → ℝ} {g : E → E →L[ℝ] ℝ} {L : ℝ}
    (hg : ∀ x, HasFDerivAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + g x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  let v := y - x
  let F := fun t : ℝ => f (x + t • v)
  let F' := fun t : ℝ => g (x + t • v) v
  have hF (t : ℝ) : HasDerivAt F (F' t) t := by
    simpa only [F, F', Function.comp_def, id_eq, one_smul] using
      (hg (x + t • v)).comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const v |>.const_add x)
  let B := fun t : ℝ => f x + t * g x v + t ^ 2 * (L / 2 * ‖v‖ ^ 2)
  have hB (t : ℝ) : HasDerivAt B (g x v + L * ‖v‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).mul_const (g x v) |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖v‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Set.Ico (0 : ℝ) 1, F' t ≤ g x v + L * ‖v‖ ^ 2 * t := by
    intro t ht
    have hp := (le_abs_self ((g (x + t • v) - g x) v)).trans
      ((g (x + t • v) - g x).le_opNorm v)
    have hs := mul_le_mul_of_nonneg_right (hlip (x + t • v) x) (norm_nonneg v)
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hs
    simp only [sub_apply] at hp
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, v] using h

lemma convex_support {C : Set E} {f : E → ℝ} {g : E →L[ℝ] ℝ} {x y : E}
    (hc : ConvexOn ℝ C f) (hx : x ∈ C) (hy : y ∈ C)
    (hg : HasFDerivAt f g x) : g (y - x) ≤ f y - f x := by
  have hconv := hc.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivAt f g ((AffineMap.lineMap x y) (0 : ℝ)) := by simpa using hg
  have hline : HasDerivAt (f ∘ AffineMap.lineMap x y) (g (y - x)) (0 : ℝ) := by
    simpa using hd.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have h := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa using hx) (by simpa using hy) (by norm_num) hline
  simpa [slope_def_field] using h

lemma relative_steepest_descent {f : E → ℝ} {G g : E →L[ℝ] ℝ}
    {x v : E} {L α : ℝ} (hL : 0 < L) (hα : 0 ≤ α) (hα' : α ≤ 1 / 4)
    (herr : ‖g - G‖ ≤ α * ‖G‖) (hv : ‖v‖ ≤ ‖g‖) (hgv : g v = ‖g‖ ^ 2)
    (hmodel : ∀ y, f y ≤ f x + G (y - x) + L / 2 * ‖y - x‖ ^ 2) :
    f (x - (1 / (2 * L)) • v) ≤ f x - ‖g‖ ^ 2 / (8 * L) := by
  have hG : ‖G‖ ≤ ‖g‖ + ‖g - G‖ := by
    have h := norm_sub_le g (g - G)
    simpa only [sub_sub_cancel] using h
  have he := PowerMirrorEnergy.relative_error_reply_bound hα' (norm_nonneg _) herr hG hα
  have he' : ‖g - G‖ ≤ ‖g‖ / 3 := by nlinarith [norm_nonneg g]
  have hp := (le_abs_self ((g - G) v)).trans ((g - G).le_opNorm v)
  have hp' : ‖g - G‖ * ‖v‖ ≤ ‖g‖ ^ 2 / 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg (g - G)),
      mul_le_mul_of_nonneg_right he' (norm_nonneg g)]
  change g v - G v ≤ ‖g - G‖ * ‖v‖ at hp
  have hGv : (2 / 3) * ‖g‖ ^ 2 ≤ G v := by rw [hgv] at hp; linarith
  have hv2 : ‖v‖ ^ 2 ≤ ‖g‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hv
  let η : ℝ := 1 / (2 * L)
  have hη : 0 < η := by dsimp [η]; positivity
  have hd : (x - η • v) - x = (-η) • v := by module
  have hs := hmodel (x - η • v)
  rw [hd, map_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη] at hs
  simp only [smul_eq_mul] at hs
  have hlin := mul_le_mul_of_nonneg_left hGv hη.le
  have hsq := mul_le_mul_of_nonneg_left hv2 (show 0 ≤ L / 2 * η ^ 2 by positivity)
  have hb : f (x - η • v) ≤ f x - η * ((2 / 3) * ‖g‖ ^ 2) +
      L / 2 * η ^ 2 * ‖g‖ ^ 2 := by nlinarith
  have heq : f x - η * ((2 / 3) * ‖g‖ ^ 2) + L / 2 * η ^ 2 * ‖g‖ ^ 2 =
      f x - 5 * ‖g‖ ^ 2 / (24 * L) := by dsimp [η]; field_simp; ring
  rw [heq] at hb
  change f (x - η • v) ≤ _
  have hn : 0 ≤ ‖g‖ ^ 2 / (24 * L) := by positivity
  have heq' : ‖g‖ ^ 2 / (8 * L) = 3 * (‖g‖ ^ 2 / (24 * L)) := by ring
  have heq5 : 5 * ‖g‖ ^ 2 / (24 * L) = 5 * (‖g‖ ^ 2 / (24 * L)) := by ring
  rw [heq5] at hb
  rw [heq']
  linarith

lemma minimizer_derivative_nonneg {C : Set E} {f : E → ℝ} {g : E →L[ℝ] ℝ}
    {x y : E} (hc : Convex ℝ C) (hx : x ∈ C) (hy : y ∈ C)
    (hmin : ∀ w ∈ C, f x ≤ f w) (hg : HasFDerivAt f g x) :
    0 ≤ g (y - x) := by
  have hm : IsMinOn f C x := hmin
  exact hm.isLocalMinOn.hasFDerivWithinAt_nonneg hg.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hc.segment_subset hx hy))

lemma convex_coupling {f : E → ℝ} {G : E →L[ℝ] ℝ} {x y z u : E}
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hc : ConvexOn ℝ Set.univ f) (hd : HasFDerivAt f G y)
    (hmix : (A + a) • y = A • x + a • z) :
    (A + a) * (f y - f u) ≤ A * (f x - f u) + a * G (z - u) := by
  have hx := convex_support hc (Set.mem_univ y) (Set.mem_univ x) hd
  have hu := convex_support hc (Set.mem_univ y) (Set.mem_univ u) hd
  have hx' := mul_le_mul_of_nonneg_left hx hA
  have hu' := mul_le_mul_of_nonneg_left hu ha
  have he := congrArg G hmix
  simp only [map_add, map_smul, smul_eq_mul] at he
  simp only [map_sub] at hx' hu' ⊢
  nlinarith

omit [NormedSpace ℝ E] in
lemma squared_norm_triangle {x0 w z : E} :
    ‖z - x0‖ ^ 2 / 2 ≤ 2 * (‖w - x0‖ ^ 2 / 2) + ‖w - z‖ ^ 2 := by
  have ht : ‖z - x0‖ ≤ ‖w - z‖ + ‖w - x0‖ := by
    simpa only [sub_add_sub_cancel, norm_sub_rev z w] using
      norm_add_le (z - w) (w - x0)
  have hs := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖w - z‖ + ‖w - x0‖) |>.mpr ht
  nlinarith [sq_nonneg (‖w - z‖ - ‖w - x0‖)]

omit [NormedSpace ℝ E] in
lemma squared_comparator_distance {x0 w z u : E} {R : ℝ}
    (hR : ‖u - x0‖ ≤ R) :
    ‖z - u‖ ^ 2 ≤ 3 * ‖w - z‖ ^ 2 +
      6 * (‖w - x0‖ ^ 2 / 2) + 3 * R ^ 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have ht : ‖z - u‖ ≤ ‖w - z‖ + ‖w - x0‖ + R := by
    calc
      _ ≤ ‖z - w‖ + ‖w - u‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (z - w) (w - u)
      _ ≤ ‖z - w‖ + (‖w - x0‖ + ‖x0 - u‖) :=
        add_le_add (le_refl _) (by simpa only [sub_add_sub_cancel] using
          (norm_add_le (w - x0) (x0 - u)))
      _ ≤ ‖w - z‖ + ‖w - x0‖ + R := by
        rw [norm_sub_rev z w, norm_sub_rev x0 u]
        linarith
  have hs := sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ ‖w - z‖ + ‖w - x0‖ + R) |>.mpr ht
  nlinarith [sq_nonneg (‖w - z‖ - ‖w - x0‖),
    sq_nonneg (‖w - z‖ - R), sq_nonneg (‖w - x0‖ - R)]

lemma norm_square_prox_minimizer {h : E →L[ℝ] ℝ} {v x0 : E} {β : ℝ}
    (hβ : 0 < β) (hv : ‖v‖ ≤ ‖h‖) (hpair : h v = ‖h‖ ^ 2) (w : E) :
    β * (‖(x0 - (1 / β) • v) - x0‖ ^ 2 / 2) + h (x0 - (1 / β) • v) ≤
      β * (‖w - x0‖ ^ 2 / 2) + h w := by
  have hz : ‖(x0 - (1 / β) • v) - x0‖ ≤ ‖h‖ / β := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      mul_le_mul_of_nonneg_left hv (show 0 ≤ 1 / β by positivity)
  have hzs := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖h‖ / β) |>.mpr hz
  have hzβ := mul_le_mul_of_nonneg_left hzs hβ.le
  have hw : -‖h‖ * ‖w - x0‖ ≤ h w - h x0 := by
    have ha := neg_abs_le (h (w - x0))
    have hb := h.le_opNorm (w - x0)
    simp only [map_sub, Real.norm_eq_abs] at ha hb
    linarith
  have hs := sq_nonneg (β * ‖w - x0‖ - ‖h‖)
  simp only [map_sub, map_smul, smul_eq_mul, hpair]
  have hden : β * (‖h‖ / β) ^ 2 = ‖h‖ ^ 2 / β := by field_simp
  rw [hden] at hzβ
  have hlow : - ‖h‖ ^ 2 / β ≤ β * ‖w - x0‖ ^ 2 + 2 * (h w - h x0) := by
    apply (div_le_iff₀ hβ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hw hβ.le]
  simp only [div_eq_mul_inv] at hzβ hlow ⊢
  nlinarith

omit [NormedSpace ℝ E] in
lemma norm_square_curvature_surrogate {x0 w z : E} {p c β μ t b : ℝ}
    (hp : 2 ≤ p) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hμ : 0 ≤ μ) (ht : 0 < t)
    (hscale : μ ≤ β * c * t ^ (p - 2))
    (hcurv : c * ‖w - z‖ ^ p / (‖w - x0‖ + ‖z - x0‖) ^ (p - 2) ≤ b) :
    μ * ‖w - z‖ ^ 2 / 2 ≤ β * b +
      4 * μ * t ^ 2 * (‖w - x0‖ ^ 2 / 2 + ‖z - x0‖ ^ 2 / 2) := by
  have hb : 0 ≤ b := le_trans (by positivity) hcurv
  have hS0 : 0 ≤ ‖w - x0‖ + ‖z - x0‖ := by positivity
  by_cases hS : ‖w - x0‖ + ‖z - x0‖ = 0
  · have hw : w = x0 := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (z - x0), norm_nonneg (w - x0)]
    have hz : z = x0 := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (z - x0), norm_nonneg (w - x0)]
    subst w
    subst z
    simpa using mul_nonneg hβ hb
  · have hSpos : 0 < ‖w - x0‖ + ‖z - x0‖ := lt_of_le_of_ne hS0 (Ne.symm hS)
    have hh := PowerMirrorEnergy.scale_relative_quadratic (norm_nonneg (w - z))
      hSpos ht hp hc hβ hμ hscale hcurv
    have hs : (‖w - x0‖ + ‖z - x0‖) ^ 2 ≤
        4 * (‖w - x0‖ ^ 2 / 2 + ‖z - x0‖ ^ 2 / 2) := by
      nlinarith [sq_nonneg (‖w - x0‖ - ‖z - x0‖)]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ μ * t ^ 2 by positivity)
    nlinarith only [hh, hm]

lemma dual_averaging_drift {ψ : E → ℝ} {dψ h g : E →L[ℝ] ℝ}
    {β β' a μ κ δ : ℝ} {z z' u : E}
    (ha : 0 ≤ a) (hμ : 0 < μ) (hd : HasFDerivAt ψ dψ z)
    (hmin : ∀ v, β * ψ z + h z ≤ β * ψ v + h v)
    (hquad : μ * ‖z' - z‖ ^ 2 / 2 + κ * ‖z' - z‖ ^ 2 - δ * ψ z' ≤
      β * (ψ z' - ψ z - dψ (z' - z))) :
    (β' * ψ u + (h + a • g) u - (β' * ψ z' + (h + a • g) z')) ≤
      (β * ψ u + h u - (β * ψ z + h z)) + (β' - β) * ψ u +
        a * g (u - z) + a ^ 2 * ‖g‖ ^ 2 / (2 * μ) +
        (δ - (β' - β)) * ψ z' - κ * ‖z' - z‖ ^ 2 := by
  have hg : HasFDerivAt (fun v => β * ψ v + h v) (β • dψ + h) z :=
    (hd.const_mul β).add h.hasFDerivAt
  have hs := minimizer_derivative_nonneg (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ z) (Set.mem_univ z') (fun v _ => hmin v) hg
  change 0 ≤ β * dψ (z' - z) + h (z' - z) at hs
  have hpair : g (z - z') ≤ ‖g‖ * ‖z' - z‖ := by
    have hh := (le_abs_self (g (z - z'))).trans (g.le_opNorm (z - z'))
    simpa only [norm_sub_rev z z'] using hh
  have hpair' := mul_le_mul_of_nonneg_left hpair ha
  have hyoung := PowerMirrorEnergy.quadratic_cross_bound
    (a := ‖z' - z‖) (b := a * ‖g‖) (s := μ / 2) (by positivity)
  have heq : (a * ‖g‖) ^ 2 / (4 * (μ / 2)) = a ^ 2 * ‖g‖ ^ 2 / (2 * μ) := by ring
  rw [heq] at hyoung
  simp only [map_sub] at hs hquad hpair' ⊢
  change β' * ψ u + (h u + a * g u) - (β' * ψ z' + (h z' + a * g z')) ≤ _
  nlinarith

end LongTails.Proofs.PowerMirrorGeometry
