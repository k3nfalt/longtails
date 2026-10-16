import LongTails.Proofs.SphereRotationMeasure

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SphereOddMoments

lemma interval_square_bound {v : ℝ → ℝ} (hv : Continuous v) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, v t) ^ 2 ≤ (b - a) * (∫ t in a..b, v t ^ 2) := by
  rcases hab.eq_or_lt with he | hlt
  · subst b
    simp
  let I := ∫ t in a..b, v t
  let c := I / (b - a)
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun t => sq_nonneg (v t - c))
  have he : (fun t => (v t - c) ^ 2) = fun t => v t ^ 2 - 2 * c * v t + c ^ 2 := by
    funext t
    ring
  have hi2 : IntervalIntegrable (fun t => v t ^ 2) volume a b :=
    (hv.pow 2).intervalIntegrable a b
  have him : IntervalIntegrable (fun t => 2 * c * v t) volume a b :=
    (hv.const_mul (2 * c)).intervalIntegrable a b
  have hsub := intervalIntegral.integral_sub hi2 him
  have hadd := intervalIntegral.integral_add (hi2.sub him)
    ((continuous_const : Continuous (fun _ : ℝ => c ^ 2)).intervalIntegrable a b)
  rw [he, hadd, hsub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hn
  have hm := mul_nonneg (sub_nonneg.mpr hab) hn
  have hc : (b - a) * c = I := by
    dsimp [c]
    field_simp [ne_of_gt (sub_pos.mpr hlt)]
  change I ^ 2 ≤ _
  change 0 ≤ (b - a) * ((∫ t in a..b, v t ^ 2) - 2 * c * I + (b - a) * c ^ 2) at hm
  nlinarith only [hm, congrArg (fun r : ℝ => r * I) hc,
    congrArg (fun r : ℝ => r ^ 2) hc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma great_circle_energy {a : E → ℝ} {g : E → E}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt a (g x) x)
    (hodd : ∀ x, a (-x) = -a x) (x y : E) :
    a x ^ 2 ≤ Real.pi / 4 *
      (∫ t in 0..Real.pi,
        ⟪g (Real.cos t • x + Real.sin t • y), -Real.sin t • x + Real.cos t • y⟫ ^ 2) := by
  let c := fun t : ℝ => Real.cos t • x + Real.sin t • y
  let w := fun t : ℝ => -Real.sin t • x + Real.cos t • y
  let v := fun t : ℝ => ⟪g (c t), w t⟫
  have hv : Continuous v := by dsimp [v, c, w]; fun_prop
  have hder (t : ℝ) : HasDerivAt (fun s => a (c s)) (v t) t := by
    have hc : HasDerivAt c (w t) t :=
      ((Real.hasDerivAt_cos t).smul_const x).add ((Real.hasDerivAt_sin t).smul_const y)
    exact (hd (c t)).hasFDerivAt.comp_hasDerivAt t hc
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    (hv.intervalIntegrable 0 Real.pi)
  have he : (∫ t in 0..Real.pi, v t) = -(2 * a x) := by
    simpa [c, hodd, two_mul, sub_eq_add_neg] using hf
  have hs := interval_square_bound hv Real.pi_pos.le
  rw [he] at hs
  dsimp [v, c, w] at hs
  nlinarith only [hs]

section Spherical

open OracleTemplate.ZerothOrder LongTails.Proofs.SphereRotationMeasure

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "e" => (fun i : Fin d => EuclideanSpace.single i (1 : ℝ))

lemma odd_sphere_second_moment {a : H → ℝ} {g : H → H}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt a (g x) x)
    (hodd : ∀ x, a (-x) = -a x) (i j : Fin d) (hij : i ≠ j) :
    ((d : ℝ) - 1) * (∫ u : sphere (0 : H) 1, a u ^ 2 ∂(sphereLaw H : Measure _)) ≤
      Real.pi ^ 2 / 4 * (∫ u : sphere (0 : H) 1, ‖g u‖ ^ 2 ∂(sphereLaw H : Measure _)) := by
  let P := rotationMeasure H
  let V := fun z : Rotation H × ℝ =>
    ⟪g (Real.cos z.2 • (z.1 : H →L[ℝ] H) (e i) +
          Real.sin z.2 • (z.1 : H →L[ℝ] H) (e j)),
      -Real.sin z.2 • (z.1 : H →L[ℝ] H) (e i) +
          Real.cos z.2 • (z.1 : H →L[ℝ] H) (e j)⟫ ^ 2
  have hV : Continuous V := by dsimp [V]; fun_prop
  have hi0 : IntegrableOn V (univ ×ˢ Icc (0 : ℝ) Real.pi) (P.prod volume) :=
    hV.continuousOn.integrableOn_compact (isCompact_univ.prod isCompact_Icc)
  have hi : Integrable V (P.prod (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    have h := hi0.mono_set (Set.prod_mono (Subset.refl _) Ioc_subset_Icc_self)
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  have ha : Continuous a := continuous_iff_continuousAt.mpr
    (fun x => (hd x).hasFDerivAt.continuousAt)
  have hLc : Continuous (fun U : Rotation H => a ((U : H →L[ℝ] H) (e i)) ^ 2) := by fun_prop
  have hL : Integrable (fun U : Rotation H => a ((U : H →L[ℝ] H) (e i)) ^ 2) P :=
    hLc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (U : Rotation H) : a ((U : H →L[ℝ] H) (e i)) ^ 2 ≤
      Real.pi / 4 * ∫ t in Ioc (0 : ℝ) Real.pi, V (U, t) := by
    simpa only [V, intervalIntegral.integral_of_le Real.pi_pos.le] using
      great_circle_energy hg hd hodd ((U : H →L[ℝ] H) (e i)) ((U : H →L[ℝ] H) (e j))
  have hm := integral_mono hL (hi.integral_prod_left.const_mul (Real.pi / 4)) hp
  rw [integral_const_mul, integral_integral_swap hi] at hm
  have he (t : ℝ) : (∫ U : Rotation H, V (U, t) ∂P) =
      ∫ U : Rotation H, ⟪g ((U : H →L[ℝ] H) (e i)), (U : H →L[ℝ] H) (e j)⟫ ^ 2 ∂P := by
    have h := integral_frame_circle H (fun x y => ⟪g x, y⟫ ^ 2)
      (x := e i) (y := e j) (by simp) (by simp) (by simp [PiLp.inner_apply, hij]) t
    simpa only [map_add, map_smul, V, P] using h
  simp_rw [he] at hm
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul] at hm
  have hs := rotation_sphere_integral H (f := fun x => a x ^ 2)
    (ha.pow 2) (x := e i) (by simp)
  have hf := frame_second_moment_bound hg i j hij
  have hdim : 0 ≤ (d : ℝ) - 1 := by
    have hn : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hn' : (1 : ℝ) ≤ d := by exact_mod_cast hn
    linarith
  have hmul := mul_le_mul_of_nonneg_left hm hdim
  have hframe := mul_le_mul_of_nonneg_left hf (show 0 ≤ Real.pi ^ 2 / 4 by positivity)
  dsimp [P] at hmul
  rw [hs] at hmul
  nlinarith only [hmul, hframe]

end Spherical

end LongTails.Proofs.SphereOddMoments
