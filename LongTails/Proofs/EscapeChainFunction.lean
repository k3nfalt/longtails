import LongTails.Proofs.EscapeChainGates
import LongTails.Proofs.EscapeChainCalculus
import LongTails.Proofs.RelativeHessianCutoffSpatial

namespace LongTails.Proofs.EscapeChainFunction

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus RelativeHessianArctan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def strength : ℝ := 2 ^ 24

noncomputable def sqf (t : ℝ) : ℝ := t ^ 2

lemma sqf_contDiff : ContDiff ℝ 3 sqf := by unfold sqf; fun_prop
lemma sqf_hasDerivAt (t : ℝ) : HasDerivAt sqf (2 * t) t := by
  have h := hasDerivAt_pow 2 t
  show HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t
  exact h.congr_deriv (by push_cast; ring)
lemma sqf1_hasDerivAt (t : ℝ) : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
  simpa using (hasDerivAt_id t).const_mul (2 : ℝ)

noncomputable def prevPsi (u : ℕ → E) : ℕ → E → ℝ
  | 0 => fun _ => 1
  | l + 1 => RidgeJets.value psi (u l)

noncomputable def prevGam (u : ℕ → E) : ℕ → E → ℝ
  | 0 => fun _ => 1
  | l + 1 => RidgeJets.value gam (u l)

noncomputable def dPsi (u : ℕ → E) : ℕ → E → E → ℝ
  | 0 => fun _ _ => 0
  | l + 1 => fun x e => psi1 ⟪u l, x⟫ * ⟪u l, e⟫

noncomputable def dGam (u : ℕ → E) : ℕ → E → E → ℝ
  | 0 => fun _ _ => 0
  | l + 1 => fun x e => gam1 ⟪u l, x⟫ * ⟪u l, e⟫

noncomputable def qPsi (u : ℕ → E) : ℕ → E → E → ℝ
  | 0 => fun _ _ => 0
  | l + 1 => fun x e => psi2 ⟪u l, x⟫ * ⟪u l, e⟫ ^ 2

noncomputable def qGam (u : ℕ → E) : ℕ → E → E → ℝ
  | 0 => fun _ _ => 0
  | l + 1 => fun x e => gam2 ⟪u l, x⟫ * ⟪u l, e⟫ ^ 2

noncomputable def link (u v : ℕ → E) (l : ℕ) (x : E) : ℝ :=
  -strength * (RidgeJets.value lam (v l) x * (prevPsi u l x * RidgeJets.value profile (u l) x))

noncomputable def resid (u v : ℕ → E) (l : ℕ) (x : E) : ℝ :=
  FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) x -
    ∑ m ∈ Finset.range l, (RidgeJets.value sqf (u m) x + RidgeJets.value sqf (v m) x)

noncomputable def quarter (u v : ℕ → E) (l : ℕ) (x : E) : ℝ := (1 / 4 : ℝ) * resid u v l x

noncomputable def window (u v : ℕ → E) (l : ℕ) (x : E) : ℝ := loc (quarter u v l x)

noncomputable def saddle (u v : ℕ → E) (l : ℕ) (x : E) : ℝ :=
  prevGam u l x * (RidgeJets.value sad (v l) x * window u v l x)

noncomputable def hidden (K : ℕ) (u v : ℕ → E) (x : E) : ℝ :=
  ∑ l ∈ Finset.range K, (link u v l x + saddle u v l x)

noncomputable def objective (K : ℕ) (R : ℝ) (u v : ℕ → E) (x : E) : ℝ :=
  RelativeHessianCutoffSpatial.value R x * hidden K u v x +
    (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) x

section smooth
omit [CompleteSpace E] [FiniteDimensional ℝ E]

lemma prevPsi_smooth (u : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (prevPsi u l) := by
  cases l with
  | zero => exact contDiff_const
  | succ l => exact RidgeJets.smooth (ag_contDiff 8 (-4)) (u l)

lemma prevGam_smooth (u : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (prevGam u l) := by
  cases l with
  | zero => exact contDiff_const
  | succ l => exact RidgeJets.smooth (ag_contDiff 20 (-12)) (u l)

lemma lamR_smooth (a : E) : ContDiff ℝ 3 (RidgeJets.value lam a) := RidgeJets.smooth lam_contDiff a
lemma phiR_smooth (a : E) : ContDiff ℝ 3 (RidgeJets.value profile a) :=
  RidgeJets.smooth profile_contDiff a
lemma sadR_smooth (a : E) : ContDiff ℝ 3 (RidgeJets.value sad a) := RidgeJets.smooth sad_contDiff a
lemma sqR_smooth (a : E) : ContDiff ℝ 3 (RidgeJets.value sqf a) := RidgeJets.smooth sqf_contDiff a

lemma pair_smooth (u : ℕ → E) (l : ℕ) :
    ContDiff ℝ 3 (fun x => prevPsi u l x * RidgeJets.value profile (u l) x) :=
  (prevPsi_smooth u l).mul (phiR_smooth (u l))

lemma core_smooth (u v : ℕ → E) (l : ℕ) :
    ContDiff ℝ 3 (fun x => RidgeJets.value lam (v l) x *
      (prevPsi u l x * RidgeJets.value profile (u l) x)) :=
  (lamR_smooth (v l)).mul (pair_smooth u l)

lemma link_smooth (u v : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (link u v l) :=
  contDiff_const.mul (core_smooth u v l)

lemma squares_smooth (u v : ℕ → E) (l : ℕ) :
    ContDiff ℝ 3 (fun x => ∑ m ∈ Finset.range l,
      (RidgeJets.value sqf (u m) x + RidgeJets.value sqf (v m) x)) :=
  ContDiff.sum fun m _ => (sqR_smooth (u m)).add (sqR_smooth (v m))

lemma resid_smooth (u v : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (resid u v l) :=
  (RelativeHessianGuard.quadratic_smooth 2).sub (squares_smooth u v l)

lemma quarter_smooth (u v : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (quarter u v l) :=
  contDiff_const.mul (resid_smooth u v l)

lemma window_smooth (u v : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (window u v l) :=
  loc_contDiff.comp (quarter_smooth u v l)

lemma inner_smooth (u v : ℕ → E) (l : ℕ) :
    ContDiff ℝ 3 (fun x => RidgeJets.value sad (v l) x * window u v l x) :=
  (sadR_smooth (v l)).mul (window_smooth u v l)

lemma saddle_smooth (u v : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (saddle u v l) :=
  (prevGam_smooth u l).mul (inner_smooth u v l)

lemma term_smooth (u v : ℕ → E) (l : ℕ) :
    ContDiff ℝ 3 (fun x => link u v l x + saddle u v l x) :=
  (link_smooth u v l).add (saddle_smooth u v l)

lemma hidden_smooth (K : ℕ) (u v : ℕ → E) : ContDiff ℝ 3 (hidden K u v) :=
  ContDiff.sum fun l _ => term_smooth u v l

lemma objective_smooth (K : ℕ) (R : ℝ) (u v : ℕ → E) : ContDiff ℝ 3 (objective K R u v) :=
  ((RelativeHessianCutoffSpatial.smooth R).mul (hidden_smooth K u v)).add
    (contDiff_const.mul (RelativeHessianGuard.quadratic_smooth 2))

end smooth

omit [FiniteDimensional ℝ E] in
lemma D_prevPsi (u : ℕ → E) (l : ℕ) (x e : E) : D (prevPsi u l) x e = dPsi u l x e := by
  cases l with
  | zero => exact D_const 1 x e
  | succ l => exact D_ridge (ag_hasDerivAt 8 (-4)) (u l) x e

omit [FiniteDimensional ℝ E] in
lemma D_prevGam (u : ℕ → E) (l : ℕ) (x e : E) : D (prevGam u l) x e = dGam u l x e := by
  cases l with
  | zero => exact D_const 1 x e
  | succ l => exact D_ridge (ag_hasDerivAt 20 (-12)) (u l) x e

omit [FiniteDimensional ℝ E] in
lemma Q_prevPsi (u : ℕ → E) (l : ℕ) (x e : E) : Q (prevPsi u l) x e = qPsi u l x e := by
  cases l with
  | zero => exact Q_const 1 x e
  | succ l => exact Q_ridge (ag_contDiff 8 (-4)) (ag_hasDerivAt 8 (-4)) (ag1_hasDerivAt 8 (-4)) (u l) x e

omit [FiniteDimensional ℝ E] in
lemma Q_prevGam (u : ℕ → E) (l : ℕ) (x e : E) : Q (prevGam u l) x e = qGam u l x e := by
  cases l with
  | zero => exact Q_const 1 x e
  | succ l =>
    exact Q_ridge (ag_contDiff 20 (-12)) (ag_hasDerivAt 20 (-12)) (ag1_hasDerivAt 20 (-12)) (u l) x e

lemma D_link (u v : ℕ → E) (l : ℕ) (x e : E) :
    D (link u v l) x e = -strength * (lam ⟪v l, x⟫ * (prevPsi u l x * (density ⟪u l, x⟫ * ⟪u l, e⟫) +
      profile ⟪u l, x⟫ * dPsi u l x e) +
      prevPsi u l x * profile ⟪u l, x⟫ * (lam1 ⟪v l, x⟫ * ⟪v l, e⟫)) := by
  have h : link u v l = fun y => -strength * (RidgeJets.value lam (v l) y *
      (prevPsi u l y * RidgeJets.value profile (u l) y)) := rfl
  rw [h, D_const_mul (core_smooth u v l), D_mul (lamR_smooth (v l)) (pair_smooth u l),
    D_mul (prevPsi_smooth u l) (phiR_smooth (u l)), D_ridge lam_hasDerivAt,
    D_ridge profile_derivative, D_prevPsi]
  simp only [RidgeJets.value]

lemma Q_link (u v : ℕ → E) (l : ℕ) (x e : E) :
    Q (link u v l) x e = -strength * (lam ⟪v l, x⟫ * (prevPsi u l x * (densitySlope ⟪u l, x⟫ * ⟪u l, e⟫ ^ 2) +
      2 * (dPsi u l x e * (density ⟪u l, x⟫ * ⟪u l, e⟫)) + profile ⟪u l, x⟫ * qPsi u l x e) +
      2 * ((lam1 ⟪v l, x⟫ * ⟪v l, e⟫) * (prevPsi u l x * (density ⟪u l, x⟫ * ⟪u l, e⟫) +
        profile ⟪u l, x⟫ * dPsi u l x e)) +
      prevPsi u l x * profile ⟪u l, x⟫ * (lam2 ⟪v l, x⟫ * ⟪v l, e⟫ ^ 2)) := by
  have h : link u v l = fun y => -strength * (RidgeJets.value lam (v l) y *
      (prevPsi u l y * RidgeJets.value profile (u l) y)) := rfl
  rw [h, Q_const_mul (core_smooth u v l), Q_mul (lamR_smooth (v l)) (pair_smooth u l),
    D_mul (prevPsi_smooth u l) (phiR_smooth (u l)), Q_mul (prevPsi_smooth u l) (phiR_smooth (u l)),
    D_ridge lam_hasDerivAt, Q_ridge lam_contDiff lam_hasDerivAt lam1_hasDerivAt,
    D_ridge profile_derivative, Q_ridge profile_contDiff profile_derivative density_derivative,
    D_prevPsi, Q_prevPsi]
  simp only [RidgeJets.value]

lemma D_resid (u v : ℕ → E) (l : ℕ) (x e : E) :
    D (resid u v l) x e = 2 * ⟪x, e⟫ -
      ∑ m ∈ Finset.range l, (2 * ⟪u m, x⟫ * ⟪u m, e⟫ + 2 * ⟪v m, x⟫ * ⟪v m, e⟫) := by
  have h : resid u v l = fun y => FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y -
      ∑ m ∈ Finset.range l, (RidgeJets.value sqf (u m) y + RidgeJets.value sqf (v m) y) := rfl
  rw [h, D_sub (RelativeHessianGuard.quadratic_smooth 2) (squares_smooth u v l), D_normsq,
    D_sum _ (fun m _ => (sqR_smooth (u m)).add (sqR_smooth (v m)))]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [D_add (sqR_smooth (u m)) (sqR_smooth (v m)), D_ridge sqf_hasDerivAt, D_ridge sqf_hasDerivAt]

lemma Q_resid (u v : ℕ → E) (l : ℕ) (x e : E) :
    Q (resid u v l) x e = 2 * ‖e‖ ^ 2 -
      ∑ m ∈ Finset.range l, (2 * ⟪u m, e⟫ ^ 2 + 2 * ⟪v m, e⟫ ^ 2) := by
  have h : resid u v l = fun y => FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y -
      ∑ m ∈ Finset.range l, (RidgeJets.value sqf (u m) y + RidgeJets.value sqf (v m) y) := rfl
  rw [h, Q_sub (RelativeHessianGuard.quadratic_smooth 2) (squares_smooth u v l), Q_normsq,
    Q_sum _ (fun m _ => (sqR_smooth (u m)).add (sqR_smooth (v m)))]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Q_add (sqR_smooth (u m)) (sqR_smooth (v m)), Q_ridge sqf_contDiff sqf_hasDerivAt sqf1_hasDerivAt,
    Q_ridge sqf_contDiff sqf_hasDerivAt sqf1_hasDerivAt]

lemma D_window (u v : ℕ → E) (l : ℕ) (x e : E) :
    D (window u v l) x e = loc1 (quarter u v l x) * ((1 / 4 : ℝ) * D (resid u v l) x e) := by
  have h : window u v l = loc ∘ quarter u v l := rfl
  rw [h, D_comp (quarter_smooth u v l) loc_hasDerivAt]
  congr 1
  exact D_const_mul (resid_smooth u v l) _ x e

lemma Q_window (u v : ℕ → E) (l : ℕ) (x e : E) :
    Q (window u v l) x e = loc1 (quarter u v l x) * ((1 / 4 : ℝ) * Q (resid u v l) x e) +
      loc2 (quarter u v l x) * ((1 / 4 : ℝ) * D (resid u v l) x e) ^ 2 := by
  have h : window u v l = loc ∘ quarter u v l := rfl
  have hq : quarter u v l = fun y => (1 / 4 : ℝ) * resid u v l y := rfl
  rw [h, Q_comp (quarter_smooth u v l) loc_contDiff loc_hasDerivAt loc1_hasDerivAt, hq,
    Q_const_mul (resid_smooth u v l), D_const_mul (resid_smooth u v l)]

lemma D_saddle (u v : ℕ → E) (l : ℕ) (x e : E) :
    D (saddle u v l) x e = prevGam u l x * (sad ⟪v l, x⟫ * D (window u v l) x e +
      window u v l x * (sad1 ⟪v l, x⟫ * ⟪v l, e⟫)) +
      sad ⟪v l, x⟫ * window u v l x * dGam u l x e := by
  have h : saddle u v l = fun y => prevGam u l y * (RidgeJets.value sad (v l) y * window u v l y) := rfl
  rw [h, D_mul (prevGam_smooth u l) (inner_smooth u v l),
    D_mul (sadR_smooth (v l)) (window_smooth u v l), D_ridge sad_hasDerivAt, D_prevGam]
  simp only [RidgeJets.value]

lemma Q_saddle (u v : ℕ → E) (l : ℕ) (x e : E) :
    Q (saddle u v l) x e = prevGam u l x * (sad ⟪v l, x⟫ * Q (window u v l) x e +
      2 * ((sad1 ⟪v l, x⟫ * ⟪v l, e⟫) * D (window u v l) x e) +
      window u v l x * (sad2 ⟪v l, x⟫ * ⟪v l, e⟫ ^ 2)) +
      2 * (dGam u l x e * (sad ⟪v l, x⟫ * D (window u v l) x e +
        window u v l x * (sad1 ⟪v l, x⟫ * ⟪v l, e⟫))) +
      sad ⟪v l, x⟫ * window u v l x * qGam u l x e := by
  have h : saddle u v l = fun y => prevGam u l y * (RidgeJets.value sad (v l) y * window u v l y) := rfl
  rw [h, Q_mul (prevGam_smooth u l) (inner_smooth u v l),
    Q_mul (sadR_smooth (v l)) (window_smooth u v l), D_mul (sadR_smooth (v l)) (window_smooth u v l),
    D_ridge sad_hasDerivAt, Q_ridge sad_contDiff sad_hasDerivAt sad1_hasDerivAt, D_prevGam, Q_prevGam]
  simp only [RidgeJets.value]

lemma D_hidden (K : ℕ) (u v : ℕ → E) (x e : E) :
    D (hidden K u v) x e = ∑ l ∈ Finset.range K, (D (link u v l) x e + D (saddle u v l) x e) := by
  have h : hidden K u v = fun y => ∑ l ∈ Finset.range K, (link u v l y + saddle u v l y) := rfl
  rw [h, D_sum _ (fun l _ => term_smooth u v l)]
  exact Finset.sum_congr rfl fun l _ => D_add (link_smooth u v l) (saddle_smooth u v l) x e

lemma Q_hidden (K : ℕ) (u v : ℕ → E) (x e : E) :
    Q (hidden K u v) x e = ∑ l ∈ Finset.range K, (Q (link u v l) x e + Q (saddle u v l) x e) := by
  have h : hidden K u v = fun y => ∑ l ∈ Finset.range K, (link u v l y + saddle u v l y) := rfl
  rw [h, Q_sum _ (fun l _ => term_smooth u v l)]
  exact Finset.sum_congr rfl fun l _ => Q_add (link_smooth u v l) (saddle_smooth u v l) x e

lemma objective_inside (K : ℕ) {R : ℝ} (hR : 0 < R) (u v : ℕ → E) (x : E) (hx : ‖x‖ ≤ R) (e : E) :
    D (objective K R u v) x e = D (hidden K u v) x e + ⟪x, e⟫ ∧
      Q (objective K R u v) x e = Q (hidden K u v) x e + ‖e‖ ^ 2 := by
  obtain ⟨hc, hg, hH, -⟩ := RelativeHessianCutoffSpatial.inside_jets hR x hx
  have h : objective K R u v = fun y => RelativeHessianCutoffSpatial.value R y * hidden K u v y +
      (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y := rfl
  have hp := (RelativeHessianCutoffSpatial.smooth R).mul (hidden_smooth K u v)
  have hq := RelativeHessianGuard.quadratic_smooth (E := E) 2
  constructor
  · rw [h, D_add hp (contDiff_const.mul hq), D_mul (RelativeHessianCutoffSpatial.smooth R)
      (hidden_smooth K u v), D_const_mul hq, D_normsq]
    simp only [D, hc, hg, inner_zero_left]
    ring
  · rw [h, Q_add hp (contDiff_const.mul hq), Q_mul (RelativeHessianCutoffSpatial.smooth R)
      (hidden_smooth K u v), Q_const_mul hq, Q_normsq]
    simp only [Q, D, hc, hg, hH, inner_zero_left, zero_apply]
    ring

end LongTails.Proofs.EscapeChainFunction
