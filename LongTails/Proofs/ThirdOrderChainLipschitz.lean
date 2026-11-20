import LongTails.Proofs.ThirdOrderJetDifference
import LongTails.Proofs.RelativeHessianLocalized

set_option maxRecDepth 2000

namespace LongTails.Proofs.ThirdOrderChainLipschitz

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGate RelativeHessianGeometry
open ThirdOrderJetDifference

section Scalar

lemma lip_of_deriv_bound {f f' : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (f' t) t) {K : ℝ}
    (hK : ∀ t, |f' t| ≤ K) (s t : ℝ) : |f s - f t| ≤ K * |s - t| := by
  have h := (convex_univ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => by simpa using hK z)
    (Set.mem_univ t) (Set.mem_univ s)
  simpa [Real.norm_eq_abs] using h

lemma positivePower_one_lipschitz (s t : ℝ) :
    |positivePower 1 s - positivePower 1 t| ≤ |s - t| := by
  simp only [positivePower, pow_one]
  exact abs_max_sub_max_le_abs s t 0

lemma spline_one_lipschitz (s t : ℝ) : |spline 1 s - spline 1 t| ≤ 16 * |s - t| := by
  have h₀ := positivePower_one_lipschitz s t
  have h₁ := positivePower_one_lipschitz (s - 1) (t - 1)
  have h₂ := positivePower_one_lipschitz (s - 2) (t - 2)
  have h₃ := positivePower_one_lipschitz (s - 3) (t - 3)
  have h₄ := positivePower_one_lipschitz (s - 4) (t - 4)
  rw [show s - 1 - (t - 1) = s - t by ring] at h₁
  rw [show s - 2 - (t - 2) = s - t by ring] at h₂
  rw [show s - 3 - (t - 3) = s - t by ring] at h₃
  rw [show s - 4 - (t - 4) = s - t by ring] at h₄
  have e : spline 1 s - spline 1 t =
      (positivePower 1 s - positivePower 1 t) - 4 * (positivePower 1 (s - 1) - positivePower 1 (t - 1)) +
        6 * (positivePower 1 (s - 2) - positivePower 1 (t - 2)) -
        4 * (positivePower 1 (s - 3) - positivePower 1 (t - 3)) +
        (positivePower 1 (s - 4) - positivePower 1 (t - 4)) := by
    simp only [spline]; ring
  rw [e]
  rw [abs_le] at h₀ h₁ h₂ h₃ h₄ ⊢
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.1, h₄.2]

lemma gateThird_lipschitz (s t : ℝ) : |gateThird s - gateThird t| ≤ 2 ^ 26 * |s - t| := by
  have h := spline_one_lipschitz (40 * s - 4) (40 * t - 4)
  rw [show 40 * s - 4 - (40 * t - 4) = 40 * (s - t) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 40)] at h
  simp only [gateThird]
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 64000)]
  nlinarith [abs_nonneg (s - t)]

lemma gate_lipschitz (s t : ℝ) : |gate s - gate t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound gate_hasDerivAt (fun z => (gate_jet_bounds z).1) s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

lemma gateSlope_lipschitz (s t : ℝ) : |gateSlope s - gateSlope t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound gateSlope_hasDerivAt (fun z => (gate_jet_bounds z).2.1) s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

lemma gateCurvature_lipschitz (s t : ℝ) : |gateCurvature s - gateCurvature t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound gateCurvature_hasDerivAt (fun z => (gate_jet_bounds z).2.2) s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

noncomputable def densityFourth (t : ℝ) : ℝ := (24 * t - 24 * t ^ 3) / (1 + t ^ 2) ^ 4

lemma densityCurvature_derivative (t : ℝ) : HasDerivAt densityCurvature (densityFourth t) t := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  have hnum : HasDerivAt (fun s : ℝ => 6 * s ^ 2 - 2) (12 * t) t := by
    have h := ((hasDerivAt_pow 2 t).const_mul 6).sub_const 2
    have e : (6 : ℝ) * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = 12 * t := by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    rwa [e] at h
  have hden : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ 3) (3 * (1 + t ^ 2) ^ 2 * (2 * t)) t := by
    have h := ((hasDerivAt_pow 2 t).const_add 1).pow 3
    have e : ((3 : ℕ) : ℝ) * (1 + t ^ 2) ^ (3 - 1) * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) =
        3 * (1 + t ^ 2) ^ 2 * (2 * t) := by
      rw [show (3 : ℕ) - 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    rwa [e] at h
  have h := hnum.div hden (pow_ne_zero 3 ht)
  have e : (12 * t * (1 + t ^ 2) ^ 3 - (6 * t ^ 2 - 2) * (3 * (1 + t ^ 2) ^ 2 * (2 * t))) /
      ((1 + t ^ 2) ^ 3) ^ 2 = densityFourth t := by
    unfold densityFourth
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e] at h
  exact h

lemma densityFourth_bound (t : ℝ) : |densityFourth t| ≤ 24 := by
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hu : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  unfold densityFourth
  rw [abs_div, abs_pow, abs_of_pos ht, div_le_iff₀ (pow_pos ht 4)]
  have h4 : (1 + t ^ 2) ^ 2 ≤ (1 + t ^ 2) ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have hab : |24 * t - 24 * t ^ 3| ≤ 24 * (1 + t ^ 2) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1), sq_nonneg (t ^ 2 - t),
      sq_nonneg (t ^ 2 + t), sq_nonneg t, sq_nonneg (t ^ 2)]
  nlinarith

lemma profile_lipschitz (s t : ℝ) : |profile s - profile t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound profile_derivative (fun z => (profile_jet_bounds z).1) s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

lemma density_lipschitz (s t : ℝ) : |density s - density t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound density_derivative (fun z => (profile_jet_bounds z).2.1) s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

lemma densitySlope_lipschitz (s t : ℝ) : |densitySlope s - densitySlope t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound densitySlope_derivative (fun z => (profile_jet_bounds z).2.2) s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

lemma densityCurvature_lipschitz (s t : ℝ) :
    |densityCurvature s - densityCurvature t| ≤ 2 ^ 26 * |s - t| :=
  (lip_of_deriv_bound densityCurvature_derivative densityFourth_bound s t).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

lemma cutoffSecond_lipschitz (s t : ℝ) :
    |RelativeHessianCutoff.second s - RelativeHessianCutoff.second t| ≤ 2 ^ 24 * |s - t| :=
  lip_of_deriv_bound RelativeHessianCutoff.second_derivative
    (fun z => (RelativeHessianCutoff.jet_bounds z).2.2) s t

lemma cutoffThird_lipschitz (s t : ℝ) :
    |RelativeHessianCutoff.third s - RelativeHessianCutoff.third t| ≤ 2 ^ 26 * |s - t| := by
  have h := gateThird_lipschitz ((s + 2) / 30) ((t + 2) / 30)
  rw [show (s + 2) / 30 - (t + 2) / 30 = (s - t) / 30 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 30)] at h
  simp only [RelativeHessianCutoff.third]
  rw [show -gateThird ((s + 2) / 30) / 27000 - -gateThird ((t + 2) / 30) / 27000 =
    -(gateThird ((s + 2) / 30) - gateThird ((t + 2) / 30)) / 27000 by ring, abs_div, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 27000), div_le_iff₀ (by norm_num)]
  have h0 := abs_nonneg (s - t)
  have : 2 ^ 26 * (|s - t| / 30) ≤ 2 ^ 26 * |s - t| * 27000 := by
    have e : (2 : ℝ) ^ 26 * (|s - t| / 30) = 2 ^ 26 / 30 * |s - t| := by ring
    rw [e]
    nlinarith
  linarith

lemma mul_diff (c c' z z' : ℝ) {A B C D : ℝ} (h₁ : |c - c'| ≤ A) (h₂ : |z| ≤ B)
    (h₃ : |c'| ≤ C) (h₄ : |z - z'| ≤ D) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    |c * z - c' * z'| ≤ A * B + C * D := by
  have e : c * z - c' * z' = (c - c') * z + c' * (z - z') := by ring
  rw [e]
  calc _ ≤ |(c - c') * z| + |c' * (z - z')| := abs_add_le _ _
    _ = |c - c'| * |z| + |c'| * |z - z'| := by rw [abs_mul, abs_mul]
    _ ≤ A * B + C * D :=
        add_le_add (mul_le_mul h₁ h₂ (abs_nonneg _) hA) (mul_le_mul h₃ h₄ (abs_nonneg _) hC)

end Scalar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

open RelativeHessianJetBounds (energy)

section Edge

lemma gate_jetBound (a z u v : E) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V) :
    JetBound (RidgeJets.value gate a) z u v (2 ^ 24) (2 ^ 24) (2 ^ 24) (2 ^ 24) U V := by
  have hgate : |gate ⟪a, z⟫| ≤ (2 : ℝ) ^ 24 := by
    rw [abs_of_nonneg (gate_bounds _).1]
    exact (gate_bounds _).2.trans (by norm_num)
  exact ridge_bound gate_contDiff gate_hasDerivAt gateSlope_hasDerivAt gateCurvature_hasDerivAt
    a z u v (by norm_num) hU hV ha hu hv hgate (gate_jet_bounds _).1 (gate_jet_bounds _).2.1
    (gate_jet_bounds _).2.2

lemma profile_jetBound (a z u v : E) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V) :
    JetBound (RidgeJets.value profile a) z u v (2 ^ 24) (2 ^ 24) (2 ^ 24) (2 ^ 24) U V := by
  have hp : |profile ⟪a, z⟫| ≤ (2 : ℝ) ^ 24 := by
    rw [abs_of_pos (profile_bounds _).1]
    exact (profile_bounds _).2.le.trans ((Real.pi_lt_four).le.trans (by norm_num))
  exact ridge_bound profile_contDiff profile_derivative density_derivative densitySlope_derivative
    a z u v (by norm_num) hU hV ha hu hv hp ((profile_jet_bounds _).1.trans (by norm_num))
    ((profile_jet_bounds _).2.1.trans (by norm_num)) ((profile_jet_bounds _).2.2.trans (by norm_num))

lemma gate_jetDiff (a x y u v : E) {U V Z : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V) (hz : |⟪a, x⟫ - ⟪a, y⟫| ≤ Z) :
    JetDiff (RidgeJets.value gate a) x y u v (2 ^ 26) (2 ^ 26) (2 ^ 26) (2 ^ 26) U V Z :=
  ridge_diff gate_contDiff gate_hasDerivAt gateSlope_hasDerivAt gateCurvature_hasDerivAt
    a x y u v (by norm_num) hU hV ha hu hv hz gate_lipschitz gateSlope_lipschitz
    gateCurvature_lipschitz gateThird_lipschitz

lemma profile_jetDiff (a x y u v : E) {U V Z : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : ‖a‖ ≤ 1)
    (hu : |⟪a, u⟫| ≤ U) (hv : |⟪a, v⟫| ≤ V) (hz : |⟪a, x⟫ - ⟪a, y⟫| ≤ Z) :
    JetDiff (RidgeJets.value profile a) x y u v (2 ^ 26) (2 ^ 26) (2 ^ 26) (2 ^ 26) U V Z :=
  ridge_diff profile_contDiff profile_derivative density_derivative densitySlope_derivative
    a x y u v (by norm_num) hU hV ha hu hv hz profile_lipschitz density_lipschitz
    densitySlope_lipschitz densityCurvature_lipschitz

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_nonneg (a b u : E) : 0 ≤ energy a b u := by unfold energy; positivity

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_diff (a b x y : E) :
    |⟪a, x⟫ - ⟪a, y⟫| ≤ energy a b (x - y) ∧ |⟪b, x⟫ - ⟪b, y⟫| ≤ energy a b (x - y) := by
  unfold energy
  rw [inner_sub_right, inner_sub_right]
  exact ⟨le_add_of_nonneg_right (abs_nonneg _), le_add_of_nonneg_left (abs_nonneg _)⟩

lemma product_diff (a b x y u v : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun z =>
        RidgeJets.value gate a z * RidgeJets.value profile b z))) x u v -
      fderiv ℝ (fderiv ℝ (gradient (fun z =>
        RidgeJets.value gate a z * RidgeJets.value profile b z))) y u v‖ ≤
      2 ^ 54 * energy a b (x - y) * energy a b u * energy a b v := by
  have hU := energy_nonneg a b u
  have hV := energy_nonneg a b v
  have hZ := energy_nonneg a b (x - y)
  have hau : |⟪a, u⟫| ≤ energy a b u := le_add_of_nonneg_right (abs_nonneg _)
  have hav : |⟪a, v⟫| ≤ energy a b v := le_add_of_nonneg_right (abs_nonneg _)
  have hbu : |⟪b, u⟫| ≤ energy a b u := le_add_of_nonneg_left (abs_nonneg _)
  have hbv : |⟪b, v⟫| ≤ energy a b v := le_add_of_nonneg_left (abs_nonneg _)
  obtain ⟨hza, hzb⟩ := energy_diff a b x y
  have h := product_third_diff (RidgeJets.smooth gate_contDiff a) (RidgeJets.smooth profile_contDiff b)
    x y u v hU hV hZ ⟨by norm_num, by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num, by norm_num⟩
    (gate_jetBound a x u v hU hV ha hau hav) (gate_jetBound a y u v hU hV ha hau hav)
    (gate_jetDiff a x y u v hU hV ha hau hav hza)
    (profile_jetBound b x u v hU hV hb hbu hbv) (profile_jetBound b y u v hU hV hb hbu hbv)
    (profile_jetDiff b x y u v hU hV hb hbu hbv hzb)
  refine h.trans (le_of_eq ?_)
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_neg (a b u : E) : energy (-a) (-b) u = energy a b u := by
  simp [energy, inner_neg_left]

lemma edge_diff (a b x y u v : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (gradient (edge a b))) x u v -
        fderiv ℝ (fderiv ℝ (gradient (edge a b))) y u v‖ ≤
      2 ^ 55 * energy a b (x - y) * energy a b u * energy a b v := by
  have hp := product_diff a b x y u v ha hb
  have hn := product_diff (-a) (-b) x y u v (by simpa using ha) (by simpa using hb)
  rw [energy_neg, energy_neg, energy_neg] at hn
  have hf := (RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b))
  have hg := (RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b)
  unfold edge
  rw [ThirdOrderAffineCalculus.difference_third hf hg, ThirdOrderAffineCalculus.difference_third hf hg]
  simp only [sub_apply]
  have e : ∀ A B C D : E, A - B - (C - D) = (A - C) - (B - D) := by intros; abel
  rw [e]
  exact (norm_sub_le _ _).trans (by linarith)

lemma edge_hessian_bilinear (a b x u v : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |⟪fderiv ℝ (gradient (edge a b)) x u, v⟫| ≤ 2 ^ 51 * energy a b u * energy a b v := by
  have hU := energy_nonneg a b u
  have hV := energy_nonneg a b v
  have hau : |⟪a, u⟫| ≤ energy a b u := le_add_of_nonneg_right (abs_nonneg _)
  have hav : |⟪a, v⟫| ≤ energy a b v := le_add_of_nonneg_right (abs_nonneg _)
  have hbu : |⟪b, u⟫| ≤ energy a b u := le_add_of_nonneg_left (abs_nonneg _)
  have hbv : |⟪b, v⟫| ≤ energy a b v := le_add_of_nonneg_left (abs_nonneg _)
  have hp := product_hessian_bilinear (RidgeJets.smooth gate_contDiff a)
    (RidgeJets.smooth profile_contDiff b) x u v hU ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (gate_jetBound a x u v hU hV ha hau hav)
    (profile_jetBound b x u v hU hV hb hbu hbv)
  have hna : ‖-a‖ ≤ 1 := by simpa using ha
  have hnb : ‖-b‖ ≤ 1 := by simpa using hb
  have hn := product_hessian_bilinear (RidgeJets.smooth gate_contDiff (-a))
    (RidgeJets.smooth profile_contDiff (-b)) x u v hU ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
    (gate_jetBound (-a) x u v hU hV hna (by simpa [inner_neg_left] using hau)
      (by simpa [inner_neg_left] using hav))
    (profile_jetBound (-b) x u v hU hV hnb (by simpa [inner_neg_left] using hbu)
      (by simpa [inner_neg_left] using hbv))
  have hf := (RidgeJets.smooth gate_contDiff (-a)).mul (RidgeJets.smooth profile_contDiff (-b))
  have hg := (RidgeJets.smooth gate_contDiff a).mul (RidgeJets.smooth profile_contDiff b)
  unfold edge
  rw [ThirdOrderAffineCalculus.difference_hessian hf hg, sub_apply, inner_sub_left]
  refine (abs_sub _ _).trans ((add_le_add hn hp).trans (le_of_eq ?_))
  ring

end Edge

section Chain

variable {m : ℕ}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_le_norm (a b z : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : energy a b z ≤ 2 * ‖z‖ := by
  unfold energy
  have h1 : |⟪a, z⟫| ≤ ‖z‖ := (abs_real_inner_le_norm a z).trans
    (by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg z))
  have h2 : |⟪b, z⟫| ≤ ‖z‖ := (abs_real_inner_le_norm b z).trans
    (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg z))
  linarith

lemma chain_hessian_apply (v : Fin (m + 1) → E) (x u : E) :
    fderiv ℝ (gradient (chain v)) x u =
      -fderiv ℝ (gradient (RidgeJets.value profile (v 0))) x u +
        ∑ i : Fin m, fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ))) x u := by
  have hf := RidgeJets.smooth profile_contDiff (v 0)
  have hg : ContDiff ℝ 3 (fun y => ∑ i : Fin m, edge (v i.castSucc) (v i.succ) y) :=
    ContDiff.sum (fun i _ => edge_smooth _ _)
  have he : chain v = fun y => (-1 : ℝ) * RidgeJets.value profile (v 0) y +
      1 * (∑ i : Fin m, edge (v i.castSucc) (v i.succ) y) := by
    funext y
    simp [chain]
  rw [he, ThirdOrderAffineCalculus.combination_hessian hf hg,
    ThirdOrderAffineCalculus.sum_hessian Finset.univ (fun i _ => edge_smooth _ _)]
  simp

lemma edge_hessian_inner_le (a b x u w : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ⟪fderiv ℝ (gradient (edge a b)) x u, w⟫ ≤ 2 ^ 51 * (energy a b u * energy a b w) := by
  have h := (le_abs_self _).trans (edge_hessian_bilinear a b x u w ha hb)
  linarith

set_option maxHeartbeats 1000000 in
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_sum_le (v : Fin (m + 1) → E) (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (u w : E) :
    ∑ i : Fin m, energy (v i.castSucc) (v i.succ) u * energy (v i.castSucc) (v i.succ) w ≤
      4 * ‖u‖ * ‖w‖ := by
  have ha := RelativeHessianJetBounds.chain_energy v hv u
  have hb := RelativeHessianJetBounds.chain_energy v hv w
  exact SparseTensorBounds.sum_product_bound (κ := 4) (U := ‖u‖) (V := ‖w‖) _ _ (norm_nonneg u)
    (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 4) ha hb

set_option maxHeartbeats 1000000 in
lemma chain_hessian_inner (v : Fin (m + 1) → E) (hn : ∀ i, ‖v i‖ ≤ 1)
    (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (x u w : E) :
    ⟪fderiv ℝ (gradient (chain v)) x u, w⟫ ≤ 2 ^ 54 * ‖u‖ * ‖w‖ := by
  rw [chain_hessian_apply, inner_add_left, inner_neg_left, sum_inner]
  have hr := RidgeJets.hessian_norm profile_contDiff profile_derivative density_derivative
    (v 0) x (by norm_num : (0 : ℝ) ≤ 2) (hn 0) (profile_jet_bounds _).2.1
  have h1 : -⟪fderiv ℝ (gradient (RidgeJets.value profile (v 0))) x u, w⟫ ≤ 2 * ‖u‖ * ‖w‖ := by
    have h := abs_real_inner_le_norm (fderiv ℝ (gradient (RidgeJets.value profile (v 0))) x u) w
    have h' := ((fderiv ℝ (gradient (RidgeJets.value profile (v 0))) x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hr (norm_nonneg u))
    have h'' := mul_le_mul_of_nonneg_right h' (norm_nonneg w)
    linarith [neg_abs_le ⟪fderiv ℝ (gradient (RidgeJets.value profile (v 0))) x u, w⟫]
  have hterm : ∀ i : Fin m, ⟪fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ))) x u, w⟫ ≤
      2 ^ 51 * (energy (v i.castSucc) (v i.succ) u * energy (v i.castSucc) (v i.succ) w) :=
    fun i => edge_hessian_inner_le (v i.castSucc) (v i.succ) x u w (hn _) (hn _)
  have h2 : ∑ i : Fin m, ⟪fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ))) x u, w⟫ ≤
      2 ^ 51 * (4 * ‖u‖ * ‖w‖) := by
    refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (energy_sum_le v hv u w) (by norm_num)
  have hp : 0 ≤ ‖u‖ * ‖w‖ := by positivity
  linarith

lemma chain_hessian_norm (v : Fin (m + 1) → E) (hn : ∀ i, ‖v i‖ ≤ 1)
    (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (x : E) :
    ‖fderiv ℝ (gradient (chain v)) x‖ ≤ 2 ^ 54 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  have h := chain_hessian_inner v hn hv x u (fderiv ℝ (gradient (chain v)) x u)
  rw [real_inner_self_eq_norm_sq, sq] at h
  by_contra hc
  push Not at hc
  have hpos : 0 < ‖fderiv ℝ (gradient (chain v)) x u‖ :=
    lt_of_le_of_lt (by positivity) hc
  have := mul_lt_mul_of_pos_right hc hpos
  linarith

lemma edge_diff_norm (a b x y u w : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (gradient (edge a b))) x u w -
        fderiv ℝ (fderiv ℝ (gradient (edge a b))) y u w‖ ≤
      2 ^ 56 * ‖x - y‖ * (energy a b u * energy a b w) := by
  have h := edge_diff a b x y u w ha hb
  have hz := energy_le_norm a b (x - y) ha hb
  have hUV : 0 ≤ energy a b u * energy a b w := mul_nonneg (energy_nonneg a b u) (energy_nonneg a b w)
  have h2 := mul_le_mul_of_nonneg_right hz hUV
  calc _ ≤ 2 ^ 55 * energy a b (x - y) * energy a b u * energy a b w := h
    _ = 2 ^ 55 * (energy a b (x - y) * (energy a b u * energy a b w)) := by ring
    _ ≤ 2 ^ 55 * (2 * ‖x - y‖ * (energy a b u * energy a b w)) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
lemma chain_third_lipschitz (v : Fin (m + 1) → E) (hn : ∀ i, ‖v i‖ ≤ 1)
    (hv : ∀ u, ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (chain v))) x - fderiv ℝ (fderiv ℝ (gradient (chain v))) y‖ ≤
      2 ^ 59 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [sub_apply, sub_apply, chain_third_apply, chain_third_apply]
  have e : ∀ (A A' : E) (B B' : Fin m → E), -A + ∑ i, B i - (-A' + ∑ i, B' i) =
      -(A - A') + ∑ i, (B i - B' i) := by
    intro A A' B B'
    rw [Finset.sum_sub_distrib]; abel
  rw [e]
  have hin : ∀ z : E, |⟪v 0, z⟫| ≤ ‖z‖ := fun z => (abs_real_inner_le_norm (v 0) z).trans
    (by simpa using mul_le_mul_of_nonneg_right (hn 0) (norm_nonneg z))
  have hz0 : |⟪v 0, x⟫ - ⟪v 0, y⟫| ≤ ‖x - y‖ := by rw [← inner_sub_right]; exact hin _
  have ha := (profile_jetDiff (v 0) x y u w (norm_nonneg u) (norm_nonneg w) (hn 0) (hin u) (hin w)
    hz0).third
  have hterm : ∀ i : Fin m,
      ‖fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) x u w -
        fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) y u w‖ ≤
      2 ^ 56 * ‖x - y‖ * (energy (v i.castSucc) (v i.succ) u * energy (v i.castSucc) (v i.succ) w) :=
    fun i => edge_diff_norm (v i.castSucc) (v i.succ) x y u w (hn _) (hn _)
  have hs : ‖∑ i : Fin m, (fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) x u w -
      fderiv ℝ (fderiv ℝ (gradient (edge (v i.castSucc) (v i.succ)))) y u w)‖ ≤
      2 ^ 56 * ‖x - y‖ * (4 * ‖u‖ * ‖w‖) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hterm i)).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (energy_sum_le v hv u w) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have hp : 0 ≤ ‖x - y‖ * ‖u‖ * ‖w‖ := by positivity
  nlinarith [ha, hs, hp]

end Chain

section Cutoff

open RelativeHessianCutoffSpatial

lemma unit_cutoff_ball (x y : E) (hx : ‖x‖ ≤ 3) (hy : ‖y‖ ≤ 3) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) x -
        fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) y‖ ≤ 2 ^ 37 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [sub_apply, sub_apply, third_apply, third_apply]
  have hκ : (2 / (1 : ℝ) ^ 2) = 2 := by norm_num
  rw [hκ]
  set sx := RelativeHessianCutoff.second (argument 1 x)
  set sy := RelativeHessianCutoff.second (argument 1 y)
  set tx := RelativeHessianCutoff.third (argument 1 x)
  set ty := RelativeHessianCutoff.third (argument 1 y)
  have hq : |argument 1 x - argument 1 y| ≤ 6 * ‖x - y‖ := by
    rw [argument_eq, argument_eq]
    simp only [one_pow, div_one]
    have h1 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
    have e : ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ + ‖y‖)]
    nlinarith [abs_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]
  have hs : |sx - sy| ≤ 2 ^ 24 * (6 * ‖x - y‖) :=
    (cutoffSecond_lipschitz _ _).trans (mul_le_mul_of_nonneg_left hq (by norm_num))
  have ht : |tx - ty| ≤ 2 ^ 26 * (6 * ‖x - y‖) :=
    (cutoffThird_lipschitz _ _).trans (mul_le_mul_of_nonneg_left hq (by norm_num))
  have hsy : |sy| ≤ 2 ^ 24 := (RelativeHessianCutoff.jet_bounds _).2.1
  have hty : |ty| ≤ 2 ^ 24 := (RelativeHessianCutoff.jet_bounds _).2.2
  have hin : ∀ p e : E, ‖p‖ ≤ 3 → |⟪(2 : ℝ) • p, e⟫| ≤ 6 * ‖e‖ := by
    intro p e hp
    rw [real_inner_smul_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := (abs_real_inner_le_norm p e).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg e))
    linarith
  have hid : ∀ e : E, |⟪(2 : ℝ) • x, e⟫ - ⟪(2 : ℝ) • y, e⟫| ≤ 2 * ‖x - y‖ * ‖e‖ := by
    intro e
    rw [← inner_sub_left, ← smul_sub, real_inner_smul_left, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_real_inner_le_norm (x - y) e
    nlinarith
  have huw : |⟪(2 : ℝ) • u, w⟫| ≤ 2 * ‖u‖ * ‖w‖ := by
    rw [real_inner_smul_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_real_inner_le_norm u w
    nlinarith
  have hn2 : ∀ e : E, ‖(2 : ℝ) • e‖ = 2 * ‖e‖ := fun e => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have c₁ : |sx * ⟪(2 : ℝ) • x, u⟫ - sy * ⟪(2 : ℝ) • y, u⟫| ≤
      2 ^ 24 * (6 * ‖x - y‖) * (6 * ‖u‖) + 2 ^ 24 * (2 * ‖x - y‖ * ‖u‖) :=
    mul_diff _ _ _ _ hs (hin x u hx) hsy (hid u) (by positivity) (by norm_num)
  have c₂ : |sx * ⟪(2 : ℝ) • x, w⟫ - sy * ⟪(2 : ℝ) • y, w⟫| ≤
      2 ^ 24 * (6 * ‖x - y‖) * (6 * ‖w‖) + 2 ^ 24 * (2 * ‖x - y‖ * ‖w‖) :=
    mul_diff _ _ _ _ hs (hin x w hx) hsy (hid w) (by positivity) (by norm_num)
  have c₃ : |tx * ⟪(2 : ℝ) • x, u⟫ - ty * ⟪(2 : ℝ) • y, u⟫| ≤
      2 ^ 26 * (6 * ‖x - y‖) * (6 * ‖u‖) + 2 ^ 24 * (2 * ‖x - y‖ * ‖u‖) :=
    mul_diff _ _ _ _ ht (hin x u hx) hty (hid u) (by positivity) (by norm_num)
  have c₃' : |ty * ⟪(2 : ℝ) • y, u⟫| ≤ 2 ^ 24 * (6 * ‖u‖) := by
    rw [abs_mul]; exact mul_le_mul hty (hin y u hy) (abs_nonneg _) (by norm_num)
  have c₄ : |tx * ⟪(2 : ℝ) • x, u⟫ * ⟪(2 : ℝ) • x, w⟫ - ty * ⟪(2 : ℝ) • y, u⟫ * ⟪(2 : ℝ) • y, w⟫| ≤
      (2 ^ 26 * (6 * ‖x - y‖) * (6 * ‖u‖) + 2 ^ 24 * (2 * ‖x - y‖ * ‖u‖)) * (6 * ‖w‖) +
        2 ^ 24 * (6 * ‖u‖) * (2 * ‖x - y‖ * ‖w‖) :=
    mul_diff _ _ _ _ c₃ (hin x w hx) c₃' (hid w) (by positivity) (by positivity)
  have c₅ : |sx * ⟪(2 : ℝ) • u, w⟫ - sy * ⟪(2 : ℝ) • u, w⟫| ≤ 2 ^ 24 * (6 * ‖x - y‖) * (2 * ‖u‖ * ‖w‖) := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul hs huw (abs_nonneg _) (by positivity)
  have c₆ : |tx * ⟪(2 : ℝ) • x, u⟫ * ⟪(2 : ℝ) • x, w⟫ + sx * ⟪(2 : ℝ) • u, w⟫ -
      (ty * ⟪(2 : ℝ) • y, u⟫ * ⟪(2 : ℝ) • y, w⟫ + sy * ⟪(2 : ℝ) • u, w⟫)| ≤
      (2 ^ 26 * (6 * ‖x - y‖) * (6 * ‖u‖) + 2 ^ 24 * (2 * ‖x - y‖ * ‖u‖)) * (6 * ‖w‖) +
        2 ^ 24 * (6 * ‖u‖) * (2 * ‖x - y‖ * ‖w‖) + 2 ^ 24 * (6 * ‖x - y‖) * (2 * ‖u‖ * ‖w‖) := by
    have e : ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) := by intros; ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add c₄ c₅)
  have c₆' : |ty * ⟪(2 : ℝ) • y, u⟫ * ⟪(2 : ℝ) • y, w⟫ + sy * ⟪(2 : ℝ) • u, w⟫| ≤
      2 ^ 24 * (6 * ‖u‖) * (6 * ‖w‖) + 2 ^ 24 * (2 * ‖u‖ * ‖w‖) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul c₃' (hin y w hy) (abs_nonneg _) (by positivity)
    · rw [abs_mul]; exact mul_le_mul hsy huw (abs_nonneg _) (by norm_num)
  have csy : |sy * ⟪(2 : ℝ) • y, u⟫| ≤ 2 ^ 24 * (6 * ‖u‖) := by
    rw [abs_mul]; exact mul_le_mul hsy (hin y u hy) (abs_nonneg _) (by norm_num)
  have csy' : |sy * ⟪(2 : ℝ) • y, w⟫| ≤ 2 ^ 24 * (6 * ‖w‖) := by
    rw [abs_mul]; exact mul_le_mul hsy (hin y w hy) (abs_nonneg _) (by norm_num)
  have t₁ := smul_diff (sx * ⟪(2 : ℝ) • x, u⟫) (sy * ⟪(2 : ℝ) • y, u⟫) ((2 : ℝ) • w) ((2 : ℝ) • w)
    c₁ (hn2 w).le csy (by simp : ‖(2 : ℝ) • w - (2 : ℝ) • w‖ ≤ 0) (by positivity) (by positivity)
  have t₂ := smul_diff (sx * ⟪(2 : ℝ) • x, w⟫) (sy * ⟪(2 : ℝ) • y, w⟫) ((2 : ℝ) • u) ((2 : ℝ) • u)
    c₂ (hn2 u).le csy' (by simp : ‖(2 : ℝ) • u - (2 : ℝ) • u‖ ≤ 0) (by positivity) (by positivity)
  have hzx : ‖(2 : ℝ) • x‖ ≤ 6 := by rw [hn2]; linarith
  have hzd : ‖(2 : ℝ) • x - (2 : ℝ) • y‖ ≤ 2 * ‖x - y‖ := by rw [← smul_sub, hn2]
  have t₃ := smul_diff _ _ ((2 : ℝ) • x) ((2 : ℝ) • y) c₆ hzx c₆' hzd (by positivity) (by positivity)
  have e : ∀ A₁ A₂ A₃ B₁ B₂ B₃ : E, A₁ + A₂ + A₃ - (B₁ + B₂ + B₃) =
      (A₁ - B₁) + (A₂ - B₂) + (A₃ - B₃) := by intros; abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  have hP : 0 ≤ ‖x - y‖ * ‖u‖ * ‖w‖ := by positivity
  nlinarith [t₁, t₂, t₃, hP]

lemma unit_cutoff_lipschitz (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) x -
        fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) y‖ ≤ 2 ^ 37 * ‖x - y‖ := by
  have hz : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 := @norm_zero (E →L[ℝ] E →L[ℝ] E) _
  have far : ∀ p q : E, 3 < ‖p‖ →
      ‖fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) q‖ ≤ 2 ^ 37 * ‖p - q‖ := by
    intro p q hp
    by_cases hq : 2 ≤ ‖q‖
    · rw [(outside_jets one_pos q (by simpa using hq)).2.2.2, hz]; positivity
    · push Not at hq
      have hb := (RelativeHessianCutoffBounds.bounds (E := E) one_pos q).2.2
      have hd : 1 ≤ ‖p - q‖ := by
        have := norm_sub_norm_le p q
        linarith
      calc _ ≤ (2 : ℝ) ^ 32 / 1 ^ 3 := hb
        _ ≤ 2 ^ 37 * ‖p - q‖ := by norm_num; nlinarith
  by_cases hx : ‖x‖ ≤ 3
  · by_cases hy : ‖y‖ ≤ 3
    · exact unit_cutoff_ball x y hx hy
    · push Not at hy
      rw [(outside_jets one_pos y (by linarith)).2.2.2, sub_zero, norm_sub_rev]
      exact far y x hy
  · push Not at hx
    have hTx := (outside_jets (E := E) one_pos x (by linarith)).2.2.2
    refine (norm_sub_le (fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) x)
      (fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) y)).trans ?_
    rw [hTx, hz, zero_add]
    exact far x y hx

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma value_scale (R : ℝ) :
    value (E := E) R = fun x => 1 * value 1 ((1 / R) • x) := by
  funext x
  simp only [value, Function.comp_apply, argument_eq, one_mul, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, one_pow, div_one]
  congr 1
  ring

lemma cutoff_scaled_third (R : ℝ) (z : E) :
    fderiv ℝ (fderiv ℝ (gradient (value (E := E) R))) z =
      (1 * (1 / R) ^ 3) • fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) ((1 / R) • z) := by
  have h := ThirdOrderAffineCalculus.scale_third (smooth (E := E) 1) 1 (1 / R) z
  rw [← value_scale R] at h
  exact h

lemma cutoff_third_lipschitz {R : ℝ} (hR : 0 < R) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value (E := E) R))) x -
        fderiv ℝ (fderiv ℝ (gradient (value (E := E) R))) y‖ ≤ 2 ^ 37 / R ^ 4 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [sub_apply, sub_apply, cutoff_scaled_third R x, cutoff_scaled_third R y]
  simp only [smul_apply]
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 * (1 / R) ^ 3)]
  have h := unit_cutoff_lipschitz ((1 / R) • x) ((1 / R) • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / R)] at h
  have h1 := ((fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) ((1 / R) • x) -
    fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) ((1 / R) • y)) u).le_opNorm w
  have h2 := (fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) ((1 / R) • x) -
    fderiv ℝ (fderiv ℝ (gradient (value (E := E) 1))) ((1 / R) • y)).le_opNorm u
  rw [sub_apply, sub_apply] at h1
  rw [sub_apply] at h2
  have h3 := h1.trans (mul_le_mul_of_nonneg_right
    (h2.trans (mul_le_mul_of_nonneg_right h (norm_nonneg u))) (norm_nonneg w))
  calc _ ≤ 1 * (1 / R) ^ 3 * (2 ^ 37 * (1 / R * ‖x - y‖) * ‖u‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end Cutoff

section Value

open RelativeHessianLocalized

variable {m : ℕ} {v : Fin (m + 1) → E}

lemma radius_facts (m : ℕ) : (1 : ℝ) ≤ radius m ∧ (2 : ℝ) ^ 37 * (m + 1 : ℕ) ≤ radius m := by
  have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  unfold radius
  constructor <;> nlinarith

lemma cutoff_small (m : ℕ) (x : E) :
    |RelativeHessianCutoffSpatial.value (radius m) x| ≤ 1 ∧
    ‖gradient (RelativeHessianCutoffSpatial.value (radius m)) x‖ ≤ 1 / (m + 1 : ℕ) ∧
    ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius m))) x‖ ≤ 1 / (m + 1 : ℕ) ∧
    ‖fderiv ℝ (fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius m)))) x‖ ≤
      1 / (m + 1 : ℕ) ∧ (2 : ℝ) ^ 37 / radius m ^ 4 ≤ 1 / (m + 1 : ℕ) := by
  obtain ⟨hR1, hRN⟩ := radius_facts m
  have hR := radius_pos m
  have hN : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  obtain ⟨h1, h2, h3⟩ := RelativeHessianCutoffBounds.bounds (E := E) hR x
  have hval : |RelativeHessianCutoffSpatial.value (radius m) x| ≤ 1 := by
    have h := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius m) x)
    exact (abs_of_nonneg h.1).trans_le h.2
  have k : ∀ j : ℕ, 1 ≤ j → (2 : ℝ) ^ 37 / radius m ^ j ≤ 1 / (m + 1 : ℕ) := by
    intro j hj
    rw [div_le_div_iff₀ (pow_pos hR j) hN, one_mul]
    have hpow : radius m ≤ radius m ^ j := le_self_pow₀ hR1 (by omega)
    linarith
  have k' : ∀ j : ℕ, 1 ≤ j → (2 : ℝ) ^ 32 / radius m ^ j ≤ 1 / (m + 1 : ℕ) := by
    intro j hj
    refine le_trans ?_ (k j hj)
    exact div_le_div_of_nonneg_right (by norm_num) (pow_pos hR j).le
  refine ⟨hval, ?_, h2.trans (k' 2 (by norm_num)), h3.trans (k' 3 (by norm_num)), k 4 (by norm_num)⟩
  have := k' 1 (by norm_num)
  rw [pow_one] at this
  exact h1.trans this

lemma value_third_lipschitz (hv : Orthonormal ℝ v) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value v))) x - fderiv ℝ (fderiv ℝ (gradient (value v))) y‖ ≤
      2 ^ 60 * ‖x - y‖ := by
  rw [third_eq, third_eq]
  have hN : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  have hn : ∀ i, ‖v i‖ ≤ 1 := fun i => (hv.norm_eq_one i).le
  have hbes := RelativeHessianGuard.bessel hv
  have hcut := cutoff_small (E := E) m
  have key := product_third_lipschitz (RelativeHessianCutoffSpatial.smooth (radius m)) (chain_smooth v)
    x y (a₀ := 1) (a₁ := 1 / (m + 1 : ℕ)) (a₂ := 1 / (m + 1 : ℕ)) (a₃ := 1 / (m + 1 : ℕ))
    (p₃ := 1 / (m + 1 : ℕ)) (b₀ := 4 * (m + 1 : ℕ)) (b₁ := 2 ^ 52 * (m + 1 : ℕ)) (b₂ := 2 ^ 54)
    (b₃ := 2 ^ 55) (q₃ := 2 ^ 59)
    ⟨by norm_num, by positivity, by positivity, by positivity⟩
    ⟨by positivity, by positivity, by norm_num, by norm_num⟩ (by positivity) (by norm_num)
    (fun z => (hcut z).1) (fun z => (hcut z).2.1) (fun z => (hcut z).2.2.1)
    (fun z => (hcut z).2.2.2.1)
    ((cutoff_third_lipschitz (radius_pos m) x y).trans
      (mul_le_mul_of_nonneg_right (hcut x).2.2.2.2 (norm_nonneg _)))
    (fun z => RelativeHessianChainBounds.value_bound v z)
    (fun z => RelativeHessianChainBounds.gradient_bound v hn z)
    (fun z => chain_hessian_norm v hn hbes z)
    (fun z => RelativeHessianJetBounds.chain_bound v hn hbes z)
    (chain_third_lipschitz v hn hbes x y)
  change ‖fderiv ℝ (fderiv ℝ (gradient (perturbation v))) x -
    fderiv ℝ (fderiv ℝ (gradient (perturbation v))) y‖ ≤ _ at key
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have e1 : (1 : ℝ) / (m + 1 : ℕ) * (2 ^ 52 * (m + 1 : ℕ)) = 2 ^ 52 := by field_simp
  have e2 : (2 : ℝ) ^ 52 * (m + 1 : ℕ) * (1 / (m + 1 : ℕ)) = 2 ^ 52 := by field_simp
  have e3 : (4 : ℝ) * (m + 1 : ℕ) * (1 / (m + 1 : ℕ)) = 4 := by field_simp
  have hle : (1 : ℝ) / (m + 1 : ℕ) ≤ 1 := by
    rw [div_le_one hN]; exact_mod_cast Nat.succ_pos m
  have h0 : (0 : ℝ) ≤ 1 / (m + 1 : ℕ) := by positivity
  rw [e1, e2, e3]
  nlinarith

lemma value_hessian_norm (hv : Orthonormal ℝ v) (x : E) :
    ‖fderiv ℝ (gradient (value v)) x‖ ≤ 2 ^ 55 := by
  have hN : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  have hn : ∀ i, ‖v i‖ ≤ 1 := fun i => (hv.norm_eq_one i).le
  have hbes := RelativeHessianGuard.bessel hv
  obtain ⟨hc0, hc1, hc2, -, -⟩ := cutoff_small (E := E) m x
  have hq : fderiv ℝ (gradient (FullGeneralizedSmoothZeroQuery.quadratic coefficient (0 : E))) x =
      coefficient • ContinuousLinearMap.id ℝ E := by
    have hg : gradient (FullGeneralizedSmoothZeroQuery.quadratic coefficient (0 : E)) =
        fun y => coefficient • y := funext (RelativeHessianGuard.quadratic_gradient coefficient)
    rw [hg]
    exact ((hasFDerivAt_id x).const_smul coefficient).fderiv
  have he : fderiv ℝ (gradient (value v)) x =
      fderiv ℝ (gradient (perturbation v)) x + coefficient • ContinuousLinearMap.id ℝ E := by
    unfold value
    have h := ThirdOrderAffineCalculus.combination_hessian (perturbation_smooth v)
      (RelativeHessianGuard.quadratic_smooth coefficient) 1 1 x
    simpa only [one_mul, one_smul, hq] using h
  have hp := product_hessian_norm (RelativeHessianCutoffSpatial.smooth (radius m)) (chain_smooth v) x
  change ‖fderiv ℝ (gradient (perturbation v)) x‖ ≤ _ at hp
  have hC0 := RelativeHessianChainBounds.value_bound v x
  have hC1 := RelativeHessianChainBounds.gradient_bound v hn x
  have hC2 := chain_hessian_norm v hn hbes x
  have hco : coefficient ≤ 13 / 10 := by
    have h3 : Real.sqrt 3 ≤ 26 / 15 := by
      have := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ (26 / 15) ^ 2 by norm_num)
      rwa [Real.sqrt_sq (by norm_num)] at this
    unfold coefficient
    linarith
  have hco0 : 0 ≤ coefficient := by linarith [balance_parameters.1]
  have hid : ‖coefficient • ContinuousLinearMap.id ℝ E‖ ≤ 13 / 10 := by
    refine (ThirdOrderAffineCalculus.norm_smul_operator_le _ _).trans ?_
    rw [abs_of_nonneg hco0]
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
    nlinarith
  rw [he]
  refine (norm_add_le _ _).trans ?_
  have t1 : |RelativeHessianCutoffSpatial.value (radius m) x| * ‖fderiv ℝ (gradient (chain v)) x‖ ≤
      1 * 2 ^ 54 := mul_le_mul hc0 hC2 (norm_nonneg _) (by norm_num)
  have t2 : 2 * ‖gradient (RelativeHessianCutoffSpatial.value (radius m)) x‖ * ‖gradient (chain v) x‖ ≤
      2 * (1 / (m + 1 : ℕ)) * (2 ^ 52 * (m + 1 : ℕ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by norm_num)) hC1 (norm_nonneg _) (by positivity)
  have t3 : |chain v x| * ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius m))) x‖ ≤
      4 * (m + 1 : ℕ) * (1 / (m + 1 : ℕ)) := mul_le_mul hC0 hc2 (norm_nonneg _) (by positivity)
  have e2 : (2 : ℝ) * (1 / (m + 1 : ℕ)) * (2 ^ 52 * (m + 1 : ℕ)) = 2 ^ 53 := by field_simp
  have e3 : (4 : ℝ) * (m + 1 : ℕ) * (1 / (m + 1 : ℕ)) = 4 := by field_simp
  rw [e2] at t2
  rw [e3] at t3
  linarith

lemma value_gradient_lipschitz (hv : Orthonormal ℝ v) (x y : E) :
    ‖gradient (value v) x - gradient (value v) y‖ ≤ 2 ^ 55 * ‖x - y‖ :=
  lipschitz_of_bound (LongTails.Proofs.GradientDependentLocal.derivative_chain (smooth v)).2.1
    (value_hessian_norm hv) x y

lemma value_hessian_lipschitz (hv : Orthonormal ℝ v) (x y : E) :
    ‖fderiv ℝ (gradient (value v)) x - fderiv ℝ (gradient (value v)) y‖ ≤ 2 ^ 56 * ‖x - y‖ :=
  lipschitz_of_bound (LongTails.Proofs.GradientDependentLocal.derivative_chain (smooth v)).2.2
    (absolute_third hv) x y

end Value

end LongTails.Proofs.ThirdOrderChainLipschitz
