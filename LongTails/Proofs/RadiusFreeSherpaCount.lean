import LongTails.Proofs.RadiusFreeSherpaBasic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

noncomputable def theta (q : ℝ) : ℝ := Real.sqrt (1 + q)

noncomputable def aMin (L0 q : ℝ) : ℝ := Real.exp (-(theta q) - 1) / (7 * L0)

noncomputable def lnm (L0 q A : ℝ) : ℝ := Real.log (max A (aMin L0 q)) - Real.log (aMin L0 q)

noncomputable def ind (L0 q A : ℝ) : ℝ := if aMin L0 q ≤ A then 1 else 0

noncomputable def omega (L0 L1 q A S : ℝ) : ℝ :=
  L1 ^ 2 / theta q ^ 2 * S + 2 * Real.sqrt 14 * Real.sqrt (L0 * A) + 14 * theta q * lnm L0 q A

lemma theta_pos {q : ℝ} (hq : 0 ≤ q) : 0 < theta q := Real.sqrt_pos.mpr (by linarith)

lemma theta_sq {q : ℝ} (hq : 0 ≤ q) : theta q ^ 2 = 1 + q := Real.sq_sqrt (by linarith)

lemma theta_ge_one {q : ℝ} (hq : 0 ≤ q) : 1 ≤ theta q := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by linarith)

lemma aMin_pos {L0 q : ℝ} (hL0 : 0 < L0) : 0 < aMin L0 q := by
  unfold aMin; positivity

lemma lnm_nonneg {L0 q A : ℝ} (hL0 : 0 < L0) : 0 ≤ lnm L0 q A := by
  unfold lnm
  have := aMin_pos (q := q) hL0
  exact sub_nonneg.mpr (Real.log_le_log this (le_max_right _ _))

lemma lnm_mono {L0 q A B : ℝ} (hL0 : 0 < L0) (hAB : A ≤ B) : lnm L0 q A ≤ lnm L0 q B := by
  unfold lnm
  have := aMin_pos (q := q) hL0
  have h1 : 0 < max A (aMin L0 q) := lt_of_lt_of_le this (le_max_right _ _)
  exact sub_le_sub_right (Real.log_le_log h1 (max_le_max hAB le_rfl)) _

lemma ind_mono {L0 q A B : ℝ} (hAB : A ≤ B) : ind L0 q A ≤ ind L0 q B := by
  unfold ind
  split_ifs with h1 h2 <;> norm_num
  exact h2 (h1.trans hAB)

lemma ind_nonneg {L0 q A : ℝ} : 0 ≤ ind L0 q A := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one {L0 q A : ℝ} : ind L0 q A ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma log_ratio_ge {a A : ℝ} (ha : 0 < a) (haA : a < A) :
    a / A ≤ Real.log A - Real.log (A - a) := by
  have hA : 0 < A := by linarith
  have hAa : 0 < A - a := by linarith
  rw [← Real.log_div hA.ne' hAa.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hAa hA)
  rw [Real.log_div hAa.ne' hA.ne'] at h
  have : (A - a) / A - 1 = -(a / A) := by field_simp; ring
  rw [this] at h
  have h2 : Real.log (A / (A - a)) = Real.log A - Real.log (A - a) := Real.log_div hA.ne' hAa.ne'
  rw [h2]
  linarith

set_option maxHeartbeats 1000000 in
lemma iteration_increment {L0 L1 q A S G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hq : 0 ≤ q)
    (hA : 0 ≤ A) (hG : 0 < G) :
    omega L0 L1 q A S + ind L0 q A + 1 ≤
      omega L0 L1 q (A + weight L0 L1 A G) (S + weight L0 L1 A G ^ 2 * G ^ 2) +
        ind L0 q (A + weight L0 L1 A G) := by
  set θ := theta q with hθdef
  have hθ : 0 < θ := theta_pos hq
  have hθ1 : 1 ≤ θ := theta_ge_one hq
  set a := weight L0 L1 A G with ha
  set L := localCurvature L0 L1 G with hLdef
  set φ := phiRatio L0 L1 G with hφdef
  have hL : 0 < L := localCurvature_pos hL0 hL1.le hG.le
  have hapos : 0 < a := weight_pos A hL0 hL1 hG
  have haeq : a ^ 2 = (A + a) / (7 * L) + a * φ := weight_eq hL0 hL1 hA hG
  have hφ0 : 0 ≤ φ := phiRatio_nonneg hL0 hL1 hG
  have hsq : (A + a) / (7 * L) ≤ a ^ 2 := weight_sq_ge hL0 hL1 hA hG
  have hA' : 0 < A + a := by linarith
  have hsqrt_mono : Real.sqrt (L0 * A) ≤ Real.sqrt (L0 * (A + a)) :=
    Real.sqrt_le_sqrt (by have := mul_pos hL0 hapos; linarith only [this])
  have hlnm_mono : lnm L0 q A ≤ lnm L0 q (A + a) := lnm_mono hL0 (by linarith)
  have hind_mono : ind L0 q A ≤ ind L0 q (A + a) := ind_mono (by linarith)
  have hS_inc : L1 ^ 2 / θ ^ 2 * S ≤ L1 ^ 2 / θ ^ 2 * (S + a ^ 2 * G ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [sq_nonneg (a * G)]
  show L1 ^ 2 / θ ^ 2 * S + 2 * Real.sqrt 14 * Real.sqrt (L0 * A) + 14 * θ * lnm L0 q A +
      ind L0 q A + 1 ≤
    L1 ^ 2 / θ ^ 2 * (S + a ^ 2 * G ^ 2) + 2 * Real.sqrt 14 * Real.sqrt (L0 * (A + a)) +
      14 * θ * lnm L0 q (A + a) + ind L0 q (A + a)
  by_cases hJ : θ ≤ L1 * a * G
  ·
    have : 1 ≤ L1 ^ 2 / θ ^ 2 * (a ^ 2 * G ^ 2) := by
      rw [show L1 ^ 2 / θ ^ 2 * (a ^ 2 * G ^ 2) = (L1 * a * G / θ) ^ 2 by ring]
      have : 1 ≤ L1 * a * G / θ := by rw [le_div_iff₀ hθ]; linarith only [hJ]
      exact one_le_pow₀ this
    have hpos14 : 0 ≤ 14 * θ := by positivity
    have hlnm_term := mul_le_mul_of_nonneg_left hlnm_mono hpos14
    have hsqrt_term := mul_le_mul_of_nonneg_left hsqrt_mono (by positivity : (0:ℝ) ≤ 2 * Real.sqrt 14)
    have e : L1 ^ 2 / θ ^ 2 * (S + a ^ 2 * G ^ 2) =
        L1 ^ 2 / θ ^ 2 * S + L1 ^ 2 / θ ^ 2 * (a ^ 2 * G ^ 2) := by ring
    rw [e]
    linarith only [this, hlnm_term, hsqrt_term, hind_mono]
  · push Not at hJ
    by_cases hβ : L1 * G < L0
    ·
      have hL2 : L < 2 * L0 := by unfold localCurvature at hLdef; rw [hLdef]; linarith only [hβ]
      have hA14 : (A + a) / (14 * L0) ≤ a ^ 2 := by
        calc (A + a) / (14 * L0) ≤ (A + a) / (7 * L) := by
              apply div_le_div_of_nonneg_left hA'.le (by positivity) (by linarith)
          _ ≤ a ^ 2 := hsq
      have h14 : 0 < Real.sqrt 14 := by positivity
      have hsq14 : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)
      have hs1 : 1 / (2 * Real.sqrt 14) ≤ Real.sqrt (L0 * (A + a)) - Real.sqrt (L0 * A) := by
        set sp := Real.sqrt (L0 * (A + a)) with hsp
        set sm := Real.sqrt (L0 * A) with hsm
        have hsm0 : 0 ≤ sm := Real.sqrt_nonneg _
        have hsp0 : 0 < sp := Real.sqrt_pos.mpr (by positivity)
        have e1 : sp ^ 2 = L0 * (A + a) := by rw [hsp]; exact Real.sq_sqrt (by positivity)
        have e2 : sm ^ 2 = L0 * A := by rw [hsm]; exact Real.sq_sqrt (by positivity)
        have hdiff : (sp - sm) * (sp + sm) = L0 * a := by linear_combination e1 - e2
        have hle : sm ≤ sp := hsqrt_mono
        have hbound : sp ≤ Real.sqrt 14 * L0 * a := by
          rw [hsp, show Real.sqrt 14 * L0 * a = Real.sqrt ((Real.sqrt 14 * L0 * a) ^ 2) from
            (Real.sqrt_sq (by positivity)).symm]
          apply Real.sqrt_le_sqrt
          have e : (Real.sqrt 14 * L0 * a) ^ 2 = 14 * L0 * (L0 * a ^ 2) := by
            linear_combination (L0 ^ 2 * a ^ 2) * hsq14
          rw [e]
          have h1 : A + a ≤ 14 * L0 * a ^ 2 := by
            have := hA14
            rw [div_le_iff₀ (by positivity)] at this
            linarith
          have := mul_le_mul_of_nonneg_left h1 hL0.le
          linarith only [this]
        have hsum : sp + sm ≤ 2 * Real.sqrt 14 * L0 * a := by linarith
        have hd0 : 0 ≤ sp - sm := by linarith
        have hLa : 0 < L0 * a := by positivity
        have hprod : L0 * a ≤ (sp - sm) * (2 * Real.sqrt 14 * L0 * a) := by
          calc L0 * a = (sp - sm) * (sp + sm) := hdiff.symm
            _ ≤ (sp - sm) * (2 * Real.sqrt 14 * L0 * a) := mul_le_mul_of_nonneg_left hsum hd0
        rw [div_le_iff₀ (by positivity)]
        have h5 : (L0 * a) * 1 ≤ (L0 * a) * ((sp - sm) * (2 * Real.sqrt 14)) := by
          calc (L0 * a) * 1 = L0 * a := mul_one _
            _ ≤ (sp - sm) * (2 * Real.sqrt 14 * L0 * a) := hprod
            _ = (L0 * a) * ((sp - sm) * (2 * Real.sqrt 14)) := by ring
        exact le_of_mul_le_mul_left h5 hLa
      have hpos14 : 0 ≤ 14 * θ := by positivity
      have hlnm_term := mul_le_mul_of_nonneg_left hlnm_mono hpos14
      have hterm : 2 * Real.sqrt 14 * Real.sqrt (L0 * A) + 1 ≤ 2 * Real.sqrt 14 * Real.sqrt (L0 * (A + a)) := by
        have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0:ℝ) ≤ 2 * Real.sqrt 14)
        have h2 : 2 * Real.sqrt 14 * (1 / (2 * Real.sqrt 14)) = 1 := by field_simp
        linarith only [this, h2]
      linarith only [hS_inc, hterm, hlnm_term, hind_mono]
    · push Not at hβ
      have hGL : 1 / 2 ≤ L1 * G / L := by
        rw [le_div_iff₀ hL]
        unfold localCurvature at hLdef; rw [hLdef]; linarith only [hβ]
      have hid : L1 * a * G = L1 * φ * G + (A + a) / (7 * a) * (L1 * G / L) := by
        have hX : (A + a) / (7 * L) = a ^ 2 - a * φ := by linarith [haeq]
        have e : (A + a) / (7 * a) * (L1 * G / L) = (A + a) / (7 * L) * (L1 * G / a) := by ring
        rw [e, hX, show (a ^ 2 - a * φ) * (L1 * G / a) = (a - φ) * (L1 * G) * (a / a) by ring,
          div_self hapos.ne', mul_one]
        ring
      have hnn : 0 ≤ (A + a) / (7 * a) * (L1 * G / L) := by positivity
      have hφG : 0 ≤ L1 * φ * G := by positivity
      have hratio : (A + a) / (14 * a) ≤ L1 * a * G := by
        have := mul_le_mul_of_nonneg_left hGL (by positivity : 0 ≤ (A + a) / (7 * a))
        have e : (A + a) / (7 * a) * (1 / 2) = (A + a) / (14 * a) := by ring
        linarith only [this, e, hid, hφG]
      have hfrac : 1 / (14 * θ) < a / (A + a) := by
        rw [div_lt_div_iff₀ (by positivity) hA']
        have := hratio
        rw [div_le_iff₀ (by positivity)] at this
        have h14a : 0 < 14 * a := by linarith only [hapos]
        calc 1 * (A + a) = A + a := one_mul _
          _ ≤ L1 * a * G * (14 * a) := this
          _ < θ * (14 * a) := mul_lt_mul_of_pos_right hJ h14a
          _ = a * (14 * θ) := by ring
      have hA_lower : 1 / (7 * L) ≤ A + a := by
        have h1 : a ≤ A + a := by linarith
        have h2 : (A + a) / (7 * L) ≤ (A + a) ^ 2 :=
          hsq.trans (pow_le_pow_left₀ hapos.le h1 2)
        have h2' : A + a ≤ (A + a) ^ 2 * (7 * L) := by rwa [div_le_iff₀ (by positivity)] at h2
        rw [div_le_iff₀ (by positivity)]
        have h3 : (A + a) * 1 ≤ (A + a) * ((A + a) * (7 * L)) := by
          calc (A + a) * 1 = A + a := mul_one _
            _ ≤ (A + a) ^ 2 * (7 * L) := h2'
            _ = (A + a) * ((A + a) * (7 * L)) := by ring
        exact le_of_mul_le_mul_left h3 hA'
      have hlogL : Real.log (1 + L1 * G / L0) < θ + 1 := by
        have h1 := phi_log_lower hL0 hL1 hG
        rw [← hφdef] at h1
        have h2 : L1 * φ * G ≤ L1 * a * G := by linarith only [hid, hnn]
        linarith only [h1, h2, hJ]
      have hLexp : L < L0 * Real.exp (θ + 1) := by
        have hpos : 0 < 1 + L1 * G / L0 := by positivity
        have := Real.exp_log hpos
        have h3 : 1 + L1 * G / L0 < Real.exp (θ + 1) := by
          rw [← this]; exact Real.exp_lt_exp.mpr hlogL
        have e : 1 + L1 * G / L0 = L / L0 := by
          rw [hLdef]; unfold localCurvature; rw [add_div, div_self hL0.ne']
        rw [e, div_lt_iff₀ hL0] at h3
        linarith
      have hAmin : aMin L0 q < A + a := by
        unfold aMin
        rw [← hθdef]
        calc Real.exp (-θ - 1) / (7 * L0) = 1 / (7 * (L0 * Real.exp (θ + 1))) := by
              rw [show -θ - 1 = -(θ + 1) by ring, Real.exp_neg]
              field_simp
          _ < 1 / (7 * L) := by
              apply div_lt_div_of_pos_left one_pos (by linarith only [hL])
              linarith only [hLexp]
          _ ≤ A + a := hA_lower
      have hindA' : ind L0 q (A + a) = 1 := by simp [ind, hAmin.le]
      have hsqrt_term := mul_le_mul_of_nonneg_left hsqrt_mono (by positivity : (0:ℝ) ≤ 2 * Real.sqrt 14)
      by_cases hprev : aMin L0 q ≤ A
      ·
        have hindA : ind L0 q A = 1 := by simp [ind, hprev]
        have hApos : 0 < A := lt_of_lt_of_le (aMin_pos hL0) hprev
        have hlnm_inc : a / (A + a) ≤ lnm L0 q (A + a) - lnm L0 q A := by
          unfold lnm
          rw [max_eq_left hAmin.le, max_eq_left hprev]
          have := log_ratio_ge hapos (show a < A + a by linarith)
          rw [show A + a - a = A by ring] at this
          linarith only [this]
        have h14 : 1 ≤ 14 * θ * (lnm L0 q (A + a) - lnm L0 q A) := by
          have := mul_le_mul_of_nonneg_left hlnm_inc (by positivity : (0:ℝ) ≤ 14 * θ)
          have h2 : 14 * θ * (1 / (14 * θ)) = 1 := by field_simp
          have h3 := mul_le_mul_of_nonneg_left hfrac.le (by positivity : (0:ℝ) ≤ 14 * θ)
          linarith only [this, h2, h3]
        rw [hindA, hindA']
        linarith only [hS_inc, hsqrt_term, h14]
      · push Not at hprev
        have hindA : ind L0 q A = 0 := by simp [ind, not_le.mpr hprev]
        have hpos14 : 0 ≤ 14 * θ := by positivity
        have hlnm_term := mul_le_mul_of_nonneg_left hlnm_mono hpos14
        rw [hindA, hindA']
        linarith only [hS_inc, hsqrt_term, hlnm_term]

end OracleTemplate.RadiusFreeSherpa
