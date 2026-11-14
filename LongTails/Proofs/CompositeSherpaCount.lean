import LongTails.Proofs.CompositeSherpaBasic
import LongTails.Proofs.RadiusFreeSherpaCount

open Set

namespace OracleTemplate.CompositeSherpa

open RadiusFreeSherpa (theta theta_pos theta_sq theta_ge_one log_ratio_ge)

noncomputable def aMin (Lp q : ℝ) : ℝ := Real.exp (-(5 / 2 * theta q) - 1) / (18 * Lp)

noncomputable def lnm (Lp q A : ℝ) : ℝ := Real.log (max A (aMin Lp q)) - Real.log (aMin Lp q)

noncomputable def ind (Lp q A : ℝ) : ℝ := if aMin Lp q ≤ A then 1 else 0

noncomputable def omega (Lp L1 q A S : ℝ) : ℝ :=
  L1 ^ 2 / theta q ^ 2 * S + 2 * Real.sqrt 24 * Real.sqrt (Lp * A) + 29 * theta q * lnm Lp q A

lemma aMin_pos {Lp q : ℝ} (hLp : 0 < Lp) : 0 < aMin Lp q := by
  unfold aMin; positivity

lemma lnm_nonneg {Lp q A : ℝ} (hLp : 0 < Lp) : 0 ≤ lnm Lp q A := by
  unfold lnm
  have := aMin_pos (q := q) hLp
  exact sub_nonneg.mpr (Real.log_le_log this (le_max_right _ _))

lemma lnm_mono {Lp q A B : ℝ} (hLp : 0 < Lp) (hAB : A ≤ B) : lnm Lp q A ≤ lnm Lp q B := by
  unfold lnm
  have := aMin_pos (q := q) hLp
  have h1 : 0 < max A (aMin Lp q) := lt_of_lt_of_le this (le_max_right _ _)
  exact sub_le_sub_right (Real.log_le_log h1 (max_le_max hAB le_rfl)) _

lemma ind_mono {Lp q A B : ℝ} (hAB : A ≤ B) : ind Lp q A ≤ ind Lp q B := by
  unfold ind
  split_ifs with h1 h2 <;> norm_num
  exact h2 (h1.trans hAB)

lemma ind_nonneg {Lp q A : ℝ} : 0 ≤ ind Lp q A := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one {Lp q A : ℝ} : ind Lp q A ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma phiFun_log_lower {Lp L1 x : ℝ} (hLp : 0 < Lp) (hL1 : 0 < L1) (hx : 0 < x) :
    (Real.log (1 + L1 * x / Lp) - 1) * x ≤ L1 * phiFun Lp L1 x := by
  unfold phiFun
  set s := L1 * x / Lp with hs
  have hs0 : 0 < s := by positivity
  have hlog : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
  have hrw : L1 * (Lp / L1 ^ 2 * ((1 + s) * Real.log (1 + s) - s)) =
      ((1 + s) * Real.log (1 + s) - s) * x / s := by
    rw [hs]; field_simp
  rw [hrw, le_div_iff₀ hs0]
  nlinarith [mul_nonneg hlog hx.le]

lemma sqrt24_sq : Real.sqrt 24 ^ 2 = 24 := Real.sq_sqrt (by norm_num)

set_option maxHeartbeats 2000000 in
lemma iteration_increment {L0 L1 M q A S G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hG : gthr L0 L1 M < G) :
    omega (L0 + L1 * M) L1 q A S + ind (L0 + L1 * M) q A + 1 ≤
      omega (L0 + L1 * M) L1 q (A + cweight L0 L1 M A G) (S + cweight L0 L1 M A G ^ 2 * G ^ 2) +
        ind (L0 + L1 * M) q (A + cweight L0 L1 M A G) := by
  set θ := theta q with hθdef
  have hθ : 0 < θ := theta_pos hq
  have hθ1 : 1 ≤ θ := theta_ge_one hq
  set Lp := L0 + L1 * M with hLpdef
  have hLp : 0 < Lp := by rw [hLpdef]; positivity
  obtain ⟨hGpos, h45, h65, hLG, hcb, hLpG⟩ := gthr_facts hL0 hL1 hM hG
  set a := cweight L0 L1 M A G with ha
  set L := curv L0 L1 M G with hLdef
  set Φ := phiFun Lp L1 (G - M) with hΦdef
  have hL : 0 < L := curv_pos hL0 hL1.le hM hGpos.le
  obtain ⟨hapos, haeq⟩ := cweight_eq hL0 hL1 hM hA hGpos (by linarith)
  rw [← ha] at hapos
  rw [← ha, ← hLpdef, ← hΦdef, ← hLdef] at haeq
  have hφ0 : 0 ≤ Φ := phiFun_nonneg hLp hL1 (by linarith)
  have hsq : (A + a) / (12 * L) ≤ a ^ 2 := by
    rw [haeq]; have : 0 ≤ a * Φ / (2 * G ^ 2) := by positivity
    linarith
  have hA' : 0 < A + a := by linarith
  have hsqrt_mono : Real.sqrt (Lp * A) ≤ Real.sqrt (Lp * (A + a)) :=
    Real.sqrt_le_sqrt (by have := mul_pos hLp hapos; linarith only [this])
  have hlnm_mono : lnm Lp q A ≤ lnm Lp q (A + a) := lnm_mono hLp (by linarith)
  have hind_mono : ind Lp q A ≤ ind Lp q (A + a) := ind_mono (by linarith)
  have hS_inc : L1 ^ 2 / θ ^ 2 * S ≤ L1 ^ 2 / θ ^ 2 * (S + a ^ 2 * G ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [sq_nonneg (a * G)]
  have hLe : L = Lp + L1 * (G + M) := by rw [hLdef, hLpdef]; unfold curv; ring
  show L1 ^ 2 / θ ^ 2 * S + 2 * Real.sqrt 24 * Real.sqrt (Lp * A) + 29 * θ * lnm Lp q A +
      ind Lp q A + 1 ≤
    L1 ^ 2 / θ ^ 2 * (S + a ^ 2 * G ^ 2) + 2 * Real.sqrt 24 * Real.sqrt (Lp * (A + a)) +
      29 * θ * lnm Lp q (A + a) + ind Lp q (A + a)
  have hc24 : (0 : ℝ) ≤ 2 * Real.sqrt 24 := by positivity
  have hsqrt_term := mul_le_mul_of_nonneg_left hsqrt_mono hc24
  have hlnm_term := mul_le_mul_of_nonneg_left hlnm_mono (by positivity : (0:ℝ) ≤ 29 * θ)
  by_cases hJ : θ ≤ L1 * a * G
  ·
    have : 1 ≤ L1 ^ 2 / θ ^ 2 * (a ^ 2 * G ^ 2) := by
      rw [show L1 ^ 2 / θ ^ 2 * (a ^ 2 * G ^ 2) = (L1 * a * G / θ) ^ 2 by ring]
      have : 1 ≤ L1 * a * G / θ := by rw [le_div_iff₀ hθ]; linarith only [hJ]
      exact one_le_pow₀ this
    have e : L1 ^ 2 / θ ^ 2 * (S + a ^ 2 * G ^ 2) =
        L1 ^ 2 / θ ^ 2 * S + L1 ^ 2 / θ ^ 2 * (a ^ 2 * G ^ 2) := by ring
    rw [e]
    linarith only [this, hlnm_term, hsqrt_term, hind_mono]
  · push Not at hJ
    by_cases hβ : L1 * (G + M) < Lp
    ·
      have hL2 : L < 2 * Lp := by rw [hLe]; linarith only [hβ]
      have hA24 : (A + a) / (24 * Lp) ≤ a ^ 2 := by
        calc (A + a) / (24 * Lp) ≤ (A + a) / (12 * L) := by
              apply div_le_div_of_nonneg_left hA'.le (by positivity) (by linarith)
          _ ≤ a ^ 2 := hsq
      have h24 : 0 < Real.sqrt 24 := by positivity
      have hs1 : 1 / (2 * Real.sqrt 24) ≤ Real.sqrt (Lp * (A + a)) - Real.sqrt (Lp * A) := by
        set sp := Real.sqrt (Lp * (A + a)) with hsp
        set sm := Real.sqrt (Lp * A) with hsm
        have hsm0 : 0 ≤ sm := Real.sqrt_nonneg _
        have hsp0 : 0 < sp := Real.sqrt_pos.mpr (by positivity)
        have e1 : sp ^ 2 = Lp * (A + a) := by rw [hsp]; exact Real.sq_sqrt (by positivity)
        have e2 : sm ^ 2 = Lp * A := by rw [hsm]; exact Real.sq_sqrt (by positivity)
        have hdiff : (sp - sm) * (sp + sm) = Lp * a := by linear_combination e1 - e2
        have hle : sm ≤ sp := hsqrt_mono
        have hbound : sp ≤ Real.sqrt 24 * Lp * a := by
          rw [hsp, show Real.sqrt 24 * Lp * a = Real.sqrt ((Real.sqrt 24 * Lp * a) ^ 2) from
            (Real.sqrt_sq (by positivity)).symm]
          apply Real.sqrt_le_sqrt
          have e : (Real.sqrt 24 * Lp * a) ^ 2 = 24 * Lp * (Lp * a ^ 2) := by
            linear_combination (Lp ^ 2 * a ^ 2) * sqrt24_sq
          rw [e]
          have h1 : A + a ≤ 24 * Lp * a ^ 2 := by
            have := hA24
            rw [div_le_iff₀ (by positivity)] at this
            linarith
          have := mul_le_mul_of_nonneg_left h1 hLp.le
          linarith only [this]
        have hsum : sp + sm ≤ 2 * Real.sqrt 24 * Lp * a := by linarith
        have hd0 : 0 ≤ sp - sm := by linarith
        have hLa : 0 < Lp * a := by positivity
        have hprod : Lp * a ≤ (sp - sm) * (2 * Real.sqrt 24 * Lp * a) := by
          calc Lp * a = (sp - sm) * (sp + sm) := hdiff.symm
            _ ≤ (sp - sm) * (2 * Real.sqrt 24 * Lp * a) := mul_le_mul_of_nonneg_left hsum hd0
        rw [div_le_iff₀ (by positivity)]
        have h5 : (Lp * a) * 1 ≤ (Lp * a) * ((sp - sm) * (2 * Real.sqrt 24)) := by
          calc (Lp * a) * 1 = Lp * a := mul_one _
            _ ≤ (sp - sm) * (2 * Real.sqrt 24 * Lp * a) := hprod
            _ = (Lp * a) * ((sp - sm) * (2 * Real.sqrt 24)) := by ring
        exact le_of_mul_le_mul_left h5 hLa
      have hterm : 2 * Real.sqrt 24 * Real.sqrt (Lp * A) + 1 ≤
          2 * Real.sqrt 24 * Real.sqrt (Lp * (A + a)) := by
        have := mul_le_mul_of_nonneg_left hs1 hc24
        have h2 : 2 * Real.sqrt 24 * (1 / (2 * Real.sqrt 24)) = 1 := by field_simp
        linarith only [this, h2]
      linarith only [hS_inc, hterm, hlnm_term, hind_mono]
    · push Not at hβ
      have hGL : 5 / 12 ≤ L1 * G / L := by
        rw [le_div_iff₀ hL, hLe]
        nlinarith [mul_nonneg hL1.le hM, mul_le_mul_of_nonneg_left h65 hL1.le]
      have hid : L1 * a * G = L1 * Φ / (2 * G) + (A + a) / (12 * a) * (L1 * G / L) := by
        have hX : (A + a) / (12 * L) = a ^ 2 - a * Φ / (2 * G ^ 2) := by linarith [haeq]
        have e : (A + a) / (12 * a) * (L1 * G / L) = (A + a) / (12 * L) * (L1 * G / a) := by
          field_simp
        rw [e, hX]
        field_simp
        ring
      have hnn : 0 ≤ (A + a) / (12 * a) * (L1 * G / L) := by positivity
      have hφG : 0 ≤ L1 * Φ / (2 * G) := by positivity
      have hratio : 5 * (A + a) / (144 * a) ≤ L1 * a * G := by
        have := mul_le_mul_of_nonneg_left hGL (by positivity : 0 ≤ (A + a) / (12 * a))
        have e : (A + a) / (12 * a) * (5 / 12) = 5 * (A + a) / (144 * a) := by ring
        linarith only [this, e, hid, hφG]
      have hfrac : 5 / (144 * θ) < a / (A + a) := by
        rw [div_lt_div_iff₀ (by positivity) hA']
        have := hratio
        rw [div_le_iff₀ (by positivity)] at this
        have h144a : 0 < 144 * a := by linarith only [hapos]
        calc 5 * (A + a) ≤ L1 * a * G * (144 * a) := this
          _ < θ * (144 * a) := mul_lt_mul_of_pos_right hJ h144a
          _ = a * (144 * θ) := by ring
      have hA_lower : 1 / (12 * L) ≤ A + a := by
        have h1 : a ≤ A + a := by linarith
        have h2 : (A + a) / (12 * L) ≤ (A + a) ^ 2 :=
          hsq.trans (pow_le_pow_left₀ hapos.le h1 2)
        have h2' : A + a ≤ (A + a) ^ 2 * (12 * L) := by rwa [div_le_iff₀ (by positivity)] at h2
        rw [div_le_iff₀ (by positivity)]
        have h3 : (A + a) * 1 ≤ (A + a) * ((A + a) * (12 * L)) := by
          calc (A + a) * 1 = A + a := mul_one _
            _ ≤ (A + a) ^ 2 * (12 * L) := h2'
            _ = (A + a) * ((A + a) * (12 * L)) := by ring
        exact le_of_mul_le_mul_left h3 hA'
      set s := L1 * (G - M) / Lp with hs
      have hGM0' : 0 < G - M := by linarith
      have hs0 : 0 < s := div_pos (mul_pos hL1 hGM0') hLp
      have hlogL : Real.log (1 + s) < 5 / 2 * θ + 1 := by
        have h1 := phiFun_log_lower (Lp := Lp) (L1 := L1) (x := G - M) hLp hL1 (by linarith)
        rw [← hs, ← hΦdef] at h1
        have h2 : L1 * Φ / (2 * G) ≤ L1 * a * G := by linarith only [hid, hnn]
        have h3 : L1 * Φ / (2 * G) < θ := lt_of_le_of_lt h2 hJ
        have hGM0 : 0 < G - M := by linarith
        by_contra hcon
        push Not at hcon
        have h4 : 0 ≤ Real.log (1 + s) - 1 := by linarith
        have h5 : (Real.log (1 + s) - 1) * (4 / 5 * G) ≤ (Real.log (1 + s) - 1) * (G - M) :=
          mul_le_mul_of_nonneg_left h45 h4
        have h6 : (Real.log (1 + s) - 1) * (4 / 5 * G) ≤ L1 * Φ := h5.trans h1
        have h7 : L1 * Φ / (2 * G) ≥ (Real.log (1 + s) - 1) * (2 / 5) := by
          rw [ge_iff_le, le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith
      have hLexp : L < 3 / 2 * Lp * Real.exp (5 / 2 * θ + 1) := by
        have hpos : 0 < 1 + s := by positivity
        have h3 : 1 + s < Real.exp (5 / 2 * θ + 1) := by
          rw [← Real.exp_log hpos]; exact Real.exp_lt_exp.mpr hlogL
        have hLs : L ≤ 3 / 2 * Lp * (1 + s) := by
          rw [hLe, hs]
          have e : 3 / 2 * Lp * (1 + L1 * (G - M) / Lp) = 3 / 2 * Lp + 3 / 2 * L1 * (G - M) := by
            field_simp
          rw [e]
          nlinarith [mul_nonneg hL1.le hM, mul_le_mul_of_nonneg_left h45 hL1.le]
        have : 3 / 2 * Lp * (1 + s) < 3 / 2 * Lp * Real.exp (5 / 2 * θ + 1) := by
          apply mul_lt_mul_of_pos_left h3 (by positivity)
        linarith
      have hAmin : aMin Lp q < A + a := by
        unfold aMin
        rw [← hθdef]
        calc Real.exp (-(5 / 2 * θ) - 1) / (18 * Lp) =
              1 / (12 * (3 / 2 * Lp * Real.exp (5 / 2 * θ + 1))) := by
              rw [show -(5 / 2 * θ) - 1 = -(5 / 2 * θ + 1) by ring, Real.exp_neg]
              field_simp
              norm_num
          _ < 1 / (12 * L) := by
              apply div_lt_div_of_pos_left one_pos (by linarith only [hL])
              linarith only [hLexp]
          _ ≤ A + a := hA_lower
      have hindA' : ind Lp q (A + a) = 1 := by simp [ind, hAmin.le]
      by_cases hprev : aMin Lp q ≤ A
      ·
        have hindA : ind Lp q A = 1 := by simp [ind, hprev]
        have hApos : 0 < A := lt_of_lt_of_le (aMin_pos hLp) hprev
        have hlnm_inc : a / (A + a) ≤ lnm Lp q (A + a) - lnm Lp q A := by
          unfold lnm
          rw [max_eq_left hAmin.le, max_eq_left hprev]
          have := log_ratio_ge hapos (show a < A + a by linarith)
          rw [show A + a - a = A by ring] at this
          linarith only [this]
        have h29 : 1 ≤ 29 * θ * (lnm Lp q (A + a) - lnm Lp q A) := by
          have := mul_le_mul_of_nonneg_left hlnm_inc (by positivity : (0:ℝ) ≤ 29 * θ)
          have h3 := mul_le_mul_of_nonneg_left hfrac.le (by positivity : (0:ℝ) ≤ 29 * θ)
          have h2 : 29 * θ * (5 / (144 * θ)) = 145 / 144 := by field_simp; ring
          linarith only [this, h2, h3]
        rw [hindA, hindA']
        linarith only [hS_inc, hsqrt_term, h29]
      · push Not at hprev
        have hindA : ind Lp q A = 0 := by simp [ind, not_le.mpr hprev]
        rw [hindA, hindA']
        linarith only [hS_inc, hsqrt_term, hlnm_term]

noncomputable def bigB (q : ℝ) : ℝ :=
  q + 1 + 2 * Real.sqrt 24 * Real.sqrt 12 * q +
    29 * theta q * (5 / 2 * theta q + 1 + Real.log (216 * (1 + q) ^ 2))

lemma omega_bound {Lp L1 q R A S : ℝ} (hLp : 0 < Lp) (hL1 : 0 < L1) (hq : q = L1 * R)
    (hR : 0 < R) (hS : S ≤ R ^ 2) (hAq : Lp * A ≤ 12 * q ^ 2) :
    omega Lp L1 q A S + ind Lp q A ≤ bigB q := by
  have hqpos : 0 < q := by rw [hq]; positivity
  have hθ := theta_pos hqpos.le
  have hθsq := theta_sq hqpos.le
  unfold omega bigB
  have h1 : L1 ^ 2 / theta q ^ 2 * S ≤ q := by
    rw [hθsq, hq]
    have : L1 ^ 2 / (1 + L1 * R) * S ≤ L1 ^ 2 / (1 + L1 * R) * R ^ 2 :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have h2 : L1 ^ 2 / (1 + L1 * R) * R ^ 2 ≤ L1 * R := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_pos hL1 hR]
    linarith
  have h2 : 2 * Real.sqrt 24 * Real.sqrt (Lp * A) ≤ 2 * Real.sqrt 24 * Real.sqrt 12 * q := by
    have : Real.sqrt (Lp * A) ≤ Real.sqrt 12 * q := by
      rw [← Real.sqrt_sq hqpos.le, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hAq
    have h24 : 0 ≤ 2 * Real.sqrt 24 := by positivity
    calc 2 * Real.sqrt 24 * Real.sqrt (Lp * A) ≤ 2 * Real.sqrt 24 * (Real.sqrt 12 * q) :=
          mul_le_mul_of_nonneg_left this h24
      _ = 2 * Real.sqrt 24 * Real.sqrt 12 * q := by ring
  have h3 : lnm Lp q A ≤ 5 / 2 * theta q + 1 + Real.log (216 * (1 + q) ^ 2) := by
    unfold lnm
    have hamin := aMin_pos (q := q) hLp
    rcases le_or_gt A (aMin Lp q) with hcase | hcase
    · rw [max_eq_right hcase]
      have hlog : 0 ≤ Real.log (216 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
      linarith [theta_pos hqpos.le]
    · rw [max_eq_left hcase.le]
      have hApos : 0 < A := lt_trans hamin hcase
      rw [← Real.log_div hApos.ne' hamin.ne']
      unfold aMin
      have hratio : A / (Real.exp (-(5 / 2 * theta q) - 1) / (18 * Lp)) ≤
          216 * (1 + q) ^ 2 * Real.exp (5 / 2 * theta q + 1) := by
        rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
        have he : Real.exp (-(5 / 2 * theta q) - 1) * Real.exp (5 / 2 * theta q + 1) = 1 := by
          rw [← Real.exp_add, show -(5 / 2 * theta q) - 1 + (5 / 2 * theta q + 1) = 0 by ring,
            Real.exp_zero]
        have h18 : A * (18 * Lp) ≤ 216 * q ^ 2 := by nlinarith [hAq]
        have hq2 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
        calc A * (18 * Lp) ≤ 216 * q ^ 2 := h18
          _ ≤ 216 * (1 + q) ^ 2 := by nlinarith
          _ = 216 * (1 + q) ^ 2 * (Real.exp (5 / 2 * theta q + 1) *
              Real.exp (-(5 / 2 * theta q) - 1)) := by
              rw [mul_comm (Real.exp (5 / 2 * theta q + 1)), he, mul_one]
          _ = 216 * (1 + q) ^ 2 * Real.exp (5 / 2 * theta q + 1) *
              Real.exp (-(5 / 2 * theta q) - 1) := by ring
      have hpos : 0 < A / (Real.exp (-(5 / 2 * theta q) - 1) / (18 * Lp)) := by positivity
      calc Real.log (A / (Real.exp (-(5 / 2 * theta q) - 1) / (18 * Lp))) ≤
            Real.log (216 * (1 + q) ^ 2 * Real.exp (5 / 2 * theta q + 1)) :=
            Real.log_le_log hpos hratio
        _ = Real.log (216 * (1 + q) ^ 2) + (5 / 2 * theta q + 1) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
        _ = 5 / 2 * theta q + 1 + Real.log (216 * (1 + q) ^ 2) := by ring
  have h3' : 29 * theta q * lnm Lp q A ≤
      29 * theta q * (5 / 2 * theta q + 1 + Real.log (216 * (1 + q) ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h4 : ind Lp q A ≤ 1 := ind_le_one
  linarith

end OracleTemplate.CompositeSherpa
