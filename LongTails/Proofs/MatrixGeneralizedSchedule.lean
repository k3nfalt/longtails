import LongTails.Algorithms.MatrixGeneralizedZO
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Real

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

structure Valid (p : Params) : Prop where
  d_pos : 0 < p.d
  L0_pos : 0 < p.L0
  L1_nonneg : 0 ≤ p.L1
  r_pos : 0 < p.r
  R_pos : 0 < p.R
  Δ_pos : 0 < p.Δ
  ε_pos : 0 < p.ε

lemma valid_of_spec {p : Params} (hp : spec.valid p) : Valid p :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1⟩

noncomputable def lagWeight (p : Params) (A : ℝ) : ℝ := weight p A / (64 * stepSize p A)

section

variable {p : Params} (hp : Valid p)
include hp

lemma dR_pos : (0 : ℝ) < p.d := by exact_mod_cast hp.d_pos

lemma one_le_d : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.d_pos

lemma sqrt_d_pos : 0 < Real.sqrt p.d := Real.sqrt_pos.mpr (dR_pos hp)

lemma one_le_sqrt_d : 1 ≤ Real.sqrt p.d := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (one_le_d hp)

lemma Lp_pos : 0 < Lp p :=
  lt_of_lt_of_le (by have := hp.R_pos; have := sqrt_d_pos hp; positivity) (le_max_right _ _)

omit hp in
lemma L1_le_Lp : p.L1 ≤ Lp p := le_max_left _ _

lemma Lp_R_sqrt_d : 1 ≤ Lp p * p.R * Real.sqrt p.d := by
  have hR := hp.R_pos
  have hs := sqrt_d_pos hp
  have h : 1 / (p.R * Real.sqrt p.d) ≤ Lp p := le_max_right _ _
  rw [div_le_iff₀ (by positivity)] at h
  linarith

lemma rp_pos : 0 < rp p := by unfold rp; have := hp.r_pos; positivity

lemma rp_ge16 : 16 ≤ rp p := by unfold rp; have := hp.r_pos; linarith

lemma r_two_le_rp : p.r + 2 ≤ rp p := by unfold rp; have := hp.r_pos; linarith

lemma r_le_rp : p.r ≤ rp p := by unfold rp; have := hp.r_pos; linarith

lemma rp_le : rp p ≤ 50 * (p.r + 1) := by unfold rp; have := hp.r_pos; linarith

lemma sqrt48r_le : 8 * Real.sqrt (48 * p.r) ≤ rp p := by
  have hr := hp.r_pos
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 48 * p.r by positivity)
  have hs0 := Real.sqrt_nonneg (48 * p.r)
  unfold rp
  nlinarith [sq_nonneg (Real.sqrt (48 * p.r) - 4)]

lemma thetaCap_pos : 0 < thetaCap p := by
  unfold thetaCap; have := hp.r_pos; apply lt_min <;> positivity

omit hp in
lemma thetaCap_le : thetaCap p ≤ 1 / 4 := min_le_left _ _

lemma thetaCap_mul : thetaCap p * (p.r + 2) ≤ 2 := by
  have hr := hp.r_pos
  have h : thetaCap p ≤ 2 / (p.r + 2) := min_le_right _ _
  have := mul_le_mul_of_nonneg_right h (show 0 ≤ p.r + 2 by linarith)
  rwa [div_mul_cancel₀ _ (by linarith)] at this

lemma gradBound_nonneg {F : ℝ} (hF : 0 ≤ F) : 0 ≤ gradBound p F := by
  unfold gradBound; have := Lp_pos hp; positivity

lemma gradBound_mono {F F' : ℝ} (h : F ≤ F') : gradBound p F ≤ gradBound p F' := by
  unfold gradBound
  have := Lp_pos hp
  have h1 : Real.sqrt (p.L0 * F) ≤ Real.sqrt (p.L0 * F') :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hp.L0_pos.le)
  nlinarith

lemma curvBound_pos {F : ℝ} (hF : 0 ≤ F) : 0 < curvBound p F := by
  unfold curvBound
  have := gradBound_nonneg hp hF
  have := Lp_pos hp
  have := hp.L0_pos
  positivity

lemma curvBound_mono {F F' : ℝ} (h : F ≤ F') :
    curvBound p F ≤ curvBound p F' := by
  unfold curvBound
  have := gradBound_mono hp h
  have := Lp_pos hp
  nlinarith

lemma L0_le_curvBound {F : ℝ} (hF : 0 ≤ F) : p.L0 ≤ curvBound p F := by
  unfold curvBound
  have := gradBound_nonneg hp hF
  have := Lp_pos hp
  nlinarith

lemma grad_le_curvBound {F : ℝ} : Lp p * gradBound p F ≤ curvBound p F := by
  unfold curvBound; have := hp.L0_pos; linarith

lemma gradBound_sq_le {F : ℝ} (hF : 0 ≤ F) : gradBound p F ^ 2 ≤ 8 * F * curvBound p F := by
  unfold curvBound gradBound
  have hs := Real.sq_sqrt (mul_nonneg hp.L0_pos.le hF)
  have hs0 := Real.sqrt_nonneg (p.L0 * F)
  have hL := Lp_pos hp
  nlinarith [sq_nonneg (2 * Lp p * F - Real.sqrt (p.L0 * F)), mul_nonneg hL.le hs0,
    mul_nonneg (mul_nonneg hL.le hF) hs0]

lemma curvBound_le {F : ℝ} (hF : 0 ≤ F) : curvBound p F ≤ 2 * p.L0 + 20 * Lp p ^ 2 * F := by
  unfold curvBound gradBound
  have hs := Real.sq_sqrt (mul_nonneg hp.L0_pos.le hF)
  have hs0 := Real.sqrt_nonneg (p.L0 * F)
  have hL := Lp_pos hp
  have hL0 := hp.L0_pos
  have key : 2 * Lp p * Real.sqrt (p.L0 * F) ≤ p.L0 + Lp p ^ 2 * F := by
    by_contra hc
    rw [not_le] at hc
    have hpos : 0 < 2 * Lp p * Real.sqrt (p.L0 * F) + (p.L0 + Lp p ^ 2 * F) := by positivity
    have := mul_pos (sub_pos.mpr hc) hpos
    nlinarith [sq_nonneg (p.L0 - Lp p ^ 2 * F)]
  nlinarith

lemma gapLevel_pos {A : ℝ} (hA : 0 < A) : 0 < gapLevel p A := by
  unfold gapLevel; have := hp.R_pos; positivity

lemma gapLevel_anti {A A' : ℝ} (hA : 0 < A) (h : A ≤ A') : gapLevel p A' ≤ gapLevel p A := by
  unfold gapLevel
  have := hp.R_pos
  exact div_le_div_of_nonneg_left (by positivity) hA h

lemma curv_mul_A {A : ℝ} (hA : 0 < A) :
    32 * Lp p ^ 2 * p.R ^ 2 ≤ curvBound p (gapLevel p A) * A := by
  have h1 := grad_le_curvBound hp (F := gapLevel p A)
  have hL := Lp_pos hp
  have hg : 4 * Lp p * gapLevel p A ≤ gradBound p (gapLevel p A) := by
    unfold gradBound; have := Real.sqrt_nonneg (p.L0 * gapLevel p A); linarith
  have h2 : Lp p * (4 * Lp p * gapLevel p A) ≤ curvBound p (gapLevel p A) :=
    le_trans (mul_le_mul_of_nonneg_left hg hL.le) h1
  have h3 : Lp p * (4 * Lp p * gapLevel p A) * A = 32 * Lp p ^ 2 * p.R ^ 2 := by
    unfold gapLevel; field_simp; ring
  rw [← h3]
  exact mul_le_mul_of_nonneg_right h2 hA.le

lemma stepSize_pos {A : ℝ} (hA : 0 < A) : 0 < stepSize p A := by
  unfold stepSize
  have := curvBound_pos hp (gapLevel_pos hp hA).le
  have := rp_pos hp
  positivity

lemma stepSize_mono {A A' : ℝ} (hA : 0 < A) (h : A ≤ A') : stepSize p A ≤ stepSize p A' := by
  unfold stepSize
  have hc := curvBound_mono hp (gapLevel_anti hp hA h)
  have := curvBound_pos hp (gapLevel_pos hp (hA.trans_le h)).le
  have := rp_pos hp
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma stepSize_curv {A : ℝ} (hA : 0 < A) :
    curvBound p (gapLevel p A) * stepSize p A = 1 / (8 * rp p) := by
  unfold stepSize
  have := curvBound_pos hp (gapLevel_pos hp hA).le
  have := rp_pos hp
  field_simp

lemma weight_pos {A : ℝ} (hA : 0 < A) : 0 < weight p A := by
  unfold weight
  have := stepSize_pos hp hA
  have := thetaCap_pos hp
  have := dR_pos hp
  apply lt_min
  · apply Real.sqrt_pos.mpr; positivity
  · positivity

omit hp in
lemma weight_le_cap {A : ℝ} : weight p A ≤ thetaCap p * A := min_le_right _ _

omit hp in
lemma weight_le_quarter {A : ℝ} (hA : 0 < A) : weight p A ≤ A / 4 := by
  have h := weight_le_cap (p := p) (A := A)
  have := mul_le_mul_of_nonneg_right (thetaCap_le (p := p)) hA.le
  linarith

lemma weight_sq_le {A : ℝ} (hA : 0 < A) :
    weight p A ^ 2 ≤ A * stepSize p A / (8 * p.d) := by
  have h1 : weight p A ≤ Real.sqrt (A * stepSize p A / (8 * p.d)) := min_le_left _ _
  have h0 := (weight_pos hp hA).le
  have hs := stepSize_pos hp hA
  have hd := dR_pos hp
  calc weight p A ^ 2 ≤ Real.sqrt (A * stepSize p A / (8 * p.d)) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = A * stepSize p A / (8 * p.d) := Real.sq_sqrt (by positivity)

lemma sched_pos (k : ℕ) : 0 < sched p k := by
  induction k with
  | zero => simp only [sched]; have := hp.R_pos; have := hp.Δ_pos; positivity
  | succ k ih => simp only [sched]; have := weight_pos hp ih; linarith

lemma sched_le_succ (k : ℕ) : sched p k ≤ sched p (k + 1) := by
  simp only [sched]; have := weight_pos hp (sched_pos hp k); linarith

lemma sched_mono {j k : ℕ} (h : j ≤ k) : sched p j ≤ sched p k :=
  monotone_nat_of_le_succ (sched_le_succ hp) h

lemma lagWeight_pos {A : ℝ} (hA : 0 < A) : 0 < lagWeight p A := by
  unfold lagWeight; have := weight_pos hp hA; have := stepSize_pos hp hA; positivity

lemma lagWeight_ratio {A : ℝ} (hA : 0 < A) :
    lagWeight p (A + weight p A) ≤ (1 + weight p A / A) * lagWeight p A := by
  set a := weight p A
  set A' := A + a
  have ha := weight_pos hp hA
  have hA' : 0 < A' := by positivity
  have hAA : A ≤ A' := by simp only [A']; linarith
  have hs := stepSize_pos hp hA
  have hs' := stepSize_pos hp hA'
  have hss := stepSize_mono hp hA hAA
  have hd := dR_pos hp
  have hθ := thetaCap_pos hp
  have hratio : A' / A = 1 + a / A := by simp only [A']; field_simp
  have hq : 1 ≤ A' / A := by rw [le_div_iff₀ hA]; linarith
  set f1 := fun B : ℝ => Real.sqrt (B * stepSize p B / (8 * p.d)) / (64 * stepSize p B)
  set f2 := fun B : ℝ => thetaCap p * B / (64 * stepSize p B)
  have hlag : ∀ B, 0 < B → lagWeight p B = min (f1 B) (f2 B) := by
    intro B hB
    have := stepSize_pos hp hB
    unfold lagWeight weight
    rw [← min_div_div_right (by positivity)]
  have hsq : ∀ B, 0 < B → f1 B ^ 2 = B / (32768 * p.d * stepSize p B) := by
    intro B hB
    have := stepSize_pos hp hB
    simp only [f1]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hf1 : f1 A' ≤ (A' / A) * f1 A := by
    have h0 : 0 ≤ f1 A' := by simp only [f1]; positivity
    have h1 : 0 ≤ (A' / A) * f1 A := by simp only [f1]; positivity
    rw [← pow_le_pow_iff_left₀ h0 h1 (by norm_num : (2 : ℕ) ≠ 0), mul_pow, hsq A' hA', hsq A hA]
    rw [show (A' / A) ^ 2 * (A / (32768 * p.d * stepSize p A)) =
      (A' / A) * (A' / (32768 * p.d * stepSize p A)) by field_simp]
    calc A' / (32768 * p.d * stepSize p A') ≤ A' / (32768 * p.d * stepSize p A) := by
          apply div_le_div_of_nonneg_left hA'.le (by positivity)
          nlinarith
      _ ≤ (A' / A) * (A' / (32768 * p.d * stepSize p A)) := by
          apply le_mul_of_one_le_left (by positivity) hq
  have hf2 : f2 A' ≤ (A' / A) * f2 A := by
    simp only [f2]
    rw [show A' / A * (thetaCap p * A / (64 * stepSize p A)) =
      thetaCap p * A' / (64 * stepSize p A) by field_simp]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  rw [hlag A' hA', hlag A hA, ← hratio]
  have hq0 : 0 ≤ A' / A := by positivity
  rw [mul_min_of_nonneg _ _ hq0]
  exact min_le_min hf1 hf2

lemma lagWeight_ge {A : ℝ} (hA : 0 < A) : 1 / (8 * p.d * rp p) ≤ lagWeight p A := by
  have hd := dR_pos hp
  have hrp := rp_pos hp
  have hrp16 := rp_ge16 hp
  have hs := stepSize_pos hp hA
  have hc := curv_mul_A hp hA
  have hsc := stepSize_curv hp hA
  have hLR := Lp_R_sqrt_d hp
  have hL := Lp_pos hp
  have hR := hp.R_pos
  have hθ := thetaCap_pos hp
  have hcurv := curvBound_pos hp (gapLevel_pos hp hA).le
  have hsd := sqrt_d_pos hp
  have hLRd : 1 ≤ Lp p ^ 2 * p.R ^ 2 * p.d := by
    have := mul_self_le_mul_self (by norm_num) hLR
    have e : Lp p * p.R * Real.sqrt p.d * (Lp p * p.R * Real.sqrt p.d) =
        Lp p ^ 2 * p.R ^ 2 * p.d := by
      rw [show Lp p * p.R * Real.sqrt p.d * (Lp p * p.R * Real.sqrt p.d) =
        Lp p ^ 2 * p.R ^ 2 * (Real.sqrt p.d) ^ 2 by ring, Real.sq_sqrt hd.le]
    linarith
  have hs_eq : stepSize p A = 1 / (8 * curvBound p (gapLevel p A) * rp p) := rfl
  unfold lagWeight weight
  rw [← min_div_div_right (by positivity)]
  apply le_min
  · -- branch 1
    set v := Real.sqrt (A * stepSize p A / (8 * p.d)) / (64 * stepSize p A)
    have hv0 : 0 ≤ v := by positivity
    have hsqv : v ^ 2 = rp p * (curvBound p (gapLevel p A) * A) / (4096 * p.d) := by
      simp only [v]
      rw [div_pow, Real.sq_sqrt (by positivity), hs_eq]
      field_simp
      ring
    rw [← pow_le_pow_iff_left₀ (by positivity) hv0 (by norm_num : (2 : ℕ) ≠ 0), hsqv]
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hMA : 32 / p.d ≤ curvBound p (gapLevel p A) * A := by
      rw [div_le_iff₀ hd]; nlinarith
    have hMA' : 32 ≤ curvBound p (gapLevel p A) * A * p.d := by
      rwa [div_le_iff₀ hd] at hMA
    have e2 : rp p * (curvBound p (gapLevel p A) * A) * (8 * p.d * rp p) ^ 2 =
        64 * rp p ^ 3 * p.d * (curvBound p (gapLevel p A) * A * p.d) := by ring
    rw [e2]
    have h3 : 2 ≤ rp p ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hrp16 3
      norm_num at this; linarith
    have h4 : 0 ≤ 64 * rp p ^ 3 * p.d := by positivity
    calc 1 * (4096 * p.d) ≤ 64 * rp p ^ 3 * p.d * 32 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h3) hd.le]
      _ ≤ 64 * rp p ^ 3 * p.d * (curvBound p (gapLevel p A) * A * p.d) :=
          mul_le_mul_of_nonneg_left hMA' h4
  · -- branch 2
    have e : thetaCap p * A / (64 * stepSize p A) =
        thetaCap p * rp p * (curvBound p (gapLevel p A) * A) / 8 := by
      rw [hs_eq]; field_simp; ring
    rw [e]
    have hθr : 2 ≤ thetaCap p * rp p := by
      unfold thetaCap
      rw [min_mul_of_nonneg _ _ hrp.le]
      apply le_min
      · linarith
      · rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [hp.r_pos])]
        linarith [r_two_le_rp hp]
    have hMA : 32 / p.d ≤ curvBound p (gapLevel p A) * A := by
      rw [div_le_iff₀ hd]
      nlinarith
    have h1 : 2 * (32 / p.d) / 8 ≤ thetaCap p * rp p * (curvBound p (gapLevel p A) * A) / 8 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hθr hMA (by positivity) (by positivity)
    have h2 : 1 / (8 * p.d * rp p) ≤ 2 * (32 / p.d) / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [show 2 * (32 / p.d) * (8 * p.d * rp p) = 2 * 32 * (8 * rp p) by field_simp]
      nlinarith
    linarith

lemma clipLevel_ge {A : ℝ} (hA : 0 < A) :
    32 * curvBound p (gapLevel p A) / Lp p ≤ clipLevel p A := by
  have hL := Lp_pos hp
  have hM := curvBound_pos hp (gapLevel_pos hp hA).le
  have hrp := rp_pos hp
  have h48 := sqrt48r_le hp
  have hr := hp.r_pos
  have hsq : 0 < Real.sqrt (48 * p.r) := Real.sqrt_pos.mpr (by positivity)
  have e : clipLevel p A = 4 * curvBound p (gapLevel p A) * rp p / (Lp p * Real.sqrt (48 * p.r)) := by
    unfold clipLevel stepSize; field_simp; ring
  rw [e, div_le_div_iff₀ hL (by positivity)]
  have : 32 * curvBound p (gapLevel p A) * (Lp p * Real.sqrt (48 * p.r)) ≤
      4 * curvBound p (gapLevel p A) * (Lp p * rp p) := by
    have := mul_le_mul_of_nonneg_left h48 (show 0 ≤ 4 * curvBound p (gapLevel p A) * Lp p by positivity)
    nlinarith
  nlinarith

lemma errWeight_ge_one (k : ℕ) : 1 ≤ errWeight p k := by
  unfold errWeight
  have := sched_pos hp (k + 1)
  have := stepSize_pos hp (sched_pos hp k)
  have := weight_pos hp (sched_pos hp k)
  have := sqrt_d_pos hp
  have := dR_pos hp
  have : 0 ≤ sched p (k + 1) * stepSize p (sched p k) + weight p (sched p k) * Real.sqrt p.d +
    weight p (sched p k) ^ 2 * p.d := by positivity
  linarith

lemma fdStep_pos (k : ℕ) : 0 < fdStep p k := by
  unfold fdStep
  have hL := Lp_pos hp
  have hd := dR_pos hp
  have hs := sqrt_d_pos hp
  have hM := curvBound_pos hp (gapLevel_pos hp (sched_pos hp k)).le
  have hW := errWeight_ge_one hp k
  have hR := hp.R_pos
  have hL0 := hp.L0_pos
  apply lt_min (by positivity) (lt_min (by positivity) (by positivity))

lemma fdStep_trust (k : ℕ) : Lp p * (fdStep p k * Real.sqrt p.d) ≤ 1 / 2 := by
  have h : fdStep p k ≤ 1 / (2 * Lp p * Real.sqrt p.d) := min_le_left _ _
  have hL := Lp_pos hp
  have hs := sqrt_d_pos hp
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

lemma fdStep_eta_L0 (k : ℕ) :
    curvBound p (gapLevel p (sched p k)) * fdStep p k * p.d / 2 ≤ 16 * p.L0 / Lp p := by
  have h : fdStep p k ≤ 32 * p.L0 / (Lp p * curvBound p (gapLevel p (sched p k)) * p.d) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hL := Lp_pos hp
  have hd := dR_pos hp
  have hM := curvBound_pos hp (gapLevel_pos hp (sched_pos hp k)).le
  rw [le_div_iff₀ (by positivity)] at h
  rw [div_le_div_iff₀ (by norm_num) hL]
  nlinarith

lemma fdStep_eta_err (k : ℕ) :
    curvBound p (gapLevel p (sched p k)) * fdStep p k * p.d / 2 ≤
      p.R / (32 * 2 ^ k * errWeight p k) := by
  have h : fdStep p k ≤ 2 * (p.R / (32 * 2 ^ k * errWeight p k)) /
      (curvBound p (gapLevel p (sched p k)) * p.d) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hd := dR_pos hp
  have hM := curvBound_pos hp (gapLevel_pos hp (sched_pos hp k)).le
  rw [le_div_iff₀ (by positivity)] at h
  linarith

noncomputable def growthRate (p : Params) : ℝ :=
  min (thetaCap p) (1 / (Lp p * p.R * Real.sqrt (20480 * p.d * rp p)))

noncomputable def growthStep (p : Params) : ℝ := 1 / (36 * Real.sqrt (p.d * rp p * p.L0))

lemma growthRate_pos : 0 < growthRate p := by
  unfold growthRate
  have h1 := thetaCap_pos hp
  have h2 := Lp_pos hp
  have h3 := hp.R_pos
  have h4 := rp_pos hp
  have h5 := dR_pos hp
  apply lt_min h1
  have : 0 < Real.sqrt (20480 * p.d * rp p) := Real.sqrt_pos.mpr (by positivity)
  positivity

omit hp in
lemma growthRate_le : growthRate p ≤ 1 / 4 := (min_le_left _ _).trans (thetaCap_le (p := p))

lemma growthStep_pos : 0 < growthStep p := by
  unfold growthStep
  have := rp_pos hp; have := dR_pos hp; have := hp.L0_pos
  have : 0 < Real.sqrt (p.d * rp p * p.L0) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma growth_dichotomy {A : ℝ} (hA : 0 < A) :
    (1 + growthRate p) * A ≤ A + weight p A ∨
      Real.sqrt A + growthStep p ≤ Real.sqrt (A + weight p A) := by
  have hL := Lp_pos hp
  have hR := hp.R_pos
  have hd := dR_pos hp
  have hrp := rp_pos hp
  have hL0 := hp.L0_pos
  have hθ := thetaCap_pos hp
  have hgap := gapLevel_pos hp hA
  have hM := curvBound_pos hp hgap.le
  have hMle := curvBound_le hp hgap.le
  have hs := stepSize_pos hp hA
  have hseq : stepSize p A = 1 / (8 * curvBound p (gapLevel p A) * rp p) := rfl
  have hg : gapLevel p A = 8 * p.R ^ 2 / A := rfl
  set a := weight p A
  have ha := weight_pos hp hA
  by_cases hcase : a = thetaCap p * A
  · left
    have : growthRate p * A ≤ a := by
      rw [hcase]; exact mul_le_mul_of_nonneg_right (min_le_left _ _) hA.le
    linarith
  · have hab : a = Real.sqrt (A * stepSize p A / (8 * p.d)) := by
      have := min_choice (Real.sqrt (A * stepSize p A / (8 * p.d))) (thetaCap p * A)
      rcases this with h | h
      · exact h
      · exact absurd h hcase
    by_cases hI : 2 * p.L0 ≤ 160 * Lp p ^ 2 * p.R ^ 2 / A
    · left
      have hM2 : curvBound p (gapLevel p A) ≤ 320 * Lp p ^ 2 * p.R ^ 2 / A := by
        have : 20 * Lp p ^ 2 * gapLevel p A = 160 * Lp p ^ 2 * p.R ^ 2 / A := by rw [hg]; ring
        have e2 : 320 * Lp p ^ 2 * p.R ^ 2 / A = 2 * (160 * Lp p ^ 2 * p.R ^ 2 / A) := by ring
        linarith
      have hsq : A / (Lp p * p.R * Real.sqrt (20480 * p.d * rp p)) ≤ a := by
        rw [hab]
        apply Real.le_sqrt_of_sq_le
        have hsq' : 0 < Real.sqrt (20480 * p.d * rp p) := Real.sqrt_pos.mpr (by positivity)
        have e1 : (A / (Lp p * p.R * Real.sqrt (20480 * p.d * rp p))) ^ 2 =
            A ^ 2 / (Lp p ^ 2 * p.R ^ 2 * (20480 * p.d * rp p)) := by
          rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have e2 : A * stepSize p A / (8 * p.d) =
            A / (64 * p.d * rp p * curvBound p (gapLevel p A)) := by
          rw [hseq]; field_simp; ring
        rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
        have hMA : curvBound p (gapLevel p A) * A ≤ 320 * Lp p ^ 2 * p.R ^ 2 := by
          rwa [le_div_iff₀ hA] at hM2
        have hk : 0 ≤ 64 * p.d * rp p * A := by positivity
        have := mul_le_mul_of_nonneg_left hMA hk
        nlinarith
      have : growthRate p * A ≤ a := by
        calc growthRate p * A ≤ (1 / (Lp p * p.R * Real.sqrt (20480 * p.d * rp p))) * A :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hA.le
          _ = A / (Lp p * p.R * Real.sqrt (20480 * p.d * rp p)) := by ring
          _ ≤ a := hsq
      linarith
    · right
      rw [not_le] at hI
      have hM4 : curvBound p (gapLevel p A) ≤ 4 * p.L0 := by
        have : 20 * Lp p ^ 2 * gapLevel p A = 160 * Lp p ^ 2 * p.R ^ 2 / A := by rw [hg]; ring
        linarith
      have hlow : Real.sqrt (A / (256 * p.d * rp p * p.L0)) ≤ a := by
        rw [hab]
        apply Real.sqrt_le_sqrt
        rw [hseq]
        rw [show A * (1 / (8 * curvBound p (gapLevel p A) * rp p)) / (8 * p.d) =
          A / (64 * p.d * rp p * curvBound p (gapLevel p A)) by field_simp; ring]
        apply div_le_div_of_nonneg_left hA.le (by positivity)
        nlinarith [mul_pos hd hrp]
      have hq : a ≤ A / 4 := weight_le_quarter (p := p) hA
      have hsA := Real.sqrt_pos.mpr hA
      have hsAa := Real.sqrt_pos.mpr (show 0 < A + a by positivity)
      have hsqAa : Real.sqrt (A + a) ≤ Real.sqrt (5 / 4 * A) := Real.sqrt_le_sqrt (by linarith)
      have h5 : Real.sqrt (5 / 4 * A) ≤ 9 / 8 * Real.sqrt A := by
        rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hA.le]; nlinarith
      have hdiff : a / (2 * Real.sqrt (A + a)) ≤ Real.sqrt (A + a) - Real.sqrt A := by
        have hsq1 := Real.sq_sqrt (show 0 ≤ A + a by positivity)
        have hsq2 := Real.sq_sqrt hA.le
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.sqrt_le_sqrt (show A ≤ A + a by linarith)]
      have hb : growthStep p ≤ a / (2 * Real.sqrt (A + a)) := by
        have hden : 2 * Real.sqrt (A + a) ≤ 9 / 4 * Real.sqrt A := by linarith
        have h1 : a / (9 / 4 * Real.sqrt A) ≤ a / (2 * Real.sqrt (A + a)) :=
          div_le_div_of_nonneg_left ha.le (by positivity) hden
        have h2 : growthStep p ≤ a / (9 / 4 * Real.sqrt A) := by
          rw [le_div_iff₀ (by positivity)]
          have hk : Real.sqrt (A / (256 * p.d * rp p * p.L0)) =
              Real.sqrt A / (16 * Real.sqrt (p.d * rp p * p.L0)) := by
            rw [Real.sqrt_div' _ (by positivity),
              show 256 * p.d * rp p * p.L0 = 16 ^ 2 * (p.d * rp p * p.L0) by ring,
              Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
          rw [hk] at hlow
          have hsdr : 0 < Real.sqrt (p.d * rp p * p.L0) := Real.sqrt_pos.mpr (by positivity)
          unfold growthStep
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          have : Real.sqrt A / (16 * Real.sqrt (p.d * rp p * p.L0)) * (16 * Real.sqrt (p.d * rp p * p.L0)) = Real.sqrt A := by
            field_simp
          nlinarith
        linarith
      linarith

omit hp in
lemma log_one_add_ge {x : ℝ} (hx : 0 < x) (hx4 : x ≤ 1 / 4) : 4 / 5 * x ≤ Real.log (1 + x) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
  have : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [this] at h
  have : 4 / 5 * x ≤ x / (1 + x) := by rw [le_div_iff₀ (by linarith)]; nlinarith
  linarith

noncomputable def potentialQ (p : Params) (A : ℝ) : ℝ :=
  Real.log A / Real.log (1 + growthRate p) + Real.sqrt A / growthStep p

lemma potentialQ_step {A : ℝ} (hA : 0 < A) :
    potentialQ p A + 1 ≤ potentialQ p (A + weight p A) := by
  have hθ := growthRate_pos hp
  have hθ4 := growthRate_le (p := p)
  have hβ := growthStep_pos hp
  have ha := weight_pos hp hA
  have hlog := Real.log_pos (show 1 < 1 + growthRate p by linarith)
  have hmonoL : Real.log A ≤ Real.log (A + weight p A) :=
    Real.log_le_log hA (by linarith)
  have hmonoS : Real.sqrt A ≤ Real.sqrt (A + weight p A) := Real.sqrt_le_sqrt (by linarith)
  unfold potentialQ
  rcases growth_dichotomy hp hA with h | h
  · have hl : Real.log A + Real.log (1 + growthRate p) ≤ Real.log (A + weight p A) := by
      rw [← Real.log_mul hA.ne' (by linarith)]
      exact Real.log_le_log (by positivity) (by linarith)
    have : Real.log A / Real.log (1 + growthRate p) + 1 ≤
        Real.log (A + weight p A) / Real.log (1 + growthRate p) := by
      rw [div_add_one hlog.ne', div_le_div_iff_of_pos_right hlog]; linarith
    have : Real.sqrt A / growthStep p ≤ Real.sqrt (A + weight p A) / growthStep p :=
      div_le_div_of_nonneg_right hmonoS hβ.le
    linarith
  · have : Real.sqrt A / growthStep p + 1 ≤ Real.sqrt (A + weight p A) / growthStep p := by
      rw [div_add_one hβ.ne', div_le_div_iff_of_pos_right hβ]; linarith
    have : Real.log A / Real.log (1 + growthRate p) ≤
        Real.log (A + weight p A) / Real.log (1 + growthRate p) :=
      div_le_div_of_nonneg_right hmonoL hlog.le
    linarith

lemma potentialQ_sched (k : ℕ) : potentialQ p (sched p 0) + k ≤ potentialQ p (sched p k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := potentialQ_step hp (sched_pos hp k)
    have e : sched p (k + 1) = sched p k + weight p (sched p k) := rfl
    rw [e]
    push_cast
    linarith

lemma potentialQ_strictMono {A B : ℝ} (hA : 0 < A) (h : A < B) :
    potentialQ p A < potentialQ p B := by
  have hθ := growthRate_pos hp
  have hβ := growthStep_pos hp
  have hlog := Real.log_pos (show 1 < 1 + growthRate p by linarith)
  unfold potentialQ
  have h1 : Real.log A / Real.log (1 + growthRate p) < Real.log B / Real.log (1 + growthRate p) :=
    div_lt_div_of_pos_right (Real.log_lt_log hA h) hlog
  have h2 : Real.sqrt A / growthStep p ≤ Real.sqrt B / growthStep p :=
    div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h.le) hβ.le
  linarith

lemma inv_log_growth_le :
    1 / Real.log (1 + growthRate p) ≤
      1300 * (p.r + 1 + p.L1 * p.R * Real.sqrt (p.d * (p.r + 1))) := by
  have hθ := growthRate_pos hp
  have hθ4 := growthRate_le (p := p)
  have hlog := log_one_add_ge hθ hθ4
  have hlogpos : 0 < Real.log (1 + growthRate p) := by linarith
  have hL := Lp_pos hp
  have hR := hp.R_pos
  have hd := dR_pos hp
  have hr := hp.r_pos
  have hrp := rp_pos hp
  have hsd := sqrt_d_pos hp
  have hθc := thetaCap_pos hp
  have hX : 0 < Real.sqrt (20480 * p.d * rp p) := Real.sqrt_pos.mpr (by positivity)
  have hinv : 1 / growthRate p ≤ 1 / thetaCap p + Lp p * p.R * Real.sqrt (20480 * p.d * rp p) := by
    unfold growthRate
    rcases min_choice (thetaCap p) (1 / (Lp p * p.R * Real.sqrt (20480 * p.d * rp p))) with h | h
    · rw [h]; have : 0 ≤ Lp p * p.R * Real.sqrt (20480 * p.d * rp p) := by positivity
      linarith
    · rw [h, one_div_one_div]; have : 0 ≤ 1 / thetaCap p := by positivity
      linarith
  have hc : 1 / thetaCap p ≤ 4 + (p.r + 2) / 2 := by
    unfold thetaCap
    rcases min_choice (1 / 4 : ℝ) (2 / (p.r + 2)) with h | h
    · rw [h]; norm_num; positivity
    · rw [h, one_div_div]; linarith
  have hLp : Lp p * p.R ≤ p.L1 * p.R + 1 / Real.sqrt p.d := by
    have : Lp p ≤ p.L1 + 1 / (p.R * Real.sqrt p.d) := by
      unfold Lp
      apply max_le
      · have : 0 ≤ 1 / (p.R * Real.sqrt p.d) := by positivity
        linarith
      · linarith [hp.L1_nonneg]
    have := mul_le_mul_of_nonneg_right this hR.le
    rw [add_mul, show 1 / (p.R * Real.sqrt p.d) * p.R = 1 / Real.sqrt p.d by field_simp] at this
    exact this
  have hsq : Real.sqrt (20480 * p.d * rp p) ≤ 1012 * Real.sqrt (p.d * (p.r + 1)) := by
    have h1 : 20480 * p.d * rp p ≤ 1024000 * (p.d * (p.r + 1)) := by
      have := rp_le hp; nlinarith
    calc Real.sqrt (20480 * p.d * rp p) ≤ Real.sqrt (1024000 * (p.d * (p.r + 1))) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt 1024000 * Real.sqrt (p.d * (p.r + 1)) := Real.sqrt_mul (by norm_num) _
      _ ≤ 1012 * Real.sqrt (p.d * (p.r + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hprod : Lp p * p.R * Real.sqrt (20480 * p.d * rp p) ≤
      1012 * (p.L1 * p.R * Real.sqrt (p.d * (p.r + 1)) + Real.sqrt (p.r + 1)) := by
    have hdr : Real.sqrt (p.d * (p.r + 1)) = Real.sqrt p.d * Real.sqrt (p.r + 1) :=
      Real.sqrt_mul hd.le _
    calc Lp p * p.R * Real.sqrt (20480 * p.d * rp p) ≤
          (p.L1 * p.R + 1 / Real.sqrt p.d) * (1012 * Real.sqrt (p.d * (p.r + 1))) :=
          mul_le_mul hLp hsq hX.le (by have := hp.L1_nonneg; positivity)
      _ = 1012 * (p.L1 * p.R * Real.sqrt (p.d * (p.r + 1)) + Real.sqrt (p.r + 1)) := by
          rw [hdr]; field_simp
  have h54 : 1 / Real.log (1 + growthRate p) ≤ 5 / 4 * (1 / growthRate p) := by
    rw [div_le_iff₀ hlogpos]
    have : 5 / 4 * (1 / growthRate p) * (4 / 5 * growthRate p) = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 5 / 4 * (1 / growthRate p) by positivity)]
  have : 5 / 4 * (1 / growthRate p) ≤ 5 / 4 * (4 + (p.r + 2) / 2) +
      5 / 4 * (1012 * (p.L1 * p.R * Real.sqrt (p.d * (p.r + 1)) + Real.sqrt (p.r + 1))) := by
    nlinarith
  have hsr : Real.sqrt (p.r + 1) ≤ p.r + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hLR0 : 0 ≤ p.L1 * p.R * Real.sqrt (p.d * (p.r + 1)) :=
    mul_nonneg (mul_nonneg hp.L1_nonneg hR.le) (Real.sqrt_nonneg _)
  linarith

lemma sched_iterations : 4 * p.R ^ 2 / p.ε ≤ sched p (iterations p) := by
  by_contra hc
  rw [not_le] at hc
  set K := iterations p
  set As := 4 * p.R ^ 2 / p.ε
  have hR := hp.R_pos
  have hε := hp.ε_pos
  have hΔ := hp.Δ_pos
  have hd := dR_pos hp
  have hr := hp.r_pos
  have hrp := rp_pos hp
  have hL0 := hp.L0_pos
  have hA0 := sched_pos hp 0
  have hQ := potentialQ_sched hp K
  have hQs := potentialQ_strictMono hp (sched_pos hp K) hc
  have hθ := growthRate_pos hp
  have hβ := growthStep_pos hp
  have hlogpos := Real.log_pos (show 1 < 1 + growthRate p by linarith)
  have hAs : 0 < As := by positivity
  have hK : (K : ℝ) < potentialQ p As - potentialQ p (sched p 0) := by linarith
  unfold potentialQ at hK
  have hlogdiff : Real.log As - Real.log (sched p 0) ≤ Real.log (Real.exp 1 + 8 * p.Δ / p.ε) := by
    rw [← Real.log_div hAs.ne' hA0.ne']
    have e : As / sched p 0 = 8 * p.Δ / p.ε := by
      simp only [As, sched]; field_simp; ring
    rw [e]
    exact Real.log_le_log (by positivity) (by have := Real.exp_pos 1; linarith)
  have hLg : 1 ≤ Real.log (Real.exp 1 + 8 * p.Δ / p.ε) := by
    have h8 : Real.exp 1 ≤ Real.exp 1 + 8 * p.Δ / p.ε := by
      have : 0 ≤ 8 * p.Δ / p.ε := by positivity
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) h8
  have hterm1 : Real.log As / Real.log (1 + growthRate p) -
      Real.log (sched p 0) / Real.log (1 + growthRate p) ≤
      1300 * (p.r + 1 + p.L1 * p.R * Real.sqrt (p.d * (p.r + 1))) *
        Real.log (Real.exp 1 + 8 * p.Δ / p.ε) := by
    rw [← sub_div, div_eq_mul_one_div]
    have hinv := inv_log_growth_le hp
    have hpos : 0 ≤ 1 / Real.log (1 + growthRate p) := by positivity
    calc (Real.log As - Real.log (sched p 0)) * (1 / Real.log (1 + growthRate p)) ≤
          Real.log (Real.exp 1 + 8 * p.Δ / p.ε) * (1 / Real.log (1 + growthRate p)) :=
          mul_le_mul_of_nonneg_right hlogdiff hpos
      _ ≤ Real.log (Real.exp 1 + 8 * p.Δ / p.ε) *
          (1300 * (p.r + 1 + p.L1 * p.R * Real.sqrt (p.d * (p.r + 1)))) :=
          mul_le_mul_of_nonneg_left hinv (by linarith)
      _ = _ := by ring
  have hterm2 : Real.sqrt As / growthStep p - Real.sqrt (sched p 0) / growthStep p ≤
      510 * Real.sqrt (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) := by
    have h0 : 0 ≤ Real.sqrt (sched p 0) / growthStep p := by positivity
    have e : Real.sqrt As / growthStep p = 72 * Real.sqrt (p.d * rp p * p.L0 * p.R ^ 2 / p.ε) := by
      unfold growthStep
      rw [div_div_eq_mul_div, div_one]
      have hsAs : Real.sqrt As = 2 * p.R / Real.sqrt p.ε := by
        simp only [As]
        rw [Real.sqrt_div' _ hε.le, show 4 * p.R ^ 2 = (2 * p.R) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      rw [hsAs]
      have h2 : Real.sqrt (p.d * rp p * p.L0 * p.R ^ 2 / p.ε) =
          Real.sqrt (p.d * rp p * p.L0) * p.R / Real.sqrt p.ε := by
        rw [Real.sqrt_div' _ hε.le, Real.sqrt_mul (by positivity), Real.sqrt_sq hR.le]
      rw [h2]
      ring
    have hle : 72 * Real.sqrt (p.d * rp p * p.L0 * p.R ^ 2 / p.ε) ≤
        510 * Real.sqrt (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) := by
      have h1 : p.d * rp p * p.L0 * p.R ^ 2 / p.ε ≤ 50 * (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) := by
        have := rp_le hp
        rw [show 50 * (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) =
          p.d * (50 * (p.r + 1)) * p.L0 * p.R ^ 2 / p.ε by ring]
        apply div_le_div_of_nonneg_right _ hε.le
        have : 0 ≤ p.d * p.L0 * p.R ^ 2 := by positivity
        nlinarith
      calc 72 * Real.sqrt (p.d * rp p * p.L0 * p.R ^ 2 / p.ε) ≤
            72 * Real.sqrt (50 * (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε)) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (by norm_num)
        _ = 72 * Real.sqrt 50 * Real.sqrt (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) := by
            rw [Real.sqrt_mul (by norm_num)]; ring
        _ ≤ 510 * Real.sqrt (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            have : Real.sqrt 50 ≤ 7.08 := by
              rw [Real.sqrt_le_left (by norm_num)]; norm_num
            linarith
    linarith
  have hKle : (510 * Real.sqrt (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) +
      1300 * (p.r + 1 + p.L1 * p.R * Real.sqrt (p.d * (p.r + 1))) *
        Real.log (Real.exp 1 + 8 * p.Δ / p.ε)) ≤ (K : ℝ) := Nat.le_ceil _
  linarith

end

end OracleTemplate.MatrixGeneralizedZO
